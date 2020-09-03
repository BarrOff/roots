## ======
## simple
## ======
##
## some simpler (and faster) implementations for root finding
##
## These avoid the setup costs of the `findZero` method, so should be faster
## though they will take similar number of function calls.

import math
import private/utils, findZero, bracketing

type
  TupleWrapper[T, S: SomeFloat] = object of RootObj
    f, fp: proc(a: T): S

let
  eps = 8 * max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(1.0, 0.0))
  eps32 = 8 * max(nextafterf(1.0, Inf) - 1.0, 1.0 - nextafterf(1.0, 0.0))

# forward declarations
proc hasConverged[S: SomeFloat](Val: bool, x1, x2, m: float, ym: S, atol,
    rtol: float): bool
proc secant[T, S: SomeFloat](f: proc(x: T): S, a, b: T, atol: T = 0.0,
    rtol: T = NaN, maxevals = 100): T
proc secant[T, S: SomeFloat, CF: CallableFunction[T, S]](f: CF, a, b: T,
    atol: T = 0.0, rtol: T = NaN, maxevals = 100): T
proc mullerStep*[T, S: SomeFloat](a, b, c: T, fa, fb, fc: S): T

## Bisection
## ---------
## Essentially from
## `Jason Merrill <https://gist.github.com/jwmerrill/9012954>`_
## cf. `here <http://squishythinking.com/2014/02/22/bisecting-floats/>`_
## This also borrows a trick from
## `here <https://discourse.julialang.org/t/simple-and-fast-bisection/14886>`_
## where we keep `x1` so that `y1` is negative, and `x2` so that `y2` is
## positive this allows the use of signbit over `y1*y2 < 0` which avoid < and
## a multiplication this has a small, but noticeable impact on performance.

proc bisection*[T, S: SomeFloat, CF: CallableFunction[float, S]](f: CF, a, b: T,
    xatol: float = 0.0, xrtol: float = 0.0): float =
  ## Performs bisection method to find a zero of a continuous
  ## function.
  ##
  ## It is assumed that `(a,b)` is a bracket, that is, the function has
  ## different signs at `a` and `b`. The interval `(a,b)` is converted to
  ## floating point and shrunk when `a` or `b` is infinite. The function f may
  ## be infinite for the typical case. If `f` is not continuous, the algorithm
  ## may find jumping points over the x axis, not just zeros.
  ##
  ## If non-trivial tolerances are specified, the process will terminate
  ## when the bracket `(a,b)` satisfies `isapprox(a, b, atol=xatol,
  ## rtol=xrtol)`. For zero tolerances, the default, for `float64`, `float32`,
  ## values, the process will terminate at a value `x` with
  ## `f(x)=0` or `f(x)*f(prevfloat(x)) < 0 ` or `f(x) * f(nextfloat(x)) <
  ## 0`. For other number types, the A42 method is used.
  var
    (x1, x2) = adjustBracket((float(a), float(b)))
  let
    atol = abs(xatol)
    rtol = abs(xrtol)
    catol = classify(atol)
    crtol = classify(rtol)

  var
    CT: bool

  if (catol == fcZero or catol == fcNegZero) and (crtol == fcZero or
      crtol == fcNegZero):
    CT = true
  else:
    CT = false

  var
    y1 = f.f(x1)
    y2 = f.f(x2)

  if y1 * y2 >= 0:
    raise newException(InitialValueError, "the interval provided does not" &
      " bracket a root")

  if sgn(y2) < 1:
    (x1, x2, y1, y2) = (x2, x1, y2, y1)

  var
    xm = middle(x1, x2)
    ym = f.f(xm)

  while true:

    if hasConverged(CT, x1, x2, xm, ym, atol, rtol):
      return xm

    if sgn(ym) < 1:
      (x1, y1) = (xm, ym)
    else:
      (x2, y2) = (xm, ym)

    xm = middle2(x1, x2)
    ym = f.f(xm)

proc bisection*[T, S: SomeFloat](f: proc(x: float): S, a, b: T,
    xatol: float = 0.0, xrtol: float = 0.0): float =
  var
    (x1, x2) = adjustBracket((float(a), float(b)))
  let
    atol = abs(xatol)
    rtol = abs(xrtol)
    catol = classify(atol)
    crtol = classify(rtol)

  var
    CT: bool

  if (catol == fcZero or catol == fcNegZero) and (crtol == fcZero or
      crtol == fcNegZero):
    CT = true
  else:
    CT = false

  var
    y1 = f(x1)
    y2 = f(x2)

  if y1 * y2 >= 0:
    raise newException(InitialValueError, "the interval provided dows not" &
      " bracket a root")

  if sgn(y2) < 1:
    (x1, x2, y1, y2) = (x2, x1, y2, y1)

  var
    xm = middle(x1, x2)
    ym = f(xm)

  while true:

    if hasConverged(CT, x1, x2, xm, ym, atol, rtol):
      return xm

    if sgn(ym) < 1:
      (x1, y1) = (xm, ym)
    else:
      (x2, y2) = (xm, ym)

    xm = middle2(x1, x2)
    ym = f(xm)


proc hasConverged[S: SomeFloat](Val: bool, x1, x2, m: float, ym: S, atol,
    rtol: float): bool =
  let
    cym = classify(ym)

  case cym
  of fcZero, fcNegZero, fcNan:
    return true
  else:
    if Val:
      if x1 != m and m != x2:
        return false
      else:
        return true
    else:
      return abs(x1 - x2) <= atol + max(abs(x1), abs(x2)) * rtol



## secantMethod
## ------------
##
## Perform secant method to solve `f(x) = 0`.
##
## The secant method is an iterative method with update step
## given by `b - fb/m` where m is the slope of the secant line between
## `(a,fa)` and `(b,fb).`
##
## The inital values can be specified as a pair of 2, as in `(a,b)` or
## `[a,b]`, or as a single value, in which case a value of `b` is chosen.
##
## The algorithm returns m when `abs(fm) <= max(atol, abs(m) * rtol)`.
## If this doesn't occur before `maxevals` steps or the algorithm
## encounters an issue, a value of `NaN` is returned. If too many steps
## are taken, the current value is checked to see if there is a sign
## change for neighboring floating point values.
##
## The `Order1` method for `findZero` also implements the secant
## method. This one will be faster, as there are fewer setup costs.

proc secantMethod*[T, S: SomeFloat, CF: CallableFunction[T, S]](f: CF, xs: T|(T,
    T), atol: float = 0.0, rtol: float = NaN, maxevals = 100): T =
  ## Perform secant method to solve `f(x) = 0`.
  var
    a, b, h: T

  when typeof(xs) is T:
    a = xs

    when sizeof(T) == 8:
      h = max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(1.0, 0.0))
    else:
      h = max(nextafterf(1.0, Inf) - 1.0, 1.0 - nextafterf(1.0, 0.0))
    h = pow(h, 1/3)
    let da = h + abs(a) * h^2
    b = a + da
  else:
    a = xs[0]
    b = xs[1]

  when sizeof(T) == 8:
    if classify(rtol) == fcNan:
      return secant(f, a, b, atol, eps, maxevals)
  else:
    if classify(rtol) == fcNan:
      return secant(f, a, b, atol, eps32, maxevals)

  return secant(f, a, b, atol, rtol, maxevals)

proc secantMethod*[T, S: SomeFloat](f: proc(x: T): S, xs: T|(T, T),
    atol: float = 0.0, rtol: float = NaN, maxevals = 100): T =
  var
    a, b, h: T

  when typeof(xs) is T:
    a = xs

    when sizeof(T) == 8:
      h = max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(1.0, 0.0))
    else:
      h = max(nextafterf(1.0, Inf) - 1.0, 1.0 - nextafterf(1.0, 0.0))
    h = pow(h, 1/3)
    let da = h + abs(a) * h^2
    b = a + da
  else:
    a = xs[0]
    b = xs[1]

  when sizeof(T) == 8:
    if classify(rtol) == fcNan:
      return secant(f, a, b, atol, eps, maxevals)
  else:
    if classify(rtol) == fcNan:
      return secant(f, a, b, atol, eps32, maxevals)

  return secant(f, a, b, atol, rtol, maxevals)

proc secant[T, S: SomeFloat, CF: CallableFunction[T, S]](f: CF, a, b: T,
    atol: T = 0.0, rtol: T = NaN, maxevals = 100): T =
  let
    nan = (0 * a) / (0 * a)
  var
    cnt = 0
    a1 = a
    b1 = b
    fa = f.f(a)
    fb = f.f(b)
    rtol = rtol

  if fb == fa:
    return nan

  let
    uatol = atol
    adjustunit = 1.0

  when sizeof(T) == 8:
    if classify(rtol) == fcNan:
      rtol = eps
  else:
    if classify(rtol) == fcNan:
      rtol = eps32

  while cnt < maxevals:
    let
      m = b1 - (b1 - a1) * fb / (fb - fa)
      fm = f.f(m)
      cfm = classify(fm)

    if cfm == fcZero or cfm == fcNegZero:
      return m
    if cfm == fcNan:
      return nan
    if abs(fm) <= adjustunit * max(uatol, abs(m) * rtol):
      return m
    if fm == fb:
      when sizeof(T) == 8:
        if sgn(fm) * sgn(f.f(nextafter(m, Inf))) <= 0:
          return m
        if sgn(fm) * sgn(f.f(nextafter(m, -Inf))) <= 0:
          return m
      else:
        if sgn(fm) * sgn(f.f(nextafterf(m, Inf))) <= 0:
          return m
        if sgn(fm) * sgn(f.f(nextafterf(m, -Inf))) <= 0:
          return m
      return nan

    (a1, b1, fa, fb) = (b1, m, fb, fm)

    inc(cnt)

  return nan

proc secant[T, S: SomeFloat](f: proc(x: T): S, a, b: T, atol: T = 0.0,
    rtol: T = NaN, maxevals = 100): T =
  let
    nan = (0 * a) / (0 * a)
  var
    cnt = 0
    a1 = a
    b1 = b
    fa = f(a)
    fb = f(b)
    rtol = rtol

  if fb == fa:
    return nan

  let
    uatol = atol
    adjustunit = 1.0

  when sizeof(T) == 8:
    if classify(rtol) == fcNan:
      rtol = eps
  else:
    if classify(rtol) == fcNan:
      rtol = eps32

  while cnt < maxevals:
    let
      m = b1 - (b1 - a1) * fb / (fb - fa)
      fm = f(m)
      cfm = classify(fm)

    if cfm == fcZero or cfm == fcNegZero:
      return m
    if cfm == fcNan:
      return nan
    if abs(fm) <= adjustunit * max(uatol, abs(m) * rtol):
      return m
    if fm == fb:
      when sizeof(T) == 8:
        if sgn(fm) * sgn(f(nextafter(m, Inf))) <= 0:
          return m
        if sgn(fm) * sgn(f(nextafter(m, -Inf))) <= 0:
          return m
      else:
        if sgn(fm) * sgn(f(nextafterf(m, Inf))) <= 0:
          return m
        if sgn(fm) * sgn(f(nextafterf(m, -Inf))) <= 0:
          return m
      return nan

    (a1, b1, fa, fb) = (b1, m, fb, fm)

    inc(cnt)

  return nan



## Muller
## ------
##
## *Muller’s method* generalizes the secant method, but uses quadratic
## interpolation among three points instead of linear interpolation between two.
## Solving for the zeros of the quadratic allows the method to find complex
## pairs of roots.
## Given three previous guesses for the root `xᵢ₋₂`, `xᵢ₋₁`, `xᵢ`, and the
## values of the polynomial `f` at those points, the next approximation `xᵢ₊₁`
## is produced.
##
## Excerpt and the algorithm taken from
##
## ``W.H. Press, S.A. Teukolsky, W.T. Vetterling and B.P. Flannery
## *Numerical Recipes in C*, Cambridge University Press (2002), p. 371``
##
## Convergence here is decided by `xᵢ₊₁ ≈ xᵢ` using the tolerances specified,
## which both default to `eps(one(typeof(abs(xᵢ))))^4/5` in the appropriate
## units. Each iteration performs three evaluations of `f`. The first method
## picks two remaining points at random in relative proximity of `xᵢ`.
##
## Note that the method may return complex result even for real intial values
## as this depends on the function.

proc muller*[T, S: SomeFloat](f: proc(a: T): S, oldest, older, old: T,
    xatol: T = NaN, xrtol: T = NaN, maxevals: int = 300): T =
  ## Perform Muller´s method to solve `f(x) = 0`.
  var
    (xI2, xI1, xI) = (oldest, older, old)
    atol, rtol: T

  when sizeof(T) == 8:
    if classify(xatol) != fcNan:
      atol = xatol
    else:
      atol = pow(max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(1.0, 0.0)), 4/5)
    if classify(xrtol) != fcNan:
      rtol = xrtol
    else:
      rtol = pow(max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(1.0, 0.0)), 4/5)
  else:
    if classify(xatol) != fcNan:
      atol = xatol
    else:
      atol = pow(max(nextafterf(1.0, Inf) - 1.0, 1.0 - nextafterf(1.0, 0.0)),
          4 / 5)
    if classify(xrtol) != fcNan:
      rtol = xrtol
    else:
      rtol = pow(max(nextafterf(1.0, Inf) - 1.0, 1.0 - nextafterf(1.0, 0.0)),
          4 / 5)


  for i in 1..maxevals div 3:
    # three evaluations per iteration
    var
      x = mullerStep(xI2, xI1, xI, f(xI2), f(xI1), f(xI))

    if classify(x) == fcNan:
      write(stderr, "The algorithm might not have converged, stopping at i=" &
          $(i) & ": " & $(abs(xI - xI1)), "\n")
      return xI

    (xI2, xI1, xI) = (xI1, xI, x)
    # stopping criterion
    if isFApprox0(xI, xI1, atol = atol, rtol = rtol):
      return xI

  return xI

proc mullerStep*[T, S: SomeFloat](a, b, c: T, fa, fb, fc: S): T =
  let
    q = (c - b) / (b - a)
    q2 = q * q
    q1 = q + T(1)

    A = q * fc - q * q1 * fb + q2 * fa
    B = (q1 + q) * fc - q1 * q1 * fb + q2 * fa
    C = q1 * fc

  var
    delta = B * B - 4 * A * C
  if delta < 0:
    raise newException(RangeError, "Discriminant is negative and " &
      " the function most likely has complex roots. You might want to" &
      " call muller with complex input.")
  delta = sqrt(delta)

  let
    dplus = B + delta
    dminus = B - delta
    den = if abs(dplus) > abs(dminus):
            dplus
          else:
            dminus

  return T(c - (c - b) * 2 * C / den)

## Newton's method
## ---------------
##
## Function may be passed in as a tuple (f, f') *or* as function which returns
## (f,f/f').
##
## Note: unlike the call `newton(f, fp, x0)`--which dispatches to a method of
## `find_zero`, these two interfaces will specialize on the function that is
## passed in. This means, these functions will be faster for subsequent calls,
## but may be slower for an initial call.
##
## Convergence here is decided by x_n ≈ x_{n-1} using the tolerances specified,
## which both default to `eps(T)^4/5` in the appropriate units.

proc newton*[T, S: SomeFloat](f0, f1: proc(a: T): S, x0: T, xatol: T = NaN,
    xrtol: T = NaN, maxevals = 100): T =
  var
    x = x0
    atol, rtol: T

  when sizeof(T) == 8:
    if classify(xatol) != fcNan:
      atol = xatol
    else:
      atol = pow(max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(1.0, 0.0)), 4/5)
    if classify(xrtol) != fcNan:
      rtol = xrtol
    else:
      rtol = pow(max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(1.0, 0.0)), 4/5)
  else:
    if classify(xatol) != fcNan:
      atol = xatol
    else:
      atol = pow(max(nextafterf(1.0, Inf) - 1.0, 1.0 - nextafterf(1.0, 0.0)),
          4 / 5)
    if classify(xrtol) != fcNan:
      rtol = xrtol
    else:
      rtol = pow(max(nextafterf(1.0, Inf) - 1.0, 1.0 - nextafterf(1.0, 0.0)),
          4 / 5)

  var
    xo = Inf
  for i in 1..maxevals:
    let
      fx = f0(x)
      deltaX = fx / f1(x)

    if classify(fx) == fcZero or classify(fx) == fcNegZero:
      return x

    x -= deltaX

    if abs(x - xo) <= atol or abs((x - x0) / x0) <= rtol:
      return x

    xo = x

  raise newException(InitialValueError, "No convergence")

proc newton*[T, S: SomeFloat, TW: TupleWrapper[T, S]](f: TW, x0: T,
    xatol: T = NaN, xrtol: T = NaN, maxevals = 100): T =
  var
    x = x0
    atol, rtol: T

  when sizeof(T) == 8:
    if classify(xatol) != fcNan:
      atol = xatol
    else:
      atol = pow(max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(1.0, 0.0)), 4/5)
    if classify(xrtol) != fcNan:
      rtol = xrtol
    else:
      rtol = pow(max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(1.0, 0.0)), 4/5)
  else:
    if classify(xatol) != fcNan:
      atol = xatol
    else:
      atol = pow(max(nextafterf(1.0, Inf) - 1.0, 1.0 - nextafterf(1.0, 0.0)),
          4 / 5)
    if classify(xrtol) != fcNan:
      rtol = xrtol
    else:
      rtol = pow(max(nextafterf(1.0, Inf) - 1.0, 1.0 - nextafterf(1.0, 0.0)),
          4 / 5)

  var
    xo = Inf
  for i in 1..maxevals:
    let
      fx = f.f(x)
      deltaX = fx / f.fp(x)

    if classify(fx) == fcZero or classify(fx) == fcNegZero:
      return x

    x -= deltaX

    if abs(x - xo) <= atol or abs((x - x0) / x0) <= rtol:
      return x

    xo = x

  raise newException(InitialValueError, "No convergence")



## dfree
## -----
##
## This is basically Order0(), but with different, default, tolerances employed
## It takes more function calls, but works harder to find exact zeros
## where exact means either iszero(fx), adjacent floats have sign change, or
## abs(fxn) <= 8 eps(xn)
##
## A more robust secant method implementation
##
## Solve for `f(x) = 0` using an alogorithm from *Personal Calculator Has Key
## to Solve Any Equation `f(x) = 0`*, the SOLVE button from the
## `HP-34C <http://www.hpl.hp.com/hpjournal/pdfs/IssuePDFs/1979-12.pdf>`_.
##
## This is also implemented as the `Order0` method for `find_zero`.
##
## The inital values can be specified as a pair of two values, as in
## `(a,b)` or `[a,b]`, or as a single value, in which case a value of `b`
## is computed, possibly from `fb`.  The basic idea is to follow the
## secant method to convergence unless:
##
## * a bracket is found, in which case bisection is used;
## * the secant method is not converging, in which case a few steps of a
##   quadratic method are used to see if that improves matters.
##
## Convergence occurs when `f(m) == 0`, there is a sign change between
## `m` and an adjacent floating point value, or `f(m) <= 2^3*eps(m)`.
##
## A value of `NaN` is returned if the algorithm takes too many steps
## before identifying a zero.

proc dfree*[T, S: SomeFloat](f: proc(a: T): S, xs: T|(T, T)): T =

  var
    a, b: T
    fa, fb: S

  when typeof(xs) is T:
    a = xs
    fa = f(a)

    when sizeof(T) == 8:
      let
        h = pow(max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(1.0, 0.0)), 1/3)
        da = h + abs(a) * h^2
    else:
      let
        h = pow(max(nextafterf(1.0, Inf) - 1.0, 1.0 - nextafterf(1.0, 0.0)), 1/3)
        da = h + abs(a) * h^2

    b = a + da
    fb = f(b)
  else:
    (a, b) = (xs[0], xs[1])
    (fa, fb) = (f(a), f(b))

  let nan = (0 * a) / (0 * a)
  var
    (cnt, MAXQUAD) = (0, 3)
    MAXCNT: int

  when sizeof(T) == 8:
    MAXCNT = 5 * int(ceil(-log(max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(
        1.0, 0.0)), exp(1.0))))

  if abs(fa) > abs(fb):
    (a, fa, b, fb) = (b, fb, a, fa)


  # we keep a, b, fa, fb, gamma, fgamma
  var
    quadCtr = 0

  while classify(fb) != fcZero and classify(fb) != fcNegZero:
    inc(cnt)

    if sgn(fa) * sgn(fb) < 0:
      return bisection(f, a, b)

    # take a secant step
    var
      gamma = (b - (b - a) * T(fb / (fb - fa)))
    # modify if gamma is too small or too big
    if classify(gamma - b) == fcZero or classify(gamma - b) == fcNegZero:
      gamma = b + 1/1000 * abs(b - a) # too small
    elif abs(gamma - b) >= 100 * abs(b - a):
      gamma = b + T(sgn(gamma - b)) * 100 * abs(b - a) # too big

    var
      fgamma = f(gamma)

    # change sign
    if sgn(fgamma) * sgn(fb) < 0:
      return bisection(f, gamma, b)

    # decreasing
    if abs(fgamma) < abs(fb):
      (a, fa, b, fb) = (b, fb, gamma, fgamma)
      quadCtr = 0
      if cnt < MAXCNT:
        continue

    gamma = quadVertex(a, fa, b, fb, gamma, fgamma)
    fgamma = f(gamma)
    # decreasing now?
    if abs(fgamma) < abs(fb):
      (a, fa, b, fb) = (b, fb, gamma, fgamma)
      quadCtr = 0
      if cnt < MAXCNT:
        continue

    inc(quadCtr)
    if (quadCtr > MAXQUAD) or (cnt > MAXCNT) or (classify(gamma - b) ==
        fcZero) or (classify(gamma - b) == fcNegZero) or (classify(gamma) == fcNan):
      var
        bprev, bnext: T
      when sizeof(T) == 8:
        bprev = nextafter(b, -Inf)
        bnext = nextafter(b, Inf)
      else:
        bprev = nextafterf(b, -Inf)
        bnext = nextafterf(b, Inf)
      let
        (fbprev, fbnext) = (f(bprev), f(bnext))
      if sgn(fb) * sgn(fbprev) < 0:
        return b
      if sgn(fb) * sgn(fbnext) < 0:
        return b
      for i in @[ (b, fb), (bprev, fbprev), (bnext, fbnext)]:
        when sizeof(T) == 8:
          if abs(i[1]) <= 8 * max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(
              1.0, 0.0)):
            return i[0]
        else:
          if abs(i[1]) <= 8 * max(nextafterf(1.0, Inf) - 1.0, 1.0 - nextafterf(
              1.0, 0.0)):
            return i[0]
      return nan # Failed.

    if abs(fgamma) < abs(fb):
      (b, fb, a, fa) = (gamma, fgamma, b, fb)
    else:
      (a, fa) = (gamma, fgamma)

  return b
