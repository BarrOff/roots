import math
import private/utils, findZero, bracketing

type
  TupleWrapper[T, S: SomeFloat] = object of RootObj
    f, fp: proc(a: T): S

let
  eps = 8 * max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(1.0, 0.0))
  eps32 = 8 * max(nextafterf(1.0, Inf) - 1.0, 1.0 - nextafterf(1.0, 0.0))

# forward declarations
proc hasConverged*[S: SomeFloat](Val: bool, x1, x2, m: float, ym: S, atol, rtol: float): bool
proc secant*[T, S: SomeFloat](f: proc(x: T): S, a, b: T, atol: T = 0.0, rtol: T = NaN, maxevals = 100): T
proc secant*[T, S: SomeFloat, CF: CallableFunction[T, S]](f: CF, a, b: T, atol: T = 0.0, rtol: T = NaN, maxevals = 100): T


proc bisection*[T, S: SomeFloat, CF: CallableFunction[float, S]](f: CF, a, b: T, xatol: float = 0.0, xrtol: float = 0.0): float =
  var
    (x1, x2) = adjustBracket((float(a), float(b)))
  let
    atol = abs(xatol)
    rtol = abs(xrtol)
    catol = classify(atol)
    crtol = classify(rtol)
  
  var
    CT: bool

  if (catol == fcZero or catol == fcNegZero) and (crtol == fcZero or crtol == fcNegZero):
    CT = true
  else:
    CT = false

  var
    y1 = f.f(x1)
    y2 = f.f(x2)

  if y1 * y2 >= 0:
    raise newException(InitialValueError, "the interval provided dows not bracket a root")

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

proc bisection*[T, S: SomeFloat](f: proc(x: float): S, a, b: T, xatol: float = 0.0, xrtol: float = 0.0): float =
  var
    (x1, x2) = adjustBracket((float(a), float(b)))
  let
    atol = abs(xatol)
    rtol = abs(xrtol)
    catol = classify(atol)
    crtol = classify(rtol)
  
  var
    CT: bool

  if (catol == fcZero or catol == fcNegZero) and (crtol == fcZero or crtol == fcNegZero):
    CT = true
  else:
    CT = false

  var
    y1 = f(x1)
    y2 = f(x2)

  if y1 * y2 >= 0:
    raise newException(InitialValueError, "the interval provided dows not bracket a root")

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


proc hasConverged[S: SomeFloat](Val: bool, x1, x2, m: float, ym: S, atol, rtol: float): bool =
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



# secantMethod

proc secantMethod*[T, S: SomeFloat, CF: CallableFunction[T, S]](f: CF, xs: T|(T, T), atol: float = 0.0, rtol: float = NaN, maxevals = 100): T =
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

proc secantMethod*[T, S: SomeFloat](f: proc(x: T): S, xs: T|(T, T), atol: float = 0.0, rtol: float = NaN, maxevals = 100): T =
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

proc secant*[T, S: SomeFloat, CF: CallableFunction[T, S]](f: CF, a, b: T, atol: T = 0.0, rtol: T = NaN, maxevals = 100): T =
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

proc secant*[T, S: SomeFloat](f: proc(x: T): S, a, b: T, atol: T = 0.0, rtol: T = NaN, maxevals = 100): T =
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



# newton

proc newton*[T, S: SomeFloat](f: (proc(a: T): S, proc(a: T): S), x0: T, xatol: T = NaN, xrtol: T = NaN, maxevals = 100): T =
  var
    x = x0
    atol, rtol: T

  when sizeof(T) == 8:
    if classify(xatol) != fcNan:
      atol = xatol
    else:
      atol = pow(max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(1.0, 0.0)), 4 / 5)
    if classify(xrtol) != fcNan:
      rtol = xrtol
    else:
      rtol = pow(max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(1.0, 0.0)), 4 / 5)
  else:
    if classify(xatol) != fcNan:
      atol = xatol
    else:
      atol = pow(max(nextafterf(1.0, Inf) - 1.0, 1.0 - nextafterf(1.0, 0.0)), 4 / 5)
    if classify(xrtol) != fcNan:
      rtol = xrtol
    else:
      rtol = pow(max(nextafterf(1.0, Inf) - 1.0, 1.0 - nextafterf(1.0, 0.0)), 4 / 5)

  var
    xo = Inf
  for i in 1..maxevals:
    let
      fx = f[0](x)
      deltaX = fx / f[1](x)

    if classify(fx) == fcZero or classify(fx) == fcNegZero:
      return x

    x -= deltaX

    if abs(x - xo) <= atol or abs((x - x0) / x0) <= rtol:
      return x

    xo = x

  raise newException(InitialValueError, "No convergence")

proc newton*[T, S: SomeFloat, TW: TupleWrapper[T, S]](f: TW, x0: T, xatol: T = NaN, xrtol: T = NaN, maxevals = 100): T =
  var
    x = x0
    atol, rtol: T

  when sizeof(T) == 8:
    if classify(xatol) != fcNan:
      atol = xatol
    else:
      atol = pow(max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(1.0, 0.0)), 4 / 5)
    if classify(xrtol) != fcNan:
      rtol = xrtol
    else:
      rtol = pow(max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(1.0, 0.0)), 4 / 5)
  else:
    if classify(xatol) != fcNan:
      atol = xatol
    else:
      atol = pow(max(nextafterf(1.0, Inf) - 1.0, 1.0 - nextafterf(1.0, 0.0)), 4 / 5)
    if classify(xrtol) != fcNan:
      rtol = xrtol
    else:
      rtol = pow(max(nextafterf(1.0, Inf) - 1.0, 1.0 - nextafterf(1.0, 0.0)), 4 / 5)

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



# dfree

proc dfree*[T, S: SomeFloat](f: proc(a: T): S, xs: T|(T, T)): T =

  var
    a, b: T
    fa, fb: S

  if typeof(xs) == T:
    a = xs[0]
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
    MAXCNT = 5 * ceil(-log(max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(1.0, 0.0))))

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

    let
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
    if (quadCtr > MAXQUAD) or (cnt > MAXCNT) or (classify(gamma - b) == fcZero) or (classify(gamma - b) == fcNegZero) or (classify(gamma) == fcNan):
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
      for i in ((b, fb), (bprev, fbprev), (bnext, fbnext)):
        when sizeof(T) == 8:
          if abs(i[1]) <= 8 * max(nextafter(1.0, Inf) - 1.0, 1.0 - nextafter(1.0, 0.0)):
            return i[0]
        else:
          if abs(i[1]) <= 8 * max(nextafterf(1.0, Inf) - 1.0, 1.0 - nextafterf(1.0, 0.0)):
            return i[0]
      return nan # Failed.

    if abs(fgamma) < abs(fb):
      (b, fb, a, fa) = (gamma, fgamma, b, fb)
    else:
      (a, fa) = (gamma, fgamma)

  return b
