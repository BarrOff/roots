## ==========
## bracketing
## ==========
##
## Bisection
## ---------
##
## If possible, will use the bisection method over `float64` values. The
## bisection method starts with a bracketing interval `[a,b]` and splits
## it into two intervals `[a,c]` and `[c,b]`, If `c` is not a zero, then
## one of these two will be a bracketing interval and the process
## continues. The computation of `c` is done by `middle`, which
## reinterprets floating point values as unsigned integers and splits
## there. It was contributed  by
## `Jason Merrill <https://gist.github.com/jwmerrill/9012954>`_. 
## This method avoids floating point issues and when the
## tolerances are set to zero (the default) guarantees a "best" solution
## (one where a zero is found or the bracketing interval is of the type
## `[a, nextfloat(a)]`).
##
## When tolerances are given, this algorithm terminates when the midpoint
## is approximately equal to an endpoint using absolute tolerance `xatol`
## and relative tolerance `xrtol`.
##
## When a zero tolerance is given and the values are not `Float64`
## values, this will call the `A42` method.

import math, tables
import private/utils, findZero

const
  bracketing_error = """The interval [a,b] is not a bracketing interval.
  You need f(a) and f(b) to have different signs (f(a) * f(b) < 0).
  Consider a different bracket"""

# forward declarations

proc middle*[T: SomeNumber](x, y: T): T
proc middle2*[T: SomeInteger](a, b: T): float
proc middle2*(a, b: float): float
proc middle2*(a, b: float32): float32
proc ipzero[T, S: SomeFloat](a, b, c, d: T, fa, fb, fc, fd: S, delta: T = T(0.0)): T
proc newtonQuadratic[T, S: SomeFloat, R: SomeInteger](a, b, d: T, fa, fb, fd: S,
    k: R, delta: T = T(0.0)): T
proc galdinoReduction(methods: FalsePosition, fa, fb, fx: float): float {.inline.}
proc findZero*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod,
    CF: CallableFunction[T, S]](M: A, F: CF, options: UnivariateZeroOptions[T,
    T, S, S], state: UnivariateZeroState[T, S], l: Tracks[T,
    S]|NullTracks = NullTracks()): T
proc findZero*[T, S: SomeFloat, AM: AbstractUnivariateZeroMethod,
    AN: AbstractBracketing, CF: CallableFunction[T, S]](M: AM, N: AN, F: CF,
    options: UnivariateZeroOptions[T, T, S, S], state: UnivariateZeroState[T,
    S], l: Tracks[T, S]|NullTracks = NullTracks()): T


proc logStep*[T, S: SomeFloat, A: AbstractBisection](l: Tracks[T, S], M: A,
    state: UnivariateZeroState[T, S]) =
  ## generic `logStep` function for type AbstractBisection
  add(l.xs, state.xn0)
  add(l.xs, state.xn1)

proc adjustBracket*[T: SomeFloat](x0: (T, T)): (T, T) =
  ## takes care that both bracketing values are finite
  ## and returns a sorted tuple
  var
    (u, v) = x0

  if u > v:
    let temp = v
    v = u
    u = temp

  if u == low(T) or u == high(T):
    when(sizeof(T) == 8):
      u = nextafter(cdouble(low(T)), 0.0)
    else:
      u = nextafterf(cfloat(low(T)), 0.0)

  if v == high(T) or v == low(T):
    when(sizeof(T) == 8):
      v = nextafter(cdouble(high(T)), 0.0)
    else:
      v = nextafterf(cfloat(high(T)), 0.0)

  return (u, v)


proc initState*[T, S: SomeFloat, A: AbstractBisection, CF: CallableFunction[T,
    S]](meth: A, fs: CF, x: (T, T)): UnivariateZeroState[T, S] =
  ## In `initState` the bracketing interval is left as `(a,b)` with
  ## `a`,`b` both finite and of the same sign
  let
    (x0, x1) = adjustBracket(x)
    fx0 = fs.f(x0)
    fx1 = fs.f(x1)

  if sgn(fx0) * sgn(fx1) > 0:
    raise newException(InitialValueError, bracketing_error)

  return initState(meth, fs, (x0, x1), (fx0, fx1))

proc initState*[T, S: SomeFloat, A: AbstractBisection](meth: A, fs: proc(
    a: T): S, x: (T, T)): UnivariateZeroState[T, S] =
  ## In `initState` the bracketing interval is left as `(a,b)` with
  ## `a`,`b` both finite and of the same sign
  let
    (x0, x1) = adjustBracket(x)
    fx0 = fs(x0)
    fx1 = fs(x1)

  if sgn(fx0) * sgn(fx1) > 0:
    raise newException(InitialValueError, bracketing_error)

  return initState(meth, fs, (x0, x1), (fx0, fx1))

proc initState*[T, S: SomeFloat, A: AbstractBisection, CF: CallableFunction[T,
    S]](meth: A, fs: CF, xs, fxs: (T, T)): UnivariateZeroState[T, S] =
  ## assume `xs`, `fxs`, have all been checked so that we have a bracket
  ## gives an  entry for the case where the endpoints are expensive to compute
  ## as requested in issue #156 by @greimel
  let
    (x0, x1) = xs
    (fx0, fx1) = fxs

  new(result)
  result.xn1 = x1
  result.xn0 = x0
  result.xstar = T(0)
  result.m = @[x1]
  result.fxn1 = fx1
  result.fxn0 = fx0
  result.fxstar = fx1
  result.fm = @[fx1]
  result.steps = 0
  result.fnevals = 2
  result.stopped = false
  result.xConverged = false
  result.fConverged = false
  result.convergenceFailed = false
  result.message = ""

  initState(result, meth, fs, (x0, x1), (fx0, fx1))

proc initState*[T, S: SomeFloat, A: AbstractBisection](meth: A, fs: proc(
    a: T): S, xs, fxs: (T, T)): UnivariateZeroState[T, S] =
  ## assume `xs`, `fxs`, have all been checked so that we have a bracket
  ## gives an  entry for the case where the endpoints are expensive to compute
  ## as requested in issue #156 by @greimel
  let
    (x0, x1) = xs
    (fx0, fx1) = fxs

  new(result)
  result.xn1 = x1
  result.xn0 = x0
  result.xstar = T(0)
  result.m = @[x1]
  result.fxn1 = fx1
  result.fxn0 = fx0
  result.fxstar = fx1
  result.fm = @[fx1]
  result.steps = 0
  result.fnevals = 2
  result.stopped = false
  result.xConverged = false
  result.fConverged = false
  result.convergenceFailed = false
  result.message = ""

  initState(result, meth, fs, (x0, x1), (fx0, fx1))
  return result

proc initState*[T, S: SomeFloat, A: AbstractBisection, CF: CallableFunction[T,
    S]](state: UnivariateZeroState[T, S], M: A, fs: CF, xs: (T, T)) =
  ## creates function values `fxs` for `xs`, then uses `xs` and `fxs`
  ## to initialise the state reference.
  let
    (x0, x1) = xs
    fx0 = fs.f(x0)
    fx1 = fs.f(x1)

  initState(state, M, fs, (x0, x1), (fx0, fx1))
  return

proc initState*[T, S: SomeFloat, A: AbstractBisection](
  state: UnivariateZeroState[T, S], M: A, fs: proc(a: T): S, xs: (T, T)) =
  ## creates function values `fxs` for `xs`, then uses `xs` and `fxs`
  ## to initialise the state reference.
  let
    (x0, x1) = xs
    fx0 = fs(x0)
    fx1 = fs(x1)

  initState(state, M, fs, (x0, x1), (fx0, fx1))
  return

proc initState*[T, S: SomeFloat, A: AbstractBisection, CF: CallableFunction[T,
    S]](state: UnivariateZeroState[T, S], M: A, fs: CF, xs: (T, T), fxs: (S, S)) =
  var
    (x0, x1) = xs
    (fx0, fx1) = fxs
    m, fm: T

  if sgn(fx0) * sgn(fx1) > 0:
    raise newException(InitialValueError, bracketing_error)

  if sgn(fx0) * sgn(fx1) == 0:
    if fx0 == 0:
      m = x0
      fm = fx0
    else:
      m = x1
      fm = fx1

    state.fConverged = true
    state.xstar = m
    state.fxstar = fm
    return

  if sgn(x0) * sgn(x1) < 0:
    m = 0.0
    fm = fs.f(m)
    incfn(state)
    if sgn(fx0) * sgn(fm) < 0:
      x1 = m
      fx1 = fm
    elif sgn(fx0) * sgn(fm) > 0:
      x0 = m
      fx0 = fm
    else:
      state.message = "Exact zero found"
      state.xstar = m
      state.fxstar = fm
      state.fConverged = true
      state.xConverged = true
      return

  m = middle(x0, x1)
  fm = fs.f(m)
  incfn(state)

  initState(state, x1, x0, @[m], fx1, fx0, @[fm])
  return

proc initState*[T, S: SomeFloat, A: AbstractBisection](
  state: UnivariateZeroState[T, S], M: A, fs: proc(a: S): T, xs: (T, T), fxs: (S, S)) =
  var
    (x0, x1) = xs
    (fx0, fx1) = fxs
    m, fm: T

  if sgn(fx0) * sgn(fx1) > 0:
    raise newException(InitialValueError, bracketing_error)

  if sgn(fx0) * sgn(fx1) == 0:
    if fx0 == 0:
      m = x0
      fm = fx0
    else:
      m = x1
      fm = fx1

    state.fConverged = true
    state.xstar = m
    state.fxstar = fm
    return

  if sgn(x0) * sgn(x1) < 0:
    m = 0.0
    fm = fs(m)
    incfn(state)
    if sgn(fx0) * sgn(fm) < 0:
      x1 = m
      fx1 = fm
    elif sgn(fx0) * sgn(fm) > 0:
      x0 = m
      fx0 = fm
    else:
      state.message = "Exact zero found"
      state.xstar = m
      state.fxstar = fm
      state.fConverged = true
      state.xConverged = true
      return

  m = middle(x0, x1)
  fm = fs(m)
  incfn(state)

  initState(state, x1, x0, @[m], fx1, fx0, @[fm])
  return



proc defaultTolerances*[Ti, Si: SomeFloat](M: Bisection | BisectionExact,
    T: typedesc[Ti], S: typedesc[Si]): (Ti, Ti, Si, Si, int, int, bool) =
  ## for Bisection, the defaults are zero tolerances and `strict=true`
  ##
  ## For `Bisection` (or `BisectionExact`), when the `x` values are of type
  ## `Float64`, `Float32` the default tolerances are zero and there is no limit
  ## on the number of iterations or function evalutions. In this case, the
  ## algorithm is guaranteed to converge to an exact zero, or a point where
  ## the function changes sign at one of the answer's adjacent floating
  ## point values.
  ##
  ## For other types,  the `A42` method (with its tolerances) is used.
  let
    xatol = Ti(0)
    xrtol = Ti(0)
    atol = Si(0)
    rtol = Si(0)
    maxevals = high(int)
    maxfnevals = high(int)
    strict = true

  return((xatol, xrtol, atol, rtol, maxevals, maxfnevals, strict))

proc middle*[T: SomeNumber](x, y: T): T =
  ## find middle of (a,b) with convention that:
  ##
  ## * if `a`, `b` infinite, they are made finite
  ## * if `a`,`b` of different signs, middle is 0
  ## * middle falls back to `a/2 + b/2`, but
  ##   for `float64` values, middle is over the
  ##   reinterpreted unsigned integer.
  var
    a, b: T
  if classify(x) == fcInf or classify(x) == fcNegInf:
    when sizeof(T) == 8:
      a = nextafter(cdouble(x), cdouble(0.0))
    else:
      a = nextafterf(cfloat(x), cfloat(0.0))
  else:
    a = x
  if classify(y) == fcInf or classify(y) == fcNegInf:
    when sizeof(T) == 8:
      b = nextafter(cdouble(y), cdouble(0.0))
    else:
      b = nextafterf(cfloat(y), cfloat(0.0))
  else:
    b = y

  if sgn(a) * sgn(b) < 0:
    return T(0.0)
  else:
    return middle2(a, b)

proc middle2*[T: SomeInteger](a, b: T): float =
  return 0.5 * float(a) + 0.5 * float(b)

proc middle2*[T: float32, S: uint32](t: typedesc[T], s: typedesc[S], a, b: T): T =
  ## Use the usual float rules for combining non-finite numbers
  ## do division over unsigned integers with bit shift
  let
    aInt = cast[S](a)
    bInt = cast[S](b)
    mid = (aInt + bInt) shr 1

  # reinterpret in original floating point
  return T(sgn(a + b)) * cast[T](mid)

proc middle2*[T: float, S: uint](t: typedesc[T], s: typedesc[S], a, b: T): T =
  ## Use the usual float rules for combining non-finite numbers
  ## do division over unsigned integers with bit shift
  let
    aInt = cast[S](a)
    bInt = cast[S](b)
    mid = (aInt + bInt) shr 1

  # reinterpret in original floating point
  return T(sgn(a + b)) * cast[T](mid)

proc middle2*(a, b: float): float =
  ## find middle assuming `a`,`b` same sign, finite
  ## Alternative "mean" definition that operates on the binary representation
  ## of a float. Using this definition, bisection will never take more than
  ## 64 steps (over float64)
  return middle2(float, uint, a, b)

proc middle2*(a, b: float32): float32 =
  ## find middle assuming `a`,`b` same sign, finite
  ## Alternative "mean" definition that operates on the binary representation
  ## of a float. Using this definition, bisection will never take more than
  ## 64 steps (over float64)
  return middle2(float32, uint32, a, b)

proc assessConvergence*[T, S: SomeFloat](M: Bisection,
    state: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]): bool =
  ## the method converges,
  ## as we bound between `x0`, `nextfloat(x0)` is not measured by `eps()`, but
  ## `eps(x0)`
  var
    M: BisectionExact
  if assessConvergence(M, state, options):
    return true

  let
    x0 = state.xn0
    x1 = state.xn1
    xm = state.m[0]
    xtol = max(options.xabstol, max(abs(x0), abs(x1)) * options.xreltol)
    xConverged = x1 - x0 < xtol

  if xConverged:
    state.message = ""
    state.xstar = xm
    state.xConverged = true
    return true

  let
    fm = state.fm[0]
    ftol = max(options.abstol, max(abs(x0), abs(x1)) * options.reltol)
    fConverged = abs(fm) < ftol

  if fConverged:
    state.message = ""
    state.xstar = xm
    state.fxstar = fm
    state.fConverged = fConverged
    return true

  return false

proc assessConvergence*[T, S](M: BisectionExact, state: UnivariateZeroState[T,
    S], options: UnivariateZeroOptions[T, T, S, S]): bool =
  ## for exact convergence, we can skip some steps
  if state.xConverged:
    return true

  let
    x0 = state.xn0
    xm = state.m[0]
    x1 = state.xn1
    y0 = state.fxn0
    ym = state.fm[0]
    y1 = state.fxn1


  for i in @[(x0, y0), (xm, ym), (x1, y1)]:
    if classify(abs(i[1])) == fcZero or classify(i[1]) == fcNan:
      state.fConverged = true
      state.xConverged = true
      state.xstar = i[0]
      state.fxstar = i[1]
      return true

  if x0 < xm and xm < x1:
    return false

  state.xstar = x1
  state.fxstar = ym
  state.xConverged = true
  return true

proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](M: Bisection |
    BisectionExact, fs: CF, o: UnivariateZeroState[T, S],
    options: UnivariateZeroOptions[T, T, S, S]) =
  let
    y0 = o.fxn0
    ym = o.fm[0]
  var
    m = o.m[0]

  if sgn(y0) * sgn(ym) < 0:
    o.xn1 = m
    o.fxn1 = ym
  else:
    o.xn0 = m
    o.fxn0 = ym

  m = middle2(o.xn0, o.xn1)
  let
    fm = fs.f(m)

  o.m[0] = m
  o.fm[0] = fm
  incfn(o)

  return

proc updateState*[T, S: SomeFloat](M: Bisection | BisectionExact, fs: proc(
    a: T): S, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T,
        S, S]) =
  let
    y0 = o.fxn0
    ym = o.fm[0]
  var
    m = o.m[0]

  if sgn(y0) * sgn(ym) < 0:
    o.xn1 = m
    o.fxn1 = ym
  else:
    o.xn0 = m
    o.fxn0 = ym

  m = middle2(o.xn0, o.xn1)
  let
    fm = fs(m)

  o.m[0] = m
  o.fm[0] = fm
  incfn(o)

  return

proc findZero*[T, S: SomeFloat, AT: Tracks[T, S] or NullTracks,
    CF: CallableFunction[T, S]](fs: CF, x0: (T, T), methods: Bisection,
    tracks: AT = NullTracks(), verbose = false, kwargs: varargs[
    UnivariateZeroOptions[T, T, S, S]]): float =
  ## Bisection has special cases
  ## for zero tolerance, we have either `BisectionExact` or `A42` methods
  ## for non-zero tolerances, we have use thegeneral Bisection method
  let
    x = adjustBracket(x0)
    F = callable_functions(fs)
    state = initState(methods, F, x)

  var
    options: UnivariateZeroOptions[T, T, S, S]

  if len(kwargs) == 0:
    options = initOptions(methods, state)
  else:
    options = kwargs[0]

  # check if tolerances are exactly 0
  let
    iszeroTol = options.xabstol == 0.0 and options.xreltol == 0.0 and
        options.abstol == 0.0 and options.reltol == 0.0

  if verbose and typeof(tracks) is NullTracks:
    var
      l: Tracks[T, S]

    new(l)
    if iszeroTol:
      let M: A42 = A42()
      return findZero(F, x, M, l, verbose)

    discard findZero(methods, F, options, state, l)

    when l is Tracks[T, S]:
      if verbose:
        var M: AbstractBracketing
        showTrace(methods, M, state, l)

    return state.xn1
  else:
    let
      l = tracks

    if iszeroTol:
      let M: A42 = A42()
      return findZero(F, x, M, l, verbose)

    discard findZero(methods, F, options, state, l)

    when l is Tracks[T, S]:
      if verbose:
        var M: AbstractBracketing
        showTrace(methods, M, state, l)

  return state.xstar

proc findZero*[T, S: SomeFloat, AT: Tracks[T, S] or NullTracks](fs: proc (
    a: T): S, x0: (T, T), methods: Bisection, tracks: AT = NullTracks(),
    verbose = false, kwargs: varargs[UnivariateZeroOptions[T, T, S, S]]): float =
  ## Bisection has special cases
  ## for zero tolerance, we have either `BisectionExact` or `A42` methods
  ## for non-zero tolerances, we have use thegeneral Bisection method

  let
    x = adjustBracket(x0)
    F = callable_functions(fs)
    state = initState(methods, F, x)

  var
    options: UnivariateZeroOptions[T, T, S, S]

  if len(kwargs) == 0:
    options = initOptions(methods, state)
  else:
    options = kwargs[0]

  let
    iszeroTol = options.xabstol == 0.0 and options.xreltol == 0.0 and
        options.abstol == 0.0 and options.reltol == 0.0

  if verbose and typeof(tracks) is NullTracks:
    var
      l: Tracks[T, S]

    new(l)
    if iszeroTol:
      let M: A42 = A42()
      return findZero(F, x, M, l, verbose)

    discard findZero(methods, F, options, state, l)

    when l is Tracks[T, S]:
      if verbose:
        var M: AbstractBracketing
        showTrace(methods, M, state, l)

    return state.xn1
  else:
    let
      l = tracks

    if iszeroTol:
      let M: A42 = A42()
      return findZero(F, x, M, l, verbose)

    discard findZero(methods, F, options, state, l)

    when l is Tracks[T, S]:
      if verbose:
        var M: AbstractBracketing
        showTrace(methods, M, state, l)

  return state.xstar

proc findZero*[T, S: SomeInteger, A: AbstractBracketing](fs: proc(
    a: float): float, x0: (T, S), M: A, verbose = false, kwargs: varargs[
    UnivariateZeroOptions[float, float, float, float]]): float =
  if len(kwargs) == 0:
    return findZero(fs, (float(x0[0]), float(x0[1])), M, verbose = verbose)
  else:
    return findZero(fs, (float(x0[0]), float(x0[1])), M, verbose = verbose,
        kwargs = kwargs[0])

proc findZero*[T, S: SomeInteger](fs: proc(a: float): float, x0: (T, S),
    verbose: bool = false, kwargs: varargs[UnivariateZeroOptions[float, float,
    float, float]]): float =
  if len(kwargs) == 0:
    return findZero(fs, (float(x0[0]), float(x0[1])), verbose = verbose)
  else:
    return findZero(fs, (float(x0[0]), float(x0[1])), verbose = verbose,
        kwargs = kwargs[0])

proc findZero*[T: SomeInteger, A: AbstractNonBracketing](fs: proc(
    a: float): float, x0: T, M: A, verbose = false, kwargs: varargs[
    UnivariateZeroOptions[float, float, float, float]]): float =
  if len(kwargs) == 0:
    return findZero(fs, float(x0), M, verbose = verbose)
  else:
    return findZero(fs, float(x0), M, verbose = verbose, kwargs = kwargs[0])

proc findZero*[T: SomeInteger](fs: proc(a: float): float, x0: T,
    verbose: bool = false, kwargs: varargs[UnivariateZeroOptions[float, float,
    float, float]]): float =
  if len(kwargs) == 0:
    return findZero(fs, float(x0), verbose = verbose)
  else:
    return findZero(fs, float(x0), verbose = verbose, kwargs = kwargs[0])

proc findZero*[T, S: SomeNumber, SI: proc(a: SomeInteger): SomeNumber|proc(
    a: SomeNumber): SomeInteger, Q: SomeInteger](fs: SI, x0: (T, S),
    verbose: bool = false, kwargs: varargs[UnivariateZeroOptions[float, float,
    float, float]]): float =
  echo "The function may not use integers as domain or codomain."

  return float(NaN)

proc findZero*[T, S: SomeNumber, SI: proc(a: SomeInteger): SomeNumber|proc(
    a: SomeNumber): SomeInteger, A: AbstractBracketing](fs: SI, x0: (T, S),
    M: A, verbose: bool = false, kwargs: varargs[UnivariateZeroOptions[float,
    float, float, float]]): float =
  echo "The function may not use integers as domain or codomain."

  return float(NaN)

## A42
## ----
##
## a provided interval `[a,b]`, without requiring derivatives. It is based
## on algorithm 4.2 described in: G. E. Alefeld, F. A. Potra, and Y. Shi,
## "Algorithm 748: enclosing zeros of continuous functions," ACM
## Trans. Math. Softw. 21, 327–344 (1995),
## DOI: `10.1145/210089.210111 <https://doi.org/10.1145/210089.210111>`_.
## Originally by John Travers.

proc isBracket[T: SomeNumber](fa, fb: T): bool {.inline.} =
  return sgn(fa) * sgn(fb) < 0

proc fAB[T, S: SomeFloat](a, b: T, fa, fb: S): float {.inline.} =
  ## `f[a,` b]
  return float(fb - fa) / float(b - a)

proc fABD[T, S: SomeFloat](a, b, d: T, fa, fb, fd: S): float {.inline.} =
  ## `f[a,b,d]`
  let
    fabi = fAB(a, b, fa, fb)
    fbdi = fAB(b, d, fb, fd)
  return (fbdi - fabi) / (d - a)

proc secantStep[T, S: SomeFloat](a, b: T, fa, fb: S): T {.inline.} =
  ## a bit better than `a - fa/f_ab`
  return a - T(fa * (b - a) / (fb - fa))

proc bracket[T, S: SomeFloat](a, b, c: T, fa, fb, fc: S): (T, T, T, S, S, S) =
  ## assume `fc != 0`
  ## return `a1,b1,d` with `a < a1 <  < b1 < b, d` not there
  if isBracket(fa, fc):
    return (a, c, b, fa, fc, fb)
  else:
    return (c, b, a, fc, fb, fa)

proc takeA42Step[T, S: SomeFloat](a, b, d, ee: T, fa, fb, fd, fe: S,
    delta: T = T(0.0)): T =
  ## Cubic if possible, if not, quadratic(3)
  var
    r = ipzero(a, b, d, ee, fa, fb, fd, fe, delta)

  if a + 2 * delta < r and r < b - 2 * delta:
    return r
  r = newtonQuadratic(a, b, d, fa, fb, fd, 3, delta)
  return r

proc ipzero[T, S: SomeFloat](a, b, c, d: T, fa, fb, fc, fd: S, delta: T = T(0.0)): T =
  let
    Q11 = (c - d) * fc / (fd - fc)
    Q21 = (b - c) * fb / (fc - fb)
    Q31 = (a - b) * fa / (fb - fa)
    D21 = (b - c) * fc / (fc - fb)
    D31 = (a - b) * fb / (fb - fa)
    Q22 = (D21 - Q11) * fb / (fd - fb)
    Q32 = (D31 - Q21) * fa / (fc - fa)
    D32 = (D31 - Q21) * fc / (fc - fa)
    Q33 = (D32 - Q22) * fa / (fd - fa)
    ci = a + (Q31 + Q32 + Q33)

  if a + 2 * delta < ci and ci < b - 2 * delta:
    return ci

  return newtonQuadratic(a, b, d, fa, fb, fd, 3, delta)

proc newtonQuadratic[T, S: SomeFloat, R: SomeInteger](a, b, d: T, fa, fb, fd: S,
    k: R, delta: T = T(0.0)): T =
  ## return `c` in `(a+delta, b-delta)`
  ## adds part of `bracket` from paper with `delta`
  let
    A = fABD(a, b, d, fa, fb, fd)

  var
    r: T

  if isBracket(A, fa):
    r = b
  else:
    r = a

  # use quadratic step; if that fails, use secant step; if that fails, bisection
  if classify(A) == fcNormal:
    let
      B = fAB(a, b, fa, fb)

    for i in 1..k:
      let
        Pr = fa + B * (r - a) + A * (r - a) * (r - b)
        Prp = (B + A * (2 * r - a - b))
      r -= Pr / Prp

    if a + 2 * delta < r and r < b - 2 * delta:
      return r

  # try secant step
  r = secantStep(a, b, fa, fb)

  if a + 2 * delta < r and r < b - 2 * delta:
    return r

  return middle(a, b)

proc initState*[T, S: SomeFloat, A: AbstractAlefeldPotraShi,
    CF: CallableFunction[T, S]](M: A, f: CF, xs: (T, T)): UnivariateZeroState[
    float, float] =
  var
    u = float(xs[0])
    v = float(xs[1])

  if u > v:
    var
      temp = u
    u = v
    v = temp

  let
    fu = f.f(u)
    fv = f.f(v)

  if not(isBracket(fu, fv)):
    raise newException(InitialValueError, bracketing_error)

  new(result)
  result.xn1 = v
  result.xn0 = u
  result.xstar = T(0)
  result.m = @[v, v]
  result.fxn1 = fv
  result.fxn0 = fu
  result.fxstar = fv
  result.fm = @[fv, fv]
  result.steps = 0
  result.fnevals = 2
  result.stopped = false
  result.xConverged = false
  result.fConverged = false
  result.convergenceFailed = false
  result.message = ""

  initState(result, M, f, (u, v), false)
  return result

proc initState*[T, S: SomeFloat, A: AbstractAlefeldPotraShi](M: A, f: proc(
    a: T): S, xs: (T, T)): UnivariateZeroState[float, float] =
  var
    u = float(xs[0])
    v = float(xs[1])

  if u > v:
    var
      temp = u
    u = v
    v = temp

  let
    fu = f(u)
    fv = f(v)

  if not(isBracket(fu, fv)):
    raise newException(InitialValueError, bracketing_error)

  new(result)
  result.xn1 = v
  result.xn0 = u
  result.xstar = T(0)
  result.m = @[v, v]
  result.fxn1 = fv
  result.fxn0 = fu
  result.fxstar = fv
  result.fm = @[fv, fv]
  result.steps = 0
  result.fnevals = 2
  result.stopped = false
  result.xConverged = false
  result.fConverged = false
  result.convergenceFailed = false
  result.message = ""

  initState(result, M, f, (u, v), false)
  return result

proc initState*[T, S: SomeFloat, A: AbstractAlefeldPotraShi,
    CF: CallableFunction[T, S]](state: UnivariateZeroState[T, S], aaps: A,
    f: CF, xs: (T, T), computeFx = true) =
  ## secant step, then bracket for initial setup
  var
    a, b, c, d, ee: T
    fa, fb, fc, fd, fe: S

  if not(computeFx):
    a = state.xn0
    b = state.xn1
    fa = state.fxn0
    fb = state.fxn1
  else:
    a = xs[0]
    b = xs[1]

    if a > b:
      var
        temp = a
      a = b
      b = temp
    fa = f.f(a)
    fb = f.f(b)
    state.fnevals = 2
    if not(isBracket(fa, fb)):
      raise newException(InitialValueError, bracketing_error)

  c = middle(a, b)
  fc = f.f(c)
  incfn(state)

  (a, b, d, fa, fb, fd) = bracket(a, b, c, fa, fb, fc)
  ee = d
  fe = fd

  initState(state, b, a, @[d, ee], fb, fa, @[fd, fe])
  state.steps = 0
  state.stopped = false
  state.xConverged = false
  state.fConverged = false
  state.convergenceFailed = false

proc initState*[T, S: SomeFloat, A: AbstractAlefeldPotraShi](
  state: UnivariateZeroState[T, S], aaps: A, f: proc(a: T): S, xs: (T, T),
    computeFx = true) =
  ## secant step, then bracket for initial setup
  var
    a, b, c, d, ee: T
    fa, fb, fc, fd, fe: S

  if not(computeFx):
    a = state.xn0
    b = state.xn1
    fa = state.fxn0
    fb = state.fxn1
  else:
    a = xs[0]
    b = xs[1]

    if a > b:
      var
        temp = a
      a = b
      b = temp
    fa = f(a)
    fb = f(b)
    state.fnevals = 2
    if not(isBracket(fa, fb)):
      raise newException(InitialValueError, bracketing_error)

  c = middle(a, b)
  fc = f(c)
  incfn(state)

  (a, b, d, fa, fb, fd) = bracket(a, b, c, fa, fb, fc)
  ee = d
  fe = fd

  initState(state, b, a, @[d, ee], fb, fa, @[fd, fe])
  state.steps = 0
  state.stopped = false
  state.xConverged = false
  state.fConverged = false
  state.convergenceFailed = false



proc defaultTolerances*(M: AbstractAlefeldPotraShi, T, S: typedesc): (T, T, S,
    S, int, int, bool) =
  ## The default tolerances for Alefeld, Potra, and Shi methods are
  ## `xatol=zero(T)`, `xrtol=eps(T)/2`, `atol= zero(S), and rtol=zero(S)`, with
  ## appropriate units; `maxevals=45`, `maxfnevals = Inf`; and `strict=true`.
  let
    xatol = T(0.0)
    atol = S(0.0)
    rtol = S(0.0)
    maxevals = 45
    maxfnevals = high(int)
    strict = true

  when sizeof(T) == 8:
    let
      xrtol = (nextafter(1.0, 2.0) - 1.0) / 2
  else:
    let
      xrtol = (nextafterf(1.0, 2.0) - 1.0) / 2

  return (xatol, xrtol, atol, rtol, maxevals, maxfnevals, strict)

proc checkZero[T, S: SomeFloat, A: AbstractBracketing](M: A,
    state: UnivariateZeroState[T, S], c: T, fc: S): bool =
  ## convergence is much different here
  if classify(c) == fcNan:
    state.stopped = true
    state.xstar = c
    state.fxstar = fc
    state.message &= "NaN encountered. "
    return true
  elif classify(c) == fcInf or classify(c) == fcNegInf:
    state.stopped = true
    state.xstar = c
    state.fxstar = fc
    state.message &= "Inf encountered. "
    return true
  elif classify(fc) == fcZero or classify(fc) == fcNegZero:
    state.stopped = true
    state.message &= "Exact zero found. "
    state.xstar = c
    state.fxstar = fc
    return true
  else:
    return false

proc assessConvergence*[T, S: SomeFloat, A: AbstractAlefeldPotraShi](M: A,
    state: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]): bool =
  if state.stopped or state.xConverged or state.fConverged:
    # if classify(state.xstar) == fcNan:
    #   (state.xstar, state.fxstar) = (state.xn1, state.fxn1)
    return true

  if state.steps > options.maxevals:
    state.stopped = true
    state.message &= "Too many steps taken. "
    return true

  if state.fnevals > options.maxfnevals:
    state.stopped = true
    state.message &= "Too many function evaluations taken. "
    return true

  var
    (u, fu) = chooseSmallest(state.xn0, state.xn1, state.fxn0, state.fxn1)

  # (u, fu) = chooseSmallest(u, state.m[0], fu, state.fm[0])

  if abs(fu) <= max(options.abstol, S(abs(u)) * options.reltol):
    state.fConverged = true
    state.xstar = u
    state.fxstar = fu
    if fu == S(0):
      state.message &= "Exact zero found. "
    return true

  let
    a = state.xn0
    b = state.xn1
    mx = max(abs(a), abs(b))
  when sizeof(T) == 8:
    let
      tol = max(options.xabstol, max(mx * options.xreltol, T(sgn(
          options.xreltol)) * max(nextafter(mx, Inf) - mx, mx - nextafter(mx, -Inf))))
  else:
    let
      tol = max(options.xabstol, max(mx * options.xreltol, T(sgn(
          options.xreltol)) * max(nextafterf(mx, Inf) - mx, mx - nextafterf(mx, -Inf))))

  if abs(b - a) <= 2 * tol:
    state.xstar = u
    state.fxstar = fu
    state.xConverged = true
    return true

  return false

proc logStep*[T, S: SomeFloat, A: AbstractAlefeldPotraShi](l: Tracks[T, S],
    M: A, state: UnivariateZeroState[T, S]) =
  ## initial step, needs to log a,b,d
  let
    a = state.xn0
    b = state.xn1
    c = state.m[0]
  if a < b and b < c:
    add(l.xs, a)
    add(l.xs, c)
  elif a < c and c < b:
    add(l.xs, a)
    add(l.xs, b)
  elif c < b and b < a:
    add(l.xs, c)
    add(l.xs, a)
  elif b < c and c < a:
    add(l.xs, b)
    add(l.xs, a)
  elif b < a and a < c:
    add(l.xs, b)
    add(l.xs, c)
  else:
    add(l.xs, c)
    add(l.xs, b)

  add(l.xs, a)
  add(l.xs, b)

proc updateState[T, S: SomeFloat, CF: CallableFunction[T, S]](M: A42, f: CF,
    state: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  ## Main algorithm for A42 method
  var
    a = state.xn0
    b = state.xn1
    d = state.m[0]
    ee = state.m[1]
    fa = state.fxn0
    fb = state.fxn1
    fd = state.fm[0]
    fe = state.fm[1]
    c: T
    fc: S

  let
    an = a
    bn = b
    mu = 0.5
    lambda = 0.7
    tole = max(options.xabstol, max(abs(a), abs(b)) * options.xreltol)
    delta = lambda * tole

  if state.steps < 1:
    c = newtonQuadratic(a, b, d, fa, fb, fd, 2)
  else:
    c = ipzero(a, b, d, ee, fa, fb, fd, fe)

  fc = f.f(c)
  incfn(state)
  if checkZero(M, state, c, fc):
    return

  var
    (ab, bb, db, fab, fbb, fdb) = bracket(a, b, c, fa, fb, fc)
    eb = d
    feb = fd
    cb = takeA42Step(ab, bb, db, eb, fab, fbb, fdb, feb, delta)
    fcb = f.f(cb)
  incfn(state)
  if checkZero(M, state, cb, fcb):
    # tighten up bracket
    (state.xn0, state.xn1, state.m[0]) = (ab, bb, db)
    (state.fxn0, state.fxn1, state.fm[0]) = (fab, fbb, fdb)
    return

  (ab, bb, db, fab, fbb, fdb) = bracket(ab, bb, cb, fab, fbb, fcb)

  var
    (u, fu) = chooseSmallest(ab, bb, fab, fbb)

  cb = u - 2 * fu * (bb - ab) / (fbb - fab)
  var
    ch = cb
  if abs(cb - u) > 0.5 * abs(b - a):
    ch = middle(an, bn)
  var
    fch = f.f(cb)
  incfn(state)
  if checkZero(M, state, ch, fch):
    # tighten up bracket
    (state.xn0, state.xn1, state.m[0]) = (ab, bb, db)
    (state.fxn0, state.fxn1, state.fm[0]) = (fab, fbb, fdb)
    return

  var
    (ah, bh, dh, fah, fbh, fdh) = bracket(ab, bb, ch, fab, fbb, fch)

  if bh - ah < mu * (b - a):
    a = ah
    b = bh
    d = dh
    ee = db
    fa = fah
    fb = fbh
    fd = fdh
    fe = fdb
  else:
    let
      m = middle(ah, bh)
      fm = f.f(m)
    incfn(state)
    ee = dh
    fe = fdh
    (a, b, d, fa, fb, fd) = bracket(ah, bh, m, fah, fbh, fm)

  state.xn0 = a
  state.xn1 = b
  state.m[0] = d
  state.m[1] = ee
  state.fxn0 = fa
  state.fxn1 = fb
  state.fm[0] = fd
  state.fm[1] = fe

  return
proc updateState[T, S: SomeFloat](M: A42, f: proc(a: T): S,
    state: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  ## Main algorithm for A42 method
  var
    a = state.xn0
    b = state.xn1
    d = state.m[0]
    ee = state.m[1]
    fa = state.fxn0
    fb = state.fxn1
    fd = state.fm[0]
    fe = state.fm[1]
    c: T
    fc: S

  let
    an = a
    bn = b
    mu = 0.5
    lambda = 0.7
    tole = max(options.xabstol, max(abs(a), abs(b)) * options.xreltol)
    delta = lambda * tole

  if state.steps < 1:
    c = newtonQuadratic(a, b, d, fa, fb, fd, 2)
  else:
    c = ipzero(a, b, d, ee, fa, fb, fd, fe)

  fc = f(c)
  incfn(state)
  if checkZero(M, state, c, fc):
    return

  var
    (ab, bb, db, fab, fbb, fdb) = bracket(a, b, c, fa, fb, fc)
    eb = d
    feb = fd
    cb = takeA42Step(ab, bb, db, eb, fab, fbb, fdb, feb, delta)
    fcb = f(cb)
  incfn(state)
  if checkZero(M, state, cb, fcb):
    # tighten up bracket
    (state.xn0, state.xn1, state.m[0]) = (ab, bb, db)
    (state.fxn0, state.fxn1, state.fm[0]) = (fab, fbb, fdb)
    return

  (ab, bb, db, fab, fbb, fdb) = bracket(ab, bb, cb, fab, fbb, fcb)

  var
    (u, fu) = chooseSmallest(ab, bb, fab, fbb)

  cb = u - 2 * fu * (bb - ab) / (fbb - fab)
  var
    ch = cb
  if abs(cb - u) > 0.5 * abs(b - a):
    ch = middle(an, bn)
  var
    fch = f(cb)
  incfn(state)
  if checkZero(M, state, ch, fch):
    # tighten up bracket
    (state.xn0, state.xn1, state.m[0]) = (ab, bb, db)
    (state.fxn0, state.fxn1, state.fm[0]) = (fab, fbb, fdb)
    return

  var
    (ah, bh, dh, fah, fbh, fdh) = bracket(ab, bb, ch, fab, fbb, fch)

  if bh - ah < mu * (b - a):
    a = ah
    b = bh
    d = dh
    ee = db
    fa = fah
    fb = fbh
    fd = fdh
    fe = fdb
  else:
    let
      m = middle(ah, bh)
      fm = f(m)
    incfn(state)
    ee = dh
    fe = fdh
    (a, b, d, fa, fb, fd) = bracket(ah, bh, m, fah, fbh, fm)

  state.xn0 = a
  state.xn1 = b
  state.m[0] = d
  state.m[1] = ee
  state.fxn0 = fa
  state.fxn1 = fb
  state.fm[0] = fd
  state.fm[1] = fe

  return


## AlefeldPotraShi
## ---------------
##
## Follows algorithm in "ON ENCLOSING SIMPLE ROOTS OF NONLINEAR
## EQUATIONS", by Alefeld, Potra, Shi; DOI:
## `10.1090/S0025-5718-1993-1192965-2 <https://doi.org/10.1090/S0025-5718-1993-1192965-2>`_.
## Efficiency is 1.618. Less efficient, but can be faster than the `A42` method.
## Originally by John Travers.
proc updateState[T, S: SomeFloat, CF: CallableFunction[T, S]](
  M: AlefeldPotraShi, f: CF, state: UnivariateZeroState[T, S],
    options: UnivariateZeroOptions[T, T, S, S]) =
  ## 3, maybe 4, functions calls per step

  var
    a = state.xn0
    b = state.xn1
    d = state.m[0]
    fa = state.fxn0
    fb = state.fxn1
    fd = state.fm[0]

  let
    mu = 0.5
    lambda = 0.7
    tole = max(options.xabstol, max(abs(a), abs(b)) * options.xreltol)
    delta = lambda * tole

  var
    c = newtonQuadratic(a, b, d, fa, fb, fd, 2, delta)
    fc = f.f(c)
  incfn(state)
  if checkZero(M, state, c, fc):
    return

  (a, b, d, fa, fb, fd) = bracket(a, b, c, fa, fb, fc)
  c = newtonQuadratic(a, b, d, fa, fb, fd, 3, delta)
  fc = f.f(c)
  incfn(state)
  if checkZero(M, state, c, fc):
    # tighten up bracket
    (state.xn0, state.xn1, state.m[0]) = (a, b, d)
    (state.fxn0, state.fxn1, state.fm[0]) = (fa, fb, fd)
    return

  (a, b, d, fa, fb, fd) = bracket(a, b, c, fa, fb, fc)

  let
    (u, fu) = chooseSmallest(a, b, fa, fb)
  c = u - 2 * fu * (b - a) / (fb - fa)
  if abs(c - u) > 0.5 * (b - a):
    c = middle(a, b)

  fc = f.f(c)
  incfn(state)
  if checkZero(M, state, c, fc):
    # tighten up bracket
    (state.xn0, state.xn1, state.m[0]) = (a, b, d)
    (state.fxn0, state.fxn1, state.fm[0]) = (fa, fb, fd)
    return

  let
    (ahat, bhat, dhat, fahat, fbhat, fdhat) = bracket(a, b, c, fa, fb, fc)

  if bhat - ahat < mu * (b - a):
    a = ahat
    b = bhat
    d = dhat
    fa = fahat
    fb = fbhat
    fd = fdhat
  else:
    let
      m = middle(ahat, bhat)
      fm = f.f(m)
    incfn(state)
    (a, b, d, fa, fb, fd) = bracket(ahat, bhat, m, fahat, fbhat, fm)

  state.xn0 = a
  state.xn1 = b
  state.m[0] = d
  state.fxn0 = fa
  state.fxn1 = fb
  state.fm[0] = fd

  return

proc updateState[T, S: SomeFloat](M: AlefeldPotraShi, f: proc(a: T): S,
    state: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =

  var
    a = state.xn0
    b = state.xn1
    d = state.m[0]
    fa = state.fxn0
    fb = state.fxn1
    fd = state.fm[0]

  let
    mu = 0.5
    lambda = 0.7
    tole = max(options.xabstol, max(abs(a), abs(b)) * options.xreltol)
    delta = lambda * tole

  var
    c = newtonQuadratic(a, b, d, fa, fb, fd, 2, delta)
    fc = f(c)
  incfn(state)
  if checkZero(M, state, c, fc):
    return

  (a, b, d, fa, fb, fd) = bracket(a, b, c, fa, fb, fc)
  c = newtonQuadratic(a, b, d, fa, fb, fd, 3, delta)
  fc = f(c)
  incfn(state)
  if checkZero(M, state, c, fc):
    return

  (a, b, d, fa, fb, fd) = bracket(a, b, c, fa, fb, fc)

  let
    (u, fu) = chooseSmallest(a, b, fa, fb)
  c = u - 2 * fu * (b - a) / (fb - fa)
  if abs(c - u) > 0.5 * (b - a):
    c = middle(a, b)

  fc = f(c)
  incfn(state)
  if checkZero(M, state, c, fc):
    return

  let
    (ahat, bhat, dhat, fahat, fbhat, fdhat) = bracket(a, b, c, fa, fb, fc)

  if bhat - ahat < mu * (b - a):
    a = ahat
    b = bhat
    d = dhat
    fa = fahat
    fb = fbhat
    fd = fdhat
  else:
    let
      m = middle(ahat, bhat)
      fm = f(m)
    incfn(state)
    (a, b, d, fa, fb, fd) = bracket(ahat, bhat, m, fahat, fbhat, fm)

  state.xn0 = a
  state.xn1 = b
  state.m[0] = d
  state.fxn0 = fa
  state.fxn1 = fb
  state.fm[0] = fd

  return


proc findZero*[T, S: SomeFloat](f: proc(a: S): T, x0: (S, S), verbose = false,
    kwargs: varargs[UnivariateZeroOptions[T, T, T, T]]): T =
  let M = Bisection()
  if len(kwargs) == 0:
    return findZero(f, x0, M, verbose = verbose)
  return findZero(f, x0, M, verbose = verbose, kwargs = kwargs[0])

proc runBisection*[T, S](f: proc(a: T): S, xs: (T, T),
                         state: UnivariateZeroState[T, S],
                         options: UnivariateZeroOptions[T, T, S, S]) =
  var
    M: AlefeldPotraShi

  runBisection(M, f, xs, state, options)

## Brent
## -----
##
## An implementation of
## `Brent's <https://en.wikipedia.org/wiki/Brent%27s_method>`_ (or Brent-Dekker)
## method. This method uses a choice of inverse quadratic interpolation or a
## secant step, falling back on bisection if necessary.

proc logStep*[T, S: SomeFloat](l: Tracks[T, S], M: Brent,
    state: UnivariateZeroState[T, S]) =
  let
    a = state.xn0
    b = state.xn1
  var
    u, v: T
  if a < b:
    u = a
    v = b
  else:
    u = b
    v = a
  add(l.xs, u)
  add(l.xs, v)
  return

proc initState*[T, S: SomeFloat, CF: CallableFunction[T, S]](M: Brent, f: CF,
    xs: (T, T)): UnivariateZeroState[T, S] =
  ## creates a new state reference for use with Brent algorithm.
  ## Checks the initial bracket for different signs of function values.
  ## Raises error for unsuitable bracket.
  let
    u = xs[0]
    v = xs[1]
    fu = f.f(u)
    fv = f.f(v)

  var
    a, b: T
    fa, fb: S

  if not(isBracket(fu, fv)):
    raise newException(InitialValueError, bracketing_error)

  if abs(fu) > abs(fv):
    a = u
    b = v
    fa = fu
    fb = fv
  else:
    a = v
    b = u
    fa = fv
    fb = fu

  new(result)
  result.xn1 = b
  result.xn0 = a
  result.xstar = T(0)
  result.m = @[a, a]
  result.fxn1 = fb
  result.fxn0 = fa
  result.fxstar = fb
  result.fm = @[fa, S(1)]
  result.steps = 0
  result.fnevals = 2
  result.stopped = false
  result.xConverged = false
  result.fConverged = false
  result.convergenceFailed = false
  result.message = ""

proc initState*[T, S: SomeFloat](M: Brent, f: proc(a: T): S, xs: (T,
    T)): UnivariateZeroState[T, S] =
  ## creates a new state reference for use with Brent algorithm.
  ## Checks the initial bracket for different signs of function values.
  ## Raises error for unsuitable bracket.
  let
    u = xs[0]
    v = xs[1]
    fu = f(u)
    fv = f(v)

  var
    a, b: T
    fa, fb: S

  if not(isBracket(fu, fv)):
    raise newException(InitialValueError, bracketing_error)

  if abs(fu) > abs(fv):
    a = u
    b = v
    fa = fu
    fb = fv
  else:
    a = v
    b = u
    fa = fv
    fb = fu

  new(result)
  result.xn1 = b
  result.xn0 = a
  result.xstar = T(0)
  result.m = @[a, a]
  result.fxn1 = fb
  result.fxn0 = fa
  result.fxstar = fb
  result.fm = @[fa, S(1)]
  result.steps = 0
  result.fnevals = 2
  result.stopped = false
  result.xConverged = false
  result.fConverged = false
  result.convergenceFailed = false
  result.message = ""

proc initState*[T, S: SomeFloat, CF: CallableFunction[T, S]](
  state: UnivariateZeroState[T, S], M: Brent, f: CF, xs: (T, T)) =
  ## Configures state to use `xs` as initial bracket for Brent algorithm.
  ## If `xs` is no suitable bracket, an `InitialValueError` is raised.
  let
    u = xs[0]
    v = xs[1]
    fu = f.f(u)
    fv = f.f(v)

  if not(isBracket(fu, fv)):
    raise newException(InitialValueError, bracketing_error)

  var
    a, b: T
    fa, fb: S

  # brent store b as smaller of |fa|, |fb|
  if abs(fu) > abs(fv):
    a = u
    b = v
    fa = fu
    fb = fv
  else:
    a = v
    b = u
    fa = fv
    fb = fu

  initState(state, b, a, @[a, a], fb, fa, @[fa, S(1)])
  state.steps = 0
  state.stopped = false
  state.xConverged = false
  state.fConverged = false
  state.convergenceFailed = false

  return

proc initState*[T, S: SomeFloat](state: UnivariateZeroState[T, S], M: Brent,
    f: proc(a: T): S, xs: (T, T)) =
  ## Configures state to use `xs` as initial bracket for Brent algorithm.
  ## If `xs` is no suitable bracket, an `InitialValueError` is raised.
  let
    u = xs[0]
    v = xs[1]
    fu = f(u)
    fv = f(v)

  if not(isBracket(fu, fv)):
    raise newException(InitialValueError, bracketing_error)

  var
    a, b: T
    fa, fb: S

  # brent store b as smaller of |fa|, |fb|
  if abs(fu) > abs(fv):
    a = u
    b = v
    fa = fu
    fb = fv
  else:
    a = v
    b = u
    fa = fv
    fb = fu

  initState(state, b, a, @[a, a], fb, fa, @[fa, S(1)])
  state.steps = 0
  state.stopped = false
  state.xConverged = false
  state.fConverged = false
  state.convergenceFailed = false

  return



proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](M: Brent, f: CF,
    state: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  ## update the `state` variable to the next step of Brent algorithm.
  var
    mflag = state.fm[1] > 0.0
    a = state.xn0
    b = state.xn1
    c = state.m[0]
    d = state.m[1]
    fa = state.fxn0
    fb = state.fxn1
    fc = state.fm[0]

  # next step
  var
    s = T(0)
    fs: S
  if fa - fc != 0.0 and fb - fc != 0.0:
    s = a * fb * fc / (fa - fb) / (fa - fc) # quad step
    s += b * fa * fc / (fb - fa) / (fb - fc)
    s += c * fa * fb / (fc - fa) / (fc - fb)
  else:
    s = secantStep(a, b, fa, fb)

  fs = f.f(s)
  incfn(state)
  if checkZero(M, state, s, fs):
    return

  # guard step
  var
    u = (3 * a + b) / 4
    v = b

  if u > v:
    var temp = u
    u = v
    v = temp

  let
    tol = max(options.xabstol, max(abs(b), max(abs(c), abs(d))) *
        options.xreltol)

  if not(u < s and s < v) or (mflag and abs(s - b) >= abs(b - c)/2) or
    (not(mflag) and abs(s - b) >= abs(b - c)/2) or (mflag and abs(b - c) <=
        tol) or
    (not(mflag) and abs(c - d) <= tol):
    s = middle(a, b)
    fs = f.f(s)
    incfn(state)
    if checkZero(M, state, s, fs):
      return
    mflag = true
  else:
    mflag = false

  d = c
  c = b
  fc = fb

  if sgn(fa) * sgn(fs) < 0:
    b = s
    fb = fs
  else:
    a = s
    fa = fs

  if abs(fa) < abs(fb):
    (a, b, fa, fb) = (b, a, fb, fa)

  (state.xn0, state.xn1, state.m[0], state.m[1]) = (a, b, c, d)
  (state.fxn0, state.fxn1, state.fm[0]) = (fa, fb, fc)
  if mflag:
    state.fm[1] = T(1)
  else:
    state.fm[1] = T(-1)

  return

proc updateState*[T, S: SomeFloat](M: Brent, f: proc(a: T): S,
    state: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  ## update the `state` variable to the next step of Brent algorithm.
  var
    mflag = state.fm[1] > 0.0
    a = state.xn0
    b = state.xn1
    c = state.m[0]
    d = state.m[1]
    fa = state.fxn0
    fb = state.fxn1
    fc = state.fm[0]

  # next step
  var
    s = T(0)
    fs: S
  if fa - fc != 0.0 and fb - fc != 0.0:
    s = a * fb * fc / (fa - fb) / (fa - fc) # quad step
    s += b * fa * fc / (fb - fa) / (fb - fc)
    s += c * fa * fb / (fc - fa) / (fc - fb)
  else:
    s = secantStep(a, b, fa, fb)

  fs = f(s)
  incfn(state)
  if checkZero(M, state, s, fs):
    return

  # guard step
  var
    u = (3 * a + b) / 4
    v = b

  if u > v:
    var temp = u
    u = v
    v = temp

  let
    tol = max(options.xabstol, max(abs(b), max(abs(c), abs(d))) *
        options.xreltol)

  if not(u < s and s < v) or (mflag and abs(s - b) >= abs(b - c)/2) or
    (not(mflag) and abs(s - b) >= abs(b - c)/2) or (mflag and abs(b - c) <=
        tol) or
    (not(mflag) and abs(c - d) <= tol):
    s = middle(a, b)
    fs = f(s)
    incfn(state)
    if checkZero(M, state, s, fs):
      return
    mflag = true
  else:
    mflag = false

  d = c
  c = b
  fc = fb

  if sgn(fa) * sgn(fs) < 0:
    b = s
    fb = fs
  else:
    a = s
    fa = fs

  if abs(fa) < abs(fb):
    (a, b, fa, fb) = (b, a, fb, fa)

  (state.xn0, state.xn1, state.m[0], state.m[1]) = (a, b, c, d)
  (state.fxn0, state.fxn1, state.fm[0]) = (fa, fb, fc)
  if mflag:
    state.fm[1] = T(1)
  else:
    state.fm[1] = T(-1)

  return

proc findBracket*[T, S: SomeFloat, A: AbstractAlefeldPotraShi or
    BisectionExact](f: proc(a: T): S, x0: (T, T), methods: A = A42(),
    kwargs: varargs[UnivariateZeroOptions[T, T, S, S]]): (T, (T, T), bool) =
  ## For bracketing methods returns an approximate root, the last bracketing interval used, and a flag indicating if an exact zero was found as a named tuple.
  ##
  ## With the default tolerances, one  of these should be the case:
  ## `exact` is `true` (indicating termination  of the algorithm due to an exact
  ## zero  being identified) or the length of `bracket` is less or equal than
  ## `2eps(maximum(abs.(bracket)))`. In the `BisectionExact` case, the 2 could
  ## be replaced by 1, as the bracket, `(a,b)` will satisfy `nextfloat(a) == b`;
  ## the Alefeld,  Potra, and Shi algorithms don't quite have that promise.
  let
    x = adjustBracket(x0)
    F = callableFunctions(f)
    state = initState(methods, F, x)

  var
    options: UnivariateZeroState[T, T, S, S]

  if len(kwargs) == 0:
    options = initOptions(methods, state)
  else:
    options = kwargs[0]

  discard findZero(methods, F, options, state)

  return (state.xstar, (state.xn0, state.xn1), state.fxstar == S(0))


## FalsePosition
## -------------
##
## Use the
## `false position <https://en.wikipedia.org/wiki/False_position_method>`_
## method to find a zero for the function `f` within the bracketing interval
## `[a,b]`.
##
## The false position method is a modified bisection method, where the
## midpoint between `[a_k, b_k]` is chosen to be the intersection point
## of the secant line with the x axis, and not the average between the
## two values.
##
## To speed up convergence for concave functions, this algorithm
## implements the 12 reduction factors of Galdino (*A family of regula
## falsi root-finding methods*). These are specified by number, as in
## `FalsePosition(2)` or by one of three names `FalsePosition(:pegasus)`,
## `FalsePosition(:illinois)`, or `FalsePosition(:anderson_bjork)` (the
## default). The default choice has generally better performance than the
## others, though there are exceptions.
##
## For some problems, the number of function calls can be greater than
## for the `bisection64` method, but generally this algorithm will make
## fewer function calls.

proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](M: FalsePosition,
    fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T,
        S, S]) =
  ## update the `state` variable to the next step of FalsePosition algorithm.
  var
    (a, b) = (o.xn0, o.xn1)
    (fa, fb) = (o.fxn0, o.fxn1)
    tau = 1e-10

  var
    lambda = fb / (fb - fa)

  if not(tau < abs(lambda) and abs(lambda) < 1 - tau):
    lambda = 0.5

  let
    x = b - lambda * (b - a)
    fx = fs.f(x)
  incfn(o)
  if fx == 0.0:
    o.xn1 = x
    o.fxn1 = fx
    o.fConverged = true
    return

  if sgn(fx) * sgn(fb) < 0:
    (a, fa) = (b, fb)
  else:
    fa = galdinoReduction(M, fa, fb, fx)

  (b, fb) = (x, fx)

  (o.xn0, o.xn1) = (a, b)
  (o.fxn0, o.fxn1) = (fa, fb)
  return

proc updateState*[T, S: SomeFloat](M: FalsePosition, fs: proc(a: T): S,
    o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  ## update the `state` variable to the next step of FalsePosition algorithm.
  var
    (a, b) = (o.xn0, o.xn1)
    (fa, fb) = (o.fxn0, o.fxn1)
    tau = 1e-10

  var
    lambda = fb / (fb - fa)

  if not(tau < abs(lambda) and abs(lambda) < 1 - tau):
    lambda = 0.5

  let
    x = b - lambda * (b - a)
    fx = fs(x)
  incfn(o)
  if fx == 0.0:
    o.xn1 = x
    o.fxn1 = fx
    o.fConverged = true
    return

  if sgn(fx) * sgn(fb) < 0:
    (a, fa) = (b, fb)
  else:
    fa = galdinoReduction(M, fa, fb, fx)

  (b, fb) = (x, fx)

  (o.xn0, o.xn1) = (a, b)
  (o.fxn0, o.fxn1) = (fa, fb)
  return

template defaultTolerances*(M: FalsePosition|Brent): (float, float, float,
    float, int, int, bool) =
  ## FalsePosition and Brent use the generic generic `defautlTolerances` proc
  defaultTolerances(AbstractNonBracketing(), float, float)

template defaultTolerances*[T, S: SomeFloat](M: FalsePosition|Brent,
    Ti: typedesc[T], Si: typedesc[S]): (T, T, S, S, int, int, bool) =
  ## FalsePosition and Brent use the generic generic `defautlTolerances` proc
  defaultTolerances(AbstractNonBracketing(), Ti, Si)

var
  galdino = initTable[int, proc(a, b, c: float): float]()
  ## the 12 reduction factors offered by Galadino

galdino[1] = proc(fa, fb, fx: float): float =
  return fa * fb / (fb + fx)

galdino[2] = proc(fa, fb, fx: float): float =
  return (fa - fb) / 2

galdino[3] = proc(fa, fb, fx: float): float =
  return (fa - fx) / (2.0 + fx / fb)

galdino[4] = proc(fa, fb, fx: float): float =
  return (fa - fx) / (1.0 + fx / fb)^2

galdino[5] = proc(fa, fb, fx: float): float =
  return (fa - fx) / (1.5 + fx / fb)^2

galdino[6] = proc(fa, fb, fx: float): float =
  return (fa - fx) / (2.0 + fx / fb)^2

galdino[7] = proc(fa, fb, fx: float): float =
  return (fa + fx) / (2.0 + fx / fb)^2

galdino[8] = proc(fa, fb, fx: float): float =
  return fa / 2

galdino[9] = proc(fa, fb, fx: float): float =
  return fa / (1.0 + fx / fb)^2

galdino[10] = proc(fa, fb, fx: float): float =
  return (fa - fx) / 4

galdino[11] = proc(fa, fb, fx: float): float =
  return fx * fa / (fb + fx)

galdino[12] = proc(fa, fb, fx: float): float =
  if (1.0 - fx / fb) > 0.0:
    return fa * (1.0 - fx / fb)
  else:
    return fa * 0.5

proc galdinoReduction(methods: FalsePosition, fa, fb, fx: float):
    float {.inline.} =
  ## Applies galdino function set up in methods to `fa`, `fb` and `fx`
  ##
  ## from `Chris Elrod <https://raw.githubusercontent.com/chriselrod/AsymptoticPosteriors.jl/master/src/false_position.jl>`
  return galdino[methods.g](fa, fb, fx)



# the following methods have been moved here from findZero.nim
# because parts of them are implemented here and can not be lazily
# declared as in Julia


# Updates state, could be `find_zero!(state, M, F, options, l)...
proc findZero*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod,
    CF: CallableFunction[T, S]](M: A, F: CF, options: UnivariateZeroOptions[T,
    T, S, S], state: UnivariateZeroState[T, S], l: Tracks[T,
    S]|NullTracks = NullTracks()): T =
  ## Main method
  ## return a zero or NaN.
  when l is NullTracks:
    logStep(l)
  elif M is AbstractAlefeldPotraShi:
    logStep(l, M, state)
  else:
    logStep(l, true, state, 1)

  while true:
    when A is Bisection or A is AbstractAlefeldPotraShi or A is BisectionExact:
      let
        val = assessConvergence(M, state, options)
    else:
      let
        val = assessConvergence(true, state, options)
    if val:
      break
    updateState(M, F, state, options)
    when l is NullTracks:
      logStep(l)
    elif A is Bisection or A is AbstractAlefeldPotraShi or A is BisectionExact:
      logStep(l, M, state)
    else:
      logStep(l, true, state)
    incsteps(state)

  return decideConvergence(M, F, state, options)

# Robust version using some tricks: idea from algorithm described in
# [The SOLVE button from the
# HP-34]C(http://www.hpl.hp.com/hpjournal/pdfs/IssuePDFs/1979-12.pdf).
# * use bracketing method if one identifed
# * limit steps so as not too far or too near the previous one
# * if not decreasing, use a quad step upto 4 times to bounce out of trap,
#     if possible
# First uses M, then N if bracket is identified
proc findZero*[T, S: SomeFloat, AM: AbstractUnivariateZeroMethod,
    AN: AbstractBracketing, CF: CallableFunction[T, S]](M: AM, N: AN, F: CF,
    options: UnivariateZeroOptions[T, T, S, S], state: UnivariateZeroState[T,
    S], l: Tracks[T, S]|NullTracks = NullTracks()): T =
  when l is NullTracks:
    logStep(l)
  elif M is AbstractAlefeldPotraShi:
    logStep(l, M, state)
  else:
    logStep(l, true, state, 1)
  let
    state0 = copyState(state)
  var
    quadCtr = 0

  while true:

    when AM is AbstractBisection or AM is AbstractAlefeldPotraShi:
      if assessConvergence(M, state, options):
        break
    else:
      if assessConvergence(true, state, options):
        break

    copyState(state0, state)
    updateState(M, F, state0, options)
    var
      adj = false

    ## did we find a zero or a bracketing interval?
    if state0.fxn1 == 0.0:
      copyState(state, state0)
      (state.xstar, state.fxstar) = (state.xn1, state.fxn1)
      state.fConverged = true
      break
    elif sgn(state0.fxn0) * sgn(state0.fxn1) < 0:
      copyState(state, state0)
      var
        a = state0.xn0
        b = state0.xn1
      runBisection(N, F, (a, b), state, options)
      break
    else:
      discard
    ## did we move too far?
    var
      r = state0.xn1
      a = state.xn0
      b = state.xn1
      deltaR = abs(r - b)
      deltaX = abs(r - a)
      ts = 1e-3
      TB = 1e2

    if deltaR >= TB * deltaX:
      adj = true
      r = b + T(sgn(r - b)) * TB * deltaX
      state0.xn1 = r
      state0.fxn1 = F.f(r)
      incfn(state)
    elif deltaR <= ts * deltaX:
      adj = true
      r = b + T(sgn(r - b)) * ts * deltaX
      var
        fr = F.f(r)
      incfn(state)
      state0.xn1 = r
      state0.fxn1 = fr
    else:
      discard
    # a sign change after shortening?
    if sgn(state.fxn1) * sgn(state0.fxn1) < 0:
      (state.xn0, state.fxn0) = (state.xn1, state.fxn1)
      (state.xn1, state.fxn1) = (state0.xn1, state0.fxn1)
      a = state.xn0
      b = state.xn1
      runBisection(N, F, (a, b), state, options)
      break
    ## did we improve?
    if adj or abs(state0.fxn1) < abs(state.fxn1):
      let
        cx = classify(state0.xn1)
        cfx = classify(state0.fxn1)
      case cx
      of fcNan, fcInf, fcNegInf:
        break
      else:
        discard
      case cfx
      of fcNan, fcInf, fcNegInf:
        break
      else:
        discard
        break

      copyState(state, state0)
      when l is NullTracks:
        logStep(l)
      elif M is Bisection or M is BisectionExact or
          M is AbstractAlefeldPotraShi:
        logStep(l, M, state)
      else:
        logStep(l, true, state)
      incsteps(state)
      quadCtr = 0
      continue

    if quadCtr > 4:
      copyState(state, state0)
      state.stopped = true
      break
    else:
      quadCtr += 1
      r = quadVertex(state0.xn1, state0.fxn1, state.xn1, state.fxn1, state.xn0,
        state.fxn0)

      if classify(r) == fcNan or classify(r) == fcInf or classify(r) == fcNegInf:
        copyState(state, state0)
      else:

        var
          fr2 = F.f(r)
        incfn(state)

        state0.xn1 = r
        state0.fxn1 = fr2
        incfn(state)
        copyState(state, state0)

      when l is NullTracks:
        logStep(l)
      elif M is Bisection or M is BisectionExact or
          M is AbstractAlefeldPotraShi:
        logStep(l, M, state)
      else:
        logStep(l, true, state)
      incsteps(state)

  return decideConvergence(M, F, state, options)
