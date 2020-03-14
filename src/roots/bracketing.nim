import math, tables
import utils, findZero

  # types needed for bracketing
type
  InitialValueError* = object of ValueError
  AbstractBisection* = object of  AbstractBracketing
  Bisection* = object of AbstractBisection
  BisectionExact* = object of AbstractBisection
  AbstractAlefeldPotraShi* = object of AbstractBracketing
  A42* = object of AbstractAlefeldPotraShi
  AlefeldPotraShi* = object of AbstractAlefeldPotraShi
  Brent* = object of AbstractBracketing
  FalsePosition* = object of AbstractBisection
    g*: int

const
  bracketing_error = """The interval [a,b] is not a bracketing interval.
  You need f(a) and f(b) to have different signs (f(a) * f(b) < 0).
  Consider a different bracket"""

# forward declarations

proc middle[T: SomeNumber](x, y: T): float
proc middle2[T, S: SomeFloat](a: T, b: S): float
proc ipzero[T, S: SomeFloat](a, b, c, d: T, fa, fb, fc, fd: S, delta: T = T(0.0)): T
proc newtonQuadratic[T, S: SomeFloat, R: SomeInteger](a, b, d: T, fa, fb, fd: S, k: R, delta: T = T(0.0)): T
proc galdinoReduction(methods: FalsePosition, fa, fb, fx: float): float {.inline.}


proc logStep*[T, S: SomeFloat, A: AbstractBisection](l: Tracks[T, S], M: A, state: UnivariateZeroState[T, S]) =
  add(l.xs, state.xn0)
  add(l.xs, state.xn1)

proc adjustBracket[T: SomeFloat](x0: (T, T)): (T, T) =
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


proc initState*[T: SomeFloat, A: AbstractBisection, CF: CallableFunction or proc (a: T): T](meth: A, fs: CF, x: (T, T)): UnivariateZeroState[T, T] =
  let
    (x0, x1) = adjustBracket(x)

  when typeof(fs) is CallableFunction:
    let
      fx0 = fs.f(x0)
      fx1 = fs.f(x1)
  else:
    let
      fx0 = fs(x0)
      fx1 = fs(x1)

  if sgn(fx0) * sgn(fx1) > 0:
    raise newException(InitialValueError, bracketing_error)

  return initState(meth, fs, (x0, x1), (fx0, fx1))

proc initState*[T: SomeFloat, A: AbstractBisection, CF: CallableFunction or proc (a: T): T](meth: A, fs: CF, xs, fxs: (T, T)): UnivariateZeroState[T, T] =
  let
    (x0, x1) = xs
    (fx0, fx1) = fxs

  var
    state: UnivariateZeroState[T, T]

  new(state)
  state.xn1 = x1
  state.xn0 = x0
  state.xstar = T(0)
  state.m = @[x1]
  state.fxn1 = fx1
  state.fxn0 = fx0
  state.fxstar = fx1
  state.fm = @[fx1]
  state.steps = 0
  state.fnevals = 2
  state.stopped = false
  state.xConverged = false
  state.fConverged = false
  state.convergenceFailed = false
  state.message = ""

  initState(state, meth, fs, (x0, x1), (fx0, fx1))
  return state

proc initState*[T: SomeFloat, A: AbstractBisection, CF: CallableFunction or proc (a: T): T](state: UnivariateZeroState[T, T], M: A, fs: CF, xs: (T, T)) =
  let
    (x0, x1) = xs

  when typeof(fs) is CallableFunction:
    let
      fx0 = fs.f(x0)
      fx1 = fs.f(x1)
  else:
    let
      fx0 = fs(x0)
      fx1 = fs(x1)

  initState(state, M, fs, (x0, x1), (fx0, fx1))
  return

proc initState*[T: SomeFloat, A: AbstractBisection, CF: CallableFunction or proc (a: T): T](state: UnivariateZeroState[T, T], M: A, fs: CF, xs, fxs: (T, T)) =
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
    when typeof(fs) is CallableFunction:
      fm = fs.f(m)
    else:
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
  when typeof(fs) is CallableFunction:
    fm = fs.f(m)
  else:
    fm = fs(m)
  incfn(state)

  initState(state, x1, x0, @[m], fx1, fx0, @[fm])
  return



proc defaultTolerances*[Ti, Si: SomeFloat](M: Bisection | BisectionExact, T: typedesc[Ti], S: typedesc[Si]): (Ti, Ti, Si, Si, int, int, bool) =
  let
    xatol = Ti(0)
    xrtol = Ti(0)
    atol = Si(0)
    rtol = Si(0)
    maxevals = high(int)
    maxfnevals = high(int)
    strict = true

  return((xatol, xrtol, atol, rtol, maxevals, maxfnevals, strict))

proc middle[T: SomeNumber](x, y: T): float =
  var
    a, b: float
  if abs(x) == Inf:
    when sizeof(T) == 8:
      a = nextafter(cdouble(x), cdouble(0.0))
    else:
      a = nextafterf(cfloat(x), cfloat(0.0))
  else:
    a = float(x)
  if y == Inf:
    when sizeof(T) == 8:
      b = nextafter(cdouble(y), cdouble(0.0))
    else:
      b = nextafterf(cfloat(y), cfloat(0.0))
  else:
    b = float(y)

  if sgn(a) * sgn(b) < 0:
    return 0.0
  else:
    return middle2(a, b)

proc middle2[T, S: SomeFloat](a: T, b: S): float =
  let
    s = sizeof(S)
    t = sizeof(T)

  if s == t:
    # let
    #   x = toInt(a)
    #   y = toInt(b)
    #   z = x + y

    # return toFloat(z shr 1)
    return 0.5 * a + 0.5 * b
  elif s < t:
    return 0.5 * float(a) + 0.5 * b
  else:
    return 0.5 * a + 0.5 * float(b)

proc middle2[T: SomeInteger](a, b: T): float =
  return 0.5 * float(a) + 0.5 * float(b)

proc assessConvergence*[T, S: SomeFloat](M: Bisection, state: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]): bool =
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

proc assessConvergence*[T, S](M: BisectionExact, state: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]): bool =
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
    if i[1] == 0.0 or i[1] == S(NaN):
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

proc updateState*[T: SomeFloat, CF: CallableFunction or proc (a: T): T](M: Bisection | BisectionExact, fs: CF, o: UnivariateZeroState[T, T], options: UnivariateZeroOptions[T, T, T, T]) =
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
  when fs is CallableFunction:
    let
      fm = fs.f(m)
  else:
    let
      fm = fs(m)
  
  o.m[0] = m
  o.fm[0] = fm
  incfn(o)

  return

proc findZero*[T, S: SomeFloat, A: AbstractBracketing, AT: Tracks[T, S] or NullTracks, CF: CallableFunction](fs: CF, x0: (T, S), methods: A, tracks: AT = NullTracks(), verbose = false, kwargs: varargs[UnivariateZeroOptions[T, T, S, S]]): float =
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
    iszeroTol = options.xabstol == 0.0 and options.xreltol == 0.0 and options.abstol == 0.0 and options.reltol == 0.0

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

proc findZero*[T, S: SomeFloat, A: AbstractBracketing, AT: Tracks[T, S] or NullTracks](fs: proc (a: T): S, x0: (T, S), methods: A, tracks: AT = NullTracks(), verbose = false, kwargs: varargs[UnivariateZeroOptions[T, T, S, S]]): float =

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
    iszeroTol = options.xabstol == 0.0 and options.xreltol == 0.0 and options.abstol == 0.0 and options.reltol == 0.0

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

  return state.xn1

proc findZero*[T, S: SomeInteger, R: SomeFloat, A: AbstractBracketing](fs: proc(a: R): float, x0: (T, S), M: A, verbose = false, kwargs: varargs[UnivariateZeroOptions[float, float, float, float]]): float =
  if len(kwargs) == 0:
    return findZero(fs, (float(x0[0]), float(x0[1])), M, verbose = verbose)
  else:
    return findZero(fs, (float(x0[0]), float(x0[1])), M, verbose = verbose, kwargs = kwargs[0])

proc findZero*[T, S: SomeInteger, R: SomeFloat](fs: proc(a: R): float, x0: (T, S), verbose: bool = false, kwargs: varargs[UnivariateZeroOptions[float, float, float, float]]): float =
  if len(kwargs) == 0:
    return findZero(fs, (float(x0[0]), float(x0[1])), verbose = verbose)
  else:
    return findZero(fs, (float(x0[0]), float(x0[1])), verbose = verbose, kwargs = kwargs[0])

proc findZero*[T, S: SomeNumber, SI: proc(a: SomeInteger): SomeNumber|proc(a: SomeNumber): SomeInteger,Q: SomeInteger](fs: SI, x0: (T, S), verbose: bool = false, kwargs: varargs[UnivariateZeroOptions[float, float, float, float]]): float =
  echo "The function may not use integers as domain or codomain."

  return float(NaN)

proc findZero*[T, S: SomeNumber, SI: proc(a: SomeInteger): SomeNumber|proc(a: SomeNumber): SomeInteger, A: AbstractBracketing](fs: SI, x0: (T, S), M: A, verbose: bool = false, kwargs: varargs[UnivariateZeroOptions[float, float, float, float]]): float =
  echo "The function may not use integers as domain or codomain."

  return float(NaN)

proc isBracket[T: SomeNumber](fa, fb: T): bool {.inline.} =
  return sgn(fa) * sgn(fb) < 0

proc fAB[T, S: SomeFloat](a, b: T, fa, fb: S): float {.inline.} =
  return float(fb - fa) / float(b - a)

proc fABD[T, S: SomeFloat](a, b, d: T, fa, fb, fd: S): float {.inline.} =
  let
    fabi = fAB(a, b, fa, fb)
    fbdi = fAB(b, d, fb, fd)
  return (fbdi - fabi) / (d - a)

proc secantStep[T, S: SomeFloat](a, b: T, fa, fb: S): T {.inline.} =
  return a - T(fa * (b - a) / (fb - fa))

proc bracket[T, S: SomeFloat](a, b, c: T, fa, fb, fc: S): (T, T, T, S, S, S) =
  if isBracket(fa, fc):
    return (a, c, b, fa, fc, fb)
  else:
    return (c, b, a, fc, fb, fa)

proc takeA42Step[T, S: SomeFloat](a, b, d, ee: T, fa, fb, fd, fe: S, delta: T = T(0.0)): T =
  let
    fs = (fa, fb, fd, fe)

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

proc newtonQuadratic[T, S: SomeFloat, R: SomeInteger](a, b, d: T, fa, fb, fd: S, k: R, delta: T = T(0.0)): T =
  let
    A = fABD(a, b, d, fa, fb, fd)

  var
    r: T

  if isBracket(A, fa):
    r = b
  else:
    r = a

  # use quadratic step; if that fails, use secant step; if that fails, bisection
  if A != NaN or A == Inf or A != T(0.0):
    let
      B = fAB(a, b, fa, fb)
      dr = T(0.0)

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

proc initState*[T, S: SomeFloat, A: AbstractAlefeldPotraShi, CF: CallableFunction or proc(a: float): float](M: A, f: CF, xs: (T, S)): UnivariateZeroState[float, float] =
  var
    u = float(xs[0])
    v = float(xs[1])

  if u > v:
    var
      temp = u
    u = v
    v = temp

  when typeof(f) is CallableFunction:
    let
      fu = f.f(u)
      fv = f.f(v)
  else:
    let
      fu = f(u)
      fv = f(v)

  if not(isBracket(fu, fv)):
    raise newException(InitialValueError, bracketing_error)

  let
    state: UnivariateZeroState[T, S] = new(UnivariateZeroState[T, S])

  # new(state)
  state.xn1 = v
  state.xn0 = u
  state.xstar = T(0)
  state.m = @[v, v]
  state.fxn1 = fv
  state.fxn0 = fu
  state.fxstar = fv
  state.fm = @[fv, fv]
  state.steps = 0
  state.fnevals = 2
  state.stopped = false
  state.xConverged = false
  state.fConverged = false
  state.convergenceFailed = false
  state.message = ""

  initState(state, M, f, (u, v), false)
  return state

proc initState*[T, S: SomeFloat, A: AbstractAlefeldPotraShi, CF: CallableFunction or proc(a: T): S](state: UnivariateZeroState[T, S], aaps: A, f: CF, xs: (T, T), computeFx = true) =
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
    when typeof(f) is CallableFunction:
      fa = f.f(a)
      fb = f.f(b)
    else:
      fa = f(a)
      fb = f(b)
    state.fnevals = 2
    if not(isBracket(fa, fb)):
      raise newException(InitialValueError, bracketing_error)

  c = middle(a, b)
  when typeof(f) is CallableFunction:
    fc = f.f(c)
  else:
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



proc defaultTolerances*(M: AbstractAlefeldPotraShi, T, S: typedesc): (T, T, S, S, int, int, bool) =
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

proc checkZero*[T, S: SomeFloat, A: AbstractBracketing](M: A, state: UnivariateZeroState[T, S], c: T, fc: S): bool =
  if c == NaN:
    state.stopped = true
    state.xn1 = c
    state.message &= "NaN encountered. "
    return true
  elif c == Inf:
    state.stopped = true
    state.xn1 = c
    state.message &= "Inf encountered. "
    return true
  elif c == T(0):
    state.stopped = true
    state.message &= "Exact zero found. "
    state.xstar = c
    state.fxstar = fc
    return true
  else:
    return false
    
proc assessConvergence*[T, S: SomeFloat, A: AbstractAlefeldPotraShi](M: A, state: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]): bool =
  if state.stopped or state.xConverged or state.fConverged:
    if state.xstar == T(NaN):
      (state.xstar, state.fxstar) = (state.xn1, state.fxn1)
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

  (u, fu) = chooseSmallest(u, state.m[0], fu, state.fm[0])

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
      tol = max(options.xabstol, max(mx * options.xreltol, T(sgn(options.xreltol)) * max(nextafter(mx, Inf) - mx, mx - nextafter(mx, -Inf ))))
  else:
    let
      tol = max(options.xabstol, max(mx * options.xreltol, T(sgn(options.xreltol)) * max(nextafterf(mx, Inf) - mx, mx - nextafterf(mx, -Inf ))))

  if abs(b - a) <= 2 * tol:
    state.xstar = u
    state.fxstar = fu
    state.xConverged = true
    return true

  return false

proc logStep*[T, S: SomeFloat, A: AbstractAlefeldPotraShi](l: Tracks[T, S], M: A, state: UnivariateZeroState[T, S]) =
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

proc updateState[T, S: SomeFloat, CF: CallableFunction or proc(a: T): S](M: A42, f: CF, state: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
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

  when typeof(f) is CallableFunction:
    fc = f.f(c)
  else:
    fc = f(c)
  incfn(state)
  if checkZero(M, state, c, fc):
    return

  var
    (ab, bb, db, fab, fbb, fdb) = bracket(a, b, c, fa, fb, fc)
    eb = d
    feb = fd
    cb = takeA42Step(ab, bb, db, eb, fab, fbb, fdb, feb, delta)
  when typeof(f) is CallableFunction:
    var
      fcb = f.f(cb)
  else:
    var
      fcb = f(cb)
  incfn(state)
  if checkZero(M, state, cb, fcb):
    return

  (ab, bb, db, fab, fbb, fdb) = bracket(ab, bb, cb, fab, fbb, fcb)

  var
    (u, fu) = chooseSmallest(ab, bb, fab, fbb)

  cb = u - 2 * fu * (bb - ab) / (fbb - fab)
  var
    ch = cb
  if abs(cb - u) > 0.5 * abs(b - a):
    ch = middle(an, bn)
  when typeof(f) is CallableFunction:
    var
      fch = f.f(cb)
  else:
    var
      fch = f(cb)
  incfn(state)
  if checkZero(M, state, ch, fch):
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
    when typeof(f) is CallableFunction:
      let
        fm = f.f(m)
    else:
      let
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

proc updateState[T, S: SomeFloat, CF: CallableFunction or proc(a: T): S](M: AlefeldPotraShi, f: CF, state: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =

  var
    a = state.xn0
    b = state.xn1
    d = state.m[0]
    ee = state.m[1]
    fa = state.fxn0
    fb = state.fxn1
    fd = state.fm[0]
    fe = state.fm[1]

  let
    mu = 0.5
    lambda = 0.7
    tole = max(options.xabstol, max(abs(a), abs(b)) * options.xreltol)
    delta = lambda * tole

  var
    c = newtonQuadratic(a, b, d, fa, fb, fd, 2, delta)
  when typeof(f) is CallableFunction:
    var
      fc = f.f(c)
  else:
    var
      fc = f(c)
  incfn(state)
  if checkZero(M, state, c, fc):
    return

  (a, b, d, fa, fb, fd) = bracket(a, b, c, fa, fb, fc)
  c = newtonQuadratic(a, b, d, fa, fb, fd, 3, delta)
  when typeof(f) is CallableFunction:
    fc = f.f(c)
  else:
    fc = f(c)
  incfn(state)
  if checkZero(M, state, c, fc):
    return

  (a, b, d, fa, fb, fd) = bracket(a, b, c, fa, fb, fc)

  let
    (u, fu) = chooseSmallest(a, b, fa, fb)
  c = u - 2 * fu  * (b - a) / (fb - fa)
  if abs(c - u) > 0.5 * (b - a):
    c = middle(a, b)

  when typeof(f) is CallableFunction:
    fc = f.f(c)
  else:
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
    when typeof(f) is CallableFunction:
      let
        fm = f.f(m)
    else:
      let
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


# the following methods have been moved here from findZero.nim
# because parts of them are implemented here and can not be lazily
# declared as in Julia

proc findZero*[T, S: SomeFloat](f: proc(a: S): T, x0: (S, S), verbose = false, kwargs: varargs[UnivariateZeroOptions[T, T, T, T]]): T =
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

# Main method
# return a zero or NaN.
## Updates state, could be `find_zero!(state, M, F, options, l)...
proc findZero*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod, CF: CallableFunction](M: A, F: CF, options: UnivariateZeroOptions[T, T, S, S], state: UnivariateZeroState[T, S], l: Tracks[T, S]|NullTracks = NullTracks()): T =
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
    else:
      logStep(l, M, state)
    incsteps(state)

  return decideConvergence(M, F, state, options)


# Robust version using some tricks: idea from algorithm described in
# [The SOLVE button from the
# HP-34]C(http://www.hpl.hp.com/hpjournal/pdfs/IssuePDFs/1979-12.pdf).
# * use bracketing method if one identifed
# * limit steps so as not too far or too near the previous one
# * if not decreasing, use a quad step upto 4 times to bounce out of trap, if possible
# First uses M, then N if bracket is identified
proc findZero*[T, S: SomeFloat, AM, AN: AbstractUnivariateZeroMethod, CF: CallableFunction](M: AM, N: AN, F: CF, options: UnivariateZeroOptions[T, T, S, S], state: UnivariateZeroState[T, S], l: Tracks[T, S]|NullTracks = NullTracks()) =
  when l is NullTracks:
    logStep(l)
  elif M is AbstractAlefeldPotraShi:
    logStep(l, M, state)
  else:
    logStep(l, true, state, 1)
  let
    state0 = copyState(state)
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
      r = b + sgn(r - b) * TB * deltaX
      state0.xn1 = r
      state0.fxn1 = F.f(r)
      incfn(state)
    elif deltaR <= ts * deltaX:
      adj = true
      r = b + sgn(r - b) * ts * deltaX
      var
        fr = F.f(r)
      incfn(state)
      state0.xn1 = r
      state0.fxn1 = fr
    else:
      discard

    # a sign change after shortening?
    if sgn(state.fxn1) * sgn(state0.fxn1) < 0:
      state.xn0 = state.xn1
      state.fxn0 = state.fxn1
      a = state.xn0
      b = state.xn1
      runBisection(N, F, (a, b), state, options)
      break

    ## did we improve?
    if adj or abs(state0.fxn1) < abs(state.fxn1):
      if state0.xn1 == NaN or state0.fxn1 == NaN or abs(state0.xn1) == Inf or abs(state0.fxn1) == Inf:
        break

      copyState(state, state0)
      when l is NullTracks:
        logStep(l)
      else:
        logStep(l, M, state)
      incsteps(state)
      quadCtr = 0
      continue

    if quadCtr > 4:
      copyState(state, state0)
      state.stopped = true
      break
    else:
      quadCtr += 1
      r = quadVertex(state0.xn1, state0.fxn1, state.xn1, state.fxn1, state.xn0, state.fxn0)

      if r == NaN or abs(r) == Inf:
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
      else:
        logStep(l, M, state)
      incsteps(state)

    decideConvergence(M, F, state, options)

# Roots.Brent()

# An implementation of
# [Brent's](https://en.wikipedia.org/wiki/Brent%27s_method) (or Brent-Dekker) method.
# This method uses a choice of inverse quadratic interpolation or a secant
# step, falling back on bisection if necessary.

proc logStep*[T, S: SomeFloat](l: Tracks[T, S], M: Brent, state: UnivariateZeroState[T, S]) =
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

proc initState*[T: SomeFloat, CF: CallableFunction or proc(a: T): float](M: Brent, f: CF, xs: (T, T)): UnivariateZeroState[T, float] =
  let
    u = xs[0]
    v = xs[1]

  when typeof(f) is CallableFunction:
    let
      fu = f.f(u)
      fv = f.f(v)
  else:
    let
      fu = f(u)
      fv = f(v)

  var
    a, b: T
    fa, fb: float

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

  let state: UnivariateZeroState[T, float] = new(UnivariateZeroState[T, float])

  state.xn1 = b
  state.xn0 = a
  state.xstar = T(0)
  state.m = @[a, a]
  state.fxn1 = fb
  state.fxn0 = fa
  state.fxstar = fb
  state.fm = @[fa, float(1)]
  state.steps = 0
  state.fnevals = 2
  state.stopped = false
  state.xConverged = false
  state.fConverged = false
  state.convergenceFailed = false
  state.message = ""

  return state

proc initState*[T, S: SomeFloat, CF: CallableFunction or proc(a: T): S](state: UnivariateZeroState[T, S], M: Brent, f: CF, xs: (T, T)) =
  let
    u = xs[0]
    v = xs[1]

  when typeof(f) is CallableFunction:
    let
      fu = f.f(u)
      fv = f.f(v)
  else:
    let
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


proc updateState*[T, S: SomeFloat, CF: CallableFunction or proc(a: T): S](M: Brent, f: CF, state: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
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
    s =  a * fb * fc / (fa - fb) / (fa - fc) # quad step
    s += b * fa * fc / (fb - fa) / (fb - fc)
    s += c * fa * fb / (fc - fa) / (fc - fb)
  else:
    s = secantStep(a, b, fa, fb)

  when f is CallableFunction:
    fs = f.f(s)
  else:
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
    tol = max(options.xabstol, max(abs(b), max(abs(c), abs(d))) * options.xreltol)

  if not(u < s and s < v) or (mflag and abs(s - b) >= abs(b - c)/2) or
    (not(mflag) and abs(s - b) >= abs(b - c)/2) or (mflag and abs(b - c) <= tol) or
    (not(mflag) and abs(c - d) <= tol):
    s = middle(a, b)
    when f is CallableFunction:
      fs = f.f(s)
    else:
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

proc findBracket*[T, S: SomeFloat, A: AbstractAlefeldPotraShi or BisectionExact](f: proc(a: T): S, x0: (T, T), methods: A = A42(), kwargs: varargs[UnivariateZeroOptions[T, T, S, S]]): (T, (T, T), bool) =
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


# FalsePosition

proc updateState*[T, S: SomeFloat, CF: CallableFunction or proc(a: T): S](M: FalsePosition, fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
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
  when fs is CallableFunction:
    let
      fx = fs.f(x)
  else:
    let
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

template defaultTolerances*(M: FalsePosition): (float, float, float, float, int, int, bool) =
  defaultTolerances(AbstractNonBracketing(), float, float)

template defaultTolerances*[T, S: SomeFloat](M: FalsePosition, Ti: typedesc[T], Si: typedesc[S]): (T, T, S, S, int, int, bool) =
  defaultTolerances(AbstractNonBracketing(), Ti, Si)

var
  galdino = initTable[int, proc(a, b, c: float): float]()

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
  if fa * (1.0 - fx / fb) > 0.0:
    return 1.0 - fx / fb
  else:
    return 0.5

proc galdinoReduction(methods: FalsePosition, fa, fb, fx: float): float {.inline.} =
  return galdino[methods.g](fa, fb, fx)
