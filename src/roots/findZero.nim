## ========
## findZero
## ========
##
## Framework for setting up an iterative problem for finding a zero

import math, sequtils
import private/utils

type
  # Methods
  AbstractUnivariateZeroMethod* = object of RootObj
  AbstractBracketing* = object of AbstractUnivariateZeroMethod
  AbstractNonBracketing* = object of AbstractUnivariateZeroMethod
  AbstractSecant* = object of AbstractNonBracketing
  AbstractNonSecant* = object of AbstractNonBracketing

  # types needed for bracketing
  InitialValueError* = object of ValueError
  AbstractBisection* = object of AbstractBracketing
  Bisection* = object of AbstractBisection
  BisectionExact* = object of AbstractBisection
  AbstractAlefeldPotraShi* = object of AbstractBracketing
  A42* = object of AbstractAlefeldPotraShi
  AlefeldPotraShi* = object of AbstractAlefeldPotraShi
  Brent* = object of AbstractBracketing
  FalsePosition* = object of AbstractBisection
    ## This algorithm needs an int field to store the chosen galdino function
    ## `g` stores the chosen galdino function
    g*: int

  # types needed for derivativefree methods
  Order0* = object of AbstractSecant
  Secant* = object of AbstractSecant
  Order1* = Secant
  Order1B* = object of AbstractSecant
  King* = object of AbstractSecant
  Order2* = object of AbstractSecant
  Steffensen* = object of AbstractSecant
  Order2B* = object of AbstractSecant
  Esser* = object of AbstractSecant
  Order5* = object of AbstractSecant
  KumarSinghAkanksha* = object of AbstractSecant
  Order8* = object of AbstractSecant
  Thukral8* = object of AbstractSecant
  Order16* = object of AbstractSecant
  Thukral16* = object of AbstractSecant

  # States
  AbstractUnivariateZeroState* = ref object of RootObj
  UnivariateZeroState*[T, S] = ref object of AbstractUnivariateZeroState
    xn0*, xn1*, xstar*: T
    m*: seq[T]
    fxn0*, fxn1*, fxstar*: S
    fm*: seq[S]
    steps*: int
    fnevals*: int
    stopped*: bool
    xConverged*: bool
    fConverged*: bool
    convergenceFailed*: bool
    message*: string

  # Options
  UnivariateZeroOptions*[Q, R, S, T: SomeFloat] = ref object of RootObj
    xabstol*: Q
    xreltol*: R
    abstol*: S
    reltol*: T
    maxevals*: int
    maxfnevals*: int
    strict*: bool

  AbstractTracks* = ref object of Rootobj
    ## Tracks (for logging actual steps)
    ## when no logging this should get optimized out to avoid a branch
  NullTracks* = ref object of AbstractTracks
  Tracks*[T, S: SomeFloat] = ref object of AbstractTracks
    xs*: seq[T]
    fs*: seq[S]

  # Function Types
  CallableFunction*[T, S: SomeFloat] = ref object of RootObj
    f*: proc(a: T): S
  DerivativeFree*[T, S: SomeFloat] = ref object of CallableFunction[T, S]
  FirstDerivative*[T, S: SomeFloat] = ref object of CallableFunction[T, S]
    fp*: proc(a: T): S
  SecondDerivative*[T, S: SomeFloat] = ref object of CallableFunction[T, S]
    fp*, fpp*: proc(a: T): S
  ConvergenceError* = object of ValueError

  # newton
  AbstractNewtonLikeMethod* = object of AbstractNonBracketing
  Newton* = object of AbstractNewtonLikeMethod
  AbstractHalleyLikeMethod* = object of AbstractNonBracketing
  Halley* = object of AbstractHalleyLikeMethod
  Schroder* = object of AbstractHalleyLikeMethod
  Schroeder* = Schroder
  Schröder* = Schroder


# declarations


proc decideConvergence*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod,
                        CF: CallableFunction[T, S]](M: A, F: CF,
                            state: UnivariateZeroState[T, S],
                            options: UnivariateZeroOptions[T, T, S, S]): T


proc runBisection*[T, S: SomeFloat, A: AbstractBracketing,
                    CF: CallableFunction[T, S]](N: A, f: CF, xs: (T, T),
                        state: UnivariateZeroState[T, S],
                        options: UnivariateZeroOptions[T, T, S, S])
proc runBisection*[T, S: SomeFloat, A: AbstractBracketing](N: A,
                    f: proc(a: T): S, xs: (T, T), state: UnivariateZeroState[T,
                        S], options: UnivariateZeroOptions[T, T, S, S])


# Start library functions


proc newState*[T, S: SomeFloat](xn1: T, fxn1: S, fnevals: int = 0, stopped,
    xConverged, fConverged,
    convergenceFailed: bool = false): UnivariateZeroState[T, S] =
  new(result)
  result.xn1 = xn1
  result.fxn1 = fxn1
  result.fnevals = 0
  result.stopped = stopped
  result.xConverged = xConverged
  result.fConverged = fConverged
  result.convergenceFailed = convergenceFailed



proc incfn*[T, S: SomeFloat](o: UnivariateZeroState[T, S], k = 1) =
  o.fnevals += k
proc incsteps*[T, S: SomeFloat](o: UnivariateZeroState[T, S], k = 1) =
  o.steps += k

proc initState*[T, S: SomeFloat, A: AbstractNonSecant, CF: CallableFunction[T,
    S]](methodes: A, fs: CF, x: T): UnivariateZeroState[T, S] =
  ## initialize state for most methods
  let
    x1 = x
    fnevals = 1
    fx1 = fs.f(x1)

  result = newState(x1, fx1, fnevals)

proc initState*[T, S: SomeFloat, A: AbstractNonSecant](methodes: A, fs: proc(
    a: T): S, x: SomeNumber): UnivariateZeroState[T, S] =
  ## initialize state for most methods
  let
    x1 = x
    fnevals = 1
    fx1 = fs(x1)

  result = newState(x1, fx1, fnevals)

proc initState*[T, S: SomeFloat](state: UnivariateZeroState[T, S], x1, x0: T,
    m: seq[T], y1, y0: S, fm: seq[S]) =
  ## This function is used to reset the state to an initial value
  ## As initializing a state is somewhat costly, this can be useful when many
  ## function calls would be used.
  state.xn1 = x1
  state.xn0 = x0
  state.m = m
  state.fxn1 = y1
  state.fxn0 = y0
  state.fm = fm
  state.steps = 0
  state.fnevals = 2
  state.stopped = false
  state.xConverged = false
  state.fConverged = false
  state.convergenceFailed = false
  state.message = ""
  return

proc initState*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod,
                CF: CallableFunction[T, S]](state: UnivariateZeroState[T, S],
                    a: A, fs: CF, x: T) =
  let
    x1 = float(x)
    fx1 = fs.f(x1)

  initState(state, x1, T(0.0), @[T],
             fx1, S(0.0), @[S])

proc initState*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod](
  state: UnivariateZeroState[T, S], a: A, fs: proc(a: T): S, x: T) =
  let
    x1 = float(x)
    fx1 = fs(x1)

  initState(state, x1, T(0.0), @[T],
             fx1, S(0.0), @[S])


proc copyState*[T, S: SomeNumber](state: UnivariateZeroState[T,
    S]): UnivariateZeroState[T, S] =
  new(result)
  result.xn1 = state.xn1
  result.xn0 = state.xn0
  result.xstar = state.xstar
  result.m = state.m
  result.fxn1 = state.fxn1
  result.fxn0 = state.fxn0
  result.fxstar = state.fxstar
  result.fm = state.fm
  result.steps = state.steps
  result.fnevals = state.fnevals
  result.stopped = state.stopped
  result.xConverged = state.xConverged
  result.fConverged = state.fConverged
  result.convergenceFailed = state.convergenceFailed
  result.message = state.message

proc copyState*[T, S: SomeNumber](dst, src: UnivariateZeroState[T, S]) =
  dst.xn1 = src.xn1
  dst.xn0 = src.xn0
  dst.m = src.m
  dst.fxn1 = src.fxn1
  dst.fxn0 = src.fxn0
  dst.fm = src.fm
  dst.steps = src.steps
  dst.fnevals = src.fnevals
  dst.stopped = src.stopped
  dst.xConverged = src.xConverged
  dst.fConverged = src.fConverged
  dst.convergenceFailed = src.convergenceFailed
  dst.message = src.message


# default_tolerances(Method, [T], [S])

template defaultTolerances*(M: AbstractUnivariateZeroMethod): (float, float,
    float, float, int, int, bool) =
  defaultTolerances(M, float, float)

proc defaultTolerances*(M: AbstractNonBracketing, T, S: typedesc): (T, T, S, S,
    int, int, bool) =
  ##  The default tolerances for most methods are `xatol=eps(T)`,
  ##  `xrtol=eps(T)`, `atol=4eps(S)`, and `rtol=4eps(S)`, with the proper
  ##  units (absolute tolerances have the units of `x` and `f(x)`; relative
  ##  tolerances are unitless). For `Complex{T}` values, `T` is used.
  ##
  ##  The number of iterations is limited by `maxevals=40`, the number of
  ##  function evaluations is not capped, due to `maxfnevals=high(int)`,
  ##  and `strict=false`.
  when sizeof(T) == 8:
    let
      xatol = nextafter(1.0, 2.0) - 1.0
      xrtol = nextafter(1.0, 2.0) - 1.0
  else:
    let
      xatol = nextafterf(1.0, 2.0) - 1.0
      xrtol = nextafterf(1.0, 2.0) - 1.0

  when sizeof(S) == 8:
    let
      atol = 4.0 * (nextafter(1.0, 2.0) - 1.0)
      rtol = 4.0 * (nextafter(1.0, 2.0) - 1.0)
  else:
    let
      atol = nextafterf(1.0, 2.0) - 1.0
      rtol = nextafterf(1.0, 2.0) - 1.0

  let
    maxevals = 40
    maxfnevals = high(int)
    strict = false

  return (xatol, xrtol, atol, rtol, maxevals, maxfnevals, strict)

proc newOption*[T, S: SomeFloat](xabstol, xreltol: T, abstol, reltol: S,
    maxevals, maxfnevals: int, strict: bool): UnivariateZeroOptions[T, T, S, S] =
  new(result)
  result.xabstol = xabstol
  result.xreltol = xreltol
  result.abstol = abstol
  result.reltol = reltol
  result.maxevals = maxevals
  result.maxfnevals = maxfnevals
  result.strict = strict

proc initOptions*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod](M: A,
    state: UnivariateZeroState[T, S]): UnivariateZeroOptions[T, T, S, S] =
  let
    defs = defaultTolerances(M, T, S)

  result = newOption(defs[0], defs[1], defs[2], defs[3], defs[4], defs[5], defs[6])

proc initOptions2*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod](
  options: UnivariateZeroOptions[T, T, S, S], M: A) =
  ## reset options to default values
  let
    defs = defaultTolerances(M, T, S)

  options.xabstol = defs[0]
  options.xreltol = defs[1]
  options.abstol = defs[2]
  options.reltol = defs[3]
  options.maxevals = defs[4]
  options.maxfnevals = defs[5]
  options.strict = defs[6]


# Track procs
proc logStep*(s: NullTracks): void =
  return

proc logStep*[T, S: SomeFloat](
  s: Tracks[T, S], M: bool, o: UnivariateZeroState[T, S]) =
  add(s.xs, o.xn1)
  add(s.fs, o.fxn1)
  return

proc logStep*[T, S: SomeFloat](
    s: Tracks[T, S], M: bool, o: UnivariateZeroState[T, S], init: int) =
  logStep(s, M, o)

proc showTracks*[T, S: SomeFloat, A: AbstractBracketing](
    l: Tracks[T, S], M: A) =
  var
    xs = l.xs
    n = len(xs) div 2 - 1
    j = 0
  for i in 0..n:
    echo "(a_", i, ", b_", i, ") = (", xs[j], ", ", xs[j + 1], ")"
    j += 2
  return

proc showTracks*[T, S: SomeFloat, A: AbstractNonBracketing](
    s: Tracks[T, S], M: A) =
  for index, item in zip(s.xs, s.fs):
    echo "x_", index, " = ", float(item[0]), ",\t fx_", index, " = ", float(
        item[1])
  echo ""
  return



# CallableFunction procs
proc fDeltaX*[T, S: SomeFloat](F: DerivativeFree[T, S], x: T): S =
  ## Return f, f/f'
  return F.f(x)

proc fDeltaX*[T, S: SomeFloat](F: FirstDerivative[T, S]|SecondDerivative[T, S],
    x: T): (S, S) =
  let
    fx = F.f(x)
    fpx = F.fp(x)

  return (fx, fx / fpx)

# return f, f/f', f'/f'' (types T, S, S)
proc fDDeltaX*[T, S: SomeFloat](F: DerivativeFree[T, S], x: T): S =
  return F.f(x)

proc fDDeltaX*[T, S: SomeFloat](F: SecondDerivative[T, S], x: T): (S, S, S) =
  let
    fx = F.f(x)
    fp = F.fp(x)
    fpp = F.fpp(x)

  return (fx, fx / fp, fp / fpp)

proc callableFunctions*[T, S: SomeFloat, CF: CallableFunction[T, S]](
    fs: CF): CF =
  return fs

proc callableFunctions*[T, S: SomeFloat](
    fs: proc(a: T): S): DerivativeFree[T, S] =
  new(result)
  result.f = fs

proc callableFunctions*[T, S](fs: (proc(a: T): S, proc(
    a: T): S)): FirstDerivative[T, S] =
  new(result)
  result.f = fs[0]
  result.fp = fs[1]

proc callableFunctions*[T, S](fs: (proc(a: T): S, proc(a: T): S, proc(
    a: T): S)): SecondDerivative[T, S] =
  new(result)
  result.f = fs[0]
  result.fp = fs[1]
  result.fpp = fs[2]





proc isFApprox0*[T: SomeFloat](
    fa, a, atol, rtol: T, relaxed: bool): bool {.inline.} =
  ## Assess convergence
  let
    aa = abs(a)
    afa = abs(fa)
  var
    tol = max(atol, aa * rtol)
  tol = abs(pow(tol, 1/3))

  return afa < tol

proc isFApprox0*[T: SomeFloat](fa, a, atol, rtol: T): bool {.inline.} =
  ## Assess convergence
  let
    aa = abs(a)
    afa = abs(fa)
    tol = max(atol, aa * rtol)

  return afa < tol

proc assessConvergence*[T, S: SomeFloat](
    methodes: bool, state: UnivariateZeroState[T, S],
    options: UnivariateZeroOptions[T, T, S, S]): bool =
  ## Assess if algorithm has converged.
  ##
  ## If alogrithm hasn't converged returns `false`.
  ##
  ## If algorithm has stopped or converged, return `true` and sets one of
  ## `state.stopped`, `state.xConverged`,  `state.fConverged`, or
  ## `state.convergenceFailed`; as well, a message may be set.
  ##
  ## * `state.xConverged = true` if `abs(xn1 - xn0) <
  ##   max(xatol, max(abs(xn1), abs(xn0)) * xrtol)`
  ## * `state.fConverged = true` if  `|f(xn1)| < max(atol, |xn1|*rtol)`
  ## * `state.convergenceFailed = true` if `xn1` or `fxn1` is `NaN` or an
  ##   infinity
  ## * `state.stopped = true` if the number of steps exceed `maxevals` or the
  ##   number of function calls exceeds `maxfnevals`.
  ##
  ## In `findZero`, stopped values (and xConverged) are checked for convergence
  ## with a relaxed tolerance.
  let
    xn0 = state.xn0
    xn1 = state.xn1
    fxn1 = state.fxn1
    cxn1 = classify(xn1)
    cfxn1 = classify(fxn1)

  if (state.xConverged or state.fConverged or state.stopped):
    if classify(state.xstar) == fcNan:
      (state.xstar, state.fxstar) = (xn1, fxn1)
    return true

  if cxn1 == fcNan or cfxn1 == fcNan:
    state.convergenceFailed = true
    state.message &= "NaN produced by algorithm. "
    return true

  if cxn1 == fcInf or cxn1 == fcNegInf or cfxn1 == fcInf or cfxn1 == fcNegInf:
    state.convergenceFailed = true
    state.message &= "Inf produced by algorithm. "
    return true

  # f(xstar) ≈ xstar * f'(xstar)*eps(), so we pass in lambda
  if isFApprox0(fxn1, xn1, options.abstol, options.reltol):
    (state.xstar, state.fxstar) = (xn1, fxn1)
    state.fConverged = true
    return true

  # stop when xn1 ~ xn.
  # in find_zeros there is a check that f could be a zero
  # with a relaxed tolerance
  if abs(xn1 - xn0) < max(options.xabstol, max(abs(xn1), abs(xn0)) *
      options.xreltol):
    (state.xstar, state.fxstar) = (xn1, fxn1)
    state.message &= "x_n ≈ x_(n-1). "
    state.xConverged = true
    return true

  if state.steps > options.maxevals:
    state.stopped = true
    state.message &= "Too many steps taken. "
    return true

  if state.fnevals > options.maxfnevals:
    state.stopped = true
    state.message &= "Too many function evaluations taken. "
    return true

  return false

proc showTrace*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod,
    B: AbstractBracketing](methodes: A, N: B, state: UnivariateZeroState[T, S],
    tracks: Tracks[T, S]) =
  let
    converged = state.xConverged or state.fConverged

  echo "Results of univariate zero finding:"

  if converged:
    echo "* Converged to: ", state.xn1
    echo "* Algorithm: ", " with possible bracketing with " #,$(N)$(methodes),

    echo "* iterations: ", $(state.steps)
    echo "* function evaluations: ", $(state.fnevals)
    if state.xConverged:
      echo "* stopped as x_n ≈ x_(n - 1) using atol = xatol, rtol=xrtol"
    if state.fConverged and state.message == "":
      echo "* stopped as |f(x_n)| ≤ max(δ, max(1,|x|)⋅ϵ)" &
        "using δ = atol, ϵ = rtol"
    if state.message != "":
      echo "* Note: ", state.message
  else:
    echo "* Convergence failed: ", $(state.message)
    # echo "* Algorithm ", $(methodes)
    # $(AbstractUnivariateZeroMethod) implementieren!

  echo ""
  echo "Trace: "
  showTracks(tracks, methodes)

proc showTrace*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod](methodes: A,
    state: UnivariateZeroState[T, S], tracks: Tracks[T, S]) =
  let
    converged = state.xConverged or state.fConverged

  echo "Results of univariate zero finding:"

  if converged:
    echo "* Converged to: ", state.xn1
    when A is AbstractBracketing:
      echo "* Algorithm: " #, $(methodes)
    else:
      echo "* Algorithm: ", " with possible bracketing with " #,$(N)$(methodes),

    echo "* iterations: ", $(state.steps)
    echo "* function evaluations: ", $(state.fnevals)
    if state.xConverged:
      echo "* stopped as x_n ≈ x_(n - 1) using atol = xatol, rtol=xrtol"
    if state.fConverged and state.message == "":
      echo "* stopped as |f(x_n)| ≤ max(δ, max(1,|x|)⋅ϵ)" &
        " using δ = atol, ϵ = rtol"
    if state.message != "":
      echo "* Note: ", state.message
  else:
    echo "* Convergence failed: ", $(state.message)
    # echo "* Algorithm ", $(methodes)
    # $(AbstractUnivariateZeroMethod) implementieren!

  echo ""
  echo "Trace: "
  showTracks(tracks, methodes)



## findZero
## --------
##
## Interface to one of several methods for find zeros of a univariate function.
##
## Optional arguments (tolerances, limit evaluations, tracing)
##
## * `xatol` - absolute tolerance for `x` values. Passed to
##   `isapprox(x_n, x_{n-1})`
## * `xrtol` - relative tolerance for `x` values. Passed to
##   `isapprox(x_n, x_{n-1})`
## * `atol`  - absolute tolerance for `f(x)` values.
## * `rtol`  - relative tolerance for `f(x)` values.
## * `maxevals`   - limit on maximum number of iterations
## * `maxfnevals` - limit on maximum number of function evaluations
## * `strict` - if `false` (the default), when the algorithm stops, possible
##   zeros are checked with a relaxed tolerance
## * `verbose` - if `true` a trace of the algorithm will be shown on
##   successful completion.

proc findZero*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod,
    B: AbstractBracketing, CF: CallableFunction[T, S]](fs: CF, x0: T|(T, T),
    methodes: A, N: B, tracks: Tracks[T, S]|NullTracks = NullTracks(),
    verbose = false, kwargs: varargs[UnivariateZeroOptions[T, T, S, S]]): T =
  let
    F = callable_functions(fs)
    state = initState(methodes, F, x0)
  var
    options: UnivariateZeroOptions[T, T, S, S]
    xstar: T

  if len(kwargs) == 0:
    options = initOptions(methodes, state)
  else:
    options = kwargs[0]

  if verbose and typeof(tracks) is NullTracks:
    var
      l: Tracks[T, S]
    new(l)
    when A is AbstractBracketing:
      xstar = findZero(methodes, F, options, state, l)
    else:
      xstar = findZero(methodes, N, F, options, state, l)

    when l is Tracks[T, S]:
      if verbose:
        showTrace(methodes, N, state, l)

    if classify(xstar) == fcNan:
      raise newException(ConvergenceError, "Stopped at: xn = " & $(state.xn1))
    else:
      return xstar
  else:
    let
      l = tracks
    when A is AbstractBracketing:
      xstar = findZero(methodes, F, options, state, l)
    else:
      xstar = findZero(methodes, N, F, options, state, l)

    when l is Tracks[T, S]:
      if verbose:
        showTrace(methodes, N, state, l)

    if classify(xstar) == fcNan:
      raise newException(ConvergenceError, "Stopped at: xn = " & $(state.xn1))
    else:
      return xstar

proc findZero*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod,
    B: AbstractBracketing](fs: proc(a: T): S, x0: T|(T, T), methodes: A, N: B,
    tracks: Tracks[T, S]|NullTracks = NullTracks(), verbose = false,
    kwargs: varargs[UnivariateZeroOptions[T, T, S, S]]): T =
  let
    F = callable_functions(fs)
    state = initState(methodes, F, x0)

  var
    options: UnivariateZeroOptions[T, T, S, S]
    xstar: T

  if len(kwargs) == 0:
    options = initOptions(methodes, state)
  else:
    options = kwargs[0]

  if verbose and typeof(tracks) is NullTracks:
    var
      l: Tracks[T, S]
    new(l)
    when A is AbstractBracketing:
      xstar = findZero(methodes, F, options, state, l)
    else:
      xstar = findZero(methodes, N, F, options, state, l)

    when l is Tracks[T, T]:
      if verbose:
        showTrace(methodes, N, state, l)

    if classify(xstar) == fcNan:
      raise newException(ConvergenceError, "Stopped at: xn = " & $(state.xn1))
    else:
      return xstar
  else:
    let
      l = tracks
    when A is AbstractBracketing:
      xstar = findZero(methodes, F, options, state, l)
    else:
      xstar = findZero(methodes, N, F, options, state, l)

    when l is Tracks[T, T]:
      if verbose:
        showTrace(methodes, N, state, l)

    if classify(xstar) == fcNan:
      raise newException(ConvergenceError, "Stopped at: xn = " & $(state.xn1))
    else:
      return xstar

proc findZero*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod,
    CF: CallableFunction[T, S]](fs: CF, x0: T|(T, T), methodes: A,
    tracks: Tracks[T, S]|NullTracks = NullTracks(), verbose = false,
    kwargs: varargs[UnivariateZeroOptions[T, T, S, S]]): T =
  let
    F = callable_functions(fs)
    state = initState(methodes, F, x0)

  var
    options: UnivariateZeroOptions[T, T, S, S]
    xstar: T

  if len(kwargs) == 0:
    options = initOptions(methodes, state)
  else:
    options = kwargs[0]

  if verbose and typeof(tracks) is NullTracks:
    var
      l: Tracks[T, S]
    new(l)
    xstar = findZero(methodes, F, options, state, l)

    when l is Tracks[T, S]:
      if verbose:
        showTrace(methodes, state, l)

    if classify(xstar) == fcNan:
      raise newException(ConvergenceError, "Stopped at: xn = " & $(state.xn1))
    else:
      return xstar
  else:
    let
      l = tracks
    xstar = findZero(methodes, F, options, state, l)

    when l is Tracks[T, S]:
      if verbose:
        showTrace(methodes, state, l)

    if classify(xstar) == fcNan:
      raise newException(ConvergenceError, "Stopped at: xn = " & $(state.xn1))
    else:
      return xstar

proc findZero*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod](fs: proc(
    a: T): S, x0: T|(T, T), methodes: A, tracks: Tracks[T,
    S]|NullTracks = NullTracks(), verbose = false, kwargs: varargs[
    UnivariateZeroOptions[T, T, S, S]]): T =
  let
    F = callable_functions(fs)
    state = initState(methodes, F, x0)

  var
    options: UnivariateZeroOptions[T, T, S, S]
    xstar: T

  if len(kwargs) == 0:
    options = initOptions(methodes, state)
  else:
    options = kwargs[0]

  if verbose and typeof(tracks) is NullTracks:
    var
      l: Tracks[T, S]
    new(l)
    xstar = findZero(methodes, F, options, state, l)

    when l is Tracks[T, T]:
      if verbose:
        showTrace(methodes, state, l)

    if classify(xstar) == fcNan:
      raise newException(ConvergenceError, "Stopped at: xn = " & $(state.xn1))
    else:
      return xstar
  else:
    let
      l = tracks
    xstar = findZero(methodes, F, options, state, l)

    when l is Tracks[T, T]:
      if verbose:
        showTrace(methodes, state, l)

    if classify(xstar) == fcNan:
      raise newException(ConvergenceError, "Stopped at: xn = " & $(state.xn1))
    else:
      return xstar

proc findZero*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod](fs: (proc(
    a: T): S, proc(a: T): S)|(proc(a: T): S, proc(a: T): S, proc(a: T): S),
    x0: T|(T, T), methodes: A, tracks: Tracks[T, S]|NullTracks = NullTracks(),
    verbose = false, kwargs: varargs[UnivariateZeroOptions[T, T, S, S]]): T =
  let
    F = callable_functions(fs)
    state = initState(methodes, F, x0)

  var
    options: UnivariateZeroOptions[T, T, S, S]
    xstar: T

  if len(kwargs) == 0:
    options = initOptions(methodes, state)
  else:
    options = kwargs[0]

  if verbose and typeof(tracks) is NullTracks:
    var
      l: Tracks[T, S]
    new(l)
    xstar = findZero(methodes, F, options, state, l)

    when l is Tracks[T, T]:
      if verbose:
        showTrace(methodes, state, l)

    if classify(xstar) == fcNan:
      raise newException(ConvergenceError, "Stopped at: xn = " & $(state.xn1))
    else:
      return xstar
  else:
    let
      l = tracks
    xstar = findZero(methodes, F, options, state, l)

    when l is Tracks[T, T]:
      if verbose:
        showTrace(methodes, state, l)

    if classify(xstar) == fcNan:
      raise newException(ConvergenceError, "Stopped at: xn = " & $(state.xn1))
    else:
      return xstar


# proc findZero*[Q: SomeNumber, T: SomeFloat](f: proc(a: Q): T, x0: Q,
#     kwargs: varargs): T =
#   return findZero(f, x0, Order0(), kwargs = kwargs)

# In Roots.jl here would be another find_zero
# but as updateState gets defined in the following modules
# it got moved to the bottom of bracketing.nim

proc findZero*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod,
    CF: CallableFunction[T, S]](M: A, F: CF, state: UnivariateZeroState[T, S],
    l: Tracks[T, S]|NullTracks = Nulltracks()) =
  let
    options = initOptions(M, state)

  findZero(M, F, options, state, l)
  return

proc findZero*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod](M: A, F: proc(
    a: T): S, state: UnivariateZeroState[T, S], l: Tracks[T,
    S]|NullTracks = Nulltracks()) =
  let
    options = initOptions(M, state)

  findZero(M, F, options, state, l)
  return

proc decideConvergence*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod,
                        CF: CallableFunction[T, S]](M: A, F: CF,
                            state: UnivariateZeroState[T, S],
                            options: UnivariateZeroOptions[T, T, S, S]): T =
  ## state has stopped, this identifies if it has converged
  let
    xn1 = state.xstar
    fxn1 = state.fxstar

  if state.stopped or (state.xConverged and not state.fConverged):
    when sizeof(T) == 8:
      for u in @[float(nextafter(cdouble(xn1), cdouble(-Inf))), float(nextafter(
          cdouble(xn1), cdouble(Inf)))]:
        let
          fu = F.f(u)
        if fu == 0.0 or fu * fxn1 < 0.0:
          state.message &= "Change of sign at xn identified. "
          state.fConverged = true
    else:
      for u in @[float32(nextafterf(cfloat(xn1), cfloat(-Inf))), float32(
          nextafterf(cfloat(xn1), cfloat(Inf)))]:
        let
          fu = F.f(u)
        if fu == 0.0 or fu * fxn1 < 0.0:
          state.message &= "Change of sign at xn identified. "
          state.fConverged = true

    if options.strict:
      if state.xConverged:
        state.fConverged = true
      else:
        state.convergenceFailed = true
    else:
      let
        xstar = state.xn1
        fxstar = state.fxn1

      if isFApprox0(fxstar, xstar, options.abstol, options.reltol,
          relaxed = true):
        (state.xstar, state.fxstar) = (xstar, fxstar)
        let
          msg = "Algorithm stopped early, but |f(xn)| < ϵ^(1/3)," &
                  " where ϵ depends on xn, rtol, and atol. "
        if state.message == "":
          state.message = msg
        else:
          state.message = state.message & "\n\t" & msg
        state.fConverged = true
      else:
        state.convergenceFailed = true

  if state.fConverged:
    when A is AbstractAlefeldPotraShi or A is Bisection or A is BisectionExact:
      return state.xstar
    else:
      return state.xn1

  if state.convergenceFailed:
    return T(NaN * xn1)

  return T(NaN)

# Switch to bracketing method
#M = Bisection()  # exact for floating point
#M = AlefeldPotraShi() # *usually* exact
#M = Brent()          # a bit faster, but not always convergent,
#                       as implemented (cf. RootTesting)
proc runBisection*[T, S: SomeFloat, A: AbstractBracketing,
    CF: CallableFunction[T, S]](N: A, f: CF, xs: (T, T),
        state: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T,
        S, S]) =
  let
    steps = state.steps
    fnevals = state.fnevals

  initState(state, N, f, xs)
  state.steps += steps
  state.fnevals += fnevals
  initOptions2(options, N)
  discard findZero(N, f, options, state)
  if xs[0] > xs[1]:
    state.message &= "Bracketing used over (" & $(xs[1]) & ", " & $(xs[0]) &
      "), those steps not shown. "
  else:
    state.message &= "Bracketing used over (" & $(xs[0]) & ", " & $(xs[1]) &
      "), those steps not shown. "

proc runBisection*[T, S: SomeFloat, A: AbstractBracketing](
    N: A, f: proc(a: T): S, xs: (T, T), state: UnivariateZeroState[T, S],
        options: UnivariateZeroOptions[T, T, S, S]) =
  let
    steps = state.steps
    fnevals = state.fnevals

  initState(state, N, f, xs)
  state.steps += steps
  state.fnevals += fnevals
  initOptions2(options, N)
  discard findZero(N, f, options, state)
  if xs[0] > xs[1]:
    state.message &= "Bracketing used over (" & $(xs[1]) & ", " & $(xs[0]) &
      "), those steps not shown. "
  else:
    state.message &= "Bracketing used over (" & $(xs[0]) & ", " & $(xs[1]) &
      "), those steps not shown. "
