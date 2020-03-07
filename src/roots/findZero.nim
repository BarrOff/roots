import math

type
  # Methods
  AbstractUnivariateZeroMethod* = ref object of RootObj
  AbstractBracketing* = ref object of AbstractUnivariateZeroMethod
  AbstractNonBracketing* = ref object of AbstractUnivariateZeroMethod
  AbstractSecant* = ref object of AbstractNonBracketing

  # States
  AbstractUnivariateZeroState* = ref object of RootObj
  UnivariateZeroState*[T, S] = ref object of AbstractUnivariateZeroState
    xn0*, xn1*: T
    m*: seq[T]
    fxn0*, fxn1*: S
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

  # Tracks (for logging actual steps)
  # when no logging this should get optimized out to avoid a branch
  AbstractTracks* = ref object of Rootobj
  NullTracks* = ref object of AbstractTracks
  Tracks*[T, S: SomeFloat] = ref object of AbstractTracks
    xs*: seq[T]
    fs*: seq[S]

  # Function Types
  CallableFunction* = ref object of RootObj
  DerivativeFree*[F] = ref object of CallableFunction
    f*: F
  FirstDerivative*[F,FP] = ref object of CallableFunction
    f*: F
    fp*: FP
  SecondDerivative*[F,FP,FPP] = ref object of CallableFunction
    f*: F
    fp*: FP
    fpp*: FPP
  ConvergenceError* = object of Exception

# imports from C
proc nextafterf*(a, b: cfloat): cfloat {.header: "<math.h>", importc: "nextafterf".}
proc nextafter*(a, b: cdouble): cdouble {.header: "<math.h>", importc: "nextafter".}


# forward declarations
proc decideConvergence*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod, CF: CallableFunction](M: A, F: CF,
                                                                          state: UnivariateZeroState[T, S],
                                                                          options: UnivariateZeroOptions[T, T, S, S]): T




## Start library functions


proc incfn*[T, S: SomeFloat](o: UnivariateZeroState[T, S], k = 1) =
  o.fnevals += k
proc incsteps*[T, S: SomeFloat](o: UnivariateZeroState[T, S], k = 1) =
  o.steps += k

# initState2 resembles the init_state function of Julia
# initialize state for most methods
proc initState2*[T: SomeFloat, A: AbstractUnivariateZeroMethod, CF: CallableFunction or proc (a: float): T](methodes: A, fs: CF, x: SomeNumber): UnivariateZeroState[float, T] =
  let
    x1 = float(x)
    fnevals = 1
    state: UnivariateZeroState[float, T]
  when typeof(fs) is CallableFunction:
    let
      fx1 = fs.f(x1)
  else:
    let
      fx1 = fs(x1)

  new(state)
  state.x1 = x1
  state.fx1 = fx1
  state.fnevals = fnevals
  state.stopped = false
  state.xConverged = false
  state.fConverged = false
  state.convergenceFailed = false

  return state
 
# initState3 resembles the init_state! function of Julia
## This function is used to reset the state to an initial value
## As initializing a state is somewhat costly, this can be useful when many
## function calls would be used.
## An example usage, might be:
# M = Order1()
# state = Roots.init_state(M, f1, 0.9)
# options = Roots.init_options(M, state)
# out = zeros(Float64, n)
# for (i,x0) in enumerate(linspace(0.9, 1.0, n))
#    Roots.init_state!(state, M, f1, x0)
#    out[i] = find_zero(M, f1, options, state)
# end
# init_state has a method call variant
proc initState3*[T, S: SomeFloat](state: UnivariateZeroState[T, S], x1, x0: T, m: seq[T], y1, y0: S, fm: seq[S]) =
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

proc initState3*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod, CF: CallableFunction or proc (fx: float): float](state: UnivariateZeroState[T, S], a: A, fs: CF, x: T) =
  let
    x1 = float(x)
  when typeof(fs) is CallableFunction:
    let
      fx1 = fs.f(x1)
  else:
    let
      fx1 = fs(x1)

  initState3(state, x1, float(0.0), @[T],
             fx1, float(0.0), @[S])


proc copyState*[T, S: SomeNumber](state: UnivariateZeroState[T, S]): UnivariateZeroState[T, S] =
  result.xn1 = state.xn1
  result.xn0 = state.xn0
  result.m = state.m
  result.fxn1 = state.fxn1
  result.fxn0 = state.fxn0
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


#     default_tolerances(Method, [T], [S])

# The default tolerances for most methods are `xatol=eps(T)`,
# `xrtol=eps(T)`, `atol=4eps(S)`, and `rtol=4eps(S)`, with the proper
# units (absolute tolerances have the units of `x` and `f(x)`; relative
# tolerances are unitless). For `Complex{T}` values, `T` is used.

# The number of iterations is limited by `maxevals=40`, the number of
# function evaluations is not capped, due to `maxfnevals=typemax(Int)`,
# and `strict=false`.

template defaultTolerances*[A: AbstractUnivariateZeroMethod](M: A) =
  defaultTolerances(M, float, float)

proc defaultTolerances*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod](M: A, Ti: typedesc[T], Si: typedesc[S]): (T, T, S, S, int, int, bool) =
  when sizeof(T) == 8:
    let
      xatol = nextafter(1.0, 2.0 ) - 1.0
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

# represents the init_options function of Julia
proc initOptions*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod](M: A, state: UnivariateZeroState[T, S]): UnivariateZeroOptions[T, T, S, S] =
  let
    defs = defaultTolerances(M, T, S)


  new(result)
  result.xabstol = defs[0]
  result.xreltol = defs[1]
  result.abstol = defs[2]
  result.reltol = defs[3]
  result.maxevals = defs[4]
  result.maxfnevals = defs[5]
  result.strict = defs[6]

  return result

# represents the init_options! function of Julia
# reset options to default values
proc initOptions2*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod](options: UnivariateZeroOptions[T, T, S, S], M: A) =
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

proc logStep*[T, S: SomeFloat](s: Tracks[T, S], M: bool, o: UnivariateZeroState[T, S]) =
  add(s.xs, o.xn1)
  add(s.fs, o.fxn1)
  return

proc logStep*[T, S: SomeFloat](s: Tracks[T, S], M: bool, o: UnivariateZeroState[T, S], init: int) =
  logStep(s, M, o)

proc showTracks*[T, S: SomeFloat, A: AbstractBracketing](l: Tracks[T, S], M: A) =
  when M is AbstractBracketing:
    var
      xs = l.xs
      n = len(xs)
    
    echo "TO BE DONE!"
    return
  else:
    for i in 0..high(s.xs):
      echo i, ": xs = ", s.xs[i], " fs: ", s.fs[i]
    echo ""
    return



# CallableFunction procs
## Return f, f/f'
proc fDeltaX*[T, S: SomeNumber](F: DerivativeFree[proc(a: S): T], x: S): T =
  return F.f(x)

proc fDeltaX*[T, S: SomeNumber](F: FirstDerivative[proc(a: S): T, proc(b: S): T]|SecondDerivative[proc(a: S): T, proc(b: S): T, proc(c: S): T], x: S): (T, T) =
  let
    fx = F.f(x)
    fpx = F.fp(x)

  return (fx, fx / fpx)

# return f, f/f', f'/f'' (types T, S, S)
proc fDDeltaX*[T, S: SomeNumber](F: DerivativeFree[proc(a: S): T], x: S): T =
  return F.f(x)

proc fDDeltaX*[T, S: SomeNumber](F: SecondDerivative[proc(a: S): T, proc(b: S): T, proc(c: S): T], x: S): (T, T, T) =
  let
    fx = F.f(x)
    fp = F.fp(x)
    fpp = F.fpp(x)

  return (fx, fx / fp, fp / fpp)

# represents the _callable_function function of Julia
proc callableFunctions*[CF: CallableFunction](fs: CF): CF =
  return fs

proc callableFunctions*[T, S: SomeFloat](fs: proc(a: T): S): DerivativeFree[proc(a: T): S] =
  new(result)
  result.f = fs

proc callableFunctions*[T, S](fs: (proc(a: T): S, proc(a: T): S)): FirstDerivative[proc(a: T): S, proc(a: T): S] =
  new(result)
  result.f = fs[0]
  result.fp = fs[1]

proc callableFunctions*[T, S](fs: (proc(a: T): S, proc(a: T): S, proc(a: T): S)): SecondDerivative[proc(a: T): S, proc(a: T): S, proc(a: T): S] =
  new(result)
  result.f = fs[0]
  result.fp = fs[1]
  result.fpp = fs[2]





## Assess convergence
proc isFApprox0*[T: SomeFloat](fa, a, atol, rtol: T, relaxed: bool): bool {.inline.} =
  let
    aa = abs(a)
    afa = abs(fa)
  var
    tol = max(atol, aa * rtol)
  tol = abs(pow(tol, 1/3))

  return afa < tol

proc isFApprox0*[T: SomeFloat](fa, a, atol, rtol: T): bool {.inline.} =
  let
    aa = abs(a)
    afa = abs(fa)
    tol = max(atol, aa * rtol)

  return afa < tol

# roots.assess_convergence(method, state, options)
#
# Assess if algorithm has converged.
#
# If alogrithm hasn't converged returns `false`.
#
# If algorithm has stopped or converged, return `true` and sets one of `state.stopped`, `state.xConverged`,  `state.fConverged`, or `state.convergenceFailed`; as well, a message may be set.
#
# * `state.xConverged = true` if `abs(xn1 - xn0) < max(xatol, max(abs(xn1), abs(xn0)) * xrtol)`
#
# * `state.fConverged = true` if  `|f(xn1)| < max(atol, |xn1|*rtol)`
#
# * `state.convergenceFailed = true` if xn1 or fxn1 is `NaN` or an infinity
#
# * `state.stopped = true` if the number of steps exceed `maxevals` or the number of function calls exceeds `maxfnevals`.
#
# In `findZero`, stopped values (and xConverged) are checked for convergence with a relaxed tolerance.
proc assessConvergence*[T, S: SomeFloat](methodes: bool, state: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]): bool =
  let
    xn0 = state.xn0
    xn1 = state.xn1
    fxn1 = state.fxn1

  if (state.converged or state.fConverged or state.stopped):
    return true

  if xn1 == NaN or fxn1 == NaN:
    state.convergenceFailed = true
    state.message &= "NaN produced by algorithm. "
    return true

  if abs(xn1) == Inf or abs(fxn1) == Inf:
    state.convergenceFailed = true
    state.message &= "Inf produced by algorithm. "
    return true
  
  # f(xstar) ≈ xstar * f'(xstar)*eps(), so we pass in lambda
  if isFApprox0(fxn1, xn1, options.abstol, options.reltol):
    state.fConverged = true
    return true

  # stop when xn1 ~ xn.
  # in find_zeros there is a check that f could be a zero with a relaxed tolerance
  if abs(xn1 - xn0) < max(options.xabstol, max(abs(xn1), abs(xn0)) * options.xreltol):
    state.message &= "x_n ≈ x_(n-1). "
    state.converged = true
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

proc showTrace*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod, B: AbstractBracketing](methodes: A, N: B, state: UnivariateZeroState[T, S], tracks: Tracks[T, S]) =
  let
    converged = state.xConverged or state.fConverged

  echo "Results of univariate zero finding:"

  if converged:
    echo "* Converged to: ", state.xn1
    if N == nil and methodes of AbstractBracketing:
      echo "* Algorithm: "#, $(methodes)
    else:
      echo "* Algorithm: ", " with possible bracketing with "#, $(N) #$(methodes),

    echo "* iterations: ", $(state.steps)
    echo "* function evaluations: ", $(state.fnevals)
    if state.xConverged:
      echo "* stopped as x_n ≈ x_(n - 1) using atol = xatol, rtol=xrtol"
    if state.fConverged and state.message == "":
      echo "* stopped as |f(x_n)| ≤ max(δ, max(1,|x|)⋅ϵ) using δ = atol, ϵ = rtol"
    if state.message != "":
      echo "* Note: ", "(state.message)"
  else:
    echo "* Convergence failed: ", $(state.message)
    # echo "* Algorithm ", $(methodes)                                  # $(AbstractUnivariateZeroMethod) implementieren!

  echo ""
  echo "Trace: "
  showTracks(tracks, methodes)




# find_zero(fs, x0, method; kwargs...)

# Interface to one of several methods for find zeros of a univariate function.
proc findZero*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod, B: AbstractBracketing, CF: CallableFunction or proc(a: T): S](fs: CF, x0: T, methodes: A, N: B = nil, tracks: Tracks[T, S]|NullTracks = NullTracks(), verbose = false, kwargs: varargs[UnivariateZeroOptions[T, T, S, S]]): T =
  let
    F = callable_functions(fs)
    state = initState2(methodes, fs, x0)
    xstar: T

  var
    options: UnivariateZeroOptions[T, T, S, S]

  if len(kwargs) == 0:
    options = initOptions(methodes, state)
  else:
    options = kwargs

  if verbose and typeof(tracks) is NullTracks:
    var
      l: Tracks[T, S]
    new(l)
    if N == nil or methodes of AbstractBracketing:
        xstar = findZero(methodes, F, options, state, l)
    else:
        xstar = findZero(methodes, N, F, options, state, l)

    when l is Tracks[T, T]:
      if verbose:
        showTrace(methodes, N, state, l)

    if xstar == NaN:
      raise newException(ConvergenceError, "Stopped at: xn = " & $(state.xn1))
    else:
      return xstar
  else:
    let
      l = tracks
    if N == nil or methodes of AbstractBracketing:
        xstar = findZero(methodes, F, options, state, l)
    else:
        xstar = findZero(methodes, N, F, options, state, l)

    when l is Tracks[T, T]:
      if verbose:
        showTrace(methodes, N, state, l)

    if xstar == NaN:
      raise newException(ConvergenceError, "Stopped at: xn = " & $(state.xn1))
    else:
      return xstar

# proc findZero*[Q: SomeNumber, T: SomeFloat](f: proc(a: Q): T, x0: Q, kwargs: varargs): T =
#   return findZero(f, x0, Order0(), kwargs)                     Order0 not yet implemented

# state has stopped, this identifies if it has converged
proc decideConvergence*[T, S: SomeFloat, A: AbstractUnivariateZeroMethod, CF: CallableFunction](M: A, F: CF,
                                                                          state: UnivariateZeroState[T, S],
                                                                          options: UnivariateZeroOptions[T, T, S, S]): T =
  let
    xn1 = state.xn1
    fxn1 = state.fxn1

  if state.stopped or (state.xConverged and not state.fConverged):
    when sizeof(T) == 8:
      for u in @[float(nextafter(cdouble(xn1), cdouble(-Inf))), float(nextafter(cdouble(xn1), cdouble(Inf)))]:
        let
          fu = F.f(u)
        if fu == 0.0 or fu * fxn1 < 0.0:
          state.message &= "Change of sign at xn identified. "
          state.fConverged = true
    else:
      for u in @[float32(nextafterf(cfloat(xn1), cfloat(-Inf))), float32(nextafterf(cfloat(xn1), cfloat(Inf)))]:
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

      if isFApprox0(fxstar, xstar, options.abstol, options.reltol, relaxed = true):
        let
          msg = "Algorithm stopped early, but |f(xn)| < ϵ^(1/3), where ϵ depends on xn, rtol, and atol. "
        if state.message == "":
          state.message = msg
        else:
          state.message = state.message & "\n\t" & msg
        state.fConverged = true
      else:
        state.convergenceFailed = true

  if state.fConverged:
    return state.xn1

  if state.convergenceFailed:
    return T(NaN)

  return T(NaN)

# Switch to bracketing method
#M = Bisection()  # exact for floating point
#M = AlefeldPotraShi() # *usually* exact
#M = Brent()          # a bit faster, but not always convergent, as implemented (cf. RootTesting)
proc runBisection*[T, S: SomeFloat, A: AbstractBracketing](N: A, f: proc(a: T): S, xs: (T, T),
                                                           state: UnivariateZeroState[T, S],
                                                           options: UnivariateZeroOptions[T, T, S, S]) =
  let
    steps = state.steps
    fnevals = state.fnevals

  initState2(state, N, f, xs)
  state.steps += steps
  state.fnevals += fnevals
  initOptions2(options, N)
  findZero(N, f, options, state)
  if xs[0] > xs[1]:
    state.message &= "Bracketing used over (" & $(xs[1]) & ", " & $(xs[0]) & "), those steps not shown. "
  else:
    state.message &= "Bracketing used over (" & $(xs[0]) & ", " & $(xs[1]) & "), those steps not shown. "
