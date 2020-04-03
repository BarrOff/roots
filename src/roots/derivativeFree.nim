import math
import utils, findZero

type
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

# forward declarations
proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](methodes: Order1, fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S])
proc updateState*[T, S: SomeFloat](methodes: Order1, fs: proc(a: T): S, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S])
proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](methodes: Order1B, fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S])
proc updateState*[T, S: SomeFloat](methodes: Order1B, fs: proc(a: T): S, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S])
proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](methodes: King, fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S])
proc updateState*[T, S: SomeFloat](methodes: King, fs: proc(a: T): S, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S])
proc steffStep*[T, S: SomeFloat](M: Order5|Order8|Order16, x: T, fx: S): T

proc doGuardedStep[T, S: SomeFloat](M: AbstractSecant, o: UnivariateZeroState[T, S]): bool {.inline.} =
  let
    (x, fx) = (o.xn1, o.fxn1)

  return 1000 * abs(fx) > T(max(S(1), abs(x) * S(1) / T(1)))

proc updateStateGuarded[T, S: SomeFloat, AS: AbstractSecant, AN, AP: AbstractUnivariateZeroMethod, CF: CallableFunction[T, S]](M: AS, N: AN, P: AP, fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  if doGuardedStep(M, o):
    updateState(N, fs, o, options)
  else:
    updateState(P, fs, o, options)

proc updateStateGuarded[T, S: SomeFloat, AS: AbstractSecant, AN, AP: AbstractUnivariateZeroMethod](M: AS, N: AN, P: AP, fs: proc(a: T): S, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  if doGuardedStep(M, o):
    updateState(N, fs, o, options)
  else:
    updateState(P, fs, o, options)

proc initState*[T, S: SomeFloat, CF: CallableFunction[T, S], AS: AbstractSecant](methodes: AS, fs: CF, x:T): UnivariateZeroState[float, S] =
  let
    x1 = float(x)
    x0 = defaultSecantStep(x1)
  return initState(methodes, fs, (x0, x1))

proc initState*[T: SomeNumber, S: SomeFloat, AS: AbstractSecant](methodes: AS, fs: proc(a: T): S, x:T): UnivariateZeroState[float, S] =
  let
    x1 = float(x)
    x0 = defaultSecantStep(x1)
  return initState(methodes, fs, (x0, x1))

proc initState*[T, S: SomeFloat, CF: CallableFunction[T, S], AS: AbstractSecant](methodes: AS, fs: CF, x: (T, T)): UnivariateZeroState[float, S] =
  let
    (x0, x1) = (float(x[0]), float(x[1]))
    (fx0, fx1) = (fs.f(x0), fs.f(x1))

  var
    state: UnivariateZeroState[float, S]

  new(state)
  state.xn1 = x1
  state.xn0 = x0
  state.xstar = float(0)
  state.fxn1 = fx1
  state.fxn0 = fx0
  state.fxstar = fx1
  state.fnevals = 2
  state.stopped = false
  state.xConverged = false
  state.fConverged = false
  state.convergenceFailed = false

  return state

proc initState*[T, S: SomeFloat, AS: AbstractSecant](methodes: AS, fs: proc(a: T): S, x: (T, T)): UnivariateZeroState[float, S] =
  let
    (x0, x1) = (float(x[0]), float(x[1]))
    (fx0, fx1) = (fs(x0), fs(x1))

  var
    state: UnivariateZeroState[float, S]

  new(state)
  state.xn1 = x1
  state.xn0 = x0
  state.xstar = float(0)
  state.fxn1 = fx1
  state.fxn0 = fx0
  state.fxstar = fx1
  state.fnevals = 2
  state.stopped = false
  state.xConverged = false
  state.fConverged = false
  state.convergenceFailed = false

  return state


proc initState*[T, S: SomeFloat, CF: CallableFunction[T, S], AS: AbstractSecant](state: UnivariateZeroState[float, S], methodes: AS, fs: CF, x: T) =
  let
    x1 = float(x)
    x0 = defaultSecantStep(x1)
  initState(state, methodes, fs, (x0, x1))
  return

proc initState*[T: SomeNumber, S: SomeFloat, AS: AbstractSecant](state: UnivariateZeroState[float, S], methodes: AS, fs: proc(a: T): S, x: T) =
  let
    x1 = float(x)
    x0 = defaultSecantStep(x1)
  initState(state, methodes, fs, (x0, x1))
  return

proc initState*[T, S: SomeFloat, CF: CallableFunction[T, S], AS: AbstractSecant](state: UnivariateZeroState[float, S], M: AS, f: CF, x: (T, T)) =
  let
    (x0, x1) = (float(x[0]), float(x[1]))
    (fx0, fx1) = (f.f(x0), f.f(x1))
  initState(state, x1, x0, seq[float], fx1, fx0, seq[S])
  state.fnevals = 2
  return

proc initState*[T: SomeNumber, S: SomeFloat, AS: AbstractSecant](state: UnivariateZeroState[float, S], M: AS, f: proc(a: T): S, x: (T, T)) =
  let
    (x0, x1) = (float(x[0]), float(x[1]))
    (fx0, fx1) = (f(x0), f(x1))
  initState(state, x1, x0, seq[float], fx1, fx0, seq[S])
  state.fnevals = 2
  return


# Order0

proc findZero*[T, S: SomeFloat, AT: Tracks[T, S] or NullTracks, CF: CallableFunction[T, S]](fs: CF, x0: T, methodes: Order0,
                                                               tracks: AT = NullTracks(),
                                                               verbose = false,
                                                               kwargs: varargs[UnivariateZeroOptions[T, T, S, S]]): T =
  let
    M = Order1()
    N = AlefeldPotraShi()
  var
    l: Tracks[T, S]

  when AT is NullTracks:
    new(l)
  else:
    l = tracks

  if len(kwargs) == 0:
    return findZero(callable_functions(fs), x0, M, N, tracks=l, verbose = verbose)
  else:
    return findZero(callable_functions(fs), x0, M, N, tracks=l, verbose = verbose, kwargs = kwargs[0])

proc findZero*[T, S: SomeFloat, AT: Tracks[T, S] or NullTracks](fs: proc(a: T): S, x0: T, methodes: Order0,
                                                               tracks: AT = NullTracks(),
                                                               verbose = false,
                                                               kwargs: varargs[UnivariateZeroOptions[T, T, S, S]]): T =
  let
    M = Order1()
    N = AlefeldPotraShi()
  var
    l: Tracks[T, S]

  when AT is NullTracks:
    new(l)
  else:
    l = tracks

  if len(kwargs) == 0:
    return findZero(callable_functions(fs), x0, M, N, tracks=l, verbose = verbose)
  else:
    return findZero(callable_functions(fs), x0, M, N, tracks=l, verbose = verbose, kwargs = kwargs[0])


# Secant

proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](methodes: Order1, fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  let
    (xn0, xn1) = (o.xn0, o.xn1)
    (fxn0, fxn1) = (o.fxn0, o.fxn1)

    delta = fxn1 * (xn1 - xn0) / (fxn1 - fxn0)
    fd = classify(abs(delta))

  if fd == fcInf or fd == fcNan:
    o.stopped = true
    o.message = "Increment `Δx` has issues. "
    return

  o.xn0 = xn1
  o.xn1 -= delta
  o.fxn0 = fxn1
  o.fxn1 = fs.f(o.xn1)
  incfn(o)

  return

proc updateState*[T, S: SomeFloat](methodes: Order1, fs: proc(a: T): S, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  let
    (xn0, xn1) = (o.xn0, o.xn1)
    (fxn0, fxn1) = (o.fxn0, o.fxn1)

    delta = fxn1 * (xn1 - xn0) / (fxn1 - fxn0)
    fd = classify(abs(delta))

  if fd == fcInf or fd == fcNan:
    o.stopped = true
    o.message = "Increment `Δx` has issues. "
    return

  o.xn0 = xn1
  o.xn1 -= delta
  o.fxn0 = fxn1
  o.fxn1 = fs(o.xn1)
  incfn(o)

  return




# Order1B

proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](methodes: Order1B, fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  updateStateGuarded(methodes, Secant(), King(), fs, o, options)
  return

proc updateState*[T, S: SomeFloat](methodes: Order1B, fs: proc(a: T): S, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  updateStateGuarded(methodes, Secant(), King(), fs, o, options)
  return

proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](methodes: King, fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  let
    (x0, x1) = (o.xn0, o.xn1)
    (fx0, fx1) = (o.fxn0, o.fxn1)

  # G(x,f0,f_1) = -fx^2/(f_1 - f0)
  var
    f0 = fx1
    f1 = fs.f(x1 - T(f0))
    G0: S
  incfn(o, 1)

  let
    G1 = -(f0^2 / (f1 - f0))

  if len(o.fm) == 0:
    f0 = fx0
    f1 = fs.f(x0 - T(f0))
    incfn(o, 1)
    G0 = -(f0^2 / (f1 - f0))
  else:
    G0 = o.fm[0]

  let
    m = (x1 - x0) / (G1 - G0)
  if abs(m) <= 1e-2:
    #@info "small m estimate, stopping"
    o.stopped = true
    o.message = "Estimate for multiplicity has issues. "
    return

  let
    delta = G1 * (x1 - x0) / (G1 - G0)
  o.fm = @[G1]

  if isIssue(delta):
    o.stopped = true
    o.message = "Increment `Δx` has issues. "
    return

  (o.xn0, o.fxn0) = (o.xn1, o.fxn1)
  o.xn1 -= delta
  o.fxn1 = fs.f(o.xn1)
  incfn(o)

  return

proc updateState*[T, S: SomeFloat](methodes: King, fs: proc(a: T): S, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  let
    (x0, x1) = (o.xn0, o.xn1)
    (fx0, fx1) = (o.fxn0, o.fxn1)


  # G(x,f0,f_1) = -fx^2/(f_1 - f0)
  var
    f0 = fx1
    f1 = fs(x1 - T(f0))
    G0: S
  incfn(o, 1)

  let
    G1 = -(f0^2 / (f1 - f0))

  if len(o.fm) == 0:
    f0 = fx0
    f1 = fs(x0 - T(f0))
    incfn(o, 1)
    G0 = -(f0^2 / (f1 - f0))
  else:
    G0 = o.fm[0]

  let
    m = (x1 - x0) / (G1 - G0)
  if abs(m) <= 1e-2:
    #@info "small m estimate, stopping"
    o.stopped = true
    o.message = "Estimate for multiplicity has issues. "
    return

  let
    delta = G1 * (x1 - x0) / (G1 - G0)
  o.fm = @[G1]

  if isIssue(delta):
    o.stopped = true
    o.message = "Increment `Δx` has issues. "
    return

  (o.xn0, o.fxn0) = (o.xn1, o.fxn1)
  o.xn1 -= delta
  o.fxn1 = fs.f(o.xn1)
  incfn(o)

  return


# Order2

proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](methodes: Order2, fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  updateStateGuarded(methodes, Secant(), Steffensen(), fs, o, options)
  return

proc updateState*[T, S: SomeFloat](methodes: Order2, fs: proc(a: T): S, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  updateStateGuarded(methodes, Secant(), Steffensen(), fs, o, options)
  return

proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](methodes: Steffensen, fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  let
    (x0, x1) = (o.xn0, o.xn1)
    (fx0, fx1) = (o.fxn0, o.fxn1)
    sign = sgn((fx1 - fx0) / (x1 - x0))
    x2 = x1 - T(sign) * T(fx1)
    f0 = fx1
    f1 = fs.f(x2)
  incfn(o, 1)

  let
    delta = - S(sign) * f0 * f0 / (f1 - f0)

  if isIssue(delta):
    o.stopped = true
    o.message = "Increment `Δx` has issues. "
    return

  (o.xn0, o.fxn0) = (o.xn1, o.fxn1)
  o.xn1 -= delta
  o.fxn1 = fs.f(o.xn1)
  incfn(o)

  return

proc updateState*[T, S: SomeFloat](methodes: Steffensen, fs: proc(a: T): S, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  let
    (x0, x1) = (o.xn0, o.xn1)
    (fx0, fx1) = (o.fxn0, o.fxn1)
    sign = sgn((fx1 - fx0) / (x1 - x0))
    x2 = x1 - T(sign) * T(fx1)
    f0 = fx1
    f1 = fs(x2)
  incfn(o, 1)

  let
    delta = - S(sign) * f0 * f0 / (f1 - f0)

  if isIssue(delta):
    o.stopped = true
    o.message = "Increment `Δx` has issues. "
    return

  (o.xn0, o.fxn0) = (o.xn1, o.fxn1)
  o.xn1 -= delta
  o.fxn1 = fs(o.xn1)
  incfn(o)

  return


# Order2B

proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](methodes: Order2B, fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  updateStateGuarded(methodes, Secant(), Esser(), fs, o, options)
  return

proc updateState*[T, S: SomeFloat](methodes: Order2B, fs: proc(a: T): S, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  updateStateGuarded(methodes, Secant(), Esser(), fs, o, options)
  return

proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](methodes: Esser, fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  let
    (x1, fx1) = (o.xn1, o.fxn1)

    f0 = fx1
    f1 = fs.f(x1 + T(f0))
    fs1 = fs.f(x1 - T(f0))
  incfn(o, 2)

  # h = f0
  # r1 = f/f' ~ f/f[x+h,x-h]
  # r2 = f'/f'' ~ f[x+h, x-h]/f[x-h,x,x+h]
  let
    r1 = f0 * 2 * f0 / (f1 - fs1)
    r2 = (f1 - fs1) / (f1 - 2 * f0 + fs1) * f0/2

    k = r2 / (r2 - r1)  # ~ m

  if abs(k) <= 1e-2:
    #@info "estimate for m is *too* small"
    o.stopped = true
    o.message = "Estimate for multiplicity had issues. "
    return

  let
    delta = k * r1

  if isIssue(delta):
    o.stopped = true
    o.message = "Increment `Δx` has issues. "
    return

  (o.xn0, o.fxn0) = (o.xn1, o.fxn1)
  o.xn1 -= delta
  o.fxn1 = fs.f(o.xn1)
  incfn(o)

  return

proc updateState*[T, S: SomeFloat](methodes: Esser, fs: proc(a: T): S, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  let
    (x1, fx1) = (o.xn1, o.fxn1)

    f0 = fx1
    f1 = fs(S(x1) + f0)
    fs1 = fs(S(x1) - f0)
  incfn(o, 2)

  # h = f0
  # r1 = f/f' ~ f/f[x+h,x-h]
  # r2 = f'/f'' ~ f[x+h, x-h]/f[x-h,x,x+h]
  let
    r1 = f0 * 2 * f0 / (f1 - f_1)
    r2 = (f1 - f_1) / (f1 - 2 * f0 + f_1) * f0/2

    k = r2 / (r2 - r1)  # ~ m

  if abs(k) <= 1e-2:
    #@info "estimate for m is *too* small"
    o.stopped = true
    o.message = "Estimate for multiplicity had issues. "
    return

  let
    delta = k * r1

  if isIssue(delta):
    o.stopped = true
    o.message = "Increment `Δx` has issues. "
    return

  (o.xn0, o.fxn0) = (o.xn1, o.fxn1)
  o.xn1 -= delta
  o.fxn1 = fs(o.xn1)
  incfn(o)

  return

# Order5

proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](M: Order5|KumarSinghAkanksha, fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  let
    xn = o.xn1
    fxn = o.fxn1

  when typeof(M) is Order5:
    let
      wn = steffStep(M, xn, fxn)
  else:
    let
      wn = steffStep(xn, fxn)
  let
    fwn = fs.f(wn)
  incfn(o)

  var
    (fp, issue) = fbracket(o.xn1, wn, o.fxn1, fwn)
  if issue:
    (o.xn0, o.xn1) = (o.xn1, wn)
    (o.fxn0, o.fxn1) = (o.fxn1, fwn)
    o.message = "Issue with divided difference f[xn, wn]. "
    o.stopped = true
    return

  let
    yn = o.xn1 - T(o.fxn1 / fp)
    fyn = fs.f(yn)
  incfn(o)

  let
    zn = xn - T((fxn + fyn) / fp)
    fzn = fs.f(zn)
  incfn(o)

  (fp, issue) = fbracketRatio(yn, o.xn1, wn, fyn, o.fxn1, fwn)
  if issue:
    (o.xn0, o.xn1) = (o.xn1, yn)
    (o.fxn0, o.fxn1) = (o.fxn1, fyn)
    o.message = "Issue with f[xn,yn]*f[yn,wn] / f[xn, wn]"
    o.stopped = true
    return

  o.xn0 = o.xn1
  o.fxn0 = o.fxn1
  o.xn1 = zn - T(fzn / fp)
  o.fxn1 = fs.f(o.xn1)
  incfn(o)

  return

proc updateState*[T, S: SomeFloat](M: Order5|KumarSinghAkanksha, fs: proc(a: T): S, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  let
    xn = o.xn1
    fxn = o.fxn1

  when typeof(M) is Order5:
    let
      wn = steffStep(M, xn, fxn)
  else:
    let
      wn = steffStep(xn, fxn)
  let
    fwn = fs(wn)
  incfn(o)

  var
    (fp, issue) = fbracket(o.xn1, wn, o.fxn1, fwn)
  if issue:
    (o.xn0, o.xn1) = (o.xn1, wn)
    (o.fxn0, o.fxn1) = (o.fxn1, fwn)
    o.message = "Issue with divided difference f[xn, wn]. "
    o.stopped = true
    return

  let
    yn = o.xn1 - T(o.fxn1 / fp)
    fyn = fs(yn)
  incfn(o)

  let
    zn = xn - T((fxn + fyn) / fp)
    fzn = fs(zn)
  incfn(o)

  (fp, issue) = fbracketRatio(yn, o.xn1, wn, fyn, o.fxn1, fwn)
  if issue:
    (o.xn0, o.xn1) = (o.xn1, yn)
    (o.fxn0, o.fxn1) = (o.fxn1, fyn)
    o.message = "Issue with f[xn,yn]*f[yn,wn] / f[xn, wn]"
    o.stopped = true
    return

  o.xn0 = o.xn1
  o.fxn0 = o.fxn1
  o.xn1 = zn - T(fzn / fp)
  o.fxn1 = fs(o.xn1)
  incfn(o)

  return


# If we have a derivative, we have this. (Deprecate?)
proc updateState*[T, S: SomeFloat](methodes: Order5, fs: FirstDerivative|SecondDerivative, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  let
    (xn, fxn) = (o.xn1, o.fxn1)
    (a, b) = fDeltaX(fs, xn)
    fpxn = S(a) / b
  incfn(o)

  if isIssue(fpxn):
    o.stopped = true
    return

  let
    yn = xn - T(fxn / fpxn)
    (fyn, deltaYn) = fDeltaX(fs, yn)
    fpyn = S(fyn) / deltaYn
  incfn(o, 2)

  if isIssue(fpyn):
    (o.xn0, o.xn1) = (xn, yn)
    (o.fxn0, o.fxn1) = (fxn, fyn)
    o.stopped = true
    return

  let
    zn = xn - T((fxn + fyn) / fpxn)
    fzn = fs.f(zn)
  incfn(o, 1)

  let
    xn1 = zn - T(fzn / fpyn)
    fxn1 = fs.f(xn1)
  incfn(o, 1)

  (o.xn0, o.xn1) = (xn, xn1)
  (o.fxn0, o.fxn1) = (fxn, fxn1)

  return


# Order8

proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](M: Thukral8|Order8, fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  let
    xn = o.xn1
    fxn = o.fxn1
    
  when typeof(M) is Order8:
    let
      wn = steffStep(M, xn, fxn)
  else:
    let
      wn = steffStep(xn, fxn)
  let
    fwn = fs.f(wn)
  incfn(o)

  if isIssue(fwn):
    (o.xn0, o.xn1) = (xn, wn)
    (o.fxn0, o.fxn1) = (fxn, fwn)
    o.stopped = true
    o.message = "issue with Steffensen step fwn"
    return

  var
    (fp, issue) = fbracket(xn, wn, fxn, fwn)

  if issue:
    o.stopped = true
    o.message = "issue with divided difference f[xn, wn]. "
    return

  let
    yn = xn - T(fxn / fp)
    fyn = fs.f(yn)
  incfn(o)

  (fp, issue) = fbracket(yn, xn, fyn, fxn)
  if issue:
    (o.xn0, o.xn1) = (xn, yn)
    (o.fxn0, o.fxn1) = (fxn, fyn)
    o.stopped = true
    o.message = "issue with divided difference f[xn, yn]. "
    return


  let
    phi = (S(1) + fyn / fwn)
    zn = yn - phi * T(fyn / fp)
    fzn = fs.f(zn)
  incfn(o)

  (fp, issue) = fbracketDiff(xn, yn, zn, fxn, fyn, fzn)
  if issue:
    (o.xn0, o.xn1) = (xn, zn)
    (o.fxn0, o.fxn1) = (fxn, fzn)
    o.stopped = true
    o.message = "issue with divided difference  f[y,z] - f[x,y] + f[x,z]. "
    return

  let
    w = 1 / (S(1) - fzn / fwn)
    xi = (S(1) - 2 * fyn * fyn * fyn / (fwn * fwn * fxn))
    xn1 = zn - w * xi * T(fzn / fp)
    fxn1 = fs.f(xn1)
  incfn(o)

  (o.xn0, o.xn1) = (xn, xn1)
  (o.fxn0, o.fxn1) = (fxn, fxn1)

  return

proc updateState*[T, S: SomeFloat](M: Thukral8|Order8, fs: proc(a: T): S, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  let
    xn = o.xn1
    fxn = o.fxn1
    
  when typeof(M) is Order8:
    let
      wn = steffStep(M, xn, fxn)
  else:
    let
      wn = steffStep(xn, fxn)
  let
    fwn = fs(wn)
  incfn(o)

  if isIssue(fwn):
    (o.xn0, o.xn1) = (xn, wn)
    (o.fxn0, o.fxn1) = (fxn, fwn)
    o.stopped = true
    o.message = "issue with Steffensen step fwn"
    return

  var
    (fp, issue) = fbracket(xn, wn, fxn, fwn)

  if issue:
    o.stopped = true
    o.message = "issue with divided difference f[xn, wn]. "
    return

  let
    yn = xn - T(fxn / fp)
    fyn = fs(yn)
  incfn(o)

  (fp, issue) = fbracket(yn, xn, fyn, fxn)
  if issue:
    (o.xn0, o.xn1) = (xn, yn)
    (o.fxn0, o.fxn1) = (fxn, fyn)
    o.stopped = true
    o.message = "issue with divided difference f[xn, yn]. "
    return


  let
    phi = (S(1) + fyn / fwn)
    zn = yn - phi * T(fyn / fp)
    fzn = fs(zn)
  incfn(o)

  (fp, issue) = fbracketDiff(xn, yn, zn, fxn, fyn, fzn)
  if issue:
    (o.xn0, o.xn1) = (xn, zn)
    (o.fxn0, o.fxn1) = (fxn, fzn)
    o.stopped = true
    o.message = "issue with divided difference  f[y,z] - f[x,y] + f[x,z]. "
    return

  let
    w = 1 / (S(1) - fzn / fwn)
    xi = (S(1) - 2 * fyn * fyn * fyn / (fwn * fwn * fxn))
    xn1 = zn - w * xi * T(fzn / fp)
    fxn1 = fs(xn1)
  incfn(o)

  (o.xn0, o.xn1) = (xn, xn1)
  (o.fxn0, o.fxn1) = (fxn, fxn1)

  return



# Order16

proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](M: Thukral16|Order16, fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  let
    xn = o.xn1
    fxn = o.fxn1

  when typeof(M) is Order16:
    let
      wn = steffStep(M, xn, fxn)
  else:
    let
      wn = steffStep(xn, fxn)
  let
    fwn = fs.f(wn)
  incfn(o)

  var
    (fp, issue) = fbracket(xn, wn, fxn, fwn)

  if issue:
    (o.xn0, o.xn1) = (xn, wn)
    (o.fxn0, o.fxn1) = (fxn, fwn)
    o.message = "isse with f[xn,wn]"
    o.stopped = true
    return

  let
    yn = xn - T(fxn / fp)
    fyn = fs.f(yn)
  incfn(o)

  (fp, issue) = fbracketRatio(yn, xn, wn, fyn, fxn, fwn)
  if issue:
    (o.xn0, o.xn1) = (xn, yn)
    (o.fxn0, o.fxn1) = (fxn, fyn)
    o.stopped = true
    o.message = "issue with f[xn,yn]*f[yn,wn]/f[xn,wn]"
    return

  let
    zn = yn - T(fyn / fp)
    fzn = fs.f(zn)
  incfn(o)

  (fp, issue) = fbracketDiff(yn, xn, zn, fyn, fxn, fzn)

  if issue:
    (o.xn0, o.xn1) = (xn, zn)
    (o.fxn0, o.fxn1) = (fxn, fzn)
    o.stopped = true
    o.message = "Approximate derivative failed"
    return

  let
    (u2, u3, u4) = (fzn / fwn, fyn / fxn, fyn / fwn)

    eta = 1 / (S(1) + S(2 * u3 * u4^2)) / (S(1) - u2)
    an = zn - T(eta * fzn / fp)
    fan = fs.f(an)
  incfn(o)

  (fp, issue) = fbracketRatio(an, yn, zn, fan, fyn, fzn)
  if issue:
    (o.xn0, o.xn1) = (xn, an)
    (o.fxn0, o.fxn1) = (fxn, fan)
    o.stopped = true
    o.message = "Approximate derivative failed"
    return

  let
    (u1, u5, u6) = (fzn / fxn, fan / fxn, fan / fwn)
  var
    fp1: typeof(fp)

  (fp1, issue) = fbracket(xn, yn, fxn, fyn)
  let
    sigma = 1.0 + u1 * u2 - u1 * u3 * u4^2 + u5 + u6 + u1^2 * u4 +
            u2^2 * u3 + 3 * u1 * u4^2 * (u3^2 - u4^2) / S(fp1)
    xn1 = an - T(sigma * fan / fp)
    fxn1 = fs.f(xn1)
  incfn(o)

  (o.xn0, o.xn1) = (xn, xn1)
  (o.fxn0, o.fxn1) = (fxn, fxn1)

  return

proc updateState*[T, S: SomeFloat](M: Thukral16|Order16, fs: proc(a: T): S, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T, S, S]) =
  let
    xn = o.xn1
    fxn = o.fxn1

  when typeof(M) is Order16:
    let
      wn = steffStep(M, xn, fxn)
  else:
    let
      wn = steffStep(xn, fxn)
  let
    fwn = fs(wn)
  incfn(o)

  var
    (fp, issue) = fbracket(xn, wn, fxn, fwn)

  if issue:
    (o.xn0, o.xn1) = (xn, wn)
    (o.fxn0, o.fxn1) = (fxn, fwn)
    o.message = "isse with f[xn,wn]"
    o.stopped = true
    return

  let
    yn = xn - T(fxn / fp)
    fyn = fs(yn)
  incfn(o)

  (fp, issue) = fbracketRatio(yn, xn, wn, fyn, fxn, fwn)
  if issue:
    (o.xn0, o.xn1) = (xn, yn)
    (o.fxn0, o.fxn1) = (fxn, fyn)
    o.stopped = true
    o.message = "issue with f[xn,yn]*f[yn,wn]/f[xn,wn]"
    return

  let
    zn = yn - T(fyn / fp)
    fzn = fs(zn)
  incfn(o)

  (fp, issue) = fbracketDiff(yn, xn, zn, fyn, fxn, fzn)

  if issue:
    (o.xn0, o.xn1) = (xn, zn)
    (o.fxn0, o.fxn1) = (fxn, fzn)
    o.stopped = true
    o.message = "Approximate derivative failed"
    return

  let
    (u2, u3, u4) = (fzn / fwn, fyn / fxn, fyn / fwn)

    eta = 1 / (S(1) + S(2 * u3 * u4^2)) / (S(1) - u2)
    an = zn - T(eta * fzn / fp)
    fan = fs(an)
  incfn(o)

  (fp, issue) = fbracketRatio(an, yn, zn, fan, fyn, fzn)
  if issue:
    (o.xn0, o.xn1) = (xn, an)
    (o.fxn0, o.fxn1) = (fxn, fan)
    o.stopped = true
    o.message = "Approximate derivative failed"
    return

  let
    (u1, u5, u6) = (fzn / fxn, fan / fxn, fan / fwn)
  var
    fp1: typeof(fp)

  (fp1, issue) = fbracket(xn, yn, fxn, fyn)
  let
    sigma = 1.0 + u1 * u2 - u1 * u3 * u4^2 + u5 + u6 + u1^2 * u4 +
            u2^2 * u3 + 3 * u1 * u4^2 * (u3^2 - u4^2) / S(fp1)
    xn1 = an - T(sigma * fan / fp)
    fxn1 = fs(xn1)
  incfn(o)

  (o.xn0, o.xn1) = (xn, xn1)
  (o.fxn0, o.fxn1) = (fxn, fxn1)

  return


##################################################
# some means of guarding against large fx when taking a secant step
# TODO: rework this
proc steffStep*[T, S: SomeFloat](M: Order5|Order8|Order16, x: T, fx: S): T =
  let
    (xbar, fxbar) = (x, fx)
  when sizeof(T) == 8:
    let
      h1 = nextafter(1.0, 2.0) - 1.0
      h2 = 1.0 - nextafter(1.0, 0.0)
      # thresh = max(1.0, abs(xbar)) * sqrt(nextafter(1.0, Inf))
      thresh = max(1.0, abs(xbar)) * sqrt(max(h1, h2))
  else:
    let
      h1 = nextafterf(1.0, 2.0) - 1.0
      h2 = 1.0 - nextafterf(1.0, 0.0)
      # thresh = max(1.0, abs(xbar)) * sqrt(nextafterf(1.0, Inf))
      thresh = max(1.0, abs(xbar)) * sqrt(max(h1, h2))

  if abs(fxbar) <= thresh:
    return x + T(fxbar)
  else:
    return x + T(sgn(fx)) * thresh
