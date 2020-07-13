import math
import findZero

proc initState*[T, S: SomeFloat, CF: CallableFunction[T, S]](
  M: AbstractNewtonLikeMethod, fs: CF, x: T): UnivariateZeroState[T, S] =
  let
    x1 = float(x)
    tmp = fDeltaX(fs, x)
    (fx1, delta) = (tmp[0], tmp[1])

    fnevals = 1

  new(result)
  result.xn1 = x1
  result.xn0 = T(0)
  result.xstar = T(0)
  result.m = @[delta]
  result.fxn1 = fx1
  result.fxn0 = S(0)
  result.fxstar = S(0)
  result.fm = @[]
  result.steps = 0
  result.fnevals = fnevals
  result.stopped = false
  result.xConverged = false
  result.fConverged = false
  result.convergenceFailed = false
  result.message = ""

proc initState2*[T, S: SomeFloat, CF: CallableFunction[T, S]](
    state: UnivariateZeroState[T, S], M: Newton, fs: CF, x: T) =
  let
    x1 = x
    tmp = fDeltaX(fs, x)
    (fx1, delta) = (tmp[0], tmp[1])
  var
    ns = newSeq[S](0)

  initState2(state, x1, T(0), @[delta], fx1, S(0), ns)

proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](M: Newton,
    fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T,
        S, S]) =
  let
    xn = o.xn1
    fxn = o.fxn1
  var
    r1 = o.m[0]
    fxn1: S

  if classify(r1) == fcNan or classify(r1) == fcInf or classify(r1) ==
      fcNegInf or classify(r1) == fcZero or classify(r1) == fcNegZero:
    o.stopped = true
    return

  let
    xn1 = xn - r1

    tmp = fDeltaX(fs, xn1)
  (fxn1, r1) = (tmp[0], tmp[1])
  incfn(o, 2)

  (o.xn0, o.xn1) = (xn, xn1)
  (o.fxn0, o.fxn1) = (fxn, fxn1)
  o.m = @[r1]

  return

proc newton2*[T, S: SomeFloat](f, fp: proc(f1: T): S, x0: T|(T, T),
    kwargs: varargs[UnivariateZeroOptions[T, T, S, S]]): T =
  return findZero(callableFunctions((f, fp)), x0, Newton(), kwargs = kwargs)


# Halley

proc initState*[T, S: SomeFloat, CF: CallableFunction[T, S]](
  methods: AbstractHalleyLikeMethod, fs: CF, x: T): UnivariateZeroState[T, S] =
  let
    x1 = x
    tmp = fDDeltaX(fs, x1)
    (fx1, delta, ddelta) = (tmp[0], tmp[1], tmp[2])
    fnevals = 3

  new(result)
  result.xn1 = x1
  result.xn0 = T(0)
  result.xstar = T(0)
  result.m = @[delta, ddelta]
  result.fxn1 = fx1
  result.fxn0 = S(0)
  result.fxstar = S(0)
  result.fm = @[]
  result.steps = 0
  result.fnevals = fnevals
  result.stopped = false
  result.xConverged = false
  result.fConverged = false
  result.convergenceFailed = false
  result.message = ""

proc initState2*[T, S: SomeFloat, CF: CallableFunction[T, S]](
  state: UnivariateZeroState[T, S], M: AbstractHalleyLikeMethod, fs: CF, x: T) =
  let
    x1 = x
    tmp = fDDeltaX(fs, x)
    (fx1, delta, ddelta) = (tmp[0], tmp[1], tmp[2])

  initState2(state, x1, T(0), @[delta, ddelta], fx1, S(0), newSeq(seq[S], 0))

proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](methods: Halley,
    fs: CF, o: UnivariateZeroState[T, S], options: UnivariateZeroOptions[T, T,
        S, S]) =
  let
    xn = o.xn1
    fxn = o.fxn1
  var
    (r1, r2) = (o.m[0], o.m[1])
  let
    xn1 = xn - 2 * r2 / (2 * r2 - r1) * r1

    tmp = fDDeltaX(fs, xn1)
    fxn1 = tmp[0]

  (r1, r2) = (tmp[1], tmp[2])
  incfn(o, 3)

  (o.xn0, o.xn1) = (xn, xn1)
  (o.fxn0, o.fxn1) = (fxn, fxn1)
  o.m = @[r1, r2]

  return

proc halley*[T, S: SomeFloat](f, fp, fpp: proc(f1: T): S, x0: T|(T, T),
    kwargs: varargs[UnivariateZeroOptions[T, T, S, S]]): T =
  return findZero(callableFunctions((f, fp, fpp)), x0, Halley(),
      kwargs = kwargs)

# Schroder

proc updateState*[T, S: SomeFloat, CF: CallableFunction[T, S]](
  methods: Schroder, fs: CF, o: UnivariateZeroState[T, S],
    options: UnivariateZeroOptions[T, T, S, S]) =
  let
    xn = o.xn1
    fxn = o.fxn1
  var
    (r1, r2) = (o.m[0], o.m[1])

  let
    delta = r2 / (r2 - r1) * r1

  if classify(delta) == fcNan or classify(delta) == fcInf or classify(delta) ==
      fcNegInf or classify(delta) == fcZero or classify(delta) == fcNegZero:
    o.stopped = true
    return

  let
    xn1 = xn - delta

    tmp = fDDeltaX(fs, xn1)
    fxn1 = tmp[0]

  (r1, r2) = (tmp[1], tmp[2])
  incfn(o, 3)

  (o.xn0, o.xn1) = (xn, xn1)
  (o.fxn0, o.fxn1) = (fxn, fxn1)
  (o.m[0], o.m[1]) = (r1, r2)

  return
