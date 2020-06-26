import math
import private/utils, findZero

proc initState*[T, S: SomeFloat](M: AbstractNewtonLikeMethod, fs: proc(
    f1: T): S, x: T): UnivariateZeroState[T, S] =
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

proc initState2*[T, S: SomeFloat](state: UnivariateZeroState[T, S], M: Newton,
    fs: proc(f1: T): S, x: T) =
  let
    x1 = x
    tmp = fDeltaX(fs, x)
    (fx1, delta) = (tmp[0], tmp[1])
  var
    ns = newSeq[S](0)

  initState2(state, x1, T(0), @[delta], fx1, S(0), ns)

proc updateState*[T, S: SomeFloat](M: Newton, fs: proc(f1: T): S,
    o: UnivariateZeroState[T, S]) =
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

proc newton*[T, S: SomeFloat](f, fp: proc(f1: T): S, x0: T, kwargs: varargs[
    UnivariateZeroOptions[T, T, S, S]]): T =
  return findZero((f, fp), x0, Newton(), kwargs)


# Halley
