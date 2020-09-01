## ======
## newton
## ======
##
## Classical derivative-based, iterative, root-finding algorithms
##
## If `ri = f^(i-1)/f^(i)`, then these have an update step `xn - delta` where:
##
## * Newton: `delta = r1`  # order 2 if simple root (multiplicity 1)
## * Halley: `delta = 2*r2/(2r2 - r1) * r1` # order 3 if simple root
## * Schroder: `delta = r2  / (r2 - r1) * r1`  # order 2
## * Thukral(3): `delta =  (-2*r3)*(r2 - r1)/(r1^2 - 3*r1*r3 + 2*r2*r3) * r1` # order 3
## * Thukral(4): `delta =  3*r1*r2*r4*(r1^2 - 3*r1*r3 + 2*r2*r3)/(-r1^3*r2 + 4*r1^2*r2*r4 + 3*r1^2*r3*r4 - 12*r1*r2*r3*r4 + 6*r2^2*r3*r4)` # order 4
##
## The latter two come from
## `Thukral <http://article.sapub.org/10.5923.j.ajcam.20170702.05.html>`_.
## They are not implemented.


import math
import findZero

## Newton
## ------
## Implements `Newton's method <http://tinyurl.com/b4d7vls>`_:
## `xᵢ₊₁ =  xᵢ - f(xᵢ)/f'(xᵢ)`. This is a quadratically convergent method
## requiring one derivative. Two function calls per step.
##
## Example
## ```nim
## findZero((sin,cos), 3.0, Newton())
## ```
##
## If function evaluations are expensive one can pass in a function which
## returns `(f, f/f')` as follows
##
## ```nim
## findZero(x -> (sin(x), sin(x)/cos(x)), 3.0, Newton())
## ```
##
## This can be advantageous if the derivative is easily computed from the
## value of f, but otherwise would be expensive to compute.
##
## The error, `eᵢ = xᵢ - α`, can be expressed as `eᵢ₊₁ = f[xᵢ,xᵢ,α]/(2f[xᵢ,xᵢ])eᵢ²`
## (Sidi, Unified treatment of regula falsi, Newton-Raphson, secant, and
## Steffensen methods for nonlinear equations).

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
  ## Implementation of Newton's method: `x_n1 = x_n - f(x_n)/ f'(x_n)`
  ## 
  ## Arguments:
  ## 
  ## * `f::Function` -- function to find zero of
  ## 
  ## * `fp::Function` -- the derivative of `f`.
  ## 
  ## * `x0::Number` -- initial guess.
  return findZero(callableFunctions((f, fp)), x0, Newton(), kwargs = kwargs)


## Halley
## ------
## Implements `Halley's method <http://tinyurl.com/yd83eytb>`_,
## `xᵢ₊₁ = xᵢ - (f/f')(xᵢ) * (1 - (f/f')(xᵢ) * (f''/f')(xᵢ) * 1/2)^(-1)`
## This method is cubically converging, but requires more function calls per
## step (3) than other methods.
##
## Example
## ```nim
## find_zero((sin, cos, x=>-sin(x)), 3.0, Halley())
## ```
##
## If function evaluations are expensive one can pass in a function which
## returns `(f, f/f',f'/f'')` as follows
##
## ```nim
## find_zero(x => (sin(x), sin(x)/cos(x), -cos(x)/sin(x)), 3.0, Halley())
## ```
##
## This can be advantageous if the derivatives are easily computed from
## the value of `f`, but otherwise would be expensive to compute.
##
## The error, `eᵢ = xᵢ - α`, satisfies
## `eᵢ₊₁ ≈ -(2f'⋅f''' -3⋅(f'')²)/(12⋅(f'')²) ⋅ eᵢ³` (all evaluated at `α`).

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
  ## Implementation of Halley's method.
  ##
  ## Arguments:
  ##
  ## * `f::Function` -- function to find zero of
  ##
  ## * `fp::Function` -- derivative of `f`.
  ##
  ## * `fpp:Function` -- second derivative of `f`.
  ##
  ## * `x0::Number` -- initial guess
  return findZero(callableFunctions((f, fp, fpp)), x0, Halley(),
      kwargs = kwargs)

## Schröder
## ========
##
## Schröder's method, like Halley's method, utilizes `f`, `f'`, and
## `f''`. Unlike Halley it is quadratically converging, but this is
## independent of the multiplicity of the zero (cf. Schröder, E. "Über
## unendlich viele Algorithmen zur Auflösung der Gleichungen."
## Math. Ann. 2, 317-365, 1870;
## `mathworld <http://mathworld.wolfram.com/SchroedersMethod.html>`_).
## Schröder's method applies Newton's method to `f/f'`, a function with all
## simple zeros.
##
##
## Example
## ```nim
## let
##   m = 2
##   fx = x => (cos(x)-x)^m
##   fpx = x => (-x + cos(x))*(-2*sin(x) - 2)
##   fppx = x => 2*((x - cos(x))*cos(x) + (sin(x) + 1)^2)
## findZero((f, fp, fpp), PI/4, Halley())    # 14 steps
## findZero((f, fp, fpp), 1.0, Schroder())    # 3 steps
## ```
##
## (Whereas, when `m=1`, Halley is 2 steps to Schröder's 3.)
##
## If function evaluations are expensive one can pass in a function which
## returns `(f, f/f',f'/f'')` as follows
##
## ```nim
## findZero(x => (sin(x), sin(x)/cos(x), -cos(x)/sin(x)), 3.0, Schroder())
## ```
##
## This can be advantageous if the derivatives are easily computed from
## the value of `f`, but otherwise would be expensive to compute.
##
## The error, `eᵢ = xᵢ - α`, is the same as `Newton` with `f` replaced by `f/f'`.

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
