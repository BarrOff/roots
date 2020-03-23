import math

# imports from C
proc nextafterf*(a, b: cfloat): cfloat {.header: "<math.h>", importc: "nextafterf".}
proc nextafter*(a, b: cdouble): cdouble {.header: "<math.h>", importc: "nextafter".}

type
  # type to throw on succesful convergence
  StateConverged* = ref object of RootObj
    x0*: SomeNumber

  # type to throw on failure
  ConvergenceFailed* = ref object of RootObj
    reason*: string

# Helpers for the various methods

# issue with approx derivative
proc isIssue*[T: SomeInteger](x: T): bool =
  return abs(x) == T(0)

proc isIssue*[T: SomeFloat](x: T): bool =
  let
    xt = classify(x)

  case xt
  of fcNormal: return false
  else: return true

# of (a,fa), (b,fb) choose pair where |f| is smallest
proc chooseSmallest*[T: SomeNumber](a, b, fa, fb: T): (T, T) {.inline.} =
  if abs(fa) < abs(fb):
    return (a, fa)

  return (b, fb)

proc sortSmallest*[T](a, b, fa, fb: T): (T, T, T, T) {.inline.} =
  if abs(fa) < abs(fb):
    return (a, b, fa, fb)

  return (b, a, fb, fa)


proc defaultSecantStep*(x1: float): float =

  let
    h1 = nextafter(1.0, Inf) - 1.0
    h2 = 1.0 - nextafter(1.0, 0.0)
    h = pow(max(h1, h2), 1/3)
    dx = h + abs(x1) * h * h
    x0 = x1 + dx

  return x0

proc defaultSecantStep*(x1: float32): float32 =

  let
    h1 = nextafterf(1.0, Inf) - 1.0
    h2 = 1.0 - nextafterf(1.0, 0.0)
    h = pow(max(h1, h2), 1/3)
    dx = h + abs(x1) * h * h
    x0 = x1 + dx

  return x0

proc steffStep*[T: SomeFloat](x: T, fx: SomeFloat): T =           # NO M: Any!
  return x + T(fx)

proc guardedSecantStep*[T: SomeFloat](a, b, fa, fb: T): (T, bool) =
  let
    fp = (fb - fa) / (b - a)

  var
    delta = fb / fp

  if isIssue(delta):
    delta = T(a) / 1000.0
  elif abs(delta) >= 100.0 * abs(a - b):
    delta = T(sgn(delta)) * 100.0 * min(a, abs(a - b))

  if isIssue(delta):
    return (a + (b - a) * 0.5, true)

  return (b - delta, false)

proc quadVertex*[T, S: SomeFloat](c: T, fc: S, b: T, fb: S, a: T, fa: S): T =
  let
    fba = (fb - fa) / (b - a)
    fbc = (fb - fc) / (b - c)

  return 0.5 * ((a + b) - fba / (fbc - fba) * (c - a))

proc fbracket*[T: SomeFloat](a, b, fa, fb: T): (T, bool) =
  let
    num = fb - fa
    den = b - a
    cnum = classify(num)
    cden = classify(den)

  if cnum == fcZero or cnum == fcNegZero or cden == fcZero or cden == fcNegZero:
    return (Inf, true)

  return (num / den, isIssue(num / den))

proc fbracketDiff*[T: SomeFloat](a, b, c, fa, fb, fc: T): (T, bool) =
  var
    (x1, issue) = fbracket(b, c, fb, fc)

  if issue:
    return (x1, issue)

  var
    x2: typeof(x1)

  (x2, issue) = fbracket(a, b, fa, fb)

  if issue:
    return (x2, issue)

  var
    x3: typeof(x1)

  (x3, issue) = fbracket(a, c, fa, fc)

  if issue:
    return (x3, issue)

  let
    outer = x1 - x2 + x3

  return (outer, isIssue(outer))

proc fbracketRatio*[T: SomeFloat](a, b, c, fa, fb, fc: T): (T, bool) =
  ## use f[a,b] * f[a,c] / f[b,c]
  let
    (x1, _) = fbracket(a, b, fa, fb)
    (x2, _) = fbracket(a, c, fa, fc)
    (x3, _) = fbracket(b, c, fb, fc)
    outer = (x1 * x2) / x3

  return (outer, isIssue(outer))

proc identifyStartingPoint*[T: SomeFloat](f: proc (x: T): T, a, b: T, N: SomeInteger): T =
  let
    stepSize = (abs(a) - abs(b)) / N
  var
    # pts: seq[T]
    # fxs: seq[T]
    sfxs = @[sgn(f(a))]

  for i in 1..N:
    sfxs.add(sgn(f(a + i * stepSize)))

  return identifyStartingPoint(a, b, sfxs)

proc identifyStartingPoint*[T: SomeFloat](a, b: T, sfxs: seq[int]): T =
  let
    N = len(sfxs) - 1
    p0 = a + (b - a) / 2
    p1 = p0 + (b - a) / (2 * N) * sfxs[0] * sum(sfxs[1:N - 1])

  return p1
