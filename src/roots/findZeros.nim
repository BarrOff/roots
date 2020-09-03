## =========
## findZeros
## =========
##
##Attempt to find all zeros in an interval (a,b)
##
## Algorithm
## =========
##
## The basic algorithm checks for zeros among the endpoints, and then
## divides the interval `(a,b)` into `no_pts-1` subintervals and then
## proceeds to look for zeros through bisection or a derivative-free
## method.  As checking for a bracketing interval is relatively cheap and
## bisection is guaranteed to converge, each interval has `k` pairs of
## intermediate points checked for a bracket.
##
## If any zeros are found, the algorithm uses these to partition `(a,b)`
## into subintervals. Each subinterval is shrunk so that the endpoints
## are not zeros and the process is repeated on the subinterval. If the
## initial interval is too large, then the naive scanning for zeros may
## be fruitless and no zeros will be reported. If there are nearby zeros,
## the shrinking of the interval may jump over them, though as seen in
## the examples, nearby roots can be identified correctly, though for
## really nearby points, or very flat functions, it may help to increase
## `no_pts`.
##
## The tolerances are used to shrink the intervals, but not to find zeros
## within a search. For searches, bisection is guaranteed to converge
## with no specified tolerance. For the derivative free search, a
## modification of the `Order0` method is used, which at worst case
## compares `|f(x)| <= 8*eps(x)` to identify a zero. The algorithm might
## identify more than one value for a zero, due to floating point
## approximations. If a potential pair of zeros satisfy
## `isapprox(a,b,atol=sqrt(xatol), rtol=sqrt(xrtol))` then they are
## consolidated.
##
## The algorithm can make many function calls. When zeros are found in an
## interval, the naive search is carried out on each subinterval. To cut
## down on function calls, though with some increased chance of missing
## some zeros, the adaptive nature can be skipped with the argument
## `naive=true` or the number of points stepped down.
##
## The algorithm is derived from one in a
## `PR [https://github.com/JuliaMath/Roots.jl/pull/113]`_ by @djsegal.
##
## Note
## ====
##
## There are two cases where the number of zeros may be underreported:
## * if the initial interval, [a,b], is too wide
## * if there are zeros  that are very nearby

import algorithm, math, sequtils, sugar
import private/utils, simple

type
  Interval[T: SomeFloat] = object
    ## the algorithm first scans for zeros using the naive approach, then
    ## splits (a,b) by these zeros. This struct holds the subintervals
    a: T
    b: T
    depth: int

proc fz2[T, S: SomeFloat](zs: var seq[S], f: proc(x: T): S, a, b: T,
    no_pts: int, k: int = 4)

proc fz[T, S: SomeFloat](f: proc(x: T): S, a, b: T, no_pts: int,
    k: int = 4): seq[S] =
  ## A naive approach to find zeros: split (a,b) by n points, look into each for a
  ## zero
  ## * k is oversampling rate for bisection. (It is relatively cheap to check
  ##   for a bracket so we oversample our intervals looking for brackets
  ## * assumes f(a) *not* a zero
  var
    zs: seq[S]
  fz2(zs, f, a, b, no_pts, k)
  return zs

proc fz2[T, S: SomeFloat](zs: var seq[S], f: proc(x: T): S, a, b: T,
    no_pts: int, k: int = 4) =
  let
    n = (no_pts - 1) * k + 1
    l = (b - a) / T(n)
  var
    pts = newSeq[S](n)
    fs = newSeq[S](n)
    sfs = newSeq[int](n)

  pts[0] = a
  pts[high(pts)] = b
  fs[0] = f(pts[0])
  fs[high(fs)] = f(pts[high(pts)])
  sfs[0] = sgn(fs[0])
  sfs[high(sfs)] = sgn(fs[high(fs)])
  for i in 1..<high(pts):
    pts[i] = pts[i - 1] + l
    fs[i] = f(pts[i])
    sfs[i] = sgn(fs[i])

  var
    u = pts[0]
    foundBisectionZero = false

  for i, x in pts:
    let
      q = i div k
      r = i mod k
    var
      p1, rt: T

    if i > 0 and r == 0:
      var
        v = x
      if not(foundBisectionZero):
        try:
          p1 = identifyStartingPoint(u, v, sfs[(i - k)..i])
          rt = dfree(f, p1)
          if not(classify(rt) == fcNan) and (u < rt) and (rt <= v):
            zs.add(rt)
        except:
          discard

      u = v
      foundBisectionZero = false

    if i < n - 1:
      if (classify(fs[i + 1]) == fcNegZero) or (classify(fs[i + 1]) == fcZero):
        foundBisectionZero = true # kinda
        zs.add(pts[i + 1])
      elif sfs[i] * sfs[i + 1] < 0:
        foundBisectionZero = true
        rt = bisection(f, x, pts[i + 1])
        zs.add(rt)

    sort(zs)

proc nonZero[T, S: SomeFloat](fa: S, a: T, atol, rtol: S): bool =
  ## check if f(a) is non zero using tolerances max(atol, eps()), rtol
  when sizeof(T) == 8:
    abs(fa) >= max(atol, max(abs(a) * rtol, (nextafter(1.0, 2.0) - 1.0)))
  else:
    abs(fa) >= max(atol, max(abs(a) * rtol, (nextafterf(1.0, 2.0) - 1.0)))

proc findNonZero[T, S: SomeFloat](f: proc(x: T): S, a, barrier, xatol, xrtol: T,
                                      atol, rtol: S): T =
  ## After splitting by zeros we have intervals (zm, zn) this is used to shrink
  ## to (zm+, zn-) where both are non-zeros, as defined above
  when sizeof(T) == 8:
    let
      xtol = max(xatol, max(abs(a) * xrtol, (nextafter(1.0, 2.0) - 1.0)))
  else:
    let
      xtol = max(xatol, max(abs(a) * xrtol, (nextafterf(1.0, 2.0) - 1.0)))

  var
    sign: int
    ctr = 0
  if barrier > a:
    sign = 1
  else:
    sign = -1

  var
    x = a + T(2^ctr * sign) * xtol

  while not(nonZero(f(x), x, atol, rtol)):
    ctr += 1
    x += T(2^ctr * sign) * xtol

    if (sign > 0 and x > barrier) or (sign < 0 and x < barrier):
      return T(0.0 / 0.0)

    if ctr > 100:
      return T(0.0 / 0.0)

  return x

proc makeIntervals[T, S: SomeFloat](ints: var seq[Interval[T]], f: proc(
    x: T): S, a, b: T, zs: seq[T], depth: int, xatol, xrtol: T, atol, rtol: S) =
  ## split a < z1 < z2 < ... < zn < b into intervals (a+,z1-), (z1+, z2-), ...
  ## where possible; push! onto ints
  var
    pts = newSeq[T](2 + zs.len)

  pts[0] = a
  pts[high(pts)] = b
  for index, value in zs:
    pts[index + 1] = value

  for (u, v) in zip(pts[0..pts.high-1], pts[1..pts.high]):
    let
      ur = findNonZero(f, u, v, xatol, xrtol, atol, rtol)
    if classify(ur) == fcNan:
      continue

    let
      vl = findNonZero(f, v, u, xatol, xrtol, atol, rtol)
    if classify(vl) == fcNan:
      continue

    ints.add(Interval[T](a: ur, b: vl, depth: depth))

proc approxClose[T: SomeFloat](z1, z2, xatol, xrtol: T): bool =
  ## adjust what we mean by x1 ~ x2 for purposes of adding a new zero
  let
    tol = max(sqrt(xatol), max(abs(z1), abs(z2)) * sqrt(xrtol))
  return abs(z1 - z2) < tol

proc notNear[T: SomeFloat](proposed: T, xs: seq[T], xatol, xrtol: T): bool =
  ## is proposed not near xs? (false and we add proposed)
  let
    n = xs.len
  if n <= 1:
    return true

  var
    ind = n + 1

  for i, rt in xs:
    if proposed < rt:
      ind = i
      break

  if ind > 0: # xs[ind-1] <= propose < xs[ind]
    let
      rt = xs[ind-1]
    if approxClose(proposed, rt, xatol, xrtol):
      return false

  if ind < n: # value to right
    let
      rt = xs[ind]
    if approxClose(proposed, rt, xatol, xrtol):
      return false

  return true

proc findZeros*[T, S: SomeFloat](f: proc(x: T): S, a, b: T, noPts: int = 12,
    k: int = 8, naive: bool = false, xatol: T = pow(eps(a), 0.8),
        xrtol: T = eps(a), atol: S = eps(float(1.0)), rtol: S = eps(float(
            1.0))): seq[T] =
  ## Search for zeros of `f` in the interval `[a,b]`.
  ##
  ## Arguments:
  ##
  ## * noPts: creates noPts - 1 subintervals in the interval `[a,b]`
  ## * k: number of pairs of intermediate points checked for a bracket
  ## * naive: naive or an adaptive search
  var
    (a0, b0) = (float(a), float(b))
  if classify(a0) == fcNegInf:
    a0 = nextafter(a0, 0)
  if classify(b0) == fcInf:
    b0 = nextafter(b0, 0)

  # set tolerances if not specified
  let
    (fa0, fb0) = (f(a0), f(b0))

  var
    zs: seq[T] # collect zeros

  if abs(fa0) <= 8 * eps(a0):
    zs.add(a0)
  if abs(fb0) <= 8 * eps(b0):
    zs.add(b0)
  a0 = findNonZero(f, a0, b0, xatol, xrtol, atol, rtol)
  b0 = findNonZero(f, b0, a0, xatol, xrtol, atol, rtol)

  fz2(zs, f, a0, b0, noPts, k) # initial zeros

  var
    ints: seq[Interval[T]]

  if not(naive) and zs.len != 0:
    makeIntervals(ints, f, a0, b0, zs, 1, xatol, xrtol, atol, rtol)

  var
    nzs: seq[T]
    cnt = 0

  if not(naive):
    while ints.len > 0:
      cnt += 1
      let
        currentInterval = ints[high(ints)]
        subNoPts = noPts div 2^currentInterval.depth
      ints = ints[0..high(ints) - 1]

      nzs = @[]
      if subNoPts >= 2:
        fz2(nzs, f, currentInterval.a, currentInterval.b, subNoPts, k)

      if nzs.len != 0:
        let
          azs = nzs.filter(x => notNear(x, zs, xatol, xrtol))
        if azs.len == 0:
          continue
        zs = concat(zs, azs)
        sort(zs)
        if currentInterval.depth > 4:
          continue
        makeIntervals(ints, f, currentInterval.a, currentInterval.b, azs,
            currentInterval.depth + 1, xatol, xrtol, atol, rtol)

  if zs.len <= 1:
    return zs
  sort(zs)

  var
    inds = @[0]
    z1 = zs[0]
  for i in 1..high(zs):
    var
      z2 = zs[i]
    if not(approxClose(z1, z2, xatol, xrtol)):
      inds.add(i)
    z1 = z2

  var
    result = newSeq[T](inds.len)

  for index, value in inds:
    result[index] = zs[value]

  return result
