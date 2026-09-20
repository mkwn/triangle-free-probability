/-!
# The purely computational kernel layer

This module holds every *computable* definition used by the certified
numerics: the dyadic interval arithmetic, the logarithm ladders, the endpoint
and side records, the spatial leaf evaluators, the subdivision trees and the
Boolean checkers.

It deliberately imports **nothing** — in particular no `Mathlib`.  All the
soundness theorems (which do speak about real numbers, and therefore do need
`Mathlib`) live in the files that import this one: `Interval.lean`,
`LogInterval.lean`, `SpatialEval.lean`, `CoverTree.lean`, `ParamEval.lean`,
`CubicCover.lean` and `TailCover.lean`.

Keeping the data layer free of `Mathlib` matters for build cost: the ~50
generated modules that replay the certified covers contain nothing but data
and `decide +kernel` checks, so they no longer have to load the whole library.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Itv

/-! ### Fixed-point dyadic intervals -/

/-- The fixed-point scale `2^128`. -/
def scale : Int := 2 ^ 128

/-- Rounding down: `⌊n/d⌋` for `d > 0`. -/
def rdown (n d : Int) : Int := n / d

/-- Rounding up: `⌈n/d⌉` for `d > 0`. -/
def rup (n d : Int) : Int := -((-n) / d)

/-- A dyadic interval: `lo/2^128 ≤ x ≤ hi/2^128`. -/
structure DI where
  lo : Int
  hi : Int
deriving DecidableEq, Repr

def add (i j : DI) : DI := ⟨i.lo + j.lo, i.hi + j.hi⟩
def neg (i : DI) : DI := ⟨-i.hi, -i.lo⟩
def sub (i j : DI) : DI := add i (neg j)

/-! ### Point intervals and small constants -/

/-- The one-point interval of a scaled integer. -/
def pt (a : Int) : DI := ⟨a, a⟩

/-- The exact interval `[1,1]`. -/
def oneI : DI := pt scale

/-- The exact interval `[2,2]`. -/
def twoI : DI := pt (2 * scale)

/-- The exact interval `[3,3]`. -/
def threeI : DI := pt (3 * scale)

/-- The exact interval of an integer. -/
def intI (n : Int) : DI := pt (n * scale)

/-! ### Multiplication

The naive enclosure of a product forms all four endpoint products and takes
their minimum and maximum.  On an *ordered* interval (`lo ≤ hi`, which every
enclosure of a real number satisfies) the signs of the endpoints already
determine which two of the four products are extremal, by monotonicity of
`x ↦ x * c` in each argument.  `mul` therefore tests the signs first and
computes only the two products it needs, falling back on the four-product
form `mulGen` in the single case where both intervals straddle zero.  This is
the same value (`Interval.mul_eq_mulGen`), at roughly half the kernel cost;
since every replayed certificate multiplies interval by interval thousands of
times, it is the dominant saving in the kernel replay. -/

/-- The four-product interval multiplication. -/
def mulGen (i j : DI) : DI :=
  ⟨rdown (min (min (i.lo * j.lo) (i.lo * j.hi)) (min (i.hi * j.lo) (i.hi * j.hi))) scale,
    rup (max (max (i.lo * j.lo) (i.lo * j.hi)) (max (i.hi * j.lo) (i.hi * j.hi))) scale⟩

/-- Interval multiplication, with the extremal pair of endpoint products
selected from the signs of the endpoints.  The ordering test in front makes
the fast form agree with `mulGen` on *every* input, not only on the ordered
intervals it is used on (`Interval.mul_eq_mulGen`). -/
def mul (i j : DI) : DI :=
  if ¬ (i.lo ≤ i.hi ∧ j.lo ≤ j.hi) then mulGen i j
  else if 0 ≤ i.lo then
    (if 0 ≤ j.lo then ⟨rdown (i.lo * j.lo) scale, rup (i.hi * j.hi) scale⟩
     else if j.hi ≤ 0 then ⟨rdown (i.hi * j.lo) scale, rup (i.lo * j.hi) scale⟩
     else ⟨rdown (i.hi * j.lo) scale, rup (i.hi * j.hi) scale⟩)
  else if i.hi ≤ 0 then
    (if 0 ≤ j.lo then ⟨rdown (i.lo * j.hi) scale, rup (i.hi * j.lo) scale⟩
     else if j.hi ≤ 0 then ⟨rdown (i.hi * j.hi) scale, rup (i.lo * j.lo) scale⟩
     else ⟨rdown (i.lo * j.hi) scale, rup (i.lo * j.lo) scale⟩)
  else
    (if 0 ≤ j.lo then ⟨rdown (i.lo * j.hi) scale, rup (i.hi * j.hi) scale⟩
     else if j.hi ≤ 0 then ⟨rdown (i.hi * j.lo) scale, rup (i.lo * j.lo) scale⟩
     else mulGen i j)

/-- Powers.  The exponents `0` and `1` are given directly, so that a square
costs one multiplication instead of two. -/
def pow (i : DI) : Nat → DI
  | 0 => oneI
  | 1 => i
  | (n + 1) => mul i (pow i n)

/-- Inverse of a strictly positive interval. -/
def inv (i : DI) : DI := ⟨rdown (scale * scale) i.hi, rup (scale * scale) i.lo⟩

/-- Division by a strictly positive interval. -/
def div (i j : DI) : DI := mul i (inv j)

/-! ### The logarithm ladders -/

/-- `L(y) = 2(y-1)/(y+1)` evaluated at the dyadic number `value a`. -/
def seedLowerI (a : Int) : DI := div (pt (2 * (a - scale))) (pt (a + scale))

/-- `U(y) = (y - 1/y)/2` evaluated at the dyadic number `value a`. -/
def seedUpperI (a : Int) : DI := div (sub (pt a) (div oneI (pt a))) twoI

/-- The last entry of a nonempty ladder given as head and tail. -/
def lastOf (a : Int) : List Int → Int
  | [] => a
  | b :: rest => lastOf b rest

/-- The lower-ladder condition: every entry is `≥ 1` and each entry squared is
at most its predecessor. -/
def lowerOk (a : Int) : List Int → Bool
  | [] => decide (scale ≤ a)
  | b :: rest => decide (scale ≤ a) && decide (b * b ≤ a * scale) && lowerOk b rest

/-- The upper-ladder condition. -/
def upperOk (a : Int) : List Int → Bool
  | [] => decide (scale ≤ a)
  | b :: rest => decide (scale ≤ a) && decide (a * scale ≤ b * b) && upperOk b rest

/-- The dyadic constant `2^n`. -/
def pow2I (n : Nat) : DI := pt (scale * 2 ^ n)

/-- Lower dyadic bound for `log (value a)` from a lower ladder. -/
def logLowerI (a : Int) (l : List Int) : DI :=
  mul (pow2I l.length) (seedLowerI (lastOf a l))

/-- Upper dyadic bound for `log (value a)` from an upper ladder. -/
def logUpperI (a : Int) (l : List Int) : DI :=
  mul (pow2I l.length) (seedUpperI (lastOf a l))

/-- Certificate for `exp x ∈ [lo, hi]` with `0 < lo, hi < 1`. -/
structure ExpCert where
  lo : Int
  hi : Int
  u : Int
  ul : List Int
  v : Int
  vl : List Int

/-- The Boolean condition the kernel checks for an exponential certificate on
the argument interval `[value xlo, value xhi]`. -/
def expOk (c : ExpCert) (xlo xhi : Int) : Bool :=
  decide (0 < c.lo) && decide (0 < c.hi) &&
    decide (c.u * c.lo ≤ scale * scale) && lowerOk c.u c.ul &&
    decide (scale * scale ≤ c.v * c.hi) && upperOk c.v c.vl &&
    decide ((neg (logLowerI c.u c.ul)).hi ≤ xlo) &&
    decide (xhi ≤ (neg (logUpperI c.v c.vl)).lo)

/-! ### Logarithm certificates for dyadic numbers in `(0,1]` -/

/-- Certificate for `log (value a)` with `0 < value a ≤ 1`: `u` is a dyadic
lower bound for `1 / value a` carrying a lower ladder, and `v` is a dyadic
upper bound for `1 / value a` carrying an upper ladder. -/
structure LogNegCert where
  a : Int
  u : Int
  ul : List Int
  v : Int
  vl : List Int

/-- The Boolean condition the kernel checks for a `LogNegCert`. -/
def logNegOk (c : LogNegCert) : Bool :=
  decide (0 < c.a) && decide (c.u * c.a ≤ scale * scale) && lowerOk c.u c.ul &&
    decide (scale * scale ≤ c.v * c.a) && upperOk c.v c.vl

/-- The dyadic interval the certificate produces for `log (value a)`. -/
def logNegI (c : LogNegCert) : DI :=
  ⟨-(logUpperI c.v c.vl).hi, -(logLowerI c.u c.ul).lo⟩

/-- The dyadic interval for `H (value a) = 1 - value a + value a · log (value a)`
produced by a logarithm certificate. -/
def HptI (c : LogNegCert) : DI :=
  add (sub oneI (pt c.a)) (mul (pt c.a) (logNegI c))

/-- The trivial certificate, used as the out-of-range default of a table
lookup; it is rejected by every check except at the endpoint `0`. -/
def dfltCert : LogNegCert := ⟨0, 0, [], 0, []⟩

/-- A certificate is acceptable if it is the exact endpoint `0` (where
`H 0 = 1` and no logarithm is used) or carries a valid pair of ladders. -/
def epOk (c : LogNegCert) : Bool := (c.a == 0) || logNegOk c

/-- The enclosure of `H` at the endpoint of a certificate. -/
def epH (c : LogNegCert) : DI := if c.a == 0 then oneI else HptI c

/-! ### Sides of a spatial box -/

/-- One side of a spatial box: the dyadic endpoints together with the
enclosures of `H` and `log` at those endpoints. -/
structure Side where
  lo : Int
  hi : Int
  IHlo : DI
  IHhi : DI
  ILlo : DI
  ILhi : DI

/-- The side record determined by the two endpoint certificates. -/
def mkSide (c d : LogNegCert) : Side :=
  ⟨c.a, d.a, epH c, epH d, logNegI c, logNegI d⟩

/-! ### Materialised endpoints

The ladder of a logarithm certificate is expensive to replay, and the same
certificates occur in many sides and on several slabs.  An `ERec` stores the
*result* of the ladder — the enclosures of `H` and of `log` at the endpoint —
as literal integers; the certificate is checked, and the two literals are
compared with what the ladder produces, exactly once, in `Endpoints.lean`. -/

/-- A materialised endpoint: the dyadic point together with the enclosures of
`H` and of `log` there. -/
structure ERec where
  /-- The endpoint (scaled integer). -/
  a : Int
  /-- The enclosure of `H` at the endpoint. -/
  IH : DI
  /-- The enclosure of `log` at the endpoint (only used when `0 < a`). -/
  IL : DI
deriving DecidableEq, Repr

/-- The endpoint record determined by a certificate. -/
def mkERec (c : LogNegCert) : ERec := ⟨c.a, epH c, logNegI c⟩

/-- The side spanned by two materialised endpoints. -/
def ERec.side (e f : ERec) : Side := ⟨e.a, f.a, e.IH, f.IH, e.IL, f.IL⟩

/-- The out-of-range default of an endpoint lookup: the endpoint `0`. -/
def dfltERec : ERec := mkERec dfltCert

/-- The table of materialised endpoints: a balanced binary tree carrying, at
each node, the certificate and the endpoint record it must produce.  The
indexing convention is the one of `RTree` below. -/
inductive ETree where
  | leaf : ETree
  | node (c : LogNegCert) (e : ERec) (left right : ETree) : ETree

/-- Lookup of the materialised endpoint with a given index. -/
def ETree.get : ETree → Nat → ERec
  | .leaf, _ => dfltERec
  | .node _ e l rt, k =>
      if k == 0 then e
      else if (k - 1) % 2 == 0 then l.get ((k - 1) / 2) else rt.get ((k - 1) / 2)

/-- The Boolean condition validating the whole endpoint table: every
certificate is valid and every stored record is what its ladder produces. -/
def ETree.ok : ETree → Bool
  | .leaf => true
  | .node c e l rt => epOk c && (e == mkERec c) && ETree.ok l && ETree.ok rt

/-- Validating an endpoint-table node from its own checks and those of the two
subtrees, so that the table can be validated in small batches. -/
theorem ETree.ok_node_of {c : LogNegCert} {e : ERec} {l rt : ETree}
    (h1 : epOk c = true) (h2 : (e == mkERec c) = true)
    (h3 : l.ok = true) (h4 : rt.ok = true) :
    (ETree.node c e l rt).ok = true := by
  simp [ETree.ok, h1, h2, h3, h4]

/-- The `w`-interval of a side. -/
def Side.Iw (s : Side) : DI := ⟨s.lo, s.hi⟩

/-- The enclosure of `H w` on a side: `H` is antitone on `[0,1]`. -/
def Side.IH (s : Side) : DI := ⟨s.IHhi.lo, s.IHlo.hi⟩

/-- The enclosure of `log w` on a side with a positive lower endpoint. -/
def Side.IL (s : Side) : DI := ⟨s.ILlo.lo, s.ILhi.hi⟩

/-- The enclosure of the shape function `D w = H w + β w² - C`. -/
def Side.ID (s : Side) (IB IC : DI) : DI :=
  sub (add s.IH (mul IB (pow s.Iw 2))) IC

/-- The enclosure of the normalised shape `X = D / Δ`. -/
def Side.IX (s : Side) (IB IC IDl : DI) : DI := div (s.ID IB IC) IDl

/-- The enclosure of `D'(w) = log w + 2 β w` on a side. -/
def Side.IDd (s : Side) (IB : DI) : DI := add s.IL (mul (mul (intI 2) IB) s.Iw)

/-- The enclosure of `η_θ(X) = 3X - X² - 1 + θ X (1-X)²`. -/
def etaI (IT IX : DI) : DI :=
  add (sub (sub (mul (intI 3) IX) (pow IX 2)) oneI)
    (mul (mul IT IX) (pow (sub oneI IX) 2))

/-- The enclosure of `η'(X) = 3 - 2X + θ(1 - 4X + 3X²)`. -/
def etaDI (IT IX : DI) : DI :=
  add (sub (intI 3) (mul (intI 2) IX))
    (mul IT (add (sub oneI (mul (intI 4) IX)) (mul (intI 3) (pow IX 2))))

/-- The full leaf evaluation: the interval for the gap helper `L_α`. -/
def leafI (s₁ s₂ s₃ : Side) (IA IDl IB IC IT : DI) : DI :=
  let X₁ := s₁.IX IB IC IDl
  let X₂ := s₂.IX IB IC IDl
  let X₃ := s₃.IX IB IC IDl
  let E₁ := etaI IT X₁
  let E₂ := etaI IT X₂
  let E₃ := etaI IT X₃
  let P := sub (sub (mul (intI 2) (add (add X₁ X₂) X₃))
      (add (add (mul E₁ E₂) (mul E₁ E₃)) (mul E₂ E₃))) (intI 3)
  sub (add (mul (mul IDl (inv (intI 6))) P)
      (mul (mul (mul IA s₁.Iw) s₂.Iw) s₃.Iw))
    (mul (mul IB (inv (intI 3))) (add (add (pow s₁.Iw 2) (pow s₂.Iw 2)) (pow s₃.Iw 2)))

/-- The enclosure of `∂₁Φ` on a leaf, with the differentiated coordinate first. -/
def derivI (s₁ s₂ s₃ : Side) (IA IDl IB IC IT : DI) : DI :=
  let X₁ := s₁.IX IB IC IDl
  let E₂ := etaI IT (s₂.IX IB IC IDl)
  let E₃ := etaI IT (s₃.IX IB IC IDl)
  sub (add (mul s₁.IL (inv (intI 3))) (mul (mul IA s₂.Iw) s₃.Iw))
    (mul (mul (mul (etaDI IT X₁) (s₁.IDd IB)) (inv (intI 6))) (add E₂ E₃))

/-! ### Materialised side records

A `SRec` is a side of a box on one *fixed* parameter slab, together with all
the derived enclosures that the leaf rules need.  The fields are literal
integers in the generated data modules and their validity is checked once per
record (in `CoverTree.lean`), instead of being recomputed at every leaf. -/

structure SRec where
  /-- The lower endpoint of the side (scaled integer). -/
  lo : Int
  /-- The upper endpoint of the side (scaled integer). -/
  hi : Int
  /-- The enclosure of `X` on the side. -/
  IX : DI
  /-- The enclosure of `η_θ(X)` on the side. -/
  E : DI
  /-- The enclosure of `w²` on the side. -/
  Iw2 : DI
  /-- The enclosure of `log w / 3` on the side (only used when `0 < lo`). -/
  IL3 : DI
  /-- The enclosure of `η'(X) · D'(w) / 6` (only used when `0 < lo`). -/
  ED6 : DI
deriving DecidableEq, Repr

/-- The record determined by a side and the slab parameters. -/
def mkSRec (s : Side) (IDl IB IC IT : DI) : SRec :=
  let X := s.IX IB IC IDl
  { lo := s.lo, hi := s.hi, IX := X, E := etaI IT X, Iw2 := pow s.Iw 2,
    IL3 := mul s.IL (inv (intI 3)),
    ED6 := mul (mul (etaDI IT X) (s.IDd IB)) (inv (intI 6)) }

/-- The `w`-interval of a record. -/
def SRec.Iw (r : SRec) : DI := ⟨r.lo, r.hi⟩

/-- The leaf evaluation from three materialised records.  `ID6` and `IB3` are
the pooled slab constants `Δ/6` and `β/3`. -/
def leafS (r₁ r₂ r₃ : SRec) (IA ID6 IB3 : DI) : DI :=
  let P := sub (sub (mul (intI 2) (add (add r₁.IX r₂.IX) r₃.IX))
      (add (add (mul r₁.E r₂.E) (mul r₁.E r₃.E)) (mul r₂.E r₃.E))) (intI 3)
  sub (add (mul ID6 P) (mul (mul (mul IA r₁.Iw) r₂.Iw) r₃.Iw))
    (mul IB3 (add (add r₁.Iw2 r₂.Iw2) r₃.Iw2))

/-- The derivative evaluation from three materialised records; `r₁` is the
differentiated coordinate. -/
def derivS (r₁ r₂ r₃ : SRec) (IA : DI) : DI :=
  sub (add r₁.IL3 (mul (mul IA r₂.Iw) r₃.Iw)) (mul r₁.ED6 (add r₂.E r₃.E))

/-! ### Dyadic boxes -/

def imin (a b : Int) : Int := if a ≤ b then a else b
def imax (a b : Int) : Int := if a ≤ b then b else a

/-- A dyadic box: the endpoints are scaled integers. -/
structure DBox where
  l₁ : Int
  u₁ : Int
  l₂ : Int
  u₂ : Int
  l₃ : Int
  u₃ : Int
deriving DecidableEq

/-- The box tightened by the ordering `w₁ ≤ w₂ ≤ w₃`. -/
def DBox.tighten (b : DBox) : DBox :=
  ⟨b.l₁, imin b.u₁ (imin b.u₂ b.u₃), imax b.l₁ b.l₂, imin b.u₂ b.u₃,
    imax (imax b.l₁ b.l₂) b.l₃, b.u₃⟩

/-- Splitting a dyadic box: the lower half. -/
def DBox.setHi (b : DBox) (axis : Nat) (c : Int) : DBox :=
  match axis with
  | 0 => { b with u₁ := c }
  | 1 => { b with u₂ := c }
  | _ => { b with u₃ := c }

/-- Splitting a dyadic box: the upper half. -/
def DBox.setLo (b : DBox) (axis : Nat) (c : Int) : DBox :=
  match axis with
  | 0 => { b with l₁ := c }
  | 1 => { b with l₂ := c }
  | _ => { b with l₃ := c }

def DBox.coordLo (b : DBox) (k : Nat) : Int :=
  match k with | 0 => b.l₁ | 1 => b.l₂ | _ => b.l₃

def DBox.coordHi (b : DBox) (k : Nat) : Int :=
  match k with | 0 => b.u₁ | 1 => b.u₂ | _ => b.u₃

/-- The root box of every spatial cover. -/
def rootBox : DBox := ⟨0, scale, 0, scale, 0, scale⟩

/-! ### The subdivision tree -/

/-- A subdivision tree: splits carry the axis and the exact dyadic cut point,
leaves carry the name of a proved acceptance rule together with the indices of
the side records it uses.  The `cvalue` leaf is the *centered* rule: besides
the three sides of the box it names three degenerate (one-point) sides, the
centre at which the gap helper is evaluated. -/
inductive STree where
  | split (axis : Nat) (cut : Int) (left right : STree) : STree
  | empty : STree
  | small : STree
  | mixed : STree
  | value (p₁ p₂ p₃ : Nat) : STree
  | desc (k p₁ p₂ p₃ : Nat) : STree
  | asc (k p₁ p₂ p₃ : Nat) : STree
  | cvalue (p₁ p₂ p₃ q₁ q₂ q₃ : Nat) : STree
deriving Repr

/-! ### The record table

The records of a slab are stored in a *balanced binary tree* in heap order
(the children of index `k` are `2k+1` and `2k+2`), together with the indices of
the two endpoint certificates they were derived from.  A list would make every
leaf of the cover pay a linear scan during kernel reduction; with the tree a
lookup costs about ten steps. -/

/-- The out-of-range default of a record lookup; it is rejected by every
check, because no box side has `hi < lo`. -/
def dfltSRec : SRec := ⟨1, 0, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩⟩

/-- The record table of one slab: a balanced binary tree in heap order. -/
inductive RTree where
  | leaf : RTree
  | node (i j : Nat) (r : SRec) (left right : RTree) : RTree

/-- Lookup of the record with a given index. -/
def RTree.getS : RTree → Nat → SRec
  | .leaf, _ => dfltSRec
  | .node _ _ r l rt, k =>
      if k == 0 then r
      else if (k - 1) % 2 == 0 then l.getS ((k - 1) / 2) else rt.getS ((k - 1) / 2)

/-- The Boolean condition validating one materialised record against the two
materialised endpoints it comes from. -/
def recOkB (e f : ERec) (r : SRec) (IDl IB IC IT : DI) : Bool :=
  decide (0 ≤ e.a) && decide (f.a ≤ scale) &&
    (r == mkSRec (e.side f) IDl IB IC IT)

/-- The Boolean condition validating a whole record table against the table of
materialised endpoints. -/
def RTree.ok (etbl : ETree) (IDl IB IC IT : DI) : RTree → Bool
  | .leaf => true
  | .node i j r l rt =>
      recOkB (etbl.get i) (etbl.get j) r IDl IB IC IT &&
        RTree.ok etbl IDl IB IC IT l && RTree.ok etbl IDl IB IC IT rt

/-- Validating a node from its own record check and the two subtree checks.
This lets the generated data modules validate the record table in small
batches — one kernel check per batch — instead of one enormous check whose
cost grows superlinearly with the size of the table. -/
theorem RTree.ok_node_of {etbl : ETree} {IDl IB IC IT : DI} {i j : Nat} {r : SRec}
    {l rt : RTree}
    (h1 : recOkB (etbl.get i) (etbl.get j) r IDl IB IC IT = true)
    (h2 : RTree.ok etbl IDl IB IC IT l = true)
    (h3 : RTree.ok etbl IDl IB IC IT rt = true) :
    RTree.ok etbl IDl IB IC IT (.node i j r l rt) = true := by
  simp [RTree.ok, h1, h2, h3]

/-! ### The Boolean checkers -/

/-- The endpoint condition of one side of a leaf box. -/
def sideOkS (r : SRec) (lo hi : Int) : Bool :=
  (r.lo == lo) && (r.hi == hi) && decide (0 ≤ lo) && decide (hi ≤ scale)

/-- The largest distance from a point of the side to the point `c`. -/
def SRec.radAt (r : SRec) (c : Int) : Int := imax (r.hi - c) (c - r.lo)

/-- An upper bound for the absolute value of every member of an interval. -/
def absBound (d : DI) : Int := imax (-d.lo) d.hi

/-- The centered (mean-value) leaf test of blueprint section 9.7, with `IA` the
enclosure of the coefficient of `w₁w₂w₃` in the gap helper.  The records
`m₁ m₂ m₃` are one-point sides inside the three sides of the box: the value of
the helper there, decreased by the mean-value defect `Σ Kᵢ · radᵢ`, must still
be nonnegative.  `Kᵢ` is the certified bound on `|∂ᵢΦ|` over the box, `radᵢ`
the largest distance from the `i`-th side to its centre. -/
def centOk (r₁ r₂ r₃ m₁ m₂ m₃ : SRec) (IA ID6 IB3 : DI) : Bool :=
  (m₁.lo == m₁.hi) && (m₂.lo == m₂.hi) && (m₃.lo == m₃.hi) &&
    decide (r₁.lo ≤ m₁.lo) && decide (m₁.lo ≤ r₁.hi) &&
    decide (r₂.lo ≤ m₂.lo) && decide (m₂.lo ≤ r₂.hi) &&
    decide (r₃.lo ≤ m₃.lo) && decide (m₃.lo ≤ r₃.hi) &&
    decide (0 < r₁.lo) && decide (0 < r₂.lo) && decide (0 < r₃.lo) &&
    decide (absBound (derivS r₁ r₂ r₃ IA) * r₁.radAt m₁.lo
        + absBound (derivS r₂ r₁ r₃ IA) * r₂.radAt m₂.lo
        + absBound (derivS r₃ r₁ r₂ IA) * r₃.radAt m₃.lo
      ≤ (leafS m₁ m₂ m₃ IA ID6 IB3).lo * scale)

/-- The Boolean acceptance test of a leaf or a whole subtree, on a finite
slab: `IA` is the enclosure of `α` and `ID6`, `IB3` the pooled constants
`Δ/6` and `β/3`. -/
def chkS (tbl : RTree) (IA ID6 IB3 : DI) : STree → DBox → Bool
  | .split axis cut l r, b =>
      decide (b.coordLo axis ≤ cut) && decide (cut ≤ b.coordHi axis) &&
        chkS tbl IA ID6 IB3 l (b.setHi axis cut) &&
        chkS tbl IA ID6 IB3 r (b.setLo axis cut)
  | .empty, b => decide (b.u₂ < b.l₁) || decide (b.u₃ < b.l₂)
  | .small, b =>
      let t := b.tighten
      decide (0 ≤ t.l₁) && decide (10 * t.u₁ ≤ scale) && decide (10 * t.u₂ ≤ scale) &&
        decide (10 * t.u₃ ≤ scale) && decide (0 ≤ t.l₂) && decide (0 ≤ t.l₃)
  | .mixed, b =>
      let t := b.tighten
      decide (0 ≤ t.l₁) && decide (10 * t.u₁ ≤ scale) &&
        decide (19 * scale ≤ 20 * t.l₂) && decide (t.u₂ ≤ scale) &&
        decide (19 * scale ≤ 20 * t.l₃) && decide (t.u₃ ≤ scale)
  | .value p₁ p₂ p₃, b =>
      let t := b.tighten
      let r₁ := tbl.getS p₁; let r₂ := tbl.getS p₂; let r₃ := tbl.getS p₃
      sideOkS r₁ t.l₁ t.u₁ && sideOkS r₂ t.l₂ t.u₂ && sideOkS r₃ t.l₃ t.u₃ &&
        decide (0 ≤ (leafS r₁ r₂ r₃ IA ID6 IB3).lo)
  | .desc k p₁ p₂ p₃, b =>
      let t := b.tighten
      let r₁ := tbl.getS p₁; let r₂ := tbl.getS p₂; let r₃ := tbl.getS p₃
      decide (k < 3) &&
        sideOkS r₁ (t.coordLo k) (t.coordHi k) &&
        (match k with
         | 0 => sideOkS r₂ t.l₂ t.u₂ && sideOkS r₃ t.l₃ t.u₃
         | 1 => sideOkS r₂ t.l₁ t.u₁ && sideOkS r₃ t.l₃ t.u₃
         | _ => sideOkS r₂ t.l₁ t.u₁ && sideOkS r₃ t.l₂ t.u₂) &&
        decide (0 < t.coordLo k) && decide (0 < t.coordHi k) &&
        decide (0 < (derivS r₁ r₂ r₃ IA).lo)
  | .asc k p₁ p₂ p₃, b =>
      let t := b.tighten
      let r₁ := tbl.getS p₁; let r₂ := tbl.getS p₂; let r₃ := tbl.getS p₃
      decide (k < 3) &&
        sideOkS r₁ (t.coordLo k) (t.coordHi k) &&
        (match k with
         | 0 => sideOkS r₂ t.l₂ t.u₂ && sideOkS r₃ t.l₃ t.u₃
         | 1 => sideOkS r₂ t.l₁ t.u₁ && sideOkS r₃ t.l₃ t.u₃
         | _ => sideOkS r₂ t.l₁ t.u₁ && sideOkS r₃ t.l₂ t.u₂) &&
        decide (0 < t.coordLo k) && decide (0 < t.coordHi k) &&
        decide (t.coordHi k < scale) &&
        decide ((derivS r₁ r₂ r₃ IA).hi < 0)
  | .cvalue p₁ p₂ p₃ q₁ q₂ q₃, b =>
      let t := b.tighten
      let r₁ := tbl.getS p₁; let r₂ := tbl.getS p₂; let r₃ := tbl.getS p₃
      sideOkS r₁ t.l₁ t.u₁ && sideOkS r₂ t.l₂ t.u₂ && sideOkS r₃ t.l₃ t.u₃ &&
        centOk r₁ r₂ r₃ (tbl.getS q₁) (tbl.getS q₂) (tbl.getS q₃) IA ID6 IB3

/-- The Boolean acceptance test of the tail cover (`h ≥ 15`).  There `α ≥ 10`
is used through the constant interval `[10,10]`, and the `asc` rule is the
conditional tail-descent rule, which compares the `α`-free derivative bound
with the `α`-free value bound. -/
def chkTS (tbl : RTree) (ID6 IB3 : DI) : STree → DBox → Bool
  | .split axis cut l r, b =>
      decide (b.coordLo axis ≤ cut) && decide (cut ≤ b.coordHi axis) &&
        chkTS tbl ID6 IB3 l (b.setHi axis cut) &&
        chkTS tbl ID6 IB3 r (b.setLo axis cut)
  | .empty, b => decide (b.u₂ < b.l₁) || decide (b.u₃ < b.l₂)
  | .small, b =>
      let t := b.tighten
      decide (0 ≤ t.l₁) && decide (10 * t.u₁ ≤ scale) && decide (10 * t.u₂ ≤ scale) &&
        decide (10 * t.u₃ ≤ scale) && decide (0 ≤ t.l₂) && decide (0 ≤ t.l₃)
  | .mixed, b =>
      let t := b.tighten
      decide (0 ≤ t.l₁) && decide (10 * t.u₁ ≤ scale) &&
        decide (19 * scale ≤ 20 * t.l₂) && decide (t.u₂ ≤ scale) &&
        decide (19 * scale ≤ 20 * t.l₃) && decide (t.u₃ ≤ scale)
  | .value p₁ p₂ p₃, b =>
      let t := b.tighten
      let r₁ := tbl.getS p₁; let r₂ := tbl.getS p₂; let r₃ := tbl.getS p₃
      sideOkS r₁ t.l₁ t.u₁ && sideOkS r₂ t.l₂ t.u₂ && sideOkS r₃ t.l₃ t.u₃ &&
        decide (0 ≤ (leafS r₁ r₂ r₃ (intI 10) ID6 IB3).lo)
  | .desc k p₁ p₂ p₃, b =>
      let t := b.tighten
      let r₁ := tbl.getS p₁; let r₂ := tbl.getS p₂; let r₃ := tbl.getS p₃
      decide (k < 3) &&
        sideOkS r₁ (t.coordLo k) (t.coordHi k) &&
        (match k with
         | 0 => sideOkS r₂ t.l₂ t.u₂ && sideOkS r₃ t.l₃ t.u₃
         | 1 => sideOkS r₂ t.l₁ t.u₁ && sideOkS r₃ t.l₃ t.u₃
         | _ => sideOkS r₂ t.l₁ t.u₁ && sideOkS r₃ t.l₂ t.u₂) &&
        decide (0 < t.coordLo k) && decide (0 < t.coordHi k) &&
        decide (0 < (derivS r₁ r₂ r₃ (intI 10)).lo)
  | .asc k p₁ p₂ p₃, b =>
      let t := b.tighten
      let r₁ := tbl.getS p₁; let r₂ := tbl.getS p₂; let r₃ := tbl.getS p₃
      decide (k < 3) &&
        sideOkS r₁ (t.coordLo k) (t.coordHi k) &&
        (match k with
         | 0 => sideOkS r₂ t.l₂ t.u₂ && sideOkS r₃ t.l₃ t.u₃
         | 1 => sideOkS r₂ t.l₁ t.u₁ && sideOkS r₃ t.l₃ t.u₃
         | _ => sideOkS r₂ t.l₁ t.u₁ && sideOkS r₃ t.l₂ t.u₂) &&
        decide (0 < t.coordLo k) && decide (0 < t.coordHi k) &&
        decide (t.coordHi k < scale) &&
        decide ((derivS r₁ r₂ r₃ ⟨0, 0⟩).hi * (t.coordLo k)
          < (leafS r₁ r₂ r₃ ⟨0, 0⟩ ID6 IB3).lo * scale)
  | .cvalue p₁ p₂ p₃ q₁ q₂ q₃, b =>
      let t := b.tighten
      let r₁ := tbl.getS p₁; let r₂ := tbl.getS p₂; let r₃ := tbl.getS p₃
      sideOkS r₁ t.l₁ t.u₁ && sideOkS r₂ t.l₂ t.u₂ && sideOkS r₃ t.l₃ t.u₃ &&
        centOk r₁ r₂ r₃ (tbl.getS q₁) (tbl.getS q₂) (tbl.getS q₃) (intI 10) ID6 IB3

/-! ### Parameter certificates -/

/-- A parameter certificate: a dyadic interval of `h` together with the two
exponential certificates needed by (B1). -/
structure ParamCert where
  hlo : Int
  hhi : Int
  cz : ExpCert
  ct : ExpCert

namespace ParamCert

variable (c : ParamCert)

def Ih : DI := ⟨c.hlo, c.hhi⟩
def Iz : DI := ⟨c.cz.lo, c.cz.hi⟩
def Ip : DI := div (mul (mul twoI c.Ih) c.Iz) (pow (sub oneI c.Iz) 2)
def It : DI := ⟨c.ct.lo, c.ct.hi⟩
def Ir : DI := mul c.It c.Iz
def IDelta : DI := sub c.It c.Ir
def IAlpha : DI := div (mul twoI c.Ih) (mul threeI (pow c.IDelta 2))
def IBeta : DI := div c.Ip (mul twoI c.It)
def IC : DI := sub oneI (mul (add oneI (div c.Ip twoI)) c.It)

/-- The Boolean acceptance condition checked by the kernel. -/
def ok : Bool :=
  expOk c.cz (-c.hhi) (-c.hlo) &&
    decide (0 < (pow (sub oneI c.Iz) 2).lo) &&
    expOk c.ct (-(c.Ip).hi) (-(c.Ip).lo) &&
    decide (0 < (mul threeI (pow c.IDelta 2)).lo) &&
    decide (0 < (mul twoI c.It).lo)

end ParamCert

/-- The enclosure of the cubic parameter `θ(X)`. -/
def thetaI (IX : DI) : DI :=
  div (add (sub (pow IX 2) (mul (intI 3) IX)) oneI) (mul IX (pow (sub oneI IX) 2))

end Itv
end TriangleNumerical
