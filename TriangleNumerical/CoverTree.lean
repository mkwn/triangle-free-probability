import TriangleNumerical.TailEval
import TriangleNumerical.LocalLarge

/- ### From `SideRec` -/

/-!
# Materialised side records

Every leaf of a spatial cover needs, for each of its three coordinates, the
enclosures of `X(w)`, `η_θ(X(w))`, `w²` and — for the derivative rules —
`log w / 3` and `η'(X(w)) · D'(w) / 6`.  These depend only on the *side*
(the pair of dyadic endpoints) and on the parameter enclosures of the slab,
not on the leaf: on a given slab the 400 000-odd leaf sides of the cover use
only a few hundred distinct sides.

This file introduces the validity predicate `SRec.Good` for a materialised
record (`SRec` in `Kernel.lean`, whose fields are literal integers in the
generated data modules), proves it for a record that the kernel has checked
against its two endpoint certificates, and proves the leaf and derivative
evaluators `leafS`, `derivS` sound in terms of it.  The slab-wide factors
`Δ/6` and `β/3` are likewise pooled into the two arguments `ID6`, `IB3`.

Nothing here is assumed: `recOkB` re-derives each record from the endpoint
logarithm certificates inside the kernel, and `Good` is proved from that
check together with the parameter enclosures of the slab.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Itv

open TriangleLogCertificate Branch

/-! ### Endpoint certificates, including the endpoint `0` -/

theorem value_zero : value (0 : Int) = 0 := by simp [value]

theorem value_mono {a b : Int} (h : a ≤ b) : value a ≤ value b := by
  have hs := scale_pos_real
  have hab : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h
  simp only [value]
  gcongr

theorem value_nonneg {a : Int} (h : 0 ≤ a) : 0 ≤ value a := by
  have := value_mono h
  simpa [value_zero] using this

theorem value_le_one {a : Int} (h : a ≤ scale) : value a ≤ 1 := by
  have := value_mono h
  rwa [value_one] at this

theorem mem_epH {c : LogNegCert} (h : epOk c = true) : (epH c).Mem (H (value c.a)) := by
  simp only [epOk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · have hz : value c.a = 0 := by simp [value, h]
    simp only [epH, h, beq_self_eq_true, if_true]
    rw [show value (0 : Int) = 0 by simp [value]]
    exact mem_HzeroI
  · have hne : ¬ (c.a == 0) = true := by
      simp only [beq_iff_eq]
      intro h0
      simp only [logNegOk, Bool.and_eq_true, decide_eq_true_eq, h0] at h
      omega
    simp only [epH, if_neg hne]
    exact mem_HptI h

theorem mem_epL {c : LogNegCert} (h : epOk c = true) (hpos : 0 < c.a) :
    (logNegI c).Mem (Real.log (value c.a)) := by
  simp only [epOk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · omega
  · exact mem_logNegI h

/-- Validity of a materialised endpoint: the two stored intervals enclose `H`
and `log` at the endpoint. -/
structure ERec.Good (e : ERec) : Prop where
  /-- The `IH` field encloses `H` at the endpoint. -/
  memH : e.IH.Mem (H (value e.a))
  /-- The `IL` field encloses `log` at a positive endpoint. -/
  memL : 0 < e.a → e.IL.Mem (Real.log (value e.a))

/-- A materialised endpoint checked against its certificate is valid. -/
theorem good_mkERec {c : LogNegCert} (h : epOk c = true) : (mkERec c).Good :=
  ⟨mem_epH h, fun hp => mem_epL h hp⟩

/-- Soundness of the kernel check of the endpoint table: every lookup, at
every index, returns a valid endpoint. -/
theorem good_ETree_get :
    ∀ t : ETree, t.ok = true → ∀ k : Nat, (t.get k).Good := by
  intro t
  induction t with
  | leaf =>
      intro _ _
      exact good_mkERec (c := dfltCert) (by decide)
  | node c e l rt ihl ihr =>
      intro hok k
      simp only [ETree.ok, Bool.and_eq_true, beq_iff_eq] at hok
      simp only [ETree.get]
      split
      · rw [hok.1.1.2]; exact good_mkERec hok.1.1.1
      · split
        · exact ihl hok.1.2 _
        · exact ihr hok.2 _

/-- Validity of a materialised side record on a slab: every field encloses the
quantity it stands for, at every weight of the side. -/
structure SRec.Good (r : SRec) (h θ : ℝ) : Prop where
  /-- The side lies in `[0,1]`: lower endpoint. -/
  lo_nonneg : 0 ≤ r.lo
  /-- The side lies in `[0,1]`: upper endpoint. -/
  hi_le : r.hi ≤ scale
  /-- The `X` field encloses `X(w)`. -/
  memX : ∀ w : ℝ, value r.lo ≤ w → w ≤ value r.hi → r.IX.Mem (bX h w)
  /-- The `E` field encloses `η_θ(X(w))`. -/
  memE : ∀ w : ℝ, value r.lo ≤ w → w ≤ value r.hi → r.E.Mem (etaT θ (bX h w))
  /-- The `Iw2` field encloses `w²`. -/
  memw2 : ∀ w : ℝ, value r.lo ≤ w → w ≤ value r.hi → r.Iw2.Mem (w ^ 2)
  /-- On a side with positive endpoints, the two derivative fields enclose
  `log w / 3` and `η'(X(w)) · D'(w) / 6`. -/
  memPos : 0 < r.lo → 0 < r.hi → ∀ w : ℝ, value r.lo ≤ w → w ≤ value r.hi →
      r.IL3.Mem (Real.log w * (1 / 3)) ∧
        r.ED6.Mem (etaD θ (bX h w) * bDd h w * (1 / 6))

theorem mem_inv_three : (inv (intI 3)).Mem (1 / (3:ℝ)) := by
  have h := mem_inv_intI (n := 3) (by norm_num)
  norm_num at h
  exact h

theorem mem_inv_six : (inv (intI 6)).Mem (1 / (6:ℝ)) := by
  have h := mem_inv_intI (n := 6) (by norm_num)
  norm_num at h
  exact h

/-- The pooled slab constant `Δ/6`. -/
theorem mem_pooled6 {ID : DI} {h : ℝ} (hD : ID.Mem (bDelta h)) :
    (mul ID (inv (intI 6))).Mem (bDelta h * (1/6)) := mem_mul hD mem_inv_six

/-- The pooled slab constant `β/3`. -/
theorem mem_pooled3 {IB : DI} {h : ℝ} (hB : IB.Mem (bBeta h)) :
    (mul IB (inv (intI 3))).Mem (bBeta h * (1/3)) := mem_mul hB mem_inv_three

/-- A record built from a side with valid endpoint enclosures is good. -/
theorem good_mkSRec {s : Side} {IDl IB IC IT : DI} {h θ : ℝ}
    (hHlo : s.IHlo.Mem (H (value s.lo))) (hHhi : s.IHhi.Mem (H (value s.hi)))
    (hlo : 0 ≤ s.lo) (hhi : s.hi ≤ scale)
    (hLlo : 0 < s.lo → s.ILlo.Mem (Real.log (value s.lo)))
    (hLhi : 0 < s.hi → s.ILhi.Mem (Real.log (value s.hi)))
    (hB : IB.Mem (bBeta h)) (hC : IC.Mem (bC h)) (hD : IDl.Mem (bDelta h))
    (hT : IT.Mem θ) (hDpos : 0 < IDl.lo) :
    (mkSRec s IDl IB IC IT).Good h θ := by
  have h0 : 0 ≤ value s.lo := value_nonneg hlo
  have h1 : value s.hi ≤ 1 := value_le_one hhi
  refine ⟨hlo, hhi, ?_, ?_, ?_, ?_⟩
  · intro w hw1 hw2
    exact (s.sound hHlo hHhi h0 h1 hB hC hD hDpos hw1 hw2).2.2.2
  · intro w hw1 hw2
    exact mem_etaI hT (s.sound hHlo hHhi h0 h1 hB hC hD hDpos hw1 hw2).2.2.2
  · intro w hw1 hw2
    exact mem_pow (⟨hw1, hw2⟩ : s.Iw.Mem w) 2
  · intro hp hp' w hw1 hw2
    have hlo' : 0 < value s.lo := value_pos hp
    obtain ⟨hlog, hDd⟩ := s.sound_log (hLlo hp) (hLhi hp') hlo' hB hw1 hw2
    have hX := (s.sound hHlo hHhi h0 h1 hB hC hD hDpos hw1 hw2).2.2.2
    exact ⟨mem_mul hlog mem_inv_three,
      mem_mul (mem_mul (mem_etaDI hT hX) hDd) mem_inv_six⟩

/-- The default record of an out-of-range lookup is vacuously good: its side
is empty. -/
theorem good_dfltSRec {h θ : ℝ} : dfltSRec.Good h θ := by
  have hempty : ∀ w : ℝ, value dfltSRec.lo ≤ w → w ≤ value dfltSRec.hi → False := by
    intro w hw1 hw2
    have h1 : (0:ℝ) < value (1 : Int) := value_pos (by norm_num)
    have h2 : value (0 : Int) = 0 := value_zero
    simp only [dfltSRec] at hw1 hw2
    rw [h2] at hw2
    linarith
  refine ⟨by norm_num [dfltSRec], by norm_num [dfltSRec, scale],
    fun w h1 h2 => absurd (hempty w h1 h2) (by simp),
    fun w h1 h2 => absurd (hempty w h1 h2) (by simp),
    fun w h1 h2 => absurd (hempty w h1 h2) (by simp),
    fun _ _ w h1 h2 => absurd (hempty w h1 h2) (by simp)⟩

/-- Soundness of the kernel check of a single materialised record. -/
theorem good_of_recOkB {e f : ERec} {r : SRec} {IDl IB IC IT : DI} {h θ : ℝ}
    (ge : e.Good) (gf : f.Good)
    (hok : recOkB e f r IDl IB IC IT = true)
    (hB : IB.Mem (bBeta h)) (hC : IC.Mem (bC h)) (hD : IDl.Mem (bDelta h))
    (hT : IT.Mem θ) (hDpos : 0 < IDl.lo) : r.Good h θ := by
  simp only [recOkB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨hlo, hhi⟩, heq⟩ := hok
  subst heq
  exact good_mkSRec (s := e.side f) ge.memH gf.memH hlo hhi
    (fun hp => ge.memL hp) (fun hp => gf.memL hp) hB hC hD hT hDpos

/-- Soundness of the kernel check of a whole record table: every lookup, at
every index, returns a valid record. -/
theorem good_getS {etbl : ETree} {IDl IB IC IT : DI} {h θ : ℝ}
    (hE : etbl.ok = true)
    (hB : IB.Mem (bBeta h)) (hC : IC.Mem (bC h)) (hD : IDl.Mem (bDelta h))
    (hT : IT.Mem θ) (hDpos : 0 < IDl.lo) :
    ∀ t : RTree, t.ok etbl IDl IB IC IT = true → ∀ k : Nat, (t.getS k).Good h θ := by
  have hg := good_ETree_get etbl hE
  intro t
  induction t with
  | leaf => intro _ k; exact good_dfltSRec
  | node i j r l rt ihl ihr =>
      intro hok k
      simp only [RTree.ok, Bool.and_eq_true] at hok
      simp only [RTree.getS]
      split
      · exact good_of_recOkB (hg i) (hg j) hok.1.1 hB hC hD hT hDpos
      · split
        · exact ihl hok.1.2 _
        · exact ihr hok.2 _

/-! ### Soundness of the pooled leaf evaluators -/

/-- Soundness of the leaf evaluator on materialised records. -/
theorem mem_leafS_gen {r₁ r₂ r₃ : SRec} {IA ID6 IB3 : DI} {A h θ w₁ w₂ w₃ : ℝ}
    (g₁ : r₁.Good h θ) (g₂ : r₂.Good h θ) (g₃ : r₃.Good h θ)
    (hA : IA.Mem A) (hD6 : ID6.Mem (bDelta h * (1 / 6)))
    (hB3 : IB3.Mem (bBeta h * (1 / 3)))
    (hw₁ : value r₁.lo ≤ w₁) (hw₁' : w₁ ≤ value r₁.hi)
    (hw₂ : value r₂.lo ≤ w₂) (hw₂' : w₂ ≤ value r₂.hi)
    (hw₃ : value r₃.lo ≤ w₃) (hw₃' : w₃ ≤ value r₃.hi) :
    (leafS r₁ r₂ r₃ IA ID6 IB3).Mem (LgenA A h θ w₁ w₂ w₃) := by
  have hu₁ : r₁.Iw.Mem w₁ := ⟨hw₁, hw₁'⟩
  have hu₂ : r₂.Iw.Mem w₂ := ⟨hw₂, hw₂'⟩
  have hu₃ : r₃.Iw.Mem w₃ := ⟨hw₃, hw₃'⟩
  have hX₁ := g₁.memX w₁ hw₁ hw₁'
  have hX₂ := g₂.memX w₂ hw₂ hw₂'
  have hX₃ := g₃.memX w₃ hw₃ hw₃'
  have hE₁ := g₁.memE w₁ hw₁ hw₁'
  have hE₂ := g₂.memE w₂ hw₂ hw₂'
  have hE₃ := g₃.memE w₃ hw₃ hw₃'
  have hs₁ := g₁.memw2 w₁ hw₁ hw₁'
  have hs₂ := g₂.memw2 w₂ hw₂ hw₂'
  have hs₃ := g₃.memw2 w₃ hw₃ hw₃'
  have hP := mem_sub (mem_sub (mem_mul (mem_intI 2) (mem_add (mem_add hX₁ hX₂) hX₃))
      (mem_add (mem_add (mem_mul hE₁ hE₂) (mem_mul hE₁ hE₃)) (mem_mul hE₂ hE₃)))
    (mem_intI 3)
  have hPeq : ((2:Int) : ℝ) * (bX h w₁ + bX h w₂ + bX h w₃)
      - (etaT θ (bX h w₁) * etaT θ (bX h w₂) + etaT θ (bX h w₁) * etaT θ (bX h w₃)
        + etaT θ (bX h w₂) * etaT θ (bX h w₃)) - ((3:Int) : ℝ)
      = gapP h θ w₁ w₂ w₃ := by
    simp only [gapP]; push_cast; ring
  rw [hPeq] at hP
  have hm := mem_sub (mem_add (mem_mul hD6 hP)
      (mem_mul (mem_mul (mem_mul hA hu₁) hu₂) hu₃))
    (mem_mul hB3 (mem_add (mem_add hs₁ hs₂) hs₃))
  have heq : bDelta h * (1 / 6) * gapP h θ w₁ w₂ w₃ + A * w₁ * w₂ * w₃
      - bBeta h * (1 / 3) * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2)
      = LgenA A h θ w₁ w₂ w₃ := by
    simp only [LgenA]
  rw [heq] at hm
  exact hm

/-- Soundness of the derivative evaluator on materialised records. -/
theorem mem_derivS_gen {r₁ r₂ r₃ : SRec} {IA : DI} {A h θ w₁ w₂ w₃ : ℝ}
    (g₁ : r₁.Good h θ) (g₂ : r₂.Good h θ) (g₃ : r₃.Good h θ)
    (hpos : 0 < r₁.lo) (hpos' : 0 < r₁.hi) (hA : IA.Mem A)
    (hw₁ : value r₁.lo ≤ w₁) (hw₁' : w₁ ≤ value r₁.hi)
    (hw₂ : value r₂.lo ≤ w₂) (hw₂' : w₂ ≤ value r₂.hi)
    (hw₃ : value r₃.lo ≤ w₃) (hw₃' : w₃ ≤ value r₃.hi) :
    (derivS r₁ r₂ r₃ IA).Mem (PhiD1gen A h θ w₁ w₂ w₃) := by
  have hu₂ : r₂.Iw.Mem w₂ := ⟨hw₂, hw₂'⟩
  have hu₃ : r₃.Iw.Mem w₃ := ⟨hw₃, hw₃'⟩
  have hE₂ := g₂.memE w₂ hw₂ hw₂'
  have hE₃ := g₃.memE w₃ hw₃ hw₃'
  obtain ⟨hL, hED⟩ := g₁.memPos hpos hpos' w₁ hw₁ hw₁'
  have hm := mem_sub (mem_add hL (mem_mul (mem_mul hA hu₂) hu₃))
    (mem_mul hED (mem_add hE₂ hE₃))
  have heq : Real.log w₁ * (1 / 3) + A * w₂ * w₃
      - etaD θ (bX h w₁) * bDd h w₁ * (1 / 6)
        * (etaT θ (bX h w₂) + etaT θ (bX h w₃))
      = PhiD1gen A h θ w₁ w₂ w₃ := by
    simp only [PhiD1gen]; ring
  rw [heq] at hm
  exact hm

/-! ### The three leaf rules on a finite slab -/

theorem nonneg_value_of_nonneg {n : Int} (h : 0 ≤ n) : (0:ℝ) ≤ value n := value_nonneg h

/-- The "direct value" leaf rule from materialised records. -/
theorem leafS_value_rule {r₁ r₂ r₃ : SRec} {IA ID6 IB3 : DI} {h θ w₁ w₂ w₃ : ℝ}
    (hh : 9 ≤ h) (g₁ : r₁.Good h θ) (g₂ : r₂.Good h θ) (g₃ : r₃.Good h θ)
    (hA : IA.Mem (bAlpha h)) (hD6 : ID6.Mem (bDelta h * (1 / 6)))
    (hB3 : IB3.Mem (bBeta h * (1 / 3)))
    (hgap : 0 ≤ (leafS r₁ r₂ r₃ IA ID6 IB3).lo)
    (hw₁ : value r₁.lo ≤ w₁) (hw₁' : w₁ ≤ value r₁.hi)
    (hw₂ : value r₂.lo ≤ w₂) (hw₂' : w₂ ≤ value r₂.hi)
    (hw₃ : value r₃.lo ≤ w₃) (hw₃' : w₃ ≤ value r₃.hi) :
    bM2 h ≤ entropyF (bAlpha h) (bG h θ) w₁ w₂ w₃ := by
  have hm := mem_leafS_gen g₁ g₂ g₃ hA hD6 hB3 hw₁ hw₁' hw₂ hw₂' hw₃ hw₃'
  have heq : LgenA (bAlpha h) h θ w₁ w₂ w₃ = Lalpha h θ w₁ w₂ w₃ := by
    simp only [LgenA, Lalpha]
  rw [heq] at hm
  have h1 : 0 ≤ Lalpha h θ w₁ w₂ w₃ := le_trans (nonneg_value_of_nonneg hgap) hm.1
  have h2 := Lalpha_le_gap (h := h) (θ := θ) hh w₁ w₂ w₃
  linarith

/-- The "decrease coordinate" leaf rule from materialised records. -/
theorem derivS_pos_rule {r₁ r₂ r₃ : SRec} {IA : DI} {h θ w₁ w₂ w₃ : ℝ}
    (g₁ : r₁.Good h θ) (g₂ : r₂.Good h θ) (g₃ : r₃.Good h θ)
    (hpos : 0 < r₁.lo) (hpos' : 0 < r₁.hi) (hA : IA.Mem (bAlpha h))
    (hsign : 0 < (derivS r₁ r₂ r₃ IA).lo)
    (hw₁ : value r₁.lo ≤ w₁) (hw₁' : w₁ ≤ value r₁.hi)
    (hw₂ : value r₂.lo ≤ w₂) (hw₂' : w₂ ≤ value r₂.hi)
    (hw₃ : value r₃.lo ≤ w₃) (hw₃' : w₃ ≤ value r₃.hi) :
    0 < PhiD1 h θ w₁ w₂ w₃ := by
  have hm := mem_derivS_gen g₁ g₂ g₃ hpos hpos' hA hw₁ hw₁' hw₂ hw₂' hw₃ hw₃'
  have h1 : 0 < PhiD1gen (bAlpha h) h θ w₁ w₂ w₃ := pos_of_mem hm hsign
  have h2 := PhiD1_eq_gen (h := h) (θ := θ) (w₁ := w₁) (w₂ := w₂) (w₃ := w₃) (bAlpha h)
  rw [h2]
  linarith

/-- The "increase coordinate" leaf rule from materialised records. -/
theorem derivS_neg_rule {r₁ r₂ r₃ : SRec} {IA : DI} {h θ w₁ w₂ w₃ : ℝ}
    (g₁ : r₁.Good h θ) (g₂ : r₂.Good h θ) (g₃ : r₃.Good h θ)
    (hpos : 0 < r₁.lo) (hpos' : 0 < r₁.hi) (hA : IA.Mem (bAlpha h))
    (hsign : (derivS r₁ r₂ r₃ IA).hi < 0)
    (hw₁ : value r₁.lo ≤ w₁) (hw₁' : w₁ ≤ value r₁.hi)
    (hw₂ : value r₂.lo ≤ w₂) (hw₂' : w₂ ≤ value r₂.hi)
    (hw₃ : value r₃.lo ≤ w₃) (hw₃' : w₃ ≤ value r₃.hi) :
    PhiD1 h θ w₁ w₂ w₃ < 0 := by
  have hm := mem_derivS_gen g₁ g₂ g₃ hpos hpos' hA hw₁ hw₁' hw₂ hw₂' hw₃ hw₃'
  have h1 : PhiD1gen (bAlpha h) h θ w₁ w₂ w₃ < 0 := neg_of_mem hm hsign
  have h2 := PhiD1_eq_gen (h := h) (θ := θ) (w₁ := w₁) (w₂ := w₂) (w₃ := w₃) (bAlpha h)
  rw [h2]
  linarith

end Itv
end TriangleNumerical


/- ### From `Centered` -/

/-!
# The centered (mean-value) leaf rule

Section 9.7 of the blueprint.  A leaf box is accepted by the *direct value*
rule only when the interval evaluation of the gap helper over the whole box is
nonnegative; because interval arithmetic overestimates, that forces the search
to subdivide until the boxes are tiny.  The centered rule replaces the interval
evaluation by

* the value of the helper at one **point** `c` of the box — a much tighter
  enclosure, since the weights are degenerate intervals there — and
* the mean-value defect `Σᵢ Kᵢ · radᵢ`, where `Kᵢ` bounds `|∂ᵢ|` of the helper
  on the box and `radᵢ` is the largest distance from a point of the `i`-th side
  to `cᵢ`,

which converges quadratically in the box width instead of linearly.  In the
covers replayed by this development it removes more than half of the leaves.

The mathematical content is three applications of the scalar mean-value
inequality, moving one coordinate at a time from `w` to `c`; the path stays
inside the box, which is a product of intervals, so the derivative bounds
obtained from the materialised side records apply at every intermediate point.
Both helpers are covered: `Lα` on a finite slab (`leafS_centered_rule`) and,
through the generic `LgenA_centered`, the tail helper `L₁₀`.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Itv

open TriangleLogCertificate Branch Set

/-! ### The scalar mean-value inequality -/

/-- If `|f'| ≤ K` on `[a,b]`, then `f` is `K`-Lipschitz there. -/
theorem abs_sub_le_of_deriv_bound {f f' : ℝ → ℝ} {a b K x y : ℝ}
    (hd : ∀ z ∈ Icc a b, HasDerivAt f (f' z) z)
    (hb : ∀ z ∈ Icc a b, |f' z| ≤ K)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f y - f x| ≤ K * |y - x| := by
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (fun z hz => (hd z hz).hasDerivWithinAt)
    (fun z hz => by simpa [Real.norm_eq_abs] using hb z hz) hx hy
  simpa [Real.norm_eq_abs] using h

/-! ### The centered bound for a symmetric differentiable objective -/

/-- The three-coordinate mean-value bound: the value of `F` anywhere in a box
of positive coordinates is at least its value at a point `c` of the box minus
the defect `Σ Kᵢ |wᵢ - cᵢ|`.  `D x y z` is the partial derivative of `F` in its
*first* argument, the other two being `y` and `z`; by symmetry of `F` the same
function gives the other two partials. -/
theorem centered_bound_gen {F D : ℝ → ℝ → ℝ → ℝ}
    (hd₁ : ∀ x y z : ℝ, x ≠ 0 → HasDerivAt (fun t => F t y z) (D x y z) x)
    (hd₂ : ∀ x y z : ℝ, y ≠ 0 → HasDerivAt (fun t => F x t z) (D y x z) y)
    (hd₃ : ∀ x y z : ℝ, z ≠ 0 → HasDerivAt (fun t => F x y t) (D z x y) z)
    {l₁ u₁ l₂ u₂ l₃ u₃ c₁ c₂ c₃ K₁ K₂ K₃ w₁ w₂ w₃ : ℝ}
    (hp₁ : 0 < l₁) (hp₂ : 0 < l₂) (hp₃ : 0 < l₃)
    (hc₁ : c₁ ∈ Icc l₁ u₁) (hc₂ : c₂ ∈ Icc l₂ u₂) (hc₃ : c₃ ∈ Icc l₃ u₃)
    (hw₁ : w₁ ∈ Icc l₁ u₁) (hw₂ : w₂ ∈ Icc l₂ u₂) (hw₃ : w₃ ∈ Icc l₃ u₃)
    (hK₁ : ∀ x₁ ∈ Icc l₁ u₁, ∀ x₂ ∈ Icc l₂ u₂, ∀ x₃ ∈ Icc l₃ u₃, |D x₁ x₂ x₃| ≤ K₁)
    (hK₂ : ∀ x₁ ∈ Icc l₁ u₁, ∀ x₂ ∈ Icc l₂ u₂, ∀ x₃ ∈ Icc l₃ u₃, |D x₂ x₁ x₃| ≤ K₂)
    (hK₃ : ∀ x₁ ∈ Icc l₁ u₁, ∀ x₂ ∈ Icc l₂ u₂, ∀ x₃ ∈ Icc l₃ u₃, |D x₃ x₁ x₂| ≤ K₃) :
    F c₁ c₂ c₃ - (K₁ * |w₁ - c₁| + K₂ * |w₂ - c₂| + K₃ * |w₃ - c₃|) ≤ F w₁ w₂ w₃ := by
  have step₁ : |F w₁ w₂ w₃ - F c₁ w₂ w₃| ≤ K₁ * |w₁ - c₁| := by
    refine abs_sub_le_of_deriv_bound (f := fun t => F t w₂ w₃)
      (f' := fun t => D t w₂ w₃) (fun z hz => ?_) (fun z hz => ?_) hc₁ hw₁
    · exact hd₁ z w₂ w₃ (ne_of_gt (lt_of_lt_of_le hp₁ hz.1))
    · exact hK₁ z hz w₂ hw₂ w₃ hw₃
  have step₂ : |F c₁ w₂ w₃ - F c₁ c₂ w₃| ≤ K₂ * |w₂ - c₂| := by
    refine abs_sub_le_of_deriv_bound (f := fun t => F c₁ t w₃)
      (f' := fun t => D t c₁ w₃) (fun z hz => ?_) (fun z hz => ?_) hc₂ hw₂
    · exact hd₂ c₁ z w₃ (ne_of_gt (lt_of_lt_of_le hp₂ hz.1))
    · exact hK₂ c₁ hc₁ z hz w₃ hw₃
  have step₃ : |F c₁ c₂ w₃ - F c₁ c₂ c₃| ≤ K₃ * |w₃ - c₃| := by
    refine abs_sub_le_of_deriv_bound (f := fun t => F c₁ c₂ t)
      (f' := fun t => D t c₁ c₂) (fun z hz => ?_) (fun z hz => ?_) hc₃ hw₃
    · exact hd₃ c₁ c₂ z (ne_of_gt (lt_of_lt_of_le hp₃ hz.1))
    · exact hK₃ c₁ hc₁ c₂ hc₂ z hz
  have b₁ := (abs_le.1 step₁).1
  have b₂ := (abs_le.1 step₂).1
  have b₃ := (abs_le.1 step₃).1
  linarith

/-! ### The gap helper with a general coefficient -/

/-- `LgenA A` differs from `Φ` by a constant and by `(α - A) w₁w₂w₃`. -/
theorem LgenA_eq_entropyF {h θ : ℝ} (hh : 0 < h) (A w₁ w₂ w₃ : ℝ) :
    LgenA A h θ w₁ w₂ w₃
      = entropyF (bAlpha h) (bG h θ) w₁ w₂ w₃
        - (bM2 h + bBeta h * (br h) ^ 2 / 3) - (bAlpha h - A) * (w₁ * w₂ * w₃) := by
  have h0 : LgenA A h θ w₁ w₂ w₃ = LgenA 0 h θ w₁ w₂ w₃ + A * (w₁ * w₂ * w₃) := by
    simp only [LgenA]; ring
  have h1 := gap_eq_base (h := h) (θ := θ) hh (w₁ := w₁) (w₂ := w₂) (w₃ := w₃)
  rw [h0]
  linarith

/-- The derivative of `LgenA A` in its first weight. -/
theorem hasDerivAt_LgenA₁ {h θ : ℝ} (hh : 0 < h) (A x y z : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t => LgenA A h θ t y z) (PhiD1gen A h θ x y z) x := by
  have hF : (fun t => LgenA A h θ t y z)
      = fun t => entropyF (bAlpha h) (bG h θ) t y z
        - (bM2 h + bBeta h * (br h) ^ 2 / 3) - (bAlpha h - A) * (t * (y * z)) := by
    funext t
    rw [LgenA_eq_entropyF hh A t y z]
    ring_nf
  have h1 := Branch.hasDerivAt_phi₁ (h := h) (θ := θ) hh x y z hx
  have h2 : HasDerivAt (fun t : ℝ => (bAlpha h - A) * (t * (y * z)))
      ((bAlpha h - A) * (y * z)) x := by
    simpa using (((hasDerivAt_id x).mul_const (y * z)).const_mul (bAlpha h - A))
  have h3 := (h1.sub_const (bM2 h + bBeta h * (br h) ^ 2 / 3)).sub h2
  have heq : PhiD1 h θ x y z - (bAlpha h - A) * (y * z) = PhiD1gen A h θ x y z := by
    have := PhiD1_eq_gen (h := h) (θ := θ) (w₁ := x) (w₂ := y) (w₃ := z) A
    rw [this]; ring
  rw [hF, ← heq]
  exact h3

/-- The derivative of `LgenA A` in its second weight. -/
theorem hasDerivAt_LgenA₂ {h θ : ℝ} (hh : 0 < h) (A x y z : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun t => LgenA A h θ x t z) (PhiD1gen A h θ y x z) y := by
  have hswap : (fun t => LgenA A h θ x t z) = fun t => LgenA A h θ t x z := by
    funext t; simp only [LgenA, gapP]; ring
  rw [hswap]
  exact hasDerivAt_LgenA₁ hh A y x z hy

/-- The derivative of `LgenA A` in its third weight. -/
theorem hasDerivAt_LgenA₃ {h θ : ℝ} (hh : 0 < h) (A x y z : ℝ) (hz : z ≠ 0) :
    HasDerivAt (fun t => LgenA A h θ x y t) (PhiD1gen A h θ z x y) z := by
  have hswap : (fun t => LgenA A h θ x y t) = fun t => LgenA A h θ t x y := by
    funext t; simp only [LgenA, gapP]; ring
  rw [hswap]
  exact hasDerivAt_LgenA₁ hh A z x y hz

/-- The centered bound for the gap helper `LgenA A`. -/
theorem LgenA_centered {h θ : ℝ} (hh : 0 < h) (A : ℝ)
    {l₁ u₁ l₂ u₂ l₃ u₃ c₁ c₂ c₃ K₁ K₂ K₃ w₁ w₂ w₃ : ℝ}
    (hp₁ : 0 < l₁) (hp₂ : 0 < l₂) (hp₃ : 0 < l₃)
    (hc₁ : c₁ ∈ Icc l₁ u₁) (hc₂ : c₂ ∈ Icc l₂ u₂) (hc₃ : c₃ ∈ Icc l₃ u₃)
    (hw₁ : w₁ ∈ Icc l₁ u₁) (hw₂ : w₂ ∈ Icc l₂ u₂) (hw₃ : w₃ ∈ Icc l₃ u₃)
    (hK₁ : ∀ x₁ ∈ Icc l₁ u₁, ∀ x₂ ∈ Icc l₂ u₂, ∀ x₃ ∈ Icc l₃ u₃,
      |PhiD1gen A h θ x₁ x₂ x₃| ≤ K₁)
    (hK₂ : ∀ x₁ ∈ Icc l₁ u₁, ∀ x₂ ∈ Icc l₂ u₂, ∀ x₃ ∈ Icc l₃ u₃,
      |PhiD1gen A h θ x₂ x₁ x₃| ≤ K₂)
    (hK₃ : ∀ x₁ ∈ Icc l₁ u₁, ∀ x₂ ∈ Icc l₂ u₂, ∀ x₃ ∈ Icc l₃ u₃,
      |PhiD1gen A h θ x₃ x₁ x₂| ≤ K₃) :
    LgenA A h θ c₁ c₂ c₃ - (K₁ * |w₁ - c₁| + K₂ * |w₂ - c₂| + K₃ * |w₃ - c₃|)
      ≤ LgenA A h θ w₁ w₂ w₃ :=
  centered_bound_gen (F := fun a b c => LgenA A h θ a b c)
    (D := fun a b c => PhiD1gen A h θ a b c)
    (fun x y z hx => hasDerivAt_LgenA₁ hh A x y z hx)
    (fun x y z hy => hasDerivAt_LgenA₂ hh A x y z hy)
    (fun x y z hz => hasDerivAt_LgenA₃ hh A x y z hz)
    hp₁ hp₂ hp₃ hc₁ hc₂ hc₃ hw₁ hw₂ hw₃ hK₁ hK₂ hK₃

/-! ### Dyadic bookkeeping -/

theorem value_le_imax_left (a b : Int) : value a ≤ value (imax a b) := by
  by_cases h : a ≤ b
  · simp only [imax, if_pos h]; exact value_mono h
  · simp only [imax, if_neg h]; exact le_refl _

theorem value_le_imax_right (a b : Int) : value b ≤ value (imax a b) := by
  by_cases h : a ≤ b
  · simp only [imax, if_pos h]; exact le_refl _
  · simp only [imax, if_neg h]; exact value_mono (by omega)

/-- An upper bound for the absolute value of a member of an interval. -/
theorem abs_le_absBound {d : DI} {x : ℝ} (hx : d.Mem x) :
    |x| ≤ value (absBound d) := by
  have h₁ : value d.hi ≤ value (absBound d) := value_le_imax_right _ _
  have h₂ : value (-d.lo) ≤ value (absBound d) := value_le_imax_left _ _
  have h₃ : value (-d.lo) = -value d.lo := by
    simp only [value]; push_cast; ring
  rw [abs_le]
  constructor
  · rw [h₃] at h₂; linarith [hx.1]
  · exact le_trans hx.2 h₁

/-- The distance from a point of a side to a point of the side is bounded by
`radAt`. -/
theorem abs_sub_le_radAt {r : SRec} {c : Int} {w : ℝ}
    (hw : value r.lo ≤ w) (hw' : w ≤ value r.hi) :
    |w - value c| ≤ value (r.radAt c) := by
  have h₁ : value (r.hi - c) ≤ value (r.radAt c) := value_le_imax_left _ _
  have h₂ : value (c - r.lo) ≤ value (r.radAt c) := value_le_imax_right _ _
  have e₁ : value (r.hi - c) = value r.hi - value c := by
    simp only [value]; push_cast; ring
  have e₂ : value (c - r.lo) = value c - value r.lo := by
    simp only [value]; push_cast; ring
  rw [e₁] at h₁; rw [e₂] at h₂
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Turning the integer acceptance inequality into the real one. -/
theorem sum_prod_value_le {a₁ b₁ a₂ b₂ a₃ b₃ c : Int}
    (h : a₁ * b₁ + a₂ * b₂ + a₃ * b₃ ≤ c * scale) :
    value a₁ * value b₁ + value a₂ * value b₂ + value a₃ * value b₃ ≤ value c := by
  have hs := scale_pos_real
  have hR : ((a₁ * b₁ + a₂ * b₂ + a₃ * b₃ : Int) : ℝ) ≤ ((c * scale : Int) : ℝ) := by
    exact_mod_cast h
  have e₁ : value a₁ * value b₁ + value a₂ * value b₂ + value a₃ * value b₃
      = ((a₁ * b₁ + a₂ * b₂ + a₃ * b₃ : Int) : ℝ) / ((scale : ℝ) * (scale : ℝ)) := by
    simp only [value]; push_cast; ring
  have e₂ : value c = ((c * scale : Int) : ℝ) / ((scale : ℝ) * (scale : ℝ)) := by
    simp only [value]; push_cast
    field_simp
  rw [e₁, e₂]
  gcongr

/-! ### The centered leaf rule on materialised records -/

/-- What the kernel check `centOk` gives about the helper `LgenA A`: at every
weight of the box, the helper is nonnegative. -/
theorem centOk_nonneg {r₁ r₂ r₃ m₁ m₂ m₃ : SRec} {IA ID6 IB3 : DI}
    {A h θ w₁ w₂ w₃ : ℝ} (hh : 0 < h)
    (g₁ : r₁.Good h θ) (g₂ : r₂.Good h θ) (g₃ : r₃.Good h θ)
    (n₁ : m₁.Good h θ) (n₂ : m₂.Good h θ) (n₃ : m₃.Good h θ)
    (hA : IA.Mem A) (hD6 : ID6.Mem (bDelta h * (1 / 6)))
    (hB3 : IB3.Mem (bBeta h * (1 / 3)))
    (hok : centOk r₁ r₂ r₃ m₁ m₂ m₃ IA ID6 IB3 = true)
    (hw₁ : value r₁.lo ≤ w₁) (hw₁' : w₁ ≤ value r₁.hi)
    (hw₂ : value r₂.lo ≤ w₂) (hw₂' : w₂ ≤ value r₂.hi)
    (hw₃ : value r₃.lo ≤ w₃) (hw₃' : w₃ ≤ value r₃.hi) :
    0 ≤ LgenA A h θ w₁ w₂ w₃ := by
  simp only [centOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨hok, hgap⟩ := hok
  obtain ⟨hok, q₃⟩ := hok
  obtain ⟨hok, q₂⟩ := hok
  obtain ⟨hok, q₁⟩ := hok
  obtain ⟨hok, c₃u⟩ := hok
  obtain ⟨hok, c₃l⟩ := hok
  obtain ⟨hok, c₂u⟩ := hok
  obtain ⟨hok, c₂l⟩ := hok
  obtain ⟨hok, c₁u⟩ := hok
  obtain ⟨hok, c₁l⟩ := hok
  obtain ⟨hok, t₃⟩ := hok
  obtain ⟨t₁, t₂⟩ := hok
  set c₁ : ℝ := value m₁.lo
  set c₂ : ℝ := value m₂.lo
  set c₃ : ℝ := value m₃.lo
  have hm₁ : value m₁.lo ≤ c₁ ∧ c₁ ≤ value m₁.hi := by
    rw [← t₁]; exact ⟨le_refl _, le_refl _⟩
  have hm₂ : value m₂.lo ≤ c₂ ∧ c₂ ≤ value m₂.hi := by
    rw [← t₂]; exact ⟨le_refl _, le_refl _⟩
  have hm₃ : value m₃.lo ≤ c₃ ∧ c₃ ≤ value m₃.hi := by
    rw [← t₃]; exact ⟨le_refl _, le_refl _⟩
  have hc₁mem : c₁ ∈ Icc (value r₁.lo) (value r₁.hi) := ⟨value_mono c₁l, value_mono c₁u⟩
  have hc₂mem : c₂ ∈ Icc (value r₂.lo) (value r₂.hi) := ⟨value_mono c₂l, value_mono c₂u⟩
  have hc₃mem : c₃ ∈ Icc (value r₃.lo) (value r₃.hi) := ⟨value_mono c₃l, value_mono c₃u⟩
  have hr₁hi : 0 < r₁.hi := lt_of_lt_of_le q₁ (le_trans c₁l c₁u)
  have hr₂hi : 0 < r₂.hi := lt_of_lt_of_le q₂ (le_trans c₂l c₂u)
  have hr₃hi : 0 < r₃.hi := lt_of_lt_of_le q₃ (le_trans c₃l c₃u)
  have hK₁ : ∀ x₁ ∈ Icc (value r₁.lo) (value r₁.hi),
      ∀ x₂ ∈ Icc (value r₂.lo) (value r₂.hi),
      ∀ x₃ ∈ Icc (value r₃.lo) (value r₃.hi),
      |PhiD1gen A h θ x₁ x₂ x₃| ≤ value (absBound (derivS r₁ r₂ r₃ IA)) := by
    intro x₁ hx₁ x₂ hx₂ x₃ hx₃
    exact abs_le_absBound
      (mem_derivS_gen g₁ g₂ g₃ q₁ hr₁hi hA hx₁.1 hx₁.2 hx₂.1 hx₂.2 hx₃.1 hx₃.2)
  have hK₂ : ∀ x₁ ∈ Icc (value r₁.lo) (value r₁.hi),
      ∀ x₂ ∈ Icc (value r₂.lo) (value r₂.hi),
      ∀ x₃ ∈ Icc (value r₃.lo) (value r₃.hi),
      |PhiD1gen A h θ x₂ x₁ x₃| ≤ value (absBound (derivS r₂ r₁ r₃ IA)) := by
    intro x₁ hx₁ x₂ hx₂ x₃ hx₃
    exact abs_le_absBound
      (mem_derivS_gen g₂ g₁ g₃ q₂ hr₂hi hA hx₂.1 hx₂.2 hx₁.1 hx₁.2 hx₃.1 hx₃.2)
  have hK₃ : ∀ x₁ ∈ Icc (value r₁.lo) (value r₁.hi),
      ∀ x₂ ∈ Icc (value r₂.lo) (value r₂.hi),
      ∀ x₃ ∈ Icc (value r₃.lo) (value r₃.hi),
      |PhiD1gen A h θ x₃ x₁ x₂| ≤ value (absBound (derivS r₃ r₁ r₂ IA)) := by
    intro x₁ hx₁ x₂ hx₂ x₃ hx₃
    exact abs_le_absBound
      (mem_derivS_gen g₃ g₁ g₂ q₃ hr₃hi hA hx₃.1 hx₃.2 hx₁.1 hx₁.2 hx₂.1 hx₂.2)
  have hcent := LgenA_centered (h := h) (θ := θ) hh A
    (value_pos q₁) (value_pos q₂) (value_pos q₃)
    hc₁mem hc₂mem hc₃mem ⟨hw₁, hw₁'⟩ ⟨hw₂, hw₂'⟩ ⟨hw₃, hw₃'⟩ hK₁ hK₂ hK₃
  have hval : value (leafS m₁ m₂ m₃ IA ID6 IB3).lo ≤ LgenA A h θ c₁ c₂ c₃ :=
    (mem_leafS_gen n₁ n₂ n₃ hA hD6 hB3 hm₁.1 hm₁.2 hm₂.1 hm₂.2 hm₃.1 hm₃.2).1
  have hd₁ : |w₁ - c₁| ≤ value (r₁.radAt m₁.lo) := abs_sub_le_radAt hw₁ hw₁'
  have hd₂ : |w₂ - c₂| ≤ value (r₂.radAt m₂.lo) := abs_sub_le_radAt hw₂ hw₂'
  have hd₃ : |w₃ - c₃| ≤ value (r₃.radAt m₃.lo) := abs_sub_le_radAt hw₃ hw₃'
  have hKnn₁ : (0:ℝ) ≤ value (absBound (derivS r₁ r₂ r₃ IA)) :=
    le_trans (abs_nonneg _) (hK₁ c₁ hc₁mem c₂ hc₂mem c₃ hc₃mem)
  have hKnn₂ : (0:ℝ) ≤ value (absBound (derivS r₂ r₁ r₃ IA)) :=
    le_trans (abs_nonneg _) (hK₂ c₁ hc₁mem c₂ hc₂mem c₃ hc₃mem)
  have hKnn₃ : (0:ℝ) ≤ value (absBound (derivS r₃ r₁ r₂ IA)) :=
    le_trans (abs_nonneg _) (hK₃ c₁ hc₁mem c₂ hc₂mem c₃ hc₃mem)
  have hsum := sum_prod_value_le hgap
  have hb₁ := mul_le_mul_of_nonneg_left hd₁ hKnn₁
  have hb₂ := mul_le_mul_of_nonneg_left hd₂ hKnn₂
  have hb₃ := mul_le_mul_of_nonneg_left hd₃ hKnn₃
  linarith

/-- The centered leaf rule on a finite slab: if the kernel accepts `centOk`,
every weight in the box has `Φ ≥ M₂`. -/
theorem leafS_centered_rule {r₁ r₂ r₃ m₁ m₂ m₃ : SRec} {IA ID6 IB3 : DI}
    {h θ w₁ w₂ w₃ : ℝ} (hh : (9:ℝ) ≤ h)
    (g₁ : r₁.Good h θ) (g₂ : r₂.Good h θ) (g₃ : r₃.Good h θ)
    (n₁ : m₁.Good h θ) (n₂ : m₂.Good h θ) (n₃ : m₃.Good h θ)
    (hA : IA.Mem (bAlpha h)) (hD6 : ID6.Mem (bDelta h * (1 / 6)))
    (hB3 : IB3.Mem (bBeta h * (1 / 3)))
    (hok : centOk r₁ r₂ r₃ m₁ m₂ m₃ IA ID6 IB3 = true)
    (hw₁ : value r₁.lo ≤ w₁) (hw₁' : w₁ ≤ value r₁.hi)
    (hw₂ : value r₂.lo ≤ w₂) (hw₂' : w₂ ≤ value r₂.hi)
    (hw₃ : value r₃.lo ≤ w₃) (hw₃' : w₃ ≤ value r₃.hi) :
    bM2 h ≤ entropyF (bAlpha h) (bG h θ) w₁ w₂ w₃ := by
  have hhpos : (0:ℝ) < h := by linarith
  have h0 := centOk_nonneg hhpos g₁ g₂ g₃ n₁ n₂ n₃ hA hD6 hB3 hok
    hw₁ hw₁' hw₂ hw₂' hw₃ hw₃'
  have heq : LgenA (bAlpha h) h θ w₁ w₂ w₃ = Lalpha h θ w₁ w₂ w₃ := by
    simp only [LgenA, Lalpha]
  rw [heq] at h0
  have h2 := Lalpha_le_gap (h := h) (θ := θ) hh w₁ w₂ w₃
  linarith

end Itv
end TriangleNumerical


/-!
# The finite spatial cover as a kernel-checkable tree

Section 10 of the blueprint.  A subdivision of the unit cube is represented by
the inductive type `STree`: a node either splits a coordinate at an exact
dyadic cut point, or is a leaf carrying the name of one of the *proved*
acceptance rules

* `empty`  — the ordered domain misses the box;
* `small`  — the box lies in `[0,1/10]³`, so the analytic lemma (A1) applies;
* `mixed`  — the box lies in `[0,1/10] × [19/20,1]²`, lemma (A2);
* `value`  — a certified nonnegative dyadic lower bound for the gap helper `Lα`;
* `desc`/`asc` — a certified sign for one spatial partial derivative;
* `cvalue` — the centered (mean-value) value rule of `Centered.lean`.

The Boolean function `chkS` recomputes every box from the root and the cut
points, so the data cannot change the domain, and checks the arithmetic
condition of the claimed rule against the *materialised side records* of the
slab (`SideRec.lean`), whose validity has been established once and for all by
the kernel from the endpoint logarithm certificates.  `chkS_sound` turns
acceptance into the checker invariant `Cover.Excludes`, hence (through
`Cover.le_of_excludes_root`) into a global lower bound for `Φ` on the cube.

Every box used by a leaf rule is first *tightened* using the ordering
`w₁ ≤ w₂ ≤ w₃`, which is available because `Cover.Excludes` only quantifies
over ordered triples.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Itv

open TriangleLogCertificate Branch

/-! ### Dyadic boxes -/

theorem le_value_imin {x : ℝ} {a b : Int} (ha : x ≤ value a) (hb : x ≤ value b) :
    x ≤ value (imin a b) := by
  simp only [imin]; split <;> assumption

theorem value_imax_le {x : ℝ} {a b : Int} (ha : value a ≤ x) (hb : value b ≤ x) :
    value (imax a b) ≤ x := by
  simp only [imax]; split <;> assumption

/-- The real box denoted by a dyadic box. -/
noncomputable def DBox.toBox (b : DBox) : Cover.Box :=
  ⟨value b.l₁, value b.u₁, value b.l₂, value b.u₂, value b.l₃, value b.u₃⟩

theorem mem_tighten {b : DBox} {w₁ w₂ w₃ : ℝ} (h₁₂ : w₁ ≤ w₂) (h₂₃ : w₂ ≤ w₃)
    (hm : b.toBox.mem w₁ w₂ w₃) : b.tighten.toBox.mem w₁ w₂ w₃ := by
  simp only [DBox.toBox, DBox.tighten, Cover.Box.mem] at hm ⊢
  obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, ⟨hc1, hc2⟩⟩ := hm
  refine ⟨⟨ha1, ?_⟩, ⟨?_, ?_⟩, ⟨?_, hc2⟩⟩
  · exact le_value_imin ha2 (le_value_imin (le_trans h₁₂ hb2) (le_trans (le_trans h₁₂ h₂₃) hc2))
  · exact value_imax_le (le_trans ha1 h₁₂) hb1
  · exact le_value_imin hb2 (le_trans h₂₃ hc2)
  · exact value_imax_le (value_imax_le (le_trans ha1 (le_trans h₁₂ h₂₃))
      (le_trans hb1 h₂₃)) hc1

theorem cover_split (b : DBox) (axis : Nat) (c : Int) (w₁ w₂ w₃ : ℝ)
    (hm : b.toBox.mem w₁ w₂ w₃) :
    (b.setHi axis c).toBox.mem w₁ w₂ w₃ ∨ (b.setLo axis c).toBox.mem w₁ w₂ w₃ := by
  obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, ⟨hc1, hc2⟩⟩ := hm
  match axis with
  | 0 =>
      rcases le_total w₁ (value c) with h | h
      · exact Or.inl ⟨⟨ha1, h⟩, ⟨hb1, hb2⟩, ⟨hc1, hc2⟩⟩
      · exact Or.inr ⟨⟨h, ha2⟩, ⟨hb1, hb2⟩, ⟨hc1, hc2⟩⟩
  | 1 =>
      rcases le_total w₂ (value c) with h | h
      · exact Or.inl ⟨⟨ha1, ha2⟩, ⟨hb1, h⟩, ⟨hc1, hc2⟩⟩
      · exact Or.inr ⟨⟨ha1, ha2⟩, ⟨h, hb2⟩, ⟨hc1, hc2⟩⟩
  | (n+2) =>
      rcases le_total w₃ (value c) with h | h
      · exact Or.inl ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, ⟨hc1, h⟩⟩
      · exact Or.inr ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, ⟨h, hc2⟩⟩

/-- Assembling two child boxes of an explicit cut. -/
theorem excludes_split_of {Φ : ℝ → ℝ → ℝ → ℝ} {M : ℝ} (b l r : DBox) (axis : Nat)
    (cut : Int) (hs : l = b.setHi axis cut ∧ r = b.setLo axis cut)
    (hl : Cover.Excludes Φ M l.toBox) (hr : Cover.Excludes Φ M r.toBox) :
    Cover.Excludes Φ M b.toBox := by
  obtain ⟨rfl, rfl⟩ := hs
  exact Cover.Excludes.split (fun w₁ w₂ w₃ hm => cover_split b axis cut w₁ w₂ w₃ hm) hl hr

theorem excludes_tighten {Φ : ℝ → ℝ → ℝ → ℝ} {M : ℝ} {b : DBox}
    (h : Cover.Excludes Φ M b.tighten.toBox) : Cover.Excludes Φ M b.toBox := by
  intro w₁ w₂ w₃ h₁₂ h₂₃ hmem
  exact h w₁ w₂ w₃ h₁₂ h₂₃ (mem_tighten h₁₂ h₂₃ hmem)

/-! ### Rational comparisons of dyadic endpoints -/

theorem value_lt_of_lt {a b : Int} (h : a < b) : value a < value b := by
  have hs := scale_pos_real
  have hab : (a : ℝ) < (b : ℝ) := by exact_mod_cast h
  simp only [value]
  gcongr

theorem value_le_tenth {a : Int} (h : 10 * a ≤ scale) : value a ≤ 1 / 10 := by
  have h' : a * (10 : Int) ≤ (1 : Int) * scale := by omega
  have := value_le_rat (p := 1) (q := 10) (n := a) (by norm_num) h'
  norm_num at this
  exact this

theorem high_le_value {a : Int} (h : 19 * scale ≤ 20 * a) : (19 : ℝ) / 20 ≤ value a := by
  have h' : (19 : Int) * scale ≤ a * (20 : Int) := by omega
  have := rat_le_value (p := 19) (q := 20) (n := a) (by norm_num) h'
  norm_num at this
  exact this

theorem mem_zeroI : (DI.mk 0 0).Mem 0 := by
  constructor <;> simp [value_zero]

theorem nine_le_value {n : Int} (h : 9 * scale ≤ n) : (9:ℝ) ≤ value n := by
  have h' : (9 : Int) * scale ≤ n * (1 : Int) := by omega
  have := rat_le_value (p := 9) (q := 1) (n := n) (by norm_num) h'
  norm_num at this
  exact this

/-! ### The soundness theorem -/

theorem chkS_sound {tbl : RTree} {h θ M : ℝ} (htbl : ∀ k : Nat, (tbl.getS k).Good h θ)
    (hh : (9:ℝ) ≤ h) (hθ1 : -(1/50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hM : M ≤ bM2 h)
    {IA ID6 IB3 : DI} (hA : IA.Mem (bAlpha h)) (hD6 : ID6.Mem (bDelta h * (1/6)))
    (hB3 : IB3.Mem (bBeta h * (1/3))) :
    ∀ (t : STree) (b : DBox), chkS tbl IA ID6 IB3 t b = true →
      Cover.Excludes (entropyF (bAlpha h) (bG h θ)) M b.toBox := by
  have hhpos : (0:ℝ) < h := by linarith
  intro t
  induction t with
  | split axis cut l r ihl ihr =>
      intro b hb
      simp only [chkS, Bool.and_eq_true] at hb
      exact Cover.Excludes.split (fun w₁ w₂ w₃ hm => cover_split b axis cut w₁ w₂ w₃ hm)
        (ihl _ hb.1.2) (ihr _ hb.2)
  | empty =>
      intro b hb
      simp only [chkS, Bool.or_eq_true, decide_eq_true_eq] at hb
      refine Cover.excludes_empty_ordered ?_
      rcases hb with hb | hb
      · exact Or.inl (value_lt_of_lt hb)
      · exact Or.inr (value_lt_of_lt hb)
  | small =>
      intro b hb
      simp only [chkS, Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hb
      refine excludes_tighten (Cover.excludes_of_bound ?_)
      rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩ - - -
      refine le_trans hM (local_small_region hh hθ1 hθ0 ?_ ?_ ?_ ?_ ?_ ?_)
      · exact le_trans (value_nonneg h1) k1
      · exact le_trans k2 (value_le_tenth h2)
      · exact le_trans (value_nonneg h5) k3
      · exact le_trans k4 (value_le_tenth h3)
      · exact le_trans (value_nonneg h6) k5
      · exact le_trans k6 (value_le_tenth h4)
  | mixed =>
      intro b hb
      simp only [chkS, Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hb
      refine excludes_tighten (Cover.excludes_of_bound ?_)
      rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩ - - -
      refine le_trans hM (local_large_region hh hθ1 hθ0 ?_ ?_ ?_ ?_ ?_ ?_)
      · exact le_trans (value_nonneg h1) k1
      · exact le_trans k2 (value_le_tenth h2)
      · exact le_trans (high_le_value h3) k3
      · exact le_trans k4 (value_le_one h4)
      · exact le_trans (high_le_value h5) k5
      · exact le_trans k6 (value_le_one h6)
  | value p₁ p₂ p₃ =>
      intro b hb
      simp only [chkS, sideOkS, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
      obtain ⟨⟨⟨⟨⟨⟨e1, e2⟩, -⟩, -⟩, ⟨⟨⟨f1, f2⟩, -⟩, -⟩⟩, ⟨⟨⟨g1, g2⟩, -⟩, -⟩⟩, hgap⟩ := hb
      refine excludes_tighten (Cover.excludes_of_bound ?_)
      rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩ - - -
      refine le_trans hM (leafS_value_rule hh (htbl p₁) (htbl p₂)
        (htbl p₃) hA hD6 hB3 hgap ?_ ?_ ?_ ?_ ?_ ?_)
      · rw [e1]; exact k1
      · rw [e2]; exact k2
      · rw [f1]; exact k3
      · rw [f2]; exact k4
      · rw [g1]; exact k5
      · rw [g2]; exact k6
  | desc k p₁ p₂ p₃ =>
      intro b hb
      match k with
      | 0 =>
          simp only [chkS, sideOkS, DBox.coordLo, DBox.coordHi, Bool.and_eq_true,
            decide_eq_true_eq, beq_iff_eq] at hb
          obtain ⟨⟨⟨⟨⟨-, ⟨⟨⟨e1, e2⟩, -⟩, -⟩⟩, ⟨⟨⟨f1, f2⟩, -⟩, -⟩,
            ⟨⟨⟨g1, g2⟩, -⟩, -⟩⟩, p1⟩, p2⟩, hsign⟩ := hb
          refine excludes_tighten (Branch.excludes_descent (h := h) (θ := θ) hhpos M ?_ ?_)
          · exact value_pos p1
          · rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩
            exact derivS_pos_rule (htbl p₁) (htbl p₂)
              (htbl p₃) (by rw [e1]; exact p1) (by rw [e2]; exact p2) hA hsign
              (by rw [e1]; exact k1) (by rw [e2]; exact k2)
              (by rw [f1]; exact k3) (by rw [f2]; exact k4)
              (by rw [g1]; exact k5) (by rw [g2]; exact k6)
      | 1 =>
          simp only [chkS, sideOkS, DBox.coordLo, DBox.coordHi, Bool.and_eq_true,
            decide_eq_true_eq, beq_iff_eq] at hb
          obtain ⟨⟨⟨⟨⟨-, ⟨⟨⟨e1, e2⟩, -⟩, -⟩⟩, ⟨⟨⟨f1, f2⟩, -⟩, -⟩,
            ⟨⟨⟨g1, g2⟩, -⟩, -⟩⟩, p1⟩, p2⟩, hsign⟩ := hb
          refine excludes_tighten (Branch.excludes_descent₂ (h := h) (θ := θ) hhpos M ?_ ?_)
          · exact value_pos p1
          · rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩
            exact derivS_pos_rule (htbl p₁) (htbl p₂)
              (htbl p₃) (by rw [e1]; exact p1) (by rw [e2]; exact p2) hA hsign
              (by rw [e1]; exact k3) (by rw [e2]; exact k4)
              (by rw [f1]; exact k1) (by rw [f2]; exact k2)
              (by rw [g1]; exact k5) (by rw [g2]; exact k6)
      | 2 =>
          simp only [chkS, sideOkS, DBox.coordLo, DBox.coordHi, Bool.and_eq_true,
            decide_eq_true_eq, beq_iff_eq] at hb
          obtain ⟨⟨⟨⟨⟨-, ⟨⟨⟨e1, e2⟩, -⟩, -⟩⟩, ⟨⟨⟨f1, f2⟩, -⟩, -⟩,
            ⟨⟨⟨g1, g2⟩, -⟩, -⟩⟩, p1⟩, p2⟩, hsign⟩ := hb
          refine excludes_tighten (Branch.excludes_descent₃ (h := h) (θ := θ) hhpos M ?_ ?_)
          · exact value_pos p1
          · rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩
            exact derivS_pos_rule (htbl p₁) (htbl p₂)
              (htbl p₃) (by rw [e1]; exact p1) (by rw [e2]; exact p2) hA hsign
              (by rw [e1]; exact k5) (by rw [e2]; exact k6)
              (by rw [f1]; exact k1) (by rw [f2]; exact k2)
              (by rw [g1]; exact k3) (by rw [g2]; exact k4)
      | (n+3) =>
          simp only [chkS, Bool.and_eq_true, decide_eq_true_eq] at hb
          omega
  | asc k p₁ p₂ p₃ =>
      intro b hb
      match k with
      | 0 =>
          simp only [chkS, sideOkS, DBox.coordLo, DBox.coordHi, Bool.and_eq_true,
            decide_eq_true_eq, beq_iff_eq] at hb
          obtain ⟨⟨⟨⟨⟨⟨-, ⟨⟨⟨e1, e2⟩, -⟩, -⟩⟩, ⟨⟨⟨f1, f2⟩, -⟩, -⟩,
            ⟨⟨⟨g1, g2⟩, -⟩, -⟩⟩, p1⟩, p2⟩, p3⟩, hsign⟩ := hb
          refine excludes_tighten (Branch.excludes_ascent (h := h) (θ := θ) hhpos M ?_ ?_ ?_)
          · exact value_pos p1
          · have := value_lt_of_lt p3
            rwa [value_one] at this
          · rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩
            exact derivS_neg_rule (htbl p₁) (htbl p₂)
              (htbl p₃) (by rw [e1]; exact p1) (by rw [e2]; exact p2) hA hsign
              (by rw [e1]; exact k1) (by rw [e2]; exact k2)
              (by rw [f1]; exact k3) (by rw [f2]; exact k4)
              (by rw [g1]; exact k5) (by rw [g2]; exact k6)
      | 1 =>
          simp only [chkS, sideOkS, DBox.coordLo, DBox.coordHi, Bool.and_eq_true,
            decide_eq_true_eq, beq_iff_eq] at hb
          obtain ⟨⟨⟨⟨⟨⟨-, ⟨⟨⟨e1, e2⟩, -⟩, -⟩⟩, ⟨⟨⟨f1, f2⟩, -⟩, -⟩,
            ⟨⟨⟨g1, g2⟩, -⟩, -⟩⟩, p1⟩, p2⟩, p3⟩, hsign⟩ := hb
          refine excludes_tighten (Branch.excludes_ascent₂ (h := h) (θ := θ) hhpos M ?_ ?_ ?_)
          · exact value_pos p1
          · have := value_lt_of_lt p3
            rwa [value_one] at this
          · rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩
            exact derivS_neg_rule (htbl p₁) (htbl p₂)
              (htbl p₃) (by rw [e1]; exact p1) (by rw [e2]; exact p2) hA hsign
              (by rw [e1]; exact k3) (by rw [e2]; exact k4)
              (by rw [f1]; exact k1) (by rw [f2]; exact k2)
              (by rw [g1]; exact k5) (by rw [g2]; exact k6)
      | 2 =>
          simp only [chkS, sideOkS, DBox.coordLo, DBox.coordHi, Bool.and_eq_true,
            decide_eq_true_eq, beq_iff_eq] at hb
          obtain ⟨⟨⟨⟨⟨⟨-, ⟨⟨⟨e1, e2⟩, -⟩, -⟩⟩, ⟨⟨⟨f1, f2⟩, -⟩, -⟩,
            ⟨⟨⟨g1, g2⟩, -⟩, -⟩⟩, p1⟩, p2⟩, p3⟩, hsign⟩ := hb
          refine excludes_tighten (Branch.excludes_ascent₃ (h := h) (θ := θ) hhpos M ?_ ?_ ?_)
          · exact value_pos p1
          · have := value_lt_of_lt p3
            rwa [value_one] at this
          · rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩
            exact derivS_neg_rule (htbl p₁) (htbl p₂)
              (htbl p₃) (by rw [e1]; exact p1) (by rw [e2]; exact p2) hA hsign
              (by rw [e1]; exact k5) (by rw [e2]; exact k6)
              (by rw [f1]; exact k1) (by rw [f2]; exact k2)
              (by rw [g1]; exact k3) (by rw [g2]; exact k4)
      | (n+3) =>
          simp only [chkS, Bool.and_eq_true, decide_eq_true_eq] at hb
          omega

  | cvalue p₁ p₂ p₃ q₁ q₂ q₃ =>
      intro b hb
      simp only [chkS, sideOkS, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
      obtain ⟨hb, hcent⟩ := hb
      obtain ⟨hb, hg⟩ := hb
      obtain ⟨he, hf⟩ := hb
      obtain ⟨⟨⟨e1, e2⟩, -⟩, -⟩ := he
      obtain ⟨⟨⟨f1, f2⟩, -⟩, -⟩ := hf
      obtain ⟨⟨⟨g1, g2⟩, -⟩, -⟩ := hg
      refine excludes_tighten (Cover.excludes_of_bound ?_)
      rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩ - - -
      refine le_trans hM (leafS_centered_rule hh (htbl p₁) (htbl p₂) (htbl p₃)
        (htbl q₁) (htbl q₂) (htbl q₃) hA hD6 hB3 hcent ?_ ?_ ?_ ?_ ?_ ?_)
      · rw [e1]; exact k1
      · rw [e2]; exact k2
      · rw [f1]; exact k3
      · rw [f2]; exact k4
      · rw [g1]; exact k5
      · rw [g2]; exact k6

/-! ### From an exhausted tree to the cube bound -/

theorem rootBox_toBox : rootBox.toBox = ⟨0, 1, 0, 1, 0, 1⟩ := by
  simp [rootBox, DBox.toBox, value_one, value_zero]

theorem cube_bound_of_excludes {h θ M : ℝ}
    (hex : Cover.Excludes (entropyF (bAlpha h) (bG h θ)) M rootBox.toBox) :
    ∀ a ∈ unitInterval, ∀ b ∈ unitInterval, ∀ c ∈ unitInterval,
      M ≤ entropyF (bAlpha h) (bG h θ) a b c := by
  rw [rootBox_toBox] at hex
  exact Branch.entropyF_ge_of_excludes M hex

end Itv
end TriangleNumerical
