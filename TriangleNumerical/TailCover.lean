import TriangleNumerical.CoverTree
import TriangleNumerical.TailEval
import TriangleNumerical.TailData
import TriangleNumerical.TailChunk0

/- ### From `TailTree` -/

/-!
# The tail cover `h ≥ 15`

The same subdivision trees as in `CoverTree.lean`, and the same materialised
side records, but checked with the tail rules of §11:

* `value` — a nonnegative dyadic lower bound for the helper `L₁₀`, which is at
  most the actual gap because `α ≥ 10`;
* `desc`  — a positive lower bound for `∂ᵢL₁₀ ≤ ∂ᵢΦ`;
* `asc`   — the **conditional** tail-descent rule (T2): the bound
  `∂ᵢΦ ≤ upper(∂ᵢ𝓑) + (−lowerB)/lᵢ`, valid at a point whose value lies below
  `M₂`, is negative.

`empty`, `small` and `mixed` are as before; the analytic local lemmas hold for
every `h ≥ 9`, hence on the tail.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Itv

open TriangleLogCertificate Branch

section Leaves

variable {h : ℝ} {ID6 IB3 : DI} {r₁ r₂ r₃ : SRec} {w₁ w₂ w₃ : ℝ}

theorem mem_tenI : (intI 10).Mem (10:ℝ) := by
  have := mem_intI 10
  norm_num at this
  exact this

/-- The `value` leaf of the tail cover. -/
theorem tail_value_rule (hh : (15:ℝ) ≤ h)
    (g₁ : r₁.Good h 0) (g₂ : r₂.Good h 0) (g₃ : r₃.Good h 0)
    (hD6 : ID6.Mem (bDelta h * (1/6))) (hB3 : IB3.Mem (bBeta h * (1/3)))
    (hgap : 0 ≤ (leafS r₁ r₂ r₃ (intI 10) ID6 IB3).lo)
    (hw₁ : value r₁.lo ≤ w₁) (hw₁' : w₁ ≤ value r₁.hi)
    (hw₂ : value r₂.lo ≤ w₂) (hw₂' : w₂ ≤ value r₂.hi)
    (hw₃ : value r₃.lo ≤ w₃) (hw₃' : w₃ ≤ value r₃.hi) :
    bM2 h ≤ entropyF (bAlpha h) (bG h 0) w₁ w₂ w₃ := by
  have hm := mem_leafS_gen g₁ g₂ g₃ mem_tenI hD6 hB3 hw₁ hw₁' hw₂ hw₂' hw₃ hw₃'
  have h1 : 0 ≤ LgenA 10 h 0 w₁ w₂ w₃ := le_trans (nonneg_value_of_nonneg hgap) hm.1
  have h2 := L10_le_gap (h := h) (θ := 0) hh
    (le_trans (value_nonneg g₁.lo_nonneg) hw₁)
    (le_trans (value_nonneg g₂.lo_nonneg) hw₂)
    (le_trans (value_nonneg g₃.lo_nonneg) hw₃)
  linarith

/-- The centered leaf of the tail cover: the mean-value rule applied to the
tail helper `L₁₀`, whose derivatives involve no unbounded parameter. -/
theorem tail_centered_rule {m₁ m₂ m₃ : SRec} (hh : (15:ℝ) ≤ h)
    (g₁ : r₁.Good h 0) (g₂ : r₂.Good h 0) (g₃ : r₃.Good h 0)
    (n₁ : m₁.Good h 0) (n₂ : m₂.Good h 0) (n₃ : m₃.Good h 0)
    (hD6 : ID6.Mem (bDelta h * (1/6))) (hB3 : IB3.Mem (bBeta h * (1/3)))
    (hok : centOk r₁ r₂ r₃ m₁ m₂ m₃ (intI 10) ID6 IB3 = true)
    (hw₁ : value r₁.lo ≤ w₁) (hw₁' : w₁ ≤ value r₁.hi)
    (hw₂ : value r₂.lo ≤ w₂) (hw₂' : w₂ ≤ value r₂.hi)
    (hw₃ : value r₃.lo ≤ w₃) (hw₃' : w₃ ≤ value r₃.hi) :
    bM2 h ≤ entropyF (bAlpha h) (bG h 0) w₁ w₂ w₃ := by
  have hhpos : (0:ℝ) < h := by linarith
  have h1 := centOk_nonneg hhpos g₁ g₂ g₃ n₁ n₂ n₃ mem_tenI hD6 hB3 hok
    hw₁ hw₁' hw₂ hw₂' hw₃ hw₃'
  have h2 := L10_le_gap (h := h) (θ := 0) hh
    (le_trans (value_nonneg g₁.lo_nonneg) hw₁)
    (le_trans (value_nonneg g₂.lo_nonneg) hw₂)
    (le_trans (value_nonneg g₃.lo_nonneg) hw₃)
  linarith

/-- The `desc` leaf of the tail cover. -/
theorem tail_desc_rule (hh : (15:ℝ) ≤ h)
    (g₁ : r₁.Good h 0) (g₂ : r₂.Good h 0) (g₃ : r₃.Good h 0)
    (hpos : 0 < r₁.lo) (hpos' : 0 < r₁.hi)
    (hsign : 0 < (derivS r₁ r₂ r₃ (intI 10)).lo)
    (hw₁ : value r₁.lo ≤ w₁) (hw₁' : w₁ ≤ value r₁.hi)
    (hw₂ : value r₂.lo ≤ w₂) (hw₂' : w₂ ≤ value r₂.hi)
    (hw₃ : value r₃.lo ≤ w₃) (hw₃' : w₃ ≤ value r₃.hi) :
    0 < PhiD1 h 0 w₁ w₂ w₃ := by
  have hm := mem_derivS_gen g₁ g₂ g₃ hpos hpos' mem_tenI hw₁ hw₁' hw₂ hw₂' hw₃ hw₃'
  have h1 : 0 < PhiD1gen 10 h 0 w₁ w₂ w₃ := pos_of_mem hm hsign
  have h2 := PhiD1_ge_ten (h := h) (θ := 0) (w₁ := w₁) hh
    (le_trans (value_nonneg g₂.lo_nonneg) hw₂)
    (le_trans (value_nonneg g₃.lo_nonneg) hw₃)
  linarith

/-- The conditional `asc` leaf of the tail cover (rule T2). -/
theorem tail_asc_rule (hh : (15:ℝ) ≤ h)
    (g₁ : r₁.Good h 0) (g₂ : r₂.Good h 0) (g₃ : r₃.Good h 0)
    (hpos : 0 < r₁.lo) (hpos' : 0 < r₁.hi)
    (hD6 : ID6.Mem (bDelta h * (1/6))) (hB3 : IB3.Mem (bBeta h * (1/3)))
    (hcond : (derivS r₁ r₂ r₃ ⟨0, 0⟩).hi * r₁.lo
      < (leafS r₁ r₂ r₃ ⟨0, 0⟩ ID6 IB3).lo * scale)
    (hbad : entropyF (bAlpha h) (bG h 0) w₁ w₂ w₃ < bM2 h)
    (hw₁ : value r₁.lo ≤ w₁) (hw₁' : w₁ ≤ value r₁.hi)
    (hw₂ : value r₂.lo ≤ w₂) (hw₂' : w₂ ≤ value r₂.hi)
    (hw₃ : value r₃.lo ≤ w₃) (hw₃' : w₃ ≤ value r₃.hi) :
    PhiD1 h 0 w₁ w₂ w₃ < 0 := by
  have hbase := mem_leafS_gen (A := 0) g₁ g₂ g₃ mem_zeroI hD6 hB3
    hw₁ hw₁' hw₂ hw₂' hw₃ hw₃'
  have hderiv := mem_derivS_gen (A := 0) g₁ g₂ g₃ hpos hpos' mem_zeroI
    hw₁ hw₁' hw₂ hw₂' hw₃ hw₃'
  set base := leafS r₁ r₂ r₃ ⟨0, 0⟩ ID6 IB3 with hbdef
  set dI := derivS r₁ r₂ r₃ ⟨0, 0⟩ with hddef
  have hl₁pos : (0:ℝ) < value r₁.lo := value_pos hpos
  have hs := scale_pos_real
  have hca : (0:ℝ) < ((r₁.lo : Int) : ℝ) := by exact_mod_cast hpos
  have hkey : value dI.hi + (-(value base.lo)) / value r₁.lo < 0 := by
    have hcast : ((dI.hi : Int) : ℝ) * ((r₁.lo : Int) : ℝ)
        < ((base.lo : Int) : ℝ) * ((scale : Int) : ℝ) := by exact_mod_cast hcond
    have hrw : value dI.hi + (-(value base.lo)) / value r₁.lo
        = (((dI.hi : Int) : ℝ) * ((r₁.lo : Int) : ℝ)
            - ((base.lo : Int) : ℝ) * ((scale : Int) : ℝ))
          / (((scale : Int) : ℝ) * ((r₁.lo : Int) : ℝ)) := by
      simp only [value]
      field_simp
      ring
    rw [hrw]
    apply div_neg_of_neg_of_pos (by linarith) (by positivity)
  exact tail_cond_ascent (h := h) (θ := 0) hh hl₁pos hw₁
    (le_trans (value_nonneg g₂.lo_nonneg) hw₂)
    (le_trans (value_nonneg g₃.lo_nonneg) hw₃) hbad
    hbase.1 hderiv.2 hkey

end Leaves

/-! ### Soundness of the tail checker -/

theorem chkTS_sound {tbl : RTree} {h M : ℝ} (htbl : ∀ k : Nat, (tbl.getS k).Good h 0)
    (hh : (15:ℝ) ≤ h) (hM : M ≤ bM2 h)
    {ID6 IB3 : DI} (hD6 : ID6.Mem (bDelta h * (1/6)))
    (hB3 : IB3.Mem (bBeta h * (1/3))) :
    ∀ (t : STree) (b : DBox), chkTS tbl ID6 IB3 t b = true →
      Cover.Excludes (entropyF (bAlpha h) (bG h 0)) M b.toBox := by
  have hhpos : (0:ℝ) < h := by linarith
  have h9 : (9:ℝ) ≤ h := by linarith
  intro t
  induction t with
  | split axis cut l r ihl ihr =>
      intro b hb
      simp only [chkTS, Bool.and_eq_true] at hb
      exact Cover.Excludes.split (fun w₁ w₂ w₃ hm => cover_split b axis cut w₁ w₂ w₃ hm)
        (ihl _ hb.1.2) (ihr _ hb.2)
  | empty =>
      intro b hb
      simp only [chkTS, Bool.or_eq_true, decide_eq_true_eq] at hb
      refine Cover.excludes_empty_ordered ?_
      rcases hb with hb | hb
      · exact Or.inl (value_lt_of_lt hb)
      · exact Or.inr (value_lt_of_lt hb)
  | small =>
      intro b hb
      simp only [chkTS, Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hb
      refine excludes_tighten (Cover.excludes_of_bound ?_)
      rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩ - - -
      refine le_trans hM (local_small_region h9 (by norm_num) (le_refl 0) ?_ ?_ ?_ ?_ ?_ ?_)
      · exact le_trans (value_nonneg h1) k1
      · exact le_trans k2 (value_le_tenth h2)
      · exact le_trans (value_nonneg h5) k3
      · exact le_trans k4 (value_le_tenth h3)
      · exact le_trans (value_nonneg h6) k5
      · exact le_trans k6 (value_le_tenth h4)
  | mixed =>
      intro b hb
      simp only [chkTS, Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hb
      refine excludes_tighten (Cover.excludes_of_bound ?_)
      rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩ - - -
      refine le_trans hM (local_large_region h9 (by norm_num) (le_refl 0) ?_ ?_ ?_ ?_ ?_ ?_)
      · exact le_trans (value_nonneg h1) k1
      · exact le_trans k2 (value_le_tenth h2)
      · exact le_trans (high_le_value h3) k3
      · exact le_trans k4 (value_le_one h4)
      · exact le_trans (high_le_value h5) k5
      · exact le_trans k6 (value_le_one h6)
  | value p₁ p₂ p₃ =>
      intro b hb
      simp only [chkTS, sideOkS, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
      obtain ⟨⟨⟨⟨⟨⟨e1, e2⟩, -⟩, -⟩, ⟨⟨⟨f1, f2⟩, -⟩, -⟩⟩, ⟨⟨⟨g1, g2⟩, -⟩, -⟩⟩, hgap⟩ := hb
      refine excludes_tighten (Cover.excludes_of_bound ?_)
      rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩ - - -
      refine le_trans hM (tail_value_rule hh (htbl p₁) (htbl p₂)
        (htbl p₃) hD6 hB3 hgap ?_ ?_ ?_ ?_ ?_ ?_)
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
          simp only [chkTS, sideOkS, DBox.coordLo, DBox.coordHi, Bool.and_eq_true,
            decide_eq_true_eq, beq_iff_eq] at hb
          obtain ⟨⟨⟨⟨⟨-, ⟨⟨⟨e1, e2⟩, -⟩, -⟩⟩, ⟨⟨⟨f1, f2⟩, -⟩, -⟩,
            ⟨⟨⟨g1, g2⟩, -⟩, -⟩⟩, p1⟩, p2⟩, hsign⟩ := hb
          refine excludes_tighten (Cover.excludes_descent₁ (Branch.hasDerivAt_phi₁ hhpos) ?_ ?_)
          · exact value_pos p1
          · rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩
            exact tail_desc_rule hh (htbl p₁) (htbl p₂)
              (htbl p₃) (by rw [e1]; exact p1) (by rw [e2]; exact p2) hsign
              (by rw [e1]; exact k1) (by rw [e2]; exact k2)
              (by rw [f1]; exact k3) (by rw [f2]; exact k4)
              (by rw [g1]; exact k5) (by rw [g2]; exact k6)
      | 1 =>
          simp only [chkTS, sideOkS, DBox.coordLo, DBox.coordHi, Bool.and_eq_true,
            decide_eq_true_eq, beq_iff_eq] at hb
          obtain ⟨⟨⟨⟨⟨-, ⟨⟨⟨e1, e2⟩, -⟩, -⟩⟩, ⟨⟨⟨f1, f2⟩, -⟩, -⟩,
            ⟨⟨⟨g1, g2⟩, -⟩, -⟩⟩, p1⟩, p2⟩, hsign⟩ := hb
          refine excludes_tighten (Cover.excludes_descent₂
            (d := fun w₁ w₂ w₃ => PhiD1 h 0 w₂ w₁ w₃) (Branch.hasDerivAt_phi₂ hhpos) ?_ ?_)
          · exact value_pos p1
          · rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩
            exact tail_desc_rule hh (htbl p₁) (htbl p₂)
              (htbl p₃) (by rw [e1]; exact p1) (by rw [e2]; exact p2) hsign
              (by rw [e1]; exact k3) (by rw [e2]; exact k4)
              (by rw [f1]; exact k1) (by rw [f2]; exact k2)
              (by rw [g1]; exact k5) (by rw [g2]; exact k6)
      | 2 =>
          simp only [chkTS, sideOkS, DBox.coordLo, DBox.coordHi, Bool.and_eq_true,
            decide_eq_true_eq, beq_iff_eq] at hb
          obtain ⟨⟨⟨⟨⟨-, ⟨⟨⟨e1, e2⟩, -⟩, -⟩⟩, ⟨⟨⟨f1, f2⟩, -⟩, -⟩,
            ⟨⟨⟨g1, g2⟩, -⟩, -⟩⟩, p1⟩, p2⟩, hsign⟩ := hb
          refine excludes_tighten (Cover.excludes_descent₃
            (d := fun w₁ w₂ w₃ => PhiD1 h 0 w₃ w₁ w₂) (Branch.hasDerivAt_phi₃ hhpos) ?_ ?_)
          · exact value_pos p1
          · rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩
            exact tail_desc_rule hh (htbl p₁) (htbl p₂)
              (htbl p₃) (by rw [e1]; exact p1) (by rw [e2]; exact p2) hsign
              (by rw [e1]; exact k5) (by rw [e2]; exact k6)
              (by rw [f1]; exact k1) (by rw [f2]; exact k2)
              (by rw [g1]; exact k3) (by rw [g2]; exact k4)
      | (n+3) =>
          simp only [chkTS, Bool.and_eq_true, decide_eq_true_eq] at hb
          omega
  | asc k p₁ p₂ p₃ =>
      intro b hb
      match k with
      | 0 =>
          simp only [chkTS, sideOkS, DBox.coordLo, DBox.coordHi, Bool.and_eq_true,
            decide_eq_true_eq, beq_iff_eq] at hb
          obtain ⟨⟨⟨⟨⟨⟨-, ⟨⟨⟨e1, e2⟩, -⟩, -⟩⟩, ⟨⟨⟨f1, f2⟩, -⟩, -⟩,
            ⟨⟨⟨g1, g2⟩, -⟩, -⟩⟩, p1⟩, p2⟩, p3⟩, hcond⟩ := hb
          refine excludes_tighten (Cover.excludes_ascent₁' (Branch.hasDerivAt_phi₁ hhpos)
            ?_ ?_ ?_)
          · exact value_pos p1
          · have := value_lt_of_lt p3
            rwa [value_one] at this
          · rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩ hbad
            exact tail_asc_rule hh (htbl p₁) (htbl p₂)
              (htbl p₃) (by rw [e1]; exact p1) (by rw [e2]; exact p2) hD6 hB3
              (by rw [e1]; exact hcond) (lt_of_lt_of_le hbad.2.2 hM)
              (by rw [e1]; exact k1) (by rw [e2]; exact k2)
              (by rw [f1]; exact k3) (by rw [f2]; exact k4)
              (by rw [g1]; exact k5) (by rw [g2]; exact k6)
      | 1 =>
          simp only [chkTS, sideOkS, DBox.coordLo, DBox.coordHi, Bool.and_eq_true,
            decide_eq_true_eq, beq_iff_eq] at hb
          obtain ⟨⟨⟨⟨⟨⟨-, ⟨⟨⟨e1, e2⟩, -⟩, -⟩⟩, ⟨⟨⟨f1, f2⟩, -⟩, -⟩,
            ⟨⟨⟨g1, g2⟩, -⟩, -⟩⟩, p1⟩, p2⟩, p3⟩, hcond⟩ := hb
          refine excludes_tighten (Cover.excludes_ascent₂'
            (d := fun w₁ w₂ w₃ => PhiD1 h 0 w₂ w₁ w₃) (Branch.hasDerivAt_phi₂ hhpos)
            ?_ ?_ ?_)
          · exact value_pos p1
          · have := value_lt_of_lt p3
            rwa [value_one] at this
          · rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩ hbad
            exact tail_asc_rule hh (htbl p₁) (htbl p₂)
              (htbl p₃) (by rw [e1]; exact p1) (by rw [e2]; exact p2) hD6 hB3
              (by rw [e1]; exact hcond)
              ((entropyF_swap12 (bAlpha h) (bG h 0) w₂ w₁ w₃).trans_lt
                (lt_of_lt_of_le hbad.2.2 hM))
              (by rw [e1]; exact k3) (by rw [e2]; exact k4)
              (by rw [f1]; exact k1) (by rw [f2]; exact k2)
              (by rw [g1]; exact k5) (by rw [g2]; exact k6)
      | 2 =>
          simp only [chkTS, sideOkS, DBox.coordLo, DBox.coordHi, Bool.and_eq_true,
            decide_eq_true_eq, beq_iff_eq] at hb
          obtain ⟨⟨⟨⟨⟨⟨-, ⟨⟨⟨e1, e2⟩, -⟩, -⟩⟩, ⟨⟨⟨f1, f2⟩, -⟩, -⟩,
            ⟨⟨⟨g1, g2⟩, -⟩, -⟩⟩, p1⟩, p2⟩, p3⟩, hcond⟩ := hb
          refine excludes_tighten (Cover.excludes_ascent₃'
            (d := fun w₁ w₂ w₃ => PhiD1 h 0 w₃ w₁ w₂) (Branch.hasDerivAt_phi₃ hhpos)
            ?_ ?_ ?_)
          · exact value_pos p1
          · have := value_lt_of_lt p3
            rwa [value_one] at this
          · rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩ hbad
            exact tail_asc_rule hh (htbl p₁) (htbl p₂)
              (htbl p₃) (by rw [e1]; exact p1) (by rw [e2]; exact p2) hD6 hB3
              (by rw [e1]; exact hcond)
              (((entropyF_swap12 (bAlpha h) (bG h 0) w₃ w₁ w₂).trans
                  (entropyF_swap23 (bAlpha h) (bG h 0) w₁ w₃ w₂)).trans_lt
                (lt_of_lt_of_le hbad.2.2 hM))
              (by rw [e1]; exact k5) (by rw [e2]; exact k6)
              (by rw [f1]; exact k1) (by rw [f2]; exact k2)
              (by rw [g1]; exact k3) (by rw [g2]; exact k4)
      | (n+3) =>
          simp only [chkTS, Bool.and_eq_true, decide_eq_true_eq] at hb
          omega
  | cvalue p₁ p₂ p₃ q₁ q₂ q₃ =>
      intro b hb
      simp only [chkTS, sideOkS, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
      obtain ⟨hb, hcent⟩ := hb
      obtain ⟨hb, hgg⟩ := hb
      obtain ⟨hee, hff⟩ := hb
      obtain ⟨⟨⟨e1, e2⟩, -⟩, -⟩ := hee
      obtain ⟨⟨⟨f1, f2⟩, -⟩, -⟩ := hff
      obtain ⟨⟨⟨g1, g2⟩, -⟩, -⟩ := hgg
      refine excludes_tighten (Cover.excludes_of_bound ?_)
      rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩ - - -
      refine le_trans hM (tail_centered_rule hh (htbl p₁) (htbl p₂) (htbl p₃)
        (htbl q₁) (htbl q₂) (htbl q₃) hD6 hB3 hcent ?_ ?_ ?_ ?_ ?_ ?_)
      · rw [e1]; exact k1
      · rw [e2]; exact k2
      · rw [f1]; exact k3
      · rw [f2]; exact k4
      · rw [g1]; exact k5
      · rw [g2]; exact k6


end Itv
end TriangleNumerical


/- ### From `TailParams` -/

/-!
# Parameter intervals for the tail `h ≥ 15`

The three dyadic intervals that enclose `Δ(h)`, `β(h)` and `C(h)` uniformly for
`h ≥ 15`, together with the membership proofs supplied by `TailBounds.lean`.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Itv

open Branch

variable {h : ℝ}

theorem mem_IDtail (hh : (15:ℝ) ≤ h) : IDtail.Mem (bDelta h) := by
  constructor
  · have h1 : value IDtail.lo ≤ ((49999 : Int) : ℝ) / ((50000 : Int) : ℝ) :=
      value_le_rat (n := IDtail.lo) (p := 49999) (q := 50000) (by norm_num)
        (by decide +kernel)
    have h2 := tail_bDelta_ge hh
    norm_num at h1
    linarith
  · have h1 : value IDtail.hi = 1 := value_one
    rw [h1]
    exact tail_bDelta_le hh

theorem mem_IBtail (hh : (15:ℝ) ≤ h) : IBtail.Mem (bBeta h) := by
  constructor
  · have h1 : value IBtail.lo = 0 := value_zero
    rw [h1]
    exact tail_bBeta_nonneg hh
  · have h1 : ((1 : Int) : ℝ) / ((200000 : Int) : ℝ) ≤ value IBtail.hi :=
      rat_le_value (n := IBtail.hi) (p := 1) (q := 200000) (by norm_num)
        (by decide +kernel)
    have h2 := tail_bBeta_le hh
    norm_num at h1
    linarith

theorem mem_ICtail (hh : (15:ℝ) ≤ h) : ICtail.Mem (bC h) := by
  constructor
  · have h1 : value ICtail.lo = 0 := value_zero
    rw [h1]
    exact tail_bC_nonneg hh
  · have h1 : ((1 : Int) : ℝ) / ((100000 : Int) : ℝ) ≤ value ICtail.hi :=
      rat_le_value (n := ICtail.hi) (p := 1) (q := 100000) (by norm_num)
        (by decide +kernel)
    have h2 := tail_bC_le hh
    norm_num at h1
    linarith

end Itv
end TriangleNumerical


/-! # The tail cover `h ≥ 15`: the assembled cube bound (generated). -/
set_option autoImplicit false
set_option maxRecDepth 8000
namespace TriangleNumerical
namespace Itv
open Branch

theorem excludesT {h M : ℝ} (hh : (15:ℝ) ≤ h) (hM : M ≤ bM2 h) :
    Cover.Excludes (entropyF (bAlpha h) (bG h 0)) M rootBox.toBox := by
  have hD6 : ID6T.Mem (bDelta h * (1/6)) := by
    rw [ID6T_eq]; exact mem_pooled6 (mem_IDtail hh)
  have hB3 : IB3T.Mem (bBeta h * (1/3)) := by
    rw [IB3T_eq]; exact mem_pooled3 (mem_IBtail hh)
  have hg : ∀ k : Nat, (recsT.getS k).Good h 0 :=
    good_getS epts_ok (mem_IBtail hh) (mem_ICtail hh) (mem_IDtail hh)
      mem_zeroI IDtail_pos _ recsT_ok
  have S : ∀ (t : STree) (b : DBox), chkTS recsT ID6T IB3T t b = true →
      Cover.Excludes (entropyF (bAlpha h) (bG h 0)) M b.toBox :=
    chkTS_sound hg hh hM hD6 hB3
  exact (excludes_split_of ⟨0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨0, 34028236692093846346337460743176821145, 0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ 0 34028236692093846346337460743176821145 (by decide)
      (excludes_split_of ⟨0, 34028236692093846346337460743176821145, 0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨0, 34028236692093846346337460743176821145, 0, 34028236692093846346337460743176821145, 0, 340282366920938463463374607431768211456⟩ ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ 1 34028236692093846346337460743176821145 (by decide)
      (S subT_0 _ chkT_0)
      (excludes_split_of ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 323268248574891540290205877060179800884, 0, 340282366920938463463374607431768211456⟩ ⟨0, 34028236692093846346337460743176821145, 323268248574891540290205877060179800884, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ 1 323268248574891540290205877060179800884 (by decide)
      (excludes_split_of ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 323268248574891540290205877060179800884, 0, 340282366920938463463374607431768211456⟩ ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 323268248574891540290205877060179800884, 0, 34028236692093846346337460743176821145⟩ ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 323268248574891540290205877060179800884, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456⟩ 2 34028236692093846346337460743176821145 (by decide)
      (S subT_1 _ chkT_1)
      (excludes_split_of ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 323268248574891540290205877060179800884, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456⟩ ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 323268248574891540290205877060179800884, 34028236692093846346337460743176821145, 323268248574891540290205877060179800884⟩ ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 323268248574891540290205877060179800884, 323268248574891540290205877060179800884, 340282366920938463463374607431768211456⟩ 2 323268248574891540290205877060179800884 (by decide)
      (excludes_split_of ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 323268248574891540290205877060179800884, 34028236692093846346337460743176821145, 323268248574891540290205877060179800884⟩ ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 178648242633492693318271668901678311014, 34028236692093846346337460743176821145, 323268248574891540290205877060179800884⟩ ⟨0, 34028236692093846346337460743176821145, 178648242633492693318271668901678311014, 323268248574891540290205877060179800884, 34028236692093846346337460743176821145, 323268248574891540290205877060179800884⟩ 1 178648242633492693318271668901678311014 (by decide)
      (excludes_split_of ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 178648242633492693318271668901678311014, 34028236692093846346337460743176821145, 323268248574891540290205877060179800884⟩ ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 178648242633492693318271668901678311014, 34028236692093846346337460743176821145, 178648242633492693318271668901678311014⟩ ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 178648242633492693318271668901678311014, 178648242633492693318271668901678311014, 323268248574891540290205877060179800884⟩ 2 178648242633492693318271668901678311014 (by decide)
      (excludes_split_of ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 178648242633492693318271668901678311014, 34028236692093846346337460743176821145, 178648242633492693318271668901678311014⟩ ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 106338239662793269832304564822427566079, 34028236692093846346337460743176821145, 178648242633492693318271668901678311014⟩ ⟨0, 34028236692093846346337460743176821145, 106338239662793269832304564822427566079, 178648242633492693318271668901678311014, 34028236692093846346337460743176821145, 178648242633492693318271668901678311014⟩ 1 106338239662793269832304564822427566079 (by decide)
      (S subT_2 _ chkT_2)
      (S subT_3 _ chkT_3))
      (S subT_4 _ chkT_4))
      (S subT_5 _ chkT_5))
      (S subT_6 _ chkT_6)))
      (S subT_7 _ chkT_7)))
      (S subT_8 _ chkT_8))

theorem boundT {h : ℝ} (hh : (15:ℝ) ≤ h) :
    ∀ a ∈ unitInterval, ∀ b ∈ unitInterval, ∀ c ∈ unitInterval,
      bM2 h ≤ entropyF (bAlpha h) (bG h 0) a b c :=
  cube_bound_of_excludes (excludesT hh (le_refl _))

end Itv
end TriangleNumerical
