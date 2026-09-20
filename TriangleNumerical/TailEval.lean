import TriangleNumerical.Deriv
import TriangleNumerical.SpatialEval

/- ### From `TailBounds` -/

/-!
# Uniform tail estimates (T1)

Section 11 of the blueprint.  For every `h ≥ 15`:

```
z ≤ Z := 1/3200000,   h z ≤ 15 Z,
p ≤ P₀ := 30 Z / (1 - Z)^2,
t ≥ 1 - P₀,   49999/50000 ≤ Δ ≤ 1,
α ≥ 10,       0 ≤ β ≤ 1/200000,   0 ≤ C ≤ 1/100000.
```

These are the parameter bounds required by the unbounded tail case.  No
monotonicity of `A`, `Δ`, `β` or `C` in `h` is used: every bound comes from the
two elementary decay estimates for `exp (-h)` and `h exp (-h)`.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Branch
noncomputable section

open Real

variable {h : ℝ}

/-- The tail decay constant `Z = 1/3200000`. -/
def tailZ : ℝ := 1 / 3200000

theorem exp_fifteen_gt : (3200000 : ℝ) < Real.exp 15 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : Real.exp 15 = (Real.exp 1) ^ 15 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  calc (3200000 : ℝ) < (2.7182818283 : ℝ) ^ 15 := by norm_num
    _ ≤ (Real.exp 1) ^ 15 := pow_le_pow_left₀ (by norm_num) h1.le 15

theorem exp_neg_fifteen_lt : Real.exp (-(15:ℝ)) < tailZ := by
  have := exp_fifteen_gt
  have hpos := Real.exp_pos (15:ℝ)
  rw [tailZ, Real.exp_neg, inv_lt_comm₀ hpos (by norm_num)]
  linarith

theorem tail_bz_lt (hh : 15 ≤ h) : bz h < tailZ := by
  have h1 : Real.exp (-h) ≤ Real.exp (-(15:ℝ)) := Real.exp_le_exp.2 (by linarith)
  have := exp_neg_fifteen_lt
  simp only [bz]
  linarith

theorem tail_h_bz_lt (hh : 15 ≤ h) : h * bz h < 15 * tailZ := by
  have h1 : h * Real.exp (-h) ≤ 15 * Real.exp (-15) :=
    mul_exp_neg_antitone (by norm_num) (Set.mem_Ici.2 (by linarith)) hh
  have h2 := exp_neg_fifteen_lt
  simp only [bz]
  linarith

/-- The tail bound `p < 47/5000000`, i.e. `p < 30 Z / (1 - Z)^2` rounded up. -/
theorem tail_bp_lt (hh : 15 ≤ h) : bp h < 47 / 5000000 := by
  have hhpos : 0 < h := by linarith
  have hz := bz_pos h
  have hzlt := tail_bz_lt hh
  have hhz := tail_h_bz_lt hh
  rw [tailZ] at hzlt hhz
  have h1 : 0 < 1 - bz h := by linarith
  have hden : (1 - 1 / 3200000 : ℝ) ^ 2 ≤ (1 - bz h) ^ 2 := by nlinarith
  rw [bp, div_lt_iff₀ (by positivity)]
  nlinarith

theorem tail_bt_gt (hh : 15 ≤ h) : 1 - 47 / 5000000 < bt h := by
  have h1 : 1 + -bp h ≤ Real.exp (-bp h) := by
    have := Real.add_one_le_exp (-bp h); linarith
  have h2 := tail_bp_lt hh
  simp only [bt]
  linarith

/-! ### The uniform tail bounds (T1) -/

theorem tail_bDelta_ge (hh : 15 ≤ h) : 49999 / 50000 ≤ bDelta h := by
  have hhpos : 0 < h := by linarith
  have h1 := tail_bt_gt hh
  have h2 := tail_bz_lt hh
  have h3 := bz_pos h
  have h4 : bt h < 1 := bt_lt_one hhpos
  rw [tailZ] at h2
  rw [bDelta_eq]
  nlinarith

theorem tail_bDelta_le (hh : 15 ≤ h) : bDelta h ≤ 1 :=
  (bDelta_lt_one (by linarith : (0:ℝ) < h)).le

theorem tail_bAlpha_ge_ten (hh : 15 ≤ h) : 10 ≤ bAlpha h := by
  have hhpos : 0 < h := by linarith
  have := bAlpha_gt hhpos
  linarith

theorem tail_bBeta_nonneg (hh : 15 ≤ h) : 0 ≤ bBeta h :=
  (bBeta_pos (by linarith)).le

theorem tail_bBeta_le (hh : 15 ≤ h) : bBeta h ≤ 1 / 200000 := by
  have hhpos : 0 < h := by linarith
  have h1 := tail_bp_lt hh
  have h2 := tail_bt_gt hh
  have h3 := bp_pos hhpos
  rw [bBeta, div_le_iff₀ (by positivity)]
  nlinarith

theorem tail_bC_nonneg (hh : 15 ≤ h) : 0 ≤ bC h :=
  (bC_pos (by linarith)).le

theorem tail_bC_le (hh : 15 ≤ h) : bC h ≤ 1 / 100000 := by
  have hhpos : 0 < h := by linarith
  have h1 := tail_bt_gt hh
  have h2 := tail_bp_lt hh
  have h3 := bp_pos hhpos
  have h4 := bt_pos h
  simp only [bC]
  nlinarith

end
end Branch
end TriangleNumerical


/-!
# The unbounded tail `h ≥ 15`

Section 11 of the blueprint.  For `h ≥ 15` the parameter `α = A(h)` is
unbounded, so the finite-slab helper `L_α` cannot be evaluated.  Instead the
numerical work uses the helper

```
L_A = Δ/6 · P − β/3 · Σ wᵢ² + A · w₁w₂w₃
```

with the *fixed* coefficient `A = 10 ≤ α` (uniform tail bound T1), together
with the *conditional* rule (T2): at a point that is a global minimum with
value below `M₂`, the actual `α w₁w₂w₃` is bounded by `−𝓑`, which turns a
certified upper bound for `∂ᵢ𝓑` into an upper bound for `∂ᵢΦ`.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Branch
noncomputable section

open Real Itv

variable {h θ w₁ w₂ w₃ : ℝ}

/-- The gap helper with an arbitrary coefficient `A` in place of `α`; `A = α`
gives `Lalpha`, `A = 10` the tail helper `L₁₀`, and `A = 0` the base `𝓑`. -/
def LgenA (A h θ w₁ w₂ w₃ : ℝ) : ℝ :=
  bDelta h * (1 / 6) * gapP h θ w₁ w₂ w₃ + A * w₁ * w₂ * w₃
    - bBeta h * (1 / 3) * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2)

/-- The first spatial derivative with an arbitrary coefficient in place of `α`. -/
def PhiD1gen (A h θ w₁ w₂ w₃ : ℝ) : ℝ :=
  Real.log w₁ / 3 + A * w₂ * w₃
    - etaD θ (bX h w₁) * bDd h w₁ / 6 * (etaT θ (bX h w₂) + etaT θ (bX h w₃))

theorem PhiD1_eq_gen (A : ℝ) :
    PhiD1 h θ w₁ w₂ w₃ = PhiD1gen A h θ w₁ w₂ w₃ + (bAlpha h - A) * w₂ * w₃ := by
  simp only [PhiD1, PhiD1gen]; ring

/-- `J = Φ − M₂` in terms of the base helper `𝓑 = L_0`. -/
theorem gap_eq_base (hh : (0:ℝ) < h) :
    entropyF (bAlpha h) (bG h θ) w₁ w₂ w₃ - bM2 h
      = LgenA 0 h θ w₁ w₂ w₃ + bAlpha h * w₁ * w₂ * w₃ + bBeta h * (br h) ^ 2 / 3 := by
  have hid := gap_identity (h := h) (θ := θ) hh w₁ w₂ w₃
  simp only [LgenA, gapP] at hid ⊢
  linarith

/-- The tail helper is a lower bound for the actual gap. -/
theorem L10_le_gap (hh : (15:ℝ) ≤ h) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) :
    LgenA 10 h θ w₁ w₂ w₃ ≤ entropyF (bAlpha h) (bG h θ) w₁ w₂ w₃ - bM2 h := by
  have h9 : (9:ℝ) ≤ h := by linarith
  have hhpos : (0:ℝ) < h := by linarith
  have hα := tail_bAlpha_ge_ten hh
  have hprod : (0:ℝ) ≤ w₁ * w₂ * w₃ := by positivity
  have hbeta := (bBeta_pos h9).le
  have hr : 0 ≤ bBeta h * (br h) ^ 2 / 3 := by positivity
  have hbase := gap_eq_base (h := h) (θ := θ) hhpos (w₁ := w₁) (w₂ := w₂) (w₃ := w₃)
  have hmul : 10 * (w₁ * w₂ * w₃) ≤ bAlpha h * (w₁ * w₂ * w₃) :=
    mul_le_mul_of_nonneg_right hα hprod
  simp only [LgenA] at hbase ⊢
  linarith

/-- The tail derivative helper is a lower bound for the actual derivative. -/
theorem PhiD1_ge_ten (hh : (15:ℝ) ≤ h) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) :
    PhiD1gen 10 h θ w₁ w₂ w₃ ≤ PhiD1 h θ w₁ w₂ w₃ := by
  have hα := tail_bAlpha_ge_ten hh
  have hprod : (0:ℝ) ≤ w₂ * w₃ := mul_nonneg hw₂ hw₃
  have := PhiD1_eq_gen (A := 10) (h := h) (θ := θ) (w₁ := w₁) (w₂ := w₂) (w₃ := w₃)
  nlinarith [this]

/-- The conditional tail-descent rule (T2).  At a point whose value is below
`M₂`, an upper bound for `∂ᵢ𝓑` plus `−lowerB / l₁` bounds `∂ᵢΦ`. -/
theorem tail_cond_ascent (hh : (15:ℝ) ≤ h) {l₁ lowerB upperD : ℝ}
    (hl₁ : 0 < l₁) (hl₁w : l₁ ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    (hbad : entropyF (bAlpha h) (bG h θ) w₁ w₂ w₃ < bM2 h)
    (hB : lowerB ≤ LgenA 0 h θ w₁ w₂ w₃)
    (hD : PhiD1gen 0 h θ w₁ w₂ w₃ ≤ upperD)
    (hneg : upperD + (-lowerB) / l₁ < 0) :
    PhiD1 h θ w₁ w₂ w₃ < 0 := by
  have h9 : (9:ℝ) ≤ h := by linarith
  have hhpos : (0:ℝ) < h := by linarith
  have hw₁ : 0 < w₁ := lt_of_lt_of_le hl₁ hl₁w
  have hα : (10:ℝ) ≤ bAlpha h := tail_bAlpha_ge_ten hh
  have hαpos : (0:ℝ) < bAlpha h := by linarith
  have hbeta := (bBeta_pos h9).le
  have hr : 0 ≤ bBeta h * (br h) ^ 2 / 3 := by positivity
  have hbase := gap_eq_base (h := h) (θ := θ) hhpos (w₁ := w₁) (w₂ := w₂) (w₃ := w₃)
  -- the product is bounded by `-lowerB`
  have hprod : bAlpha h * w₁ * w₂ * w₃ ≤ -lowerB := by
    have : bAlpha h * w₁ * w₂ * w₃ ≤ -LgenA 0 h θ w₁ w₂ w₃ := by linarith
    linarith
  have hprod0 : (0:ℝ) ≤ bAlpha h * w₁ * w₂ * w₃ := by positivity
  -- divide by `w₁`
  have hdiv : bAlpha h * w₂ * w₃ ≤ (-lowerB) / l₁ := by
    have h1 : bAlpha h * w₂ * w₃ = (bAlpha h * w₁ * w₂ * w₃) / w₁ := by
      field_simp
    rw [h1]
    have h2 : (bAlpha h * w₁ * w₂ * w₃) / w₁ ≤ (-lowerB) / w₁ := by
      gcongr
    refine le_trans h2 ?_
    exact div_le_div_of_nonneg_left (by linarith) hl₁ hl₁w
  have heq := PhiD1_eq_gen (A := 0) (h := h) (θ := θ) (w₁ := w₁) (w₂ := w₂) (w₃ := w₃)
  have : PhiD1 h θ w₁ w₂ w₃ ≤ upperD + (-lowerB) / l₁ := by
    rw [heq]
    have : (bAlpha h - 0) * w₂ * w₃ = bAlpha h * w₂ * w₃ := by ring
    linarith [this ▸ hdiv]
  linarith

end
end Branch

namespace Itv

open Branch

/-! ### Interval evaluation with an arbitrary coefficient in the cubic term -/

/-- Soundness of the leaf evaluator for `LgenA`. -/
theorem mem_leafI_gen {s₁ s₂ s₃ : Side} {IA IDl IB IC IT : DI} {A h θ w₁ w₂ w₃ : ℝ}
    (hH₁lo : s₁.IHlo.Mem (H (value s₁.lo))) (hH₁hi : s₁.IHhi.Mem (H (value s₁.hi)))
    (hH₂lo : s₂.IHlo.Mem (H (value s₂.lo))) (hH₂hi : s₂.IHhi.Mem (H (value s₂.hi)))
    (hH₃lo : s₃.IHlo.Mem (H (value s₃.lo))) (hH₃hi : s₃.IHhi.Mem (H (value s₃.hi)))
    (h0₁ : 0 ≤ value s₁.lo) (h1₁ : value s₁.hi ≤ 1)
    (h0₂ : 0 ≤ value s₂.lo) (h1₂ : value s₂.hi ≤ 1)
    (h0₃ : 0 ≤ value s₃.lo) (h1₃ : value s₃.hi ≤ 1)
    (hA : IA.Mem A) (hD : IDl.Mem (bDelta h)) (hB : IB.Mem (bBeta h))
    (hC : IC.Mem (bC h)) (hT : IT.Mem θ) (hDpos : 0 < IDl.lo)
    (hw₁ : value s₁.lo ≤ w₁) (hw₁' : w₁ ≤ value s₁.hi)
    (hw₂ : value s₂.lo ≤ w₂) (hw₂' : w₂ ≤ value s₂.hi)
    (hw₃ : value s₃.lo ≤ w₃) (hw₃' : w₃ ≤ value s₃.hi) :
    (leafI s₁ s₂ s₃ IA IDl IB IC IT).Mem (LgenA A h θ w₁ w₂ w₃) := by
  obtain ⟨hu₁, -, -, hX₁⟩ := s₁.sound hH₁lo hH₁hi h0₁ h1₁ hB hC hD hDpos hw₁ hw₁'
  obtain ⟨hu₂, -, -, hX₂⟩ := s₂.sound hH₂lo hH₂hi h0₂ h1₂ hB hC hD hDpos hw₂ hw₂'
  obtain ⟨hu₃, -, -, hX₃⟩ := s₃.sound hH₃lo hH₃hi h0₃ h1₃ hB hC hD hDpos hw₃ hw₃'
  have hE₁ := mem_etaI hT hX₁
  have hE₂ := mem_etaI hT hX₂
  have hE₃ := mem_etaI hT hX₃
  have hP := mem_sub (mem_sub (mem_mul (mem_intI 2) (mem_add (mem_add hX₁ hX₂) hX₃))
      (mem_add (mem_add (mem_mul hE₁ hE₂) (mem_mul hE₁ hE₃)) (mem_mul hE₂ hE₃)))
    (mem_intI 3)
  have hPeq : ((2:Int) : ℝ) * (bX h w₁ + bX h w₂ + bX h w₃)
      - (etaT θ (bX h w₁) * etaT θ (bX h w₂) + etaT θ (bX h w₁) * etaT θ (bX h w₃)
        + etaT θ (bX h w₂) * etaT θ (bX h w₃)) - ((3:Int) : ℝ)
      = gapP h θ w₁ w₂ w₃ := by
    simp only [gapP]
    push_cast
    ring
  rw [hPeq] at hP
  have h6 := mem_inv_intI (n := 6) (by norm_num)
  have h3 := mem_inv_intI (n := 3) (by norm_num)
  have hm := mem_sub (mem_add (mem_mul (mem_mul hD h6) hP)
      (mem_mul (mem_mul (mem_mul hA hu₁) hu₂) hu₃))
    (mem_mul (mem_mul hB h3)
      (mem_add (mem_add (mem_pow hu₁ 2) (mem_pow hu₂ 2)) (mem_pow hu₃ 2)))
  have heq : bDelta h * (1 / ((6:Int) : ℝ)) * gapP h θ w₁ w₂ w₃
      + A * w₁ * w₂ * w₃
      - bBeta h * (1 / ((3:Int) : ℝ)) * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2)
      = LgenA A h θ w₁ w₂ w₃ := by
    simp only [LgenA]
    push_cast
    ring
  rw [heq] at hm
  exact hm

/-- Soundness of the derivative evaluator for `PhiD1gen`. -/
theorem mem_derivI_gen {s₁ s₂ s₃ : Side} {IA IDl IB IC IT : DI} {A h θ w₁ w₂ w₃ : ℝ}
    (hH₁lo : s₁.IHlo.Mem (H (value s₁.lo))) (hH₁hi : s₁.IHhi.Mem (H (value s₁.hi)))
    (hH₂lo : s₂.IHlo.Mem (H (value s₂.lo))) (hH₂hi : s₂.IHhi.Mem (H (value s₂.hi)))
    (hH₃lo : s₃.IHlo.Mem (H (value s₃.lo))) (hH₃hi : s₃.IHhi.Mem (H (value s₃.hi)))
    (hL₁lo : s₁.ILlo.Mem (Real.log (value s₁.lo)))
    (hL₁hi : s₁.ILhi.Mem (Real.log (value s₁.hi)))
    (hpos₁ : 0 < value s₁.lo)
    (h0₁ : 0 ≤ value s₁.lo) (h1₁ : value s₁.hi ≤ 1)
    (h0₂ : 0 ≤ value s₂.lo) (h1₂ : value s₂.hi ≤ 1)
    (h0₃ : 0 ≤ value s₃.lo) (h1₃ : value s₃.hi ≤ 1)
    (hA : IA.Mem A) (hD : IDl.Mem (bDelta h)) (hB : IB.Mem (bBeta h))
    (hC : IC.Mem (bC h)) (hT : IT.Mem θ) (hDpos : 0 < IDl.lo)
    (hw₁ : value s₁.lo ≤ w₁) (hw₁' : w₁ ≤ value s₁.hi)
    (hw₂ : value s₂.lo ≤ w₂) (hw₂' : w₂ ≤ value s₂.hi)
    (hw₃ : value s₃.lo ≤ w₃) (hw₃' : w₃ ≤ value s₃.hi) :
    (derivI s₁ s₂ s₃ IA IDl IB IC IT).Mem (PhiD1gen A h θ w₁ w₂ w₃) := by
  obtain ⟨-, -, -, hX₁⟩ := s₁.sound hH₁lo hH₁hi h0₁ h1₁ hB hC hD hDpos hw₁ hw₁'
  obtain ⟨hu₂, -, -, hX₂⟩ := s₂.sound hH₂lo hH₂hi h0₂ h1₂ hB hC hD hDpos hw₂ hw₂'
  obtain ⟨hu₃, -, -, hX₃⟩ := s₃.sound hH₃lo hH₃hi h0₃ h1₃ hB hC hD hDpos hw₃ hw₃'
  obtain ⟨hlog, hDd⟩ := s₁.sound_log hL₁lo hL₁hi hpos₁ hB hw₁ hw₁'
  have h3 := mem_inv_intI (n := 3) (by norm_num)
  have h6 := mem_inv_intI (n := 6) (by norm_num)
  have hm := mem_sub (mem_add (mem_mul hlog h3) (mem_mul (mem_mul hA hu₂) hu₃))
    (mem_mul (mem_mul (mem_mul (mem_etaDI hT hX₁) hDd) h6)
      (mem_add (mem_etaI hT hX₂) (mem_etaI hT hX₃)))
  have heq : Real.log w₁ * (1 / ((3:Int) : ℝ)) + A * w₂ * w₃
      - etaD θ (bX h w₁) * bDd h w₁ * (1 / ((6:Int) : ℝ))
        * (etaT θ (bX h w₂) + etaT θ (bX h w₃))
      = PhiD1gen A h θ w₁ w₂ w₃ := by
    simp only [PhiD1gen]
    push_cast
    ring
  rw [heq] at hm
  exact hm

end Itv
end TriangleNumerical
