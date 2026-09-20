import TriangleNumerical.Root
import Mathlib.Analysis.Complex.ExponentialBounds

/- ### From `Branch` -/

/-!
# The explicit nonconstant branch

Section 4 of the blueprint.  For `h > 0` the branch parameters are

```
z = exp (-h), p = 2 h z / (1 - z)^2, t = exp (-p), r = t z,
Δ = t - r,     α = 2 h / (3 Δ^2),    M₂ = 1 - (r+t)/2 - α (r^3 + 3 r t^2)/2
```

and we prove the two exact logarithm identities (B2), the branch value
identity (B3), and the coverage statement: every `α ≥ A h₀` is `A h` for some
`h ≥ h₀`.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Branch
noncomputable section

open Real

def bz (h : ℝ) : ℝ := Real.exp (-h)
def bp (h : ℝ) : ℝ := 2 * h * bz h / (1 - bz h) ^ 2
def bt (h : ℝ) : ℝ := Real.exp (-bp h)
def br (h : ℝ) : ℝ := bt h * bz h
def bDelta (h : ℝ) : ℝ := bt h - br h
def bAlpha (h : ℝ) : ℝ := 2 * h / (3 * (bDelta h) ^ 2)
def bM2 (h : ℝ) : ℝ :=
  1 - (br h + bt h) / 2 - bAlpha h * ((br h) ^ 3 + 3 * br h * (bt h) ^ 2) / 2

variable {h : ℝ}

theorem bz_pos (h : ℝ) : 0 < bz h := Real.exp_pos _

theorem bz_lt_one (hh : 0 < h) : bz h < 1 := by
  rw [bz, Real.exp_lt_one_iff]; linarith

theorem one_sub_bz_pos (hh : 0 < h) : 0 < 1 - bz h := by
  have := bz_lt_one hh; linarith

theorem bp_pos (hh : 0 < h) : 0 < bp h := by
  have h1 := bz_pos h
  have h2 := one_sub_bz_pos hh
  rw [bp]
  positivity

theorem bt_pos (h : ℝ) : 0 < bt h := Real.exp_pos _

theorem bt_lt_one (hh : 0 < h) : bt h < 1 := by
  rw [bt, Real.exp_lt_one_iff]
  have := bp_pos hh; linarith

theorem br_pos (h : ℝ) : 0 < br h := mul_pos (bt_pos h) (bz_pos h)

theorem br_lt_bt (hh : 0 < h) : br h < bt h := by
  have h1 := bt_pos h
  have h2 := bz_lt_one hh
  rw [br]
  nlinarith

theorem bDelta_pos (hh : 0 < h) : 0 < bDelta h := by
  have := br_lt_bt hh; rw [bDelta]; linarith

theorem bDelta_lt_one (hh : 0 < h) : bDelta h < 1 := by
  have h1 := br_pos h
  have h2 := bt_lt_one hh
  rw [bDelta]; linarith

theorem bAlpha_pos (hh : 0 < h) : 0 < bAlpha h := by
  have h1 := bDelta_pos hh
  rw [bAlpha]
  positivity

/-- `A(h) > 2h/3`, which makes `A` unbounded. -/
theorem bAlpha_gt (hh : 0 < h) : 2 * h / 3 < bAlpha h := by
  have h1 := bDelta_pos hh
  have h2 := bDelta_lt_one hh
  have hsq : (bDelta h) ^ 2 < 1 := by nlinarith
  have hsqpos : 0 < (bDelta h) ^ 2 := by positivity
  rw [bAlpha, lt_div_iff₀ (by positivity)]
  nlinarith

/-! ## The two logarithm identities (B2) -/

theorem log_bt_eq (h : ℝ) : Real.log (bt h) = -bp h := by
  rw [bt, Real.log_exp]

theorem log_br_eq (h : ℝ) : Real.log (br h) = -bp h - h := by
  rw [br, Real.log_mul (ne_of_gt (bt_pos h)) (ne_of_gt (bz_pos h)), bt, bz,
    Real.log_exp, Real.log_exp]
  ring

theorem bDelta_eq (h : ℝ) : bDelta h = bt h * (1 - bz h) := by
  simp only [bDelta, br]; ring

theorem log_bt (hh : 0 < h) : Real.log (bt h) = -(3 * bAlpha h * br h * bt h) := by
  have hz := bz_pos h
  have h1 := one_sub_bz_pos hh
  have ht := bt_pos h
  have key : 3 * bAlpha h * br h * bt h = bp h := by
    simp only [bAlpha, br, bDelta_eq, bp]
    field_simp
  rw [log_bt_eq, key]

theorem log_br (hh : 0 < h) :
    Real.log (br h) = -(3 * bAlpha h / 2 * ((br h) ^ 2 + (bt h) ^ 2)) := by
  have hz := bz_pos h
  have h1 := one_sub_bz_pos hh
  have ht := bt_pos h
  have key : 3 * bAlpha h / 2 * ((br h) ^ 2 + (bt h) ^ 2) = bp h + h := by
    simp only [bAlpha, br, bDelta_eq, bp]
    field_simp
    ring
  rw [log_br_eq, key]
  ring

/-! ## The branch value (B3) -/

theorem twoBlock_at_branch (hh : 0 < h) :
    twoBlockObjective (bAlpha h) (br h) (bt h) = bM2 h := by
  have h1 := log_br hh
  have h2 := log_bt hh
  simp only [twoBlockObjective, bM2, H, h1, h2]
  ring

/-! ## Coverage: every large parameter is attained -/

theorem continuous_bz : Continuous bz := by
  unfold bz; fun_prop

theorem continuousOn_bp : ContinuousOn bp (Set.Ioi 0) := by
  apply ContinuousOn.div
  · exact ((continuous_const.mul continuous_id).mul continuous_bz).continuousOn
  · exact ((continuous_const.sub continuous_bz).pow 2).continuousOn
  · intro x hx
    have := one_sub_bz_pos (Set.mem_Ioi.1 hx)
    positivity

theorem continuousOn_bt : ContinuousOn bt (Set.Ioi 0) :=
  Real.continuous_exp.comp_continuousOn continuousOn_bp.neg

theorem continuousOn_br : ContinuousOn br (Set.Ioi 0) :=
  continuousOn_bt.mul continuous_bz.continuousOn

theorem continuousOn_bDelta : ContinuousOn bDelta (Set.Ioi 0) :=
  continuousOn_bt.sub continuousOn_br

theorem continuousOn_bAlpha : ContinuousOn bAlpha (Set.Ioi 0) := by
  apply ContinuousOn.div
  · exact (continuous_const.mul continuous_id).continuousOn
  · exact continuousOn_const.mul (continuousOn_bDelta.pow 2)
  · intro x hx
    have := bDelta_pos (Set.mem_Ioi.1 hx)
    positivity

/-- Every `α ≥ A h₀` equals `A h` for some `h ≥ h₀`. -/
theorem exists_branch_param {h₀ α : ℝ} (hh₀ : 0 < h₀) (hα : bAlpha h₀ ≤ α) :
    ∃ h, h₀ ≤ h ∧ bAlpha h = α := by
  have hαpos : 0 < α := lt_of_lt_of_le (bAlpha_pos hh₀) hα
  set h₁ : ℝ := max h₀ (3 * α / 2 + 1) with hh₁def
  have hh₁ : h₀ ≤ h₁ := le_max_left _ _
  have hh₁pos : 0 < h₁ := lt_of_lt_of_le hh₀ hh₁
  have hupper : α ≤ bAlpha h₁ := by
    have h2 : 3 * α / 2 + 1 ≤ h₁ := le_max_right _ _
    have := bAlpha_gt hh₁pos
    linarith
  have hcont : ContinuousOn bAlpha (Set.Icc h₀ h₁) :=
    continuousOn_bAlpha.mono (by
      intro x hx
      exact Set.mem_Ioi.2 (lt_of_lt_of_le hh₀ hx.1))
  obtain ⟨h, hmem, hval⟩ := intermediate_value_Icc hh₁ hcont (Set.mem_Icc.2 ⟨hα, hupper⟩)
  exact ⟨h, hmem.1, hval⟩

end
end Branch
end TriangleNumerical


/- ### From `BranchBounds` -/

/-!
# Uniform branch estimates (B4)

Section 4.1 of the blueprint.  For every `h ≥ 9`:

```
z < 1/8000,  h z < 9/8000,  h² z < 81/8000,
p < 1/400,   t > 399/400,   99/100 < Δ < 1,
α ≥ 6,       0 < β < 1/500, 0 < C < 1/250,  α² r < 1/100.
```

Here `β = p/(2t)` and `C = 1 - (1 + p/2) t`, as in the blueprint.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Branch
noncomputable section

open Real

variable {h : ℝ}

/-- The branch quantity `β = 3 α r / 2 = p / (2 t)`. -/
def bBeta (h : ℝ) : ℝ := bp h / (2 * bt h)

/-- The branch quantity `C = 1 - (1 + p/2) t`. -/
def bC (h : ℝ) : ℝ := 1 - (1 + bp h / 2) * bt h

theorem bBeta_eq (hh : 0 < h) : bBeta h = 3 * bAlpha h * br h / 2 := by
  have ht := bt_pos h
  have hz := bz_pos h
  have h1 := one_sub_bz_pos hh
  have key : 3 * bAlpha h * br h * bt h = bp h := by
    simp only [bAlpha, br, bDelta_eq, bp]
    field_simp
  rw [bBeta]
  field_simp
  linarith [key]

/-! ### Exponential decay estimates -/

theorem exp_nine_gt : (8000 : ℝ) < Real.exp 9 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : Real.exp 9 = (Real.exp 1) ^ 9 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  calc (8000 : ℝ) < (2.7182818283 : ℝ) ^ 9 := by norm_num
    _ ≤ (Real.exp 1) ^ 9 := by
        apply pow_le_pow_left₀ (by norm_num) h1.le

theorem bz_lt (hh : 9 ≤ h) : bz h < 1 / 8000 := by
  have h1 : Real.exp 9 ≤ Real.exp h := Real.exp_le_exp.2 hh
  have h2 : (8000 : ℝ) < Real.exp h := lt_of_lt_of_le exp_nine_gt h1
  have h3 : bz h = 1 / Real.exp h := by
    rw [bz, Real.exp_neg]; ring
  rw [h3]
  have := Real.exp_pos h
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- `h ↦ h exp (-h)` is antitone on `[1, ∞)`. -/
theorem mul_exp_neg_antitone : AntitoneOn (fun x : ℝ => x * Real.exp (-x)) (Set.Ici 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 1) (by fun_prop)
  · intro x hx
    exact ((hasDerivAt_id x).mul ((Real.hasDerivAt_exp (-x)).comp x
      (by simpa using (hasDerivAt_id x).neg))).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hd : HasDerivAt (fun x : ℝ => x * Real.exp (-x))
        (1 * Real.exp (-x) + x * (Real.exp (-x) * -1)) x :=
      (hasDerivAt_id x).mul ((Real.hasDerivAt_exp (-x)).comp x
        (by simpa using (hasDerivAt_id x).neg))
    rw [hd.deriv]
    have hx1 : (1:ℝ) < x := hx
    have := Real.exp_pos (-x)
    nlinarith

/-- `h ↦ h² exp (-h)` is antitone on `[2, ∞)`. -/
theorem sq_mul_exp_neg_antitone :
    AntitoneOn (fun x : ℝ => x ^ 2 * Real.exp (-x)) (Set.Ici 2) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 2) (by fun_prop)
  · intro x hx
    exact (((hasDerivAt_id x).pow 2).mul ((Real.hasDerivAt_exp (-x)).comp x
      (by simpa using (hasDerivAt_id x).neg))).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hd : HasDerivAt (fun x : ℝ => x ^ 2 * Real.exp (-x))
        ((2 * x ^ 1 * 1) * Real.exp (-x) + x ^ 2 * (Real.exp (-x) * -1)) x :=
      ((hasDerivAt_id x).pow 2).mul ((Real.hasDerivAt_exp (-x)).comp x
        (by simpa using (hasDerivAt_id x).neg))
    rw [hd.deriv]
    have hx1 : (2:ℝ) < x := hx
    have hexp := Real.exp_pos (-x)
    have hfac : (0:ℝ) ≤ x * (x - 2) := by nlinarith
    nlinarith [mul_nonneg hfac hexp.le]

theorem h_bz_lt (hh : 9 ≤ h) : h * bz h < 9 / 8000 := by
  have h1 : h * Real.exp (-h) ≤ 9 * Real.exp (-9) :=
    mul_exp_neg_antitone (by norm_num) (Set.mem_Ici.2 (by linarith)) hh
  have h2 : Real.exp (-(9:ℝ)) < 1 / 8000 := by
    have := exp_nine_gt
    rw [Real.exp_neg]
    rw [inv_lt_comm₀ (Real.exp_pos 9) (by norm_num)]
    linarith
  have h3 : 9 * Real.exp (-(9:ℝ)) < 9 / 8000 := by linarith
  simp only [bz]
  linarith

theorem h_sq_bz_lt (hh : 9 ≤ h) : h ^ 2 * bz h < 81 / 8000 := by
  have h1 : h ^ 2 * Real.exp (-h) ≤ 9 ^ 2 * Real.exp (-9) :=
    sq_mul_exp_neg_antitone (by norm_num) (Set.mem_Ici.2 (by linarith)) hh
  have h2 : Real.exp (-(9:ℝ)) < 1 / 8000 := by
    have := exp_nine_gt
    rw [Real.exp_neg]
    rw [inv_lt_comm₀ (Real.exp_pos 9) (by norm_num)]
    linarith
  simp only [bz]
  nlinarith

/-! ### The uniform bounds -/

theorem bp_lt (hh : 9 ≤ h) : bp h < 1 / 400 := by
  have hhpos : 0 < h := by linarith
  have hz := bz_pos h
  have hzlt := bz_lt hh
  have hhz := h_bz_lt hh
  have h1 : 0 < 1 - bz h := by linarith
  have hden : (1 - 1 / 8000 : ℝ) ^ 2 ≤ (1 - bz h) ^ 2 := by nlinarith
  rw [bp, div_lt_iff₀ (by positivity)]
  nlinarith

theorem bt_gt (hh : 9 ≤ h) : 399 / 400 < bt h := by
  have h1 : 1 + -bp h ≤ Real.exp (-bp h) := by
    have := Real.add_one_le_exp (-bp h)
    linarith
  have h2 := bp_lt hh
  simp only [bt]
  linarith

theorem bDelta_gt (hh : 9 ≤ h) : 99 / 100 < bDelta h := by
  have hhpos : 0 < h := by linarith
  have h1 := bt_gt hh
  have h2 := bz_lt hh
  have h3 := bz_pos h
  have h4 : bt h < 1 := bt_lt_one hhpos
  rw [bDelta_eq]
  nlinarith

theorem bAlpha_ge_six (hh : 9 ≤ h) : 6 ≤ bAlpha h := by
  have hhpos : 0 < h := by linarith
  have h1 := bDelta_pos hhpos
  have h2 := bDelta_lt_one hhpos
  have hsq : (bDelta h) ^ 2 < 1 := by nlinarith
  rw [bAlpha, le_div_iff₀ (by positivity)]
  nlinarith

theorem bBeta_pos (hh : 9 ≤ h) : 0 < bBeta h := by
  have hhpos : 0 < h := by linarith
  have h1 := bp_pos hhpos
  have h2 := bt_pos h
  rw [bBeta]
  positivity

theorem bBeta_lt (hh : 9 ≤ h) : bBeta h < 1 / 500 := by
  have hhpos : 0 < h := by linarith
  have h1 := bp_lt hh
  have h2 := bt_gt hh
  have h3 := bp_pos hhpos
  rw [bBeta, div_lt_iff₀ (by positivity)]
  nlinarith

theorem bC_pos (hh : 9 ≤ h) : 0 < bC h := by
  have hhpos : 0 < h := by linarith
  have hp := bp_pos hhpos
  -- exp p > 1 + p/2
  have h1 : 1 + bp h ≤ Real.exp (bp h) := by
    have := Real.add_one_le_exp (bp h); linarith
  have h2 : Real.exp (bp h) * Real.exp (-bp h) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : 0 < Real.exp (-bp h) := Real.exp_pos _
  simp only [bC, bt]
  nlinarith

theorem bC_lt (hh : 9 ≤ h) : bC h < 1 / 250 := by
  have hhpos : 0 < h := by linarith
  have h1 := bt_gt hh
  have h2 := bp_lt hh
  have h3 := bp_pos hhpos
  have h4 := bt_pos h
  simp only [bC]
  nlinarith

theorem alpha_sq_r_lt (hh : 9 ≤ h) : (bAlpha h) ^ 2 * br h < 1 / 100 := by
  have hhpos : 0 < h := by linarith
  have hz := bz_pos h
  have hzlt := bz_lt hh
  have ht := bt_gt hh
  have ht1 := bt_lt_one hhpos
  have hd := bDelta_gt hh
  have hd1 := bDelta_lt_one hhpos
  have hdpos := bDelta_pos hhpos
  have hhsq := h_sq_bz_lt hh
  -- α² r = 4 h² z t / (9 Δ⁴)
  have hkey : (bAlpha h) ^ 2 * br h
      = 4 * (h ^ 2 * bz h) * bt h / (9 * (bDelta h) ^ 4) := by
    simp only [bAlpha, br]
    field_simp
    ring
  rw [hkey, div_lt_iff₀ (by positivity)]
  have hd2 : (99 / 100 : ℝ) ^ 2 < (bDelta h) ^ 2 := by nlinarith
  have hd4 : (99 / 100 : ℝ) ^ 4 < (bDelta h) ^ 4 := by nlinarith [hd2]
  nlinarith

end
end Branch
end TriangleNumerical


/- ### From `Certificate` -/

/-!
# The explicit certificate: exact identities

Section 5 of the blueprint: the shape function `D`, its normalisation `X`, the
polynomial `η_θ`, the certificate `G`, the sharp values (G2), (G5) and the
stable gap identity (G7).  Everything here is an exact identity, valid for
every auxiliary parameter `θ`.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Branch
noncomputable section

open Real

variable {h θ : ℝ}

/-- The shape function `D(w) = H(w) + β w² - C`. -/
def bD (h w : ℝ) : ℝ := H w + bBeta h * w ^ 2 - bC h

/-- Normalised shape `X = D / Δ`. -/
def bX (h w : ℝ) : ℝ := bD h w / bDelta h

/-- The cubic interpolation polynomial. -/
def etaT (θ X : ℝ) : ℝ := 3 * X - X ^ 2 - 1 + θ * X * (1 - X) ^ 2

/-- The certificate function. -/
def bG (h θ w : ℝ) : ℝ := Real.sqrt (bDelta h / 6) * etaT θ (bX h w)

/-! ### Polynomial values of η -/

theorem etaT_zero (θ : ℝ) : etaT θ 0 = -1 := by simp [etaT]

theorem etaT_one (θ : ℝ) : etaT θ 1 = 1 := by simp [etaT]; ring

/-! ### Continuity -/

theorem continuous_bD (h : ℝ) : Continuous (bD h) :=
  (continuous_H.add (continuous_const.mul (continuous_pow 2))).sub continuous_const

theorem continuous_bX (h : ℝ) : Continuous (bX h) :=
  (continuous_bD h).div_const _

theorem continuous_etaT (θ : ℝ) : Continuous (etaT θ) := by
  unfold etaT
  fun_prop

theorem continuous_bG (h θ : ℝ) : Continuous (bG h θ) :=
  continuous_const.mul ((continuous_etaT θ).comp (continuous_bX h))

/-! ### Sharp values of D (G2) -/

theorem bD_t (h : ℝ) : bD h (bt h) = 0 := by
  have ht := bt_pos h
  have hlog := log_bt_eq h
  simp only [bD, H, bBeta, bC, hlog]
  field_simp
  ring

theorem bD_r (hh : 0 < h) : bD h (br h) = bDelta h := by
  have ht := bt_pos h
  have hz := bz_pos h
  have h1 := one_sub_bz_pos hh
  have hlog : Real.log (bt h * bz h) = -bp h - h := by
    simpa [br] using log_br_eq h
  have hp : bp h = 2 * h * bz h / (1 - bz h) ^ 2 := rfl
  simp only [bD, H, bBeta, bC, bDelta_eq, br, hlog, hp]
  field_simp
  ring

theorem bX_t (h : ℝ) : bX h (bt h) = 0 := by
  simp only [bX, bD_t h, zero_div]

theorem bX_r (hh : 0 < h) : bX h (br h) = 1 := by
  simp only [bX, bD_r hh]
  exact div_self (ne_of_gt (bDelta_pos hh))

/-! ### Sharp values of the certificate -/

theorem bG_t (h θ : ℝ) : bG h θ (bt h) = -Real.sqrt (bDelta h / 6) := by
  simp only [bG, bX_t h, etaT_zero]
  ring

theorem bG_r (hh : 0 < h) : bG h θ (br h) = Real.sqrt (bDelta h / 6) := by
  simp only [bG, bX_r hh, etaT_one]
  ring

theorem sqrt_delta_sq (hh : 0 < h) :
    Real.sqrt (bDelta h / 6) * Real.sqrt (bDelta h / 6) = bDelta h / 6 :=
  Real.mul_self_sqrt (div_nonneg (bDelta_pos hh).le (by norm_num))

/-! ### The scalar excess identity -/

theorem bC_sub_bM2 (hh : 0 < h) :
    bC h - bM2 h = -(bDelta h) / 2 + bBeta h * (br h) ^ 2 / 3 := by
  have ht := bt_pos h
  have hz := bz_pos h
  have h1 := one_sub_bz_pos hh
  have hp : bp h = 2 * h * bz h / (1 - bz h) ^ 2 := rfl
  simp only [bC, bM2, bBeta, bAlpha, bDelta_eq, br, hp]
  field_simp
  ring

/-! ### Sharp values of Φ (G5) -/

theorem entropyF_rtt (hh : 0 < h) :
    entropyF (bAlpha h) (bG h θ) (br h) (bt h) (bt h) = bM2 h := by
  have hsq := sqrt_delta_sq (h := h) hh
  have hlogr := log_br hh
  have hlogt := log_bt hh
  have hdelta : bDelta h = bt h - br h := rfl
  simp only [entropyF, bG_r hh, bG_t h θ, H, hlogr, hlogt, bM2]
  linear_combination hsq + (1 / 6 : ℝ) * hdelta

/-! ### The stable gap identity (G7) -/

theorem gap_identity (hh : 0 < h) (w₁ w₂ w₃ : ℝ) :
    entropyF (bAlpha h) (bG h θ) w₁ w₂ w₃ - bM2 h
      = bDelta h / 6 *
          (2 * (bX h w₁ + bX h w₂ + bX h w₃)
            - (etaT θ (bX h w₁) * etaT θ (bX h w₂)
              + etaT θ (bX h w₁) * etaT θ (bX h w₃)
              + etaT θ (bX h w₂) * etaT θ (bX h w₃)) - 3)
        + bAlpha h * w₁ * w₂ * w₃
        - bBeta h / 3 * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2)
        + bBeta h * (br h) ^ 2 / 3 := by
  have hd : bDelta h ≠ 0 := ne_of_gt (bDelta_pos hh)
  have hsq := sqrt_delta_sq (h := h) hh
  have hH : ∀ w : ℝ, H w = bDelta h * bX h w - bBeta h * w ^ 2 + bC h := by
    intro w
    simp only [bX, bD]
    field_simp
    ring
  have hC := bC_sub_bM2 hh
  simp only [entropyF, bG, hH w₁, hH w₂, hH w₃]
  linear_combination
    (-(etaT θ (bX h w₁) * etaT θ (bX h w₂) + etaT θ (bX h w₁) * etaT θ (bX h w₃)
      + etaT θ (bX h w₂) * etaT θ (bX h w₃))) * hsq + hC

end
end Branch
end TriangleNumerical


/-!
# Spatial derivatives of the certificate (G8)

Section 5.1 of the blueprint.  For fixed branch parameters (`h` and the
auxiliary `θ`) we prove *actual Lean derivative theorems* — not symbolic
expressions — for

```
D'(w) = log w + 2 β w,            D''(w) = 1/w + 2 β,
η'(X) = 3 - 2X + θ(1 - 4X + 3X²), η''(X) = -2 + θ(6X - 4),
G'(w), G''(w),
```

and for the first and second spatial partial derivatives of

```
Φ(w₁,w₂,w₃) = (H w₁ + H w₂ + H w₃)/3 + α w₁w₂w₃
                - (G w₁ * G w₂ + G w₁ * G w₃ + G w₂ * G w₃).
```

The square roots hidden in `G` cancel in every displayed formula, so the
resulting expressions are rational in `log w`, the weights and the parameters
`α, Δ, β, θ`; this is exactly what the interval evaluator needs.

Only the differentiated coordinate has to be nonzero; the two frozen
coordinates are arbitrary reals.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Branch
noncomputable section

open Real

variable {h θ : ℝ}

/-! ### Derivatives of the cubic `η` -/

/-- `η'(X)`. -/
def etaD (θ X : ℝ) : ℝ := 3 - 2 * X + θ * (1 - 4 * X + 3 * X ^ 2)

/-- `η''(X)`. -/
def etaD2 (θ X : ℝ) : ℝ := -2 + θ * (6 * X - 4)

theorem hasDerivAt_etaT (θ X : ℝ) : HasDerivAt (etaT θ) (etaD θ X) X := by
  have h1 : HasDerivAt (fun x : ℝ => x) 1 X := hasDerivAt_id X
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * X) X := by simpa using h1.pow 2
  have h3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * X ^ 2) X := by simpa using h1.pow 3
  have h : HasDerivAt (fun x : ℝ => 3 * x - x ^ 2 - 1 + θ * (x - 2 * x ^ 2 + x ^ 3))
      (3 * 1 - 2 * X - 0 + θ * (1 - 2 * (2 * X) + 3 * X ^ 2)) X :=
    (((h1.const_mul 3).sub h2).sub (hasDerivAt_const X (1:ℝ))).add
      (((h1.sub (h2.const_mul 2)).add h3).const_mul θ)
  have hfun : (fun x : ℝ => 3 * x - x ^ 2 - 1 + θ * (x - 2 * x ^ 2 + x ^ 3)) = etaT θ := by
    funext x; simp only [etaT]; ring
  rw [hfun] at h
  convert h using 1
  simp only [etaD]; ring

theorem hasDerivAt_etaD (θ X : ℝ) : HasDerivAt (etaD θ) (etaD2 θ X) X := by
  have h1 : HasDerivAt (fun x : ℝ => x) 1 X := hasDerivAt_id X
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * X) X := by simpa using h1.pow 2
  have h : HasDerivAt (fun x : ℝ => 3 - 2 * x + θ * (1 - 4 * x + 3 * x ^ 2))
      (0 - 2 * 1 + θ * (0 - 4 * 1 + 3 * (2 * X))) X :=
    ((hasDerivAt_const X (3:ℝ)).sub (h1.const_mul 2)).add
      ((((hasDerivAt_const X (1:ℝ)).sub (h1.const_mul 4)).add (h2.const_mul 3)).const_mul θ)
  have hfun : (fun x : ℝ => 3 - 2 * x + θ * (1 - 4 * x + 3 * x ^ 2)) = etaD θ := rfl
  rw [hfun] at h
  convert h using 1
  simp only [etaD2]; ring

/-! ### Derivatives of the shape function `D` and of `X = D/Δ` -/

/-- `D'(w) = log w + 2 β w`. -/
def bDd (h w : ℝ) : ℝ := Real.log w + 2 * bBeta h * w

/-- `D''(w) = 1/w + 2 β`. -/
def bDd2 (h w : ℝ) : ℝ := 1 / w + 2 * bBeta h

theorem hasDerivAt_bD (h : ℝ) {w : ℝ} (hw : w ≠ 0) :
    HasDerivAt (bD h) (bDd h w) w := by
  have h1 : HasDerivAt (fun x : ℝ => x) 1 w := hasDerivAt_id w
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * w) w := by simpa using h1.pow 2
  have hd : HasDerivAt (fun x : ℝ => H x + bBeta h * x ^ 2 - bC h)
      (Real.log w + bBeta h * (2 * w)) w :=
    ((hasDerivAt_H hw).add (h2.const_mul (bBeta h))).sub_const _
  have hfun : (fun x : ℝ => H x + bBeta h * x ^ 2 - bC h) = bD h := rfl
  rw [hfun] at hd
  convert hd using 1
  simp only [bDd]; ring

theorem hasDerivAt_bDd (h : ℝ) {w : ℝ} (hw : w ≠ 0) :
    HasDerivAt (bDd h) (bDd2 h w) w := by
  have h1 : HasDerivAt (fun x : ℝ => x) 1 w := hasDerivAt_id w
  have hd : HasDerivAt (fun x : ℝ => Real.log x + 2 * bBeta h * x)
      (w⁻¹ + 2 * bBeta h * 1) w :=
    (Real.hasDerivAt_log hw).add (h1.const_mul (2 * bBeta h))
  have hfun : (fun x : ℝ => Real.log x + 2 * bBeta h * x) = bDd h := rfl
  rw [hfun] at hd
  convert hd using 1
  simp only [bDd2]
  rw [one_div]
  ring

theorem hasDerivAt_bX (h : ℝ) {w : ℝ} (hw : w ≠ 0) :
    HasDerivAt (bX h) (bDd h w / bDelta h) w :=
  (hasDerivAt_bD h hw).div_const _

/-! ### Derivatives of the certificate `G` -/

/-- `G'(w) = √(Δ/6) η'(X(w)) D'(w) / Δ`. -/
def bGd (h θ w : ℝ) : ℝ :=
  Real.sqrt (bDelta h / 6) * (etaD θ (bX h w) * (bDd h w / bDelta h))

/-- `G''(w) = √(Δ/6) (η''(X) D'(w)²/Δ² + η'(X) D''(w)/Δ)`. -/
def bGd2 (h θ w : ℝ) : ℝ :=
  Real.sqrt (bDelta h / 6) *
    (etaD2 θ (bX h w) * (bDd h w / bDelta h) ^ 2 + etaD θ (bX h w) * (bDd2 h w / bDelta h))

theorem hasDerivAt_bG (h θ : ℝ) {w : ℝ} (hw : w ≠ 0) :
    HasDerivAt (bG h θ) (bGd h θ w) w := by
  have h1 : HasDerivAt (fun x : ℝ => etaT θ (bX h x))
      (etaD θ (bX h w) * (bDd h w / bDelta h)) w :=
    (hasDerivAt_etaT θ (bX h w)).comp w (hasDerivAt_bX h hw)
  exact h1.const_mul _

theorem hasDerivAt_bGd (h θ : ℝ) {w : ℝ} (hw : w ≠ 0) :
    HasDerivAt (bGd h θ) (bGd2 h θ w) w := by
  have hX := hasDerivAt_bX h hw
  have h1 : HasDerivAt (fun x : ℝ => etaD θ (bX h x))
      (etaD2 θ (bX h w) * (bDd h w / bDelta h)) w :=
    (hasDerivAt_etaD θ (bX h w)).comp w hX
  have h2 : HasDerivAt (fun x : ℝ => bDd h x / bDelta h) (bDd2 h w / bDelta h) w :=
    (hasDerivAt_bDd h hw).div_const _
  have h3 : HasDerivAt (fun x : ℝ => etaD θ (bX h x) * (bDd h x / bDelta h))
      (etaD2 θ (bX h w) * (bDd h w / bDelta h) * (bDd h w / bDelta h)
        + etaD θ (bX h w) * (bDd2 h w / bDelta h)) w := h1.mul h2
  have h4 := h3.const_mul (Real.sqrt (bDelta h / 6))
  convert h4 using 1
  simp only [bGd2]; ring

/-! ### The spatial derivatives of `Φ` -/

/-- `∂₁Φ`. -/
def PhiD1 (h θ w₁ w₂ w₃ : ℝ) : ℝ :=
  Real.log w₁ / 3 + bAlpha h * w₂ * w₃
    - etaD θ (bX h w₁) * bDd h w₁ / 6 * (etaT θ (bX h w₂) + etaT θ (bX h w₃))

/-- The square-root cancellation used throughout: `√(Δ/6) * √(Δ/6) = Δ/6`. -/
theorem sqrtDelta_mul (hh : 0 < h) :
    Real.sqrt (bDelta h / 6) * Real.sqrt (bDelta h / 6) = bDelta h / 6 :=
  sqrt_delta_sq hh

/-- The product of `G'` at one point with `G` at two others, after the square
roots cancel. -/
theorem bGd_mul_bG (hh : 0 < h) (w₁ w₂ w₃ : ℝ) :
    bGd h θ w₁ * bG h θ w₂ + bGd h θ w₁ * bG h θ w₃
      = etaD θ (bX h w₁) * bDd h w₁ / 6 * (etaT θ (bX h w₂) + etaT θ (bX h w₃)) := by
  have hsq := sqrtDelta_mul (h := h) hh
  have hΔ : bDelta h ≠ 0 := ne_of_gt (bDelta_pos hh)
  simp only [bGd, bG]
  field_simp
  linear_combination (etaD θ (bX h w₁) * bDd h w₁ * 6 *
    (etaT θ (bX h w₂) + etaT θ (bX h w₃))) * hsq

/-- First partial derivative of `Φ` in its first coordinate. -/
theorem hasDerivAt_entropyF_1 (hh : 0 < h) {w₁ : ℝ} (hw : w₁ ≠ 0) (w₂ w₃ : ℝ) :
    HasDerivAt (fun x : ℝ => entropyF (bAlpha h) (bG h θ) x w₂ w₃)
      (PhiD1 h θ w₁ w₂ w₃) w₁ := by
  have hH : HasDerivAt (fun x : ℝ => (H x + H w₂ + H w₃) / 3) (Real.log w₁ / 3) w₁ :=
    (((hasDerivAt_H hw).add_const _).add_const _).div_const 3
  have hid : HasDerivAt (fun x : ℝ => x) 1 w₁ := hasDerivAt_id w₁
  have hcube : HasDerivAt (fun x : ℝ => bAlpha h * x * w₂ * w₃) (bAlpha h * w₂ * w₃) w₁ := by
    simpa using ((hid.const_mul (bAlpha h)).mul_const w₂).mul_const w₃
  have hG := hasDerivAt_bG h θ (w := w₁) hw
  have hpair : HasDerivAt
      (fun x : ℝ => bG h θ x * bG h θ w₂ + bG h θ x * bG h θ w₃ + bG h θ w₂ * bG h θ w₃)
      (bGd h θ w₁ * bG h θ w₂ + bGd h θ w₁ * bG h θ w₃) w₁ := by
    simpa using ((hG.mul_const (bG h θ w₂)).add (hG.mul_const (bG h θ w₃))).add_const
      (bG h θ w₂ * bG h θ w₃)
  have hmain : HasDerivAt (fun x : ℝ => entropyF (bAlpha h) (bG h θ) x w₂ w₃)
      (Real.log w₁ / 3 + bAlpha h * w₂ * w₃
        - (bGd h θ w₁ * bG h θ w₂ + bGd h θ w₁ * bG h θ w₃)) w₁ :=
    (hH.add hcube).sub hpair
  rw [bGd_mul_bG hh] at hmain
  exact hmain

/-! ### Symmetry of `Φ`

`entropyF` is a symmetric function of its three weights, so the formulas above
give every partial derivative after a permutation of the arguments. -/

theorem entropyF_swap12 (α : ℝ) (G : ℝ → ℝ) (a b c : ℝ) :
    entropyF α G a b c = entropyF α G b a c := by
  simp only [entropyF]; ring

theorem entropyF_swap23 (α : ℝ) (G : ℝ → ℝ) (a b c : ℝ) :
    entropyF α G a b c = entropyF α G a c b := by
  simp only [entropyF]; ring

/-- Second coordinate: derivative of `Φ` in `w₂`. -/
theorem hasDerivAt_entropyF_2 (hh : 0 < h) (w₁ : ℝ) {w₂ : ℝ} (hw : w₂ ≠ 0) (w₃ : ℝ) :
    HasDerivAt (fun y : ℝ => entropyF (bAlpha h) (bG h θ) w₁ y w₃)
      (PhiD1 h θ w₂ w₁ w₃) w₂ := by
  have h1 := hasDerivAt_entropyF_1 (h := h) (θ := θ) hh hw w₁ w₃
  have hfun : (fun y : ℝ => entropyF (bAlpha h) (bG h θ) y w₁ w₃)
      = fun y : ℝ => entropyF (bAlpha h) (bG h θ) w₁ y w₃ := by
    funext y; exact entropyF_swap12 _ _ _ _ _
  rwa [hfun] at h1

/-- Third coordinate: derivative of `Φ` in `w₃`. -/
theorem hasDerivAt_entropyF_3 (hh : 0 < h) (w₁ w₂ : ℝ) {w₃ : ℝ} (hw : w₃ ≠ 0) :
    HasDerivAt (fun z : ℝ => entropyF (bAlpha h) (bG h θ) w₁ w₂ z)
      (PhiD1 h θ w₃ w₁ w₂) w₃ := by
  have h1 := hasDerivAt_entropyF_1 (h := h) (θ := θ) hh hw w₁ w₂
  have hfun : (fun z : ℝ => entropyF (bAlpha h) (bG h θ) z w₁ w₂)
      = fun z : ℝ => entropyF (bAlpha h) (bG h θ) w₁ w₂ z := by
    funext z
    simp only [entropyF]; ring
  rwa [hfun] at h1

end
end Branch
end TriangleNumerical
