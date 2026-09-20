import TriangleNumerical.Deriv

/-!
# Analytic region A: all three weights at most 1/10

Section 6 of the blueprint (A1).  For every `h ≥ 9` and every
`-1/50 ≤ θ ≤ 0`,

```
w ∈ [0, 1/10]³  ⟹  Φ_{A(h), G_{h,θ}}(w) ≥ M₂(h).
```

The proof is quantitative and needs no subdivision near the exponentially
small `r`.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Branch
noncomputable section

open Real

variable {h θ : ℝ}

/-! ### Scalar lemmas -/

theorem pairwise_le_sq (b₁ b₂ b₃ : ℝ) :
    b₁ * b₂ + b₁ * b₃ + b₂ * b₃ ≤ b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2 := by
  nlinarith [sq_nonneg (b₁ - b₂), sq_nonneg (b₁ - b₃), sq_nonneg (b₂ - b₃)]

/-- The cubic term of the AM–GM defect is controlled when all weights are
nonnegative (each displacement is at least `-r`). -/
theorem cube_product_lower {r δ₁ δ₂ δ₃ : ℝ} (hr : 0 < r)
    (h₁ : -r ≤ δ₁) (h₂ : -r ≤ δ₂) (h₃ : -r ≤ δ₃) :
    -(r / 2) * (δ₁ ^ 2 + δ₂ ^ 2 + δ₃ ^ 2) ≤ δ₁ * δ₂ * δ₃ := by
  rcases le_or_gt 0 δ₁ with p₁ | n₁ <;> rcases le_or_gt 0 δ₂ with p₂ | n₂ <;>
    rcases le_or_gt 0 δ₃ with p₃ | n₃
  · nlinarith [mul_nonneg (mul_nonneg p₁ p₂) p₃, sq_nonneg δ₁, sq_nonneg δ₂, sq_nonneg δ₃]
  · nlinarith [sq_nonneg (δ₁ - δ₂), sq_nonneg (δ₁ + δ₂), mul_nonneg p₁ p₂, sq_nonneg δ₃]
  · nlinarith [sq_nonneg (δ₁ - δ₃), sq_nonneg (δ₁ + δ₃), mul_nonneg p₁ p₃, sq_nonneg δ₂]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ -δ₂) (by linarith : (0:ℝ) ≤ -δ₃),
      sq_nonneg δ₁, sq_nonneg δ₂, sq_nonneg δ₃]
  · nlinarith [sq_nonneg (δ₂ - δ₃), sq_nonneg (δ₂ + δ₃), mul_nonneg p₂ p₃, sq_nonneg δ₁]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ -δ₁) (by linarith : (0:ℝ) ≤ -δ₃),
      sq_nonneg δ₁, sq_nonneg δ₂, sq_nonneg δ₃]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ -δ₁) (by linarith : (0:ℝ) ≤ -δ₂),
      sq_nonneg δ₁, sq_nonneg δ₂, sq_nonneg δ₃]
  · nlinarith [sq_nonneg (δ₂ - δ₃), sq_nonneg (δ₂ + δ₃), sq_nonneg δ₁]

/-- `ℓ(y) ≥ y²` and `|b(y)| ≤ (27/20)|y|` for `|y| ≤ 17/50`, `-1/50 ≤ θ ≤ 0`. -/
theorem b_bounds {y : ℝ} (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hl : -(17 / 50 : ℝ) ≤ y) (hu : y ≤ 17 / 50) :
    y ^ 2 ≤ (1 - θ + θ * y) * y ^ 2 ∧
      (y + (1 - θ + θ * y) * y ^ 2) ^ 2 ≤ 729 / 400 * y ^ 2 := by
  have hθn : 0 ≤ -θ := by linarith
  have h1y : (0:ℝ) ≤ 1 - y := by linarith
  refine ⟨by nlinarith [mul_nonneg (mul_nonneg hθn h1y) (sq_nonneg y)], ?_⟩
  have hfac : |1 + (1 - θ + θ * y) * y| ≤ 27 / 20 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg y, mul_nonneg hθn h1y]
  have heq : y + (1 - θ + θ * y) * y ^ 2 = y * (1 + (1 - θ + θ * y) * y) := by ring
  have h3 : (y + (1 - θ + θ * y) * y ^ 2) ^ 2 ≤ (27 / 20 * |y|) ^ 2 := by
    rw [← sq_abs, heq, abs_mul, mul_comm]
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_right hfac (abs_nonneg y)
  calc (y + (1 - θ + θ * y) * y ^ 2) ^ 2 ≤ (27 / 20 * |y|) ^ 2 := h3
    _ = 729 / 400 * y ^ 2 := by rw [mul_pow, sq_abs]; ring

/-- The quadratic lower bound for `P` on the small region. -/
theorem P_lower_bound {X₁ X₂ X₃ : ℝ} (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (h₁ : |1 - X₁| ≤ 17 / 50) (h₂ : |1 - X₂| ≤ 17 / 50) (h₃ : |1 - X₃| ≤ 17 / 50) :
    71 / 400 * ((1 - X₁) ^ 2 + (1 - X₂) ^ 2 + (1 - X₃) ^ 2)
      ≤ 2 * (X₁ + X₂ + X₃) - (etaT θ X₁ * etaT θ X₂ + etaT θ X₁ * etaT θ X₃
          + etaT θ X₂ * etaT θ X₃) - 3 := by
  obtain ⟨hl₁, hu₁⟩ := abs_le.1 h₁
  obtain ⟨hl₂, hu₂⟩ := abs_le.1 h₂
  obtain ⟨hl₃, hu₃⟩ := abs_le.1 h₃
  obtain ⟨ha₁, hb₁⟩ := b_bounds hθ1 hθ0 hl₁ hu₁
  obtain ⟨ha₂, hb₂⟩ := b_bounds hθ1 hθ0 hl₂ hu₂
  obtain ⟨ha₃, hb₃⟩ := b_bounds hθ1 hθ0 hl₃ hu₃
  have hid : 2 * (X₁ + X₂ + X₃) - (etaT θ X₁ * etaT θ X₂ + etaT θ X₁ * etaT θ X₃
          + etaT θ X₂ * etaT θ X₃) - 3
      = 2 * ((1 - θ + θ * (1 - X₁)) * (1 - X₁) ^ 2 + (1 - θ + θ * (1 - X₂)) * (1 - X₂) ^ 2
             + (1 - θ + θ * (1 - X₃)) * (1 - X₃) ^ 2)
        - (((1 - X₁) + (1 - θ + θ * (1 - X₁)) * (1 - X₁) ^ 2)
             * ((1 - X₂) + (1 - θ + θ * (1 - X₂)) * (1 - X₂) ^ 2)
          + ((1 - X₁) + (1 - θ + θ * (1 - X₁)) * (1 - X₁) ^ 2)
             * ((1 - X₃) + (1 - θ + θ * (1 - X₃)) * (1 - X₃) ^ 2)
          + ((1 - X₂) + (1 - θ + θ * (1 - X₂)) * (1 - X₂) ^ 2)
             * ((1 - X₃) + (1 - θ + θ * (1 - X₃)) * (1 - X₃) ^ 2)) := by
    simp only [etaT]; ring
  rw [hid]
  have hpair := pairwise_le_sq ((1 - X₁) + (1 - θ + θ * (1 - X₁)) * (1 - X₁) ^ 2)
    ((1 - X₂) + (1 - θ + θ * (1 - X₂)) * (1 - X₂) ^ 2)
    ((1 - X₃) + (1 - θ + θ * (1 - X₃)) * (1 - X₃) ^ 2)
  linarith

/-- The final quantitative combination. -/
theorem local_small_core {Δ ar S P AT : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (har0 : 0 ≤ ar) (har : ar ≤ 1 / 750) (hS : 0 ≤ S)
    (hP : 71 / 400 * S ≤ P) (hAT : -(3 / 2 * ar * (Δ ^ 2 / 4) * S) ≤ AT) :
    0 ≤ Δ / 6 * P + AT := by
  have h1 : Δ / 6 * (71 / 400 * S) ≤ Δ / 6 * P :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  have hΔsq : Δ ^ 2 ≤ Δ := by nlinarith
  have h2 : 3 / 2 * ar * (Δ ^ 2 / 4) * S ≤ 3 / 2 * (1 / 750) * (Δ / 4) * S := by
    nlinarith [mul_nonneg hS hΔ0.le, mul_nonneg hS har0, mul_nonneg (mul_nonneg hS har0) hΔ0.le]
  have h3 : 0 ≤ Δ * S * (71 / 2400 - 1 / 2000) :=
    mul_nonneg (mul_nonneg hΔ0.le hS) (by norm_num)
  linarith

/-! ### The scalar logarithm constants -/

theorem log_ten_lt : Real.log 10 < 7 / 3 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h7 : (1000 : ℝ) < Real.exp 7 := by
    have h2 : Real.exp 7 = (Real.exp 1) ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    calc (1000 : ℝ) < (2.7182818283 : ℝ) ^ 7 := by norm_num
      _ ≤ (Real.exp 1) ^ 7 := pow_le_pow_left₀ (by norm_num) h1.le 7
  have hcube : (Real.exp (7 / 3)) ^ 3 = Real.exp 7 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h10 : (10 : ℝ) < Real.exp (7 / 3) := by
    by_contra hcon
    push_neg at hcon
    have hpos : (0:ℝ) < Real.exp (7 / 3) := Real.exp_pos _
    have hle : (Real.exp (7 / 3)) ^ 3 ≤ (10 : ℝ) ^ 3 := pow_le_pow_left₀ hpos.le hcon 3
    rw [hcube] at hle
    norm_num at hle
    linarith
  calc Real.log 10 < Real.log (Real.exp (7 / 3)) := Real.log_lt_log (by norm_num) h10
    _ = 7 / 3 := Real.log_exp _

theorem log_ten_gt : (23 / 10 : ℝ) < Real.log 10 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h23 : Real.exp 23 = (Real.exp 1) ^ 23 := by rw [← Real.exp_nat_mul]; norm_num
  have hlt : Real.exp 23 < 10 ^ 10 := by
    rw [h23]
    calc (Real.exp 1) ^ 23 < (2.7182818286 : ℝ) ^ 23 :=
          pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
      _ < 10 ^ 10 := by norm_num
  have hpow : (Real.exp (23 / 10)) ^ 10 = Real.exp 23 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h10 : Real.exp (23 / 10) < 10 := by
    by_contra hcon
    push_neg at hcon
    have hge : (10:ℝ) ^ 10 ≤ (Real.exp (23 / 10)) ^ 10 := pow_le_pow_left₀ (by norm_num) hcon 10
    rw [hpow] at hge
    linarith
  calc (23 / 10 : ℝ) = Real.log (Real.exp (23 / 10)) := (Real.log_exp _).symm
    _ < Real.log 10 := Real.log_lt_log (Real.exp_pos _) h10

theorem log_tenth_gt : -(7 / 3 : ℝ) < Real.log (1 / 10) := by
  rw [one_div, Real.log_inv]; linarith [log_ten_lt]

theorem log_tenth_lt : Real.log (1 / 10 : ℝ) < -(23 / 10) := by
  rw [one_div, Real.log_inv]; linarith [log_ten_gt]

theorem H_tenth_gt : (2 / 3 : ℝ) < H (1 / 10) := by
  simp only [H]
  nlinarith [log_tenth_gt]

/-! ### Bounds on X on the small region -/

theorem bX_upper (hh : 9 ≤ h) {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 1 / 10) :
    bX h w < 1011 / 1000 := by
  have hhpos : (0:ℝ) < h := by linarith
  have hHle : H w ≤ 1 := by
    have hmono := H_antitoneOn (Set.mem_Icc.2 ⟨le_refl (0:ℝ), by norm_num⟩)
      (Set.mem_Icc.2 ⟨hw0, by linarith⟩) hw0
    simpa [H] using hmono
  have hβ := bBeta_lt hh
  have hβ0 := bBeta_pos hh
  have hC0 := bC_pos hh
  have hΔ := bDelta_gt hh
  have hnum : H w + bBeta h * w ^ 2 - bC h < 1 + 1 / 50000 := by
    nlinarith
  rw [bX, bD, div_lt_iff₀ (by linarith)]
  linarith

theorem bX_lower (hh : 9 ≤ h) {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 1 / 10) :
    33 / 50 < bX h w := by
  have hhpos : (0:ℝ) < h := by linarith
  have hHge : (2 / 3 : ℝ) < H w := by
    have hmono := H_antitoneOn (Set.mem_Icc.2 ⟨hw0, by linarith⟩)
      (Set.mem_Icc.2 ⟨by norm_num, by norm_num⟩) hw
    linarith [H_tenth_gt]
  have hβ0 := bBeta_pos hh
  have hC := bC_lt hh
  have hΔ1 := bDelta_lt_one hhpos
  have hΔ0 := bDelta_pos hhpos
  rw [bX, bD, lt_div_iff₀ hΔ0]
  nlinarith [mul_nonneg hβ0.le (sq_nonneg w)]

theorem abs_one_sub_bX (hh : 9 ≤ h) {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 1 / 10) :
    |1 - bX h w| ≤ 17 / 50 := by
  rw [abs_le]
  exact ⟨by linarith [bX_upper hh hw0 hw], by linarith [bX_lower hh hw0 hw]⟩

/-! ### The mean value estimate -/

theorem br_le_tenth (hh : 9 ≤ h) : br h ≤ 1 / 10 := by
  have hhpos : (0:ℝ) < h := by linarith
  have h1 := bz_lt hh
  have h2 := bt_lt_one hhpos
  have h3 := bz_pos h
  have h4 := bt_pos h
  rw [br]
  nlinarith

/-- `D(w) + 2w` is antitone on `[0, 1/10]`: the shape function decreases at
speed at least `2`. -/
theorem bD_shift_antitone (hh : 9 ≤ h) :
    AntitoneOn (fun w : ℝ => bD h w + 2 * w) (Set.Icc 0 (1 / 10)) := by
  have hβ0 := bBeta_pos hh
  have hβ := bBeta_lt hh
  have hderiv : ∀ x : ℝ, x ≠ 0 →
      HasDerivAt (fun w : ℝ => bD h w + 2 * w)
        ((Real.log x + bBeta h * (2 * x ^ 1)) + 2 * 1) x := by
    intro x hx0
    have h1 : HasDerivAt (fun w : ℝ => H w + bBeta h * w ^ 2 - bC h)
        (Real.log x + bBeta h * (2 * x ^ 1)) x :=
      ((hasDerivAt_H hx0).add ((hasDerivAt_pow 2 x).const_mul (bBeta h))).sub_const (bC h)
    exact h1.add ((hasDerivAt_id x).const_mul 2)
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 (1 / 10))
  · apply ContinuousOn.add _ (by fun_prop)
    exact ((continuous_H.add (continuous_const.mul (continuous_pow 2))).sub
      continuous_const).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (hderiv x (ne_of_gt hx.1)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hderiv x (ne_of_gt hx.1)).deriv]
    have hlog : Real.log x < -(23 / 10) :=
      lt_of_le_of_lt (Real.log_le_log hx.1 hx.2.le) log_tenth_lt
    have hx0 : (0:ℝ) < x := hx.1
    have hx1 : x ≤ 1 / 10 := hx.2.le
    have hbx : bBeta h * (2 * x ^ 1) ≤ 1 / 2500 := by
      have h1 : bBeta h * (2 * x ^ 1) ≤ (1 / 500) * (2 * x ^ 1) := by
        apply mul_le_mul_of_nonneg_right hβ.le (by simp; linarith)
      have h2 : (1 / 500 : ℝ) * (2 * x ^ 1) ≤ (1 / 500) * (2 * (1 / 10)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simp; linarith
      linarith
    linarith

/-- Mean value estimate: `|w - r| ≤ (Δ/2)|1 - X(w)|` on the small region. -/
theorem mvt_small (hh : 9 ≤ h) {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 1 / 10) :
    |w - br h| ≤ bDelta h / 2 * |1 - bX h w| := by
  have hhpos : (0:ℝ) < h := by linarith
  have hr0 : 0 < br h := br_pos h
  have hr := br_le_tenth hh
  have hΔ0 := bDelta_pos hhpos
  have hDw : bD h w = bDelta h * bX h w := by
    rw [bX]; field_simp
  have hDr : bD h (br h) = bDelta h := bD_r hhpos
  have hmono := bD_shift_antitone hh
  have hmemw : w ∈ Set.Icc (0:ℝ) (1 / 10) := Set.mem_Icc.2 ⟨hw0, hw⟩
  have hmemr : br h ∈ Set.Icc (0:ℝ) (1 / 10) := Set.mem_Icc.2 ⟨hr0.le, hr⟩
  rcases le_total w (br h) with hle | hge
  · have hstep : bD h (br h) + 2 * br h ≤ bD h w + 2 * w := hmono hmemw hmemr hle
    rw [hDw, hDr] at hstep
    have hX1 : 1 ≤ bX h w := by nlinarith
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    nlinarith
  · have hstep : bD h w + 2 * w ≤ bD h (br h) + 2 * br h := hmono hmemr hmemw hge
    rw [hDw, hDr] at hstep
    have hX1 : bX h w ≤ 1 := by nlinarith
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    nlinarith

theorem displacement_sq (hh : 9 ≤ h) {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 1 / 10) :
    (w - br h) ^ 2 ≤ bDelta h ^ 2 / 4 * (1 - bX h w) ^ 2 := by
  have hmv := mvt_small hh hw0 hw
  have h1 : |w - br h| ^ 2 ≤ (bDelta h / 2 * |1 - bX h w|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hmv 2
  rw [sq_abs] at h1
  calc (w - br h) ^ 2 ≤ (bDelta h / 2 * |1 - bX h w|) ^ 2 := h1
    _ = bDelta h ^ 2 / 4 * |1 - bX h w| ^ 2 := by ring
    _ = bDelta h ^ 2 / 4 * (1 - bX h w) ^ 2 := by rw [sq_abs]

/-! ### The local lower bound (A1) -/

theorem local_small_region (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    {w₁ w₂ w₃ : ℝ} (hw₁ : 0 ≤ w₁) (hw₁' : w₁ ≤ 1 / 10)
    (hw₂ : 0 ≤ w₂) (hw₂' : w₂ ≤ 1 / 10) (hw₃ : 0 ≤ w₃) (hw₃' : w₃ ≤ 1 / 10) :
    bM2 h ≤ entropyF (bAlpha h) (bG h θ) w₁ w₂ w₃ := by
  have hhpos : (0:ℝ) < h := by linarith
  have hΔ0 := bDelta_pos hhpos
  have hΔ1 := bDelta_lt_one hhpos
  have hr0 : 0 < br h := br_pos h
  have hα0 : 0 < bAlpha h := bAlpha_pos hhpos
  have hβeq := bBeta_eq hhpos
  have hβlt := bBeta_lt hh
  have hαr : bAlpha h * br h ≤ 1 / 750 := by rw [hβeq] at hβlt; linarith
  have hαr0 : 0 ≤ bAlpha h * br h := (mul_pos hα0 hr0).le
  -- the P bound
  have hP := P_lower_bound (θ := θ) (X₁ := bX h w₁) (X₂ := bX h w₂) (X₃ := bX h w₃)
    hθ1 hθ0 (abs_one_sub_bX hh hw₁ hw₁') (abs_one_sub_bX hh hw₂ hw₂')
    (abs_one_sub_bX hh hw₃ hw₃')
  -- the displacement bound
  have hd₁ := displacement_sq hh hw₁ hw₁'
  have hd₂ := displacement_sq hh hw₂ hw₂'
  have hd₃ := displacement_sq hh hw₃ hw₃'
  have hS0 : 0 ≤ (1 - bX h w₁) ^ 2 + (1 - bX h w₂) ^ 2 + (1 - bX h w₃) ^ 2 := by positivity
  have hdsum : (w₁ - br h) ^ 2 + (w₂ - br h) ^ 2 + (w₃ - br h) ^ 2
      ≤ bDelta h ^ 2 / 4
        * ((1 - bX h w₁) ^ 2 + (1 - bX h w₂) ^ 2 + (1 - bX h w₃) ^ 2) := by
    have : bDelta h ^ 2 / 4 * ((1 - bX h w₁) ^ 2 + (1 - bX h w₂) ^ 2 + (1 - bX h w₃) ^ 2)
        = bDelta h ^ 2 / 4 * (1 - bX h w₁) ^ 2 + bDelta h ^ 2 / 4 * (1 - bX h w₂) ^ 2
          + bDelta h ^ 2 / 4 * (1 - bX h w₃) ^ 2 := by ring
    rw [this]; linarith
  -- the AM-GM defect
  have hT : -(3 * br h / 2) * ((w₁ - br h) ^ 2 + (w₂ - br h) ^ 2 + (w₃ - br h) ^ 2)
      ≤ w₁ * w₂ * w₃ - br h / 2 * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2) + (br h) ^ 3 / 2 := by
    have hc := cube_product_lower (r := br h) (δ₁ := w₁ - br h) (δ₂ := w₂ - br h)
      (δ₃ := w₃ - br h) hr0 (by linarith) (by linarith) (by linarith)
    have hid : w₁ * w₂ * w₃ - br h / 2 * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2) + (br h) ^ 3 / 2
        = br h * (((w₁ - br h) + (w₂ - br h) + (w₃ - br h)) ^ 2 / 2
            - ((w₁ - br h) ^ 2 + (w₂ - br h) ^ 2 + (w₃ - br h) ^ 2))
          + (w₁ - br h) * (w₂ - br h) * (w₃ - br h) := by ring
    rw [hid]
    nlinarith [hc, mul_nonneg hr0.le
      (sq_nonneg ((w₁ - br h) + (w₂ - br h) + (w₃ - br h)))]
  -- the α T bound
  have hAT : -(3 / 2 * (bAlpha h * br h) * (bDelta h ^ 2 / 4)
        * ((1 - bX h w₁) ^ 2 + (1 - bX h w₂) ^ 2 + (1 - bX h w₃) ^ 2))
      ≤ bAlpha h * (w₁ * w₂ * w₃ - br h / 2 * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2) + (br h) ^ 3 / 2) := by
    have h1 : bAlpha h * (-(3 * br h / 2)
        * ((w₁ - br h) ^ 2 + (w₂ - br h) ^ 2 + (w₃ - br h) ^ 2))
        ≤ bAlpha h * (w₁ * w₂ * w₃ - br h / 2 * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2)
          + (br h) ^ 3 / 2) := mul_le_mul_of_nonneg_left hT hα0.le
    have h2 : 3 / 2 * (bAlpha h * br h)
        * ((w₁ - br h) ^ 2 + (w₂ - br h) ^ 2 + (w₃ - br h) ^ 2)
        ≤ 3 / 2 * (bAlpha h * br h) * (bDelta h ^ 2 / 4
          * ((1 - bX h w₁) ^ 2 + (1 - bX h w₂) ^ 2 + (1 - bX h w₃) ^ 2)) :=
      mul_le_mul_of_nonneg_left hdsum (by positivity)
    linarith
  -- combine through the gap identity
  have hgap := gap_identity (h := h) (θ := θ) hhpos w₁ w₂ w₃
  have hTeq : bAlpha h * w₁ * w₂ * w₃ - bBeta h / 3 * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2)
      + bBeta h * (br h) ^ 2 / 3
      = bAlpha h * (w₁ * w₂ * w₃ - br h / 2 * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2)
          + (br h) ^ 3 / 2) := by
    rw [hβeq]; ring
  have hcore := local_small_core (Δ := bDelta h) (ar := bAlpha h * br h)
    (S := (1 - bX h w₁) ^ 2 + (1 - bX h w₂) ^ 2 + (1 - bX h w₃) ^ 2)
    (P := 2 * (bX h w₁ + bX h w₂ + bX h w₃)
      - (etaT θ (bX h w₁) * etaT θ (bX h w₂) + etaT θ (bX h w₁) * etaT θ (bX h w₃)
        + etaT θ (bX h w₂) * etaT θ (bX h w₃)) - 3)
    (AT := bAlpha h * (w₁ * w₂ * w₃ - br h / 2 * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2)
      + (br h) ^ 3 / 2))
    hΔ0 hΔ1.le hαr0 hαr hS0 hP hAT
  linarith [hgap, hcore, hTeq]

end
end Branch
end TriangleNumerical
