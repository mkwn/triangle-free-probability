import TriangleNumerical.Deriv
import TriangleNumerical.LogLadder

/-!
# Scalar auxiliary estimates for the analytic local lemmas

Elementary one-variable facts used by the region-B analysis of §7 of the
blueprint:

* monotonicity of `x ↦ x log x` on `(0,1/4]` and of `x ↦ x (log x)²` on
  `(0,1/10]`, which replace any appeal to a series expansion near `0`;
* the quadratic Taylor bound `H u ≤ (10/19)(u-1)²` for `u ≥ 19/20`;
* a handful of explicit logarithm constants, including the uniform estimate
  `log (30 α²) ≤ 5 + α/3` for `α ≥ 6`.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Scalar
noncomputable section

open Real

/-! ### `x log x` and `x (log x)²` -/

/-- `x ↦ x log x` is antitone on `(0, 1/4]`. -/
theorem mul_log_antitoneOn : AntitoneOn (fun x : ℝ => x * Real.log x) (Set.Ioc 0 (1 / 4)) := by
  have hlt : Real.log (1 / 4 : ℝ) < -1 := by
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h2 : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
      rw [one_div, Real.log_inv]
    have h3 : (1:ℝ) < Real.log 4 := by
      have : Real.exp 1 < 4 := by linarith
      calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ < Real.log 4 := Real.log_lt_log (Real.exp_pos 1) this
    rw [h2]; linarith
  apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 (1 / 4))
  · exact Real.continuous_mul_log.continuousOn
  · intro x hx
    rw [interior_Ioc] at hx
    exact (Real.hasDerivAt_mul_log (ne_of_gt hx.1)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    rw [(Real.hasDerivAt_mul_log (ne_of_gt hx.1)).deriv]
    have : Real.log x ≤ Real.log (1 / 4 : ℝ) := Real.log_le_log hx.1 hx.2.le
    linarith

/-- `x (-log x) ≤ b (-log b)` for `0 ≤ x ≤ b ≤ 1/4`. -/
theorem mul_neg_log_le {x b : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b) (hb0 : 0 < b) (hb : b ≤ 1 / 4) :
    x * (-Real.log x) ≤ b * (-Real.log b) := by
  rcases eq_or_lt_of_le hx with h | hxpos
  · have hlogb : Real.log b < 0 := Real.log_neg hb0 (by linarith)
    rw [← h]
    simp only [Real.log_zero, neg_zero, mul_zero]
    nlinarith
  · have := mul_log_antitoneOn ⟨hxpos, le_trans hxb hb⟩ ⟨hb0, hb⟩ hxb
    simp only at this
    nlinarith

/-- `x ↦ x (log x)²` is monotone on `(0, 1/10]`. -/
theorem mul_log_sq_monotoneOn :
    MonotoneOn (fun x : ℝ => x * (Real.log x) ^ 2) (Set.Ioc 0 (1 / 10)) := by
  have hlt : Real.log (1 / 10 : ℝ) < -2 := by
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hsq : Real.exp 2 = (Real.exp 1) ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h2 : Real.exp 2 < 10 := by
      rw [hsq]; nlinarith [Real.exp_pos 1]
    have h3 : (2:ℝ) < Real.log 10 := by
      calc (2:ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
        _ < Real.log 10 := Real.log_lt_log (Real.exp_pos 2) h2
    rw [one_div, Real.log_inv]; linarith
  have hderiv : ∀ x : ℝ, x ≠ 0 →
      HasDerivAt (fun y : ℝ => y * (Real.log y) ^ 2)
        ((Real.log x) ^ 2 + x * (2 * Real.log x * x⁻¹)) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => (Real.log y) ^ 2) (2 * Real.log x * x⁻¹) x := by
      have := (Real.hasDerivAt_log hx).pow 2
      simpa using this
    simpa using (hasDerivAt_id x).mul h1
  apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 (1 / 10))
  · apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.pow
    exact Real.continuousOn_log.mono (by intro x hx; exact ne_of_gt hx.1)
  · intro x hx
    rw [interior_Ioc] at hx
    exact (hderiv x (ne_of_gt hx.1)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    rw [(hderiv x (ne_of_gt hx.1)).deriv]
    have hx0 : (0:ℝ) < x := hx.1
    have hlog : Real.log x ≤ Real.log (1 / 10 : ℝ) := Real.log_le_log hx0 hx.2.le
    have hlx : Real.log x < -2 := lt_of_le_of_lt hlog hlt
    have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hx0)
    have : (Real.log x) ^ 2 + x * (2 * Real.log x * x⁻¹)
        = (Real.log x) ^ 2 + 2 * Real.log x * (x * x⁻¹) := by ring
    rw [this, hxinv]
    nlinarith

theorem mul_log_sq_le {x b : ℝ} (hx : 0 < x) (hxb : x ≤ b) (hb : b ≤ 1 / 10) :
    x * (Real.log x) ^ 2 ≤ b * (Real.log b) ^ 2 :=
  mul_log_sq_monotoneOn ⟨hx, le_trans hxb hb⟩ ⟨lt_of_lt_of_le hx hxb, hb⟩ hxb

/-! ### The quadratic bound for `H` near `1` -/

/-- `H u ≤ (10/19)(u-1)²` for every `u ≥ 19/20`. -/
theorem H_le_quad {u : ℝ} (hu : 19 / 20 ≤ u) : H u ≤ 10 / 19 * (u - 1) ^ 2 := by
  set g : ℝ → ℝ := fun y => 10 / 19 * (y - 1) ^ 2 - H y with hg
  have hu0 : (0:ℝ) < u := by linarith
  -- derivative of g
  have hgd : ∀ y : ℝ, y ≠ 0 →
      HasDerivAt g (10 / 19 * (2 * (y - 1)) - Real.log y) y := by
    intro y hy
    have h1 : HasDerivAt (fun z : ℝ => 10 / 19 * (z - 1) ^ 2) (10 / 19 * (2 * (y - 1))) y := by
      have := ((hasDerivAt_id y).sub_const 1).pow 2
      simpa using (this.const_mul (10 / 19 : ℝ))
    exact h1.sub (hasDerivAt_H hy)
  set g' : ℝ → ℝ := fun y => 10 / 19 * (2 * (y - 1)) - Real.log y with hg'
  have hg'mono : MonotoneOn g' (Set.Ici (19 / 20 : ℝ)) := by
    have hd : ∀ y : ℝ, y ≠ 0 → HasDerivAt g' (20 / 19 - y⁻¹) y := by
      intro y hy
      have h1 : HasDerivAt (fun z : ℝ => 10 / 19 * (2 * (z - 1))) (20 / 19 : ℝ) y := by
        have h0 : (fun z : ℝ => 10 / 19 * (2 * (z - 1))) = fun z : ℝ => 20 / 19 * (z - 1) := by
          funext z; ring
        rw [h0]
        simpa using ((hasDerivAt_id y).sub_const 1).const_mul (20 / 19 : ℝ)
      simpa using h1.sub (Real.hasDerivAt_log hy)
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · apply ContinuousOn.sub (by fun_prop)
      exact Real.continuousOn_log.mono (by intro y hy; simp at hy ⊢; linarith)
    · intro y hy
      rw [interior_Ici] at hy
      simp only [Set.mem_Ioi] at hy
      exact (hd y (by linarith)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      simp only [Set.mem_Ioi] at hy
      rw [(hd y (by linarith)).deriv]
      have hy0 : (0:ℝ) < y := by linarith
      have : y⁻¹ ≤ 20 / 19 := by
        rw [inv_le_comm₀ hy0 (by norm_num)]
        linarith
      linarith
  have hg'one : g' 1 = 0 := by simp [hg']
  -- g is antitone on [19/20, 1] and monotone on [1, ∞)
  have hgcont : ContinuousOn g (Set.Ici (19 / 20 : ℝ)) := by
    apply ContinuousOn.sub (by fun_prop)
    exact continuous_H.continuousOn
  rcases le_total u 1 with hle | hge
  · have hanti : AntitoneOn g (Set.Icc (19 / 20 : ℝ) 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · exact hgcont.mono (by intro y hy; exact Set.mem_Ici.2 hy.1)
      · intro y hy
        rw [interior_Icc] at hy
        exact (hgd y (by linarith [hy.1])).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        rw [(hgd y (by linarith [hy.1])).deriv]
        have := hg'mono (Set.mem_Ici.2 (le_of_lt hy.1)) (Set.mem_Ici.2 (by norm_num)) hy.2.le
        simp only [hg'] at this ⊢
        rw [Real.log_one] at this
        linarith [this]
    have := hanti (Set.mem_Icc.2 ⟨hu, hle⟩) (Set.mem_Icc.2 ⟨by norm_num, le_refl 1⟩) hle
    have hg1 : g 1 = 0 := by simp [hg, H_one]
    simp only [hg] at this hg1
    linarith
  · have hmono : MonotoneOn g (Set.Ici (1 : ℝ)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici _)
      · exact hgcont.mono (by intro y hy; simp at hy ⊢; linarith)
      · intro y hy
        rw [interior_Ici] at hy
        simp only [Set.mem_Ioi] at hy
        exact (hgd y (by linarith)).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        simp only [Set.mem_Ioi] at hy
        rw [(hgd y (by linarith)).deriv]
        have := hg'mono (Set.mem_Ici.2 (by norm_num : (19/20:ℝ) ≤ 1))
          (Set.mem_Ici.2 (by linarith : (19/20:ℝ) ≤ y)) hy.le
        simp only [hg'] at this ⊢
        rw [Real.log_one] at this
        linarith [this]
    have := hmono (Set.mem_Ici.2 (le_refl 1)) (Set.mem_Ici.2 hge) hge
    have hg1 : g 1 = 0 := by simp [hg, H_one]
    simp only [hg] at this hg1
    linarith

/-! ### Explicit logarithm constants -/

theorem exp_seven_gt : (1090 : ℝ) < Real.exp 7 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : Real.exp 7 = (Real.exp 1) ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  calc (1090 : ℝ) < (2.7182818283 : ℝ) ^ 7 := by norm_num
    _ ≤ (Real.exp 1) ^ 7 := pow_le_pow_left₀ (by norm_num) h1.le 7

theorem exp_three_lt : Real.exp 3 < 21 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp 3 = (Real.exp 1) ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  calc (Real.exp 1) ^ 3 < (2.7182818286 : ℝ) ^ 3 :=
        pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
    _ < 21 := by norm_num

theorem log_1080_lt : Real.log 1080 < 7 := by
  have h : (1080 : ℝ) < Real.exp 7 := by linarith [exp_seven_gt]
  calc Real.log 1080 < Real.log (Real.exp 7) := Real.log_lt_log (by norm_num) h
    _ = 7 := Real.log_exp 7

theorem log_thirty_lt : Real.log 30 < 7 / 2 := by
  have h9 : (900 : ℝ) < Real.exp 7 := by linarith [exp_seven_gt]
  have hsq : Real.exp (7 / 2) ^ 2 = Real.exp 7 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h30 : (30 : ℝ) < Real.exp (7 / 2) := by
    by_contra hcon
    push_neg at hcon
    have hpos : (0:ℝ) < Real.exp (7 / 2) := Real.exp_pos _
    have := pow_le_pow_left₀ hpos.le hcon 2
    rw [hsq] at this
    norm_num at this
    linarith
  calc Real.log 30 < Real.log (Real.exp (7 / 2)) := Real.log_lt_log (by norm_num) h30
    _ = 7 / 2 := Real.log_exp _

theorem log_thirty_gt : (3 : ℝ) < Real.log 30 := by
  have h : Real.exp 3 < 30 := by linarith [exp_three_lt]
  calc (3:ℝ) = Real.log (Real.exp 3) := (Real.log_exp 3).symm
    _ < Real.log 30 := Real.log_lt_log (Real.exp_pos 3) h

/-- Uniform bound for the logarithm appearing at the convex-box endpoint
`L = 1/(30α²)`: for every `α ≥ 6`, `log (30 α²) ≤ 5 + α/3`. -/
theorem log_thirty_sq_le {α : ℝ} (hα : 6 ≤ α) : Real.log (30 * α ^ 2) ≤ 5 + α / 3 := by
  have hα0 : (0:ℝ) < α := by linarith
  have hfac : (30 : ℝ) * α ^ 2 = 1080 * (α / 6) ^ 2 := by ring
  have hq : (1:ℝ) ≤ α / 6 := by linarith
  have hlog : Real.log (30 * α ^ 2) = Real.log 1080 + 2 * Real.log (α / 6) := by
    rw [hfac, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have hle : Real.log (α / 6) ≤ α / 6 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [hlog]
  linarith [log_1080_lt]

/-- `log (20/19) ≤ 39/760`, from the Padé upper seed. -/
theorem log_twentieth_le : Real.log (20 / 19 : ℝ) ≤ 39 / 760 := by
  have h := TriangleLogCertificate.log_le_upper_seed (20 / 19 : ℝ) (by norm_num)
  simp only [TriangleLogCertificate.upperSeed] at h
  norm_num at h ⊢
  linarith

/-- `-log w ≤ 39/760` for `19/20 ≤ w ≤ 1`: the logarithm is tiny on the high
coordinate range. -/
theorem neg_log_high_le {w : ℝ} (hw : 19 / 20 ≤ w) :
    -Real.log w ≤ 39 / 760 := by
  have h1 : Real.log (19 / 20 : ℝ) ≤ Real.log w := Real.log_le_log (by norm_num) hw
  have h2 : Real.log (19 / 20 : ℝ) = -Real.log (20 / 19 : ℝ) := by
    rw [show (19 / 20 : ℝ) = (20 / 19 : ℝ)⁻¹ by norm_num, Real.log_inv]
  linarith [log_twentieth_le]

end
end Scalar
end TriangleNumerical
