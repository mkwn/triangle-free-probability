import TriangleNumerical.EntropyBasics

/-!
Short algebraic milestones from the integrated shortcuts.
The last two statements are purely scalar inequalities: no matrix theory.
-/
set_option autoImplicit false
namespace TriangleNumerical
noncomputable section

/-- Exact excess over the constant competitor; w=0 must be handled explicitly. -/
theorem constant_excess_identity (α s w : ℝ)
    (hs : 0 < s) (hw : 0 ≤ w)
    (hroot : Real.log s + 3 * α * s ^ 2 = 0) :
    H w + α * w ^ 3 - (H s + α * s ^ 3) =
      s * H (w / s) + α * (w - s) ^ 2 * (w + 2 * s) := by
  rcases eq_or_lt_of_le hw with h | hwpos
  · -- w = 0
    subst_vars
    have : Real.log s = -(3 * α * s ^ 2) := by linarith
    simp only [H, zero_div, Real.log_zero]
    rw [this]
    ring
  · have hdiv : Real.log (w / s) = Real.log w - Real.log s :=
      Real.log_div (ne_of_gt hwpos) (ne_of_gt hs)
    have hlogs : Real.log s = -(3 * α * s ^ 2) := by linarith
    simp only [H, hdiv]
    field_simp
    rw [hlogs]
    ring

/-- The root-free rational trial bounds the exact constant competitor. -/
theorem constant_le_trial (α s w : ℝ)
    (hα : 0 ≤ α) (hs : 0 < s) (hw : 0 ≤ w)
    (hroot : Real.log s + 3 * α * s ^ 2 = 0) :
    H s + α * s ^ 3 ≤ H w + α * w ^ 3 := by
  have hid := constant_excess_identity α s w hs hw hroot
  have h1 : 0 ≤ s * H (w / s) :=
    mul_nonneg (le_of_lt hs) (entropy_nonnegative _ (by positivity))
  have h2 : 0 ≤ α * (w - s) ^ 2 * (w + 2 * s) := by positivity
  linarith

/-- Constant-neighborhood Hessian estimate, without matrices or determinants. -/
theorem scalar_diagonal_dominance (a b c d e f U V W : ℝ)
    (ha : 1 ≤ a) (hd : 1 ≤ d) (hf : 1 ≤ f)
    (hb : |b| ≤ (1 / 3 : ℝ)) (hc : |c| ≤ (1 / 3 : ℝ))
    (he : |e| ≤ (1 / 3 : ℝ)) :
    (U ^ 2 + V ^ 2 + W ^ 2) / 3 ≤
      a * U ^ 2 + 2 * b * U * V + 2 * c * U * W +
      d * V ^ 2 + 2 * e * V * W + f * W ^ 2 := by
  obtain ⟨hb1, hb2⟩ := abs_le.1 hb
  obtain ⟨hc1, hc2⟩ := abs_le.1 hc
  obtain ⟨he1, he2⟩ := abs_le.1 he
  nlinarith [sq_nonneg (U + V), sq_nonneg (U - V), sq_nonneg (U + W), sq_nonneg (U - W),
    sq_nonneg (V + W), sq_nonneg (V - W), sq_nonneg U, sq_nonneg V, sq_nonneg W]

/-- Mixed-neighborhood Hessian estimate by two squares, without a Schur complement. -/
theorem scalar_mixed_form (x a b c d e f U V W : ℝ)
    (hx : 0 < x) (ha : 1 / (3 * x) ≤ a)
    (hd : (8 / 25 : ℝ) ≤ d) (hf : (8 / 25 : ℝ) ≤ f)
    (he : |e| ≤ (1 / 100 : ℝ))
    (hb : x * b ^ 2 ≤ (1 / 25 : ℝ))
    (hc : x * c ^ 2 ≤ (1 / 25 : ℝ)) :
    U ^ 2 / (75 * x) + (V ^ 2 + W ^ 2) / 20 ≤
      a * U ^ 2 + 2 * b * U * V + 2 * c * U * W +
      d * V ^ 2 + 2 * e * V * W + f * W ^ 2 := by
  obtain ⟨he1, he2⟩ := abs_le.1 he
  -- two completed squares
  have h1 : 0 ≤ 4 * b ^ 2 * U ^ 2 + 2 * b * U * V + V ^ 2 / 4 := by
    nlinarith [sq_nonneg (2 * b * U + V / 2)]
  have h2 : 0 ≤ 4 * c ^ 2 * U ^ 2 + 2 * c * U * W + W ^ 2 / 4 := by
    nlinarith [sq_nonneg (2 * c * U + W / 2)]
  have h3 : -((1 / 100 : ℝ) * (V ^ 2 + W ^ 2)) ≤ 2 * e * V * W := by
    nlinarith [sq_nonneg (V + W), sq_nonneg (V - W)]
  -- the coefficient of U^2
  have hb' : b ^ 2 ≤ 1 / (25 * x) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hc' : c ^ 2 ≤ 1 / (25 * x) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hU : U ^ 2 / (75 * x) ≤ (a - 4 * b ^ 2 - 4 * c ^ 2) * U ^ 2 := by
    have hcoef : 1 / (75 * x) ≤ a - 4 * b ^ 2 - 4 * c ^ 2 := by
      have : 1 / (3 * x) - 4 * (1 / (25 * x)) - 4 * (1 / (25 * x)) = 1 / (75 * x) := by
        field_simp; ring
      linarith
    calc U ^ 2 / (75 * x) = (1 / (75 * x)) * U ^ 2 := by ring
      _ ≤ (a - 4 * b ^ 2 - 4 * c ^ 2) * U ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef (sq_nonneg U)
  nlinarith [sq_nonneg V, sq_nonneg W]

end
end TriangleNumerical
