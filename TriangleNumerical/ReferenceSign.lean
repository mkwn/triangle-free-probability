import TriangleNumerical.RefDefs
import TriangleNumerical.ReferencePilot

/-!
# The reference sign (R1)

Section 12 of the blueprint: the constant competitor wins at the reference
parameter,
`M₁(α₀) ≤ M₂(h₀)`,
obtained root-free from the rational trial comparison (R0) and the exact
constant-excess identity (C2).
-/
set_option autoImplicit false
namespace TriangleNumerical
noncomputable section

open Real

/-- The two branch developments agree: the reference pilot's `alpha` is the
branch parameter `A(h)`. -/
theorem alpha_pilot_eq (h : ℝ) : TriangleReferencePilot.alpha h = Branch.bAlpha h := rfl

theorem M2_pilot_eq (h : ℝ) : TriangleReferencePilot.M2 h = Branch.bM2 h := rfl

/-- (R1): at the reference parameter the constant competitor value does not
exceed the branch value. -/
theorem reference_sign : M1 alphaRef sRef ≤ Branch.bM2 hRef := by
  obtain ⟨hs, _, hroot⟩ := sRef_spec
  have hα : (0:ℝ) ≤ alphaRef := le_of_lt alphaRef_pos
  -- the exact constant competitor value
  have h1 : M1 alphaRef sRef = H sRef + alphaRef * sRef ^ 3 :=
    (entropy_plus_cubic_eq_M1 hroot).symm
  -- the root-free trial bound (C2)
  have h2 : H sRef + alphaRef * sRef ^ 3
      ≤ H (53 / 200) + alphaRef * (53 / 200 : ℝ) ^ 3 :=
    constant_le_trial alphaRef sRef (53 / 200) hα hs (by norm_num) hroot
  -- the trial expression is the one appearing in (R0)
  have h3 : H (53 / 200 : ℝ) + alphaRef * (53 / 200 : ℝ) ^ 3
      = 1 - (53 / 200 : ℝ) + (53 / 200 : ℝ) * Real.log (53 / 200 : ℝ)
        + TriangleReferencePilot.alpha (939 / 100) * (53 / 200 : ℝ) ^ 3 := by
    simp only [H, alphaRef, hRef, alpha_pilot_eq]
  rw [h3] at h2
  have h4 := TriangleReferencePilot.reference_trial_comparison
  have h5 : TriangleReferencePilot.M2 (939 / 100) = Branch.bM2 hRef := by
    rw [M2_pilot_eq, hRef]
  rw [h5] at h4
  linarith

end
end TriangleNumerical
