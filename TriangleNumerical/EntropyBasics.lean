import TriangleNumerical.Statement

/-!
Basic entropy lemmas used by the entropy-certificate proof.
The two proof bodies below are retained verbatim. The unrelated Q-coordinate
substitution and deduction have been removed.
-/
set_option autoImplicit false
namespace TriangleNumerical
noncomputable section

/-- Foundational estimate, including w=0; needed after rescaling above 1. -/
theorem entropy_nonnegative (w : ℝ) (hw : 0 ≤ w) : 0 ≤ H w := by
  rcases eq_or_lt_of_le hw with h | h
  · simp [H, ← h]
  · have hinv : Real.log (1 / w) ≤ 1 / w - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt h), Real.log_one] at hinv
    have hmul : w * (0 - Real.log w) ≤ w * (1 / w - 1) :=
      mul_le_mul_of_nonneg_left hinv hw
    have hinvw : w * (1 / w) = 1 := by field_simp
    simp only [H]
    nlinarith [hmul, hinvw]

/-- A polynomial identity. No domain hypotheses or integration are needed. -/
theorem twoBlock_averaging (α r t : ℝ) (G : ℝ → ℝ) :
    twoBlockObjective α r t =
      (entropyF α G r r r + 3 * entropyF α G r t t) / 4
        + (3 / 4 : ℝ) * (G r + G t) ^ 2 := by
  simp only [twoBlockObjective, entropyF]
  ring

end
end TriangleNumerical
