import TriangleNumerical.Subcritical
import TriangleNumerical.Deriv

/-!
# The reference parameter and the chosen constant roots

The reference branch parameter `h₀ = 9.39`, the parameter `α₀ = A(h₀)`, and a
choice of constant root at every nonnegative parameter.  These are separated
from `Assembly.lean` so that the reference sign (R1) can be proved before the
assembly uses it.
-/
set_option autoImplicit false
namespace TriangleNumerical
noncomputable section

/-- The reference branch parameter `h₀ = 9.39`. -/
def hRef : ℝ := 939 / 100

theorem hRef_pos : 0 < hRef := by norm_num [hRef]

/-- The reference parameter `α₀ = A(h₀)`. -/
def alphaRef : ℝ := Branch.bAlpha hRef

theorem alphaRef_pos : 0 < alphaRef := Branch.bAlpha_pos hRef_pos

/-- The constant root at the reference parameter. -/
def sRef : ℝ := Classical.choose (exists_constant_root (le_of_lt alphaRef_pos))

theorem sRef_spec : 0 < sRef ∧ sRef ≤ 1 ∧ rootResidual alphaRef sRef = 0 :=
  Classical.choose_spec (exists_constant_root (le_of_lt alphaRef_pos))

/-- The constant root at a nonnegative parameter, chosen once and for all. -/
def sAt {α : ℝ} (hα : 0 ≤ α) : ℝ := Classical.choose (exists_constant_root hα)

theorem sAt_spec {α : ℝ} (hα : 0 ≤ α) :
    0 < sAt hα ∧ sAt hα ≤ 1 ∧ rootResidual α (sAt hα) = 0 :=
  Classical.choose_spec (exists_constant_root hα)

end
end TriangleNumerical
