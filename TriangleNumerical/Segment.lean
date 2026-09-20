import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A scalar segment lemma

If `f` has first derivative `f'` and second derivative `f''` on `[0,1)`, if
`f'' ≥ 0` there, if `f'(0) = 0` and `f` is continuous on `[0,1]`, then
`f 0 ≤ f 1`.

This is the one-dimensional restriction argument used in §7.2 and §8.3 of the
blueprint: no multivariable second-derivative machinery is needed, because the
objective restricted to a segment is a sum of products of functions of one
variable.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Segment

open Set

/-- The derivative is nonnegative on `[0,1)`. -/
theorem deriv_nonneg_of_second {f' f'' : ℝ → ℝ}
    (hd' : ∀ τ ∈ Ico (0:ℝ) 1, HasDerivAt f' (f'' τ) τ)
    (hpos : ∀ τ ∈ Ico (0:ℝ) 1, 0 ≤ f'' τ) (hzero : f' 0 = 0) :
    ∀ τ ∈ Ico (0:ℝ) 1, 0 ≤ f' τ := by
  intro τ hτ
  have hmono : MonotoneOn f' (Icc 0 τ) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro s hs
      have hs' : s ∈ Ico (0:ℝ) 1 := ⟨hs.1, lt_of_le_of_lt hs.2 hτ.2⟩
      exact ((hd' s hs').continuousAt).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs' : s ∈ Ico (0:ℝ) 1 := ⟨hs.1.le, lt_trans hs.2 hτ.2⟩
      exact (hd' s hs').differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs' : s ∈ Ico (0:ℝ) 1 := ⟨hs.1.le, lt_trans hs.2 hτ.2⟩
      rw [(hd' s hs').deriv]
      exact hpos s hs'
  have := hmono (mem_Icc.2 ⟨le_refl 0, hτ.1⟩) (mem_Icc.2 ⟨hτ.1, le_refl τ⟩) hτ.1
  rw [hzero] at this
  exact this

/-- The segment lemma. -/
theorem le_endpoint {f f' f'' : ℝ → ℝ}
    (hcont : ContinuousOn f (Icc 0 1))
    (hd : ∀ τ ∈ Ico (0:ℝ) 1, HasDerivAt f (f' τ) τ)
    (hd' : ∀ τ ∈ Ico (0:ℝ) 1, HasDerivAt f' (f'' τ) τ)
    (hpos : ∀ τ ∈ Ico (0:ℝ) 1, 0 ≤ f'' τ) (hzero : f' 0 = 0) :
    f 0 ≤ f 1 := by
  have hd'nonneg := deriv_nonneg_of_second (f' := f') (f'' := f'') hd' hpos hzero
  have hmono : MonotoneOn f (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont
    · intro s hs
      rw [interior_Icc] at hs
      exact (hd s ⟨hs.1.le, hs.2⟩).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hd s ⟨hs.1.le, hs.2⟩).deriv]
      exact hd'nonneg s ⟨hs.1.le, hs.2⟩
  exact hmono (mem_Icc.2 ⟨le_refl 0, by norm_num⟩) (mem_Icc.2 ⟨by norm_num, le_refl 1⟩)
    (by norm_num)

end Segment
end TriangleNumerical
