import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TriangleNumerical.AlgebraTasks

/-!
# Entropy facts, the constant root, and the minimum criterion

Section 3 of the blueprint: continuity and derivatives of `H`, existence and
uniqueness of the constant root `s` of `log s + 3 α s² = 0`, the constant
competitor value `M₁`, and the general criterion turning a cube lower bound
plus an attaining pair into `IsTwoBlockMinimum`.
-/
set_option autoImplicit false
namespace TriangleNumerical
noncomputable section

open Real

/-! ## Entropy basics -/

theorem H_one : H 1 = 0 := by simp [H]

theorem continuous_H : Continuous H := by
  have : H = fun w => 1 - w + w * Real.log w := rfl
  rw [this]
  exact (continuous_const.sub continuous_id).add Real.continuous_mul_log

theorem hasDerivAt_H {w : ℝ} (hw : w ≠ 0) : HasDerivAt H (Real.log w) w := by
  have h1 : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log w + 1) w := by
    simpa using (Real.hasDerivAt_mul_log hw)
  have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  simpa using h2.add h1

/-- `H` is nonincreasing on `(0,1]` and nondecreasing on `[1,∞)`; we only need
the monotone-decreasing part on `[0,1]`. -/
theorem H_antitoneOn : AntitoneOn H (Set.Icc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1) continuous_H.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_H (ne_of_gt hx.1)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_H (ne_of_gt hx.1)).deriv]
    exact Real.log_nonpos (le_of_lt hx.1) (le_of_lt hx.2)

/-! ## The constant root -/

/-- The residual whose zero defines the constant root. -/
def rootResidual (α s : ℝ) : ℝ := Real.log s + 3 * α * s ^ 2

theorem rootResidual_strictMonoOn {α : ℝ} (hα : 0 ≤ α) :
    StrictMonoOn (rootResidual α) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : (0:ℝ) < x := hx
  have hlog : Real.log x < Real.log y := Real.log_lt_log hx0 hxy
  have hsq : 3 * α * x ^ 2 ≤ 3 * α * y ^ 2 := by
    have : x ^ 2 ≤ y ^ 2 := by nlinarith
    nlinarith
  simp only [rootResidual]
  linarith

/-- Existence of the constant root in `(0,1]`. -/
theorem exists_constant_root {α : ℝ} (hα : 0 ≤ α) :
    ∃ s, 0 < s ∧ s ≤ 1 ∧ rootResidual α s = 0 := by
  rcases eq_or_lt_of_le hα with h | hpos
  · exact ⟨1, one_pos, le_rfl, by simp [rootResidual, ← h]⟩
  · set e : ℝ := Real.exp (-(3 * α)) with he
    have hepos : 0 < e := Real.exp_pos _
    have hle : e ≤ 1 := by
      rw [he, Real.exp_le_one_iff]; linarith
    have hlow : rootResidual α e ≤ 0 := by
      have h1 : Real.log e = -(3 * α) := by rw [he, Real.log_exp]
      have h2 : e ^ 2 ≤ 1 := by nlinarith
      simp only [rootResidual, h1]
      nlinarith
    have hhigh : 0 ≤ rootResidual α 1 := by
      simp only [rootResidual, Real.log_one]
      nlinarith
    have hcont : ContinuousOn (rootResidual α) (Set.Icc e 1) := by
      apply ContinuousOn.add
      · exact Real.continuousOn_log.mono (by
          intro x hx
          simp only [Set.mem_Icc] at hx
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h; rw [h] at hx; linarith [hx.1])
      · fun_prop
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc hle hcont
      (Set.mem_Icc.2 ⟨hlow, hhigh⟩)
    exact ⟨s, lt_of_lt_of_le hepos hs.1, hs.2, hs0⟩

/-- The constant competitor value. -/
def M1 (α s : ℝ) : ℝ := 1 - s - 2 * α * s ^ 3

theorem twoBlock_at_constant {α s : ℝ} (hroot : rootResidual α s = 0) :
    twoBlockObjective α s s = M1 α s := by
  have hlog : Real.log s = -(3 * α * s ^ 2) := by
    simp only [rootResidual] at hroot; linarith
  simp only [twoBlockObjective, M1, H, hlog]
  ring

theorem entropy_plus_cubic_eq_M1 {α s : ℝ} (hroot : rootResidual α s = 0) :
    H s + α * s ^ 3 = M1 α s := by
  have hlog : Real.log s = -(3 * α * s ^ 2) := by
    simp only [rootResidual] at hroot; linarith
  simp only [M1, H, hlog]; ring

/-! ## From a cube bound to the two-block minimum -/

/-- The graphon-free criterion: a cube lower bound together with an attaining
pair gives `IsTwoBlockMinimum`. -/
theorem isTwoBlockMinimum_of_cube_bound {α M : ℝ} {G : ℝ → ℝ}
    (hcube : ∀ a ∈ unitInterval, ∀ b ∈ unitInterval, ∀ c ∈ unitInterval,
      M ≤ entropyF α G a b c)
    {r t : ℝ} (hr : r ∈ unitInterval) (ht : t ∈ unitInterval)
    (hval : twoBlockObjective α r t = M) :
    IsTwoBlockMinimum α M := by
  refine ⟨⟨r, hr, t, ht, hval⟩, ?_⟩
  intro r' hr' t' ht'
  rw [twoBlock_averaging α r' t' G]
  have h1 : M ≤ entropyF α G r' r' r' := hcube r' hr' r' hr' r' hr'
  have h2 : M ≤ entropyF α G r' t' t' := hcube r' hr' t' ht' t' ht'
  nlinarith [sq_nonneg (G r' + G t')]

/-! ## The case α = 0 -/

theorem entropy_certificate_zero :
    ∃ (M : ℝ) (G : ℝ → ℝ),
      IsTwoBlockMinimum 0 M ∧ ContinuousOn G unitInterval ∧
      ∀ a ∈ unitInterval, ∀ b ∈ unitInterval, ∀ c ∈ unitInterval,
        M ≤ entropyF 0 G a b c := by
  have hcube : ∀ a ∈ unitInterval, ∀ b ∈ unitInterval, ∀ c ∈ unitInterval,
      (0:ℝ) ≤ entropyF 0 (fun _ => 0) a b c := by
    intro a ha b hb c hc
    have h1 := entropy_nonnegative a ha.1
    have h2 := entropy_nonnegative b hb.1
    have h3 := entropy_nonnegative c hc.1
    simp only [entropyF, zero_mul, mul_zero, sub_zero, add_zero]
    linarith
  exact ⟨0, fun _ => 0,
    isTwoBlockMinimum_of_cube_bound hcube (r := 1) (t := 1)
      ⟨zero_le_one, le_rfl⟩ ⟨zero_le_one, le_rfl⟩ (by simp [twoBlockObjective, H]),
    continuousOn_const, hcube⟩
end
end TriangleNumerical
