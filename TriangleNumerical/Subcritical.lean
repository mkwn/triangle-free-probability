import TriangleNumerical.Rescale

/-!
# From one reference certificate to every smaller parameter

Assembling Sections 3, 12 and 13 of the blueprint: a single reference
certificate at `α₀ > 0` (with the constant root `s₀`, the value `M₁(α₀)`, a
continuous `G₀` and the cube bound) yields the entropy certificate for every
`0 ≤ α ≤ α₀`.
-/
set_option autoImplicit false
namespace TriangleNumerical
noncomputable section

open Real

/-- The entropy certificate at a fixed parameter. -/
def EntropyCertificateAt (α : ℝ) : Prop :=
  ∃ (M : ℝ) (G : ℝ → ℝ),
    IsTwoBlockMinimum α M ∧ ContinuousOn G unitInterval ∧
    ∀ a ∈ unitInterval, ∀ b ∈ unitInterval, ∀ c ∈ unitInterval,
      M ≤ entropyF α G a b c

theorem entropyCertificate_zero : EntropyCertificateAt 0 :=
  entropy_certificate_zero

/-- Rescaling: a reference certificate of constant type at `α₀` gives the
certificate at every `0 ≤ α ≤ α₀`. -/
theorem entropyCertificateAt_of_reference
    {α₀ s₀ : ℝ} (hα₀ : 0 < α₀) (hs₀ : 0 < s₀)
    (hroot₀ : rootResidual α₀ s₀ = 0)
    (G₀ : ℝ → ℝ) (hcont₀ : ContinuousOn G₀ unitInterval)
    (href : ∀ a ∈ unitInterval, ∀ b ∈ unitInterval, ∀ c ∈ unitInterval,
      M1 α₀ s₀ ≤ entropyF α₀ G₀ a b c)
    {α : ℝ} (hα : 0 ≤ α) (hαα₀ : α ≤ α₀) :
    EntropyCertificateAt α := by
  rcases eq_or_lt_of_le hα with h | hαpos
  · rw [← h]; exact entropyCertificate_zero
  obtain ⟨s, hs, hs1, hroot⟩ := exists_constant_root hα
  have hss₀ : s₀ ≤ s := root_mono hs hs1 hs₀ hroot hroot₀ hαα₀ hα₀
  have hb₀ : 0 < α₀ * s₀ ^ 2 := by positivity
  set ρ : ℝ := (α * s ^ 2) / (α₀ * s₀ ^ 2) with hρdef
  have hρ : ρ * (α₀ * s₀ ^ 2) = α * s ^ 2 := by
    rw [hρdef]; field_simp
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef]; positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef, div_le_one hb₀]
    exact b_mono hs₀ hss₀ hroot hroot₀
  have hcube := rescaled_cube_bound (α := α) (α₀ := α₀) (s := s) (s₀ := s₀) (ρ := ρ)
    G₀ hs hs₀ hss₀ hroot hroot₀ hρ hρ0 hρ1 href
  refine ⟨M1 α s, fun w => Real.sqrt (s * ρ / s₀) * G₀ (s₀ / s * w), ?_, ?_, hcube⟩
  · refine isTwoBlockMinimum_of_cube_bound hcube (r := s) (t := s)
      ⟨hs.le, hs1⟩ ⟨hs.le, hs1⟩ (twoBlock_at_constant hroot)
  · apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.comp hcont₀ (by fun_prop)
    intro w hw
    obtain ⟨hw0, hw1⟩ := hw
    have hks : s₀ / s ≤ 1 := (div_le_one hs).2 hss₀
    have hks0 : 0 ≤ s₀ / s := div_nonneg hs₀.le hs.le
    exact ⟨by positivity, by nlinarith⟩

end
end TriangleNumerical
