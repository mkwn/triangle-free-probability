import TriangleNumerical.Root

/-!
# Rescaling from a reference parameter to all smaller parameters

Section 12 of the blueprint.  If the entropy certificate holds at a reference
parameter `α₀` with constant root `s₀` and reference value `M₁(α₀)`, then it
holds at every smaller `α > 0`, with the rescaled certificate function
`Gα w = √(s ρ / s₀) * G (k w)` where `k = s₀ / s` and `ρ = b / b₀`,
`b = α s²`, `b₀ = α₀ s₀²`.
-/
set_option autoImplicit false
namespace TriangleNumerical
noncomputable section

open Real

/-- Scaling law for the entropy function. Valid at `x = 0` as well. -/
theorem H_scale {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    H (s * x) = 1 - s + s * H x + s * x * Real.log s := by
  rcases eq_or_lt_of_le hx with h | hxpos
  · simp [H, ← h]
  · have : Real.log (s * x) = Real.log s + Real.log x :=
      Real.log_mul (ne_of_gt hs) (ne_of_gt hxpos)
    simp only [H, this]
    ring

/-- The excess over the constant competitor, in rescaled coordinates, is affine
in `b = α s²`. -/
theorem excess_affine_in_b {α s x₁ x₂ x₃ : ℝ} (hs : 0 < s)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hx₃ : 0 ≤ x₃)
    (hroot : rootResidual α s = 0) :
    (H (s * x₁) + H (s * x₂) + H (s * x₃)) / 3 + α * (s * x₁) * (s * x₂) * (s * x₃)
        - M1 α s
      = s * ((H x₁ + H x₂ + H x₃) / 3
          + (α * s ^ 2) * (x₁ * x₂ * x₃ - (x₁ + x₂ + x₃) + 2)) := by
  have hlog : Real.log s = -(3 * α * s ^ 2) := by
    simp only [rootResidual] at hroot; linarith
  rw [H_scale hs hx₁, H_scale hs hx₂, H_scale hs hx₃]
  simp only [M1, hlog]
  ring

/-- The exact rescaling identity (R2), in rescaled coordinates. -/
theorem rescaling_identity_scaled {α α₀ s s₀ ρ c x₁ x₂ x₃ : ℝ} (G : ℝ → ℝ)
    (hs : 0 < s) (hs₀ : 0 < s₀)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hx₃ : 0 ≤ x₃)
    (hroot : rootResidual α s = 0) (hroot₀ : rootResidual α₀ s₀ = 0)
    (hρ : ρ * (α₀ * s₀ ^ 2) = α * s ^ 2)
    (hc : c * s₀ = s * ρ) (hc0 : 0 ≤ c) :
    entropyF α (fun w => Real.sqrt c * G (s₀ / s * w)) (s * x₁) (s * x₂) (s * x₃)
        - M1 α s
      = c * (entropyF α₀ G (s₀ * x₁) (s₀ * x₂) (s₀ * x₃) - M1 α₀ s₀)
        + s * (1 - ρ) / 3 * (H x₁ + H x₂ + H x₃) := by
  have hsne : s ≠ 0 := ne_of_gt hs
  have hk : ∀ x : ℝ, s₀ / s * (s * x) = s₀ * x := by
    intro x; field_simp
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0
  have e1 := excess_affine_in_b (α := α) (s := s) hs hx₁ hx₂ hx₃ hroot
  have e0 := excess_affine_in_b (α := α₀) (s := s₀) hs₀ hx₁ hx₂ hx₃ hroot₀
  simp only [entropyF, hk]
  linear_combination e1 - c * e0 +
    (-(G (s₀ * x₁) * G (s₀ * x₂) + G (s₀ * x₁) * G (s₀ * x₃)
      + G (s₀ * x₂) * G (s₀ * x₃))) * hsq
    - (s * (x₁ * x₂ * x₃ - (x₁ + x₂ + x₃) + 2)) * hρ
    - ((H x₁ + H x₂ + H x₃) / 3
        + (α₀ * s₀ ^ 2) * (x₁ * x₂ * x₃ - (x₁ + x₂ + x₃) + 2)) * hc

/-- Transport of a reference cube bound to a smaller parameter. -/
theorem rescaled_cube_bound {α α₀ s s₀ ρ : ℝ} (G : ℝ → ℝ)
    (hs : 0 < s) (hs₀ : 0 < s₀) (hss₀ : s₀ ≤ s)
    (hroot : rootResidual α s = 0) (hroot₀ : rootResidual α₀ s₀ = 0)
    (hρ : ρ * (α₀ * s₀ ^ 2) = α * s ^ 2) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (href : ∀ a ∈ unitInterval, ∀ b ∈ unitInterval, ∀ c ∈ unitInterval,
      M1 α₀ s₀ ≤ entropyF α₀ G a b c) :
    ∀ a ∈ unitInterval, ∀ b ∈ unitInterval, ∀ c ∈ unitInterval,
      M1 α s ≤
        entropyF α (fun w => Real.sqrt (s * ρ / s₀) * G (s₀ / s * w)) a b c := by
  intro a ha b hb c hc
  have hsne : s ≠ 0 := ne_of_gt hs
  set C : ℝ := s * ρ / s₀ with hCdef
  have hC : C * s₀ = s * ρ := by rw [hCdef]; field_simp
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  -- rewrite the three weights in scaled coordinates
  have hx : ∀ w : ℝ, s * (w / s) = w := by intro w; field_simp
  have hid := rescaling_identity_scaled (α := α) (α₀ := α₀) (s := s) (s₀ := s₀)
    (ρ := ρ) (c := C) (x₁ := a / s) (x₂ := b / s) (x₃ := c / s) G hs hs₀
    (div_nonneg ha.1 hs.le) (div_nonneg hb.1 hs.le) (div_nonneg hc.1 hs.le)
    hroot hroot₀ hρ hC hC0
  rw [hx a, hx b, hx c] at hid
  have hks : s₀ / s ≤ 1 := (div_le_one hs).2 hss₀
  have hks0 : 0 ≤ s₀ / s := div_nonneg hs₀.le hs.le
  have hmem' : ∀ {w : ℝ}, w ∈ unitInterval → s₀ * (w / s) ∈ unitInterval := by
    intro w hw
    obtain ⟨hw0, hw1⟩ := hw
    have h1 : 0 ≤ w / s := div_nonneg hw0 hs.le
    have heq : s₀ * (w / s) = (s₀ / s) * w := by ring
    refine ⟨by positivity, ?_⟩
    rw [heq]
    nlinarith
  have h1 : 0 ≤ entropyF α₀ G (s₀ * (a / s)) (s₀ * (b / s)) (s₀ * (c / s))
      - M1 α₀ s₀ := by
    have := href _ (hmem' ha) _ (hmem' hb) _ (hmem' hc)
    linarith
  have h3 : 0 ≤ H (a / s) + H (b / s) + H (c / s) := by
    have h1' := entropy_nonnegative (a / s) (div_nonneg ha.1 hs.le)
    have h2' := entropy_nonnegative (b / s) (div_nonneg hb.1 hs.le)
    have h3' := entropy_nonnegative (c / s) (div_nonneg hc.1 hs.le)
    linarith
  have h4 : 0 ≤ s * (1 - ρ) / 3 := by
    have h : 0 ≤ 1 - ρ := by linarith
    positivity
  nlinarith [mul_nonneg hC0 h1, mul_nonneg h4 h3]

/-- The constant root is antitone in `α`: a smaller parameter has a larger root. -/
theorem root_mono {α α₀ s s₀ : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hs₀ : 0 < s₀)
    (hroot : rootResidual α s = 0) (hroot₀ : rootResidual α₀ s₀ = 0)
    (hlt : α ≤ α₀) (hα₀ : 0 < α₀) : s₀ ≤ s := by
  by_contra hcon
  push_neg at hcon
  have hlogs : Real.log s = -(3 * α * s ^ 2) := by
    simp only [rootResidual] at hroot; linarith
  have hlogs₀ : Real.log s₀ = -(3 * α₀ * s₀ ^ 2) := by
    simp only [rootResidual] at hroot₀; linarith
  have hlogsle : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1
  have hspos : (0:ℝ) < s ^ 2 := by positivity
  have hαnn : 0 ≤ α := by nlinarith
  have h1 : Real.log s < Real.log s₀ := Real.log_lt_log hs hcon
  have h2 : 3 * α₀ * s₀ ^ 2 < 3 * α * s ^ 2 := by linarith
  have hsq : s ^ 2 ≤ s₀ ^ 2 := by nlinarith
  have h3 : α * s ^ 2 ≤ α₀ * s ^ 2 := by nlinarith [sq_nonneg s]
  have h4 : α₀ * s ^ 2 ≤ α₀ * s₀ ^ 2 := by nlinarith
  linarith

/-- `b = α s²` is monotone in `α`. -/
theorem b_mono {α α₀ s s₀ : ℝ} (hs₀ : 0 < s₀) (hss₀ : s₀ ≤ s)
    (hroot : rootResidual α s = 0) (hroot₀ : rootResidual α₀ s₀ = 0) :
    α * s ^ 2 ≤ α₀ * s₀ ^ 2 := by
  have hlogs : Real.log s = -(3 * α * s ^ 2) := by
    simp only [rootResidual] at hroot; linarith
  have hlogs₀ : Real.log s₀ = -(3 * α₀ * s₀ ^ 2) := by
    simp only [rootResidual] at hroot₀; linarith
  have h : Real.log s₀ ≤ Real.log s := Real.log_le_log hs₀ hss₀
  linarith

end
end TriangleNumerical
