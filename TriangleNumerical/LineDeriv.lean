import TriangleNumerical.Deriv

/-!
# Derivatives of the certificate along a segment

The objective restricted to a line is a sum of products of functions of the
single parameter, so its first and second derivatives are obtained from
ordinary one-dimensional calculus — no multivariable differentiation is used.

`lineD1` is the directional derivative and `lineD2` the second directional
derivative; `lineD2_eq` rewrites the latter as the quadratic form with the
entries of the spatial Hessian, which is the shape required by the scalar
quadratic-form lemmas.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Branch
noncomputable section

open Real

variable {h θ : ℝ}

/-- First derivative of `Φ` along the direction `(a₁,a₂,a₃)`. -/
def lineD1 (h θ x y z a₁ a₂ a₃ : ℝ) : ℝ :=
  (a₁ * Real.log x + a₂ * Real.log y + a₃ * Real.log z) / 3
    + bAlpha h * (a₁ * y * z + a₂ * x * z + a₃ * x * y)
    - (a₁ * bGd h θ x * (bG h θ y + bG h θ z)
      + a₂ * bGd h θ y * (bG h θ x + bG h θ z)
      + a₃ * bGd h θ z * (bG h θ x + bG h θ y))

/-- Second derivative of `Φ` along the direction `(a₁,a₂,a₃)`. -/
def lineD2 (h θ x y z a₁ a₂ a₃ : ℝ) : ℝ :=
  (a₁ ^ 2 / x + a₂ ^ 2 / y + a₃ ^ 2 / z) / 3
    + 2 * bAlpha h * (a₁ * a₂ * z + a₁ * a₃ * y + a₂ * a₃ * x)
    - (a₁ ^ 2 * bGd2 h θ x * (bG h θ y + bG h θ z)
      + a₂ ^ 2 * bGd2 h θ y * (bG h θ x + bG h θ z)
      + a₃ ^ 2 * bGd2 h θ z * (bG h θ x + bG h θ y)
      + 2 * (a₁ * a₂ * bGd h θ x * bGd h θ y + a₁ * a₃ * bGd h θ x * bGd h θ z
            + a₂ * a₃ * bGd h θ y * bGd h θ z))

theorem hasDerivAt_affine (p a τ : ℝ) : HasDerivAt (fun s : ℝ => p + s * a) a τ := by
  simpa using ((hasDerivAt_id τ).mul_const a).const_add p

/-- The directional derivative of the objective. -/
theorem hasDerivAt_line1 (p₁ p₂ p₃ a₁ a₂ a₃ τ : ℝ)
    (h1 : p₁ + τ * a₁ ≠ 0) (h2 : p₂ + τ * a₂ ≠ 0) (h3 : p₃ + τ * a₃ ≠ 0) :
    HasDerivAt (fun s : ℝ => entropyF (bAlpha h) (bG h θ)
        (p₁ + s * a₁) (p₂ + s * a₂) (p₃ + s * a₃))
      (lineD1 h θ (p₁ + τ * a₁) (p₂ + τ * a₂) (p₃ + τ * a₃) a₁ a₂ a₃) τ := by
  set x := p₁ + τ * a₁ with hx
  set y := p₂ + τ * a₂ with hy
  set z := p₃ + τ * a₃ with hz
  have hu₁ := hasDerivAt_affine p₁ a₁ τ
  have hu₂ := hasDerivAt_affine p₂ a₂ τ
  have hu₃ := hasDerivAt_affine p₃ a₃ τ
  have hH₁ : HasDerivAt (fun s : ℝ => H (p₁ + s * a₁)) (Real.log x * a₁) τ :=
    by simpa [Function.comp] using (hasDerivAt_H h1).comp τ hu₁
  have hH₂ : HasDerivAt (fun s : ℝ => H (p₂ + s * a₂)) (Real.log y * a₂) τ :=
    by simpa [Function.comp] using (hasDerivAt_H h2).comp τ hu₂
  have hH₃ : HasDerivAt (fun s : ℝ => H (p₃ + s * a₃)) (Real.log z * a₃) τ :=
    by simpa [Function.comp] using (hasDerivAt_H h3).comp τ hu₃
  have hG₁ : HasDerivAt (fun s : ℝ => bG h θ (p₁ + s * a₁)) (bGd h θ x * a₁) τ :=
    by simpa [Function.comp] using (hasDerivAt_bG h θ h1).comp τ hu₁
  have hG₂ : HasDerivAt (fun s : ℝ => bG h θ (p₂ + s * a₂)) (bGd h θ y * a₂) τ :=
    by simpa [Function.comp] using (hasDerivAt_bG h θ h2).comp τ hu₂
  have hG₃ : HasDerivAt (fun s : ℝ => bG h θ (p₃ + s * a₃)) (bGd h θ z * a₃) τ :=
    by simpa [Function.comp] using (hasDerivAt_bG h θ h3).comp τ hu₃
  have hsum : HasDerivAt
      (fun s : ℝ => (H (p₁ + s * a₁) + H (p₂ + s * a₂) + H (p₃ + s * a₃)) / 3)
      ((Real.log x * a₁ + Real.log y * a₂ + Real.log z * a₃) / 3) τ :=
    ((hH₁.add hH₂).add hH₃).div_const 3
  have hcube : HasDerivAt
      (fun s : ℝ => bAlpha h * (p₁ + s * a₁) * (p₂ + s * a₂) * (p₃ + s * a₃))
      (bAlpha h * (a₁ * y * z + a₂ * x * z + a₃ * x * y)) τ := by
    have := ((hu₁.const_mul (bAlpha h)).mul hu₂).mul hu₃
    convert this using 1
    simp only [Pi.mul_apply]
    ring
  have hpair : HasDerivAt
      (fun s : ℝ => bG h θ (p₁ + s * a₁) * bG h θ (p₂ + s * a₂)
        + bG h θ (p₁ + s * a₁) * bG h θ (p₃ + s * a₃)
        + bG h θ (p₂ + s * a₂) * bG h θ (p₃ + s * a₃))
      (a₁ * bGd h θ x * (bG h θ y + bG h θ z)
        + a₂ * bGd h θ y * (bG h θ x + bG h θ z)
        + a₃ * bGd h θ z * (bG h θ x + bG h θ y)) τ := by
    have := ((hG₁.mul hG₂).add (hG₁.mul hG₃)).add (hG₂.mul hG₃)
    convert this using 1
    try simp only [Pi.mul_apply, Pi.add_apply]
    ring
  have := (hsum.add hcube).sub hpair
  convert this using 1
  simp only [lineD1]
  ring

/-- The second directional derivative. -/
theorem hasDerivAt_line2 (p₁ p₂ p₃ a₁ a₂ a₃ τ : ℝ)
    (h1 : p₁ + τ * a₁ ≠ 0) (h2 : p₂ + τ * a₂ ≠ 0) (h3 : p₃ + τ * a₃ ≠ 0) :
    HasDerivAt (fun s : ℝ => lineD1 h θ
        (p₁ + s * a₁) (p₂ + s * a₂) (p₃ + s * a₃) a₁ a₂ a₃)
      (lineD2 h θ (p₁ + τ * a₁) (p₂ + τ * a₂) (p₃ + τ * a₃) a₁ a₂ a₃) τ := by
  set x := p₁ + τ * a₁ with hx
  set y := p₂ + τ * a₂ with hy
  set z := p₃ + τ * a₃ with hz
  have hu₁ := hasDerivAt_affine p₁ a₁ τ
  have hu₂ := hasDerivAt_affine p₂ a₂ τ
  have hu₃ := hasDerivAt_affine p₃ a₃ τ
  have hl₁ : HasDerivAt (fun s : ℝ => Real.log (p₁ + s * a₁)) (x⁻¹ * a₁) τ :=
    by simpa [Function.comp] using (Real.hasDerivAt_log h1).comp τ hu₁
  have hl₂ : HasDerivAt (fun s : ℝ => Real.log (p₂ + s * a₂)) (y⁻¹ * a₂) τ :=
    by simpa [Function.comp] using (Real.hasDerivAt_log h2).comp τ hu₂
  have hl₃ : HasDerivAt (fun s : ℝ => Real.log (p₃ + s * a₃)) (z⁻¹ * a₃) τ :=
    by simpa [Function.comp] using (Real.hasDerivAt_log h3).comp τ hu₃
  have hG₁ : HasDerivAt (fun s : ℝ => bG h θ (p₁ + s * a₁)) (bGd h θ x * a₁) τ :=
    by simpa [Function.comp] using (hasDerivAt_bG h θ h1).comp τ hu₁
  have hG₂ : HasDerivAt (fun s : ℝ => bG h θ (p₂ + s * a₂)) (bGd h θ y * a₂) τ :=
    by simpa [Function.comp] using (hasDerivAt_bG h θ h2).comp τ hu₂
  have hG₃ : HasDerivAt (fun s : ℝ => bG h θ (p₃ + s * a₃)) (bGd h θ z * a₃) τ :=
    by simpa [Function.comp] using (hasDerivAt_bG h θ h3).comp τ hu₃
  have hg₁ : HasDerivAt (fun s : ℝ => bGd h θ (p₁ + s * a₁)) (bGd2 h θ x * a₁) τ :=
    by simpa [Function.comp] using (hasDerivAt_bGd h θ h1).comp τ hu₁
  have hg₂ : HasDerivAt (fun s : ℝ => bGd h θ (p₂ + s * a₂)) (bGd2 h θ y * a₂) τ :=
    by simpa [Function.comp] using (hasDerivAt_bGd h θ h2).comp τ hu₂
  have hg₃ : HasDerivAt (fun s : ℝ => bGd h θ (p₃ + s * a₃)) (bGd2 h θ z * a₃) τ :=
    by simpa [Function.comp] using (hasDerivAt_bGd h θ h3).comp τ hu₃
  have hlog : HasDerivAt
      (fun s : ℝ => (a₁ * Real.log (p₁ + s * a₁) + a₂ * Real.log (p₂ + s * a₂)
        + a₃ * Real.log (p₃ + s * a₃)) / 3)
      ((a₁ * (x⁻¹ * a₁) + a₂ * (y⁻¹ * a₂) + a₃ * (z⁻¹ * a₃)) / 3) τ :=
    (((hl₁.const_mul a₁).add (hl₂.const_mul a₂)).add (hl₃.const_mul a₃)).div_const 3
  have hcube : HasDerivAt
      (fun s : ℝ => bAlpha h * (a₁ * (p₂ + s * a₂) * (p₃ + s * a₃)
        + a₂ * (p₁ + s * a₁) * (p₃ + s * a₃) + a₃ * (p₁ + s * a₁) * (p₂ + s * a₂)))
      (2 * bAlpha h * (a₁ * a₂ * z + a₁ * a₃ * y + a₂ * a₃ * x)) τ := by
    have := ((((hu₂.const_mul a₁).mul hu₃).add ((hu₁.const_mul a₂).mul hu₃)).add
      ((hu₁.const_mul a₃).mul hu₂)).const_mul (bAlpha h)
    convert this using 1
    try simp only [Pi.mul_apply, Pi.add_apply]
    ring
  have hpair : HasDerivAt
      (fun s : ℝ => a₁ * bGd h θ (p₁ + s * a₁)
            * (bG h θ (p₂ + s * a₂) + bG h θ (p₃ + s * a₃))
          + a₂ * bGd h θ (p₂ + s * a₂)
            * (bG h θ (p₁ + s * a₁) + bG h θ (p₃ + s * a₃))
          + a₃ * bGd h θ (p₃ + s * a₃)
            * (bG h θ (p₁ + s * a₁) + bG h θ (p₂ + s * a₂)))
      (a₁ ^ 2 * bGd2 h θ x * (bG h θ y + bG h θ z)
        + a₂ ^ 2 * bGd2 h θ y * (bG h θ x + bG h θ z)
        + a₃ ^ 2 * bGd2 h θ z * (bG h θ x + bG h θ y)
        + 2 * (a₁ * a₂ * bGd h θ x * bGd h θ y + a₁ * a₃ * bGd h θ x * bGd h θ z
              + a₂ * a₃ * bGd h θ y * bGd h θ z)) τ := by
    have := ((((hg₁.const_mul a₁).mul (hG₂.add hG₃)).add
      ((hg₂.const_mul a₂).mul (hG₁.add hG₃))).add
      ((hg₃.const_mul a₃).mul (hG₁.add hG₂)))
    convert this using 1
    simp only [Pi.add_apply]
    ring
  have := (hlog.add hcube).sub hpair
  convert this using 1
  simp only [lineD2]
  field_simp
  try ring

/-- The second directional derivative as a quadratic form in the direction. -/
theorem lineD2_eq (x y z a₁ a₂ a₃ : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    lineD2 h θ x y z a₁ a₂ a₃
      = (1 / (3 * x) - bGd2 h θ x * (bG h θ y + bG h θ z)) * a₁ ^ 2
        + 2 * (bAlpha h * z - bGd h θ x * bGd h θ y) * a₁ * a₂
        + 2 * (bAlpha h * y - bGd h θ x * bGd h θ z) * a₁ * a₃
        + (1 / (3 * y) - bGd2 h θ y * (bG h θ x + bG h θ z)) * a₂ ^ 2
        + 2 * (bAlpha h * x - bGd h θ y * bGd h θ z) * a₂ * a₃
        + (1 / (3 * z) - bGd2 h θ z * (bG h θ x + bG h θ y)) * a₃ ^ 2 := by
  simp only [lineD2]
  field_simp
  ring

end
end Branch
end TriangleNumerical
