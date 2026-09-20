import TriangleNumerical.SpatialEval
import TriangleNumerical.LineDeriv
import TriangleNumerical.Segment
import TriangleNumerical.CoverTree
import TriangleNumerical.CubicData
import TriangleNumerical.ParamEval
import TriangleNumerical.CubicChunk0
import TriangleNumerical.CubicChunk1

/- ### From `HessEval` -/

/-!
# Interval enclosures of the spatial Hessian

The entries of the spatial Hessian of `Φ` that appear in `lineD2_eq` are

* the diagonal `1/(3w₁) - G''(w₁) (G(w₂) + G(w₃))`, and
* the off-diagonal `α w₃ - G'(w₁) G'(w₂)`.

Both are free of square roots once `G = √(Δ/6) η` is expanded, because the
two factors of `√(Δ/6)` combine into `Δ/6`:

```
G''(x) (G(y) + G(z)) = (1/6) (η''(X) D'(x)²/Δ + η'(X) D''(x)) (η(Y) + η(Z)),
G'(x) G'(y)          = η'(X) η'(Y) D'(x) D'(y) / (6Δ).
```

This module proves those two identities and the soundness of the
corresponding dyadic evaluators; they are used by the constant-neighbourhood
rule of blueprint §8.3.
-/
set_option autoImplicit false
namespace TriangleNumerical

namespace Branch
noncomputable section
open Real

variable {h θ : ℝ}

theorem sq_sqrtDelta (hh : 0 < h) :
    Real.sqrt (bDelta h / 6) * Real.sqrt (bDelta h / 6) = bDelta h / 6 :=
  Real.mul_self_sqrt (by positivity [bDelta_pos hh])

/-- The square-root-free form of the diagonal Hessian correction. -/
theorem bGd2_mul_bG_add (hh : 0 < h) (x y z : ℝ) :
    bGd2 h θ x * (bG h θ y + bG h θ z)
      = 1 / 6 * (etaD2 θ (bX h x) * (bDd h x ^ 2 / bDelta h)
          + etaD θ (bX h x) * bDd2 h x) * (etaT θ (bX h y) + etaT θ (bX h z)) := by
  have hD : bDelta h ≠ 0 := ne_of_gt (bDelta_pos hh)
  have hs := sq_sqrtDelta (h := h) hh
  calc bGd2 h θ x * (bG h θ y + bG h θ z)
      = (Real.sqrt (bDelta h / 6) * Real.sqrt (bDelta h / 6))
          * ((etaD2 θ (bX h x) * (bDd h x / bDelta h) ^ 2
              + etaD θ (bX h x) * (bDd2 h x / bDelta h))
            * (etaT θ (bX h y) + etaT θ (bX h z))) := by
        simp only [bGd2, bG]; ring
    _ = 1 / 6 * (etaD2 θ (bX h x) * (bDd h x ^ 2 / bDelta h)
          + etaD θ (bX h x) * bDd2 h x) * (etaT θ (bX h y) + etaT θ (bX h z)) := by
        rw [hs]; field_simp

/-- The square-root-free form of a product of two first derivatives of `G`. -/
theorem bGd_mul_bGd (hh : 0 < h) (x y : ℝ) :
    bGd h θ x * bGd h θ y
      = etaD θ (bX h x) * etaD θ (bX h y) * (bDd h x * bDd h y)
          / (6 * bDelta h) := by
  have hD : bDelta h ≠ 0 := ne_of_gt (bDelta_pos hh)
  have hs := sq_sqrtDelta (h := h) hh
  calc bGd h θ x * bGd h θ y
      = (Real.sqrt (bDelta h / 6) * Real.sqrt (bDelta h / 6))
          * ((etaD θ (bX h x) * (bDd h x / bDelta h))
            * (etaD θ (bX h y) * (bDd h y / bDelta h))) := by
        simp only [bGd]; ring
    _ = etaD θ (bX h x) * etaD θ (bX h y) * (bDd h x * bDd h y)
          / (6 * bDelta h) := by
        rw [hs]; field_simp

end
end Branch

namespace Itv

open Branch

variable {h θ : ℝ}

/-- The enclosure of `η''(X) = -2 + θ(6X - 4)`. -/
def etaD2I (IT IX : DI) : DI :=
  add (intI (-2)) (mul IT (sub (mul (intI 6) IX) (intI 4)))

theorem mem_etaD2I {IT IX : DI} {t x : ℝ} (hT : IT.Mem t) (hX : IX.Mem x) :
    (etaD2I IT IX).Mem (etaD2 t x) := by
  have hm := mem_add (mem_intI (-2))
    (mem_mul hT (mem_sub (mem_mul (mem_intI 6) hX) (mem_intI 4)))
  have heq : ((-2 : Int) : ℝ) + t * (((6:Int) : ℝ) * x - ((4:Int) : ℝ)) = etaD2 t x := by
    simp only [etaD2]; push_cast; ring
  rwa [heq] at hm

/-- The enclosure of `D''(w) = 1/w + 2β` on a side with positive lower endpoint. -/
def Side.IDd2 (s : Side) (IB : DI) : DI := add (inv s.Iw) (mul (intI 2) IB)

theorem Side.sound_Dd2 (s : Side) {IB : DI} {w : ℝ} (hpos : 0 < s.lo)
    (hB : IB.Mem (bBeta h)) (hw1 : value s.lo ≤ w) (hw2 : w ≤ value s.hi) :
    (s.IDd2 IB).Mem (bDd2 h w) := by
  have hw : s.Iw.Mem w := ⟨hw1, hw2⟩
  have hm := mem_add (mem_inv hw hpos) (mem_mul (mem_intI 2) hB)
  have heq : w⁻¹ + ((2:Int) : ℝ) * bBeta h = bDd2 h w := by
    simp only [bDd2]; push_cast; rw [one_div]
  rwa [heq] at hm

/-- The enclosure of the diagonal Hessian entry
`1/(3w₁) - G''(w₁)(G(w₂) + G(w₃))`. -/
def hessDiagI (s₁ s₂ s₃ : Side) (IDl IB IC IT : DI) : DI :=
  let X₁ := s₁.IX IB IC IDl
  let E₂ := etaI IT (s₂.IX IB IC IDl)
  let E₃ := etaI IT (s₃.IX IB IC IDl)
  let inner := add (mul (etaD2I IT X₁) (div (pow (s₁.IDd IB) 2) IDl))
    (mul (etaDI IT X₁) (s₁.IDd2 IB))
  sub (div oneI (mul (intI 3) s₁.Iw))
    (mul (mul (inv (intI 6)) inner) (add E₂ E₃))

/-- The enclosure of the off-diagonal Hessian entry `α w₃ - G'(w₁) G'(w₂)`. -/
def hessOffI (s₁ s₂ s₃ : Side) (IA IDl IB IC IT : DI) : DI :=
  let X₁ := s₁.IX IB IC IDl
  let X₂ := s₂.IX IB IC IDl
  sub (mul IA s₃.Iw)
    (div (mul (mul (etaDI IT X₁) (etaDI IT X₂)) (mul (s₁.IDd IB) (s₂.IDd IB)))
      (mul (intI 6) IDl))

/-- Soundness of the diagonal Hessian evaluator. -/
theorem mem_hessDiagI {s₁ s₂ s₃ : Side} {IDl IB IC IT : DI} {w₁ w₂ w₃ : ℝ}
    (hh : 0 < h)
    (hH₁lo : s₁.IHlo.Mem (H (value s₁.lo))) (hH₁hi : s₁.IHhi.Mem (H (value s₁.hi)))
    (hH₂lo : s₂.IHlo.Mem (H (value s₂.lo))) (hH₂hi : s₂.IHhi.Mem (H (value s₂.hi)))
    (hH₃lo : s₃.IHlo.Mem (H (value s₃.lo))) (hH₃hi : s₃.IHhi.Mem (H (value s₃.hi)))
    (hL₁lo : s₁.ILlo.Mem (Real.log (value s₁.lo)))
    (hL₁hi : s₁.ILhi.Mem (Real.log (value s₁.hi)))
    (hpos₁ : 0 < s₁.lo)
    (h0₁ : 0 ≤ value s₁.lo) (h1₁ : value s₁.hi ≤ 1)
    (h0₂ : 0 ≤ value s₂.lo) (h1₂ : value s₂.hi ≤ 1)
    (h0₃ : 0 ≤ value s₃.lo) (h1₃ : value s₃.hi ≤ 1)
    (hD : IDl.Mem (bDelta h)) (hB : IB.Mem (bBeta h)) (hC : IC.Mem (bC h))
    (hT : IT.Mem θ) (hDpos : 0 < IDl.lo)
    (h3pos : 0 < (mul (intI 3) s₁.Iw).lo)
    (hw₁ : value s₁.lo ≤ w₁) (hw₁' : w₁ ≤ value s₁.hi)
    (hw₂ : value s₂.lo ≤ w₂) (hw₂' : w₂ ≤ value s₂.hi)
    (hw₃ : value s₃.lo ≤ w₃) (hw₃' : w₃ ≤ value s₃.hi) :
    (hessDiagI s₁ s₂ s₃ IDl IB IC IT).Mem
      (1 / (3 * w₁) - bGd2 h θ w₁ * (bG h θ w₂ + bG h θ w₃)) := by
  obtain ⟨hu₁, -, -, hX₁⟩ := s₁.sound hH₁lo hH₁hi h0₁ h1₁ hB hC hD hDpos hw₁ hw₁'
  obtain ⟨-, -, -, hX₂⟩ := s₂.sound hH₂lo hH₂hi h0₂ h1₂ hB hC hD hDpos hw₂ hw₂'
  obtain ⟨-, -, -, hX₃⟩ := s₃.sound hH₃lo hH₃hi h0₃ h1₃ hB hC hD hDpos hw₃ hw₃'
  have hposv : 0 < value s₁.lo := value_pos hpos₁
  obtain ⟨-, hDd₁⟩ := s₁.sound_log hL₁lo hL₁hi hposv hB hw₁ hw₁'
  have hDd2₁ := s₁.sound_Dd2 (h := h) hpos₁ hB hw₁ hw₁'
  have h6 := mem_inv_intI (n := 6) (by norm_num)
  have hinner := mem_add
    (mem_mul (mem_etaD2I hT hX₁) (mem_div (mem_pow hDd₁ 2) hD hDpos))
    (mem_mul (mem_etaDI hT hX₁) hDd2₁)
  have hfirst := mem_div mem_oneI (mem_mul (mem_intI 3) hu₁) h3pos
  have hm := mem_sub hfirst
    (mem_mul (mem_mul h6 hinner) (mem_add (mem_etaI hT hX₂) (mem_etaI hT hX₃)))
  have heq : (1:ℝ) / (((3:Int) : ℝ) * w₁)
      - 1 / ((6:Int) : ℝ) * (etaD2 θ (bX h w₁) * (bDd h w₁ ^ 2 / bDelta h)
          + etaD θ (bX h w₁) * bDd2 h w₁)
        * (etaT θ (bX h w₂) + etaT θ (bX h w₃))
      = 1 / (3 * w₁) - bGd2 h θ w₁ * (bG h θ w₂ + bG h θ w₃) := by
    rw [bGd2_mul_bG_add (θ := θ) hh w₁ w₂ w₃]
    push_cast
    ring
  rwa [heq] at hm

/-- Soundness of the off-diagonal Hessian evaluator. -/
theorem mem_hessOffI {s₁ s₂ s₃ : Side} {IA IDl IB IC IT : DI} {w₁ w₂ w₃ : ℝ}
    (hh : 0 < h)
    (hH₁lo : s₁.IHlo.Mem (H (value s₁.lo))) (hH₁hi : s₁.IHhi.Mem (H (value s₁.hi)))
    (hH₂lo : s₂.IHlo.Mem (H (value s₂.lo))) (hH₂hi : s₂.IHhi.Mem (H (value s₂.hi)))
    (hL₁lo : s₁.ILlo.Mem (Real.log (value s₁.lo)))
    (hL₁hi : s₁.ILhi.Mem (Real.log (value s₁.hi)))
    (hL₂lo : s₂.ILlo.Mem (Real.log (value s₂.lo)))
    (hL₂hi : s₂.ILhi.Mem (Real.log (value s₂.hi)))
    (hpos₁ : 0 < s₁.lo) (hpos₂ : 0 < s₂.lo)
    (h0₁ : 0 ≤ value s₁.lo) (h1₁ : value s₁.hi ≤ 1)
    (h0₂ : 0 ≤ value s₂.lo) (h1₂ : value s₂.hi ≤ 1)
    (hA : IA.Mem (bAlpha h)) (hD : IDl.Mem (bDelta h)) (hB : IB.Mem (bBeta h))
    (hC : IC.Mem (bC h)) (hT : IT.Mem θ) (hDpos : 0 < IDl.lo)
    (h6pos : 0 < (mul (intI 6) IDl).lo)
    (hw₁ : value s₁.lo ≤ w₁) (hw₁' : w₁ ≤ value s₁.hi)
    (hw₂ : value s₂.lo ≤ w₂) (hw₂' : w₂ ≤ value s₂.hi)
    (hw₃ : value s₃.lo ≤ w₃) (hw₃' : w₃ ≤ value s₃.hi) :
    (hessOffI s₁ s₂ s₃ IA IDl IB IC IT).Mem
      (bAlpha h * w₃ - bGd h θ w₁ * bGd h θ w₂) := by
  obtain ⟨-, -, -, hX₁⟩ := s₁.sound hH₁lo hH₁hi h0₁ h1₁ hB hC hD hDpos hw₁ hw₁'
  obtain ⟨-, -, -, hX₂⟩ := s₂.sound hH₂lo hH₂hi h0₂ h1₂ hB hC hD hDpos hw₂ hw₂'
  have hu₃ : s₃.Iw.Mem w₃ := ⟨hw₃, hw₃'⟩
  obtain ⟨-, hDd₁⟩ := s₁.sound_log hL₁lo hL₁hi (value_pos hpos₁) hB hw₁ hw₁'
  obtain ⟨-, hDd₂⟩ := s₂.sound_log hL₂lo hL₂hi (value_pos hpos₂) hB hw₂ hw₂'
  have hm := mem_sub (mem_mul hA hu₃)
    (mem_div (mem_mul (mem_mul (mem_etaDI hT hX₁) (mem_etaDI hT hX₂))
      (mem_mul hDd₁ hDd₂)) (mem_mul (mem_intI 6) hD) h6pos)
  have heq : bAlpha h * w₃
      - etaD θ (bX h w₁) * etaD θ (bX h w₂) * (bDd h w₁ * bDd h w₂)
          / (((6:Int) : ℝ) * bDelta h)
      = bAlpha h * w₃ - bGd h θ w₁ * bGd h θ w₂ := by
    rw [bGd_mul_bGd (θ := θ) hh w₁ w₂]
    push_cast
    ring
  rwa [heq] at hm

end Itv
end TriangleNumerical


/- ### From `ConstBox` -/

/-!
# The constant-neighbourhood rule (blueprint §8.3)

On a cube `[lo,hi]³` containing the constant root `s`, where the certificate
vanishes (`G(s) = 0`), the objective is at least its value `M₁` at `(s,s,s)`.

The proof is the scalar segment argument: along the segment from `(s,s,s)` to
any point of the cube, the restriction of `Φ` has vanishing first derivative
at `τ = 0` — because `G(s) = 0` and `log s + 3αs² = 0` — and nonnegative
second derivative, because the Hessian is diagonally dominant on the cube.
No multivariable second-derivative theory and no determinants are used.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Branch
noncomputable section

open Real Set

variable {h θ : ℝ}

/-- The objective at the constant point, when the certificate vanishes there. -/
theorem entropyF_at_root {s : ℝ} (hroot : rootResidual (bAlpha h) s = 0)
    (hG : bG h θ s = 0) :
    entropyF (bAlpha h) (bG h θ) s s s = M1 (bAlpha h) s := by
  have := entropy_plus_cubic_eq_M1 (α := bAlpha h) (s := s) hroot
  simp only [entropyF, hG]
  rw [← this]
  ring

/-- The first directional derivative vanishes at the constant point. -/
theorem lineD1_at_root {s a₁ a₂ a₃ : ℝ} (hroot : rootResidual (bAlpha h) s = 0)
    (hG : bG h θ s = 0) :
    lineD1 h θ s s s a₁ a₂ a₃ = 0 := by
  have hlog : Real.log s = -(3 * bAlpha h * s ^ 2) := by
    simp only [rootResidual] at hroot; linarith
  simp only [lineD1, hG, hlog]
  ring

/-- The constant-neighbourhood bound. -/
theorem const_cube_bound {s lo hi : ℝ}
    (hroot : rootResidual (bAlpha h) s = 0) (hG : bG h θ s = 0)
    (hlo : 0 < lo) (hs1 : lo ≤ s) (hs2 : s ≤ hi)
    (hdiag : ∀ x y z : ℝ, lo ≤ x → x ≤ hi → lo ≤ y → y ≤ hi → lo ≤ z → z ≤ hi →
      1 ≤ 1 / (3 * x) - bGd2 h θ x * (bG h θ y + bG h θ z))
    (hoff : ∀ x y z : ℝ, lo ≤ x → x ≤ hi → lo ≤ y → y ≤ hi → lo ≤ z → z ≤ hi →
      |bAlpha h * z - bGd h θ x * bGd h θ y| ≤ 1 / 3)
    {w₁ w₂ w₃ : ℝ} (hw₁ : lo ≤ w₁) (hw₁' : w₁ ≤ hi) (hw₂ : lo ≤ w₂)
    (hw₂' : w₂ ≤ hi) (hw₃ : lo ≤ w₃) (hw₃' : w₃ ≤ hi) :
    M1 (bAlpha h) s ≤ entropyF (bAlpha h) (bG h θ) w₁ w₂ w₃ := by
  set a₁ := w₁ - s with ha₁
  set a₂ := w₂ - s with ha₂
  set a₃ := w₃ - s with ha₃
  -- the segment stays in the cube
  have hseg : ∀ (w : ℝ), lo ≤ w → w ≤ hi → ∀ τ ∈ Icc (0:ℝ) 1,
      lo ≤ s + τ * (w - s) ∧ s + τ * (w - s) ≤ hi := by
    intro w hw hw' τ hτ
    constructor
    · nlinarith [hτ.1, hτ.2]
    · nlinarith [hτ.1, hτ.2]
  have hpos : ∀ (w : ℝ), lo ≤ w → w ≤ hi → ∀ τ ∈ Icc (0:ℝ) 1,
      s + τ * (w - s) ≠ 0 := by
    intro w hw hw' τ hτ
    exact ne_of_gt (lt_of_lt_of_le hlo (hseg w hw hw' τ hτ).1)
  set f : ℝ → ℝ := fun τ => entropyF (bAlpha h) (bG h θ)
    (s + τ * a₁) (s + τ * a₂) (s + τ * a₃) with hf
  set f' : ℝ → ℝ := fun τ => lineD1 h θ
    (s + τ * a₁) (s + τ * a₂) (s + τ * a₃) a₁ a₂ a₃ with hf'
  set f'' : ℝ → ℝ := fun τ => lineD2 h θ
    (s + τ * a₁) (s + τ * a₂) (s + τ * a₃) a₁ a₂ a₃ with hf''
  have hd : ∀ τ ∈ Icc (0:ℝ) 1, HasDerivAt f (f' τ) τ := by
    intro τ hτ
    exact hasDerivAt_line1 s s s a₁ a₂ a₃ τ (hpos w₁ hw₁ hw₁' τ hτ)
      (hpos w₂ hw₂ hw₂' τ hτ) (hpos w₃ hw₃ hw₃' τ hτ)
  have hd' : ∀ τ ∈ Icc (0:ℝ) 1, HasDerivAt f' (f'' τ) τ := by
    intro τ hτ
    exact hasDerivAt_line2 s s s a₁ a₂ a₃ τ (hpos w₁ hw₁ hw₁' τ hτ)
      (hpos w₂ hw₂ hw₂' τ hτ) (hpos w₃ hw₃ hw₃' τ hτ)
  have hsecond : ∀ τ ∈ Icc (0:ℝ) 1, 0 ≤ f'' τ := by
    intro τ hτ
    obtain ⟨hx1, hx2⟩ := hseg w₁ hw₁ hw₁' τ hτ
    obtain ⟨hy1, hy2⟩ := hseg w₂ hw₂ hw₂' τ hτ
    obtain ⟨hz1, hz2⟩ := hseg w₃ hw₃ hw₃' τ hτ
    set x := s + τ * a₁
    set y := s + τ * a₂
    set z := s + τ * a₃
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hlo hx1)
    have hy0 : y ≠ 0 := ne_of_gt (lt_of_lt_of_le hlo hy1)
    have hz0 : z ≠ 0 := ne_of_gt (lt_of_lt_of_le hlo hz1)
    have hfτ : f'' τ = lineD2 h θ x y z a₁ a₂ a₃ := rfl
    rw [hfτ, lineD2_eq (h := h) (θ := θ) x y z a₁ a₂ a₃ hx0 hy0 hz0]
    have key := scalar_diagonal_dominance
      (1 / (3 * x) - bGd2 h θ x * (bG h θ y + bG h θ z))
      (bAlpha h * z - bGd h θ x * bGd h θ y)
      (bAlpha h * y - bGd h θ x * bGd h θ z)
      (1 / (3 * y) - bGd2 h θ y * (bG h θ x + bG h θ z))
      (bAlpha h * x - bGd h θ y * bGd h θ z)
      (1 / (3 * z) - bGd2 h θ z * (bG h θ x + bG h θ y))
      a₁ a₂ a₃
      (hdiag x y z hx1 hx2 hy1 hy2 hz1 hz2)
      (hdiag y x z hy1 hy2 hx1 hx2 hz1 hz2)
      (hdiag z x y hz1 hz2 hx1 hx2 hy1 hy2)
      (hoff x y z hx1 hx2 hy1 hy2 hz1 hz2)
      (hoff x z y hx1 hx2 hz1 hz2 hy1 hy2)
      (hoff y z x hy1 hy2 hz1 hz2 hx1 hx2)
    nlinarith [sq_nonneg a₁, sq_nonneg a₂, sq_nonneg a₃, key]
  have hzero : f' 0 = 0 := by
    have : f' 0 = lineD1 h θ s s s a₁ a₂ a₃ := by simp [hf']
    rw [this]
    exact lineD1_at_root hroot hG
  have hcont : ContinuousOn f (Icc 0 1) := fun τ hτ =>
    ((hd τ hτ).continuousAt).continuousWithinAt
  have hmain := Segment.le_endpoint (f := f) (f' := f') (f'' := f'') hcont
    (fun τ hτ => hd τ ⟨hτ.1, le_of_lt hτ.2⟩)
    (fun τ hτ => hd' τ ⟨hτ.1, le_of_lt hτ.2⟩)
    (fun τ hτ => hsecond τ ⟨hτ.1, le_of_lt hτ.2⟩) hzero
  have h0 : f 0 = M1 (bAlpha h) s := by
    have : f 0 = entropyF (bAlpha h) (bG h θ) s s s := by simp [hf]
    rw [this]
    exact entropyF_at_root hroot hG
  have h1 : f 1 = entropyF (bAlpha h) (bG h θ) w₁ w₂ w₃ := by
    simp only [hf, ha₁, ha₂, ha₃, one_mul]
    ring_nf
  rw [h0, h1] at hmain
  exact hmain

end
end Branch
end TriangleNumerical


/- ### From `ConstRule` -/

/-!
# The certified constant-neighbourhood leaf

The dyadic form of blueprint §8.3: two interval checks on the cube
`[value c.a, value d.a]³` — a diagonal Hessian entry at least `1` and an
off-diagonal entry of absolute value at most `1/3` — give the hypotheses of
`Branch.const_cube_bound`, hence the bound `M₁ ≤ Φ` on that cube.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Itv

open Branch

theorem abs_le_third_of_mem {i : DI} {x : ℝ} (hx : i.Mem x)
    (h1 : -scale ≤ 3 * i.lo) (h2 : 3 * i.hi ≤ scale) : |x| ≤ 1 / 3 := by
  have hs := scale_pos_real
  rw [mem_iff] at hx
  have hc1 : (-(scale:ℝ)) ≤ 3 * (i.lo : ℝ) := by exact_mod_cast h1
  have hc2 : 3 * (i.hi : ℝ) ≤ (scale:ℝ) := by exact_mod_cast h2
  rw [abs_le]
  constructor
  · nlinarith [hx.1]
  · nlinarith [hx.2]

/-- The constant-neighbourhood leaf rule. -/
theorem const_leaf_rule {c d : LogNegCert} {IA IDl IB IC IT : DI} {h θ s : ℝ}
    (hh : 0 < h) (ho : epOk c = true) (ho' : epOk d = true)
    (hpos : 0 < c.a) (hpos' : 0 < d.a) (hu : d.a ≤ scale)
    (hA : IA.Mem (bAlpha h)) (hD : IDl.Mem (bDelta h)) (hB : IB.Mem (bBeta h))
    (hC : IC.Mem (bC h)) (hT : IT.Mem θ) (hDpos : 0 < IDl.lo)
    (h3pos : 0 < (mul (intI 3) (mkSide c d).Iw).lo)
    (h6pos : 0 < (mul (intI 6) IDl).lo)
    (hroot : rootResidual (bAlpha h) s = 0) (hG : bG h θ s = 0)
    (hs1 : value c.a ≤ s) (hs2 : s ≤ value d.a)
    (hdiag : scale ≤
      (hessDiagI (mkSide c d) (mkSide c d) (mkSide c d) IDl IB IC IT).lo)
    (hoff1 : -scale ≤
      3 * (hessOffI (mkSide c d) (mkSide c d) (mkSide c d) IA IDl IB IC IT).lo)
    (hoff2 :
      3 * (hessOffI (mkSide c d) (mkSide c d) (mkSide c d) IA IDl IB IC IT).hi
        ≤ scale)
    {w₁ w₂ w₃ : ℝ}
    (hw₁ : value c.a ≤ w₁) (hw₁' : w₁ ≤ value d.a)
    (hw₂ : value c.a ≤ w₂) (hw₂' : w₂ ≤ value d.a)
    (hw₃ : value c.a ≤ w₃) (hw₃' : w₃ ≤ value d.a) :
    M1 (bAlpha h) s ≤ entropyF (bAlpha h) (bG h θ) w₁ w₂ w₃ := by
  have hlo : 0 < value c.a := value_pos hpos
  have hle : value d.a ≤ 1 := value_le_one hu
  have hHlo := mem_epH ho
  have hHhi := mem_epH ho'
  have hLlo := mem_epL ho hpos
  have hLhi := mem_epL ho' hpos'
  refine Branch.const_cube_bound (θ := θ) hroot hG hlo hs1 hs2 ?_ ?_
    hw₁ hw₁' hw₂ hw₂' hw₃ hw₃'
  · intro x y z hx1 hx2 hy1 hy2 hz1 hz2
    have hm := mem_hessDiagI (h := h) (θ := θ) (s₁ := mkSide c d) (w₁ := x)
      (s₂ := mkSide c d) (s₃ := mkSide c d)
      hh hHlo hHhi hHlo hHhi hHlo hHhi hLlo hLhi hpos hlo.le hle hlo.le hle
      hlo.le hle hD hB hC hT hDpos h3pos hx1 hx2 hy1 hy2 hz1 hz2
    exact le_trans (one_le_value hdiag) hm.1
  · intro x y z hx1 hx2 hy1 hy2 hz1 hz2
    have hm := mem_hessOffI (h := h) (θ := θ) (s₁ := mkSide c d)
      (s₂ := mkSide c d) (s₃ := mkSide c d)
      hh hHlo hHhi hHlo hHhi hLlo hLhi hLlo hLhi hpos hpos hlo.le hle hlo.le hle
      hA hD hB hC hT hDpos h6pos hx1 hx2 hy1 hy2 hz1 hz2
    exact abs_le_third_of_mem hm hoff1 hoff2

end Itv
end TriangleNumerical


/- ### From `CubicTheta` -/

/-!
# The cubic parameter θ of the transition slab (blueprint §5 (G4), §8.2)

On the transition slab the certificate uses the cubic correction

`θ = (X(s)² - 3X(s) + 1) / (X(s)(1 - X(s))²)`,

chosen so that `η_θ(X(s)) = 0`, i.e. `G(s) = 0` at the constant root `s`.
This module proves that defining property, the interval enclosure of `θ`, and
the uniform root bracket obtained from the two residual signs of §8.2.
-/
set_option autoImplicit false
namespace TriangleNumerical

namespace Branch
noncomputable section

variable {h : ℝ}

/-- The cubic parameter of (G4) as a function of `X(s)`. -/
def bTheta (X : ℝ) : ℝ := (X ^ 2 - 3 * X + 1) / (X * (1 - X) ^ 2)

/-- The defining property of `θ`: the certificate vanishes at the root. -/
theorem etaT_bTheta {X : ℝ} (hX : X * (1 - X) ^ 2 ≠ 0) :
    etaT (bTheta X) X = 0 := by
  have hkey : bTheta X * (X * (1 - X) ^ 2) = X ^ 2 - 3 * X + 1 :=
    div_mul_cancel₀ _ hX
  have hassoc : bTheta X * X * (1 - X) ^ 2 = bTheta X * (X * (1 - X) ^ 2) := by ring
  simp only [etaT]
  rw [hassoc, hkey]
  ring

theorem bG_eq_zero_of_theta {s : ℝ}
    (hX : bX h s * (1 - bX h s) ^ 2 ≠ 0) :
    bG h (bTheta (bX h s)) s = 0 := by
  simp only [bG, etaT_bTheta hX, mul_zero]

end
end Branch

namespace Itv

open Branch

theorem mem_thetaI {IX : DI} {x : ℝ} (hX : IX.Mem x)
    (hpos : 0 < (mul IX (pow (sub oneI IX) 2)).lo) :
    (thetaI IX).Mem (bTheta x) := by
  have hm := mem_div (mem_add (mem_sub (mem_pow hX 2) (mem_mul (mem_intI 3) hX))
    mem_oneI) (mem_mul hX (mem_pow (mem_sub mem_oneI hX) 2)) hpos
  have heq : (x ^ 2 - ((3:Int) : ℝ) * x + 1) / (x * (1 - x) ^ 2) = bTheta x := by
    simp only [bTheta]; push_cast; ring_nf
  rwa [heq] at hm

/-- The denominator of `θ` is positive, hence the defining identity applies. -/
theorem denom_ne_zero_of_mem {IX : DI} {x : ℝ} (hX : IX.Mem x)
    (hpos : 0 < (mul IX (pow (sub oneI IX) 2)).lo) : x * (1 - x) ^ 2 ≠ 0 :=
  ne_of_gt (pos_of_mem (mem_mul hX (mem_pow (mem_sub mem_oneI hX) 2)) hpos)

/-! ### The uniform root bracket of §8.2 -/

/-- A certified negative residual at a dyadic point. -/
theorem residual_neg {c : LogNegCert} {IA : DI} {α : ℝ} (ho : epOk c = true)
    (hpos : 0 < c.a) (hA : IA.Mem α)
    (hsign : (add (logNegI c)
      (mul (mul (intI 3) IA) (pow ⟨c.a, c.a⟩ 2))).hi < 0) :
    rootResidual α (value c.a) < 0 := by
  have hw : (⟨c.a, c.a⟩ : DI).Mem (value c.a) := ⟨le_refl _, le_refl _⟩
  have hm := mem_add (mem_epL ho hpos)
    (mem_mul (mem_mul (mem_intI 3) hA) (mem_pow hw 2))
  have heq : Real.log (value c.a) + ((3:Int) : ℝ) * α * value c.a ^ 2
      = rootResidual α (value c.a) := by
    simp only [rootResidual]; push_cast; ring
  rw [heq] at hm
  exact neg_of_mem hm hsign

/-- A certified positive residual at a dyadic point. -/
theorem residual_pos {c : LogNegCert} {IA : DI} {α : ℝ} (ho : epOk c = true)
    (hpos : 0 < c.a) (hA : IA.Mem α)
    (hsign : 0 < (add (logNegI c)
      (mul (mul (intI 3) IA) (pow ⟨c.a, c.a⟩ 2))).lo) :
    0 < rootResidual α (value c.a) := by
  have hw : (⟨c.a, c.a⟩ : DI).Mem (value c.a) := ⟨le_refl _, le_refl _⟩
  have hm := mem_add (mem_epL ho hpos)
    (mem_mul (mem_mul (mem_intI 3) hA) (mem_pow hw 2))
  have heq : Real.log (value c.a) + ((3:Int) : ℝ) * α * value c.a ^ 2
      = rootResidual α (value c.a) := by
    simp only [rootResidual]; push_cast; ring
  rw [heq] at hm
  exact pos_of_mem hm hsign

/-- The two residual signs bracket the root. -/
theorem root_bracket {α s lo hi : ℝ} (hα : 0 ≤ α) (hs : 0 < s)
    (hroot : rootResidual α s = 0) (hlopos : 0 < lo) (hhipos : 0 < hi)
    (hlo : rootResidual α lo < 0) (hhi : 0 < rootResidual α hi) :
    lo ≤ s ∧ s ≤ hi := by
  have hmono := rootResidual_strictMonoOn hα
  constructor
  · by_contra hcon
    push_neg at hcon
    have := hmono (Set.mem_Ioi.2 hs) (Set.mem_Ioi.2 hlopos) hcon
    rw [hroot] at this
    linarith
  · by_contra hcon
    push_neg at hcon
    have := hmono (Set.mem_Ioi.2 hhipos) (Set.mem_Ioi.2 hs) hcon
    rw [hroot] at this
    linarith

end Itv
end TriangleNumerical


/- ### From `CubicTable` -/

/-! # The cubic slab: endpoint certificates and parameter data.

Generated, untrusted data; every entry is rechecked in the kernel. -/
set_option autoImplicit false
set_option maxRecDepth 8000
namespace TriangleNumerical
namespace Itv
open Branch

theorem paramsC {x : ℝ} (h1 : value (pcC).hlo ≤ x)
    (h2 : x ≤ value (pcC).hhi) :
    (IAC).Mem (bAlpha x) ∧ (IDC).Mem (bDelta x) ∧
      (IBC).Mem (bBeta x) ∧ (ICC).Mem (bC x) := by
  obtain ⟨-, -, -, -, hd, ha, hb, hc⟩ := param_sound (pcC) pcC_ok h1 h2
  exact ⟨by rw [IAC_eq]; exact ha, by rw [IDC_eq]; exact hd,
    by rw [IBC_eq]; exact hb, by rw [ICC_eq]; exact hc⟩

theorem IXC_eq : IXC = (mkSide sloC shiC).IX IBC ICC IDC := by
  decide +kernel

end Itv
end TriangleNumerical


/- ### From `CubicSetup` -/

/-!
# The cubic slab: parameters, root bracket and the constant cube

This module turns the generated data of `CubicTable.lean` into the two
hypotheses that the replayed subdivision tree needs:

* `chk_soundC` — the soundness of the Boolean cover checker at the cubic
  parameter `θ = θ(h,s)`, whose enclosure `ITC` is verified here, and
* `excludes_constC` — the constant-neighbourhood rule on the cube `[26/100,
  27/100]³`, which is *not* a tree leaf.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
namespace TriangleNumerical
namespace Itv

open Branch

noncomputable section

/-- The cubic parameter of the slab at the constant root `s`. -/
def thetaC (h s : ℝ) : ℝ := bTheta (bX h s)

variable {h s : ℝ}

theorem hC_nine (h1 : value (pcC).hlo ≤ h) : (9:ℝ) ≤ h :=
  le_trans (nine_le_value (by decide)) h1

/-- All facts about the cubic slab that the cover replay needs. -/
theorem setupC (h1 : value (pcC).hlo ≤ h) (h2 : h ≤ value (pcC).hhi)
    (hs : 0 < s) (hroot : rootResidual (bAlpha h) s = 0) :
    (IAC).Mem (bAlpha h) ∧ (IDC).Mem (bDelta h) ∧ (IBC).Mem (bBeta h) ∧
      (ICC).Mem (bC h) ∧ (ITC).Mem (thetaC h s) ∧
      -(1/50 : ℝ) ≤ thetaC h s ∧ thetaC h s ≤ 0 ∧
      value sloC.a ≤ s ∧ s ≤ value shiC.a ∧ bG h (thetaC h s) s = 0 := by
  obtain ⟨hA, hD, hB, hC⟩ := paramsC h1 h2
  have h9 : (9:ℝ) ≤ h := hC_nine h1
  have hhpos : (0:ℝ) < h := by linarith
  have hαpos : 0 < bAlpha h := bAlpha_pos hhpos
  -- the uniform root bracket
  have hrlo : rootResidual (bAlpha h) (value sloC.a) < 0 :=
    residual_neg sloC_ok (by decide) hA (by decide +kernel)
  have hrhi : 0 < rootResidual (bAlpha h) (value shiC.a) :=
    residual_pos shiC_ok (by decide) hA (by decide +kernel)
  obtain ⟨hb1, hb2⟩ := root_bracket hαpos.le hs hroot
    (value_pos (by decide)) (value_pos (by decide)) hrlo hrhi
  -- the enclosure of X(s)
  have hDpos : 0 < (IDC).lo := by decide
  obtain ⟨-, -, -, hX⟩ := (mkSide sloC shiC).sound (IB := IBC) (IC := ICC)
    (IDl := IDC) (h := h) (w := s) (mem_epH sloC_ok) (mem_epH shiC_ok)
    (value_nonneg (by decide)) (value_le_one (by decide)) hB hC hD hDpos hb1 hb2
  have hXC : (IXC).Mem (bX h s) := by rw [IXC_eq]; exact hX
  have hden : 0 < (mul IXC (pow (sub oneI IXC) 2)).lo := by decide
  have hT : (ITC).Mem (thetaC h s) := by
    rw [ITC_eq]; exact mem_thetaI hXC hden
  have hzero : bG h (thetaC h s) s = 0 :=
    bG_eq_zero_of_theta (denom_ne_zero_of_mem hXC hden)
  refine ⟨hA, hD, hB, hC, hT, ?_, ?_, hb1, hb2, hzero⟩
  · have hlow : ((-1 : Int) : ℝ) / ((50 : Int) : ℝ) ≤ value (ITC).lo :=
      rat_le_value (n := (ITC).lo) (p := -1) (q := 50) (by norm_num) (by decide)
    norm_num at hlow
    linarith [hT.1]
  · have hupp : value (ITC).hi ≤ ((0 : Int) : ℝ) / ((1 : Int) : ℝ) :=
      value_le_rat (n := (ITC).hi) (p := 0) (q := 1) (by norm_num) (by decide)
    norm_num at hupp
    linarith [hT.2]

/-- Soundness of the Boolean checker on the cubic slab. -/
theorem chk_soundC (h1 : value (pcC).hlo ≤ h) (h2 : h ≤ value (pcC).hhi)
    (hs : 0 < s) (hroot : rootResidual (bAlpha h) s = 0) {M : ℝ}
    (hM : M ≤ bM2 h) :
    ∀ (t : STree) (b : DBox), chkS recsC IAC ID6C IB3C t b = true →
      Cover.Excludes (entropyF (bAlpha h) (bG h (thetaC h s))) M b.toBox := by
  obtain ⟨hA, hD, hB, hC, hT, hθ1, hθ0, -, -, -⟩ := setupC h1 h2 hs hroot
  have hD6 : ID6C.Mem (bDelta h * (1/6)) := by rw [ID6C_eq]; exact mem_pooled6 hD
  have hB3 : IB3C.Mem (bBeta h * (1/3)) := by rw [IB3C_eq]; exact mem_pooled3 hB
  have hg : ∀ k : Nat, (recsC.getS k).Good h (thetaC h s) :=
    good_getS epts_ok hB hC hD hT (by decide) _ recsC_ok
  exact chkS_sound hg (hC_nine h1) hθ1 hθ0 hM hA hD6 hB3

/-- The constant-neighbourhood rule on the constant cube. -/
theorem excludes_constC (h1 : value (pcC).hlo ≤ h) (h2 : h ≤ value (pcC).hhi)
    (hs : 0 < s) (hroot : rootResidual (bAlpha h) s = 0) {M : ℝ}
    (hM : M ≤ M1 (bAlpha h) s) :
    Cover.Excludes (entropyF (bAlpha h) (bG h (thetaC h s))) M
      constBoxC.toBox := by
  obtain ⟨hA, hD, hB, hC, hT, -, -, hb1, hb2, hzero⟩ := setupC h1 h2 hs hroot
  have hhpos : (0:ℝ) < h := by linarith [hC_nine h1]
  refine Cover.excludes_of_bound ?_
  rintro w₁ w₂ w₃ ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩⟩ - - -
  refine le_trans hM (const_leaf_rule (c := cloC) (d := chiC) (s := s)
    hhpos cloC_ok chiC_ok (by decide) (by decide) (by decide)
    hA hD hB hC hT (by decide) (by decide) (by decide) hroot hzero ?_ ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    k1 k2 k3 k4 k5 k6)
  · exact le_trans (value_mono (by decide)) hb1
  · exact le_trans hb2 (value_mono (by decide))

end

end Itv
end TriangleNumerical


/-! # The cubic slab: the assembled cube bound (generated). -/
set_option autoImplicit false
set_option maxRecDepth 8000
namespace TriangleNumerical
namespace Itv
open Branch

theorem excludesC {h s M : ℝ} (h1 : value (pcC).hlo ≤ h)
    (h2 : h ≤ value (pcC).hhi) (hs : 0 < s)
    (hroot : rootResidual (bAlpha h) s = 0)
    (hM1 : M ≤ M1 (bAlpha h) s) (hM2 : M ≤ bM2 h) :
    Cover.Excludes (entropyF (bAlpha h) (bG h (thetaC h s))) M
      rootBox.toBox := by
  have S := chk_soundC h1 h2 hs hroot hM2
  have K := excludes_constC h1 h2 hs hroot hM1
  exact (excludes_split_of ⟨0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨0, 34028236692093846346337460743176821145, 0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ 0 34028236692093846346337460743176821145 (by decide)
      (excludes_split_of ⟨0, 34028236692093846346337460743176821145, 0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨0, 34028236692093846346337460743176821145, 0, 34028236692093846346337460743176821145, 0, 340282366920938463463374607431768211456⟩ ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ 1 34028236692093846346337460743176821145 (by decide)
      (S subC_0 _ chkC_0)
      (excludes_split_of ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 0, 340282366920938463463374607431768211456⟩ ⟨0, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ 1 88473415399444000500477397932259734978 (by decide)
      (excludes_split_of ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 0, 340282366920938463463374607431768211456⟩ ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 0, 34028236692093846346337460743176821145⟩ ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456⟩ 2 34028236692093846346337460743176821145 (by decide)
      (S subC_1 _ chkC_1)
      (excludes_split_of ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456⟩ ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978⟩ ⟨0, 34028236692093846346337460743176821145, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 340282366920938463463374607431768211456⟩ 2 88473415399444000500477397932259734978 (by decide)
      (S subC_2 _ chkC_2)
      (S subC_3 _ chkC_3)))
      (excludes_split_of ⟨0, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨0, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 0, 340282366920938463463374607431768211456⟩ ⟨0, 34028236692093846346337460743176821145, 91876239068653385135111144006577417093, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ 1 91876239068653385135111144006577417093 (by decide)
      (S subC_4 _ chkC_4)
      (S subC_5 _ chkC_5))))
      (excludes_split_of ⟨34028236692093846346337460743176821145, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨88473415399444000500477397932259734978, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ 0 88473415399444000500477397932259734978 (by decide)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 0, 34028236692093846346337460743176821145, 0, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ 1 34028236692093846346337460743176821145 (by decide)
      (S subC_6 _ chkC_6)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 0, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ 1 88473415399444000500477397932259734978 (by decide)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 0, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 0, 34028236692093846346337460743176821145⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456⟩ 2 34028236692093846346337460743176821145 (by decide)
      (S subC_7 _ chkC_7)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 340282366920938463463374607431768211456⟩ 2 88473415399444000500477397932259734978 (by decide)
      (S subC_8 _ chkC_8)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 340282366920938463463374607431768211456⟩ 2 91876239068653385135111144006577417093 (by decide)
      (S subC_9 _ chkC_9)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 323268248574891540290205877060179800884, 340282366920938463463374607431768211456⟩ 2 323268248574891540290205877060179800884 (by decide)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 207572243821772462712658510533378608988, 323268248574891540290205877060179800884⟩ 2 207572243821772462712658510533378608988 (by decide)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 149724241445212923923884827269978013040, 207572243821772462712658510533378608988⟩ 2 149724241445212923923884827269978013040 (by decide)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ ⟨34028236692093846346337460743176821145, 61250826045768923423407429337718278061, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ 0 61250826045768923423407429337718278061 (by decide)
      (S subC_10 _ chkC_10)
      (excludes_split_of ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 120800240256933154529497985638277715066, 149724241445212923923884827269978013040⟩ 2 120800240256933154529497985638277715066 (by decide)
      (excludes_split_of ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ ⟨61250826045768923423407429337718278061, 74862120722606461961942413634989006519, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ 0 74862120722606461961942413634989006519 (by decide)
      (S subC_11 _ chkC_11)
      (excludes_split_of ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 106338239662793269832304564822427566079⟩ ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 106338239662793269832304564822427566079, 120800240256933154529497985638277715066⟩ 2 106338239662793269832304564822427566079 (by decide)
      (S subC_12 _ chkC_12)
      (S subC_13 _ chkC_13)))
      (S subC_14 _ chkC_14)))
      (S subC_15 _ chkC_15))
      (S subC_16 _ chkC_16))
      (S subC_17 _ chkC_17)))))
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 0, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ 1 91876239068653385135111144006577417093 (by decide)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 0, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 0, 34028236692093846346337460743176821145⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456⟩ 2 34028236692093846346337460743176821145 (by decide)
      (S subC_18 _ chkC_18)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 340282366920938463463374607431768211456⟩ 2 88473415399444000500477397932259734978 (by decide)
      (S subC_19 _ chkC_19)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 340282366920938463463374607431768211456⟩ 2 91876239068653385135111144006577417093 (by decide)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093⟩ ⟨34028236692093846346337460743176821145, 61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093⟩ ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093⟩ 0 61250826045768923423407429337718278061 (by decide)
      (S subC_20 _ chkC_20)
      (excludes_split_of ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093⟩ ⟨61250826045768923423407429337718278061, 74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093⟩ ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093⟩ 0 74862120722606461961942413634989006519 (by decide)
      (S subC_21 _ chkC_21)
      (excludes_split_of ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093⟩ ⟨74862120722606461961942413634989006519, 81667768061025231231209905783624370748, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093⟩ ⟨81667768061025231231209905783624370748, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093⟩ 0 81667768061025231231209905783624370748 (by decide)
      (S subC_22 _ chkC_22)
      (excludes_split_of ⟨81667768061025231231209905783624370748, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093⟩ ⟨81667768061025231231209905783624370748, 85070591730234615865843651857942052863, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093⟩ ⟨85070591730234615865843651857942052863, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093⟩ 0 85070591730234615865843651857942052863 (by decide)
      (S subC_23 _ chkC_23)
      (S subC_24 _ chkC_24)))))
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884, 340282366920938463463374607431768211456⟩ 2 323268248574891540290205877060179800884 (by decide)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988, 323268248574891540290205877060179800884⟩ 2 207572243821772462712658510533378608988 (by decide)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040, 207572243821772462712658510533378608988⟩ 2 149724241445212923923884827269978013040 (by decide)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ ⟨34028236692093846346337460743176821145, 61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ 0 61250826045768923423407429337718278061 (by decide)
      (S subC_25 _ chkC_25)
      (excludes_split_of ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066, 149724241445212923923884827269978013040⟩ 2 120800240256933154529497985638277715066 (by decide)
      (excludes_split_of ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ ⟨61250826045768923423407429337718278061, 74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ 0 74862120722606461961942413634989006519 (by decide)
      (S subC_26 _ chkC_26)
      (excludes_split_of ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 106338239662793269832304564822427566079⟩ ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 106338239662793269832304564822427566079, 120800240256933154529497985638277715066⟩ 2 106338239662793269832304564822427566079 (by decide)
      (excludes_split_of ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 106338239662793269832304564822427566079⟩ ⟨74862120722606461961942413634989006519, 81667768061025231231209905783624370748, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 106338239662793269832304564822427566079⟩ ⟨81667768061025231231209905783624370748, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 106338239662793269832304564822427566079⟩ 0 81667768061025231231209905783624370748 (by decide)
      (S subC_27 _ chkC_27)
      (excludes_split_of ⟨81667768061025231231209905783624370748, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 106338239662793269832304564822427566079⟩ ⟨81667768061025231231209905783624370748, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 99107239365723327483707854414502491586⟩ ⟨81667768061025231231209905783624370748, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 99107239365723327483707854414502491586, 106338239662793269832304564822427566079⟩ 2 99107239365723327483707854414502491586 (by decide)
      (excludes_split_of ⟨81667768061025231231209905783624370748, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 99107239365723327483707854414502491586⟩ ⟨81667768061025231231209905783624370748, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 95491739217188356309409499210539954339⟩ ⟨81667768061025231231209905783624370748, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 95491739217188356309409499210539954339, 99107239365723327483707854414502491586⟩ 2 95491739217188356309409499210539954339 (by decide)
      (excludes_split_of ⟨81667768061025231231209905783624370748, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 95491739217188356309409499210539954339⟩ ⟨81667768061025231231209905783624370748, 85070591730234615865843651857942052863, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 95491739217188356309409499210539954339⟩ ⟨85070591730234615865843651857942052863, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 95491739217188356309409499210539954339⟩ 0 85070591730234615865843651857942052863 (by decide)
      (S subC_28 _ chkC_28)
      (excludes_split_of ⟨85070591730234615865843651857942052863, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 95491739217188356309409499210539954339⟩ ⟨85070591730234615865843651857942052863, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 93683989142920870722260321608558685716⟩ ⟨85070591730234615865843651857942052863, 88473415399444000500477397932259734978, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 93683989142920870722260321608558685716, 95491739217188356309409499210539954339⟩ 2 93683989142920870722260321608558685716 (by decide)
      (S subC_29 _ chkC_29)
      (S subC_30 _ chkC_30)))
      (S subC_31 _ chkC_31))
      (S subC_32 _ chkC_32)))
      (S subC_33 _ chkC_33)))
      (S subC_34 _ chkC_34)))
      (S subC_35 _ chkC_35))
      (S subC_36 _ chkC_36))
      (S subC_37 _ chkC_37)))))
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884, 0, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 323268248574891540290205877060179800884, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ 1 323268248574891540290205877060179800884 (by decide)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884, 0, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884, 0, 34028236692093846346337460743176821145⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456⟩ 2 34028236692093846346337460743176821145 (by decide)
      (S subC_38 _ chkC_38)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884, 88473415399444000500477397932259734978, 340282366920938463463374607431768211456⟩ 2 88473415399444000500477397932259734978 (by decide)
      (S subC_39 _ chkC_39)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884, 88473415399444000500477397932259734978, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884, 91876239068653385135111144006577417093, 340282366920938463463374607431768211456⟩ 2 91876239068653385135111144006577417093 (by decide)
      (S subC_40 _ chkC_40)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884, 91876239068653385135111144006577417093, 340282366920938463463374607431768211456⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884, 323268248574891540290205877060179800884, 340282366920938463463374607431768211456⟩ 2 323268248574891540290205877060179800884 (by decide)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 207572243821772462712658510533378608988, 323268248574891540290205877060179800884, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884⟩ 1 207572243821772462712658510533378608988 (by decide)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988, 207572243821772462712658510533378608988, 323268248574891540290205877060179800884⟩ 2 207572243821772462712658510533378608988 (by decide)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 149724241445212923923884827269978013040, 207572243821772462712658510533378608988, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988⟩ 1 149724241445212923923884827269978013040 (by decide)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040, 149724241445212923923884827269978013040, 207572243821772462712658510533378608988⟩ 2 149724241445212923923884827269978013040 (by decide)
      (excludes_split_of ⟨34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ ⟨34028236692093846346337460743176821145, 61250826045768923423407429337718278061, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ 0 61250826045768923423407429337718278061 (by decide)
      (S subC_41 _ chkC_41)
      (excludes_split_of ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 120800240256933154529497985638277715066, 149724241445212923923884827269978013040, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ 1 120800240256933154529497985638277715066 (by decide)
      (excludes_split_of ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066, 120800240256933154529497985638277715066, 149724241445212923923884827269978013040⟩ 2 120800240256933154529497985638277715066 (by decide)
      (excludes_split_of ⟨61250826045768923423407429337718278061, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ ⟨61250826045768923423407429337718278061, 74862120722606461961942413634989006519, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ 0 74862120722606461961942413634989006519 (by decide)
      (S subC_42 _ chkC_42)
      (excludes_split_of ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 106338239662793269832304564822427566079, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 106338239662793269832304564822427566079, 120800240256933154529497985638277715066, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ 1 106338239662793269832304564822427566079 (by decide)
      (excludes_split_of ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 106338239662793269832304564822427566079, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 106338239662793269832304564822427566079, 91876239068653385135111144006577417093, 106338239662793269832304564822427566079⟩ ⟨74862120722606461961942413634989006519, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 106338239662793269832304564822427566079, 106338239662793269832304564822427566079, 120800240256933154529497985638277715066⟩ 2 106338239662793269832304564822427566079 (by decide)
      (S subC_43 _ chkC_43)
      (S subC_44 _ chkC_44))
      (S subC_45 _ chkC_45)))
      (S subC_46 _ chkC_46))
      (S subC_47 _ chkC_47)))
      (S subC_48 _ chkC_48))
      (S subC_49 _ chkC_49))
      (S subC_50 _ chkC_50))
      (S subC_51 _ chkC_51))
      (S subC_52 _ chkC_52)))))
      (S subC_53 _ chkC_53)))))
      (excludes_split_of ⟨88473415399444000500477397932259734978, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨91876239068653385135111144006577417093, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ 0 91876239068653385135111144006577417093 (by decide)
      (excludes_split_of ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 0, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 0, 34028236692093846346337460743176821145, 0, 340282366920938463463374607431768211456⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ 1 34028236692093846346337460743176821145 (by decide)
      (S subC_54 _ chkC_54)
      (excludes_split_of ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978, 0, 340282366920938463463374607431768211456⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ 1 88473415399444000500477397932259734978 (by decide)
      (S subC_55 _ chkC_55)
      (excludes_split_of ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 0, 340282366920938463463374607431768211456⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 340282366920938463463374607431768211456, 0, 340282366920938463463374607431768211456⟩ 1 91876239068653385135111144006577417093 (by decide)
      (excludes_split_of ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 0, 340282366920938463463374607431768211456⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 0, 34028236692093846346337460743176821145⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456⟩ 2 34028236692093846346337460743176821145 (by decide)
      (S subC_56 _ chkC_56)
      (excludes_split_of ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 34028236692093846346337460743176821145, 340282366920938463463374607431768211456⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 34028236692093846346337460743176821145, 88473415399444000500477397932259734978⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 340282366920938463463374607431768211456⟩ 2 88473415399444000500477397932259734978 (by decide)
      (S subC_57 _ chkC_57)
      (excludes_split_of ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 340282366920938463463374607431768211456⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 340282366920938463463374607431768211456⟩ 2 91876239068653385135111144006577417093 (by decide)
      K
      (excludes_split_of ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 340282366920938463463374607431768211456⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884, 340282366920938463463374607431768211456⟩ 2 323268248574891540290205877060179800884 (by decide)
      (excludes_split_of ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 323268248574891540290205877060179800884⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988, 323268248574891540290205877060179800884⟩ 2 207572243821772462712658510533378608988 (by decide)
      (excludes_split_of ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 207572243821772462712658510533378608988⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040, 207572243821772462712658510533378608988⟩ 2 149724241445212923923884827269978013040 (by decide)
      (excludes_split_of ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 149724241445212923923884827269978013040⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066, 149724241445212923923884827269978013040⟩ 2 120800240256933154529497985638277715066 (by decide)
      (excludes_split_of ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 120800240256933154529497985638277715066⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 106338239662793269832304564822427566079⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 106338239662793269832304564822427566079, 120800240256933154529497985638277715066⟩ 2 106338239662793269832304564822427566079 (by decide)
      (excludes_split_of ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 106338239662793269832304564822427566079⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 99107239365723327483707854414502491586⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 99107239365723327483707854414502491586, 106338239662793269832304564822427566079⟩ 2 99107239365723327483707854414502491586 (by decide)
      (excludes_split_of ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 99107239365723327483707854414502491586⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 95491739217188356309409499210539954339⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 95491739217188356309409499210539954339, 99107239365723327483707854414502491586⟩ 2 95491739217188356309409499210539954339 (by decide)
      (excludes_split_of ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 95491739217188356309409499210539954339⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 93683989142920870722260321608558685716⟩ ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 93683989142920870722260321608558685716, 95491739217188356309409499210539954339⟩ 2 93683989142920870722260321608558685716 (by decide)
      (excludes_split_of ⟨88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 93683989142920870722260321608558685716⟩ ⟨88473415399444000500477397932259734978, 90174827234048692817794270969418576035, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 93683989142920870722260321608558685716⟩ ⟨90174827234048692817794270969418576035, 91876239068653385135111144006577417093, 88473415399444000500477397932259734978, 91876239068653385135111144006577417093, 91876239068653385135111144006577417093, 93683989142920870722260321608558685716⟩ 0 90174827234048692817794270969418576035 (by decide)
      (S subC_58 _ chkC_58)
      (S subC_59 _ chkC_59))
      (S subC_60 _ chkC_60))
      (S subC_61 _ chkC_61))
      (S subC_62 _ chkC_62))
      (S subC_63 _ chkC_63))
      (S subC_64 _ chkC_64))
      (S subC_65 _ chkC_65))
      (S subC_66 _ chkC_66))
      (S subC_67 _ chkC_67)))))
      (S subC_68 _ chkC_68))))
      (S subC_69 _ chkC_69))))

theorem boundC {h s : ℝ} (h1 : value (pcC).hlo ≤ h)
    (h2 : h ≤ value (pcC).hhi) (hs : 0 < s)
    (hroot : rootResidual (bAlpha h) s = 0) :
    ∀ a ∈ unitInterval, ∀ b ∈ unitInterval, ∀ c ∈ unitInterval,
      min (M1 (bAlpha h) s) (bM2 h)
        ≤ entropyF (bAlpha h) (bG h (thetaC h s)) a b c :=
  cube_bound_of_excludes
    (excludesC h1 h2 hs hroot (min_le_left _ _) (min_le_right _ _))

end Itv
end TriangleNumerical
