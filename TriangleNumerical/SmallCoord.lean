import TriangleNumerical.HighCoord
import TriangleNumerical.LocalSmall

/-!
# The small coordinate range `0 < x ≤ 1/10`

Sections 7.1 and 7.2 of the blueprint, second half.  For every branch parameter
`h ≥ 9` and every `θ ∈ [-1/50, 0]` we prove, on `0 < x ≤ 1/10`,

```
η'(X(x)) ≥ 97/100,   -41/20 ≤ η''(X(x)) < 0,   D'(x) < 0,   |D'(x)| ≤ |log x|,
```

and the convexity statement `G''(x) > 0`, whose proof splits the interval at
`1/30` and uses the monotonicity of `x (log x)²`.

On the much smaller range `0 < x ≤ 1/1080` — which contains the whole convex
box `(0, L]`, `L = 1/(30 α²)`, because `α ≥ 6` — we also certify

```
X(x) ≥ 9885/10000,  987/1000 ≤ η(X(x)) ≤ 1011/1000,  0 < η'(X(x)) ≤ 103/100,
|G'(x)| ≤ (43/100)|log x|.
```
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Branch
noncomputable section

open Real

variable {h θ x : ℝ}

/-! ### `η` derivatives on the small range -/

theorem etaD_small_ge (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 10) : 97 / 100 ≤ etaD θ (bX h x) := by
  have hlo := bX_lower hh hx0 hx
  have hhi := bX_upper hh hx0 hx
  simp only [etaD]
  nlinarith [sq_nonneg (bX h x), sq_nonneg (bX h x - 1)]

theorem etaD2_small_neg (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 10) : etaD2 θ (bX h x) < 0 := by
  have hlo := bX_lower hh hx0 hx
  have hhi := bX_upper hh hx0 hx
  simp only [etaD2]
  nlinarith

theorem etaD2_small_ge (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 10) : -(41 / 20 : ℝ) ≤ etaD2 θ (bX h x) := by
  have hlo := bX_lower hh hx0 hx
  have hhi := bX_upper hh hx0 hx
  simp only [etaD2]
  nlinarith

/-! ### `D'` on the small range -/

theorem bDd_small_neg (hh : 9 ≤ h) (hx0 : 0 < x) (hx : x ≤ 1 / 10) : bDd h x < 0 := by
  have hβ := bBeta_lt hh
  have hβ0 := bBeta_pos hh
  have hlog : Real.log x < -(23 / 10) :=
    lt_of_le_of_lt (Real.log_le_log hx0 hx) log_tenth_lt
  simp only [bDd]
  nlinarith

theorem abs_bDd_small (hh : 9 ≤ h) (hx0 : 0 < x) :
    -bDd h x ≤ -Real.log x := by
  have hβ0 := bBeta_pos hh
  simp only [bDd]
  nlinarith

/-! ### Convexity of `G` on the small range -/

/-- The key comparison behind `G'' > 0`: `η'(X(x)) > (2.0916) x (log x)²`. -/
theorem etaD_gt_log_sq (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hx0 : 0 < x) (hx : x ≤ 1 / 10) :
    20917 / 10000 * (x * (Real.log x) ^ 2) < etaD θ (bX h x) := by
  have hhpos : (0:ℝ) < h := by linarith
  rcases le_total x (1 / 30 : ℝ) with hsmall | hbig
  · -- very small `x`: the global lower bound `η' ≥ 97/100` suffices
    have hmono : x * (Real.log x) ^ 2 ≤ (1 / 30 : ℝ) * (Real.log (1 / 30 : ℝ)) ^ 2 :=
      Scalar.mul_log_sq_le hx0 hsmall (by norm_num)
    have hlog30 : Real.log (1 / 30 : ℝ) = -Real.log 30 := by
      rw [one_div, Real.log_inv]
    have hlog : (Real.log (1 / 30 : ℝ)) ^ 2 ≤ (7 / 2 : ℝ) ^ 2 := by
      rw [hlog30]
      have h1 := Scalar.log_thirty_lt
      have h2 := Scalar.log_thirty_gt
      nlinarith
    have h97 := etaD_small_ge hh hθ1 hθ0 hx0.le hx
    nlinarith
  · -- moderate `x`: `X(x)` is bounded away from `1`
    have hHle : H x ≤ 13 / 15 := by
      have hmono := H_antitoneOn (Set.mem_Icc.2 ⟨by norm_num, by norm_num⟩)
        (Set.mem_Icc.2 ⟨hx0.le, by linarith⟩) hbig
      have hH30 : H (1 / 30 : ℝ) ≤ 13 / 15 := by
        simp only [H]
        have hlog30 : Real.log (1 / 30 : ℝ) = -Real.log 30 := by
          rw [one_div, Real.log_inv]
        rw [hlog30]
        nlinarith [Scalar.log_thirty_gt]
      linarith
    have hβ := bBeta_lt hh
    have hβ0 := bBeta_pos hh
    have hC0 := bC_pos hh
    have hΔ := bDelta_gt hh
    have hXle : bX h x ≤ 8755 / 10000 := by
      rw [bX, bD, div_le_iff₀ (by linarith)]
      nlinarith
    have hXlo := bX_lower hh hx0.le hx
    have hq : (0:ℝ) ≤ -(1 - 4 * bX h x + 3 * (bX h x) ^ 2) := by nlinarith
    have hη : 124 / 100 ≤ etaD θ (bX h x) := by
      simp only [etaD]
      nlinarith [mul_nonneg (neg_nonneg.2 hθ0) hq]
    have hmono : x * (Real.log x) ^ 2 ≤ (1 / 10 : ℝ) * (Real.log (1 / 10 : ℝ)) ^ 2 :=
      Scalar.mul_log_sq_le hx0 hx (le_refl _)
    have hlog : (Real.log (1 / 10 : ℝ)) ^ 2 ≤ (7 / 3 : ℝ) ^ 2 := by
      have h1 := log_tenth_gt
      have h2 := log_tenth_lt
      nlinarith
    have hcomb : x * (Real.log x) ^ 2 ≤ (1 / 10 : ℝ) * (7 / 3 : ℝ) ^ 2 := by
      nlinarith
    nlinarith

/-- `G'' > 0` on `(0, 1/10]`, blueprint §7.1. -/
theorem bGd2_small_pos (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hx0 : 0 < x) (hx : x ≤ 1 / 10) : 0 < bGd2 h θ x := by
  have hhpos : (0:ℝ) < h := by linarith
  have hΔ := bDelta_gt hh
  have hΔ1 := bDelta_lt_one hhpos
  have hΔ0 : (0:ℝ) < bDelta h := by linarith
  have hsq0 := sqrtDelta_pos hhpos
  have hβ0 := bBeta_pos hh
  have hη2 := etaD2_small_ge hh hθ1 hθ0 hx0.le hx
  have hη2neg := etaD2_small_neg hh hθ1 hθ0 hx0.le hx
  have hηpos : 97 / 100 ≤ etaD θ (bX h x) := etaD_small_ge hh hθ1 hθ0 hx0.le hx
  have hkey := etaD_gt_log_sq hh hθ1 hθ0 hx0 hx
  -- the second derivative of `D`
  have hD2 : 1 / x ≤ bDd2 h x := by
    simp only [bDd2]; linarith
  have hD2div : 1 / x ≤ bDd2 h x / bDelta h := by
    have h1 : bDd2 h x / bDelta h ≥ bDd2 h x := by
      rw [ge_iff_le, le_div_iff₀ hΔ0]
      nlinarith [hD2, one_div_pos.2 hx0]
    linarith
  -- the square of `D'/Δ`
  have hDsq : (bDd h x / bDelta h) ^ 2 ≤ (Real.log x) ^ 2 / (99 / 100) ^ 2 := by
    have hb := abs_bDd_small hh hx0
    have hneg := bDd_small_neg hh hx0 hx
    have habs : |bDd h x / bDelta h| ≤ (-Real.log x) / (99 / 100) := by
      rw [abs_div, abs_of_pos hΔ0, abs_of_neg hneg, div_le_div_iff₀ hΔ0 (by norm_num)]
      nlinarith
    have hlogneg : Real.log x < 0 := by
      have : Real.log x < -(23 / 10) := lt_of_le_of_lt (Real.log_le_log hx0 hx) log_tenth_lt
      linarith
    calc (bDd h x / bDelta h) ^ 2 = |bDd h x / bDelta h| ^ 2 := (sq_abs _).symm
      _ ≤ ((-Real.log x) / (99 / 100)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = (Real.log x) ^ 2 / (99 / 100) ^ 2 := by rw [div_pow]; ring_nf
  have hinner : 0 < etaD2 θ (bX h x) * (bDd h x / bDelta h) ^ 2
      + etaD θ (bX h x) * (bDd2 h x / bDelta h) := by
    have h1 : etaD2 θ (bX h x) * (bDd h x / bDelta h) ^ 2
        ≥ etaD2 θ (bX h x) * ((Real.log x) ^ 2 / (99 / 100) ^ 2) := by
      nlinarith [hDsq, hη2neg]
    have h2 : etaD θ (bX h x) * (bDd2 h x / bDelta h) ≥ etaD θ (bX h x) * (1 / x) := by
      nlinarith [hD2div, hηpos]
    have h3 : etaD θ (bX h x) * (1 / x) > 20917 / 10000 * (Real.log x) ^ 2 := by
      rw [gt_iff_lt, mul_one_div, lt_div_iff₀ hx0]
      nlinarith [hkey]
    have h4 : etaD2 θ (bX h x) * ((Real.log x) ^ 2 / (99 / 100) ^ 2)
        ≥ -(20917 / 10000) * (Real.log x) ^ 2 := by
      have : (Real.log x) ^ 2 / (99 / 100) ^ 2 = (10000 / 9801) * (Real.log x) ^ 2 := by
        field_simp; ring
      rw [this]
      nlinarith [sq_nonneg (Real.log x), hη2]
    linarith
  simp only [bGd2]
  positivity

/-! ### The convex box `0 < x ≤ 1/1080` -/

theorem bX_convex_ge (hh : 9 ≤ h) (hx0 : 0 < x) (hx : x ≤ 1 / 1080) :
    9885 / 10000 ≤ bX h x := by
  have hhpos : (0:ℝ) < h := by linarith
  have hΔ1 := bDelta_lt_one hhpos
  have hΔ0 := bDelta_pos hhpos
  have hβ0 := bBeta_pos hh
  have hC := bC_lt hh
  have hxlog : x * (-Real.log x) ≤ (1 / 1080 : ℝ) * (-Real.log (1 / 1080 : ℝ)) :=
    Scalar.mul_neg_log_le hx0.le hx (by norm_num) (by norm_num)
  have hlog1080 : -Real.log (1 / 1080 : ℝ) = Real.log 1080 := by
    rw [one_div, Real.log_inv, neg_neg]
  have hxlog' : x * (-Real.log x) ≤ 7 / 1080 := by
    rw [hlog1080] at hxlog
    nlinarith [Scalar.log_1080_lt]
  have hH : 1 - 1 / 1080 - 7 / 1080 ≤ H x := by
    simp only [H]
    nlinarith
  have hD : 98859 / 100000 ≤ bD h x := by
    simp only [bD]
    nlinarith [sq_nonneg x, mul_nonneg hβ0.le (sq_nonneg x)]
  rw [bX, le_div_iff₀ hΔ0]
  nlinarith

theorem etaT_convex_ge (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ)
    (hx0 : 0 < x) (hx : x ≤ 1 / 1080) : 987 / 1000 ≤ etaT θ (bX h x) := by
  have hlo := bX_convex_ge hh hx0 hx
  have hhi := bX_upper hh hx0.le (by linarith)
  simp only [etaT]
  nlinarith [sq_nonneg (1 - bX h x), mul_nonneg (by linarith : (0:ℝ) ≤ bX h x)
    (sq_nonneg (1 - bX h x))]

theorem etaT_convex_le (hh : 9 ≤ h) (hθ0 : θ ≤ 0)
    (hx0 : 0 < x) (hx : x ≤ 1 / 1080) : etaT θ (bX h x) ≤ 1011 / 1000 := by
  have hlo := bX_convex_ge hh hx0 hx
  have hhi := bX_upper hh hx0.le (by linarith)
  simp only [etaT]
  nlinarith [sq_nonneg (1 - bX h x), mul_nonneg (by linarith : (0:ℝ) ≤ bX h x)
    (sq_nonneg (1 - bX h x))]

theorem etaD_convex_le (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hx0 : 0 < x) (hx : x ≤ 1 / 1080) : etaD θ (bX h x) ≤ 103 / 100 := by
  have hlo := bX_convex_ge hh hx0 hx
  have hhi := bX_upper hh hx0.le (by linarith)
  simp only [etaD]
  nlinarith [sq_nonneg (bX h x - 1)]

/-- `|G'(x)| ≤ (43/100)|log x|` on the convex box. -/
theorem abs_bGd_convex (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hx0 : 0 < x) (hx : x ≤ 1 / 1080) :
    |bGd h θ x| ≤ 43 / 100 * (-Real.log x) := by
  have hhpos : (0:ℝ) < h := by linarith
  have hΔ := bDelta_gt hh
  have hΔ1 := bDelta_lt_one hhpos
  have hΔ0 : (0:ℝ) < bDelta h := by linarith
  have hsq := sqrtDelta_le hhpos
  have hsq0 := (sqrtDelta_pos hhpos).le
  have hηle := etaD_convex_le hh hθ1 hθ0 hx0 hx
  have hηge := etaD_small_ge hh hθ1 hθ0 hx0.le (by linarith)
  have hneg := bDd_small_neg hh hx0 (by linarith)
  have hbd := abs_bDd_small hh hx0
  have hlogneg : Real.log x < 0 := by
    have : Real.log x < -(23 / 10) := lt_of_le_of_lt (Real.log_le_log hx0 (by linarith)) log_tenth_lt
    linarith
  have hdiv : |bDd h x / bDelta h| ≤ (-Real.log x) / (99 / 100) := by
    rw [abs_div, abs_of_pos hΔ0, abs_of_neg hneg, div_le_div_iff₀ hΔ0 (by norm_num)]
    nlinarith
  have hprod : |etaD θ (bX h x) * (bDd h x / bDelta h)|
      ≤ (103 / 100) * ((-Real.log x) / (99 / 100)) := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.2 ⟨by linarith, hηle⟩) hdiv (abs_nonneg _) (by norm_num)
  simp only [bGd]
  rw [abs_mul, abs_of_nonneg hsq0]
  have hbound : Real.sqrt (bDelta h / 6) * |etaD θ (bX h x) * (bDd h x / bDelta h)|
      ≤ (41 / 100) * ((103 / 100) * ((-Real.log x) / (99 / 100))) :=
    mul_le_mul hsq hprod (abs_nonneg _) (by norm_num)
  have hfinal : (41 / 100 : ℝ) * ((103 / 100) * ((-Real.log x) / (99 / 100)))
      ≤ 43 / 100 * (-Real.log x) := by
    rw [div_eq_mul_inv]
    nlinarith [hlogneg]
  linarith

end
end Branch
end TriangleNumerical
