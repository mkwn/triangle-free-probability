import TriangleNumerical.ScalarAux
import TriangleNumerical.Deriv

/-!
# The high coordinate range `19/20 ≤ w ≤ 1`

Section 7.2 of the blueprint, first half.  For every branch parameter `h ≥ 9`
and every `θ ∈ [-1/50, 0]` we certify, uniformly on `[19/20, 1]`:

```
0 ≤ X(w) ≤ 7/5000,      -1 ≤ η(X(w)) ≤ -199/200,
|D'(w)| ≤ 39/760,       1 ≤ D''(w) ≤ 20/19 + 1/250,
|G'(w)| ≤ 13/200,       |G''(w)| ≤ 4/3.
```

The Taylor estimate at `t` is replaced by the exact identity
`D(w) = t·H(w/t) + β(w-t)²` together with the quadratic bound for `H` near `1`.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Branch
noncomputable section

open Real

variable {h θ w : ℝ}

/-! ### The exact shape identity and nonnegativity of `D` -/

/-- `D(w) = t·H(w/t) + β(w-t)²` for every `w > 0`. -/
theorem bD_eq_scaled (h : ℝ) (hw : 0 < w) :
    bD h w = bt h * H (w / bt h) + bBeta h * (w - bt h) ^ 2 := by
  have ht := bt_pos h
  have hlog : Real.log (w / bt h) = Real.log w - Real.log (bt h) :=
    Real.log_div (ne_of_gt hw) (ne_of_gt ht)
  have hlt : Real.log (bt h) = -bp h := log_bt_eq h
  simp only [bD, H, bBeta, bC, hlog, hlt]
  field_simp
  ring

/-- `D ≥ 0` on the nonnegative axis. -/
theorem bD_nonneg (hh : 0 < h) (hw : 0 ≤ w) : 0 ≤ bD h w := by
  rcases eq_or_lt_of_le hw with h0 | hpos
  · have ht := bt_pos h
    have hp := bp_pos hh
    have hD : bD h 0 = (1 + bp h / 2) * bt h := by
      simp only [bD, H, bC]
      norm_num
    rw [← h0, hD]
    positivity
  · rw [bD_eq_scaled h hpos]
    have h1 : 0 ≤ bt h * H (w / bt h) :=
      mul_nonneg (bt_pos h).le
        (entropy_nonnegative _ (div_nonneg hpos.le (bt_pos h).le))
    have hβ : 0 < bBeta h := by
      have : bBeta h = bp h / (2 * bt h) := rfl
      rw [this]
      exact div_pos (bp_pos hh) (by linarith [bt_pos h])
    nlinarith [sq_nonneg (w - bt h)]

/-! ### `X` on the high range -/

theorem bX_high_nonneg (hh : 9 ≤ h) (hw : 19 / 20 ≤ w) : 0 ≤ bX h w := by
  have hhpos : (0:ℝ) < h := by linarith
  exact div_nonneg (bD_nonneg hhpos (by linarith)) (bDelta_pos hhpos).le

theorem bD_high_le (hh : 9 ≤ h) (hw : 19 / 20 ≤ w) (hw1 : w ≤ 1) :
    bD h w ≤ 67 / 50000 := by
  have hhpos : (0:ℝ) < h := by linarith
  have ht0 := bt_pos h
  have ht1 := bt_lt_one hhpos
  have htg := bt_gt hh
  have hw0 : (0:ℝ) < w := by linarith
  have hβ := bBeta_lt hh
  have hβ0 := bBeta_pos hh
  have hu : 19 / 20 ≤ w / bt h := by
    rw [le_div_iff₀ ht0]
    nlinarith
  have hHu : H (w / bt h) ≤ 10 / 19 * (w / bt h - 1) ^ 2 := Scalar.H_le_quad hu
  have hsq : (w - bt h) ^ 2 ≤ 1 / 400 := by
    rcases le_total w (bt h) with hle | hge
    · nlinarith
    · nlinarith
  have hid := bD_eq_scaled h hw0
  have hfrac : (w / bt h - 1) ^ 2 = (w - bt h) ^ 2 / (bt h) ^ 2 := by
    field_simp
  have hkey : bt h * H (w / bt h) ≤ 10 / 19 * (w - bt h) ^ 2 / bt h := by
    have h1 : bt h * H (w / bt h) ≤ bt h * (10 / 19 * (w / bt h - 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hHu ht0.le
    rw [hfrac] at h1
    have h2 : bt h * (10 / 19 * ((w - bt h) ^ 2 / (bt h) ^ 2))
        = 10 / 19 * (w - bt h) ^ 2 / bt h := by
      field_simp
    linarith [h1, h2.le, h2.ge]
  have hbnd : 10 / 19 * (w - bt h) ^ 2 / bt h ≤ 1 / 750 := by
    rw [div_le_iff₀ ht0]
    nlinarith
  have hβsq : bBeta h * (w - bt h) ^ 2 ≤ (1 / 500) * (1 / 400) := by
    nlinarith [sq_nonneg (w - bt h)]
  rw [hid]
  nlinarith

theorem bX_high_le (hh : 9 ≤ h) (hw : 19 / 20 ≤ w) (hw1 : w ≤ 1) :
    bX h w ≤ 7 / 5000 := by
  have hhpos : (0:ℝ) < h := by linarith
  have hΔ := bDelta_gt hh
  have hD := bD_high_le hh hw hw1
  rw [bX, div_le_iff₀ (by linarith)]
  nlinarith

/-! ### `η` and its derivatives on the high range -/

theorem etaT_high_le {X : ℝ} (hθ0 : θ ≤ 0)
    (hX0 : 0 ≤ X) (hX : X ≤ 7 / 5000) : etaT θ X ≤ -(199 / 200) := by
  simp only [etaT]
  nlinarith [sq_nonneg X, sq_nonneg (1 - X), mul_nonneg hX0 (sq_nonneg (1 - X))]

theorem etaT_high_ge {X : ℝ} (hθ1 : -(1 / 50 : ℝ) ≤ θ)
    (hX0 : 0 ≤ X) (hX : X ≤ 7 / 5000) : -1 ≤ etaT θ X := by
  simp only [etaT]
  nlinarith [sq_nonneg X, sq_nonneg (1 - X), mul_nonneg hX0 (sq_nonneg (1 - X))]

theorem etaD_high_le {X : ℝ} (hθ0 : θ ≤ 0) (hX0 : 0 ≤ X) (hX : X ≤ 7 / 5000) :
    etaD θ X ≤ 3 := by
  simp only [etaD]
  nlinarith [sq_nonneg X]

theorem etaD_high_ge {X : ℝ} (hθ1 : -(1 / 50 : ℝ) ≤ θ)
    (hX0 : 0 ≤ X) (hX : X ≤ 7 / 5000) : 297 / 100 ≤ etaD θ X := by
  simp only [etaD]
  nlinarith [sq_nonneg X]

theorem abs_etaD2_high {X : ℝ} (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hX0 : 0 ≤ X) (hX : X ≤ 7 / 5000) : |etaD2 θ X| ≤ 2 := by
  rw [abs_le]
  constructor <;> · simp only [etaD2]; nlinarith

/-! ### `D'` and `D''` on the high range -/

theorem abs_bDd_high (hh : 9 ≤ h) (hw : 19 / 20 ≤ w) (hw1 : w ≤ 1) :
    |bDd h w| ≤ 39 / 760 := by
  have hβ := bBeta_lt hh
  have hβ0 := bBeta_pos hh
  have hlog0 : Real.log w ≤ 0 := Real.log_nonpos (by linarith) hw1
  have hlog : -Real.log w ≤ 39 / 760 := Scalar.neg_log_high_le hw
  rw [abs_le]
  simp only [bDd]
  constructor
  · nlinarith
  · nlinarith

theorem bDd2_high_ge (hh : 9 ≤ h) (hw : 19 / 20 ≤ w) (hw1 : w ≤ 1) :
    1 ≤ bDd2 h w := by
  have hβ0 := bBeta_pos hh
  have hw0 : (0:ℝ) < w := by linarith
  simp only [bDd2]
  have : (1:ℝ) ≤ 1 / w := by
    rw [le_div_iff₀ hw0]; linarith
  linarith

theorem bDd2_high_le (hh : 9 ≤ h) (hw : 19 / 20 ≤ w) :
    bDd2 h w ≤ 20 / 19 + 1 / 250 := by
  have hβ := bBeta_lt hh
  have hw0 : (0:ℝ) < w := by linarith
  simp only [bDd2]
  have : (1:ℝ) / w ≤ 20 / 19 := by
    rw [div_le_iff₀ hw0]; linarith
  linarith

/-! ### The square root factor -/

theorem sqrtDelta_pos (hh : 0 < h) : 0 < Real.sqrt (bDelta h / 6) :=
  Real.sqrt_pos.2 (by linarith [bDelta_pos hh])

theorem sqrtDelta_le (hh : 0 < h) : Real.sqrt (bDelta h / 6) ≤ 41 / 100 := by
  have h1 : bDelta h / 6 ≤ (41 / 100 : ℝ) ^ 2 := by
    have := bDelta_lt_one hh
    nlinarith
  calc Real.sqrt (bDelta h / 6) ≤ Real.sqrt ((41 / 100 : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
    _ = 41 / 100 := by rw [Real.sqrt_sq (by norm_num)]

theorem sqrtDelta_ge (hh : 9 ≤ h) : 2 / 5 ≤ Real.sqrt (bDelta h / 6) := by
  have hΔ := bDelta_gt hh
  have h1 : ((2 : ℝ) / 5) ^ 2 ≤ bDelta h / 6 := by nlinarith
  calc (2:ℝ) / 5 = Real.sqrt (((2:ℝ) / 5) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (bDelta h / 6) := Real.sqrt_le_sqrt h1

/-! ### `G`, `G'` and `G''` on the high range -/

theorem bG_high_neg (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hw : 19 / 20 ≤ w) (hw1 : w ≤ 1) : bG h θ w ≤ -(2 / 5) * (199 / 200) := by
  have hhpos : (0:ℝ) < h := by linarith
  have hsq := sqrtDelta_ge hh
  have hsq0 := sqrtDelta_pos hhpos
  have hη := etaT_high_le (θ := θ) hθ0 (bX_high_nonneg hh hw) (bX_high_le hh hw hw1)
  have hηge := etaT_high_ge (θ := θ) hθ1 (bX_high_nonneg hh hw) (bX_high_le hh hw hw1)
  simp only [bG]
  nlinarith

theorem bG_high_ge (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hw : 19 / 20 ≤ w) (hw1 : w ≤ 1) : -(41 / 100 : ℝ) ≤ bG h θ w := by
  have hhpos : (0:ℝ) < h := by linarith
  have hsq := sqrtDelta_le hhpos
  have hsq0 := sqrtDelta_pos hhpos
  have hηge := etaT_high_ge (θ := θ) hθ1 (bX_high_nonneg hh hw) (bX_high_le hh hw hw1)
  have hη := etaT_high_le (θ := θ) hθ0 (bX_high_nonneg hh hw) (bX_high_le hh hw hw1)
  simp only [bG]
  nlinarith

/-- `|D'(w)/Δ| ≤ 519/10000` on the high range. -/
theorem abs_bDd_div_high (hh : 9 ≤ h) (hw : 19 / 20 ≤ w) (hw1 : w ≤ 1) :
    |bDd h w / bDelta h| ≤ 519 / 10000 := by
  have hhpos : (0:ℝ) < h := by linarith
  have hΔ := bDelta_gt hh
  have hΔ0 : (0:ℝ) < bDelta h := by linarith
  rw [abs_div, abs_of_pos hΔ0, div_le_iff₀ hΔ0]
  nlinarith [abs_bDd_high hh hw hw1, abs_nonneg (bDd h w)]

/-- `D''(w)/Δ ≤ 107/100` on the high range. -/
theorem bDd2_div_high_le (hh : 9 ≤ h) (hw : 19 / 20 ≤ w) :
    bDd2 h w / bDelta h ≤ 107 / 100 := by
  have hhpos : (0:ℝ) < h := by linarith
  have hΔ := bDelta_gt hh
  have hΔ1 := bDelta_lt_one hhpos
  have hΔ0 : (0:ℝ) < bDelta h := by linarith
  rw [div_le_iff₀ hΔ0]
  nlinarith [bDd2_high_le hh hw]

theorem bDd2_div_high_nonneg (hh : 9 ≤ h) (hw : 19 / 20 ≤ w) (hw1 : w ≤ 1) :
    0 ≤ bDd2 h w / bDelta h := by
  have hhpos : (0:ℝ) < h := by linarith
  exact div_nonneg (by linarith [bDd2_high_ge hh hw hw1]) (bDelta_pos hhpos).le

theorem abs_bGd_high (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hw : 19 / 20 ≤ w) (hw1 : w ≤ 1) : |bGd h θ w| ≤ 13 / 200 := by
  have hhpos : (0:ℝ) < h := by linarith
  have hΔ := bDelta_gt hh
  have hΔ0 : (0:ℝ) < bDelta h := by linarith
  have hsq := sqrtDelta_le hhpos
  have hsq0 := (sqrtDelta_pos hhpos).le
  have hηle := etaD_high_le (θ := θ) hθ0 (bX_high_nonneg hh hw) (bX_high_le hh hw hw1)
  have hηge := etaD_high_ge (θ := θ) hθ1 (bX_high_nonneg hh hw) (bX_high_le hh hw hw1)
  have hdiv := abs_bDd_div_high hh hw hw1
  have hηabs : |etaD θ (bX h w)| ≤ 3 := abs_le.2 ⟨by linarith, hηle⟩
  have hprod : |etaD θ (bX h w) * (bDd h w / bDelta h)| ≤ 3 * (519 / 10000) := by
    rw [abs_mul]
    exact mul_le_mul hηabs hdiv (abs_nonneg _) (by norm_num)
  simp only [bGd]
  rw [abs_mul, abs_of_nonneg hsq0]
  calc Real.sqrt (bDelta h / 6) * |etaD θ (bX h w) * (bDd h w / bDelta h)|
      ≤ (41 / 100) * (3 * (519 / 10000)) :=
        mul_le_mul hsq hprod (abs_nonneg _) (by norm_num)
    _ ≤ 13 / 200 := by norm_num

theorem abs_bGd2_high (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hw : 19 / 20 ≤ w) (hw1 : w ≤ 1) : |bGd2 h θ w| ≤ 4 / 3 := by
  have hhpos : (0:ℝ) < h := by linarith
  have hΔ := bDelta_gt hh
  have hΔ1 := bDelta_lt_one hhpos
  have hΔ0 : (0:ℝ) < bDelta h := by linarith
  have hsq := sqrtDelta_le hhpos
  have hsq0 := (sqrtDelta_pos hhpos).le
  have hηle := etaD_high_le (θ := θ) hθ0 (bX_high_nonneg hh hw) (bX_high_le hh hw hw1)
  have hηge := etaD_high_ge (θ := θ) hθ1 (bX_high_nonneg hh hw) (bX_high_le hh hw hw1)
  have hη2 := abs_etaD2_high (θ := θ) hθ1 hθ0 (bX_high_nonneg hh hw) (bX_high_le hh hw hw1)
  have hD2ge := bDd2_high_ge hh hw hw1
  rw [abs_le] at hη2
  have h1 := abs_bDd_div_high hh hw hw1
  have hsqd : (bDd h w / bDelta h) ^ 2 ≤ (519 / 10000 : ℝ) ^ 2 := by
    calc (bDd h w / bDelta h) ^ 2 = |bDd h w / bDelta h| ^ 2 := (sq_abs _).symm
      _ ≤ (519 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hsqd0 : 0 ≤ (bDd h w / bDelta h) ^ 2 := sq_nonneg _
  have hd2 := bDd2_div_high_le hh hw
  have hd20 := bDd2_div_high_nonneg hh hw hw1
  have hinner : |etaD2 θ (bX h w) * (bDd h w / bDelta h) ^ 2
      + etaD θ (bX h w) * (bDd2 h w / bDelta h)| ≤ 3216 / 1000 := by
    rw [abs_le]
    constructor <;> nlinarith
  simp only [bGd2]
  rw [abs_mul, abs_of_nonneg hsq0]
  calc Real.sqrt (bDelta h / 6) * |etaD2 θ (bX h w) * (bDd h w / bDelta h) ^ 2
        + etaD θ (bX h w) * (bDd2 h w / bDelta h)|
      ≤ (41 / 100) * (3216 / 1000) := mul_le_mul hsq hinner (abs_nonneg _) (by norm_num)
    _ ≤ 4 / 3 := by norm_num

end
end Branch
end TriangleNumerical
