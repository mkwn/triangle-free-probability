import TriangleNumerical.SmallCoord
import TriangleNumerical.LineDeriv
import TriangleNumerical.Segment

/-!
# Analytic region B: one small and two large weights

Section 7 of the blueprint (A2).  For every `h ≥ 9` and every `θ ∈ [-1/50, 0]`,

```
0 ≤ x ≤ 1/10,  19/20 ≤ y, z ≤ 1   ⟹   Φ(x,y,z) ≥ M₂(h).
```

The proof has two halves, separated by `L = 1/(30 α²)`:

* on the convex box `(0, L] × [19/20, 1]²` the spatial Hessian is positive
  definite in the scalar sense of `scalar_mixed_form`, and the sharp point
  `(r,t,t)` — which lies in the box and is stationary with value `M₂` — is
  joined to the target by a segment along which the objective is convex;
* on `[L, 1/10] × [19/20, 1]²` the objective increases in the small
  coordinate, because `Φ_xx > 0` there and `Φ_x(L,y,z) > 0`.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Branch
noncomputable section

open Real

variable {h θ x y z : ℝ}

/-! ### The convex-box endpoint `L` -/

/-- The endpoint `L = 1/(30 α²)` of the convex box. -/
def bL (h : ℝ) : ℝ := 1 / (30 * (bAlpha h) ^ 2)

theorem bL_pos (hh : 9 ≤ h) : 0 < bL h := by
  have := bAlpha_pos (by linarith : (0:ℝ) < h)
  unfold bL
  positivity

theorem bL_le (hh : 9 ≤ h) : bL h ≤ 1 / 1080 := by
  have hα := bAlpha_ge_six hh
  have : (1080:ℝ) ≤ 30 * (bAlpha h) ^ 2 := by nlinarith
  unfold bL
  rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
  linarith

theorem alpha_mul_bL_le (hh : 9 ≤ h) : bAlpha h * bL h ≤ 1 / 180 := by
  have hα := bAlpha_ge_six hh
  have h0 : (0:ℝ) < bAlpha h := by linarith
  unfold bL
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem br_le_bL (hh : 9 ≤ h) : br h ≤ bL h := by
  have hαr := alpha_sq_r_lt hh
  have hα := bAlpha_ge_six hh
  have h0 : (0:ℝ) < bAlpha h := by linarith
  have hr := br_pos h
  unfold bL
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-! ### Stationarity of the sharp point `(r,t,t)` -/

theorem bDd_bt (h : ℝ) : bDd h (bt h) = 0 := by
  have ht := bt_pos h
  have hlog : Real.log (bt h) = -bp h := log_bt_eq h
  have hbeta : bBeta h = bp h / (2 * bt h) := rfl
  simp only [bDd, hlog, hbeta]
  field_simp
  ring

theorem bGd_bt (h θ : ℝ) : bGd h θ (bt h) = 0 := by
  simp only [bGd, bDd_bt]
  ring

theorem etaD_one (θ : ℝ) : etaD θ 1 = 1 := by simp only [etaD]; ring

theorem bGd_br (hh : 0 < h) :
    bGd h θ (br h) = Real.sqrt (bDelta h / 6) * (bDd h (br h) / bDelta h) := by
  simp only [bGd, bX_r hh, etaD_one]
  ring

/-- The first partial derivative of `Φ` in the small coordinate, in the form
used by `lineD1`. -/
def phiX (h θ x y z : ℝ) : ℝ :=
  Real.log x / 3 + bAlpha h * y * z - bGd h θ x * (bG h θ y + bG h θ z)

theorem hasDerivAt_phiX_obj (y z : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun u : ℝ => entropyF (bAlpha h) (bG h θ) u y z) (phiX h θ x y z) x := by
  have hH : HasDerivAt (fun u : ℝ => (H u + H y + H z) / 3) (Real.log x / 3) x :=
    (((hasDerivAt_H hx).add_const _).add_const _).div_const 3
  have hcube : HasDerivAt (fun u : ℝ => bAlpha h * u * y * z) (bAlpha h * y * z) x := by
    simpa using (((hasDerivAt_id x).const_mul (bAlpha h)).mul_const y).mul_const z
  have hG := hasDerivAt_bG h θ (w := x) hx
  have hpair : HasDerivAt
      (fun u : ℝ => bG h θ u * bG h θ y + bG h θ u * bG h θ z + bG h θ y * bG h θ z)
      (bGd h θ x * (bG h θ y + bG h θ z)) x := by
    have := ((hG.mul_const (bG h θ y)).add (hG.mul_const (bG h θ z))).add_const
      (bG h θ y * bG h θ z)
    convert this using 1
    ring
  have := (hH.add hcube).sub hpair
  convert this using 1

/-- The second derivative in the small coordinate. -/
def phiXX (h θ x y z : ℝ) : ℝ :=
  1 / (3 * x) - bGd2 h θ x * (bG h θ y + bG h θ z)

theorem hasDerivAt_phiX (y z : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun u : ℝ => phiX h θ u y z) (phiXX h θ x y z) x := by
  have hlog : HasDerivAt (fun u : ℝ => Real.log u / 3) (x⁻¹ / 3) x :=
    (Real.hasDerivAt_log hx).div_const 3
  have hg := hasDerivAt_bGd h θ (w := x) hx
  have hpair : HasDerivAt (fun u : ℝ => bGd h θ u * (bG h θ y + bG h θ z))
      (bGd2 h θ x * (bG h θ y + bG h θ z)) x := hg.mul_const _
  have := (hlog.add_const (bAlpha h * y * z)).sub hpair
  convert this using 1
  simp only [phiXX]
  field_simp

/-- Stationarity of `Φ` at `(r,t,t)` in the first coordinate. -/
theorem phiX_at_sharp (hh : 0 < h) : phiX h θ (br h) (bt h) (bt h) = 0 := by
  have hsq2 : Real.sqrt (bDelta h / 6) ^ 2 = bDelta h / 6 :=
    Real.sq_sqrt (by linarith [bDelta_pos hh] : (0:ℝ) ≤ bDelta h / 6)
  have hΔ : bDelta h ≠ 0 := ne_of_gt (bDelta_pos hh)
  have hlogr := log_br hh
  have hbeta := bBeta_eq hh
  simp only [phiX, bGd_br hh, bG_t h θ, bDd, hlogr, hbeta]
  field_simp
  linear_combination (6 * bAlpha h * (br h ^ 2 - bt h ^ 2)) * hsq2

/-- Stationarity of `Φ` at `(r,t,t)` in the second (and third) coordinate. -/
theorem phiX_at_sharp' (hh : 0 < h) : phiX h θ (bt h) (br h) (bt h) = 0 := by
  have hlogt := log_bt hh
  simp only [phiX, bGd_bt, hlogt]
  ring

/-! ### The Hessian estimates on the convex box -/

theorem bG_sum_high (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hy : 19 / 20 ≤ y) (hy1 : y ≤ 1) (hz : 19 / 20 ≤ z) (hz1 : z ≤ 1) :
    bG h θ y + bG h θ z ≤ -(79 / 100) := by
  have h1 := bG_high_neg hh hθ1 hθ0 hy hy1
  have h2 := bG_high_neg hh hθ1 hθ0 hz hz1
  linarith

theorem bG_sum_high_ge (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hy : 19 / 20 ≤ y) (hy1 : y ≤ 1) (hz : 19 / 20 ≤ z) (hz1 : z ≤ 1) :
    -(82 / 100 : ℝ) ≤ bG h θ y + bG h θ z := by
  have h1 := bG_high_ge hh hθ1 hθ0 hy hy1
  have h2 := bG_high_ge hh hθ1 hθ0 hz hz1
  linarith

theorem bG_sum_mixed (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hx0 : 0 < x) (hx : x ≤ 1 / 1080) (hz : 19 / 20 ≤ z) (hz1 : z ≤ 1) :
    |bG h θ x + bG h θ z| ≤ 7 / 1000 := by
  have hhpos : (0:ℝ) < h := by linarith
  have hsq := sqrtDelta_le hhpos
  have hsq0 := (sqrtDelta_pos hhpos).le
  have hx1 := etaT_convex_ge hh hθ1 hx0 hx
  have hx2 := etaT_convex_le hh hθ0 hx0 hx
  have hz1' := etaT_high_ge (θ := θ) hθ1 (bX_high_nonneg hh hz) (bX_high_le hh hz hz1)
  have hz2 := etaT_high_le (θ := θ) hθ0 (bX_high_nonneg hh hz) (bX_high_le hh hz hz1)
  have hfac : bG h θ x + bG h θ z
      = Real.sqrt (bDelta h / 6) * (etaT θ (bX h x) + etaT θ (bX h z)) := by
    simp only [bG]; ring
  rw [hfac, abs_mul, abs_of_nonneg hsq0]
  have habs : |etaT θ (bX h x) + etaT θ (bX h z)| ≤ 16 / 1000 := by
    rw [abs_le]; constructor <;> linarith
  calc Real.sqrt (bDelta h / 6) * |etaT θ (bX h x) + etaT θ (bX h z)|
      ≤ (41 / 100) * (16 / 1000) := mul_le_mul hsq habs (abs_nonneg _) (by norm_num)
    _ ≤ 7 / 1000 := by norm_num

theorem hess_xx (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hx0 : 0 < x) (hx : x ≤ 1 / 10)
    (hy : 19 / 20 ≤ y) (hy1 : y ≤ 1) (hz : 19 / 20 ≤ z) (hz1 : z ≤ 1) :
    1 / (3 * x) ≤ phiXX h θ x y z := by
  have hG := bGd2_small_pos hh hθ1 hθ0 hx0 hx
  have hsum := bG_sum_high hh hθ1 hθ0 hy hy1 hz hz1
  have hprod : bGd2 h θ x * (bG h θ y + bG h θ z) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hG.le (by linarith)
  simp only [phiXX]
  linarith

theorem hess_yy (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hx0 : 0 < x) (hx : x ≤ 1 / 1080)
    (hy : 19 / 20 ≤ y) (hy1 : y ≤ 1) (hz : 19 / 20 ≤ z) (hz1 : z ≤ 1) :
    8 / 25 ≤ 1 / (3 * y) - bGd2 h θ y * (bG h θ x + bG h θ z) := by
  have hmix := bG_sum_mixed hh hθ1 hθ0 hx0 hx hz hz1
  have hG2 := abs_bGd2_high hh hθ1 hθ0 hy hy1
  have hy0 : (0:ℝ) < y := by linarith
  have hinv : 1 / 3 ≤ 1 / (3 * y) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hprod : |bGd2 h θ y * (bG h θ x + bG h θ z)| ≤ (4 / 3) * (7 / 1000) := by
    rw [abs_mul]
    exact mul_le_mul hG2 hmix (abs_nonneg _) (by norm_num)
  rw [abs_le] at hprod
  linarith [hprod.1, hprod.2]

theorem hess_yz (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hx0 : 0 < x) (hx : x ≤ bL h)
    (hy : 19 / 20 ≤ y) (hy1 : y ≤ 1) (hz : 19 / 20 ≤ z) (hz1 : z ≤ 1) :
    |bAlpha h * x - bGd h θ y * bGd h θ z| ≤ 1 / 100 := by
  have hhpos : (0:ℝ) < h := by linarith
  have hα := bAlpha_ge_six hh
  have hαL := alpha_mul_bL_le hh
  have hαx : bAlpha h * x ≤ 1 / 180 := by
    have : bAlpha h * x ≤ bAlpha h * bL h :=
      mul_le_mul_of_nonneg_left hx (by linarith)
    linarith
  have hαx0 : 0 ≤ bAlpha h * x := by positivity
  have h1 := abs_bGd_high hh hθ1 hθ0 hy hy1
  have h2 := abs_bGd_high hh hθ1 hθ0 hz hz1
  have hprod : |bGd h θ y * bGd h θ z| ≤ (13 / 200) * (13 / 200) := by
    rw [abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
  rw [abs_le] at hprod ⊢
  constructor <;> linarith [hprod.1, hprod.2]

set_option maxHeartbeats 1000000 in
theorem hess_xy (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hx0 : 0 < x) (hx : x ≤ bL h)
    (hy : 19 / 20 ≤ y) (hy1 : y ≤ 1) (hz : 19 / 20 ≤ z) (hz1 : z ≤ 1) :
    x * (bAlpha h * z - bGd h θ x * bGd h θ y) ^ 2 ≤ 1 / 25 := by
  have hhpos : (0:ℝ) < h := by linarith
  have hα := bAlpha_ge_six hh
  have hα0 : (0:ℝ) < bAlpha h := by linarith
  have hL := bL_le hh
  have hL0 := bL_pos hh
  have hxL : x ≤ 1 / 1080 := le_trans hx hL
  have hx10 : x ≤ 1 / 10 := by linarith
  -- the logarithm of the box endpoint
  have hLlog : -Real.log (bL h) = Real.log (30 * (bAlpha h) ^ 2) := by
    unfold bL
    rw [one_div, Real.log_inv, neg_neg]
  have hΛL : Real.log (30 * (bAlpha h) ^ 2) ≤ 5 + bAlpha h / 3 := Scalar.log_thirty_sq_le hα
  have hΛL0 : 0 ≤ Real.log (30 * (bAlpha h) ^ 2) := by
    have : (1:ℝ) ≤ 30 * (bAlpha h) ^ 2 := by nlinarith
    exact Real.log_nonneg this
  -- three scalar bounds
  have hxa : x * (bAlpha h) ^ 2 ≤ 1 / 30 := by
    have : x ≤ 1 / (30 * (bAlpha h) ^ 2) := hx
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hmono1 : x * (-Real.log x) ≤ bL h * (-Real.log (bL h)) :=
    Scalar.mul_neg_log_le hx0.le hx hL0
      (by linarith)
  have hxl : x * (-Real.log x) ≤ (5 + bAlpha h / 3) / (30 * (bAlpha h) ^ 2) := by
    have hb : bL h * (-Real.log (bL h)) ≤ (5 + bAlpha h / 3) / (30 * (bAlpha h) ^ 2) := by
      rw [hLlog]
      have : bL h = 1 / (30 * (bAlpha h) ^ 2) := rfl
      rw [this, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hmono2 : x * (Real.log x) ^ 2 ≤ bL h * (Real.log (bL h)) ^ 2 :=
    Scalar.mul_log_sq_le hx0 hx (by linarith)
  have hxl2 : x * (Real.log x) ^ 2 ≤ (5 + bAlpha h / 3) ^ 2 / (30 * (bAlpha h) ^ 2) := by
    have hsq : (Real.log (bL h)) ^ 2 ≤ (5 + bAlpha h / 3) ^ 2 := by
      have h1 : Real.log (bL h) = -Real.log (30 * (bAlpha h) ^ 2) := by
        rw [← hLlog]; ring
      rw [h1]
      nlinarith
    have hb : bL h * (Real.log (bL h)) ^ 2 ≤ (5 + bAlpha h / 3) ^ 2 / (30 * (bAlpha h) ^ 2) := by
      have hbL : bL h = 1 / (30 * (bAlpha h) ^ 2) := rfl
      rw [hbL, div_mul_eq_mul_div, one_mul]
      apply div_le_div_of_nonneg_right hsq (by positivity)
    linarith
  -- the derivative bounds
  have hGx := abs_bGd_convex hh hθ1 hθ0 hx0 hxL
  have hGy := abs_bGd_high hh hθ1 hθ0 hy hy1
  have hlogneg : Real.log x ≤ 0 := by
    have : Real.log x ≤ Real.log (1 / 10 : ℝ) := Real.log_le_log hx0 hx10
    linarith [log_tenth_lt]
  have hprod : |bGd h θ x * bGd h θ y| ≤ (43 / 100 * (-Real.log x)) * (13 / 200) := by
    rw [abs_mul]
    exact mul_le_mul hGx hGy (abs_nonneg _) (by linarith)
  have hK : |bAlpha h * z - bGd h θ x * bGd h θ y|
      ≤ bAlpha h + (559 / 20000) * (-Real.log x) := by
    have h1 : |bAlpha h * z| ≤ bAlpha h := by
      rw [abs_mul, abs_of_pos hα0, abs_of_nonneg (by linarith : (0:ℝ) ≤ z)]
      nlinarith
    calc |bAlpha h * z - bGd h θ x * bGd h θ y|
        ≤ |bAlpha h * z| + |bGd h θ x * bGd h θ y| := abs_sub _ _
      _ ≤ bAlpha h + (43 / 100 * (-Real.log x)) * (13 / 200) := by linarith
      _ = bAlpha h + (559 / 20000) * (-Real.log x) := by ring
  have hsq : (bAlpha h * z - bGd h θ x * bGd h θ y) ^ 2
      ≤ (bAlpha h + (559 / 20000) * (-Real.log x)) ^ 2 := by
    calc (bAlpha h * z - bGd h θ x * bGd h θ y) ^ 2
        = |bAlpha h * z - bGd h θ x * bGd h θ y| ^ 2 := (sq_abs _).symm
      _ ≤ (bAlpha h + (559 / 20000) * (-Real.log x)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hK 2
  have hexp : x * (bAlpha h + (559 / 20000) * (-Real.log x)) ^ 2
      = x * (bAlpha h) ^ 2 + 2 * (559 / 20000) * bAlpha h * (x * (-Real.log x))
        + (559 / 20000) ^ 2 * (x * (Real.log x) ^ 2) := by ring
  have e2 : bAlpha h * (x * (-Real.log x)) ≤ 7 / 180 := by
    have hkey : x * (-Real.log x) * (30 * (bAlpha h) ^ 2) ≤ 5 + bAlpha h / 3 :=
      (le_div_iff₀ (by positivity)).mp hxl
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_pos hα0 (sub_pos.2 hcon), hα]
  have e3 : x * (Real.log x) ^ 2 ≤ 49 / 1080 := by
    have h2 : (5 + bAlpha h / 3) ^ 2 / (30 * (bAlpha h) ^ 2) ≤ 49 / 1080 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_nonneg (sub_nonneg.2 hα) (by linarith : (0:ℝ) ≤ 9 * bAlpha h + 30)]
    linarith
  have hfinal : x * (bAlpha h + (559 / 20000) * (-Real.log x)) ^ 2 ≤ 1 / 25 := by
    rw [hexp]
    linarith [hxa, e2, e3]
  calc x * (bAlpha h * z - bGd h θ x * bGd h θ y) ^ 2
      ≤ x * (bAlpha h + (559 / 20000) * (-Real.log x)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hx0.le
    _ ≤ 1 / 25 := hfinal

/-! ### The convex box: `Φ ≥ M₂` for `0 ≤ x ≤ L` -/

theorem local_large_convex (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hx0 : 0 ≤ x) (hx : x ≤ bL h)
    (hy : 19 / 20 ≤ y) (hy1 : y ≤ 1) (hz : 19 / 20 ≤ z) (hz1 : z ≤ 1) :
    bM2 h ≤ entropyF (bAlpha h) (bG h θ) x y z := by
  have hhpos : (0:ℝ) < h := by linarith
  have hL0 := bL_pos hh
  have hL := bL_le hh
  have hr0 := br_pos h
  have hrL := br_le_bL hh
  have ht1 := (bt_lt_one hhpos).le
  have htg := (bt_gt hh).le
  -- the segment stays inside the convex box
  have hxpos : ∀ s : ℝ, 0 ≤ s → s < 1 → 0 < br h + s * (x - br h) := by
    intro s hs0 hs1
    nlinarith [mul_nonneg hs0 hx0, mul_pos hr0 (by linarith : (0:ℝ) < 1 - s)]
  have hxle : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → br h + s * (x - br h) ≤ bL h := by
    intro s hs0 hs1
    nlinarith [mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 hrL),
      mul_nonneg hs0 (sub_nonneg.2 hx)]
  have hwlo : ∀ w s : ℝ, 19 / 20 ≤ w → 0 ≤ s → s ≤ 1 → 19 / 20 ≤ bt h + s * (w - bt h) := by
    intro w s hw hs0 hs1
    nlinarith [mul_nonneg (sub_nonneg.2 hs1) (by linarith : (0:ℝ) ≤ bt h - 19 / 20),
      mul_nonneg hs0 (by linarith : (0:ℝ) ≤ w - 19 / 20)]
  have hwhi : ∀ w s : ℝ, w ≤ 1 → 0 ≤ s → s ≤ 1 → bt h + s * (w - bt h) ≤ 1 := by
    intro w s hw hs0 hs1
    nlinarith [mul_nonneg (sub_nonneg.2 hs1) (by linarith : (0:ℝ) ≤ 1 - bt h),
      mul_nonneg hs0 (by linarith : (0:ℝ) ≤ 1 - w)]
  -- continuity of the restriction
  have hcont : ContinuousOn (fun s : ℝ => entropyF (bAlpha h) (bG h θ)
      (br h + s * (x - br h)) (bt h + s * (y - bt h)) (bt h + s * (z - bt h)))
      (Set.Icc 0 1) := by
    apply Continuous.continuousOn
    have hH := continuous_H
    have hG := continuous_bG h θ
    unfold entropyF
    fun_prop
  -- first and second derivatives along the segment
  have hd : ∀ τ ∈ Set.Ico (0:ℝ) 1, HasDerivAt
      (fun s : ℝ => entropyF (bAlpha h) (bG h θ)
        (br h + s * (x - br h)) (bt h + s * (y - bt h)) (bt h + s * (z - bt h)))
      (lineD1 h θ (br h + τ * (x - br h)) (bt h + τ * (y - bt h)) (bt h + τ * (z - bt h))
        (x - br h) (y - bt h) (z - bt h)) τ := by
    intro τ hτ
    exact hasDerivAt_line1 _ _ _ _ _ _ τ (ne_of_gt (hxpos τ hτ.1 hτ.2))
      (ne_of_gt (by linarith [hwlo y τ hy hτ.1 hτ.2.le]))
      (ne_of_gt (by linarith [hwlo z τ hz hτ.1 hτ.2.le]))
  have hd' : ∀ τ ∈ Set.Ico (0:ℝ) 1, HasDerivAt
      (fun s : ℝ => lineD1 h θ (br h + s * (x - br h)) (bt h + s * (y - bt h))
        (bt h + s * (z - bt h)) (x - br h) (y - bt h) (z - bt h))
      (lineD2 h θ (br h + τ * (x - br h)) (bt h + τ * (y - bt h)) (bt h + τ * (z - bt h))
        (x - br h) (y - bt h) (z - bt h)) τ := by
    intro τ hτ
    exact hasDerivAt_line2 _ _ _ _ _ _ τ (ne_of_gt (hxpos τ hτ.1 hτ.2))
      (ne_of_gt (by linarith [hwlo y τ hy hτ.1 hτ.2.le]))
      (ne_of_gt (by linarith [hwlo z τ hz hτ.1 hτ.2.le]))
  -- convexity along the segment
  have hpos : ∀ τ ∈ Set.Ico (0:ℝ) 1, 0 ≤ lineD2 h θ
      (br h + τ * (x - br h)) (bt h + τ * (y - bt h)) (bt h + τ * (z - bt h))
      (x - br h) (y - bt h) (z - bt h) := by
    intro τ hτ
    set X := br h + τ * (x - br h) with hX
    set Y := bt h + τ * (y - bt h) with hY
    set Z := bt h + τ * (z - bt h) with hZ
    have hX0 : 0 < X := hxpos τ hτ.1 hτ.2
    have hXL : X ≤ bL h := hxle τ hτ.1 hτ.2.le
    have hX1080 : X ≤ 1 / 1080 := le_trans hXL hL
    have hX10 : X ≤ 1 / 10 := by linarith
    have hYlo : 19 / 20 ≤ Y := hwlo y τ hy hτ.1 hτ.2.le
    have hYhi : Y ≤ 1 := hwhi y τ hy1 hτ.1 hτ.2.le
    have hZlo : 19 / 20 ≤ Z := hwlo z τ hz hτ.1 hτ.2.le
    have hZhi : Z ≤ 1 := hwhi z τ hz1 hτ.1 hτ.2.le
    have hY0 : Y ≠ 0 := by intro hc; rw [hc] at hYlo; linarith
    have hZ0 : Z ≠ 0 := by intro hc; rw [hc] at hZlo; linarith
    rw [lineD2_eq X Y Z _ _ _ (ne_of_gt hX0) hY0 hZ0]
    have hform := scalar_mixed_form X
      (1 / (3 * X) - bGd2 h θ X * (bG h θ Y + bG h θ Z))
      (bAlpha h * Z - bGd h θ X * bGd h θ Y)
      (bAlpha h * Y - bGd h θ X * bGd h θ Z)
      (1 / (3 * Y) - bGd2 h θ Y * (bG h θ X + bG h θ Z))
      (bAlpha h * X - bGd h θ Y * bGd h θ Z)
      (1 / (3 * Z) - bGd2 h θ Z * (bG h θ X + bG h θ Y))
      (x - br h) (y - bt h) (z - bt h) hX0
      (hess_xx hh hθ1 hθ0 hX0 hX10 hYlo hYhi hZlo hZhi)
      (hess_yy hh hθ1 hθ0 hX0 hX1080 hYlo hYhi hZlo hZhi)
      (hess_yy hh hθ1 hθ0 hX0 hX1080 hZlo hZhi hYlo hYhi)
      (hess_yz hh hθ1 hθ0 hX0 hXL hYlo hYhi hZlo hZhi)
      (hess_xy hh hθ1 hθ0 hX0 hXL hYlo hYhi hZlo hZhi)
      (hess_xy hh hθ1 hθ0 hX0 hXL hZlo hZhi hYlo hYhi)
    have hlhs : 0 ≤ (x - br h) ^ 2 / (75 * X)
        + ((y - bt h) ^ 2 + (z - bt h) ^ 2) / 20 := by positivity
    linarith
  -- stationarity at the sharp point
  have hzero : lineD1 h θ (br h + (0:ℝ) * (x - br h)) (bt h + (0:ℝ) * (y - bt h))
      (bt h + (0:ℝ) * (z - bt h)) (x - br h) (y - bt h) (z - bt h) = 0 := by
    have h1 := phiX_at_sharp (h := h) (θ := θ) hhpos
    have h2 := phiX_at_sharp' (h := h) (θ := θ) hhpos
    simp only [phiX] at h1 h2
    simp only [zero_mul, add_zero, lineD1]
    linear_combination (x - br h) * h1 + (y - bt h) * h2 + (z - bt h) * h2
  have key := Segment.le_endpoint hcont hd hd' hpos hzero
  simp only [zero_mul, add_zero, one_mul] at key
  rw [entropyF_rtt hhpos] at key
  have e1 : br h + (x - br h) = x := by ring
  have e2 : bt h + (y - bt h) = y := by ring
  have e3 : bt h + (z - bt h) = z := by ring
  rw [e1, e2, e3] at key
  exact key

/-! ### The remaining part of the small-coordinate interval -/

theorem phiX_at_bL_pos (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hy : 19 / 20 ≤ y) (hy1 : y ≤ 1) (hz : 19 / 20 ≤ z) (hz1 : z ≤ 1) :
    0 < phiX h θ (bL h) y z := by
  have hα := bAlpha_ge_six hh
  have hα0 : (0:ℝ) < bAlpha h := by linarith
  have hL0 := bL_pos hh
  have hL := bL_le hh
  have hLlog : -Real.log (bL h) = Real.log (30 * (bAlpha h) ^ 2) := by
    unfold bL
    rw [one_div, Real.log_inv, neg_neg]
  have hΛ : Real.log (30 * (bAlpha h) ^ 2) ≤ 5 + bAlpha h / 3 := Scalar.log_thirty_sq_le hα
  have hΛ0 : 0 ≤ Real.log (30 * (bAlpha h) ^ 2) :=
    Real.log_nonneg (by nlinarith)
  have hGd : |bGd h θ (bL h)| ≤ 43 / 100 * Real.log (30 * (bAlpha h) ^ 2) := by
    rw [← hLlog]
    exact abs_bGd_convex hh hθ1 hθ0 hL0 hL
  have hs1 := bG_sum_high hh hθ1 hθ0 hy hy1 hz hz1
  have hs2 := bG_sum_high_ge hh hθ1 hθ0 hy hy1 hz hz1
  have habs : |bG h θ y + bG h θ z| ≤ 82 / 100 := by
    rw [abs_le]; constructor <;> linarith
  have hprod : |bGd h θ (bL h) * (bG h θ y + bG h θ z)|
      ≤ (43 / 100 * Real.log (30 * (bAlpha h) ^ 2)) * (82 / 100) := by
    rw [abs_mul]
    exact mul_le_mul hGd habs (abs_nonneg _) (by linarith)
  rw [abs_le] at hprod
  have hyz0 : (361 : ℝ) / 400 ≤ y * z := by nlinarith
  have hyz : 361 / 400 * bAlpha h ≤ bAlpha h * y * z := by
    nlinarith [mul_nonneg hα0.le (sub_nonneg.2 hyz0)]
  have hlogL : Real.log (bL h) = -Real.log (30 * (bAlpha h) ^ 2) := by linarith
  simp only [phiX, hlogL]
  linarith [hprod.1, hprod.2]

theorem local_large_tail (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hxL : bL h ≤ x) (hx : x ≤ 1 / 10)
    (hy : 19 / 20 ≤ y) (hy1 : y ≤ 1) (hz : 19 / 20 ≤ z) (hz1 : z ≤ 1) :
    entropyF (bAlpha h) (bG h θ) (bL h) y z ≤ entropyF (bAlpha h) (bG h θ) x y z := by
  have hhpos : (0:ℝ) < h := by linarith
  have hL0 := bL_pos hh
  have hL := bL_le hh
  have hLhi : bL h ≤ 1 / 10 := by linarith
  -- the small-coordinate derivative is positive on the whole tail
  have hphi : ∀ u ∈ Set.Icc (bL h) (1 / 10 : ℝ), 0 < phiX h θ u y z := by
    have hmono : MonotoneOn (fun u : ℝ => phiX h θ u y z) (Set.Icc (bL h) (1 / 10 : ℝ)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · intro s hs
        have hs0 : 0 < s := lt_of_lt_of_le hL0 hs.1
        exact ((hasDerivAt_phiX y z (ne_of_gt hs0)).continuousAt).continuousWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        have hs0 : 0 < s := lt_trans hL0 hs.1
        exact (hasDerivAt_phiX y z
          (ne_of_gt hs0)).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        have hs0 : 0 < s := lt_trans hL0 hs.1
        rw [(hasDerivAt_phiX y z (ne_of_gt hs0)).deriv]
        have hxx := hess_xx hh hθ1 hθ0 hs0 hs.2.le hy hy1 hz hz1
        have hpos : (0:ℝ) < 1 / (3 * s) := by positivity
        linarith
    intro u hu
    have h0 := phiX_at_bL_pos hh hθ1 hθ0 hy hy1 hz hz1
    have := hmono (Set.mem_Icc.2 ⟨le_refl _, hLhi⟩) hu hu.1
    simp only at this
    linarith
  -- hence the objective is monotone in the small coordinate
  have hmono : MonotoneOn (fun u : ℝ => entropyF (bAlpha h) (bG h θ) u y z)
      (Set.Icc (bL h) (1 / 10 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le hL0 hs.1
      exact ((hasDerivAt_phiX_obj y z (ne_of_gt hs0)).continuousAt).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs0 : 0 < s := lt_trans hL0 hs.1
      exact (hasDerivAt_phiX_obj y z
        (ne_of_gt hs0)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs0 : 0 < s := lt_trans hL0 hs.1
      rw [(hasDerivAt_phiX_obj y z (ne_of_gt hs0)).deriv]
      exact (hphi s ⟨hs.1.le, hs.2.le⟩).le
  exact hmono (Set.mem_Icc.2 ⟨le_refl _, hLhi⟩) (Set.mem_Icc.2 ⟨hxL, hx⟩) hxL

/-! ### The local lower bound (A2) -/

theorem local_large_region (hh : 9 ≤ h) (hθ1 : -(1 / 50 : ℝ) ≤ θ) (hθ0 : θ ≤ 0)
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 10)
    (hy : 19 / 20 ≤ y) (hy1 : y ≤ 1) (hz : 19 / 20 ≤ z) (hz1 : z ≤ 1) :
    bM2 h ≤ entropyF (bAlpha h) (bG h θ) x y z := by
  rcases le_total x (bL h) with hle | hge
  · exact local_large_convex hh hθ1 hθ0 hx0 hle hy hy1 hz hz1
  · have h1 : bM2 h ≤ entropyF (bAlpha h) (bG h θ) (bL h) y z :=
      local_large_convex hh hθ1 hθ0 (bL_pos hh).le (le_refl _) hy hy1 hz hz1
    have h2 := local_large_tail hh hθ1 hθ0 hge hx hy hy1 hz hz1
    linarith

end
end Branch
end TriangleNumerical
