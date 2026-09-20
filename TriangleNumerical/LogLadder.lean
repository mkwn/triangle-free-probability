import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Rational logarithm ladders: seed bounds, finite-ladder soundness, and
exponential enclosures by logarithmic inversion.

All statements are theorems about real numbers; the witness data that will be
fed to them happen to be rational.
-/

set_option autoImplicit false

namespace TriangleLogCertificate
noncomputable section

def lowerSeed (y : ℝ) : ℝ := 2 * (y - 1) / (y + 1)
def upperSeed (y : ℝ) : ℝ := (y - 1 / y) / 2

/-- Padé-type lower bound for the logarithm on `[1, ∞)`. -/
theorem lower_seed_le_log (y : ℝ) (hy : 1 ≤ y) :
    lowerSeed y ≤ Real.log y := by
  have hmono : MonotoneOn (fun x : ℝ => Real.log x - 2 * (x - 1) / (x + 1)) (Set.Ici 1) := by
    have hderiv : ∀ x ∈ Set.Ioi (1:ℝ),
        HasDerivAt (fun x : ℝ => Real.log x - 2 * (x - 1) / (x + 1))
          (x⁻¹ - (2 * (x + 1) - 2 * (x - 1) * 1) / (x + 1) ^ 2) x := by
      intro x hx
      simp only [Set.mem_Ioi] at hx
      have hx0 : x ≠ 0 := by linarith
      have hx1 : x + 1 ≠ 0 := by linarith
      have h1 : HasDerivAt (fun x : ℝ => 2 * (x - 1)) 2 x := by
        simpa using ((hasDerivAt_id x).sub_const 1).const_mul 2
      have h2 : HasDerivAt (fun x : ℝ => x + 1) 1 x := (hasDerivAt_id x).add_const 1
      exact (Real.hasDerivAt_log hx0).sub (h1.div h2 hx1)
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · apply ContinuousOn.sub
      · exact Real.continuousOn_log.mono (by intro x hx; simp at hx ⊢; linarith)
      · apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro x hx; simp at hx; linarith
    · intro x hx
      rw [interior_Ici] at hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hderiv x hx).deriv]
      simp only [Set.mem_Ioi] at hx
      have hx0 : (0:ℝ) < x := by linarith
      have hsq : (0:ℝ) < (x + 1) ^ 2 := by positivity
      rw [sub_nonneg, div_le_iff₀ hsq, inv_mul_eq_div, le_div_iff₀ hx0]
      nlinarith [sq_nonneg (x - 1)]
  have h := hmono Set.self_mem_Ici (Set.mem_Ici.2 hy) hy
  simp only [lowerSeed, Real.log_one] at h ⊢
  norm_num at h
  linarith

/-- Padé-type upper bound for the logarithm on `[1, ∞)`. -/
theorem log_le_upper_seed (y : ℝ) (hy : 1 ≤ y) :
    Real.log y ≤ upperSeed y := by
  have hmono : MonotoneOn (fun x : ℝ => (x - 1 / x) / 2 - Real.log x) (Set.Ici 1) := by
    have hderiv : ∀ x ∈ Set.Ioi (1:ℝ),
        HasDerivAt (fun x : ℝ => (x - 1 / x) / 2 - Real.log x)
          ((1 - (-(x ^ 2)⁻¹)) / 2 - x⁻¹) x := by
      intro x hx
      simp only [Set.mem_Ioi] at hx
      have hx0 : x ≠ 0 := by linarith
      have h1 : HasDerivAt (fun x : ℝ => 1 / x) (-(x ^ 2)⁻¹) x := by
        simpa [one_div] using (hasDerivAt_inv hx0)
      exact ((((hasDerivAt_id x).sub h1).div_const 2).sub (Real.hasDerivAt_log hx0))
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · apply ContinuousOn.sub
      · apply ContinuousOn.div_const
        apply ContinuousOn.sub (by fun_prop)
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro x hx; simp at hx; linarith
      · exact Real.continuousOn_log.mono (by intro x hx; simp at hx ⊢; linarith)
    · intro x hx
      rw [interior_Ici] at hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hderiv x hx).deriv]
      simp only [Set.mem_Ioi] at hx
      have hx0 : (0:ℝ) < x := by linarith
      rw [sub_nonneg, inv_le_iff_one_le_mul₀ hx0]
      have h2 : (0:ℝ) < x ^ 2 := by positivity
      field_simp
      nlinarith [sq_nonneg (x - 1)]
  have h := hmono Set.self_mem_Ici (Set.mem_Ici.2 hy) hy
  simp only [upperSeed, Real.log_one, one_div] at h ⊢
  norm_num at h
  linarith

/-- Halving step of the lower ladder: `2^n * log (a n) ≤ log (a 0)`. -/
theorem log_lower_chain (n : ℕ) (a : ℕ → ℝ)
    (hpos : ∀ i, i ≤ n → 1 ≤ a i)
    (hstep : ∀ i, i < n → (a (i + 1)) ^ 2 ≤ a i) :
    (2 : ℝ) ^ n * Real.log (a n) ≤ Real.log (a 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hIH := ih (fun i hi => hpos i (hi.trans (Nat.le_succ n)))
        (fun i hi => hstep i (hi.trans (Nat.lt_succ_self n)))
      have h1 : (1:ℝ) ≤ a (n + 1) := hpos (n + 1) le_rfl
      have hsq : (a (n + 1)) ^ 2 ≤ a n := hstep n (Nat.lt_succ_self n)
      have hlog : 2 * Real.log (a (n + 1)) ≤ Real.log (a n) := by
        have : Real.log ((a (n + 1)) ^ 2) ≤ Real.log (a n) :=
          Real.log_le_log (by positivity) hsq
        rwa [Real.log_pow] at this
      have h2 : (0:ℝ) ≤ (2:ℝ) ^ n := by positivity
      calc (2:ℝ) ^ (n + 1) * Real.log (a (n + 1))
          = (2:ℝ) ^ n * (2 * Real.log (a (n + 1))) := by ring
        _ ≤ (2:ℝ) ^ n * Real.log (a n) := by
              exact mul_le_mul_of_nonneg_left hlog h2
        _ ≤ Real.log (a 0) := hIH

/-- Lower ladder with the seed applied at the final endpoint. -/
theorem log_lower_ladder (n : ℕ) (a : ℕ → ℝ)
    (hpos : ∀ i, i ≤ n → 1 ≤ a i)
    (hstep : ∀ i, i < n → (a (i + 1)) ^ 2 ≤ a i) :
    (2 : ℝ) ^ n * lowerSeed (a n) ≤ Real.log (a 0) := by
  refine le_trans ?_ (log_lower_chain n a hpos hstep)
  have h2 : (0:ℝ) ≤ (2:ℝ) ^ n := by positivity
  exact mul_le_mul_of_nonneg_left (lower_seed_le_log _ (hpos n le_rfl)) h2

/-- Doubling step of the upper ladder: `log (b 0) ≤ 2^n * log (b n)`. -/
theorem log_upper_chain (n : ℕ) (b : ℕ → ℝ)
    (hpos : ∀ i, i ≤ n → 1 ≤ b i)
    (hstep : ∀ i, i < n → b i ≤ (b (i + 1)) ^ 2) :
    Real.log (b 0) ≤ (2 : ℝ) ^ n * Real.log (b n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hIH := ih (fun i hi => hpos i (hi.trans (Nat.le_succ n)))
        (fun i hi => hstep i (hi.trans (Nat.lt_succ_self n)))
      have h1 : (1:ℝ) ≤ b (n + 1) := hpos (n + 1) le_rfl
      have hsq : b n ≤ (b (n + 1)) ^ 2 := hstep n (Nat.lt_succ_self n)
      have hbn : (1:ℝ) ≤ b n := hpos n (Nat.le_succ n)
      have hlog : Real.log (b n) ≤ 2 * Real.log (b (n + 1)) := by
        have : Real.log (b n) ≤ Real.log ((b (n + 1)) ^ 2) :=
          Real.log_le_log (by linarith) hsq
        rwa [Real.log_pow] at this
      have h2 : (0:ℝ) ≤ (2:ℝ) ^ n := by positivity
      calc Real.log (b 0) ≤ (2:ℝ) ^ n * Real.log (b n) := hIH
        _ ≤ (2:ℝ) ^ n * (2 * Real.log (b (n + 1))) :=
              mul_le_mul_of_nonneg_left hlog h2
        _ = (2:ℝ) ^ (n + 1) * Real.log (b (n + 1)) := by ring

/-- Upper ladder with the seed applied at the final endpoint. -/
theorem log_upper_ladder (n : ℕ) (b : ℕ → ℝ)
    (hpos : ∀ i, i ≤ n → 1 ≤ b i)
    (hstep : ∀ i, i < n → b i ≤ (b (i + 1)) ^ 2) :
    Real.log (b 0) ≤ (2 : ℝ) ^ n * upperSeed (b n) := by
  refine le_trans (log_upper_chain n b hpos hstep) ?_
  have h2 : (0:ℝ) ≤ (2:ℝ) ^ n := by positivity
  exact mul_le_mul_of_nonneg_left (log_le_upper_seed _ (hpos n le_rfl)) h2

/-- Exponential enclosures by logarithmic inversion. -/
theorem exp_enclosure_of_log_bounds (x lo hi : ℝ)
    (hlo : 0 < lo) (hhi : 0 < hi)
    (hlower : Real.log lo ≤ x) (hupper : x ≤ Real.log hi) :
    lo ≤ Real.exp x ∧ Real.exp x ≤ hi := by
  constructor
  · calc lo = Real.exp (Real.log lo) := (Real.exp_log hlo).symm
      _ ≤ Real.exp x := Real.exp_le_exp.2 hlower
  · calc Real.exp x ≤ Real.exp (Real.log hi) := Real.exp_le_exp.2 hupper
      _ = hi := Real.exp_log hhi

/-- Logarithm bounds for arguments in `(0,1)`, by inversion. -/
theorem log_bounds_of_inv {q L U : ℝ}
    (hL : L ≤ Real.log (1 / q)) (hU : Real.log (1 / q) ≤ U) :
    -U ≤ Real.log q ∧ Real.log q ≤ -L := by
  have h : Real.log (1 / q) = -Real.log q := by
    rw [one_div, Real.log_inv]
  rw [h] at hL hU
  constructor <;> linarith

end
end TriangleLogCertificate
