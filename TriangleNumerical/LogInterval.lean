import TriangleNumerical.Interval
import TriangleNumerical.LogLadder

/-!
# Computable logarithm and exponential enclosures

Section 9.2/9.3 of the blueprint, in kernel-checkable form.  `LogLadder.lean`
proves the two seed bounds and the finite square-ladder induction for *real*
sequences; here the ladders become **finite lists of scaled integers** and the
whole ladder condition becomes one `Bool`-valued function that the kernel can
evaluate.

A lower ladder for `log y` (`y ≥ 1`) is a list `a₁, …, a_n` of dyadic numbers
with `1 ≤ a_i`, `a₁² ≤ y` and `a_{i+1}² ≤ a_i`; an upper ladder has `1 ≤ b_i`,
`y ≤ b₁²` and `b_i ≤ b_{i+1}²`.  Then

```
2ⁿ L(a_n) ≤ log y ≤ 2ⁿ U(b_n)
```

with `L` and `U` the two proved Padé seeds.  Both seeds are evaluated with the
dyadic interval arithmetic of `Interval.lean`, so the resulting bounds are
again dyadic and outward rounded.  Exponentials are enclosed by inverting
these logarithm bounds.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Itv

open TriangleLogCertificate

theorem mem_pt (a : Int) : (pt a).Mem (value a) := ⟨le_refl _, le_refl _⟩

theorem value_one : value scale = 1 := by
  simp only [value]
  exact div_self (ne_of_gt scale_pos_real)

theorem value_sub (m n : Int) : value (m - n) = value m - value n := by
  simp only [value]; push_cast; ring

theorem value_add' (m n : Int) : value (m + n) = value m + value n := by
  simp only [value]; push_cast; ring

theorem value_two_mul (n : Int) : value (2 * n) = 2 * value n := by
  simp only [value]; push_cast; ring


theorem mem_twoI : twoI.Mem 2 := by
  have h := mem_pt (2 * scale)
  rwa [value_two_mul, value_one, mul_one] at h

theorem one_le_value {a : Int} (h : scale ≤ a) : 1 ≤ value a := by
  have hs := scale_pos_real
  have h' : ((scale : Int) : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
  rw [value, le_div_iff₀ hs]
  linarith

theorem value_pos {a : Int} (h : 0 < a) : 0 < value a := by
  have hs := scale_pos_real
  have h' : (0:ℝ) < (a : ℝ) := by exact_mod_cast h
  simp only [value]
  positivity

/-! ### The two seeds, evaluated with dyadic intervals -/

theorem mem_seedLowerI {a : Int} (h : scale ≤ a) :
    (seedLowerI a).Mem (lowerSeed (value a)) := by
  have hs : 0 < scale := scale_pos
  have hpos : 0 < (pt (a + scale)).lo := by simp only [pt]; omega
  have hmem := mem_div (mem_pt (2 * (a - scale))) (mem_pt (a + scale)) hpos
  have heq : value (2 * (a - scale)) / value (a + scale) = lowerSeed (value a) := by
    rw [value_two_mul, value_sub, value_add', value_one, lowerSeed]
  rwa [heq] at hmem

theorem mem_seedUpperI {a : Int} (h : scale ≤ a) :
    (seedUpperI a).Mem (upperSeed (value a)) := by
  have hs : 0 < scale := scale_pos
  have hapos : 0 < (pt a).lo := by simp only [pt]; omega
  have h2pos : 0 < twoI.lo := by simp only [twoI, pt]; omega
  have hmem := mem_div (mem_sub (mem_pt a) (mem_div mem_oneI (mem_pt a) hapos)) mem_twoI h2pos
  have heq : (value a - 1 / value a) / 2 = upperSeed (value a) := rfl
  rwa [heq] at hmem

/-! ### The computable ladder conditions -/

theorem scale_le_of_lowerOk {a : Int} {l : List Int} (h : lowerOk a l = true) : scale ≤ a := by
  cases l with
  | nil => simpa [lowerOk] using h
  | cons b rest =>
      simp only [lowerOk, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1

theorem scale_le_of_upperOk {a : Int} {l : List Int} (h : upperOk a l = true) : scale ≤ a := by
  cases l with
  | nil => simpa [upperOk] using h
  | cons b rest =>
      simp only [upperOk, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1

theorem scale_le_lastOf {a : Int} {l : List Int} (h : lowerOk a l = true) :
    scale ≤ lastOf a l := by
  induction l generalizing a with
  | nil => simpa [lastOf] using scale_le_of_lowerOk h
  | cons b rest ih =>
      simp only [lowerOk, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ih h.2

theorem scale_le_lastOf_upper {a : Int} {l : List Int} (h : upperOk a l = true) :
    scale ≤ lastOf a l := by
  induction l generalizing a with
  | nil => simpa [lastOf] using scale_le_of_upperOk h
  | cons b rest ih =>
      simp only [upperOk, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ih h.2

/-- The square step in real terms. -/
theorem sq_step_le {a b : Int} (h : b * b ≤ a * scale) : value b ^ 2 ≤ value a := by
  have hs := scale_pos_real
  have h' : ((b : ℝ)) * (b : ℝ) ≤ (a : ℝ) * (scale : ℝ) := by exact_mod_cast h
  simp only [value]
  rw [div_pow, div_le_div_iff₀ (by positivity) hs]
  nlinarith [hs]

theorem sq_step_ge {a b : Int} (h : a * scale ≤ b * b) : value a ≤ value b ^ 2 := by
  have hs := scale_pos_real
  have h' : ((a : ℝ)) * (scale : ℝ) ≤ (b : ℝ) * (b : ℝ) := by exact_mod_cast h
  simp only [value]
  rw [div_pow, div_le_div_iff₀ hs (by positivity)]
  nlinarith [hs]

/-! ### Soundness of the finite ladders -/

theorem lowerOk_sound : ∀ (l : List Int) (a : Int), lowerOk a l = true →
    (2:ℝ) ^ l.length * lowerSeed (value (lastOf a l)) ≤ Real.log (value a) := by
  intro l
  induction l with
  | nil =>
      intro a h
      have h1 : (1:ℝ) ≤ value a := one_le_value (scale_le_of_lowerOk h)
      simpa [lastOf] using lower_seed_le_log (value a) h1
  | cons b rest ih =>
      intro a h
      simp only [lowerOk, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨ha, hsq⟩, hrest⟩ := h
      have hb : (1:ℝ) ≤ value b := one_le_value (scale_le_of_lowerOk hrest)
      have hstep : value b ^ 2 ≤ value a := sq_step_le hsq
      have hlog : 2 * Real.log (value b) ≤ Real.log (value a) := by
        have hle : Real.log (value b ^ 2) ≤ Real.log (value a) :=
          Real.log_le_log (by positivity) hstep
        rwa [Real.log_pow] at hle
      have hIH := ih b hrest
      have hpow : (0:ℝ) ≤ (2:ℝ) ^ rest.length := by positivity
      have hlast : lastOf a (b :: rest) = lastOf b rest := rfl
      rw [hlast, List.length_cons]
      calc (2:ℝ) ^ (rest.length + 1) * lowerSeed (value (lastOf b rest))
          = 2 * ((2:ℝ) ^ rest.length * lowerSeed (value (lastOf b rest))) := by ring
        _ ≤ 2 * Real.log (value b) := by linarith
        _ ≤ Real.log (value a) := hlog

theorem upperOk_sound : ∀ (l : List Int) (a : Int), upperOk a l = true →
    Real.log (value a) ≤ (2:ℝ) ^ l.length * upperSeed (value (lastOf a l)) := by
  intro l
  induction l with
  | nil =>
      intro a h
      have h1 : (1:ℝ) ≤ value a := one_le_value (scale_le_of_upperOk h)
      simpa [lastOf] using log_le_upper_seed (value a) h1
  | cons b rest ih =>
      intro a h
      simp only [upperOk, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨ha, hsq⟩, hrest⟩ := h
      have hb : (1:ℝ) ≤ value b := one_le_value (scale_le_of_upperOk hrest)
      have hstep : value a ≤ value b ^ 2 := sq_step_ge hsq
      have hva : (1:ℝ) ≤ value a := one_le_value ha
      have hlog : Real.log (value a) ≤ 2 * Real.log (value b) := by
        have hle : Real.log (value a) ≤ Real.log (value b ^ 2) :=
          Real.log_le_log (by linarith) hstep
        rwa [Real.log_pow] at hle
      have hIH := ih b hrest
      have hpow : (0:ℝ) ≤ (2:ℝ) ^ rest.length := by positivity
      have hlast : lastOf a (b :: rest) = lastOf b rest := rfl
      rw [hlast, List.length_cons]
      calc Real.log (value a) ≤ 2 * Real.log (value b) := hlog
        _ ≤ 2 * ((2:ℝ) ^ rest.length * upperSeed (value (lastOf b rest))) := by linarith
        _ = (2:ℝ) ^ (rest.length + 1) * upperSeed (value (lastOf b rest)) := by ring

/-! ### Dyadic logarithm enclosures -/

theorem mem_pow2I (n : ℕ) : (pow2I n).Mem ((2:ℝ) ^ n) := by
  have h := mem_pt (scale * 2 ^ n)
  have heq : value (scale * 2 ^ n) = (2:ℝ) ^ n := by
    simp only [value]
    push_cast
    rw [mul_comm, mul_div_assoc, div_self (ne_of_gt scale_pos_real), mul_one]
  rwa [heq] at h

/-! ### Logarithms of dyadic numbers below `1`, by inversion -/

/-! ### Exponential enclosures -/

/-! ### Logarithms and exponentials of numbers below `1`

Every exponential this development needs has a negative argument, so the
enclosing endpoints are below `1` and the ladders — which require an argument
`≥ 1` — are run on dyadic *lower bounds for the reciprocals*.  A dyadic `u`
with `u * a ≤ scale²` satisfies `value u ≤ 1 / value a`, hence
`log (value a) ≤ -log (value u)`, and symmetrically for the other side. -/

theorem value_neg' (n : Int) : value (-n) = -value n := by
  simp only [value]; push_cast; ring

theorem value_le_value {m n : Int} (h : m ≤ n) : value m ≤ value n := by
  have hs := scale_pos_real
  have h' : ((m : Int) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  simp only [value]
  gcongr

theorem mem_expOk {c : ExpCert} {xlo xhi : Int} {x : ℝ} (h : expOk c xlo xhi = true)
    (hx1 : value xlo ≤ x) (hx2 : x ≤ value xhi) :
    (DI.mk c.lo c.hi).Mem (Real.exp x) := by
  simp only [expOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hlo, hhi⟩, hu⟩, hul⟩, hv⟩, hvl⟩, hcmp1⟩, hcmp2⟩ := h
  have hs := scale_pos_real
  have hvlo : 0 < value c.lo := value_pos hlo
  have hvhi : 0 < value c.hi := value_pos hhi
  have hvu : (1:ℝ) ≤ value c.u := one_le_value (scale_le_of_lowerOk hul)
  have hvv : (1:ℝ) ≤ value c.v := one_le_value (scale_le_of_upperOk hvl)
  have hupos : 0 < value c.u := lt_of_lt_of_le zero_lt_one hvu
  have hvpos : 0 < value c.v := lt_of_lt_of_le zero_lt_one hvv
  -- `value u * value lo ≤ 1`
  have hprod : value c.u * value c.lo ≤ 1 := by
    have h' : ((c.u : ℝ)) * (c.lo : ℝ) ≤ (scale : ℝ) * (scale : ℝ) := by exact_mod_cast hu
    simp only [value]
    rw [div_mul_div_comm, div_le_one (by positivity)]
    linarith
  have hprod' : (1:ℝ) ≤ value c.v * value c.hi := by
    have h' : ((scale : ℝ)) * (scale : ℝ) ≤ (c.v : ℝ) * (c.hi : ℝ) := by exact_mod_cast hv
    simp only [value]
    rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
    linarith
  -- the two logarithm comparisons
  have hloglo : Real.log (value c.lo) ≤ -Real.log (value c.u) := by
    have hml : Real.log (value c.u) + Real.log (value c.lo) ≤ 0 := by
      rw [← Real.log_mul (ne_of_gt hupos) (ne_of_gt hvlo)]
      have := Real.log_le_log (by positivity) hprod
      simpa using this
    linarith
  have hloghi : -Real.log (value c.v) ≤ Real.log (value c.hi) := by
    have hml : (0:ℝ) ≤ Real.log (value c.v) + Real.log (value c.hi) := by
      rw [← Real.log_mul (ne_of_gt hvpos) (ne_of_gt hvhi)]
      have := Real.log_le_log (by norm_num) hprod'
      simpa using this
    linarith
  -- the ladder bounds
  have hlad1 : value (logLowerI c.u c.ul).lo ≤ Real.log (value c.u) := by
    have hm := mem_mul (mem_pow2I c.ul.length) (mem_seedLowerI (scale_le_lastOf hul))
    exact le_trans hm.1 (lowerOk_sound c.ul c.u hul)
  have hlad2 : Real.log (value c.v) ≤ value (logUpperI c.v c.vl).hi := by
    have hm := mem_mul (mem_pow2I c.vl.length) (mem_seedUpperI (scale_le_lastOf_upper hvl))
    exact le_trans (upperOk_sound c.vl c.v hvl) hm.2
  have hstep1 : Real.log (value c.lo) ≤ value xlo := by
    have h1 : value ((neg (logLowerI c.u c.ul)).hi) ≤ value xlo := value_le_value hcmp1
    have h2 : (neg (logLowerI c.u c.ul)).hi = -(logLowerI c.u c.ul).lo := rfl
    rw [h2, value_neg'] at h1
    linarith
  have hstep2 : value xhi ≤ Real.log (value c.hi) := by
    have h1 : value xhi ≤ value ((neg (logUpperI c.v c.vl)).lo) := value_le_value hcmp2
    have h2 : (neg (logUpperI c.v c.vl)).lo = -(logUpperI c.v c.vl).hi := rfl
    rw [h2, value_neg'] at h1
    linarith
  exact TriangleLogCertificate.exp_enclosure_of_log_bounds x (value c.lo) (value c.hi)
    hvlo hvhi (le_trans hstep1 hx1) (le_trans hx2 hstep2)

end Itv
end TriangleNumerical
