import TriangleNumerical.LogInterval
import TriangleNumerical.Deriv

/-!
# Certified enclosures of the branch parameters over an interval of `h`

Section 8.1 of the blueprint.  Given a rational (dyadic) interval of branch
parameters `h` and two exponential certificates — one for `z = exp(-h)` and one
for `t = exp(-p)` — this module evaluates the explicit formulas (B1)

```
z = exp(-h),  p = 2 h z / (1-z)²,  t = exp(-p),  r = t z,
Δ = t - r,    α = 2h / (3Δ²),      β = p / (2t),  C = 1 - (1 + p/2) t
```

with outward-rounded dyadic interval arithmetic, and proves that **every**
actual branch parameter with `h` in the given interval lies in the computed
enclosures.  The whole acceptance condition is one Boolean that the kernel
evaluates; the certificates themselves are untrusted witness data.

No monotonicity of `A`, `Δ`, `β` or `C` in `h` is used, exactly as the
blueprint requires: the enclosures come from interval evaluation alone, and a
slab that does not fit a target table is simply bisected.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Itv

open TriangleNumerical.Branch

theorem value_three_mul (n : Int) : value (3 * n) = 3 * value n := by
  simp only [value]; push_cast; ring

theorem mem_threeI : threeI.Mem 3 := by
  have h := mem_pt (3 * scale)
  rwa [value_three_mul, value_one, mul_one] at h

/-! ### Soundness -/

theorem param_sound (c : ParamCert) (hok : c.ok = true) {x : ℝ}
    (h1 : value c.hlo ≤ x) (h2 : x ≤ value c.hhi) :
    c.Iz.Mem (bz x) ∧ c.Ip.Mem (bp x) ∧ c.It.Mem (bt x) ∧ c.Ir.Mem (br x) ∧
      c.IDelta.Mem (bDelta x) ∧ c.IAlpha.Mem (bAlpha x) ∧ c.IBeta.Mem (bBeta x) ∧
      c.IC.Mem (bC x) := by
  simp only [ParamCert.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hz, hden⟩, ht⟩, hden2⟩, hden3⟩ := hok
  -- `h` itself
  have hmh : c.Ih.Mem x := ⟨h1, h2⟩
  -- `z = exp (-h)`
  have hmz : c.Iz.Mem (bz x) := by
    have harg1 : value (-c.hhi) ≤ -x := by rw [value_neg']; linarith
    have harg2 : -x ≤ value (-c.hlo) := by rw [value_neg']; linarith
    exact mem_expOk hz harg1 harg2
  -- `p = 2 h z / (1-z)^2`
  have hmp : c.Ip.Mem (bp x) := by
    have hnum := mem_mul (mem_mul mem_twoI hmh) hmz
    have hsq := mem_pow (mem_sub mem_oneI hmz) 2
    have hdiv := mem_div hnum hsq hden
    have heq : 2 * x * bz x / (1 - bz x) ^ 2 = bp x := rfl
    rwa [heq] at hdiv
  -- `t = exp (-p)`
  have hmt : c.It.Mem (bt x) := by
    have harg1 : value (-(c.Ip).hi) ≤ -bp x := by
      rw [value_neg']
      have := hmp.2
      simp only [value] at this ⊢
      linarith
    have harg2 : -bp x ≤ value (-(c.Ip).lo) := by
      rw [value_neg']
      have := hmp.1
      simp only [value] at this ⊢
      linarith
    exact mem_expOk ht harg1 harg2
  -- the algebraic consequences
  have hmr : c.Ir.Mem (br x) := mem_mul hmt hmz
  have hmd : c.IDelta.Mem (bDelta x) := mem_sub hmt hmr
  have hma : c.IAlpha.Mem (bAlpha x) := by
    have hnum := mem_mul mem_twoI hmh
    have hsq := mem_mul mem_threeI (mem_pow hmd 2)
    have hdiv := mem_div hnum hsq hden2
    have heq : 2 * x / (3 * bDelta x ^ 2) = bAlpha x := rfl
    rwa [heq] at hdiv
  have hmb : c.IBeta.Mem (bBeta x) := by
    have hdiv := mem_div hmp (mem_mul mem_twoI hmt) hden3
    have heq : bp x / (2 * bt x) = bBeta x := rfl
    rwa [heq] at hdiv
  have hmc : c.IC.Mem (bC x) := by
    have h2pos : 0 < twoI.lo := by
      have : 0 < scale := scale_pos
      simp only [twoI, pt]; omega
    have hmem := mem_sub mem_oneI
      (mem_mul (mem_add mem_oneI (mem_div hmp mem_twoI h2pos)) hmt)
    have heq : 1 - (1 + bp x / 2) * bt x = bC x := rfl
    rwa [heq] at hmem
  exact ⟨hmz, hmp, hmt, hmr, hmd, hma, hmb, hmc⟩

/-! ### Chains of certificates covering a whole slab

A slab is covered by finitely many dyadic sub-intervals of `h`; the enclosure
for the slab is the hull of the per-piece enclosures.  Coverage is again a
Boolean condition. -/

end Itv
end TriangleNumerical
