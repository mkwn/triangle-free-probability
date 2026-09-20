import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TriangleNumerical.Kernel

/-!
# Kernel-checkable dyadic interval arithmetic

Section 9.4 of the blueprint.  The Lean kernel cannot evaluate `ℚ` arithmetic
(rational normalisation goes through `Nat.gcd`, which does not reduce), so all
certified numerics in this development use **fixed-point dyadic intervals**:
an integer `n` denotes the real number `n / 2^128`, and an interval is a pair
of such integers.  Every operation rounds outwards with `Int` division, which the
kernel evaluates with its GMP-backed arithmetic.

Only the soundness direction is ever needed: each operation returns an interval
that provably *contains* the exact real result.  Nothing here assumes the
returned interval is tight.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Itv

theorem scale_pos : 0 < scale := by norm_num [scale]

theorem scale_pos_real : (0:ℝ) < (scale : ℝ) := by
  have h : (0:Int) < scale := scale_pos
  exact_mod_cast h

/-- The real number denoted by a scaled integer. -/
noncomputable def value (n : Int) : ℝ := (n : ℝ) / (scale : ℝ)

/-! ### Directed integer rounding -/

theorem rdown_le {n d : Int} (hd : 0 < d) : ((rdown n d : Int) : ℝ) ≤ (n : ℝ) / (d : ℝ) := by
  have hmul : (rdown n d) * d ≤ n := by
    have h1 := Int.mul_ediv_add_emod n d
    have h2 := Int.emod_nonneg n (by omega : d ≠ 0)
    have h3 : n / d * d = d * (n / d) := mul_comm _ _
    simp only [rdown]
    omega
  have hd' : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [le_div_iff₀ hd']
  exact_mod_cast hmul

theorem le_rup {n d : Int} (hd : 0 < d) : (n : ℝ) / (d : ℝ) ≤ ((rup n d : Int) : ℝ) := by
  have hmul : n ≤ (rup n d) * d := by
    have h1 := Int.mul_ediv_add_emod (-n) d
    have h2 := Int.emod_nonneg (-n) (by omega : d ≠ 0)
    have h3 : (-n) / d * d = d * ((-n) / d) := mul_comm _ _
    have h4 : -((-n) / d) * d = -(d * ((-n) / d)) := by rw [neg_mul, h3]
    simp only [rup]
    omega
  have hd' : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [div_le_iff₀ hd']
  exact_mod_cast hmul

/-! ### Intervals -/

/-- Membership of a real number in a dyadic interval. -/
noncomputable def DI.Mem (i : DI) (x : ℝ) : Prop := value i.lo ≤ x ∧ x ≤ value i.hi

/-- The scale-free form of membership, used in every soundness proof. -/
theorem mem_iff {i : DI} {x : ℝ} :
    i.Mem x ↔ ((i.lo : ℝ) ≤ x * (scale : ℝ) ∧ x * (scale : ℝ) ≤ (i.hi : ℝ)) := by
  have hs := scale_pos_real
  constructor
  · rintro ⟨h1, h2⟩
    rw [value, div_le_iff₀ hs] at h1
    rw [value, le_div_iff₀ hs] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [value, div_le_iff₀ hs]; exact h1, by rw [value, le_div_iff₀ hs]; exact h2⟩

/-! ### Addition, subtraction, negation -/

theorem mem_add {i j : DI} {x y : ℝ} (hx : i.Mem x) (hy : j.Mem y) :
    (add i j).Mem (x + y) := by
  rw [mem_iff] at hx hy ⊢
  constructor
  · show ((i.lo + j.lo : Int) : ℝ) ≤ _
    push_cast
    nlinarith [hx.1, hy.1]
  · show _ ≤ ((i.hi + j.hi : Int) : ℝ)
    push_cast
    nlinarith [hx.2, hy.2]

theorem mem_neg {i : DI} {x : ℝ} (hx : i.Mem x) : (neg i).Mem (-x) := by
  rw [mem_iff] at hx ⊢
  constructor
  · show ((-i.hi : Int) : ℝ) ≤ _
    push_cast
    nlinarith [hx.2]
  · show _ ≤ ((-i.lo : Int) : ℝ)
    push_cast
    nlinarith [hx.1]

theorem mem_sub {i j : DI} {x y : ℝ} (hx : i.Mem x) (hy : j.Mem y) :
    (sub i j).Mem (x - y) := by
  have h := mem_add hx (mem_neg hy)
  simpa [sub, sub_eq_add_neg] using h

/-! ### Multiplication -/

/-- The scalar monotonicity step used for products. -/
theorem mul_between {k c d y : ℝ} (h1 : c ≤ y) (h2 : y ≤ d) :
    min (k * c) (k * d) ≤ k * y ∧ k * y ≤ max (k * c) (k * d) := by
  rcases le_total 0 k with hk | hk
  · exact ⟨le_trans (min_le_left _ _) (by nlinarith),
      le_trans (by nlinarith) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (by nlinarith),
      le_trans (by nlinarith) (le_max_left _ _)⟩

/-- The real four-product enclosure of a product. -/
theorem mul_enclosure {a b c d x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b)
    (hy1 : c ≤ y) (hy2 : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  obtain ⟨hc1, hc2⟩ := mul_between (k := x) hy1 hy2
  obtain ⟨hac1, hac2⟩ := mul_between (k := c) hx1 hx2
  obtain ⟨had1, had2⟩ := mul_between (k := d) hx1 hx2
  have hxc1 : min (a * c) (b * c) ≤ x * c := by
    have h : min (c * a) (c * b) ≤ c * x := hac1
    rwa [mul_comm c a, mul_comm c b, mul_comm c x] at h
  have hxc2 : x * c ≤ max (a * c) (b * c) := by
    have h : c * x ≤ max (c * a) (c * b) := hac2
    rwa [mul_comm c a, mul_comm c b, mul_comm c x] at h
  have hxd1 : min (a * d) (b * d) ≤ x * d := by
    have h : min (d * a) (d * b) ≤ d * x := had1
    rwa [mul_comm d a, mul_comm d b, mul_comm d x] at h
  have hxd2 : x * d ≤ max (a * d) (b * d) := by
    have h : d * x ≤ max (d * a) (d * b) := had2
    rwa [mul_comm d a, mul_comm d b, mul_comm d x] at h
  constructor
  · refine le_trans ?_ hc1
    rcases min_cases (x * c) (x * d) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he]
    · refine le_trans ?_ hxc1
      rcases min_cases (a * c) (b * c) with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm]
      · exact le_trans (min_le_left _ _) (min_le_left _ _)
      · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · refine le_trans ?_ hxd1
      rcases min_cases (a * d) (b * d) with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm]
      · exact le_trans (min_le_left _ _) (min_le_right _ _)
      · exact le_trans (min_le_right _ _) (min_le_right _ _)
  · refine le_trans hc2 ?_
    rcases max_cases (x * c) (x * d) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he]
    · refine le_trans hxc2 ?_
      rcases max_cases (a * c) (b * c) with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm]
      · exact le_trans (le_max_left _ _) (le_max_left _ _)
      · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · refine le_trans hxd2 ?_
      rcases max_cases (a * d) (b * d) with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm]
      · exact le_trans (le_max_right _ _) (le_max_left _ _)
      · exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem mem_mulGen {i j : DI} {x y : ℝ} (hx : i.Mem x) (hy : j.Mem y) :
    (mulGen i j).Mem (x * y) := by
  have hs := scale_pos_real
  rw [mem_iff] at hx hy ⊢
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  obtain ⟨hlo, hhi⟩ := mul_enclosure h1 h2 h3 h4
  constructor
  · have hr := rdown_le (n := min (min (i.lo * j.lo) (i.lo * j.hi))
      (min (i.hi * j.lo) (i.hi * j.hi))) scale_pos
    refine le_trans hr ?_
    rw [div_le_iff₀ hs]
    have hcast : ((min (min (i.lo * j.lo) (i.lo * j.hi))
        (min (i.hi * j.lo) (i.hi * j.hi)) : Int) : ℝ)
        = min (min ((i.lo:ℝ) * (j.lo:ℝ)) ((i.lo:ℝ) * (j.hi:ℝ)))
          (min ((i.hi:ℝ) * (j.lo:ℝ)) ((i.hi:ℝ) * (j.hi:ℝ))) := by
      push_cast
      rfl
    rw [hcast]
    nlinarith [hlo]
  · have hr := le_rup (n := max (max (i.lo * j.lo) (i.lo * j.hi))
      (max (i.hi * j.lo) (i.hi * j.hi))) scale_pos
    refine le_trans ?_ hr
    rw [le_div_iff₀ hs]
    have hcast : ((max (max (i.lo * j.lo) (i.lo * j.hi))
        (max (i.hi * j.lo) (i.hi * j.hi)) : Int) : ℝ)
        = max (max ((i.lo:ℝ) * (j.lo:ℝ)) ((i.lo:ℝ) * (j.hi:ℝ)))
          (max ((i.hi:ℝ) * (j.lo:ℝ)) ((i.hi:ℝ) * (j.hi:ℝ))) := by
      push_cast
      rfl
    rw [hcast]
    nlinarith [hhi]

/-! ### The sign-classified form of multiplication

`mul` selects the extremal pair of endpoint products from the signs of the
endpoints.  On ordered intervals — the only ones that can contain a real
number — this is the same value as the four-product form `mulGen`. -/

/-- The minimum of four integers, identified by a member that is a lower bound. -/
theorem min4_eq {a b c d x : Int} (hx : x = a ∨ x = b ∨ x = c ∨ x = d)
    (h1 : x ≤ a) (h2 : x ≤ b) (h3 : x ≤ c) (h4 : x ≤ d) :
    min (min a b) (min c d) = x := by
  refine le_antisymm ?_ (le_min (le_min h1 h2) (le_min h3 h4))
  rcases hx with rfl | rfl | rfl | rfl
  · exact le_trans (min_le_left _ _) (min_le_left _ _)
  · exact le_trans (min_le_left _ _) (min_le_right _ _)
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · exact le_trans (min_le_right _ _) (min_le_right _ _)

/-- The maximum of four integers, identified by a member that is an upper bound. -/
theorem max4_eq {a b c d x : Int} (hx : x = a ∨ x = b ∨ x = c ∨ x = d)
    (h1 : a ≤ x) (h2 : b ≤ x) (h3 : c ≤ x) (h4 : d ≤ x) :
    max (max a b) (max c d) = x := by
  refine le_antisymm (max_le (max_le h1 h2) (max_le h3 h4)) ?_
  rcases hx with rfl | rfl | rfl | rfl
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem mul_eq_mulGen (i j : DI) : mul i j = mulGen i j := by
  obtain ⟨a, b⟩ := i
  obtain ⟨c, d⟩ := j
  by_cases hord : a ≤ b ∧ c ≤ d
  · obtain ⟨hi, hj⟩ := hord
    simp only [mul, mulGen, hi, hj, and_self, not_true, if_false]
    by_cases ha : 0 ≤ a
    · by_cases hc : 0 ≤ c
      · simp only [ha, hc, if_true]
        have h1 : min (min (a * c) (a * d)) (min (b * c) (b * d)) = a * c :=
          min4_eq (Or.inl rfl) (by nlinarith) (by nlinarith) (by nlinarith)
            (by nlinarith)
        have h2 : max (max (a * c) (a * d)) (max (b * c) (b * d)) = b * d :=
          max4_eq (Or.inr (Or.inr (Or.inr rfl))) (by nlinarith) (by nlinarith) (by nlinarith)
            (by nlinarith)
        rw [h1, h2]
      · by_cases hd : d ≤ 0
        · simp only [ha, hc, hd, if_true, if_false]
          have h1 : min (min (a * c) (a * d)) (min (b * c) (b * d)) = b * c :=
            min4_eq (Or.inr (Or.inr (Or.inl rfl))) (by nlinarith) (by nlinarith) (by nlinarith)
              (by nlinarith)
          have h2 : max (max (a * c) (a * d)) (max (b * c) (b * d)) = a * d :=
            max4_eq (Or.inr (Or.inl rfl)) (by nlinarith) (by nlinarith) (by nlinarith)
              (by nlinarith)
          rw [h1, h2]
        · simp only [ha, hc, hd, if_true, if_false]
          have h1 : min (min (a * c) (a * d)) (min (b * c) (b * d)) = b * c :=
            min4_eq (Or.inr (Or.inr (Or.inl rfl))) (by nlinarith) (by nlinarith) (by nlinarith)
              (by nlinarith)
          have h2 : max (max (a * c) (a * d)) (max (b * c) (b * d)) = b * d :=
            max4_eq (Or.inr (Or.inr (Or.inr rfl))) (by nlinarith) (by nlinarith) (by nlinarith)
              (by nlinarith)
          rw [h1, h2]
    · by_cases hb : b ≤ 0
      · by_cases hc : 0 ≤ c
        · simp only [ha, hb, hc, if_true, if_false]
          have h1 : min (min (a * c) (a * d)) (min (b * c) (b * d)) = a * d :=
            min4_eq (Or.inr (Or.inl rfl)) (by nlinarith) (by nlinarith) (by nlinarith)
              (by nlinarith)
          have h2 : max (max (a * c) (a * d)) (max (b * c) (b * d)) = b * c :=
            max4_eq (Or.inr (Or.inr (Or.inl rfl))) (by nlinarith) (by nlinarith) (by nlinarith)
              (by nlinarith)
          rw [h1, h2]
        · by_cases hd : d ≤ 0
          · simp only [ha, hb, hc, hd, if_true, if_false]
            have h1 : min (min (a * c) (a * d)) (min (b * c) (b * d)) = b * d :=
              min4_eq (Or.inr (Or.inr (Or.inr rfl))) (by nlinarith) (by nlinarith) (by nlinarith)
                (by nlinarith)
            have h2 : max (max (a * c) (a * d)) (max (b * c) (b * d)) = a * c :=
              max4_eq (Or.inl rfl) (by nlinarith) (by nlinarith) (by nlinarith)
                (by nlinarith)
            rw [h1, h2]
          · simp only [ha, hb, hc, hd, if_true, if_false]
            have h1 : min (min (a * c) (a * d)) (min (b * c) (b * d)) = a * d :=
              min4_eq (Or.inr (Or.inl rfl)) (by nlinarith) (by nlinarith) (by nlinarith)
                (by nlinarith)
            have h2 : max (max (a * c) (a * d)) (max (b * c) (b * d)) = a * c :=
              max4_eq (Or.inl rfl) (by nlinarith) (by nlinarith) (by nlinarith)
                (by nlinarith)
            rw [h1, h2]
      · by_cases hc : 0 ≤ c
        · simp only [ha, hb, hc, if_true, if_false]
          have h1 : min (min (a * c) (a * d)) (min (b * c) (b * d)) = a * d :=
            min4_eq (Or.inr (Or.inl rfl)) (by nlinarith) (by nlinarith) (by nlinarith)
              (by nlinarith)
          have h2 : max (max (a * c) (a * d)) (max (b * c) (b * d)) = b * d :=
            max4_eq (Or.inr (Or.inr (Or.inr rfl))) (by nlinarith) (by nlinarith) (by nlinarith)
              (by nlinarith)
          rw [h1, h2]
        · by_cases hd : d ≤ 0
          · simp only [ha, hb, hc, hd, if_true, if_false]
            have h1 : min (min (a * c) (a * d)) (min (b * c) (b * d)) = b * c :=
              min4_eq (Or.inr (Or.inr (Or.inl rfl))) (by nlinarith) (by nlinarith) (by nlinarith)
                (by nlinarith)
            have h2 : max (max (a * c) (a * d)) (max (b * c) (b * d)) = a * c :=
              max4_eq (Or.inl rfl) (by nlinarith) (by nlinarith) (by nlinarith)
                (by nlinarith)
            rw [h1, h2]
          · simp only [ha, hb, hc, hd, if_false]
  · simp only [mul, hord, not_false_eq_true, if_true]

theorem mem_mul {i j : DI} {x y : ℝ} (hx : i.Mem x) (hy : j.Mem y) :
    (mul i j).Mem (x * y) := by
  rw [mul_eq_mulGen]
  exact mem_mulGen hx hy

/-! ### Powers -/

theorem mem_oneI : oneI.Mem 1 := by
  have hs := scale_pos_real
  rw [mem_iff]
  simp [oneI, pt]

theorem mem_pow {i : DI} {x : ℝ} (hx : i.Mem x) : ∀ n : ℕ, (pow i n).Mem (x ^ n)
  | 0 => by simpa [pow] using mem_oneI
  | 1 => by simpa [pow] using hx
  | (n + 2) => by
      have h := mem_mul hx (mem_pow hx (n + 1))
      simpa [pow, pow_succ, mul_comm] using h

/-! ### Inversion and division of positive intervals -/

theorem mem_inv {i : DI} {x : ℝ} (hx : i.Mem x) (hlo : 0 < i.lo) : (inv i).Mem x⁻¹ := by
  have hs := scale_pos_real
  have hlo' : (0:ℝ) < (i.lo : ℝ) := by exact_mod_cast hlo
  rw [mem_iff] at hx
  obtain ⟨h1, h2⟩ := hx
  have hxs : 0 < x * (scale:ℝ) := lt_of_lt_of_le hlo' h1
  have hxpos : 0 < x := by nlinarith
  have hhiR : (0:ℝ) < (i.hi:ℝ) := lt_of_lt_of_le hxs h2
  have hhi : 0 < i.hi := by exact_mod_cast hhiR
  have hinv : 0 < x⁻¹ * (scale:ℝ) := mul_pos (inv_pos.2 hxpos) hs
  have hcancel : x⁻¹ * (scale:ℝ) * (x * (scale:ℝ)) = (scale:ℝ) * (scale:ℝ) := by
    field_simp
  rw [mem_iff]
  constructor
  · refine le_trans (rdown_le (n := scale * scale) hhi) ?_
    rw [div_le_iff₀ hhiR]
    have hstep := mul_le_mul_of_nonneg_left h2 hinv.le
    rw [hcancel] at hstep
    push_cast
    nlinarith [hstep]
  · refine le_trans ?_ (le_rup (n := scale * scale) hlo)
    rw [le_div_iff₀ hlo']
    have hstep := mul_le_mul_of_nonneg_left h1 hinv.le
    rw [hcancel] at hstep
    push_cast
    nlinarith [hstep]

theorem mem_div {i j : DI} {x y : ℝ} (hx : i.Mem x) (hy : j.Mem y) (hlo : 0 < j.lo) :
    (div i j).Mem (x / y) := by
  have h := mem_mul hx (mem_inv hy hlo)
  simpa [div, div_eq_mul_inv] using h

/-! ### Reading off sign information -/

theorem pos_of_mem {i : DI} {x : ℝ} (hx : i.Mem x) (h : 0 < i.lo) : 0 < x := by
  have hs := scale_pos_real
  have h1 : (0:ℝ) < (i.lo : ℝ) := by exact_mod_cast h
  rw [mem_iff] at hx
  nlinarith [hx.1]

theorem neg_of_mem {i : DI} {x : ℝ} (hx : i.Mem x) (h : i.hi < 0) : x < 0 := by
  have hs := scale_pos_real
  have h1 : ((i.hi : Int) : ℝ) < 0 := by exact_mod_cast h
  rw [mem_iff] at hx
  nlinarith [hx.2]

/-- Comparison of a scaled integer with a rational number: `p/q ≤ value n`. -/
theorem rat_le_value {p q n : Int} (hq : 0 < q) (h : p * scale ≤ n * q) :
    (p : ℝ) / (q : ℝ) ≤ value n := by
  have hq' : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hs := scale_pos_real
  have hcast : (p : ℝ) * (scale:ℝ) ≤ (n : ℝ) * (q:ℝ) := by exact_mod_cast h
  rw [value, div_le_div_iff₀ hq' hs]
  linarith

/-- Comparison of a scaled integer with a rational number: `value n ≤ p/q`. -/
theorem value_le_rat {p q n : Int} (hq : 0 < q) (h : n * q ≤ p * scale) :
    value n ≤ (p : ℝ) / (q : ℝ) := by
  have hq' : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hs := scale_pos_real
  have hcast : (n : ℝ) * (q:ℝ) ≤ (p : ℝ) * (scale:ℝ) := by exact_mod_cast h
  rw [value, div_le_div_iff₀ hs hq']
  linarith

end Itv
end TriangleNumerical
