import TriangleNumerical.Deriv
import TriangleNumerical.LogInterval

/- ### From `Cover` -/

/-!
# Soundness of the finite cover and of its leaf rules

Section 10 of the blueprint, in the abstract.  Nothing here mentions interval
arithmetic or the exported trees: the file fixes a symmetric continuous
function `Φ : ℝ³ → ℝ` and a target value `M`, and proves

* a *global minimiser* of `Φ` on the cube `[0,1]³` exists and may be assumed
  ordered (`exists_ordered_min`);
* the checker invariant `Excludes`, "no ordered bad global minimum lies in this
  box", is preserved by splitting a box into two closed children whose union
  covers it (`Excludes.split`);
* each of the leaf acceptance rules of §10 implies `Excludes`:
  empty ordered intersection, an analytic local lower bound, a strict pointwise
  gap, and the two feasible-descent rules;
* and finally that `Excludes` for the root box `[0,1]³` implies the desired
  global lower bound `M ≤ Φ` on the cube (`le_of_excludes_root`).

A *bad* point is by definition a global minimiser on the **full** cube whose
value is strictly below the target, so the derivative rules never need a
pointwise gap: they only have to exhibit a feasible descent direction.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Cover
noncomputable section

open Real Set Filter Topology

/-! ### The cube and bad points -/

/-- The unit cube as a subset of `ℝ × ℝ × ℝ`. -/
def cube : Set (ℝ × ℝ × ℝ) := Icc 0 1 ×ˢ Icc 0 1 ×ˢ Icc 0 1

theorem mem_cube {w₁ w₂ w₃ : ℝ} :
    (w₁, w₂, w₃) ∈ cube ↔
      (0 ≤ w₁ ∧ w₁ ≤ 1) ∧ (0 ≤ w₂ ∧ w₂ ≤ 1) ∧ (0 ≤ w₃ ∧ w₃ ≤ 1) := by
  simp only [cube, Set.mem_prod, Set.mem_Icc]

/-- `w` is a *bad global minimum*: it lies in the cube, minimises `Φ` over the
whole cube, and its value is strictly below the target `M`. -/
def BadMin (Φ : ℝ → ℝ → ℝ → ℝ) (M : ℝ) (w₁ w₂ w₃ : ℝ) : Prop :=
  ((0 ≤ w₁ ∧ w₁ ≤ 1) ∧ (0 ≤ w₂ ∧ w₂ ≤ 1) ∧ (0 ≤ w₃ ∧ w₃ ≤ 1)) ∧
    (∀ v₁ v₂ v₃ : ℝ, (0 ≤ v₁ ∧ v₁ ≤ 1) → (0 ≤ v₂ ∧ v₂ ≤ 1) → (0 ≤ v₃ ∧ v₃ ≤ 1) →
      Φ w₁ w₂ w₃ ≤ Φ v₁ v₂ v₃) ∧
    Φ w₁ w₂ w₃ < M

/-! ### Boxes -/

/-- A closed axis-parallel box with real (in practice rational) endpoints. -/
structure Box where
  lo₁ : ℝ
  hi₁ : ℝ
  lo₂ : ℝ
  hi₂ : ℝ
  lo₃ : ℝ
  hi₃ : ℝ

/-- Membership in a box. -/
def Box.mem (b : Box) (w₁ w₂ w₃ : ℝ) : Prop :=
  (b.lo₁ ≤ w₁ ∧ w₁ ≤ b.hi₁) ∧ (b.lo₂ ≤ w₂ ∧ w₂ ≤ b.hi₂) ∧ (b.lo₃ ≤ w₃ ∧ w₃ ≤ b.hi₃)

/-- The checker invariant: the box contains no ordered bad global minimum. -/
def Excludes (Φ : ℝ → ℝ → ℝ → ℝ) (M : ℝ) (b : Box) : Prop :=
  ∀ w₁ w₂ w₃ : ℝ, w₁ ≤ w₂ → w₂ ≤ w₃ → b.mem w₁ w₂ w₃ → ¬ BadMin Φ M w₁ w₂ w₃

/-! ### Symmetry: an ordered minimiser -/

/-- The symmetry hypothesis: `Φ` is invariant under the two adjacent
transpositions, hence under every permutation of its arguments. -/
structure Symm (Φ : ℝ → ℝ → ℝ → ℝ) : Prop where
  swap12 : ∀ a b c : ℝ, Φ a b c = Φ b a c
  swap23 : ∀ a b c : ℝ, Φ a b c = Φ a c b

theorem Symm.swap13 {Φ : ℝ → ℝ → ℝ → ℝ} (hs : Symm Φ) (a b c : ℝ) :
    Φ a b c = Φ c b a := by
  rw [hs.swap23 a b c, hs.swap12 a c b, hs.swap23 c a b]

/-- Any triple can be reordered increasingly without changing the value of a
symmetric `Φ`, and the reordering stays in the cube. -/
theorem exists_sorted {Φ : ℝ → ℝ → ℝ → ℝ} (hs : Symm Φ) (a b c : ℝ) :
    ∃ x y z : ℝ, x ≤ y ∧ y ≤ z ∧ Φ x y z = Φ a b c ∧
      ((x = a ∨ x = b ∨ x = c) ∧ (y = a ∨ y = b ∨ y = c) ∧ (z = a ∨ z = b ∨ z = c)) := by
  rcases le_total a b with hab | hab <;> rcases le_total b c with hbc | hbc <;>
    rcases le_total a c with hac | hac
  · exact ⟨a, b, c, hab, hbc, rfl, by tauto⟩
  · exact ⟨a, b, c, hab, hbc, rfl, by tauto⟩
  · exact ⟨a, c, b, hac, hbc, (hs.swap23 a b c).symm, by tauto⟩
  · exact ⟨c, a, b, hac, hab, (hs.swap12 c a b).trans (hs.swap23 a b c).symm, by tauto⟩
  · exact ⟨b, a, c, hab, hac, hs.swap12 b a c, by tauto⟩
  · exact ⟨b, c, a, hbc, hac, (hs.swap12 b c a).trans (hs.swap13 a b c).symm, by tauto⟩
  · exact ⟨b, a, c, hab, hac, hs.swap12 b a c, by tauto⟩
  · exact ⟨c, b, a, hbc, hab, (hs.swap13 a b c).symm, by tauto⟩

/-! ### Existence of a global minimiser -/

theorem exists_min {Φ : ℝ → ℝ → ℝ → ℝ}
    (hc : Continuous fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2) :
    ∃ w₁ w₂ w₃ : ℝ, ((0 ≤ w₁ ∧ w₁ ≤ 1) ∧ (0 ≤ w₂ ∧ w₂ ≤ 1) ∧ (0 ≤ w₃ ∧ w₃ ≤ 1)) ∧
      ∀ v₁ v₂ v₃ : ℝ, (0 ≤ v₁ ∧ v₁ ≤ 1) → (0 ≤ v₂ ∧ v₂ ≤ 1) → (0 ≤ v₃ ∧ v₃ ≤ 1) →
        Φ w₁ w₂ w₃ ≤ Φ v₁ v₂ v₃ := by
  have hK : IsCompact cube :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hne : cube.Nonempty := ⟨(0, 0, 0), by simp [mem_cube]⟩
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hc.continuousOn
  refine ⟨p.1, p.2.1, p.2.2, mem_cube.1 (by simpa using hp), ?_⟩
  intro v₁ v₂ v₃ h₁ h₂ h₃
  exact hmin (show (v₁, v₂, v₃) ∈ cube from mem_cube.2 ⟨h₁, h₂, h₃⟩)

/-! ### The main soundness theorem -/

/-- If the root box excludes every ordered bad global minimum, the target is a
global lower bound on the cube. -/
theorem le_of_excludes_root {Φ : ℝ → ℝ → ℝ → ℝ} {M : ℝ} (hs : Symm Φ)
    (hc : Continuous fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2)
    (hex : Excludes Φ M ⟨0, 1, 0, 1, 0, 1⟩) :
    ∀ w₁ w₂ w₃ : ℝ, (0 ≤ w₁ ∧ w₁ ≤ 1) → (0 ≤ w₂ ∧ w₂ ≤ 1) → (0 ≤ w₃ ∧ w₃ ≤ 1) →
      M ≤ Φ w₁ w₂ w₃ := by
  obtain ⟨m₁, m₂, m₃, hmem, hmin⟩ := exists_min hc
  intro w₁ w₂ w₃ h₁ h₂ h₃
  by_contra hlt
  push_neg at hlt
  have hmlt : Φ m₁ m₂ m₃ < M := lt_of_le_of_lt (hmin w₁ w₂ w₃ h₁ h₂ h₃) hlt
  obtain ⟨x, y, z, hxy, hyz, hval, hmemx, hmemy, hmemz⟩ := exists_sorted hs m₁ m₂ m₃
  have hcube : ∀ u : ℝ, (u = m₁ ∨ u = m₂ ∨ u = m₃) → 0 ≤ u ∧ u ≤ 1 := by
    rintro u (rfl | rfl | rfl)
    exacts [hmem.1, hmem.2.1, hmem.2.2]
  refine hex x y z hxy hyz ⟨hcube x hmemx, hcube y hmemy, hcube z hmemz⟩
    ⟨⟨hcube x hmemx, hcube y hmemy, hcube z hmemz⟩, ?_, ?_⟩
  · intro v₁ v₂ v₃ k₁ k₂ k₃
    rw [hval]; exact hmin v₁ v₂ v₃ k₁ k₂ k₃
  · rw [hval]; exact hmlt

/-! ### Splitting -/

/-- Splitting a box into two closed children whose union covers it. -/
theorem Excludes.split {Φ : ℝ → ℝ → ℝ → ℝ} {M : ℝ} {b l r : Box}
    (hcov : ∀ w₁ w₂ w₃ : ℝ, b.mem w₁ w₂ w₃ → l.mem w₁ w₂ w₃ ∨ r.mem w₁ w₂ w₃)
    (hl : Excludes Φ M l) (hr : Excludes Φ M r) : Excludes Φ M b := by
  intro w₁ w₂ w₃ h₁₂ h₂₃ hmem
  rcases hcov w₁ w₂ w₃ hmem with h | h
  · exact hl w₁ w₂ w₃ h₁₂ h₂₃ h
  · exact hr w₁ w₂ w₃ h₁₂ h₂₃ h

/-! ### Leaf rule 1: empty ordered intersection -/

theorem excludes_empty_ordered {Φ : ℝ → ℝ → ℝ → ℝ} {M : ℝ} {b : Box}
    (h : b.hi₂ < b.lo₁ ∨ b.hi₃ < b.lo₂) : Excludes Φ M b := by
  intro w₁ w₂ w₃ h₁₂ h₂₃ hmem _
  rcases h with h | h
  · exact absurd (le_trans hmem.1.1 (le_trans h₁₂ hmem.2.1.2)) (not_le.2 h)
  · exact absurd (le_trans hmem.2.1.1 (le_trans h₂₃ hmem.2.2.2)) (not_le.2 h)

/-! ### Leaf rule 2/3/4: a lower bound valid on the whole box -/

/-- Any box on which the target is already a lower bound excludes bad minima.
This covers the analytic local regions as well as the direct and centered
numerical value tests. -/
theorem excludes_of_bound {Φ : ℝ → ℝ → ℝ → ℝ} {M : ℝ} {b : Box}
    (h : ∀ w₁ w₂ w₃ : ℝ, b.mem w₁ w₂ w₃ →
      (0 ≤ w₁ ∧ w₁ ≤ 1) → (0 ≤ w₂ ∧ w₂ ≤ 1) → (0 ≤ w₃ ∧ w₃ ≤ 1) → M ≤ Φ w₁ w₂ w₃) :
    Excludes Φ M b := by
  intro w₁ w₂ w₃ _ _ hmem hbad
  exact absurd (h w₁ w₂ w₃ hmem hbad.1.1 hbad.1.2.1 hbad.1.2.2) (not_le.2 hbad.2.2)

/-! ### The scalar descent lemmas -/

/-- A point with positive derivative and positive coordinate is not a minimum
of a one-dimensional restriction on `[0,1]`. -/
theorem not_min_of_deriv_pos {g : ℝ → ℝ} {w d : ℝ} (hd : HasDerivAt g d w)
    (hpos : 0 < d) (hw : 0 < w) (hmin : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → g w ≤ g x)
    (hw1 : w ≤ 1) : False := by
  have hslope : Tendsto (slope g w) (𝓝[≠] w) (𝓝 d) := hasDerivAt_iff_tendsto_slope.1 hd
  have h1 : ∀ᶠ y in 𝓝[<] w, 0 < slope g w y := by
    have h0 : ∀ᶠ y in 𝓝[≠] w, 0 < slope g w y := hslope.eventually (eventually_gt_nhds hpos)
    exact nhdsWithin_mono w (fun x hx => ne_of_lt hx) h0
  have h2 : ∀ᶠ y in 𝓝[<] w, 0 < y :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hw)
  have h3 : ∀ᶠ y in 𝓝[<] w, y < w := eventually_mem_nhdsWithin
  obtain ⟨y, ⟨⟨hy1, hy2⟩, hy3⟩⟩ := ((h1.and h2).and h3).exists
  rw [slope_def_field] at hy1
  have hneg : y - w < 0 := by linarith
  have hlt : g y < g w := by
    rcases div_pos_iff.1 hy1 with ⟨hnum, _⟩ | ⟨hnum, _⟩
    · linarith
    · linarith
  exact absurd (hmin y hy2.le (by linarith)) (not_le.2 hlt)

/-- A point with negative derivative and coordinate below `1` is not a minimum
of a one-dimensional restriction on `[0,1]`. -/
theorem not_min_of_deriv_neg {g : ℝ → ℝ} {w d : ℝ} (hd : HasDerivAt g d w)
    (hneg : d < 0) (hw : w < 1) (hmin : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → g w ≤ g x)
    (hw0 : 0 ≤ w) : False := by
  have hin : HasDerivAt (fun x : ℝ => 1 - x) (-1 : ℝ) (1 - w) := by
    simpa using (hasDerivAt_id (1 - w)).const_sub (1:ℝ)
  have hd0 : HasDerivAt g d (1 - (1 - w)) := by simpa using hd
  have hd2 := HasDerivAt.comp (1 - w) hd0 hin
  have hd' : HasDerivAt (fun x : ℝ => g (1 - x)) (-d) (1 - w) := by
    simpa [Function.comp] using hd2
  refine not_min_of_deriv_pos (g := fun x : ℝ => g (1 - x)) (w := 1 - w) (d := -d) hd'
    (by linarith) (by linarith) ?_ (by linarith)
  intro x hx0 hx1
  simpa using hmin (1 - x) (by linarith) (by linarith)

/-! ### Leaf rules 5 and 6: feasible descent -/

/-- Descent in the first coordinate: if `∂₁Φ > 0` throughout the box and the
box has a positive lower endpoint in that coordinate, no bad minimum lies in
it.  (The proof only needs the derivative at the candidate point.) -/
theorem excludes_descent₁ {Φ : ℝ → ℝ → ℝ → ℝ} {M : ℝ} {b : Box} {d : ℝ → ℝ → ℝ → ℝ}
    (hderiv : ∀ w₁ w₂ w₃ : ℝ, w₁ ≠ 0 → HasDerivAt (fun x => Φ x w₂ w₃) (d w₁ w₂ w₃) w₁)
    (hlo : 0 < b.lo₁)
    (hsign : ∀ w₁ w₂ w₃ : ℝ, b.mem w₁ w₂ w₃ → 0 < d w₁ w₂ w₃) :
    Excludes Φ M b := by
  intro w₁ w₂ w₃ _ _ hmem hbad
  have hw₁pos : 0 < w₁ := lt_of_lt_of_le hlo hmem.1.1
  exact not_min_of_deriv_pos (hderiv w₁ w₂ w₃ (ne_of_gt hw₁pos)) (hsign w₁ w₂ w₃ hmem)
    hw₁pos (fun x hx0 hx1 => hbad.2.1 x w₂ w₃ ⟨hx0, hx1⟩ hbad.1.2.1 hbad.1.2.2)
    hbad.1.1.2

/-- Ascent in the first coordinate: if `∂₁Φ < 0` throughout the box and the box
has an upper endpoint below `1` in that coordinate. -/
theorem excludes_ascent₁ {Φ : ℝ → ℝ → ℝ → ℝ} {M : ℝ} {b : Box} {d : ℝ → ℝ → ℝ → ℝ}
    (hderiv : ∀ w₁ w₂ w₃ : ℝ, w₁ ≠ 0 → HasDerivAt (fun x => Φ x w₂ w₃) (d w₁ w₂ w₃) w₁)
    (hlo : 0 < b.lo₁) (hhi : b.hi₁ < 1)
    (hsign : ∀ w₁ w₂ w₃ : ℝ, b.mem w₁ w₂ w₃ → d w₁ w₂ w₃ < 0) :
    Excludes Φ M b := by
  intro w₁ w₂ w₃ _ _ hmem hbad
  have hw₁pos : 0 < w₁ := lt_of_lt_of_le hlo hmem.1.1
  exact not_min_of_deriv_neg (hderiv w₁ w₂ w₃ (ne_of_gt hw₁pos)) (hsign w₁ w₂ w₃ hmem)
    (lt_of_le_of_lt hmem.1.2 hhi)
    (fun x hx0 hx1 => hbad.2.1 x w₂ w₃ ⟨hx0, hx1⟩ hbad.1.2.1 hbad.1.2.2) hw₁pos.le

/-- Descent in the second coordinate.  A bad minimum is a global minimum in
*every* coordinate, so no symmetry of `Φ` is needed here. -/
theorem excludes_descent₂ {Φ : ℝ → ℝ → ℝ → ℝ} {M : ℝ} {b : Box} {d : ℝ → ℝ → ℝ → ℝ}
    (hderiv : ∀ w₁ w₂ w₃ : ℝ, w₂ ≠ 0 → HasDerivAt (fun x => Φ w₁ x w₃) (d w₁ w₂ w₃) w₂)
    (hlo : 0 < b.lo₂)
    (hsign : ∀ w₁ w₂ w₃ : ℝ, b.mem w₁ w₂ w₃ → 0 < d w₁ w₂ w₃) :
    Excludes Φ M b := by
  intro w₁ w₂ w₃ _ _ hmem hbad
  have hw₂pos : 0 < w₂ := lt_of_lt_of_le hlo hmem.2.1.1
  exact not_min_of_deriv_pos (hderiv w₁ w₂ w₃ (ne_of_gt hw₂pos)) (hsign w₁ w₂ w₃ hmem)
    hw₂pos (fun x hx0 hx1 => hbad.2.1 w₁ x w₃ hbad.1.1 ⟨hx0, hx1⟩ hbad.1.2.2)
    hbad.1.2.1.2

/-- Ascent in the second coordinate. -/
theorem excludes_ascent₂ {Φ : ℝ → ℝ → ℝ → ℝ} {M : ℝ} {b : Box} {d : ℝ → ℝ → ℝ → ℝ}
    (hderiv : ∀ w₁ w₂ w₃ : ℝ, w₂ ≠ 0 → HasDerivAt (fun x => Φ w₁ x w₃) (d w₁ w₂ w₃) w₂)
    (hlo : 0 < b.lo₂) (hhi : b.hi₂ < 1)
    (hsign : ∀ w₁ w₂ w₃ : ℝ, b.mem w₁ w₂ w₃ → d w₁ w₂ w₃ < 0) :
    Excludes Φ M b := by
  intro w₁ w₂ w₃ _ _ hmem hbad
  have hw₂pos : 0 < w₂ := lt_of_lt_of_le hlo hmem.2.1.1
  exact not_min_of_deriv_neg (hderiv w₁ w₂ w₃ (ne_of_gt hw₂pos)) (hsign w₁ w₂ w₃ hmem)
    (lt_of_le_of_lt hmem.2.1.2 hhi)
    (fun x hx0 hx1 => hbad.2.1 w₁ x w₃ hbad.1.1 ⟨hx0, hx1⟩ hbad.1.2.2) hw₂pos.le

/-- Descent in the third coordinate. -/
theorem excludes_descent₃ {Φ : ℝ → ℝ → ℝ → ℝ} {M : ℝ} {b : Box} {d : ℝ → ℝ → ℝ → ℝ}
    (hderiv : ∀ w₁ w₂ w₃ : ℝ, w₃ ≠ 0 → HasDerivAt (fun x => Φ w₁ w₂ x) (d w₁ w₂ w₃) w₃)
    (hlo : 0 < b.lo₃)
    (hsign : ∀ w₁ w₂ w₃ : ℝ, b.mem w₁ w₂ w₃ → 0 < d w₁ w₂ w₃) :
    Excludes Φ M b := by
  intro w₁ w₂ w₃ _ _ hmem hbad
  have hw₃pos : 0 < w₃ := lt_of_lt_of_le hlo hmem.2.2.1
  exact not_min_of_deriv_pos (hderiv w₁ w₂ w₃ (ne_of_gt hw₃pos)) (hsign w₁ w₂ w₃ hmem)
    hw₃pos (fun x hx0 hx1 => hbad.2.1 w₁ w₂ x hbad.1.1 hbad.1.2.1 ⟨hx0, hx1⟩)
    hbad.1.2.2.2

/-- Ascent in the third coordinate. -/
theorem excludes_ascent₃ {Φ : ℝ → ℝ → ℝ → ℝ} {M : ℝ} {b : Box} {d : ℝ → ℝ → ℝ → ℝ}
    (hderiv : ∀ w₁ w₂ w₃ : ℝ, w₃ ≠ 0 → HasDerivAt (fun x => Φ w₁ w₂ x) (d w₁ w₂ w₃) w₃)
    (hlo : 0 < b.lo₃) (hhi : b.hi₃ < 1)
    (hsign : ∀ w₁ w₂ w₃ : ℝ, b.mem w₁ w₂ w₃ → d w₁ w₂ w₃ < 0) :
    Excludes Φ M b := by
  intro w₁ w₂ w₃ _ _ hmem hbad
  have hw₃pos : 0 < w₃ := lt_of_lt_of_le hlo hmem.2.2.1
  exact not_min_of_deriv_neg (hderiv w₁ w₂ w₃ (ne_of_gt hw₃pos)) (hsign w₁ w₂ w₃ hmem)
    (lt_of_le_of_lt hmem.2.2.2 hhi)
    (fun x hx0 hx1 => hbad.2.1 w₁ w₂ x hbad.1.1 hbad.1.2.1 ⟨hx0, hx1⟩) hw₃pos.le

/-! ### Conditional feasible-ascent rules

The tail argument of §11 only bounds the derivative *at a bad minimum*, where
the value constraint `Φ < M` is available.  These variants of the ascent rules
take exactly that weaker hypothesis. -/

theorem excludes_ascent₁' {Φ : ℝ → ℝ → ℝ → ℝ} {M : ℝ} {b : Box} {d : ℝ → ℝ → ℝ → ℝ}
    (hderiv : ∀ w₁ w₂ w₃ : ℝ, w₁ ≠ 0 → HasDerivAt (fun x => Φ x w₂ w₃) (d w₁ w₂ w₃) w₁)
    (hlo : 0 < b.lo₁) (hhi : b.hi₁ < 1)
    (hsign : ∀ w₁ w₂ w₃ : ℝ, b.mem w₁ w₂ w₃ → BadMin Φ M w₁ w₂ w₃ → d w₁ w₂ w₃ < 0) :
    Excludes Φ M b := by
  intro w₁ w₂ w₃ _ _ hmem hbad
  have hw₁pos : 0 < w₁ := lt_of_lt_of_le hlo hmem.1.1
  exact not_min_of_deriv_neg (hderiv w₁ w₂ w₃ (ne_of_gt hw₁pos))
    (hsign w₁ w₂ w₃ hmem hbad) (lt_of_le_of_lt hmem.1.2 hhi)
    (fun x hx0 hx1 => hbad.2.1 x w₂ w₃ ⟨hx0, hx1⟩ hbad.1.2.1 hbad.1.2.2) hw₁pos.le

theorem excludes_ascent₂' {Φ : ℝ → ℝ → ℝ → ℝ} {M : ℝ} {b : Box} {d : ℝ → ℝ → ℝ → ℝ}
    (hderiv : ∀ w₁ w₂ w₃ : ℝ, w₂ ≠ 0 → HasDerivAt (fun x => Φ w₁ x w₃) (d w₁ w₂ w₃) w₂)
    (hlo : 0 < b.lo₂) (hhi : b.hi₂ < 1)
    (hsign : ∀ w₁ w₂ w₃ : ℝ, b.mem w₁ w₂ w₃ → BadMin Φ M w₁ w₂ w₃ → d w₁ w₂ w₃ < 0) :
    Excludes Φ M b := by
  intro w₁ w₂ w₃ _ _ hmem hbad
  have hw₂pos : 0 < w₂ := lt_of_lt_of_le hlo hmem.2.1.1
  exact not_min_of_deriv_neg (hderiv w₁ w₂ w₃ (ne_of_gt hw₂pos))
    (hsign w₁ w₂ w₃ hmem hbad) (lt_of_le_of_lt hmem.2.1.2 hhi)
    (fun x hx0 hx1 => hbad.2.1 w₁ x w₃ hbad.1.1 ⟨hx0, hx1⟩ hbad.1.2.2) hw₂pos.le

theorem excludes_ascent₃' {Φ : ℝ → ℝ → ℝ → ℝ} {M : ℝ} {b : Box} {d : ℝ → ℝ → ℝ → ℝ}
    (hderiv : ∀ w₁ w₂ w₃ : ℝ, w₃ ≠ 0 → HasDerivAt (fun x => Φ w₁ w₂ x) (d w₁ w₂ w₃) w₃)
    (hlo : 0 < b.lo₃) (hhi : b.hi₃ < 1)
    (hsign : ∀ w₁ w₂ w₃ : ℝ, b.mem w₁ w₂ w₃ → BadMin Φ M w₁ w₂ w₃ → d w₁ w₂ w₃ < 0) :
    Excludes Φ M b := by
  intro w₁ w₂ w₃ _ _ hmem hbad
  have hw₃pos : 0 < w₃ := lt_of_lt_of_le hlo hmem.2.2.1
  exact not_min_of_deriv_neg (hderiv w₁ w₂ w₃ (ne_of_gt hw₃pos))
    (hsign w₁ w₂ w₃ hmem hbad) (lt_of_le_of_lt hmem.2.2.2 hhi)
    (fun x hx0 hx1 => hbad.2.1 w₁ w₂ x hbad.1.1 hbad.1.2.1 ⟨hx0, hx1⟩) hw₃pos.le

end
end Cover
end TriangleNumerical


/- ### From `CoverPhi` -/

/-!
# The cover machinery applied to the branch certificate

This instantiates the abstract results of `Cover.lean` at the concrete
objective `Φ = entropyF (A h) (G_{h,θ})`: symmetry, continuity and the
derivative hypothesis are discharged once here, so that a finished replay of a
subdivision tree only has to supply `Excludes` for the root box.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Branch
noncomputable section

open Real

variable {h θ : ℝ}

theorem continuous_entropyF_triple (α : ℝ) {G : ℝ → ℝ} (hG : Continuous G) :
    Continuous fun p : ℝ × ℝ × ℝ => entropyF α G p.1 p.2.1 p.2.2 := by
  have hH := continuous_H
  unfold entropyF
  fun_prop

theorem symm_entropyF (α : ℝ) (G : ℝ → ℝ) : Cover.Symm (entropyF α G) :=
  ⟨fun a b c => entropyF_swap12 α G a b c, fun a b c => entropyF_swap23 α G a b c⟩

/-- The global cube bound produced by an exhausted subdivision tree. -/
theorem entropyF_ge_of_excludes (M : ℝ)
    (hex : Cover.Excludes (entropyF (bAlpha h) (bG h θ)) M ⟨0, 1, 0, 1, 0, 1⟩) :
    ∀ a ∈ unitInterval, ∀ b ∈ unitInterval, ∀ c ∈ unitInterval,
      M ≤ entropyF (bAlpha h) (bG h θ) a b c := by
  have hmain := Cover.le_of_excludes_root (symm_entropyF (bAlpha h) (bG h θ))
    (continuous_entropyF_triple (bAlpha h) (continuous_bG h θ)) hex
  intro a ha b hb c hc
  exact hmain a b c ⟨ha.1, ha.2⟩ ⟨hb.1, hb.2⟩ ⟨hc.1, hc.2⟩

/-- The derivative hypothesis of the descent rules, in the form the abstract
lemmas expect. -/
theorem hasDerivAt_phi₁ (hh : 0 < h) :
    ∀ w₁ w₂ w₃ : ℝ, w₁ ≠ 0 →
      HasDerivAt (fun x : ℝ => entropyF (bAlpha h) (bG h θ) x w₂ w₃)
        (PhiD1 h θ w₁ w₂ w₃) w₁ :=
  fun _ w₂ w₃ hw => hasDerivAt_entropyF_1 hh hw w₂ w₃

/-- Leaf rule 5 for the branch objective. -/
theorem excludes_descent (hh : 0 < h) (M : ℝ) {b : Cover.Box} (hlo : 0 < b.lo₁)
    (hsign : ∀ w₁ w₂ w₃ : ℝ, b.mem w₁ w₂ w₃ → 0 < PhiD1 h θ w₁ w₂ w₃) :
    Cover.Excludes (entropyF (bAlpha h) (bG h θ)) M b :=
  Cover.excludes_descent₁ (hasDerivAt_phi₁ hh) hlo hsign

/-- Leaf rule 6 for the branch objective. -/
theorem excludes_ascent (hh : 0 < h) (M : ℝ) {b : Cover.Box} (hlo : 0 < b.lo₁)
    (hhi : b.hi₁ < 1)
    (hsign : ∀ w₁ w₂ w₃ : ℝ, b.mem w₁ w₂ w₃ → PhiD1 h θ w₁ w₂ w₃ < 0) :
    Cover.Excludes (entropyF (bAlpha h) (bG h θ)) M b :=
  Cover.excludes_ascent₁ (hasDerivAt_phi₁ hh) hlo hhi hsign

/-- The derivative hypothesis in the second coordinate. -/
theorem hasDerivAt_phi₂ (hh : 0 < h) :
    ∀ w₁ w₂ w₃ : ℝ, w₂ ≠ 0 →
      HasDerivAt (fun x : ℝ => entropyF (bAlpha h) (bG h θ) w₁ x w₃)
        (PhiD1 h θ w₂ w₁ w₃) w₂ :=
  fun w₁ _ w₃ hw => hasDerivAt_entropyF_2 hh w₁ hw w₃

/-- The derivative hypothesis in the third coordinate. -/
theorem hasDerivAt_phi₃ (hh : 0 < h) :
    ∀ w₁ w₂ w₃ : ℝ, w₃ ≠ 0 →
      HasDerivAt (fun x : ℝ => entropyF (bAlpha h) (bG h θ) w₁ w₂ x)
        (PhiD1 h θ w₃ w₁ w₂) w₃ :=
  fun w₁ w₂ _ hw => hasDerivAt_entropyF_3 hh w₁ w₂ hw

/-- Leaf rule 5 in the second coordinate. -/
theorem excludes_descent₂ (hh : 0 < h) (M : ℝ) {b : Cover.Box} (hlo : 0 < b.lo₂)
    (hsign : ∀ w₁ w₂ w₃ : ℝ, b.mem w₁ w₂ w₃ → 0 < PhiD1 h θ w₂ w₁ w₃) :
    Cover.Excludes (entropyF (bAlpha h) (bG h θ)) M b :=
  Cover.excludes_descent₂ (d := fun w₁ w₂ w₃ => PhiD1 h θ w₂ w₁ w₃)
    (hasDerivAt_phi₂ hh) hlo hsign

/-- Leaf rule 6 in the second coordinate. -/
theorem excludes_ascent₂ (hh : 0 < h) (M : ℝ) {b : Cover.Box} (hlo : 0 < b.lo₂)
    (hhi : b.hi₂ < 1)
    (hsign : ∀ w₁ w₂ w₃ : ℝ, b.mem w₁ w₂ w₃ → PhiD1 h θ w₂ w₁ w₃ < 0) :
    Cover.Excludes (entropyF (bAlpha h) (bG h θ)) M b :=
  Cover.excludes_ascent₂ (d := fun w₁ w₂ w₃ => PhiD1 h θ w₂ w₁ w₃)
    (hasDerivAt_phi₂ hh) hlo hhi hsign

/-- Leaf rule 5 in the third coordinate. -/
theorem excludes_descent₃ (hh : 0 < h) (M : ℝ) {b : Cover.Box} (hlo : 0 < b.lo₃)
    (hsign : ∀ w₁ w₂ w₃ : ℝ, b.mem w₁ w₂ w₃ → 0 < PhiD1 h θ w₃ w₁ w₂) :
    Cover.Excludes (entropyF (bAlpha h) (bG h θ)) M b :=
  Cover.excludes_descent₃ (d := fun w₁ w₂ w₃ => PhiD1 h θ w₃ w₁ w₂)
    (hasDerivAt_phi₃ hh) hlo hsign

/-- Leaf rule 6 in the third coordinate. -/
theorem excludes_ascent₃ (hh : 0 < h) (M : ℝ) {b : Cover.Box} (hlo : 0 < b.lo₃)
    (hhi : b.hi₃ < 1)
    (hsign : ∀ w₁ w₂ w₃ : ℝ, b.mem w₁ w₂ w₃ → PhiD1 h θ w₃ w₁ w₂ < 0) :
    Cover.Excludes (entropyF (bAlpha h) (bG h θ)) M b :=
  Cover.excludes_ascent₃ (d := fun w₁ w₂ w₃ => PhiD1 h θ w₃ w₁ w₂)
    (hasDerivAt_phi₃ hh) hlo hhi hsign

end
end Branch
end TriangleNumerical


/-!
# The spatial interval evaluator

Sections 9.5 and 9.6 of the blueprint.  A *spatial leaf* is a box
`[l₁,u₁] × [l₂,u₂] × [l₃,u₃]` with dyadic endpoints, together with uniform
dyadic enclosures of the four branch parameters `α, Δ, β, C` and of the
auxiliary parameter `θ` on the current slab.  This file turns such data into a
kernel-checkable lower bound for the *gap helper*

```
L_α = Δ/6 · P − β/3 · Σ wᵢ²  +  α w₁w₂w₃,
      P = 2(X₁+X₂+X₃) − (η₁η₂ + η₁η₃ + η₂η₃) − 3
```

of §9.6, which by the stable gap identity (G7) satisfies `L_α ≤ Φ − M₂`
whenever `β ≥ 0`.  Hence a certified *nonnegative* lower bound for `L_α` on a
box gives `M₂ ≤ Φ` there, which is exactly the "direct value" leaf rule of
§10.

The one-dimensional data are shared: everything a side contributes is
determined by the two endpoint enclosures of `H`, which are proved once per
endpoint (§9.5) from the logarithm ladders and then reused by every leaf that
touches that endpoint.  The spatial evaluator itself contains no `exp`, no
square root and no logarithm — only dyadic interval arithmetic.
-/
set_option autoImplicit false
namespace TriangleNumerical
namespace Itv

open TriangleLogCertificate

/-! ### Logarithms of dyadic numbers in `(0,1]` -/

theorem mem_logNegI {c : LogNegCert} (h : logNegOk c = true) :
    (logNegI c).Mem (Real.log (value c.a)) := by
  simp only [logNegOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨ha, hu⟩, hul⟩, hv⟩, hvl⟩ := h
  have hs := scale_pos_real
  have hva : 0 < value c.a := value_pos ha
  have hvu : (1:ℝ) ≤ value c.u := one_le_value (scale_le_of_lowerOk hul)
  have hvv : (1:ℝ) ≤ value c.v := one_le_value (scale_le_of_upperOk hvl)
  have hupos : 0 < value c.u := lt_of_lt_of_le zero_lt_one hvu
  have hvpos : 0 < value c.v := lt_of_lt_of_le zero_lt_one hvv
  -- the two product conditions
  have hprod : value c.u * value c.a ≤ 1 := by
    have h' : ((c.u : ℝ)) * (c.a : ℝ) ≤ (scale : ℝ) * (scale : ℝ) := by exact_mod_cast hu
    simp only [value]
    rw [div_mul_div_comm, div_le_one (by positivity)]
    linarith
  have hprod' : (1:ℝ) ≤ value c.v * value c.a := by
    have h' : ((scale : ℝ)) * (scale : ℝ) ≤ (c.v : ℝ) * (c.a : ℝ) := by exact_mod_cast hv
    simp only [value]
    rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
    linarith
  have hupper : Real.log (value c.a) ≤ -Real.log (value c.u) := by
    have hml : Real.log (value c.u) + Real.log (value c.a) ≤ 0 := by
      rw [← Real.log_mul (ne_of_gt hupos) (ne_of_gt hva)]
      simpa using Real.log_le_log (by positivity) hprod
    linarith
  have hlower : -Real.log (value c.v) ≤ Real.log (value c.a) := by
    have hml : (0:ℝ) ≤ Real.log (value c.v) + Real.log (value c.a) := by
      rw [← Real.log_mul (ne_of_gt hvpos) (ne_of_gt hva)]
      simpa using Real.log_le_log (by norm_num) hprod'
    linarith
  -- the two ladder bounds
  have hlad1 : value (logLowerI c.u c.ul).lo ≤ Real.log (value c.u) := by
    have hm := mem_mul (mem_pow2I c.ul.length) (mem_seedLowerI (scale_le_lastOf hul))
    exact le_trans hm.1 (lowerOk_sound c.ul c.u hul)
  have hlad2 : Real.log (value c.v) ≤ value (logUpperI c.v c.vl).hi := by
    have hm := mem_mul (mem_pow2I c.vl.length) (mem_seedUpperI (scale_le_lastOf_upper hvl))
    exact le_trans (upperOk_sound c.vl c.v hvl) hm.2
  constructor
  · show value (-(logUpperI c.v c.vl).hi) ≤ _
    rw [value_neg']
    linarith
  · show _ ≤ value (-(logLowerI c.u c.ul).lo)
    rw [value_neg']
    linarith

/-! ### Endpoint enclosures for the entropy function -/

theorem mem_HptI {c : LogNegCert} (h : logNegOk c = true) :
    (HptI c).Mem (H (value c.a)) := by
  have hlog := mem_logNegI h
  have hm := mem_add (mem_sub mem_oneI (mem_pt c.a)) (mem_mul (mem_pt c.a) hlog)
  have heq : (1 : ℝ) - value c.a + value c.a * Real.log (value c.a) = H (value c.a) := rfl
  rwa [heq] at hm

/-- `H 0 = 1`. -/
theorem mem_HzeroI : oneI.Mem (H 0) := by
  have : H 0 = 1 := by norm_num [H]
  rw [this]
  exact mem_oneI

/-! ### Small integer intervals -/

theorem mem_intI (n : Int) : (intI n).Mem (n : ℝ) := by
  have h := mem_pt (n * scale)
  have heq : value (n * scale) = (n : ℝ) := by
    simp only [value]
    push_cast
    exact mul_div_cancel_right₀ _ (ne_of_gt scale_pos_real)
  rwa [heq] at h

end Itv

namespace Branch
noncomputable section

open Real Itv

variable {h θ : ℝ}

/-! ### The gap helper of §9.6 -/

/-- The symmetric polynomial `P` of the stable gap identity. -/
def gapP (h θ w₁ w₂ w₃ : ℝ) : ℝ :=
  2 * (bX h w₁ + bX h w₂ + bX h w₃)
    - (etaT θ (bX h w₁) * etaT θ (bX h w₂) + etaT θ (bX h w₁) * etaT θ (bX h w₃)
      + etaT θ (bX h w₂) * etaT θ (bX h w₃)) - 3

/-- The finite-slab lower-bound helper `L_α` of §9.6. -/
def Lalpha (h θ w₁ w₂ w₃ : ℝ) : ℝ :=
  bDelta h * (1 / 6) * gapP h θ w₁ w₂ w₃
    + bAlpha h * w₁ * w₂ * w₃
    - bBeta h * (1 / 3) * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2)

/-- `L_α ≤ Φ - M₂`: the omitted term `β r²/3` is nonnegative. -/
theorem Lalpha_le_gap (hh : 9 ≤ h) (w₁ w₂ w₃ : ℝ) :
    Lalpha h θ w₁ w₂ w₃ ≤ entropyF (bAlpha h) (bG h θ) w₁ w₂ w₃ - bM2 h := by
  have hhpos : (0:ℝ) < h := by linarith
  have hid := gap_identity (h := h) (θ := θ) hhpos w₁ w₂ w₃
  have hbeta := (bBeta_pos hh).le
  have hr : 0 ≤ bBeta h * (br h) ^ 2 / 3 := by positivity
  rw [hid]
  simp only [Lalpha, gapP]
  linarith

end
end Branch

namespace Itv

open Branch

/-! ### The interval evaluator -/

theorem mem_etaI {IT IX : DI} {t x : ℝ} (hT : IT.Mem t) (hX : IX.Mem x) :
    (etaI IT IX).Mem (etaT t x) := by
  have hm := mem_add
    (mem_sub (mem_sub (mem_mul (mem_intI 3) hX) (mem_pow hX 2)) mem_oneI)
    (mem_mul (mem_mul hT hX) (mem_pow (mem_sub mem_oneI hX) 2))
  have heq : ((3:Int) : ℝ) * x - x ^ 2 - 1 + t * x * (1 - x) ^ 2 = etaT t x := by
    simp only [etaT]
    push_cast
    ring
  rwa [heq] at hm

/-- Soundness of a side: every real weight in the side interval has its `H`,
`D` and `X` values inside the computed intervals. -/
theorem Side.sound (s : Side) {IB IC IDl : DI} {h w : ℝ}
    (hHlo : s.IHlo.Mem (H (value s.lo))) (hHhi : s.IHhi.Mem (H (value s.hi)))
    (h0 : 0 ≤ value s.lo) (h1 : value s.hi ≤ 1)
    (hB : IB.Mem (bBeta h)) (hC : IC.Mem (bC h)) (hD : IDl.Mem (bDelta h))
    (hDpos : 0 < IDl.lo)
    (hw1 : value s.lo ≤ w) (hw2 : w ≤ value s.hi) :
    s.Iw.Mem w ∧ s.IH.Mem (H w) ∧ (s.ID IB IC).Mem (bD h w) ∧
      (s.IX IB IC IDl).Mem (bX h w) := by
  have hw : s.Iw.Mem w := ⟨hw1, hw2⟩
  have hmemlo : value s.lo ∈ Set.Icc (0:ℝ) 1 := ⟨h0, le_trans hw1 (le_trans hw2 h1)⟩
  have hmemhi : value s.hi ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans h0 (le_trans hw1 hw2), h1⟩
  have hmemw : w ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans h0 hw1, le_trans hw2 h1⟩
  have hHw : s.IH.Mem (H w) := by
    constructor
    · exact le_trans hHhi.1 (H_antitoneOn hmemw hmemhi hw2)
    · exact le_trans (H_antitoneOn hmemlo hmemw hw1) hHlo.2
  have hDw : (s.ID IB IC).Mem (bD h w) := by
    have hm := mem_sub (mem_add hHw (mem_mul hB (mem_pow hw 2))) hC
    have heq : H w + bBeta h * w ^ 2 - bC h = bD h w := rfl
    rwa [heq] at hm
  exact ⟨hw, hHw, hDw, mem_div hDw hD hDpos⟩

theorem mem_inv_intI {n : Int} (hn : 0 < n) : (inv (intI n)).Mem (1 / (n : ℝ)) := by
  have hlo : 0 < (intI n).lo := by
    have : (0:Int) < n * scale := mul_pos hn scale_pos
    simpa [intI, pt] using this
  have hm := mem_inv (mem_intI n) hlo
  have heq : ((n : ℝ))⁻¹ = 1 / (n : ℝ) := by rw [one_div]
  rwa [heq] at hm

/-- Soundness of the leaf evaluator. -/
theorem mem_leafI {s₁ s₂ s₃ : Side} {IA IDl IB IC IT : DI} {h θ w₁ w₂ w₃ : ℝ}
    (hH₁lo : s₁.IHlo.Mem (H (value s₁.lo))) (hH₁hi : s₁.IHhi.Mem (H (value s₁.hi)))
    (hH₂lo : s₂.IHlo.Mem (H (value s₂.lo))) (hH₂hi : s₂.IHhi.Mem (H (value s₂.hi)))
    (hH₃lo : s₃.IHlo.Mem (H (value s₃.lo))) (hH₃hi : s₃.IHhi.Mem (H (value s₃.hi)))
    (h0₁ : 0 ≤ value s₁.lo) (h1₁ : value s₁.hi ≤ 1)
    (h0₂ : 0 ≤ value s₂.lo) (h1₂ : value s₂.hi ≤ 1)
    (h0₃ : 0 ≤ value s₃.lo) (h1₃ : value s₃.hi ≤ 1)
    (hA : IA.Mem (bAlpha h)) (hD : IDl.Mem (bDelta h)) (hB : IB.Mem (bBeta h))
    (hC : IC.Mem (bC h)) (hT : IT.Mem θ) (hDpos : 0 < IDl.lo)
    (hw₁ : value s₁.lo ≤ w₁) (hw₁' : w₁ ≤ value s₁.hi)
    (hw₂ : value s₂.lo ≤ w₂) (hw₂' : w₂ ≤ value s₂.hi)
    (hw₃ : value s₃.lo ≤ w₃) (hw₃' : w₃ ≤ value s₃.hi) :
    (leafI s₁ s₂ s₃ IA IDl IB IC IT).Mem (Lalpha h θ w₁ w₂ w₃) := by
  obtain ⟨hu₁, -, -, hX₁⟩ := s₁.sound hH₁lo hH₁hi h0₁ h1₁ hB hC hD hDpos hw₁ hw₁'
  obtain ⟨hu₂, -, -, hX₂⟩ := s₂.sound hH₂lo hH₂hi h0₂ h1₂ hB hC hD hDpos hw₂ hw₂'
  obtain ⟨hu₃, -, -, hX₃⟩ := s₃.sound hH₃lo hH₃hi h0₃ h1₃ hB hC hD hDpos hw₃ hw₃'
  have hE₁ := mem_etaI hT hX₁
  have hE₂ := mem_etaI hT hX₂
  have hE₃ := mem_etaI hT hX₃
  have hP := mem_sub (mem_sub (mem_mul (mem_intI 2) (mem_add (mem_add hX₁ hX₂) hX₃))
      (mem_add (mem_add (mem_mul hE₁ hE₂) (mem_mul hE₁ hE₃)) (mem_mul hE₂ hE₃)))
    (mem_intI 3)
  have hPeq : ((2:Int) : ℝ) * (bX h w₁ + bX h w₂ + bX h w₃)
      - (etaT θ (bX h w₁) * etaT θ (bX h w₂) + etaT θ (bX h w₁) * etaT θ (bX h w₃)
        + etaT θ (bX h w₂) * etaT θ (bX h w₃)) - ((3:Int) : ℝ)
      = gapP h θ w₁ w₂ w₃ := by
    simp only [gapP]
    push_cast
    ring
  rw [hPeq] at hP
  have h6 := mem_inv_intI (n := 6) (by norm_num)
  have h3 := mem_inv_intI (n := 3) (by norm_num)
  have hm := mem_sub (mem_add (mem_mul (mem_mul hD h6) hP)
      (mem_mul (mem_mul (mem_mul hA hu₁) hu₂) hu₃))
    (mem_mul (mem_mul hB h3)
      (mem_add (mem_add (mem_pow hu₁ 2) (mem_pow hu₂ 2)) (mem_pow hu₃ 2)))
  have heq : bDelta h * (1 / ((6:Int) : ℝ)) * gapP h θ w₁ w₂ w₃
      + bAlpha h * w₁ * w₂ * w₃
      - bBeta h * (1 / ((3:Int) : ℝ)) * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2)
      = Lalpha h θ w₁ w₂ w₃ := by
    simp only [Lalpha]
    push_cast
    ring
  rw [heq] at hm
  exact hm

/-- The "direct value" leaf rule of §10: a nonnegative certified lower bound
for the helper `L_α` on the box gives `M₂ ≤ Φ` there. -/
theorem leaf_value_rule {s₁ s₂ s₃ : Side} {IA IDl IB IC IT : DI} {h θ w₁ w₂ w₃ : ℝ}
    (hh : 9 ≤ h)
    (hH₁lo : s₁.IHlo.Mem (H (value s₁.lo))) (hH₁hi : s₁.IHhi.Mem (H (value s₁.hi)))
    (hH₂lo : s₂.IHlo.Mem (H (value s₂.lo))) (hH₂hi : s₂.IHhi.Mem (H (value s₂.hi)))
    (hH₃lo : s₃.IHlo.Mem (H (value s₃.lo))) (hH₃hi : s₃.IHhi.Mem (H (value s₃.hi)))
    (h0₁ : 0 ≤ value s₁.lo) (h1₁ : value s₁.hi ≤ 1)
    (h0₂ : 0 ≤ value s₂.lo) (h1₂ : value s₂.hi ≤ 1)
    (h0₃ : 0 ≤ value s₃.lo) (h1₃ : value s₃.hi ≤ 1)
    (hA : IA.Mem (bAlpha h)) (hD : IDl.Mem (bDelta h)) (hB : IB.Mem (bBeta h))
    (hC : IC.Mem (bC h)) (hT : IT.Mem θ) (hDpos : 0 < IDl.lo)
    (hgap : 0 ≤ (leafI s₁ s₂ s₃ IA IDl IB IC IT).lo)
    (hw₁ : value s₁.lo ≤ w₁) (hw₁' : w₁ ≤ value s₁.hi)
    (hw₂ : value s₂.lo ≤ w₂) (hw₂' : w₂ ≤ value s₂.hi)
    (hw₃ : value s₃.lo ≤ w₃) (hw₃' : w₃ ≤ value s₃.hi) :
    bM2 h ≤ entropyF (bAlpha h) (bG h θ) w₁ w₂ w₃ := by
  have hm := mem_leafI hH₁lo hH₁hi hH₂lo hH₂hi hH₃lo hH₃hi h0₁ h1₁ h0₂ h1₂ h0₃ h1₃
    hA hD hB hC hT hDpos hw₁ hw₁' hw₂ hw₂' hw₃ hw₃'
  have hnn : (0:ℝ) ≤ value (leafI s₁ s₂ s₃ IA IDl IB IC IT).lo := by
    have hs := scale_pos_real
    have h' : (0:ℝ) ≤ ((leafI s₁ s₂ s₃ IA IDl IB IC IT).lo : ℝ) := by exact_mod_cast hgap
    simp only [value]
    positivity
  have h1 : 0 ≤ Lalpha h θ w₁ w₂ w₃ := le_trans hnn hm.1
  have h2 := Lalpha_le_gap (h := h) (θ := θ) hh w₁ w₂ w₃
  linarith

/-! ### The derivative evaluator and the feasible-descent rules -/

theorem mem_etaDI {IT IX : DI} {t x : ℝ} (hT : IT.Mem t) (hX : IX.Mem x) :
    (etaDI IT IX).Mem (etaD t x) := by
  have hm := mem_add (mem_sub (mem_intI 3) (mem_mul (mem_intI 2) hX))
    (mem_mul hT (mem_add (mem_sub mem_oneI (mem_mul (mem_intI 4) hX))
      (mem_mul (mem_intI 3) (mem_pow hX 2))))
  have heq : ((3:Int) : ℝ) - ((2:Int) : ℝ) * x
      + t * (1 - ((4:Int) : ℝ) * x + ((3:Int) : ℝ) * x ^ 2) = etaD t x := by
    simp only [etaD]
    push_cast
    ring
  rwa [heq] at hm

/-- Soundness of the logarithm and `D'` enclosures on a side with a positive
lower endpoint. -/
theorem Side.sound_log (s : Side) {IB : DI} {h w : ℝ}
    (hLlo : s.ILlo.Mem (Real.log (value s.lo))) (hLhi : s.ILhi.Mem (Real.log (value s.hi)))
    (h0 : 0 < value s.lo) (hB : IB.Mem (bBeta h))
    (hw1 : value s.lo ≤ w) (hw2 : w ≤ value s.hi) :
    s.IL.Mem (Real.log w) ∧ (s.IDd IB).Mem (bDd h w) := by
  have hwpos : 0 < w := lt_of_lt_of_le h0 hw1
  have hlog : s.IL.Mem (Real.log w) := by
    constructor
    · exact le_trans hLlo.1 (Real.log_le_log h0 hw1)
    · exact le_trans (Real.log_le_log hwpos hw2) hLhi.2
  refine ⟨hlog, ?_⟩
  have hm := mem_add hlog (mem_mul (mem_mul (mem_intI 2) hB) (⟨hw1, hw2⟩ : s.Iw.Mem w))
  have heq : Real.log w + ((2:Int) : ℝ) * bBeta h * w = bDd h w := by
    simp only [bDd]
    push_cast
    ring
  rwa [heq] at hm

/-- Soundness of the derivative evaluator. -/
theorem mem_derivI {s₁ s₂ s₃ : Side} {IA IDl IB IC IT : DI} {h θ w₁ w₂ w₃ : ℝ}
    (hH₁lo : s₁.IHlo.Mem (H (value s₁.lo))) (hH₁hi : s₁.IHhi.Mem (H (value s₁.hi)))
    (hH₂lo : s₂.IHlo.Mem (H (value s₂.lo))) (hH₂hi : s₂.IHhi.Mem (H (value s₂.hi)))
    (hH₃lo : s₃.IHlo.Mem (H (value s₃.lo))) (hH₃hi : s₃.IHhi.Mem (H (value s₃.hi)))
    (hL₁lo : s₁.ILlo.Mem (Real.log (value s₁.lo)))
    (hL₁hi : s₁.ILhi.Mem (Real.log (value s₁.hi)))
    (hpos₁ : 0 < value s₁.lo)
    (h0₁ : 0 ≤ value s₁.lo) (h1₁ : value s₁.hi ≤ 1)
    (h0₂ : 0 ≤ value s₂.lo) (h1₂ : value s₂.hi ≤ 1)
    (h0₃ : 0 ≤ value s₃.lo) (h1₃ : value s₃.hi ≤ 1)
    (hA : IA.Mem (bAlpha h)) (hD : IDl.Mem (bDelta h)) (hB : IB.Mem (bBeta h))
    (hC : IC.Mem (bC h)) (hT : IT.Mem θ) (hDpos : 0 < IDl.lo)
    (hw₁ : value s₁.lo ≤ w₁) (hw₁' : w₁ ≤ value s₁.hi)
    (hw₂ : value s₂.lo ≤ w₂) (hw₂' : w₂ ≤ value s₂.hi)
    (hw₃ : value s₃.lo ≤ w₃) (hw₃' : w₃ ≤ value s₃.hi) :
    (derivI s₁ s₂ s₃ IA IDl IB IC IT).Mem (PhiD1 h θ w₁ w₂ w₃) := by
  obtain ⟨-, -, -, hX₁⟩ := s₁.sound hH₁lo hH₁hi h0₁ h1₁ hB hC hD hDpos hw₁ hw₁'
  obtain ⟨hu₂, -, -, hX₂⟩ := s₂.sound hH₂lo hH₂hi h0₂ h1₂ hB hC hD hDpos hw₂ hw₂'
  obtain ⟨hu₃, -, -, hX₃⟩ := s₃.sound hH₃lo hH₃hi h0₃ h1₃ hB hC hD hDpos hw₃ hw₃'
  obtain ⟨hlog, hDd⟩ := s₁.sound_log hL₁lo hL₁hi hpos₁ hB hw₁ hw₁'
  have h3 := mem_inv_intI (n := 3) (by norm_num)
  have h6 := mem_inv_intI (n := 6) (by norm_num)
  have hm := mem_sub (mem_add (mem_mul hlog h3) (mem_mul (mem_mul hA hu₂) hu₃))
    (mem_mul (mem_mul (mem_mul (mem_etaDI hT hX₁) hDd) h6)
      (mem_add (mem_etaI hT hX₂) (mem_etaI hT hX₃)))
  have heq : Real.log w₁ * (1 / ((3:Int) : ℝ)) + bAlpha h * w₂ * w₃
      - etaD θ (bX h w₁) * bDd h w₁ * (1 / ((6:Int) : ℝ))
        * (etaT θ (bX h w₂) + etaT θ (bX h w₃))
      = PhiD1 h θ w₁ w₂ w₃ := by
    simp only [PhiD1]
    push_cast
    ring
  rwa [heq] at hm

/-- The "decrease coordinate" leaf rule (rule 5 of §10) in the first
coordinate: a certified positive enclosure of `∂₁Φ` on the box. -/
theorem leaf_descent_rule {s₁ s₂ s₃ : Side} {IA IDl IB IC IT : DI} {h θ w₁ w₂ w₃ : ℝ}
    (hH₁lo : s₁.IHlo.Mem (H (value s₁.lo))) (hH₁hi : s₁.IHhi.Mem (H (value s₁.hi)))
    (hH₂lo : s₂.IHlo.Mem (H (value s₂.lo))) (hH₂hi : s₂.IHhi.Mem (H (value s₂.hi)))
    (hH₃lo : s₃.IHlo.Mem (H (value s₃.lo))) (hH₃hi : s₃.IHhi.Mem (H (value s₃.hi)))
    (hL₁lo : s₁.ILlo.Mem (Real.log (value s₁.lo)))
    (hL₁hi : s₁.ILhi.Mem (Real.log (value s₁.hi)))
    (hpos₁ : 0 < value s₁.lo)
    (h1₁ : value s₁.hi ≤ 1) (h0₂ : 0 ≤ value s₂.lo) (h1₂ : value s₂.hi ≤ 1)
    (h0₃ : 0 ≤ value s₃.lo) (h1₃ : value s₃.hi ≤ 1)
    (hA : IA.Mem (bAlpha h)) (hD : IDl.Mem (bDelta h)) (hB : IB.Mem (bBeta h))
    (hC : IC.Mem (bC h)) (hT : IT.Mem θ) (hDpos : 0 < IDl.lo)
    (hsign : 0 < (derivI s₁ s₂ s₃ IA IDl IB IC IT).lo)
    (hw₁ : value s₁.lo ≤ w₁) (hw₁' : w₁ ≤ value s₁.hi)
    (hw₂ : value s₂.lo ≤ w₂) (hw₂' : w₂ ≤ value s₂.hi)
    (hw₃ : value s₃.lo ≤ w₃) (hw₃' : w₃ ≤ value s₃.hi) :
    0 < PhiD1 h θ w₁ w₂ w₃ := by
  have hm := mem_derivI hH₁lo hH₁hi hH₂lo hH₂hi hH₃lo hH₃hi hL₁lo hL₁hi hpos₁
    hpos₁.le h1₁ h0₂ h1₂ h0₃ h1₃ hA hD hB hC hT hDpos hw₁ hw₁' hw₂ hw₂' hw₃ hw₃'
  exact pos_of_mem hm hsign

/-- The "increase coordinate" leaf rule (rule 6 of §10) in the first
coordinate: a certified negative enclosure of `∂₁Φ` on the box. -/
theorem leaf_ascent_rule {s₁ s₂ s₃ : Side} {IA IDl IB IC IT : DI} {h θ w₁ w₂ w₃ : ℝ}
    (hH₁lo : s₁.IHlo.Mem (H (value s₁.lo))) (hH₁hi : s₁.IHhi.Mem (H (value s₁.hi)))
    (hH₂lo : s₂.IHlo.Mem (H (value s₂.lo))) (hH₂hi : s₂.IHhi.Mem (H (value s₂.hi)))
    (hH₃lo : s₃.IHlo.Mem (H (value s₃.lo))) (hH₃hi : s₃.IHhi.Mem (H (value s₃.hi)))
    (hL₁lo : s₁.ILlo.Mem (Real.log (value s₁.lo)))
    (hL₁hi : s₁.ILhi.Mem (Real.log (value s₁.hi)))
    (hpos₁ : 0 < value s₁.lo)
    (h1₁ : value s₁.hi ≤ 1) (h0₂ : 0 ≤ value s₂.lo) (h1₂ : value s₂.hi ≤ 1)
    (h0₃ : 0 ≤ value s₃.lo) (h1₃ : value s₃.hi ≤ 1)
    (hA : IA.Mem (bAlpha h)) (hD : IDl.Mem (bDelta h)) (hB : IB.Mem (bBeta h))
    (hC : IC.Mem (bC h)) (hT : IT.Mem θ) (hDpos : 0 < IDl.lo)
    (hsign : (derivI s₁ s₂ s₃ IA IDl IB IC IT).hi < 0)
    (hw₁ : value s₁.lo ≤ w₁) (hw₁' : w₁ ≤ value s₁.hi)
    (hw₂ : value s₂.lo ≤ w₂) (hw₂' : w₂ ≤ value s₂.hi)
    (hw₃ : value s₃.lo ≤ w₃) (hw₃' : w₃ ≤ value s₃.hi) :
    PhiD1 h θ w₁ w₂ w₃ < 0 := by
  have hm := mem_derivI hH₁lo hH₁hi hH₂lo hH₂hi hH₃lo hH₃hi hL₁lo hL₁hi hpos₁
    hpos₁.le h1₁ h0₂ h1₂ h0₃ h1₃ hA hD hB hC hT hDpos hw₁ hw₁' hw₂ hw₂' hw₃ hw₃'
  exact neg_of_mem hm hsign

end Itv
end TriangleNumerical
