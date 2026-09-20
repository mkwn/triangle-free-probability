import TriangleNumerical.ReferenceSign
import TriangleNumerical.CubicCover
import TriangleNumerical.SlabA0Cover
import TriangleNumerical.SlabA1Cover
import TriangleNumerical.SlabA2Cover
import TriangleNumerical.SlabA3Cover
import TriangleNumerical.SlabA4Cover
import TriangleNumerical.SlabA5Cover
import TriangleNumerical.SlabA6Cover
import TriangleNumerical.SlabA7Cover
import TriangleNumerical.SlabA8Cover
import TriangleNumerical.TailCover

/-!
# Assembly of the entropy certificate

Section 13 of the blueprint.  The two numerical obligations

* `reference_cube_bound`   (blueprint §5–§10 and §12 (R0)/(R1)), and
* `branch_cube_bound`      (blueprint §5–§11)

are discharged here from the kernel-checked covers: the cubic transition slab
`[9.39, 9.40625]`, the nine finite sub-slabs covering `[9.40625, 15]`, and the
tail `h ≥ 15`.
-/
set_option autoImplicit false
namespace TriangleNumerical
noncomputable section

open Real

/-! ## The two remaining numerical obligations -/

/-- OBLIGATION 1 (blueprint §5–§10 and §12 (R0)/(R1)).
The reference certificate: at the reference parameter `α₀ = A(9.39)` there is a
continuous `G` whose cube bound is the constant competitor value `M₁(α₀)`. -/
theorem hRef_mem_cubic :
    Itv.value (Itv.pcC).hlo ≤ hRef ∧ hRef ≤ Itv.value (Itv.pcC).hhi := by
  constructor
  · have := Itv.value_le_rat (n := (Itv.pcC).hlo) (p := 939) (q := 100)
      (by norm_num) (by decide)
    norm_num at this
    simpa [hRef] using this
  · have := Itv.rat_le_value (n := (Itv.pcC).hhi) (p := 939) (q := 100)
      (by norm_num) (by decide)
    norm_num at this
    simpa [hRef] using this

theorem reference_cube_bound :
    ∃ G : ℝ → ℝ, ContinuousOn G unitInterval ∧
      ∀ a ∈ unitInterval, ∀ b ∈ unitInterval, ∀ c ∈ unitInterval,
        M1 alphaRef sRef ≤ entropyF alphaRef G a b c := by
  obtain ⟨hs, -, hroot⟩ := sRef_spec
  obtain ⟨h1, h2⟩ := hRef_mem_cubic
  have hroot' : rootResidual (Branch.bAlpha hRef) sRef = 0 := hroot
  have hbound := Itv.boundC h1 h2 hs hroot'
  have hmin : min (M1 (Branch.bAlpha hRef) sRef) (Branch.bM2 hRef)
      = M1 alphaRef sRef := min_eq_left reference_sign
  rw [hmin] at hbound
  exact ⟨Branch.bG hRef (Itv.thetaC hRef sRef),
    (Branch.continuous_bG hRef _).continuousOn, hbound⟩

/-- OBLIGATION 2 (blueprint §5–§11).
The branch certificate: for every `h ≥ h₀` there is a continuous `G` whose cube
bound is the smaller of the two competitor values at `α = A(h)`. -/
theorem branch_cube_bound (h : ℝ) (hh : hRef ≤ h) :
    ∃ G : ℝ → ℝ, ContinuousOn G unitInterval ∧
      ∀ a ∈ unitInterval, ∀ b ∈ unitInterval, ∀ c ∈ unitInterval,
        min (M1 (Branch.bAlpha h) (sAt (le_of_lt (Branch.bAlpha_pos
              (lt_of_lt_of_le hRef_pos hh))))) (Branch.bM2 h)
          ≤ entropyF (Branch.bAlpha h) G a b c := by
  have hhpos : 0 < h := lt_of_lt_of_le hRef_pos hh
  have hαpos : 0 < Branch.bAlpha h := Branch.bAlpha_pos hhpos
  set s : ℝ := sAt (le_of_lt hαpos) with hsdef
  obtain ⟨hs, -, hroot⟩ := sAt_spec (le_of_lt hαpos)
  -- every slab bound with target `M₂` gives the required `min` bound
  have fin : (∀ a ∈ unitInterval, ∀ b ∈ unitInterval, ∀ c ∈ unitInterval,
        Branch.bM2 h ≤ entropyF (Branch.bAlpha h) (Branch.bG h 0) a b c) →
      ∃ G : ℝ → ℝ, ContinuousOn G unitInterval ∧
        ∀ a ∈ unitInterval, ∀ b ∈ unitInterval, ∀ c ∈ unitInterval,
          min (M1 (Branch.bAlpha h) s) (Branch.bM2 h)
            ≤ entropyF (Branch.bAlpha h) G a b c := by
    intro hb
    exact ⟨Branch.bG h 0, (Branch.continuous_bG h 0).continuousOn,
      fun a ha b hb' c hc => le_trans (min_le_right _ _) (hb a ha b hb' c hc)⟩
  have hlo : Itv.value (Itv.pcC).hlo ≤ h := le_trans hRef_mem_cubic.1 hh
  rcases le_or_gt h (Itv.value (Itv.pcC).hhi) with hk | hk
  · exact ⟨Branch.bG h (Itv.thetaC h s), (Branch.continuous_bG h _).continuousOn,
      Itv.boundC hlo hk hs hroot⟩
  replace hlo : Itv.value (Itv.pc0).hlo ≤ h := le_of_lt hk
  rcases le_or_gt h (Itv.value (Itv.pc0).hhi) with hk | hk
  · exact fin (Itv.bound0 (by exact hlo) hk)
  replace hlo : Itv.value (Itv.pc1).hlo ≤ h := le_of_lt hk
  rcases le_or_gt h (Itv.value (Itv.pc1).hhi) with hk | hk
  · exact fin (Itv.bound1 (by exact hlo) hk)
  replace hlo : Itv.value (Itv.pc2).hlo ≤ h := le_of_lt hk
  rcases le_or_gt h (Itv.value (Itv.pc2).hhi) with hk | hk
  · exact fin (Itv.bound2 (by exact hlo) hk)
  replace hlo : Itv.value (Itv.pc3).hlo ≤ h := le_of_lt hk
  rcases le_or_gt h (Itv.value (Itv.pc3).hhi) with hk | hk
  · exact fin (Itv.bound3 (by exact hlo) hk)
  replace hlo : Itv.value (Itv.pc4).hlo ≤ h := le_of_lt hk
  rcases le_or_gt h (Itv.value (Itv.pc4).hhi) with hk | hk
  · exact fin (Itv.bound4 (by exact hlo) hk)
  replace hlo : Itv.value (Itv.pc5).hlo ≤ h := le_of_lt hk
  rcases le_or_gt h (Itv.value (Itv.pc5).hhi) with hk | hk
  · exact fin (Itv.bound5 (by exact hlo) hk)
  replace hlo : Itv.value (Itv.pc6).hlo ≤ h := le_of_lt hk
  rcases le_or_gt h (Itv.value (Itv.pc6).hhi) with hk | hk
  · exact fin (Itv.bound6 (by exact hlo) hk)
  replace hlo : Itv.value (Itv.pc7).hlo ≤ h := le_of_lt hk
  rcases le_or_gt h (Itv.value (Itv.pc7).hhi) with hk | hk
  · exact fin (Itv.bound7 (by exact hlo) hk)
  replace hlo : Itv.value (Itv.pc8).hlo ≤ h := le_of_lt hk
  rcases le_or_gt h (Itv.value (Itv.pc8).hhi) with hk | hk
  · exact fin (Itv.bound8 (by exact hlo) hk)
  -- the tail: `pc8.hhi` is exactly `15`
  have h15 : (15:ℝ) ≤ Itv.value (Itv.pc8).hhi := by
    have := Itv.rat_le_value (n := (Itv.pc8).hhi) (p := 15) (q := 1)
      (by norm_num) (by decide)
    norm_num at this
    exact this
  have htail : (15:ℝ) ≤ h := le_of_lt (lt_of_le_of_lt h15 hk)
  exact ⟨Branch.bG h 0, (Branch.continuous_bG h 0).continuousOn,
    fun a ha b hb c hc => le_trans (min_le_right _ _)
      (Itv.boundT htail a ha b hb c hc)⟩

/-! ## Assembly -/

/-- The certificate at every parameter at or below the reference. -/
theorem entropyCertificateAt_le_ref {α : ℝ} (hα : 0 ≤ α) (hle : α ≤ alphaRef) :
    EntropyCertificateAt α := by
  obtain ⟨G, hGcont, hGbound⟩ := reference_cube_bound
  obtain ⟨hs₀, _, hroot₀⟩ := sRef_spec
  exact entropyCertificateAt_of_reference alphaRef_pos hs₀ hroot₀ G hGcont hGbound hα hle

/-- The certificate at every parameter on the branch. -/
theorem entropyCertificateAt_branch {h : ℝ} (hh : hRef ≤ h) :
    EntropyCertificateAt (Branch.bAlpha h) := by
  have hhpos : 0 < h := lt_of_lt_of_le hRef_pos hh
  have hαpos : 0 < Branch.bAlpha h := Branch.bAlpha_pos hhpos
  obtain ⟨G, hGcont, hGbound⟩ := branch_cube_bound h hh
  obtain ⟨hs, hs1, hroot⟩ := sAt_spec (le_of_lt hαpos)
  set M : ℝ := min (M1 (Branch.bAlpha h) (sAt (le_of_lt hαpos))) (Branch.bM2 h) with hM
  refine ⟨M, G, ?_, hGcont, hGbound⟩
  rcases min_cases (M1 (Branch.bAlpha h) (sAt (le_of_lt hαpos))) (Branch.bM2 h) with
    ⟨heq, _⟩ | ⟨heq, _⟩
  · -- the constant competitor attains it
    refine isTwoBlockMinimum_of_cube_bound hGbound
      (r := sAt (le_of_lt hαpos)) (t := sAt (le_of_lt hαpos))
      ⟨hs.le, hs1⟩ ⟨hs.le, hs1⟩ ?_
    rw [hM, heq]
    exact twoBlock_at_constant hroot
  · -- the branch pair attains it
    have hr : Branch.br h ∈ unitInterval :=
      ⟨(Branch.br_pos h).le, le_of_lt (lt_trans (Branch.br_lt_bt hhpos)
        (Branch.bt_lt_one hhpos))⟩
    have ht : Branch.bt h ∈ unitInterval :=
      ⟨(Branch.bt_pos h).le, (Branch.bt_lt_one hhpos).le⟩
    refine isTwoBlockMinimum_of_cube_bound hGbound
      (r := Branch.br h) (t := Branch.bt h) hr ht ?_
    rw [hM, heq]
    exact Branch.twoBlock_at_branch hhpos

/-- The entropy-coordinate certificate for every nonnegative parameter. -/
theorem entropy_certificate : EntropyCertificateProposition := by
  intro α hα
  rcases le_or_gt α alphaRef with hle | hgt
  · exact entropyCertificateAt_le_ref hα hle
  · obtain ⟨h, hh, hval⟩ := Branch.exists_branch_param hRef_pos (le_of_lt hgt)
    have := entropyCertificateAt_branch hh
    rwa [hval] at this

end
end TriangleNumerical
