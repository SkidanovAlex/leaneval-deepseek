import Mathlib
import Submission.Work.EKLComp.LeafAux
import Submission.Work.EKLComp.measurable_kernel_atom

/-!
# Positivity of the weight `x ↦ condExpKernel ν 𝔪.m x (atom 𝔫.m x)`

Pisa Lemma 5.18 / EKL 6.21.  Let `ν` be a finite measure on `X₃`, `𝔪 ⊆ 𝔫` two countably generated
sub-σ-algebras of the Borel σ-algebra, and `Y` a measurable set whose `𝔪`-atoms are covered by
countably many sets of the form `[y]_𝔪 ∩ [y]_𝔫` (`y ∈ Y`).  Then for `ν`-almost every `x ∈ Y` the
`𝔪`-conditional measure of `x` gives *positive* mass to the `𝔫`-atom of `x`.

This is the countable-refinement argument: the bad set `Z = {x ∈ Y : κ_x([x]_𝔫) = 0}` is a union
of `𝔫`-atoms, hence the weight is constant on it; covering `[x]_𝔪 ∩ Y` by the countably many
pieces `[y]_𝔪 ∩ [y]_𝔫` (each of which is entirely inside `Z` or disjoint from it) shows that
`κ_x(Z) = 0` for every `x` whose `𝔪`-conditional measure is carried by `[x]_𝔪`, and the
disintegration identity `ν Z = ∫⁻ x, κ_x Z ∂ν` converts this into `ν Z = 0`.
-/

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLComp

open Work.EKLContract

/-- **Positivity of the weight.**  Under the countable cover hypothesis `hcover` on `Y`, the
`𝔪`-atoms of the points of `Y` have positive `𝔫`-weight `ν`-almost everywhere. -/
theorem weight_pos (ν : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure ν] [StandardBorelSpace Work.EKLContract.X3]
    (𝔪 𝔫 : Work.EKLComp.SigAlg) (hm : 𝔪.m ≤ borel Work.EKLContract.X3)
    (hn : 𝔫.m ≤ borel Work.EKLContract.X3) (hmn : 𝔪.m ≤ 𝔫.m)
    (hgen𝔪 : Work.EKLComp.CountablyGen 𝔪.m) (hgen𝔫 : Work.EKLComp.CountablyGen 𝔫.m)
    {Y : Set Work.EKLContract.X3} (hYmeas : MeasurableSet Y)
    (hcover : ∀ x : Work.EKLContract.X3, ∃ s : Set (Set Work.EKLContract.X3), s.Countable ∧
        (∀ t ∈ s, ∃ y ∈ Y, t = Work.EKLContract.atom 𝔪.m y ∩ Work.EKLContract.atom 𝔫.m y) ∧
        (∀ t ∈ s, t ⊆ Y) ∧
        Work.EKLContract.atom 𝔪.m x ∩ Y ⊆ ⋃₀ s) :
    ∀ᵐ x ∂ν, x ∈ Y →
      0 < ProbabilityTheory.condExpKernel ν 𝔪.m x (Work.EKLContract.atom 𝔫.m x) := by
  classical
  -- The bad set: the points of `Y` whose `𝔫`-weight vanishes.
  let Z : Set X3 := {x : X3 | ProbabilityTheory.condExpKernel ν 𝔪.m x (atom 𝔫.m x) = 0} ∩ Y
  have hZmeas : MeasurableSet Z := by
    refine MeasurableSet.inter ?_ hYmeas
    exact measurable_kernel_atom ν 𝔪 hm 𝔫 hn hgen𝔫 (measurableSet_singleton (0 : ℝ≥0∞))
  -- The conditional measure of `x` is carried by the `𝔪`-atom of `x`, a.e.
  have hcarried : ∀ᵐ x ∂ν,
      ProbabilityTheory.condExpKernel ν 𝔪.m x (atom 𝔪.m x) = 1 :=
    condExpKernel_atom 𝔪 hm hgen𝔪 ν
  -- Main pointwise statement: `κ_x Z = 0` whenever `κ_x` is carried by `[x]_𝔪`.
  have hmain : ∀ x : X3, ProbabilityTheory.condExpKernel ν 𝔪.m x (atom 𝔪.m x) = 1 →
      ProbabilityTheory.condExpKernel ν 𝔪.m x Z = 0 := by
    intro x hx1
    have hAmeas : MeasurableSet (atom 𝔪.m x) := hm _ (measurableSet_atom 𝔪.m hgen𝔪 x)
    have hcompl : (ProbabilityTheory.condExpKernel ν 𝔪.m x) (atom 𝔪.m x)ᶜ = 0 := by
      have hmarkov : IsMarkovKernel (ProbabilityTheory.condExpKernel ν 𝔪.m) := inferInstance
      rw [measure_compl hAmeas (measure_ne_top _ _),
        (hmarkov.isProbabilityMeasure x).measure_univ, hx1, tsub_self]
    obtain ⟨s, hsc, hform, hsY, hcov⟩ := hcover x
    haveI : Countable ↥s := hsc.to_subtype
    -- `Z ∩ [x]_𝔪` is covered by the countably many pieces `t ∩ [x]_𝔪 ∩ Z`.
    have hsub : Z ∩ atom 𝔪.m x ⊆ ⋃ t : ↥s, ((t : Set X3) ∩ atom 𝔪.m x ∩ Z) := by
      intro y hy
      obtain ⟨hyZ, hyA⟩ := hy
      have hy1 : y ∈ atom 𝔪.m x ∩ Y := ⟨hyA, hyZ.2⟩
      have hy2 : y ∈ ⋃₀ s := hcov hy1
      rw [Set.sUnion_eq_biUnion] at hy2
      obtain ⟨t, ht, hyt⟩ := Set.mem_iUnion₂.mp hy2
      exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, ⟨⟨hyt, hyA⟩, hyZ⟩⟩
    -- Each piece contributes zero measure.
    have hpiece : ∀ t : ↥s,
        (ProbabilityTheory.condExpKernel ν 𝔪.m x) ((t : Set X3) ∩ atom 𝔪.m x ∩ Z) = 0 := by
      intro t
      obtain ⟨y, _hyY, hty⟩ := hform (t : Set X3) t.2
      by_cases hInt : (t : Set X3) ∩ atom 𝔪.m x = ∅
      · rw [hInt, Set.empty_inter]
        simp
      · -- the piece meets `[x]_𝔪`, hence lies inside it
        obtain ⟨z₀, hz₀t, hz₀A⟩ := Set.nonempty_iff_ne_empty.mpr hInt
        have htyz : z₀ ∈ atom 𝔪.m y ∩ atom 𝔫.m y := hty ▸ hz₀t
        have hAz : atom 𝔪.m y = atom 𝔪.m x := by
          rw [← atom_eq_of_mem 𝔪.m htyz.1, atom_eq_of_mem 𝔪.m hz₀A]
        have htsub : (t : Set X3) ⊆ atom 𝔪.m x := by
          rw [hty, hAz]
          exact Set.inter_subset_left
        rw [Set.inter_eq_left.mpr htsub]
        by_cases hIZ : (t : Set X3) ∩ Z = ∅
        · rw [hIZ]
          simp
        · obtain ⟨z, hzt, hzZ⟩ := Set.nonempty_iff_ne_empty.mpr hIZ
          have hzA : z ∈ atom 𝔪.m x := htsub hzt
          have hzW : ProbabilityTheory.condExpKernel ν 𝔪.m z (atom 𝔫.m z) = 0 := hzZ.1
          have htz : z ∈ atom 𝔪.m y ∩ atom 𝔫.m y := hty ▸ hzt
          have hsub2 : (t : Set X3) ⊆ atom 𝔫.m z := by
            rw [hty, atom_eq_of_mem 𝔫.m htz.2]
            exact Set.inter_subset_right
          refine le_antisymm ?_ bot_le
          calc (ProbabilityTheory.condExpKernel ν 𝔪.m x) ((t : Set X3) ∩ Z)
              ≤ (ProbabilityTheory.condExpKernel ν 𝔪.m x) (t : Set X3) :=
                measure_mono Set.inter_subset_left
            _ = (ProbabilityTheory.condExpKernel ν 𝔪.m z) (t : Set X3) := by
                rw [kernel_atom_const 𝔪 hzA]
            _ ≤ (ProbabilityTheory.condExpKernel ν 𝔪.m z) (atom 𝔫.m z) := measure_mono hsub2
            _ = 0 := hzW
    refine le_antisymm ?_ bot_le
    calc (ProbabilityTheory.condExpKernel ν 𝔪.m x) Z
        = (ProbabilityTheory.condExpKernel ν 𝔪.m x)
            (Z ∩ atom 𝔪.m x ∪ Z \ atom 𝔪.m x) := by
          rw [Set.inter_union_sdiff]
      _ ≤ (ProbabilityTheory.condExpKernel ν 𝔪.m x) (Z ∩ atom 𝔪.m x)
            + (ProbabilityTheory.condExpKernel ν 𝔪.m x) (Z \ atom 𝔪.m x) :=
          measure_union_le _ _
      _ ≤ (ProbabilityTheory.condExpKernel ν 𝔪.m x) (Z ∩ atom 𝔪.m x) + 0 := by
          refine add_le_add le_rfl ?_
          calc (ProbabilityTheory.condExpKernel ν 𝔪.m x) (Z \ atom 𝔪.m x)
              ≤ (ProbabilityTheory.condExpKernel ν 𝔪.m x) (atom 𝔪.m x)ᶜ :=
                measure_mono (fun y hy => hy.2)
            _ = 0 := hcompl
      _ = (ProbabilityTheory.condExpKernel ν 𝔪.m x) (Z ∩ atom 𝔪.m x) := add_zero _
      _ ≤ (ProbabilityTheory.condExpKernel ν 𝔪.m x)
            (⋃ t : ↥s, ((t : Set X3) ∩ atom 𝔪.m x ∩ Z)) := measure_mono hsub
      _ ≤ ∑' t : ↥s,
            (ProbabilityTheory.condExpKernel ν 𝔪.m x) ((t : Set X3) ∩ atom 𝔪.m x ∩ Z) :=
          measure_iUnion_le _
      _ = 0 := by
          rw [ENNReal.tsum_eq_zero]
          exact hpiece
  -- Disintegration: `ν Z = ∫⁻ x, κ_x Z ∂ν`, and the integrand vanishes a.e.
  have hνZ : ν Z = 0 := by
    rw [measure_apply_eq_lintegral_condExpKernel' 𝔪 hm ν hZmeas]
    have hzero : (fun x : X3 => ProbabilityTheory.condExpKernel ν 𝔪.m x Z)
        =ᵐ[ν] fun _ => (0 : ℝ≥0∞) := by
      filter_upwards [hcarried] with x hx
      exact hmain x hx
    rw [lintegral_congr_ae hzero, lintegral_zero]
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hνZ] with x hx
  intro hxY
  by_contra hle
  exact hx ⟨le_antisymm (le_of_not_gt hle) bot_le, hxY⟩

end Work.EKLComp
