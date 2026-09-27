import Mathlib
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLComp.X3Background
import Submission.Work.EKLComp.condExpKernel_atom
import Submission.Work.EKLComp.exists_isCompact_cover_subgroup
import Submission.Work.EKLComp.isClosed_exists_smul_eq_of_isCompact

/-!
# Pisa Lemma 6.20: the conditional measure of an orbit-neighbourhood is positive

For a plaque algebra `(Z, 𝔪)` of a closed subgroup `U ≤ SL₃(ℝ)`, a probability measure `μ` on
`X₃ = SL₃(ℝ)/SL₃(ℤ)` and an open neighbourhood `O` of the identity in `SL₃(ℝ)`, the conditional
measure `condExpKernel (μ|Z) 𝔪.m x` gives positive mass to the orbit image
`{g • x : g ∈ O ∩ U}` for `μ|Z`-almost every `x ∈ Z`.

This is Lemma 6.20 of Einsiedler–Lindenstrauss, *Diagonal actions on locally homogeneous spaces*;
its proof is the "bad set" argument of 6.21: writing `B` for the set of `x` with
`κ x (O • x) = 0`, one shows that for every `x ∈ Z` the conditional measure of `B ∩ [x]` vanishes,
by covering `[x] ∩ B` by countably many translates of the orbit image `O • (t • x)` at points
`t • x ∈ B` (using second countability of `SL₃(ℝ)`), and then integrates over the atoms.

The file also contains the (elementary) auxiliary facts about atoms and `condExpKernel` used in
the argument: the conditional kernel is constant on atoms, its mass on an atom is one, and the
map `x ↦ κ x (A_x)` is Borel for Borel `A ⊆ X₃ × X₃`.
-/

open MeasureTheory ProbabilityTheory Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLComp

/-! ## 1. Atoms and the conditional kernel -/

/-- `Work.EKLContract.atom m x` is Mathlib's `measurableAtom`: the intersection of the
`m`-measurable sets containing `x`. -/
lemma atom_eq_measurableAtom' (m : MeasurableSpace X3) (x : X3) :
    atom m x = @measurableAtom X3 m x := by
  ext z
  simp only [Work.EKLContract.atom, measurableAtom, Set.mem_sInter, Set.mem_iInter,
    Set.mem_ofPred_eq]
  constructor
  · intro h s hxs hs; exact h s ⟨hs, hxs⟩
  · intro h t ht; exact h t ht.2 ht.1

/-- Every `m`-measurable set containing `x` contains the whole atom of `x`. -/
lemma mem_of_mem_atom' (m : MeasurableSpace X3) {s : Set X3} (hs : MeasurableSet[m] s)
    {x : X3} (hx : x ∈ s) {y : X3} (hy : y ∈ atom m x) : y ∈ s :=
  Set.mem_sInter.mp hy s ⟨hs, hx⟩

/-- Conversely: if `y` is in the atom of `x`, then every `m`-measurable set containing `y`
contains `x`. -/
lemma mem_of_mem_atom'' (m : MeasurableSpace X3) {s : Set X3} (hs : MeasurableSet[m] s)
    {x y : X3} (hy : y ∈ atom m x) (hys : y ∈ s) : x ∈ s := by
  by_contra hxs
  exact (Set.mem_sInter.mp hy sᶜ ⟨hs.compl, hxs⟩) hys

/-- An atom of a countably generated σ-algebra is measurable. -/
lemma measurableSet_atom' (m : MeasurableSpace X3)
    (hcg : ∃ b : Set (Set X3), b.Countable ∧ m = MeasurableSpace.generateFrom b) (x : X3) :
    MeasurableSet[m] (atom m x) := by
  letI := m
  haveI : MeasurableSpace.CountablyGenerated X3 :=
    ⟨hcg.choose, hcg.choose_spec.1, hcg.choose_spec.2⟩
  rw [atom_eq_measurableAtom']
  exact MeasurableSpace.measurableSet_measurableAtom x

/-- An `ℝ≥0∞`-valued `m`-measurable function is constant on atoms. -/
lemma eq_of_mem_atom_ennreal' {m : MeasurableSpace X3} {f : X3 → ℝ≥0∞} (hf : Measurable[m] f)
    {x y : X3} (hy : y ∈ atom m x) : f y = f x := by
  refine le_antisymm ?_ ?_
  · by_contra hcon
    rw [not_le] at hcon
    exact absurd (mem_of_mem_atom'' m (hf measurableSet_Ioi) hy hcon) (lt_irrefl (f x))
  · by_contra hcon
    rw [not_le] at hcon
    exact absurd (mem_of_mem_atom'' m (hf measurableSet_Iio) hy hcon) (lt_irrefl (f x))

/-- The conditional kernel `condExpKernel μ 𝔪.m` is constant on the atoms of `𝔪.m`. -/
lemma condExpKernel_eq_of_mem_atom' (𝔪 : SigAlg) [StandardBorelSpace X3]
    (μ : Measure X3) [IsFiniteMeasure μ] {x y : X3} (hy : y ∈ atom 𝔪.m x) :
    condExpKernel μ 𝔪.m x = condExpKernel μ 𝔪.m y := by
  refine Measure.ext fun s hs => ?_
  exact (eq_of_mem_atom_ennreal' (measurable_condExpKernel (μ := μ) (m := 𝔪.m) hs) hy).symm

/-- The measure of a set is the integral of its conditional probabilities. -/
lemma measure_apply_eq_lintegral_condExpKernel' (𝔪 : SigAlg) [StandardBorelSpace X3]
    (hm : 𝔪.m ≤ borelX3) (μ : Measure X3) [IsFiniteMeasure μ] {B : Set X3}
    (hB : MeasurableSet B) :
    μ B = ∫⁻ x, condExpKernel μ 𝔪.m x B ∂μ := by
  have hcomp := condExpKernel_comp_trim (μ := μ) (m := 𝔪.m) hm
  calc μ B = (condExpKernel μ 𝔪.m ∘ₘ μ.trim hm) B := by rw [hcomp]
    _ = ∫⁻ x, condExpKernel μ 𝔪.m x B ∂(μ.trim hm) :=
        Measure.bind_apply hB (condExpKernel μ 𝔪.m).aemeasurable
    _ = ∫⁻ x, condExpKernel μ 𝔪.m x B ∂μ :=
        lintegral_trim hm (Kernel.measurable_coe (condExpKernel μ 𝔪.m) hB)

/-- For a Borel set `A ⊆ X₃ × X₃` the map `x ↦ κ x (A_x)` is Borel, where `κ` is a conditional
expectation kernel whose σ-algebra may be smaller than the Borel one. -/
lemma measurable_condExpKernel_section' (𝔪 : SigAlg) [StandardBorelSpace X3]
    (hm : 𝔪.m ≤ borelX3) (μ : Measure X3) [IsFiniteMeasure μ] {A : Set (X3 × X3)}
    (hA : MeasurableSet A) :
    Measurable fun x : X3 => condExpKernel μ 𝔪.m x (Prod.mk x ⁻¹' A) := by
  have hmeas : @Measurable X3 X3 (borel X3) 𝔪.m id := fun s hs => hm s hs
  let k' : @Kernel X3 X3 (borel X3) (borel X3) :=
    @Kernel.comap X3 X3 𝔪.m (borel X3) X3 (borel X3) (condExpKernel μ 𝔪.m) id hmeas
  haveI : IsSFiniteKernel k' :=
    @Kernel.IsSFiniteKernel.comap X3 X3 𝔪.m (borel X3) X3 (borel X3) id
      (condExpKernel μ 𝔪.m) inferInstance hmeas
  have hsec : Measurable fun x : X3 => k' x (Prod.mk x ⁻¹' A) :=
    Kernel.measurable_kernel_prodMk_left (κ := k') hA
  have hfun : (fun x : X3 => k' x (Prod.mk x ⁻¹' A))
      = fun x : X3 => condExpKernel μ 𝔪.m x (Prod.mk x ⁻¹' A) := by
    funext x
    rw [@Kernel.comap_apply X3 X3 𝔪.m (borel X3) X3 (borel X3) id (condExpKernel μ 𝔪.m) hmeas x]
    rfl
  rw [hfun] at hsec
  exact hsec

/-! ## 2. The main statement -/

/- The topological inputs (`O ∩ U` is a countable union of compacta; the `K`-orbit relation on
`X₃ × X₃` is closed for compact `K`) are `Work.EKLComp.exists_isCompact_cover_subgroup` and
`Work.EKLComp.isClosed_exists_smul_eq_of_isCompact`. -/

theorem condExpKernel_pos (U : Subgroup Work.EKLContract.SL3)
    (hcl : IsClosed (U : Set Work.EKLContract.SL3))
    (Z : Set Work.EKLContract.X3) (𝔪 : Work.EKLComp.SigAlg)
    (hm : Work.EKLContract.IsPlaqueAlgebra U Z 𝔪.m)
    (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    [StandardBorelSpace Work.EKLContract.X3]
    (O : Set Work.EKLContract.SL3) (hO : IsOpen O) (h1 : (1 : Work.EKLContract.SL3) ∈ O) :
    ∀ᵐ x ∂(μ.restrict Z),
      0 < ProbabilityTheory.condExpKernel (μ.restrict Z) 𝔪.m x
            ((fun g : Work.EKLContract.SL3 => g • x) '' (O ∩ (U : Set Work.EKLContract.SL3))) := by
  classical
  haveI : SecondCountableTopology SL3 := Work.EKLContract.Lemmas.SL3Topology.2
  haveI : T2Space X3 := Work.EKLComp.X3Background.1
  haveI : SecondCountableTopology X3 := Work.EKLComp.X3Background.2.2.1
  let ν : Measure X3 := μ.restrict Z
  haveI : IsFiniteMeasure ν := inferInstanceAs (IsFiniteMeasure (μ.restrict Z))
  let E : X3 → Set X3 := fun x => (fun g : SL3 => g • x) '' (O ∩ (U : Set SL3))
  let B : Set X3 := {x | condExpKernel ν 𝔪.m x (E x) = 0}
  have hm_borel : 𝔪.m ≤ borelX3 := hm.1
  have hm_cg : ∃ b : Set (Set X3), b.Countable ∧ 𝔪.m = MeasurableSpace.generateFrom b := hm.2.1
  have hatom_sub : ∀ x ∈ Z,
      atom 𝔪.m x ⊆ Z ∧ atom 𝔪.m x ⊆ (fun u : SL3 => u • x) '' (U : Set SL3) :=
    fun x hx => ⟨(hm.2.2.2 x hx).1, (hm.2.2.2 x hx).2.1⟩
  have hatom_shape : ∀ x ∈ Z, atom 𝔪.m x = (fun g : SL3 => g • x) '' shape 𝔪.m U x := by
    intro x hx
    refine Set.Subset.antisymm ?_ ?_
    · intro y hy
      obtain ⟨u, hu, rfl⟩ := (hatom_sub x hx).2 hy
      exact ⟨u, ⟨hu, hy⟩, rfl⟩
    · rintro y ⟨u, hu, rfl⟩
      exact hu.2
  have hcarried : ∀ᵐ x ∂ν, condExpKernel ν 𝔪.m x (atom 𝔪.m x) = 1 :=
    condExpKernel_atom 𝔪 hm_borel hm_cg ν
  obtain ⟨C, hCcomp, hCcov⟩ := exists_isCompact_cover_subgroup U hcl O hO
  let An : ℕ → Set (X3 × X3) := fun n => {p | ∃ g ∈ C n, g • p.1 = p.2}
  have hAn_closed : ∀ n, IsClosed (An n) := fun n => isClosed_exists_smul_eq_of_isCompact (C n) (hCcomp n)
  have hAn_sec : ∀ n x, Prod.mk x ⁻¹' An n = (fun g : SL3 => g • x) '' C n := fun n x => rfl
  have hE_eq : ∀ x, E x = ⋃ n, (fun g : SL3 => g • x) '' C n := by
    intro x
    show (fun g : SL3 => g • x) '' (O ∩ (U : Set SL3)) = ⋃ n, (fun g : SL3 => g • x) '' C n
    rw [← hCcov, Set.image_iUnion]
  let Bad : Set X3 := ⋂ n, {x : X3 | condExpKernel ν 𝔪.m x (Prod.mk x ⁻¹' An n) = 0}
  have hBadmem : ∀ x : X3, x ∈ Bad ↔ ∀ n, condExpKernel ν 𝔪.m x (Prod.mk x ⁻¹' An n) = 0 := by
    intro x
    show x ∈ ⋂ n, {y : X3 | condExpKernel ν 𝔪.m y (Prod.mk y ⁻¹' An n) = 0} ↔ _
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  have hBad_eq : Bad = B := by
    ext x
    rw [hBadmem x]
    constructor
    · intro hx
      show condExpKernel ν 𝔪.m x (E x) = 0
      rw [hE_eq x]
      refine le_antisymm ?_ bot_le
      calc condExpKernel ν 𝔪.m x (⋃ n, (fun g : SL3 => g • x) '' C n)
          ≤ ∑' n, condExpKernel ν 𝔪.m x ((fun g : SL3 => g • x) '' C n) := measure_iUnion_le _
        _ = 0 := by
            rw [ENNReal.tsum_eq_zero]
            intro n
            rw [← hAn_sec n x]
            exact hx n
    · intro hx n
      rw [hAn_sec n x]
      refine le_antisymm ?_ bot_le
      calc condExpKernel ν 𝔪.m x ((fun g : SL3 => g • x) '' C n)
          ≤ condExpKernel ν 𝔪.m x (E x) := by
            rw [hE_eq x]
            exact measure_mono (Set.subset_iUnion (fun k => (fun g : SL3 => g • x) '' C k) n)
        _ = 0 := hx
  have hBad_meas : MeasurableSet Bad := by
    refine MeasurableSet.iInter fun n => ?_
    have hmeas := measurable_condExpKernel_section' 𝔪 hm_borel ν (hAn_closed n).measurableSet
    show MeasurableSet
      ((fun x : X3 => condExpKernel ν 𝔪.m x (Prod.mk x ⁻¹' An n)) ⁻¹' ({0} : Set ℝ≥0∞))
    exact hmeas (measurableSet_singleton (0 : ℝ≥0∞))
  have hB_meas : MeasurableSet B := hBad_eq ▸ hBad_meas
  have hbad_atom : ∀ x ∈ Z, condExpKernel ν 𝔪.m x (B ∩ atom 𝔪.m x) = 0 := by
    intro x hxZ
    let W : Set SL3 := shape 𝔪.m U x
    have hatomW : atom 𝔪.m x = (fun g : SL3 => g • x) '' W := hatom_shape x hxZ
    have h1W : (1 : SL3) ∈ W :=
      ⟨U.one_mem, by rw [one_smul]; exact Set.mem_sInter.mpr fun s hs => hs.2⟩
    let S : Set SL3 := {t | t ∈ W ∧ t • x ∈ B}
    have hBS : B ∩ atom 𝔪.m x = (fun g : SL3 => g • x) '' S := by
      rw [hatomW]
      ext y
      constructor
      · rintro ⟨hyB, g, hgW, rfl⟩
        exact ⟨g, ⟨hgW, hyB⟩, rfl⟩
      · rintro ⟨g, ⟨hgW, hgB⟩, rfl⟩
        exact ⟨hgB, ⟨g, hgW, rfl⟩⟩
    have hopen : ∀ t : ↥S, IsOpen ((fun g : SL3 => g * ((t : ↥S) : SL3)) '' O) := fun t =>
      (Homeomorph.mulRight ((t : ↥S) : SL3)).isOpen_image.mpr hO
    obtain ⟨T, hTcount, hTcov⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun t : ↥S => (fun g : SL3 => g * ((t : ↥S) : SL3)) '' O) hopen
    haveI : Countable ↥T := hTcount.to_subtype
    have hcover : (fun g : SL3 => g • x) '' S
        ⊆ ⋃ t : ↥T, E (((((t : ↥T) : ↥S) : SL3) • x)) := by
      rintro y ⟨s, hs, rfl⟩
      have hs1 : s ∈ ⋃ t : ↥S, (fun g : SL3 => g * ((t : ↥S) : SL3)) '' O :=
        Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ⟨1, h1, by simp⟩⟩
      rw [← hTcov] at hs1
      obtain ⟨t, htT, g, hgO, hgs⟩ := Set.mem_iUnion₂.mp hs1
      refine Set.mem_iUnion.mpr ⟨(⟨t, htT⟩ : ↥T), ?_⟩
      have hsU : s ∈ (U : Set SL3) := hs.1.1
      have htU : ((t : ↥S) : SL3) ∈ (U : Set SL3) := t.2.1.1
      have hgU : g ∈ (U : Set SL3) := by
        have hg : g = s * (((t : ↥S) : SL3))⁻¹ := by
          rw [← hgs, mul_assoc, mul_inv_cancel, mul_one]
        rw [hg]
        exact U.mul_mem hsU (U.inv_mem htU)
      have hgs' : g * ((t : ↥S) : SL3) = s := hgs
      have hkey : s • x = g • (((t : ↥S) : SL3) • x) := by
        calc s • x = (g * ((t : ↥S) : SL3)) • x := by rw [hgs']
          _ = g • (((t : ↥S) : SL3) • x) := mul_smul g ((t : ↥S) : SL3) x
      exact ⟨g, ⟨hgO, hgU⟩, hkey.symm⟩
    have hzero : ∀ t : ↥T, condExpKernel ν 𝔪.m x (E ((((t : ↥T) : ↥S) : SL3) • x)) = 0 := by
      intro t
      have htS : (((t : ↥T) : ↥S) : SL3) ∈ S := ((t : ↥T) : ↥S).2
      have hmem : ((((t : ↥T) : ↥S) : SL3)) • x ∈ atom 𝔪.m x := by
        rw [hatomW]
        exact ⟨(((t : ↥T) : ↥S) : SL3), htS.1, rfl⟩
      have hconst : condExpKernel ν 𝔪.m x
          = condExpKernel ν 𝔪.m ((((t : ↥T) : ↥S) : SL3) • x) :=
        condExpKernel_eq_of_mem_atom' 𝔪 ν hmem
      rw [hconst]
      exact htS.2
    refine le_antisymm ?_ bot_le
    calc condExpKernel ν 𝔪.m x (B ∩ atom 𝔪.m x)
        = condExpKernel ν 𝔪.m x ((fun g : SL3 => g • x) '' S) := by rw [hBS]
      _ ≤ condExpKernel ν 𝔪.m x (⋃ t : ↥T, E ((((t : ↥T) : ↥S) : SL3) • x)) :=
          measure_mono hcover
      _ ≤ ∑' t : ↥T, condExpKernel ν 𝔪.m x (E ((((t : ↥T) : ↥S) : SL3) • x)) :=
          measure_iUnion_le _
      _ = 0 := by
          rw [ENNReal.tsum_eq_zero]
          exact hzero
  have key1 : ∫⁻ x, condExpKernel ν 𝔪.m x Bad ∂ν
      = ∫⁻ x, condExpKernel ν 𝔪.m x (Bad ∩ atom 𝔪.m x) ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [hcarried] with x hx
    have hcompl : condExpKernel ν 𝔪.m x (atom 𝔪.m x)ᶜ = 0 := by
      have hmarkov : IsMarkovKernel (condExpKernel ν 𝔪.m) := inferInstance
      rw [measure_compl (μ := condExpKernel ν 𝔪.m x) (s := atom 𝔪.m x)
          (hm_borel _ (measurableSet_atom' 𝔪.m hm_cg x)) (by rw [hx]; exact ENNReal.one_ne_top),
        (hmarkov.isProbabilityMeasure x).measure_univ, hx, tsub_self]
    refine le_antisymm ?_ (measure_mono Set.inter_subset_left)
    have hsub : Bad \ atom 𝔪.m x ⊆ (atom 𝔪.m x)ᶜ := fun y hy => hy.2
    calc condExpKernel ν 𝔪.m x Bad
        = condExpKernel ν 𝔪.m x (Bad ∩ atom 𝔪.m x ∪ Bad \ atom 𝔪.m x) := by
          rw [Set.inter_union_sdiff]
      _ ≤ condExpKernel ν 𝔪.m x (Bad ∩ atom 𝔪.m x)
          + condExpKernel ν 𝔪.m x (Bad \ atom 𝔪.m x) := measure_union_le _ _
      _ ≤ condExpKernel ν 𝔪.m x (Bad ∩ atom 𝔪.m x)
          + condExpKernel ν 𝔪.m x (atom 𝔪.m x)ᶜ :=
          add_le_add_right (measure_mono (μ := condExpKernel ν 𝔪.m x) hsub) _
      _ = condExpKernel ν 𝔪.m x (Bad ∩ atom 𝔪.m x) := by rw [hcompl, add_zero]
  have key2 : ∫⁻ x, condExpKernel ν 𝔪.m x (Bad ∩ atom 𝔪.m x) ∂ν = 0 := by
    have hle : ∫⁻ x, condExpKernel ν 𝔪.m x (Bad ∩ atom 𝔪.m x) ∂ν
        ≤ ∫⁻ x, (0 : ℝ≥0∞) ∂ν := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem (hm_borel Z hm.2.2.1)] with x hxZ
      rw [hBad_eq]
      exact le_of_eq (hbad_atom x hxZ)
    rw [lintegral_zero] at hle
    exact nonpos_iff_eq_zero.mp hle
  have hνBad : ν Bad = 0 := by
    rw [measure_apply_eq_lintegral_condExpKernel' 𝔪 hm_borel ν hBad_meas, key1, key2]
  have h0 : ν {x : X3 | condExpKernel ν 𝔪.m x (E x) = 0} = 0 := by
    rw [show {x : X3 | condExpKernel ν 𝔪.m x (E x) = 0} = B from rfl, ← hBad_eq]
    exact hνBad
  have hfin : ∀ᵐ x ∂ν, condExpKernel ν 𝔪.m x (E x) ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using h0
  filter_upwards [hfin] with x hx
  exact pos_iff_ne_zero.mpr hx

end Work.EKLComp
