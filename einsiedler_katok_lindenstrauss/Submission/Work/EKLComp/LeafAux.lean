import Mathlib
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLComp.condExpKernel_atom

/-!
# Support material for `Work.EKLComp.plaque_propor`

This module collects the elementary σ-algebra/atoms API, a countable π-system generating the Borel
σ-algebra of `X₃`, the fact that conditional kernels are constant on atoms, and the two "null /
conull set" facts for conditional kernels, together with the nested case of Pisa Prop. 5.17
(`nested_propor`, which takes the tower property of the conditional kernel as a hypothesis so that
this module does not depend on the modules proving that tower property).

The module `Work.EKLComp.plaque_propor` imports this module together with the three auxiliary
lemmas `plaque_cover`, `kernel_comp_self`, `kernel_restrict` and assembles the target theorem.
-/

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.EKLComp

noncomputable section

/-! ## 1. Countable generation, atoms, and the join -/

/-- `m` is a countably generated σ-algebra on `X₃` (convenience wrapper around
`MeasurableSpace.CountablyGenerated`, so that hypotheses about *named* σ-algebras are directly
usable). -/
def CountablyGen (m : MeasurableSpace Work.EKLContract.X3) : Prop :=
  ∃ b : Set (Set Work.EKLContract.X3), b.Countable ∧ m = MeasurableSpace.generateFrom b

lemma CountablyGen.toCG {m : MeasurableSpace Work.EKLContract.X3} (hm : CountablyGen m) :
    @MeasurableSpace.CountablyGenerated Work.EKLContract.X3 m :=
  ⟨hm.choose, hm.choose_spec.1, hm.choose_spec.2⟩

/-- `Work.EKLContract.atom m x` is Mathlib's `measurableAtom` for the σ-algebra `m`. -/
lemma atom_eq_measurableAtom (m : MeasurableSpace Work.EKLContract.X3)
    (x : Work.EKLContract.X3) : Work.EKLContract.atom m x = @measurableAtom _ m x := by
  ext z
  simp only [Work.EKLContract.atom, measurableAtom, Set.mem_sInter, Set.mem_iInter,
    Set.mem_ofPred_eq]
  constructor
  · intro h s hxs hs; exact h s ⟨hs, hxs⟩
  · intro h t ht; exact h t ht.2 ht.1

/-- Every `m`-measurable set containing `x` contains the whole atom of `x`. -/
lemma mem_of_mem_atom (m : MeasurableSpace Work.EKLContract.X3) {s : Set Work.EKLContract.X3}
    (hs : MeasurableSet[m] s) {x : Work.EKLContract.X3} (hx : x ∈ s)
    {y : Work.EKLContract.X3} (hy : y ∈ Work.EKLContract.atom m x) : y ∈ s :=
  Set.mem_sInter.mp hy s ⟨hs, hx⟩

/-- Conversely: if `y` is in the atom of `x`, then every `m`-measurable set containing `y`
contains `x`. -/
lemma mem_of_mem_atom_of_mem (m : MeasurableSpace Work.EKLContract.X3) {s : Set Work.EKLContract.X3}
    (hs : MeasurableSet[m] s) {x y : Work.EKLContract.X3}
    (hy : y ∈ Work.EKLContract.atom m x) (hys : y ∈ s) : x ∈ s := by
  by_contra hxs
  exact (Set.mem_sInter.mp hy sᶜ ⟨hs.compl, hxs⟩) hys

/-- Atoms are measurable for a countably generated σ-algebra. -/
lemma measurableSet_atom (m : MeasurableSpace Work.EKLContract.X3) (hm : CountablyGen m)
    (x : Work.EKLContract.X3) : MeasurableSet[m] (Work.EKLContract.atom m x) := by
  letI := m
  haveI : MeasurableSpace.CountablyGenerated Work.EKLContract.X3 := hm.toCG
  rw [atom_eq_measurableAtom]
  exact MeasurableSpace.measurableSet_measurableAtom x

/-- If `y` is in the atom of `x` then the atoms coincide. -/
lemma atom_eq_of_mem (m : MeasurableSpace Work.EKLContract.X3) {x y : Work.EKLContract.X3}
    (hy : y ∈ Work.EKLContract.atom m x) :
    Work.EKLContract.atom m y = Work.EKLContract.atom m x := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    rw [Work.EKLContract.atom, Set.mem_sInter] at hz ⊢
    intro s hs
    exact hz s ⟨hs.1, mem_of_mem_atom m hs.1 hs.2 hy⟩
  · intro z hz
    rw [Work.EKLContract.atom, Set.mem_sInter] at hz ⊢
    intro s hs
    exact hz s ⟨hs.1, mem_of_mem_atom_of_mem m hs.1 hy hs.2⟩

/-- Atoms are finer for finer σ-algebras. -/
lemma atom_subset_of_le (m n : MeasurableSpace Work.EKLContract.X3) (hmn : m ≤ n)
    (hm : CountablyGen m) (x : Work.EKLContract.X3) :
    Work.EKLContract.atom n x ⊆ Work.EKLContract.atom m x := by
  have hmmeas : MeasurableSet[m] (Work.EKLContract.atom m x) := measurableSet_atom m hm x
  have hxm : x ∈ Work.EKLContract.atom m x := by simp [Work.EKLContract.atom]
  intro z hz
  exact mem_of_mem_atom n (hmn _ hmmeas) hxm hz

/-- The atom of the join of two countably generated σ-algebras is the intersection of the atoms. -/
lemma atom_join (m n : MeasurableSpace Work.EKLContract.X3) (hm : CountablyGen m)
    (hn : CountablyGen n) (x : Work.EKLContract.X3) :
    Work.EKLContract.atom (m ⊔ n) x = Work.EKLContract.atom m x ∩ Work.EKLContract.atom n x := by
  obtain ⟨bm, hbmc, hbm⟩ := hm
  obtain ⟨bn, hbnc, hbn⟩ := hn
  have hxm : x ∈ Work.EKLContract.atom m x := by simp [Work.EKLContract.atom]
  have hxn : x ∈ Work.EKLContract.atom n x := by simp [Work.EKLContract.atom]
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    exact ⟨atom_subset_of_le m (m ⊔ n) le_sup_left ⟨bm, hbmc, hbm⟩ x hz,
      atom_subset_of_le n (m ⊔ n) le_sup_right ⟨bn, hbnc, hbn⟩ x hz⟩
  · intro z hz
    obtain ⟨hzm, hzn⟩ := hz
    rw [Work.EKLContract.atom, Set.mem_sInter]
    intro s hs
    obtain ⟨hsmeas, hxs⟩ := hs
    have key : x ∈ s ↔ z ∈ s := by
      rw [hbm, hbn, MeasurableSpace.generateFrom_sup_generateFrom] at hsmeas
      refine MeasurableSpace.generateFrom_induction (bm ∪ bn) (fun u _ => x ∈ u ↔ z ∈ u)
        ?_ ?_ ?_ ?_ s hsmeas
      · intro t ht _
        rcases (show t ∈ bm ∨ t ∈ bn from ht) with ht | ht
        · have hmt : MeasurableSet[m] t := by
            rw [hbm]; exact MeasurableSpace.measurableSet_generateFrom ht
          exact ⟨fun hx => mem_of_mem_atom m hmt hx hzm,
            fun hz' => mem_of_mem_atom_of_mem m hmt hzm hz'⟩
        · have hnt : MeasurableSet[n] t := by
            rw [hbn]; exact MeasurableSpace.measurableSet_generateFrom ht
          exact ⟨fun hx => mem_of_mem_atom n hnt hx hzn,
            fun hz' => mem_of_mem_atom_of_mem n hnt hzn hz'⟩
      · simp
      · intro t ht ih
        exact ih.not
      · intro f hf ihf
        simp only [Set.mem_iUnion]
        exact exists_congr fun k => ihf k
    exact key.mp hxs

/-- If `y` is in the atom of `x`, then the σ-algebras' atoms identify: `atom m y = atom m x`. -/
lemma atom_inter_eq_of_mem (m : MeasurableSpace Work.EKLContract.X3)
    {x y : Work.EKLContract.X3} (hy : y ∈ Work.EKLContract.atom m x) :
    Work.EKLContract.atom m y = Work.EKLContract.atom m x := atom_eq_of_mem m hy

/-- A measurable real-valued function is constant on atoms. -/
lemma eq_of_mem_atom (m : MeasurableSpace Work.EKLContract.X3)
    {f : Work.EKLContract.X3 → ℝ} (hf : Measurable[m] f) {x y : Work.EKLContract.X3}
    (hy : y ∈ Work.EKLContract.atom m x) : f y = f x := by
  refine le_antisymm ?_ ?_
  · by_contra hcon
    rw [not_le] at hcon
    have hSm : MeasurableSet[m] (f ⁻¹' Ioi (f x)) := hf measurableSet_Ioi
    exact absurd (mem_of_mem_atom_of_mem m hSm hy hcon) (lt_irrefl (f x))
  · by_contra hcon
    rw [not_le] at hcon
    have hSm : MeasurableSet[m] (f ⁻¹' Iio (f x)) := hf measurableSet_Iio
    exact absurd (mem_of_mem_atom_of_mem m hSm hy hcon) (lt_irrefl (f x))

/-- A measurable `ℝ≥0∞`-valued function is constant on atoms. -/
lemma eq_of_mem_atom_ennreal (m : MeasurableSpace Work.EKLContract.X3)
    {f : Work.EKLContract.X3 → ℝ≥0∞} (hf : Measurable[m] f) {x y : Work.EKLContract.X3}
    (hy : y ∈ Work.EKLContract.atom m x) : f y = f x := by
  refine le_antisymm ?_ ?_
  · by_contra hcon
    rw [not_le] at hcon
    have hSm : MeasurableSet[m] (f ⁻¹' Ioi (f x)) := hf measurableSet_Ioi
    exact absurd (mem_of_mem_atom_of_mem m hSm hy hcon) (lt_irrefl (f x))
  · by_contra hcon
    rw [not_le] at hcon
    have hSm : MeasurableSet[m] (f ⁻¹' Iio (f x)) := hf measurableSet_Iio
    exact absurd (mem_of_mem_atom_of_mem m hSm hy hcon) (lt_irrefl (f x))

/-! ## 2. A countable π-system generating the Borel σ-algebra of `X₃` -/

/-- An enumeration of a countable topological basis of `X₃` (with `univ` as the junk value). -/
noncomputable def basisEnum : ℕ → Set Work.EKLContract.X3 := by
  classical
  exact fun n => if h : ∃ b : TopologicalSpace.countableBasis Work.EKLContract.X3,
      Encodable.encode b = n
    then ((h.choose : TopologicalSpace.countableBasis Work.EKLContract.X3) : Set _) else Set.univ

lemma basisEnum_cases (n : ℕ) :
    basisEnum n ∈ TopologicalSpace.countableBasis Work.EKLContract.X3 ∨
      basisEnum n = Set.univ := by
  classical
  by_cases h : ∃ b : TopologicalSpace.countableBasis Work.EKLContract.X3, Encodable.encode b = n
  · left
    simpa only [basisEnum, dif_pos h] using h.choose.2
  · right
    simp only [basisEnum, dif_neg h]

lemma basisEnum_mem_range {b : Set Work.EKLContract.X3}
    (hb : b ∈ TopologicalSpace.countableBasis Work.EKLContract.X3) :
    ∃ n, basisEnum n = b := by
  classical
  refine ⟨Encodable.encode (⟨b, hb⟩ : TopologicalSpace.countableBasis Work.EKLContract.X3), ?_⟩
  have h : ∃ c : TopologicalSpace.countableBasis Work.EKLContract.X3,
      Encodable.encode c = Encodable.encode (⟨b, hb⟩ : TopologicalSpace.countableBasis _) :=
    ⟨⟨b, hb⟩, rfl⟩
  have hch : ((h.choose : TopologicalSpace.countableBasis Work.EKLContract.X3) : Set _) = b := by
    rw [Encodable.encode_injective h.choose_spec]
  simpa only [basisEnum, dif_pos h] using hch

/-- The countable π-system of finite intersections of the enumerated basis of `X₃`. -/
def piBasis : Set (Set Work.EKLContract.X3) :=
  Set.range (fun t : Finset ℕ => ⋂ n ∈ (t : Set ℕ), basisEnum n)

lemma countable_piBasis : piBasis.Countable := Set.countable_range _

lemma isPiSystem_piBasis : IsPiSystem piBasis := by
  rintro s ⟨t, rfl⟩ u ⟨t', rfl⟩ _
  refine ⟨t ∪ t', ?_⟩
  ext x
  simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.coe_union, Set.mem_union]
  constructor
  · intro h
    exact ⟨fun n hn => h n (Or.inl hn), fun n hn => h n (Or.inr hn)⟩
  · rintro ⟨h1, h2⟩ n (hn | hn)
    exacts [h1 n hn, h2 n hn]

/-- Every element of the π-system is Borel. -/
lemma measurableSet_of_mem_piBasis {s : Set Work.EKLContract.X3} (hs : s ∈ piBasis) :
    MeasurableSet s := by
  obtain ⟨t, rfl⟩ := hs
  refine MeasurableSet.biInter t.countable_toSet fun n _ => ?_
  rcases basisEnum_cases n with h | h
  · exact (TopologicalSpace.isOpen_of_mem_countableBasis h).measurableSet
  · rw [h]; exact MeasurableSet.univ

lemma generateFrom_subset_borel_piBasis :
    MeasurableSpace.generateFrom piBasis ≤ borel Work.EKLContract.X3 := by
  refine MeasurableSpace.generateFrom_le ?_
  intro s hs
  exact measurableSet_of_mem_piBasis hs

lemma generateFrom_piBasis :
    MeasurableSpace.generateFrom piBasis = borel Work.EKLContract.X3 := by
  refine le_antisymm generateFrom_subset_borel_piBasis ?_
  have hborel : borel Work.EKLContract.X3 =
      MeasurableSpace.generateFrom (TopologicalSpace.countableBasis Work.EKLContract.X3) :=
    (TopologicalSpace.isBasis_countableBasis Work.EKLContract.X3).borel_eq_generateFrom
  rw [hborel]
  refine MeasurableSpace.generateFrom_le ?_
  intro b hb
  obtain ⟨n, hn⟩ := basisEnum_mem_range hb
  refine MeasurableSpace.measurableSet_generateFrom (show b ∈ piBasis from ⟨{n}, ?_⟩)
  show (⋂ m ∈ (({n} : Finset ℕ) : Set ℕ), basisEnum m) = b
  rw [Finset.coe_singleton, Set.biInter_singleton, hn]

/-- Two finite measures agreeing on the π-system `piBasis` and having the same total mass agree. -/
lemma ext_of_piBasis {μ ν : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsFiniteMeasure μ] (h : ∀ s ∈ piBasis, μ s = ν s)
    (h1 : μ Set.univ = ν Set.univ) : μ = ν :=
  MeasureTheory.ext_of_generate_finite piBasis generateFrom_piBasis.symm isPiSystem_piBasis h h1

/-! ## 3. The conditional kernel is constant on atoms -/

/-- The conditional kernel `condExpKernel μ m` takes the same value at any two points of the
same `m`-atom. -/
lemma kernel_atom_const {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsFiniteMeasure μ] [StandardBorelSpace Work.EKLContract.X3]
    (𝔪 : Work.EKLComp.SigAlg) {x y : Work.EKLContract.X3}
    (hy : y ∈ Work.EKLContract.atom 𝔪.m x) :
    ProbabilityTheory.condExpKernel μ 𝔪.m x = ProbabilityTheory.condExpKernel μ 𝔪.m y := by
  refine MeasureTheory.Measure.ext fun s hs => ?_
  have hmeas : Measurable[𝔪.m] (fun z => ProbabilityTheory.condExpKernel μ 𝔪.m z s) :=
    ProbabilityTheory.measurable_condExpKernel hs
  exact (eq_of_mem_atom_ennreal 𝔪.m hmeas hy).symm


/-! ## 3. Null and conull sets for the conditional kernel -/

/-- A measurable `ν`-null set has `condExpKernel ν 𝔪.m x`-measure zero for `ν`-a.e. `x`. -/
lemma kernel_measure_eq_zero (ν : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure ν] [StandardBorelSpace Work.EKLContract.X3]
    (𝔪 : Work.EKLComp.SigAlg) (hm : 𝔪.m ≤ borel Work.EKLContract.X3)
    {B : Set Work.EKLContract.X3} (hB : MeasurableSet B) (hBν : ν B = 0) :
    ∀ᵐ x ∂ν, ProbabilityTheory.condExpKernel ν 𝔪.m x B = 0 := by
  classical
  set g : Work.EKLContract.X3 → ℝ := B.indicator 1 with hg
  have hgmeas : Measurable g := measurable_const.indicator hB
  have hgb : ∀ᵐ y ∂ν, ‖g y‖ ≤ 1 := Filter.Eventually.of_forall fun y => by
    by_cases hy : y ∈ B
    · rw [hg, Set.indicator_of_mem hy]; simp
    · rw [hg, Set.indicator_of_notMem hy]; simp
  have hgint : Integrable g ν := Integrable.of_bound hgmeas.aestronglyMeasurable 1 hgb
  have h1 : ν[g | 𝔪.m] =ᵐ[ν]
      fun x => ∫ y, g y ∂(ProbabilityTheory.condExpKernel ν 𝔪.m x) :=
    ProbabilityTheory.condExp_ae_eq_integral_condExpKernel hm hgint
  have h2 : ν[g | 𝔪.m] =ᵐ[ν] fun _ => (0 : ℝ) := by
    have hgg : g =ᵐ[ν] fun _ => (0 : ℝ) := by
      filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hBν] with y hy
      rw [hg, Set.indicator_of_notMem hy]
    have hc : ν[g | 𝔪.m] =ᵐ[ν] ν[(fun _ => (0 : ℝ)) | 𝔪.m] :=
      MeasureTheory.condExp_congr_ae hgg
    simpa only [MeasureTheory.condExp_const hm (0 : ℝ)] using hc
  filter_upwards [h1, h2] with x hx1 hx2
  have hzero : ∫ y, g y ∂(ProbabilityTheory.condExpKernel ν 𝔪.m x) = 0 := by
    rw [← hx1, hx2]
  have hreal : ((ProbabilityTheory.condExpKernel ν 𝔪.m x) B).toReal = 0 := by
    rw [← MeasureTheory.measureReal_def, ← MeasureTheory.integral_indicator_one hB]
    simpa [hg] using hzero
  have hfin : (ProbabilityTheory.condExpKernel ν 𝔪.m x) B ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ _
  rcases (ENNReal.toReal_eq_zero_iff _).mp hreal with h | h
  · exact h
  · exact absurd h hfin

/-- A measurable `ν`-conull set has `condExpKernel ν 𝔪.m x`-measure one for `ν`-a.e. `x`. -/
lemma kernel_measure_eq_one (ν : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure ν] [StandardBorelSpace Work.EKLContract.X3]
    (𝔪 : Work.EKLComp.SigAlg) (hm : 𝔪.m ≤ borel Work.EKLContract.X3)
    {G : Set Work.EKLContract.X3} (hG : MeasurableSet G) (hGν : ν Gᶜ = 0) :
    ∀ᵐ x ∂ν, ProbabilityTheory.condExpKernel ν 𝔪.m x G = 1 := by
  filter_upwards [kernel_measure_eq_zero ν 𝔪 hm hG.compl hGν] with x hx
  have huniv : (ProbabilityTheory.condExpKernel ν 𝔪.m x) Set.univ = 1 :=
    (ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure x).measure_univ
  have hadd := MeasureTheory.measure_add_measure_compl
    (μ := ProbabilityTheory.condExpKernel ν 𝔪.m x) (s := G) hG
  rw [huniv, hx, add_zero] at hadd
  exact hadd





end

end Work.EKLComp
