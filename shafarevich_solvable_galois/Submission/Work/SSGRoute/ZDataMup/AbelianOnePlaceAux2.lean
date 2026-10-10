import Mathlib.Order.CompletePartialOrder
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.Work.SSGRoute.ZDataMup.AbelianOnePlaceAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open scoped NumberField Valued
open NumberField IsDedekindDomain

namespace Work.SSGRoute.ZDataMup

theorem isCyclic_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) [IsCyclic H] :
    IsCyclic G := by
  obtain ⟨h, hh⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic H)
  refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨e.symm h, ?_⟩
  change Subgroup.zpowers ((e.symm : H →* G) h) = ⊤
  rw [← MonoidHom.map_zpowers (e.symm : H →* G) h, hh,
    Subgroup.map_top_of_surjective _ (fun y => ⟨e y, by simp⟩)]

theorem exists_cyclic_quotient_separating {G : Type*} [CommGroup G] [Finite G]
    (g : G) (hg : g ≠ 1) : ∃ H : Subgroup G, g ∉ H ∧ IsCyclic (G ⧸ H) := by
  classical
  obtain ⟨ι, x, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  obtain ⟨i, hi⟩ : ∃ i, e g i ≠ 1 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hg (e.injective (funext fun j => (h j).trans (congrFun (map_one e) j).symm))
  let φ : G →* Multiplicative (ZMod (n i)) :=
    (Pi.evalMonoidHom (fun j => Multiplicative (ZMod (n j))) i).comp e.toMonoidHom
  have hφ : ∀ y : G, φ y = e y i := fun y => rfl
  have hsurj : Function.Surjective φ := by
    intro y
    refine ⟨e.symm (Pi.mulSingle i y), ?_⟩
    rw [hφ, MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same]
  refine ⟨φ.ker, ?_, ?_⟩
  · intro hmem
    exact hi ((hφ g).symm.trans (MonoidHom.mem_ker.mp hmem))
  · have hrange : φ.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
    have hiso : G ⧸ φ.ker ≃* Multiplicative (ZMod (n i)) :=
      (QuotientGroup.quotientKerEquivRange φ).trans
        ((MulEquiv.subgroupCongr hrange).trans Subgroup.topEquiv)
    exact isCyclic_of_mulEquiv hiso

theorem fixingSubgroup_iSup_eq_iInf' {F : Type*} {X : Type*} [Field F] [Field X] [Algebra F X]
    {ι : Type*} (A : ι → IntermediateField F X) :
    (⨆ i, A i).fixingSubgroup = ⨅ i, (A i).fixingSubgroup := by
  refine le_antisymm (le_iInf fun j => IntermediateField.fixingSubgroup_le (le_iSup A j)) ?_
  have h : ∀ i, A i ≤ IntermediateField.fixedField (⨅ i, (A i).fixingSubgroup) := by
    intro i
    rw [IntermediateField.le_iff_le]
    exact iInf_le _ i
  have h2 : (⨆ i, A i) ≤ IntermediateField.fixedField (⨅ i, (A i).fixingSubgroup) := iSup_le h
  rwa [IntermediateField.le_iff_le] at h2

theorem isCyclic_intermediateField_iSup_eq_top {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a) :
    (⨆ (M : {M : IntermediateField K L // IsCyclic (M ≃ₐ[K] M)}), M.1) = ⊤ := by
  letI : CommGroup (L ≃ₐ[K] L) := { mul_comm := hcomm }
  have hfix : (⨆ (M : {M : IntermediateField K L // IsCyclic (M ≃ₐ[K] M)}), M.1).fixingSubgroup
      = ⊥ := by
    rw [fixingSubgroup_iSup_eq_iInf', eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    by_contra hne
    obtain ⟨H, hH, hcyc⟩ := exists_cyclic_quotient_separating σ (by simpa [Ne] using hne)
    haveI : IsCyclic ((IntermediateField.fixedField H) ≃ₐ[K] (IntermediateField.fixedField H)) :=
      isCyclic_of_mulEquiv (IsGalois.normalAutEquivQuotient H).symm
    have h2 := Subgroup.mem_iInf.mp hσ ⟨IntermediateField.fixedField H, inferInstance⟩
    rw [IntermediateField.fixingSubgroup_fixedField] at h2
    exact hH h2
  have h1 : IntermediateField.fixedField
      ((⨆ (M : {M : IntermediateField K L // IsCyclic (M ≃ₐ[K] M)}), M.1).fixingSubgroup)
      = IntermediateField.fixedField (⊥ : Subgroup (L ≃ₐ[K] L)) := by rw [hfix]
  rw [IsGalois.fixedField_fixingSubgroup] at h1
  rw [← IntermediateField.fixingSubgroup_top (F := K) (E := L),
    IsGalois.fixedField_fixingSubgroup (⊤ : IntermediateField K L)] at h1
  exact h1

theorem image_mem_localFieldImage {K : Type} [Field K] [NumberField K] {L : Type} [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (M : IntermediateField K L) (x : M) :
    algebraMap L (q.adicCompletion L) (x : L) ∈
      localFieldImage Q q hq M := by
  letI : Algebra (Q.adicCompletion K)
      ((Submission.NeukirchUchida.Local.placeUnder M q).adicCompletion M) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q
      (Submission.NeukirchUchida.Local.placeUnder M q)
      (Submission.NeukirchUchida.Local.liesOver_placeUnder M q Q)
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q hq
  show algebraMap L (q.adicCompletion L) (x : L) ∈
    IntermediateField.map (adjCompletionHom Q q hq M) ⊤
  rw [IntermediateField.mem_map]
  refine ⟨(x : (Submission.NeukirchUchida.Local.placeUnder M q).adicCompletion M), trivial, ?_⟩
  exact Commons.RingTheory.Henselian.adicCompletionMap_apply (K := ↥M) (L := L)
    (Submission.NeukirchUchida.Local.placeUnder M q) q
    (Ideal.LiesOver.mk (by rw [Submission.NeukirchUchida.Local.placeUnder_asIdeal])) x

theorem iSup_localFieldImage_eq_top {K : Type} [Field K] [NumberField K] {L : Type} [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    (⨆ (M : {M : IntermediateField K L // IsCyclic (M ≃ₐ[K] M)}),
      localFieldImage Q q hq M.1) = ⊤ := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q hq
  haveI : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  have hcont : Continuous (algebraMap (Q.adicCompletion K) (q.adicCompletion L)) :=
    Commons.RingTheory.Henselian.adicCompletionMap_continuous Q q hq
  haveI : ContinuousSMul (Q.adicCompletion K) (q.adicCompletion L) :=
    continuousSMul_of_algebraMap _ _ hcont
  have hgen : Algebra.adjoin (Q.adicCompletion K)
      (Set.range (algebraMap L (q.adicCompletion L))) = ⊤ := by
    set S := Algebra.adjoin (Q.adicCompletion K) (Set.range (algebraMap L (q.adicCompletion L)))
      with hS
    have hclosed : IsClosed (S : Set (q.adicCompletion L)) := by
      haveI : FiniteDimensional (Q.adicCompletion K) ↥(S.toSubmodule) :=
        Submodule.finiteDimensional_of_le (le_top)
      exact Submodule.closed_of_finiteDimensional S.toSubmodule
    have hdense : DenseRange (algebraMap L (q.adicCompletion L)) :=
      IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap L q
    have hrange : Set.range (algebraMap L (q.adicCompletion L)) ⊆ (S : Set (q.adicCompletion L)) :=
      Algebra.subset_adjoin
    have huniv : (Set.univ : Set (q.adicCompletion L)) ⊆ (S : Set (q.adicCompletion L)) := by
      have hd : closure (Set.range (algebraMap L (q.adicCompletion L))) = Set.univ :=
        hdense.closure_range
      rw [← hd]
      exact closure_minimal hrange hclosed
    exact Algebra.eq_top_iff.mpr (fun z => huniv (Set.mem_univ z))
  let g : {M : IntermediateField K L // IsCyclic (M ≃ₐ[K] M)} →
      IntermediateField (Q.adicCompletion K) (q.adicCompletion L) :=
    fun M => localFieldImage Q q hq M.1
  let S' : IntermediateField (Q.adicCompletion K) (q.adicCompletion L) := ⨆ M, g M
  let X : IntermediateField K L :=
    { Subfield.comap (algebraMap L (q.adicCompletion L)) S'.toSubfield with
      algebraMap_mem' := fun k => by
        have hcomp : algebraMap L (q.adicCompletion L) (algebraMap K L k)
            = algebraMap (Q.adicCompletion K) (q.adicCompletion L) k :=
          (Commons.RingTheory.Henselian.adicCompletionMap_apply Q q hq k).symm
        show algebraMap L (q.adicCompletion L) (algebraMap K L k) ∈ S'.toSubfield
        rw [hcomp]
        exact IntermediateField.algebraMap_mem S' k }
  have hpre : (⨆ (M : {M : IntermediateField K L // IsCyclic (M ≃ₐ[K] M)}), M.1) ≤ X := by
    refine iSup_le fun M => ?_
    intro x hx
    show x ∈ Subfield.comap (algebraMap L (q.adicCompletion L)) S'.toSubfield
    rw [Subfield.mem_comap]
    exact le_iSup g M (image_mem_localFieldImage (K := K) (L := L) Q q hq M.1 ⟨x, hx⟩)
  have hB : Set.range (algebraMap L (q.adicCompletion L)) ⊆ (S'.toSubalgebra :
      Set (q.adicCompletion L)) := by
    intro y hy
    obtain ⟨l, rfl⟩ := hy
    have hl : l ∈ (⨆ (M : {M : IntermediateField K L // IsCyclic (M ≃ₐ[K] M)}), M.1) := by
      rw [isCyclic_intermediateField_iSup_eq_top hcomm]
      trivial
    exact hpre hl
  show S' = ⊤
  rw [eq_top_iff]
  intro x _
  have hadj : Algebra.adjoin (Q.adicCompletion K) (Set.range (algebraMap L (q.adicCompletion L)))
      ≤ S'.toSubalgebra := Algebra.adjoin_le_iff.mpr hB
  exact hadj (hgen.symm.le (show x ∈ (⊤ : Subalgebra (Q.adicCompletion K)
      (q.adicCompletion L)) from trivial))


end Work.SSGRoute.ZDataMup
