import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.FrobLiftDefs
import Submission.Work.SSGRoute.decomp_mod_inertia_cyclic
import Submission.Work.SSGRoute.levelInertia_defs
import Submission.Work.SSGRoute.inertiaAtLevelDefs
import Submission.Work.SSGRoute.mem_levelSub_iff_mem_inertia
import Submission.Work.SSGRoute.levelSub_comap_index_eq_inertiaDeg
import Submission.Work.SSGRoute.exists_frob_lift
import Submission.Work.SSGRoute.level_residueDeg_dvd_general
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

/-! ## Auxiliary topology of the inertia subgroup

The inertia subgroup `I_A` of a finite place `A` of `Ω` is a closed subgroup of `G_k = Ω ≃ₐ[k] Ω`
for the Krull topology, and every element outside it can be separated from it by an open subgroup
of `G_k` containing `I_A`.  These are the two facts used to convert the "generation modulo every
open subgroup containing `I_A`" produced by `Work.SSGRoute.decomp_mod_inertia_cyclic` into
statements about the closed subgroup `closure (zpowers σ)`.
-/

section Aux

variable (k : Type) [Field k] [NumberField k] (Ω : Type) [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- The open subgroups of `G_k = Ω ≃ₐ[k] Ω` containing the inertia subgroup `I_A`. -/
def OpenSubgroupsAbove (A : ValuationSubring Ω) : Type _ :=
  {V : Subgroup (Ω ≃ₐ[k] Ω) // IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧ inertiaSub k Ω A ≤ V}

/-- The decomposition group is closed in the Krull topology. -/
private theorem isClosed_decomp_ssg (A : ValuationSubring Ω) :
    IsClosed ((SSGRoute.decomp k A : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := by
  haveI : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  exact Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A

/-- **Separation from a closed set by an open normal subgroup.**  If `S` is a closed subset of the
Krull topology and `g ∉ S`, there is an open normal subgroup `N` of `G_k` with
`g * n ∉ S` for all `n ∈ N`. -/
private theorem exists_openNormal_forall_mul_notMem (A : ValuationSubring Ω) (S : Set (Ω ≃ₐ[k] Ω))
    (hS : IsClosed S) {g : Ω ≃ₐ[k] Ω} (hg : g ∉ S) :
    ∃ N : Subgroup (Ω ≃ₐ[k] Ω), N.Normal ∧ IsOpen (N : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ n ∈ N, g * n ∉ S := by
  classical
  have hclosed : IsClosed {n : Ω ≃ₐ[k] Ω | g * n ∈ S} :=
    hS.preimage (continuous_const.mul continuous_id)
  have h1 : (1 : Ω ≃ₐ[k] Ω) ∉ {n : Ω ≃ₐ[k] Ω | g * n ∈ S} := by
    simpa using hg
  have hopen : ({n : Ω ≃ₐ[k] Ω | g * n ∈ S}ᶜ) ∈ nhds (1 : Ω ≃ₐ[k] Ω) :=
    hclosed.isOpen_compl.mem_nhds h1
  obtain ⟨L, hLfin, hLsub⟩ := (krullTopology_mem_nhds_one_iff k Ω _).mp hopen
  haveI := hLfin
  let L' : IntermediateField k Ω := IntermediateField.normalClosure k L Ω
  haveI hL'fin : FiniteDimensional k L' := normalClosure.is_finiteDimensional k L Ω
  haveI hL'norm : Normal k L' := inferInstance
  haveI hL'gal : IsGalois k L' := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  refine ⟨L'.fixingSubgroup, inferInstance, IntermediateField.fixingSubgroup_isOpen L', ?_⟩
  intro n hn
  exact hLsub (IntermediateField.fixingSubgroup_le (IntermediateField.le_normalClosure L) hn)

/-- **Separation from the inertia subgroup.**  An element `g ∉ I_A` can be separated from `I_A` by
an open subgroup of `G_k` containing `I_A`. -/
theorem exists_isOpen_subgroup_ge_inertiaSub_notMem (A : ValuationSubring Ω) {g : Ω ≃ₐ[k] Ω}
    (hg : g ∉ inertiaSub k Ω A) :
    ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
      inertiaSub k Ω A ≤ V ∧ g ∉ V := by
  classical
  by_cases hgD : g ∈ SSGRoute.decomp k A
  · -- `g` lies in the decomposition group but not in the inertia subgroup
    have hnotin : ¬ (∀ x : Ω, x ∈ A → A.valuation (g x - x) < 1) := by
      intro h
      exact hg ⟨hgD, h⟩
    push_neg at hnotin
    obtain ⟨x, hxA, hxval⟩ := hnotin
    have hxint : IsIntegral k x := IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic x)
    let L₀ : IntermediateField k Ω := IntermediateField.adjoin k ({x} : Set Ω)
    haveI hL₀fin : FiniteDimensional k L₀ :=
      IntermediateField.adjoin.finiteDimensional hxint
    let L : IntermediateField k Ω := IntermediateField.normalClosure k L₀ Ω
    haveI hLfin : FiniteDimensional k L := normalClosure.is_finiteDimensional k L₀ Ω
    haveI hLnorm : Normal k L := inferInstance
    haveI hLgal : IsGalois k L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
    haveI hLnormal : (L.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)).Normal :=
      IsGalois.fixingSubgroup_normal_of_isGalois L
    have hxL : x ∈ L := IntermediateField.le_normalClosure L₀
      (IntermediateField.subset_adjoin k ({x} : Set Ω) (Set.mem_singleton x))
    refine ⟨inertiaSub k Ω A ⊔ L.fixingSubgroup, ?_, le_sup_left, ?_⟩
    · have hmem : (((inertiaSub k Ω A ⊔ L.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω))) :
            Set (Ω ≃ₐ[k] Ω)) ∈ nhds (1 : Ω ≃ₐ[k] Ω) :=
        Filter.mem_of_superset
          ((IntermediateField.fixingSubgroup_isOpen L).mem_nhds L.fixingSubgroup.one_mem)
          (fun y hy => Subgroup.mem_sup_right hy)
      exact Subgroup.isOpen_of_mem_nhds _ hmem
    · intro hmem
      have hmem₂ : g ∈ ((inertiaSub k Ω A : Set (Ω ≃ₐ[k] Ω)) *
          (L.fixingSubgroup : Set (Ω ≃ₐ[k] Ω))) := by
        have h := (Subgroup.mul_normal (inertiaSub k Ω A) L.fixingSubgroup).symm
        rw [h]
        exact hmem
      rw [Set.mem_mul] at hmem₂
      obtain ⟨i, hi, γ, hγ, hgiγ⟩ := hmem₂
      have hγx : γ x = x := (IntermediateField.mem_fixingSubgroup_iff L γ).mp hγ x hxL
      have hix : i x = g x := by
        rw [← hgiγ, AlgEquiv.mul_apply, hγx]
      exact absurd (hix ▸ hi.2 x hxA) (not_lt.mpr hxval)
  · -- `g` is outside the decomposition group, which is closed
    obtain ⟨N, hNnorm, hNopen, hN⟩ :=
      exists_openNormal_forall_mul_notMem k Ω A (SSGRoute.decomp k A : Set (Ω ≃ₐ[k] Ω))
        (isClosed_decomp_ssg k Ω A) hgD
    haveI : N.Normal := hNnorm
    refine ⟨inertiaSub k Ω A ⊔ N, ?_, le_sup_left, ?_⟩
    · have hmem : (((inertiaSub k Ω A ⊔ N : Subgroup (Ω ≃ₐ[k] Ω))) : Set (Ω ≃ₐ[k] Ω)) ∈
          nhds (1 : Ω ≃ₐ[k] Ω) :=
        Filter.mem_of_superset (hNopen.mem_nhds N.one_mem)
          (fun y hy => Subgroup.mem_sup_right hy)
      exact Subgroup.isOpen_of_mem_nhds _ hmem
    · intro hmem
      have hmem₂ : g ∈ ((inertiaSub k Ω A : Set (Ω ≃ₐ[k] Ω)) * (N : Set (Ω ≃ₐ[k] Ω))) := by
        have h := (Subgroup.mul_normal (inertiaSub k Ω A) N).symm
        rw [h]
        exact hmem
      rw [Set.mem_mul] at hmem₂
      obtain ⟨i, hi, n, hn, hin⟩ := hmem₂
      have hD : g * n⁻¹ ∈ SSGRoute.decomp k A := by
        rw [← hin]
        have h1 : (i * n) * n⁻¹ = i := by group
        rw [h1]
        exact inertiaSub_le_decomp k Ω A hi
      exact hN n⁻¹ (N.inv_mem hn) hD

/-- **The intersection of the open subgroups containing `I_A` is `I_A`.** -/
theorem mem_inertiaSub_of_forall_mem_isOpen_ge (A : ValuationSubring Ω) {g : Ω ≃ₐ[k] Ω}
    (h : ∀ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) →
      inertiaSub k Ω A ≤ V → g ∈ V) : g ∈ inertiaSub k Ω A := by
  by_contra hg
  obtain ⟨V, hVopen, hIV, hgV⟩ := exists_isOpen_subgroup_ge_inertiaSub_notMem k Ω A hg
  exact hgV (h V hVopen hIV)

/-- **The decomposition group is contained in `I_A · closure (zpowers σ)` for a Frobenius lift
`σ`.**  For `δ ∈ D_A` and every open subgroup `V ⊇ I_A`, the generation condition supplies
`m` with `δ * σ^m ∈ V`; a compactness argument over these `V` then produces a single
`x ∈ closure (zpowers σ)` with `δ * x ∈ I_A`. -/
theorem decomp_le_inertia_sup_closure (A : ValuationSubring Ω) (σ : Ω ≃ₐ[k] Ω)
    (hσ : IsFrobLift k A σ) :
    SSGRoute.decomp k A ≤ inertiaSub k Ω A ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ) := by
  classical
  haveI : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  intro δ hδ
  let L : OpenSubgroupsAbove k Ω A → Set (Ω ≃ₐ[k] Ω) :=
    fun i => {x | δ * x ∈ (i.1 : Set (Ω ≃ₐ[k] Ω))}
  have hLclosed : ∀ i, IsClosed (L i) := fun i =>
    (Subgroup.isClosed_of_isOpen i.1 i.2.1).preimage (continuous_const.mul continuous_id)
  have hFIP : ∀ u : Finset (OpenSubgroupsAbove k Ω A),
      (((Subgroup.topologicalClosure (Subgroup.zpowers σ) : Subgroup (Ω ≃ₐ[k] Ω)) :
        Set (Ω ≃ₐ[k] Ω)) ∩ ⋂ i ∈ u, L i).Nonempty := by
    intro u
    have key : ∃ W : Subgroup (Ω ≃ₐ[k] Ω),
        IsOpen (W : Set (Ω ≃ₐ[k] Ω)) ∧ inertiaSub k Ω A ≤ W ∧
        ∀ i ∈ u, W ≤ i.1 := by
      induction u using Finset.induction_on with
      | empty => exact ⟨⊤, isOpen_univ, le_top, by intro i hi; exact absurd hi (Finset.notMem_empty i)⟩
      | insert a s ha ih =>
        obtain ⟨W, hWo, hIW, hWle⟩ := ih
        refine ⟨W ⊓ a.1, hWo.inter a.2.1, le_inf hIW a.2.2, ?_⟩
        intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact inf_le_right
        · exact le_trans inf_le_left (hWle i hi)
    obtain ⟨W, hWo, hIW, hWle⟩ := key
    obtain ⟨m, hm⟩ := hσ.mul_zpow_mem (V := W) hWo hIW hδ
    refine ⟨σ ^ m, Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩), ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    exact hWle i hi hm
  have hne : (((Subgroup.topologicalClosure (Subgroup.zpowers σ) : Subgroup (Ω ≃ₐ[k] Ω)) :
        Set (Ω ≃ₐ[k] Ω)) ∩ ⋂ i : OpenSubgroupsAbove k Ω A, L i).Nonempty :=
    (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers σ)).isCompact.inter_iInter_nonempty
      L hLclosed hFIP
  obtain ⟨x, hxC, hxL⟩ := hne
  have hxL' : ∀ i : OpenSubgroupsAbove k Ω A, x ∈ L i := by
    simpa only [Set.mem_iInter] using hxL
  have hdxI : δ * x ∈ inertiaSub k Ω A := by
    apply mem_inertiaSub_of_forall_mem_isOpen_ge k Ω A
    intro V hVopen hIV
    exact hxL' ⟨V, hVopen, hIV⟩
  have hδx : δ = (δ * x) * x⁻¹ := by group
  rw [hδx]
  exact mul_mem (Subgroup.mem_sup_left hdxI)
    (Subgroup.mem_sup_right ((Subgroup.topologicalClosure (Subgroup.zpowers σ)).inv_mem hxC))

end Aux

/-! ## An abstract cyclic-quotient criterion

The following group-theoretic statement is the heart of the triviality of `I_A ⊓ closure (zpowers σ)`.
It says that an element `x` which is approximable by powers of `σ`, and which lies in a subgroup
`K` such that `σ` generates `G ⧸ K`, must lie in `N` as soon as `N.index ∣ K.index`. -/

/-- **A cyclic-quotient criterion for containment of a subgroup.**  Let `G` be a topological group,
`K, N ⊴ G` open subgroups, and `σ, x ∈ G` with `x` approximable by powers of `σ` (`hxcl`) and `σ`
generating `G ⧸ K` (`hgen`), with `N.index ∣ K.index`.  Then `x ∈ N`.

Indeed, `hgen` exhibits `G ⧸ K` as cyclic generated by the class of `σ`, whose order is therefore
`K.index`; `x ∈ closure (zpowers σ)` supplies `σ ^ e ∈ K ⊓ x • N` for some `e`, and `σ ^ e ∈ K`
forces `K.index ∣ e`; since `N.index ∣ K.index`, the class of `σ` in `G ⧸ N` has `(e.natAbs)`-th
power `1`, i.e. `σ ^ e ∈ N`; finally `σ ^ e ∈ x • N` gives `x ∈ N`. -/
theorem mem_of_index_dvd_of_zpowers {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SeparatelyContinuousMul G]
    {K N : Subgroup G} [K.Normal] [N.Normal] (hKopen : IsOpen (K : Set G))
    (hNopen : IsOpen (N : Set G)) (σ x : G)
    (hgen : ∀ δ : G, ∃ e : ℤ, δ⁻¹ * σ ^ e ∈ K) (hdvd : N.index ∣ K.index)
    (hxK : x ∈ K) (hxcl : ∀ U : Set G, IsOpen U → x ∈ U → ∃ e : ℤ, σ ^ e ∈ U) :
    x ∈ N := by
  have hcardK : Nat.card (G ⧸ K) = K.index := (Subgroup.index_eq_card K).symm
  have hcardN : Nat.card (G ⧸ N) = N.index := (Subgroup.index_eq_card N).symm
  have hgen' : ∀ y : G ⧸ K, y ∈ Subgroup.zpowers (QuotientGroup.mk' K σ) := by
    intro y
    obtain ⟨δ, rfl⟩ := QuotientGroup.mk'_surjective K y
    obtain ⟨e, he⟩ := hgen δ
    refine Subgroup.mem_zpowers_iff.mpr ⟨e, ?_⟩
    have h1 : (QuotientGroup.mk' K δ)⁻¹ * (QuotientGroup.mk' K σ) ^ e = 1 := by
      have hk : δ⁻¹ * σ ^ e ∈ (QuotientGroup.mk' K).ker := by
        rw [QuotientGroup.ker_mk']; exact he
      have h0 : QuotientGroup.mk' K (δ⁻¹ * σ ^ e) = 1 := MonoidHom.mem_ker.mp hk
      rwa [map_mul, map_inv, map_zpow] at h0
    exact (inv_mul_eq_one.mp h1).symm
  have hord : orderOf (QuotientGroup.mk' K σ) = K.index := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen', hcardK]
  obtain ⟨e, heK, heN⟩ : ∃ e : ℤ, σ ^ e ∈ K ∧ σ ^ e ∈ (x : G) • (N : Set G) := by
    have hopen : IsOpen ((K : Set G) ∩ ((x : G) • (N : Set G))) :=
      hKopen.inter (hNopen.leftCoset x)
    have hmem : x ∈ (K : Set G) ∩ ((x : G) • (N : Set G)) :=
      ⟨hxK, ⟨1, N.one_mem, by simp⟩⟩
    obtain ⟨e, he⟩ := hxcl _ hopen hmem
    exact ⟨e, he.1, he.2⟩
  have hpowK : (QuotientGroup.mk' K σ) ^ e = 1 := by
    have hk : σ ^ e ∈ (QuotientGroup.mk' K).ker := by
      rw [QuotientGroup.ker_mk']; exact heK
    have h0 : QuotientGroup.mk' K (σ ^ e) = 1 := MonoidHom.mem_ker.mp hk
    rwa [map_zpow] at h0
  have heKz : (K.index : ℤ) ∣ e := by
    have h1 : ((orderOf (QuotientGroup.mk' K σ) : ℕ) : ℤ) ∣ e :=
      orderOf_dvd_iff_zpow_eq_one.mpr hpowK
    rwa [hord] at h1
  have heKdvd : K.index ∣ e.natAbs := by
    have h : ((K.index : ℤ)).natAbs ∣ e.natAbs := Int.natAbs_dvd_natAbs.mpr heKz
    rwa [Int.natAbs_natCast] at h
  have heNdvd : N.index ∣ e.natAbs := dvd_trans hdvd heKdvd
  have heNpow : (QuotientGroup.mk' N σ) ^ e.natAbs = 1 := by
    have h1 : orderOf (QuotientGroup.mk' N σ) ∣ N.index := by
      rw [← hcardN]; exact orderOf_dvd_natCard _
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_trans h1 heNdvd)
  have hσeN : σ ^ e ∈ N := by
    have h2 : (QuotientGroup.mk' N σ) ^ e = 1 := by
      obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg e
      · have hmabs : e.natAbs = m := by rw [hm]; simp
        rw [hm, zpow_natCast, ← hmabs, heNpow]
      · have hmabs : e.natAbs = m := by rw [hm]; simp
        rw [hm, zpow_neg, zpow_natCast, ← hmabs, heNpow, inv_one]
    have h0 : QuotientGroup.mk' N (σ ^ e) = 1 := by rwa [map_zpow]
    have hk : σ ^ e ∈ (QuotientGroup.mk' N).ker := MonoidHom.mem_ker.mpr h0
    rwa [QuotientGroup.ker_mk'] at hk
  obtain ⟨n, hn, hxn⟩ := Set.mem_smul_set.mp heN
  have hx' : x = (x • n) * n⁻¹ := by rw [smul_eq_mul]; group
  rw [hx', hxn]
  exact N.mul_mem hσeN (N.inv_mem hn)

/-! ## Two elementary facts about level subgroups and the inertia of an ideal -/

/-- **The inertia subgroup is contained in every level subgroup**: an element of `G_k` acting
trivially on the residue field of `A` acts trivially, modulo the maximal ideal of `A`, on the level
ring `A ∩ M`.  This is immediate from the definitions: the elements of `A ∩ M` are elements of `A`
on which the inertia condition applies. -/
theorem inertiaSub_le_levelSub (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (M : IntermediateField k Ω) [FiniteDimensional k M]
    [Normal k M] :
    inertiaSub k Ω A ≤ Work.SSGRoute.levelSub A M := by
  intro g hg
  refine ⟨inertiaSub_le_decomp k Ω A hg, fun x => ?_⟩
  exact hg.2 _ (by
    simpa [IntermediateField.algebraMap_apply] using (ValuationSubring.mem_comap).mp x.2)

/-- **The inertia subgroup of an ideal is normal in its stabiliser**: if `τ` stabilises the ideal
`P` and `σ` lies in the inertia subgroup of `P`, then `τ σ τ⁻¹` lies in the inertia subgroup. -/
theorem conj_mem_inertia {G : Type*} [Group G] {R : Type*} [Ring R] [MulSemiringAction G R]
    (P : Ideal R) {τ : G} (hτ : τ ∈ MulAction.stabilizer G P) {σ : G}
    (hσ : σ ∈ Ideal.inertia G P) : τ * σ * τ⁻¹ ∈ Ideal.inertia G P := by
  haveI hN : (P.inertia (MulAction.stabilizer G P)).Normal := inferInstance
  have hσ' : (⟨σ, Ideal.inertia_le_stabilizer P hσ⟩ : MulAction.stabilizer G P) ∈
      P.inertia (MulAction.stabilizer G P) :=
    (Ideal.coe_mem_inertia (I := P) (H := MulAction.stabilizer G P)
      (σ := ⟨σ, Ideal.inertia_le_stabilizer P hσ⟩)).mp hσ
  have h := Subgroup.Normal.conj_mem hN _ hσ' (⟨τ, hτ⟩ : MulAction.stabilizer G P)
  exact (Ideal.coe_mem_inertia (I := P) (H := MulAction.stabilizer G P)
    (σ := (⟨τ, hτ⟩ : MulAction.stabilizer G P) *
      (⟨σ, Ideal.inertia_le_stabilizer P hσ⟩ : MulAction.stabilizer G P) *
      (⟨τ, hτ⟩ : MulAction.stabilizer G P)⁻¹)).mpr h

/-! ## The trivial intersection -/

/-- **The inertia subgroup meets the closed cyclic subgroup generated by a Frobenius lift
trivially.**  With `D = decomp k A`, `I = inertiaSub k Ω A` and `C = closure (zpowers σ)` where
`σ` is a Frobenius lift (`IsFrobLift k A σ`), any `x ∈ I ⊓ C` is `1`: a finite normal level `L`
with `x ∉ G_L` gives an open normal subgroup `N = D ⊓ G_L ≤ D` of finite index not containing `x`;
`level_residueDeg_dvd_general` supplies a finite normal level `M` whose level subgroup `K` has
index (the inertia degree of `M`) divisible by `N.index`; `σ` generates `D ⧸ K` by `IsFrobLift`;
and `x ∈ K` because `I ≤ levelSub A M`.  The abstract criterion
`mem_of_index_dvd_of_zpowers` then gives `x ∈ N`, a contradiction. -/
theorem inf_inertiaSub_topologicalClosure_eq_bot
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (σ : Ω ≃ₐ[k] Ω)
    (hσ : IsFrobLift k A σ) :
    inertiaSub k Ω A ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥ := by
  classical
  haveI hgalΩ : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hxne
  obtain ⟨hxI, hxC⟩ := Subgroup.mem_inf.mp hx
  -- (1) a finite normal level whose fixing subgroup does not contain `x`
  obtain ⟨y, hy⟩ : ∃ y : Ω, x y ≠ y := by
    by_contra h
    push_neg at h
    exact hxne (AlgEquiv.ext fun z => h z)
  let M₀ : IntermediateField k Ω := IntermediateField.adjoin k ({y} : Set Ω)
  haveI hM₀fin : FiniteDimensional k M₀ :=
    IntermediateField.adjoin.finiteDimensional
      (IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic y))
  let L : IntermediateField k Ω := IntermediateField.normalClosure k M₀ Ω
  haveI hLfin : FiniteDimensional k L := normalClosure.is_finiteDimensional k M₀ Ω
  haveI hLnorm : Normal k L := inferInstance
  haveI hLgal : IsGalois k L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hLfixnorm : (L.fixingSubgroup).Normal := IsGalois.fixingSubgroup_normal_of_isGalois L
  have hyL : y ∈ L := IntermediateField.le_normalClosure M₀
    (IntermediateField.subset_adjoin k ({y} : Set Ω) (Set.mem_singleton y))
  have hxfix : x ∉ L.fixingSubgroup := by
    intro hmem
    exact hy ((IntermediateField.mem_fixingSubgroup_iff L x).mp hmem y hyL)
  -- the decomposition group and the separating subgroup
  set D : Subgroup (Ω ≃ₐ[k] Ω) := SSGRoute.decomp k A with hDdef
  have hxD : x ∈ D := inertiaSub_le_decomp k Ω A hxI
  set N : Subgroup ↥D := (L.fixingSubgroup).comap (Subgroup.subtype D) with hNdef
  haveI hNnormal : N.Normal := Subgroup.Normal.comap hLfixnorm (Subgroup.subtype D)
  have hNopen : IsOpen (N : Set ↥D) :=
    (IntermediateField.fixingSubgroup_isOpen L).preimage continuous_subtype_val
  have hNindex_dvd : N.index ∣ (L.fixingSubgroup).index := by
    have h1 : N.index = (L.fixingSubgroup).relIndex D := by
      rw [hNdef, Subgroup.index_comap, Subgroup.range_subtype]
    rw [h1]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  have hxNfalse : (⟨x, hxD⟩ : ↥D) ∉ N := by
    intro hmem
    exact hxfix (Subgroup.mem_comap.mp (by rw [hNdef] at hmem; exact hmem))
  -- (2) a finite normal level whose inertia degree is divisible by `[G : G_L]`
  haveI hLfixfin : (L.fixingSubgroup).FiniteIndex :=
    (IntermediateField.restrictNormalHom_ker L).symm ▸
      Subgroup.finiteIndex_ker (AlgEquiv.restrictNormalHom ↥L)
  have hdpos : 0 < (L.fixingSubgroup).index := Nat.pos_of_ne_zero hLfixfin.index_ne_zero
  obtain ⟨M, hMfd, hMnorm, hMnf, hMdiv⟩ :=
    level_residueDeg_dvd_general k Ω A hA (L.fixingSubgroup).index hdpos
  haveI hMfdI : FiniteDimensional k M := hMfd
  haveI hMnormI : Normal k M := hMnorm
  haveI hMnfI : NumberField ↥M := hMnf
  set P := Work.SSGRoute.levelPrime k Ω A hA M with hPdef
  -- (3) the level subgroup of `M`, its index, and generation by `σ`
  set V : Subgroup (Ω ≃ₐ[k] Ω) :=
    (Ideal.inertia (↥M ≃ₐ[k] ↥M) P.asIdeal).comap (AlgEquiv.restrictNormalHom ↥M) with hVdef
  have hVopen : IsOpen (V : Set (Ω ≃ₐ[k] Ω)) := by
    refine Subgroup.isOpen_of_mem_nhds V (g := 1) ?_
    refine Filter.mem_of_superset
      ((IntermediateField.fixingSubgroup_isOpen M).mem_nhds M.fixingSubgroup.one_mem) ?_
    intro γ hγ
    have hker : γ ∈ (AlgEquiv.restrictNormalHom ↥M).ker := by
      rw [IntermediateField.restrictNormalHom_ker M]
      exact hγ
    simp only [hVdef, SetLike.mem_coe, Subgroup.mem_comap]
    rw [MonoidHom.mem_ker.mp hker]
    exact Subgroup.one_mem _
  have hIV : inertiaSub k Ω A ≤ V := by
    intro u hu
    show (AlgEquiv.restrictNormalHom ↥M) u ∈ Ideal.inertia (↥M ≃ₐ[k] ↥M) P.asIdeal
    exact (mem_levelSub_iff_mem_inertia k Ω A hA M ⟨u, inertiaSub_le_decomp k Ω A hu⟩).mp
      (inertiaSub_le_levelSub k Ω A M hu)
  set K : Subgroup ↥D := V.comap (Subgroup.subtype D) with hKdef
  have hK_eq : V.comap (Subgroup.subtype D) =
      (Work.SSGRoute.levelSub A M).comap (Subgroup.subtype D) := by
    ext δ
    show (AlgEquiv.restrictNormalHom ↥M) ((δ : Ω ≃ₐ[k] Ω)) ∈
        Ideal.inertia (↥M ≃ₐ[k] ↥M) P.asIdeal ↔
      (δ : Ω ≃ₐ[k] Ω) ∈ Work.SSGRoute.levelSub A M
    exact (mem_levelSub_iff_mem_inertia k Ω A hA M δ).symm
  have hKopen : IsOpen (K : Set ↥D) := hVopen.preimage continuous_subtype_val
  haveI hKnormal : K.Normal := by
    refine Subgroup.Normal.mk fun n hn g => ?_
    have hnV : (Subgroup.subtype D) n ∈ V :=
      Subgroup.mem_comap.mp (by rw [hKdef] at hn; exact hn)
    have hnI : (AlgEquiv.restrictNormalHom ↥M) (n : Ω ≃ₐ[k] Ω) ∈
        Ideal.inertia (↥M ≃ₐ[k] ↥M) P.asIdeal := by
      have h := hnV
      rw [hVdef] at h
      exact Subgroup.mem_comap.mp h
    have hgstab : (AlgEquiv.restrictNormalHom ↥M) (g : Ω ≃ₐ[k] Ω) ∈
        MulAction.stabilizer (↥M ≃ₐ[k] ↥M) P.asIdeal := by
      rw [← range_restrictNormalHom_eq_stabilizer A hA M]
      exact ⟨g, rfl⟩
    have hconj := conj_mem_inertia P.asIdeal hgstab hnI
    have hgoal : (AlgEquiv.restrictNormalHom ↥M) ((g * n * g⁻¹ : ↥D) : Ω ≃ₐ[k] Ω) ∈
        Ideal.inertia (↥M ≃ₐ[k] ↥M) P.asIdeal := by
      have hcoe : ((g * n * g⁻¹ : ↥D) : Ω ≃ₐ[k] Ω) =
          (g : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (g : Ω ≃ₐ[k] Ω)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcoe, map_mul, map_mul, map_inv]
      exact hconj
    rw [hKdef, hVdef]
    exact Subgroup.mem_comap.mpr (Subgroup.mem_comap.mpr hgoal)
  have hKindex : K.index = P.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    rw [hKdef, hK_eq]
    exact levelSub_comap_index_eq_inertiaDeg k Ω A hA M
  have hdvd : N.index ∣ K.index := by
    rw [hKindex]
    exact dvd_trans hNindex_dvd hMdiv
  have hgen : ∀ δ : ↥D, ∃ e : ℤ, δ⁻¹ * (⟨σ, hσ.mem_decomp⟩ : ↥D) ^ e ∈ K := by
    intro δ
    obtain ⟨e, he⟩ := hσ.2 V hVopen hIV (δ : Ω ≃ₐ[k] Ω) δ.2
    refine ⟨e, ?_⟩
    show (Subgroup.subtype D) (δ⁻¹ * (⟨σ, hσ.mem_decomp⟩ : ↥D) ^ e) ∈ V
    show (AlgEquiv.restrictNormalHom ↥M)
        ((δ⁻¹ * (⟨σ, hσ.mem_decomp⟩ : ↥D) ^ e : ↥D) : Ω ≃ₐ[k] Ω) ∈
      Ideal.inertia (↥M ≃ₐ[k] ↥M) P.asIdeal
    have hcoe : ((δ⁻¹ * (⟨σ, hσ.mem_decomp⟩ : ↥D) ^ e : ↥D) : Ω ≃ₐ[k] Ω) =
        (δ : Ω ≃ₐ[k] Ω)⁻¹ * σ ^ e := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    rw [hcoe]
    exact he
  have hxK : (⟨x, hxD⟩ : ↥D) ∈ K := by
    show (Subgroup.subtype D) (⟨x, hxD⟩ : ↥D) ∈ V
    exact hIV hxI
  have hxcl : ∀ U : Set ↥D, IsOpen U → (⟨x, hxD⟩ : ↥D) ∈ U → ∃ e : ℤ,
      (⟨σ, hσ.mem_decomp⟩ : ↥D) ^ e ∈ U := by
    intro U hU hxU
    obtain ⟨U', hU'open, hU'eq⟩ := isOpen_induced_iff.mp hU
    have hxU' : x ∈ U' := by
      have h : (⟨x, hxD⟩ : ↥D) ∈ Subtype.val ⁻¹' U' := by
        rw [hU'eq]; exact hxU
      simpa using h
    obtain ⟨z, hzU', hzzp⟩ := (mem_closure_iff.mp hxC) U' hU'open hxU'
    obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzzp
    refine ⟨e, ?_⟩
    have h : (Subgroup.subtype D) ((⟨σ, hσ.mem_decomp⟩ : ↥D) ^ e) ∈ U' := by
      simpa using hzU'
    rw [← hU'eq]
    exact h
  exact hxNfalse
    (mem_of_index_dvd_of_zpowers (K := K) (N := N) hKopen hNopen
      (⟨σ, hσ.mem_decomp⟩ : ↥D) (⟨x, hxD⟩ : ↥D) hgen hdvd hxK hxcl)


/-- **The inertia subgroup has a procyclic complement in the decomposition group.**

`I_A = Work.SSGRoute.inertiaSub k Ω A` (the elements of `D_A = SSGRoute.decomp k A` acting
trivially on the residue field of `A`, `Submission/Work/SSGRoute/InertiaDefs.lean`) is the inertia
subgroup of a finite place `A` of `Ω` over a number field `k`.  There is a Frobenius lift
`σ ∈ D_A` such that `D_A` is generated by `I_A` together with the closed cyclic subgroup generated
by `σ`, and these meet trivially: `D_A = I_A · closure(zpowers σ)` with `I_A ⊓ closure(zpowers σ)
= ⊥`.

ROUTE.  (1) For every finite Galois level `L/k` (`L ⊆ Ω`) with the prime `P_L` of `𝓞 L` below `A`,
the level decomposition group `D_L ≤ Gal(L/k)` (image of `D_A` under the restriction) has cyclic
quotient `D_L/I_L` (`I_L` = the elements acting trivially on the residue field of `L`), generated
by a Frobenius; equivalently `Work.SSGRoute.decomp_mod_inertia_cyclic`
(`Submission/Work/SSGRoute/decomp_mod_inertia_cyclic.lean`, PROVED): for every open `V ≤ G_k`
containing all inertia elements of `A`, `D_A/(D_A ⊓ V)` is cyclic.  The system of *generators* is a
cofiltered family of nonempty finite sets, and the sets
`S_V := {x ∈ D_A : the class of x generates D_A/(D_A ⊓ V)}` (`V` open normal, containing the
inertia) are nonempty, clopen, and directed (`S_{V ⊓ V'} ⊆ S_V ∩ S_{V'}`), so by compactness of
`D_A` there is `σ ∈ ⋂_V S_V`; then the class of `σ` generates `D_A/(D_A ⊓ V)` for every such `V`.

(2) `I_A` is closed and is the intersection of the open subgroups of `G_k` containing it, so
`D_A ≤ I_A · closure(zpowers σ)`: for `δ ∈ D_A`, the sets `K_V := {x ∈ closure(zpowers σ) : δ x⁻¹
∈ V}` are nonempty (some power of `σ` conjugates `δ` into `V`) closed subsets of the compact
`closure(zpowers σ)`, directed by inclusion; an element `x` of their intersection satisfies
`δ x⁻¹ ∈ ⋂_V V = I_A`, whence `δ ∈ I_A · closure(zpowers σ)`.
`I_A · closure(zpowers σ)` is closed (image of the compact `I_A × closure(zpowers σ)`), so it is all
of `D_A`, and `D_A ≤ I_A ⊔ closure(zpowers σ)` as subgroups.

(3) `I_A ⊓ closure(zpowers σ) = ⊥`: on every finite level `L` the image of `closure(zpowers σ)` in
the finite group `D_L` is the cyclic subgroup generated by the Frobenius, whose order modulo the
level inertia `I_L` is `f_L = |D_L/I_L|`, so its intersection with `I_L` is trivial; an element of
`I_A ⊓ closure(zpowers σ)` restricts to `1` on every level, hence is `1` (the finite levels
separate points of `G_k`).

Useful on disk: `Work.SSGRoute.decomp_mod_inertia_cyclic`, `Work.SSGRoute.decomp_inertia_quotient_cyclic`,
`Work.SSGRoute.decomp_mod_inertia_cyclic_over_K`, `Work.SSGRoute.level_inertia_surjective`,
`Work.SSGRoute.inertiaSub_le_decomp`, `Work.SSGRoute.inertiaSub_normal` (`InertiaDefs.lean`),
`Work.SSGRoute.decomp_conj`, `Work.SSGRoute.isFinPlace_smul_iff`. -/
theorem exists_frobenius_complement
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k A ∧
      SSGRoute.decomp k A ≤ inertiaSub k Ω A ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ) ∧
      inertiaSub k Ω A ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥ := by
  obtain ⟨σ, hσ⟩ := exists_frob_lift k Ω A hA
  exact ⟨σ, hσ.mem_decomp, decomp_le_inertia_sup_closure k Ω A σ hσ,
    inf_inertiaSub_topologicalClosure_eq_bot k Ω A hA σ hσ⟩

end Work.SSGRoute
