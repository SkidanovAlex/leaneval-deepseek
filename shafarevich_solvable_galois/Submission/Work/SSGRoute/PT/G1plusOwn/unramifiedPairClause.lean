import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.G1plusOwn.inertiaSub_normalClosure_inf_decomp
import Submission.Work.SSGRoute.PT.G1plusOwn.levelFree
import Submission.Work.SSGRoute.PT.levelPair_unramified_eq_zero
import Submission.Work.SSGRoute.unramifiedLevelFactorsAux

open scoped TensorProduct Pointwise Topology
open Filter

namespace Work.SSGRoute.PT.G1plusOwn

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section



/-! ## The compactness step -/

/-- **Separation from the closed normal closure.** -/
theorem exists_normal_isOpen_ge_notMem (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (H : Subgroup (Ω ≃ₐ[k] Ω)) {g : Ω ≃ₐ[k] Ω}
    (hg : g ∉ Subgroup.topologicalClosure (Subgroup.normalClosure H)) :
    ∃ V : Subgroup (Ω ≃ₐ[k] Ω), V.Normal ∧ IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧ H ≤ V ∧
      g ∉ V := by
  classical
  haveI hgal : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  set N : Subgroup (Ω ≃ₐ[k] Ω) :=
    Subgroup.topologicalClosure (Subgroup.normalClosure H) with hN
  haveI hNCN : (Subgroup.normalClosure (H : Set (Ω ≃ₐ[k] Ω))).Normal := inferInstance
  haveI hNnormal : N.Normal := by
    rw [hN]
    refine Subgroup.Normal.mk (fun n hn g => ?_)
    have hcont : Continuous (fun x : Ω ≃ₐ[k] Ω => g * x * g⁻¹) :=
      (continuous_const.mul continuous_id).mul continuous_const
    have hle : (Subgroup.topologicalClosure (Subgroup.normalClosure (H : Set (Ω ≃ₐ[k] Ω)))) ≤
        Subgroup.comap (MulAut.conj g).toMonoidHom
          (Subgroup.topologicalClosure (Subgroup.normalClosure (H : Set (Ω ≃ₐ[k] Ω)))) := by
      refine Subgroup.topologicalClosure_minimal (Subgroup.normalClosure (H : Set (Ω ≃ₐ[k] Ω))) ?_ ?_
      · intro x hx
        rw [Subgroup.mem_comap]
        show (MulAut.conj g) x ∈
          Subgroup.topologicalClosure (Subgroup.normalClosure (H : Set (Ω ≃ₐ[k] Ω)))
        rw [MulAut.conj_apply]
        exact Subgroup.le_topologicalClosure _ (Subgroup.Normal.conj_mem hNCN x hx g)
      · show IsClosed ((fun x : Ω ≃ₐ[k] Ω => g * x * g⁻¹) ⁻¹'
          (Subgroup.topologicalClosure (Subgroup.normalClosure (H : Set (Ω ≃ₐ[k] Ω))) :
            Set (Ω ≃ₐ[k] Ω)))
        exact (Subgroup.isClosed_topologicalClosure _).preimage hcont
    have := hle hn
    rw [Subgroup.mem_comap] at this
    simpa [MulAut.conj_apply] using this
  have hNclosed : IsClosed (N : Set (Ω ≃ₐ[k] Ω)) := Subgroup.isClosed_topologicalClosure _
  have hopen : IsOpen {y : Ω ≃ₐ[k] Ω | g * y ∉ N} :=
    hNclosed.isOpen_compl.preimage (continuous_const.mul continuous_id)
  have h1 : (1 : Ω ≃ₐ[k] Ω) ∈ {y : Ω ≃ₐ[k] Ω | g * y ∉ N} := by
    simp only [Set.mem_setOf_eq, mul_one]
    exact hg
  obtain ⟨E, hEfin, hEnorm, hEsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal k Ω {y : Ω ≃ₐ[k] Ω | g * y ∉ N}).mp
      (hopen.mem_nhds h1)
  haveI := hEfin
  haveI := hEnorm
  have hEopen : IsOpen ((E.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen E
  haveI hEnormal : (E.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)).Normal :=
    IsGalois.fixingSubgroup_normal_of_isGalois E
  refine ⟨(E.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) ⊔ N, inferInstance, ?_, ?_, ?_⟩
  · exact Subgroup.isOpen_mono le_sup_left hEopen
  · exact ((Subgroup.le_normalClosure).trans (Subgroup.le_topologicalClosure _)).trans le_sup_right
  · intro hgV
    have hword : g ∈ (((E.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) *
        (N : Set (Ω ≃ₐ[k] Ω))) := by
      rw [← Subgroup.mul_normal (E.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) N]
      exact hgV
    rw [Set.mem_mul] at hword
    obtain ⟨v, hv, n, hn, hgvn⟩ := hword
    have hvW : g * v⁻¹ ∉ N := hEsub (Subgroup.inv_mem _ hv)
    have hgv : g * v⁻¹ ∈ N := by
      have hconj : v * n * v⁻¹ ∈ N :=
        Subgroup.Normal.conj_mem (inferInstance : N.Normal) n hn v
      rwa [show v * n * v⁻¹ = g * v⁻¹ from by rw [hgvn]] at hconj
    exact hvW hgv

/-- **The compactness step.** -/
theorem exists_openNormal_inf_decomp_le (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (Z : Subgroup (Ω ≃ₐ[k] Ω))
    (hZI : Work.SSGRoute.inertiaSub k Ω A ≤ Z)
    (hZ : ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      U ⊓ SSGRoute.decomp k A ≤ Z) :
    ∃ V : Subgroup (Ω ≃ₐ[k] Ω), V.Normal ∧ IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
      Work.SSGRoute.inertiaSub k Ω A ≤ V ∧ V ⊓ SSGRoute.decomp k A ≤ Z := by
  classical
  haveI hgalΩ : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  obtain ⟨U, hUopen, hUle⟩ := hZ
  haveI : CompactSpace (Ω ≃ₐ[k] Ω) := inferInstance
  have hDclosed : IsClosed ((SSGRoute.decomp k A : Subgroup (Ω ≃ₐ[k] Ω)) :
      Set (Ω ≃ₐ[k] Ω)) :=
    Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A
  have hDcompact : IsCompact ((SSGRoute.decomp k A : Subgroup (Ω ≃ₐ[k] Ω)) :
      Set (Ω ≃ₐ[k] Ω)) := hDclosed.isCompact
  haveI : CompactSpace ↥(SSGRoute.decomp k A) := isCompact_iff_compactSpace.mp hDcompact
  by_contra hcon
  push_neg at hcon
  let ι := {V : Subgroup (Ω ≃ₐ[k] Ω) // V.Normal ∧ IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
    Work.SSGRoute.inertiaSub k Ω A ≤ V}
  have hι : Nonempty ι := ⟨⟨⊤, inferInstance, isOpen_univ, le_top⟩⟩
  let t : ι → Set ↥(SSGRoute.decomp k A) :=
    fun W => {x | (x : Ω ≃ₐ[k] Ω) ∈ W.1} ∩ {x | (x : Ω ≃ₐ[k] Ω) ∈ Z}ᶜ
  have htd : Directed (· ⊇ ·) t := by
    intro W₁ W₂
    haveI h1n : W₁.1.Normal := W₁.2.1
    haveI h2n : W₂.1.Normal := W₂.2.1
    refine ⟨⟨W₁.1 ⊓ W₂.1, inferInstance, W₁.2.2.1.inter W₂.2.2.1,
      le_inf W₁.2.2.2 W₂.2.2.2⟩, ?_, ?_⟩
    · intro x hx
      exact ⟨hx.1.1, hx.2⟩
    · intro x hx
      exact ⟨hx.1.2, hx.2⟩
  have hne : ∀ W : ι, (t W).Nonempty := by
    intro W
    have hnot : ¬ W.1 ⊓ SSGRoute.decomp k A ≤ Z :=
      hcon W.1 W.2.1 W.2.2.1 W.2.2.2
    obtain ⟨y, hy⟩ : ∃ y : Ω ≃ₐ[k] Ω, y ∈ W.1 ⊓ SSGRoute.decomp k A ∧ y ∉ Z := by
      by_contra hno
      exact hnot (fun y hy => by
        by_contra hyZ
        exact hno ⟨y, hy, hyZ⟩)
    exact ⟨⟨y, hy.1.2⟩, hy.1.1, hy.2⟩
  have hclosed : ∀ W : ι, IsClosed (t W) := by
    intro W
    have h1 : IsClosed {x : ↥(SSGRoute.decomp k A) | (x : Ω ≃ₐ[k] Ω) ∈ W.1} :=
      (Subgroup.isClosed_of_isOpen W.1 W.2.2.1).preimage continuous_subtype_val
    have h2 : IsClosed {x : ↥(SSGRoute.decomp k A) | (x : Ω ≃ₐ[k] Ω) ∈ Z}ᶜ := by
      refine IsOpen.isClosed_compl ?_
      refine Subgroup.isOpen_mono (H₁ := (U.comap (Subgroup.subtype (SSGRoute.decomp k A))))
        (H₂ := (Z.comap (Subgroup.subtype (SSGRoute.decomp k A))))
        (fun x hx => hUle ⟨hx, x.2⟩) ?_
      rw [Subgroup.coe_comap]
      exact hUopen.preimage continuous_subtype_val
    exact h1.inter h2
  have hcompact : ∀ W : ι, IsCompact (t W) := fun W => (hclosed W).isCompact
  have htot : (⋂ W, t W) ⊆ {x : ↥(SSGRoute.decomp k A) | (x : Ω ≃ₐ[k] Ω) ∈ Z} := by
    intro x hx
    rw [Set.mem_iInter] at hx
    by_contra hxZ
    have hxcl : (x : Ω ≃ₐ[k] Ω) ∈ Subgroup.topologicalClosure
        (Subgroup.normalClosure (Work.SSGRoute.inertiaSub k Ω A)) := by
      by_contra hcon2
      obtain ⟨V, hVn, hVo, hIV, hVg⟩ :=
        exists_normal_isOpen_ge_notMem k Ω (Work.SSGRoute.inertiaSub k Ω A) hcon2
      exact hVg (hx ⟨V, hVn, hVo, hIV⟩).1
    have hkey := Work.SSGRoute.PT.G1plusOwn.inertiaSub_normalClosure_inf_decomp k Ω A hA
    exact hxZ (hZI (hkey ⟨hxcl, x.2⟩))
  obtain ⟨x, hxmem⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd hne hcompact hclosed
  have hxnZ : (x : Ω ≃ₐ[k] Ω) ∉ Z := (Set.mem_iInter.mp hxmem hι.some).2
  have hxZ : (x : Ω ≃ₐ[k] Ω) ∈ Z :=
    htot (Set.mem_iInter.mpr fun W => Set.mem_iInter.mp hxmem W)
  exact hxnZ hxZ

/-! ## `finQW` is the prime of the level below `A`; a level fixed by `I_A` is unramified -/

/-- `finQW L A hA` is the prime of `𝓞 L` below `A`, i.e. it is `Work.SSGRoute.levelPrime`. -/
theorem finQW_eq_levelPrime (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    [NumberField ↥L] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.PT.finQW L A hA = Work.SSGRoute.levelPrime k Ω A hA L := by
  have hA' : A.comap (algebraMap k Ω) ≠ ⊤ := hA
  ext x
  rw [Work.SSGRoute.PT.finQW_spec L A hA x,
    Work.SSGRoute.primeOfLevel_mem_iff_k k Ω A hA L x]
  simp only [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥L) ↥L Ω]
  rfl

/-- **A level fixed pointwise by the inertia has trivial inertia at its prime below `A`.** -/
theorem isInertiaAt_eq_one_of_inertiaSub_le (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L] [NumberField ↥L]
    (h : Work.SSGRoute.inertiaSub k Ω A ≤ L.fixingSubgroup)
    (σ : ↥L ≃ₐ[k] ↥L)
    (hσ : SSGRoute.PTExt.IsInertiaAt (Work.SSGRoute.PT.finQW L A hA) σ) : σ = 1 := by
  haveI hgalΩ : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  have hA' : A.comap (algebraMap k Ω) ≠ ⊤ := hA
  have hbot : (Work.SSGRoute.inertiaSub k Ω A).map (AlgEquiv.restrictNormalHom L) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    have hx' : x ∈ L.fixingSubgroup := h hx
    rwa [← IntermediateField.restrictNormalHom_ker] at hx'
  have himg : Ideal.inertia (↥L ≃ₐ[k] ↥L)
      (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal = ⊥ := by
    have h2 := Work.SSGRoute.inertiaSub_image_eq_levelInertia k Ω A hA L
    rw [hbot] at h2
    exact h2.symm
  have hmem : σ ∈ Ideal.inertia (↥L ≃ₐ[k] ↥L)
      (Work.SSGRoute.PT.finQW L A hA).asIdeal :=
    (Work.SSGRoute.PT.isInertiaAt_iff_mem_inertia_local
      (Work.SSGRoute.PT.finQW L A hA) σ).mp hσ
  rw [finQW_eq_levelPrime k Ω L A hA, himg] at hmem
  simpa using hmem

/-! ## The arithmetic input of clause (6) -/

/-- **Clause (6)'s level input.** -/
theorem exists_unramified_level_factors' (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hramA : ¬ SSGRoute.IsRamifiedIn k K A)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hiner : ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (_ : Normal k L)
      (_ : NumberField ↥L),
      K ≤ L ∧ Work.SSGRoute.inertiaSub k Ω A ≤ L.fixingSubgroup ∧
      ∃ b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ) := by
  classical
  haveI hgalΩ : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  have hramK : Work.SSGRoute.inertiaSub k Ω A ≤ K.fixingSubgroup := by
    intro σ hσ
    by_contra hcon
    exact hramA ⟨σ, (Work.SSGRoute.mem_inertiaSub k Ω A σ).mp hσ, hcon⟩
  obtain ⟨U, hUnorm, hUopen, hUle⟩ :=
    exists_normal_inf_le_periodSub (T := T) (K := K) A hb hl
  haveI := hUnorm
  obtain ⟨V, hVnorm, hVopen, hVI, hVle⟩ :=
    exists_openNormal_inf_decomp_le k Ω A hA (periodSub (T := T) (K := K) A b hb)
      (inertiaSub_le_periodSub (T := T) (K := K) A hb hiner hramK)
      ⟨U, hUopen, hUle⟩
  haveI hKnormal : (K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)).Normal :=
    IsGalois.fixingSubgroup_normal_of_isGalois K
  haveI hVn : V.Normal := hVnorm
  have hWopen : IsOpen ((V ⊓ K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) :
      Set (Ω ≃ₐ[k] Ω)) := hVopen.inter K.fixingSubgroup_isOpen
  have hWfix : (IntermediateField.fixedField (V ⊓ K.fixingSubgroup)).fixingSubgroup =
      V ⊓ K.fixingSubgroup :=
    Work.SSGRoute.PT.fixingSubgroup_fixedField_of_isOpen _ hWopen
  have hWfd : FiniteDimensional k ↥(IntermediateField.fixedField (V ⊓ K.fixingSubgroup)) :=
    Work.SSGRoute.PT.finiteDimensional_fixedField_of_isOpen _ hWopen
  haveI : IsGalois k ↥(IntermediateField.fixedField (V ⊓ K.fixingSubgroup)) :=
    IsGalois.of_fixedField_normal_subgroup (V ⊓ K.fixingSubgroup)
  have hWnf : NumberField ↥(IntermediateField.fixedField (V ⊓ K.fixingSubgroup)) :=
    NumberField.of_module_finite k _
  refine ⟨IntermediateField.fixedField (V ⊓ K.fixingSubgroup), hWfd, inferInstance, hWnf, ?_, ?_,
    ?_⟩
  · exact (IntermediateField.le_iff_le (V ⊓ K.fixingSubgroup) K).mpr inf_le_right
  · rw [hWfix]
    exact le_inf hVI hramK
  · refine exists_factor_of_periodSub (T := T) (K := K) A hb ?_
    rw [hWfix, inf_comm]
    exact le_trans (le_inf (le_trans inf_le_left inf_le_left) inf_le_right) hVle


/-- Clause (6) of `G1⁺` over the abstract dictionary interface: at a good finite place `A` (not over
`p`, unramified in `K`), the pairing of two locally constant cocycles that both vanish on the
inertia `I_A` is `0` — "the Yoneda product of two unramified classes vanishes".

Certifiable (abstract) form of `G1plusOwn/g1FinHalf_unramified.lean` (filed 01:32, `by sorry`),
whose *type* mentions `G1pOwn.g1FinHalf` and hence reports `sorryAx` while
`E1aClean.localDictionary_natural_family` is sorried; here `pair` and the dictionary `βl` are
variables with the value formula `hpair` and the unramified clause `hβl_unr`.

Shape of `hpair`: the level data's `Algebra ↥K ↥L`-family is bound by `letI` at the canonical
instances, **not** by instance binders — the binder form is unsatisfiable for
`pair := G1pOwn.g1FinHalf`, whose type cannot mention an `Algebra ↥K ↥L` structure.  See
`PT/PING_s14_hpair_instances_and_clause4.md`.  A proved supply of `hpair` for
`pair := G1pOwn.g1FinHalf`, `βl := PT.finZB` is `G1plusOwn.g1FinHalf_hpair`.

Route.
1. `hpair` at a level `L ≥ K` at which `b` factors (`b = b₀ ∘ res_L`) and which is *unramified at
   `A`* turns the value into `χ L hKL (ι (levelPair (finZF …) (finZI …) (βl A hA a) ([b]_L)))`.
2. **Crux: a level that is simultaneously unramified at `A` and factors `b`.**  Both conditions
   are needed, and no existing result gives both:
   `exists_finiteNormal_fixingSubgroup_le_of_isOpen` gives, for an open `U ≤ Gal(Ω/k)`, a finite
   normal `L ≥ K` with `L.fixingSubgroup ≤ U` (only the *upper* bound), while
   `exists_level_factors_locConstOn` gives a level factoring `b` with no unramifiedness.
   Unramifiedness of the level at `A` is `I_A ≤ L.fixingSubgroup` (equivalently: the place
   `finQW L A hA` has trivial inertia in `Gal(↥L/k)`), i.e. `L ⊆ Ω^{I_A}`; factoring `b` on
   `decomp k A` holds as soon as `L.fixingSubgroup ∩ decomp k A` is inside the open normal
   constancy subgroup `U₀ ≤ Gal(Ω/k)` of `IsLocConstOn (decomp k A) b`.
   Both come from one compactness sandwich: the family of finite normal `L` with `K ≤ L ⊆ Ω^{I_A}`
   is directed by the compositum (which stays inside `Ω^{I_A}`), and
   `⋂_L (L.fixingSubgroup ∩ decomp k A) = I_A ∩ decomp k A ⊆ ⟨I_A, U₀ ∩ decomp k A⟩` (as
   `Gal(Ω/Ω^{I_A}) = I_A`); as `decomp k A` is compact (closed in the compact Krull topology),
   a single `L` of the family satisfies
   `L.fixingSubgroup ∩ decomp k A ≤ ⟨I_A, U₀ ∩ decomp k A⟩`, and then `b` is constant on the
   `L.fixingSubgroup ∩ decomp k A`-cosets because it is constant on `U₀`-cosets and vanishes on
   `I_A` (`hiner` with the cocycle identity `b (h ι) = b h + h • b ι = b h`; note `b 1 = 0` from
   the cocycle identity at `(1,1)`, so `b` vanishes on `U₀ ∩ decomp k A`).
   Splitting this level-existence off into its own auxiliary result is expected; the exact form it
   needs is `∃ L, K ≤ L ∧ L.fixingSubgroup ∩ decomp k A ≤ ⟨I_A, U₀ ∩ decomp k A⟩ ∧
   I_A ≤ L.fixingSubgroup` — the intersection with `decomp k A` is *not* droppable.
3. `hβl_unr` makes `βl A hA a` unramified at the base place `ofFinite (finQ K A hA)`, so the proved
   `PT.levelPair_unramified_eq_zero` (`PT/levelPair_unramified_eq_zero.lean`) kills the level value.
4. `ι 0 = 0` and `χ 0 = 0` (from `hχadd` applied to `0 + 0`).

The consumer instantiates `βl := PT.finZB`, `pair := G1pOwn.g1FinHalf`,
`hpair := G1pOwn.g1FinHalf_hpair` (proved), `hβl_unr := PT.finZB_unramified` (proved). -/
theorem unramifiedPairClause
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (βl : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ((Ω ≃ₐ[k] Ω) → M) →
        CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) 1)
    (hβl_unr : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ b : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) →
        SSGRoute.PTExt.IsUnramifiedExt (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (βl A hA b))
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
      ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hpair : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      ∀ (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
        (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L),
        letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
        letI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
        letI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
        ∀ (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)),
        pair (SSGRoute.decomp k A) a b =
          χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
            (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
              (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
              (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀))))
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hpA : ¬ A.valuation (p : Ω) < 1) (hramA : ¬ SSGRoute.IsRamifiedIn k K A)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hiner : ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0) :
    pair (SSGRoute.decomp k A) a b = 0 := by
  classical
  -- ## a finite Galois level `L ≥ K`, unramified at `A`, on which `b` factors
  obtain ⟨L, hLfd, hLnorm, hLnf, hKL, hLI, b₀, hb₀⟩ :=
    exists_unramified_level_factors' p k Ω K T M A hA hramA b hb.1 hb.2
      (fun σ hσ => (hiner σ hσ).2)
  letI : FiniteDimensional k L := hLfd
  letI : Normal k L := hLnorm
  haveI : IsGalois k L :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero (F := k) (E := ↥L)
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  haveI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- ## the value formula at that level
  rw [hpair A hA a b ha.2 hb.2 hb.1 L hKL b₀ hb₀]
  -- ## the level pairing vanishes: `βl A hA a` is unramified, and so is the level at `A`
  have hz : SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
      (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
      (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb.1 b₀ hb₀) = 0 := by
    have hw' : NK.GlobalCFT.Place.LiesOver
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) :=
      (Work.SSGRoute.PT.place_glue_level k Ω K L hKL A hA (Work.SSGRoute.PT.finQ K A hA)
        (fun x => Work.SSGRoute.PT.finQ_spec K A hA x)
        (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y)).1
    refine Work.SSGRoute.PT.levelPair_unramified_eq_zero (k := k) (K := ↥K)
      (M := SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
      (w := NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (L := ↥L)
      (q' := Work.SSGRoute.PT.finQW L A hA) (hw' := hw')
      (hunr := fun σ hσ => isInertiaAt_eq_one_of_inertiaSub_le k Ω A hA L hLI σ hσ)
      (f := Work.SSGRoute.PT.finZF hKL A hA) (hf := Work.SSGRoute.PT.finZF_spec hKL A hA)
      (ι := Work.SSGRoute.PT.finZI hKL A hA) ?_
      (y := βl A hA a)
      (hy := hβl_unr A hA hpA hramA a ha.1 ha.2 (fun σ hσ => (hiner σ hσ).1))
      (h := Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb.1 b₀ hb₀)
    intro u
    simp only [Work.SSGRoute.PT.finZI]
    exact Work.SSGRoute.PT.localUnitsMapAt_spec k ↥K ↥L
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) hw'
      (Work.SSGRoute.PT.finZF hKL A hA) (Work.SSGRoute.PT.finZF_spec hKL A hA) u
  rw [hz, Work.SSGRoute.PT.iota_zero]
  -- ## `χ 0 = 0`
  have hχ0 : χ L hKL (0 : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2) = 0 := by
    have h := hχadd L hKL 0 0 (by simp) (by simp)
    rw [add_zero] at h
    exact add_left_cancel (show χ L hKL 0 + χ L hKL 0 = χ L hKL 0 + 0 from by
      rw [add_zero]; exact h.symm)
  exact hχ0


end

end Work.SSGRoute.PT.G1plusOwn
