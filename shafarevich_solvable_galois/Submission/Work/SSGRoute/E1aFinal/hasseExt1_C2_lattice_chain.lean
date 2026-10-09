import Mathlib
import Submission.Work.SSGRoute.E1aFinal.HasseDefs
import Submission.Work.SSGRoute.E1aFinal.C2Chain.Basic
import Submission.Work.SSGRoute.E1aFinal.C2Chain.Eigenspace
import Submission.Work.SSGRoute.E1aFinal.C2Chain.coeff_submodule_finite
import Submission.Work.SSGRoute.E1aFinal.C2Chain.coeff_submodule_free

/-!
# The lattice chain of an involution (Shafarevich, (S3))

Everything happens with `Coeff = ULift ℤ`; we remove the competing `ULift`-scalar instances so
that `c • x` always denotes the module action.
-/

set_option maxHeartbeats 8000000

attribute [-instance] ULift.module
attribute [-instance] ULift.smulLeft
attribute [-instance] ULift.smulZeroClass
attribute [-instance] ULift.distribSMul
attribute [-instance] ULift.distribMulAction
attribute [-instance] ULift.mulAction
attribute [-instance] ULift.smulWithZero
attribute [-instance] ULift.mulActionWithZero

namespace Work.SSGRoute.E1aFinal

open CategoryTheory

open scoped BigOperators

noncomputable section

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]

/-- The subrepresentation of `M` on an `H`-stable submodule. -/
abbrev subRep {σ : Ω ≃ₐ[k] Ω}
    (M : Rep.{0} SSGRoute.PTExt.Coeff ↥(Subgroup.zpowers (SSGRoute.res k K σ)))
    (L : Submodule SSGRoute.PTExt.Coeff M.V)
    (hL : ∀ (h : ↥(Subgroup.zpowers (SSGRoute.res k K σ))), ∀ x ∈ L, M.ρ h x ∈ L) :
    Rep.{0} SSGRoute.PTExt.Coeff ↥(Subgroup.zpowers (SSGRoute.res k K σ)) :=
  Rep.of ((Subrepresentation.toRepresentation (ρ := M.ρ)
    { toSubmodule := L
      apply_mem_toSubmodule := fun g x hx => hL g x hx })
    : Representation SSGRoute.PTExt.Coeff ↥(Subgroup.zpowers (SSGRoute.res k K σ)) ↥L)

lemma subRep_rho_apply {σ : Ω ≃ₐ[k] Ω}
    {M : Rep.{0} SSGRoute.PTExt.Coeff ↥(Subgroup.zpowers (SSGRoute.res k K σ))}
    {L : Submodule SSGRoute.PTExt.Coeff M.V}
    {hL : ∀ (h : ↥(Subgroup.zpowers (SSGRoute.res k K σ))), ∀ x ∈ L, M.ρ h x ∈ L}
    {h : ↥(Subgroup.zpowers (SSGRoute.res k K σ))} {x : M.V} (hx : x ∈ L) :
    (subRep M L hL).ρ h ⟨x, hx⟩ = ⟨M.ρ h x, hL h x hx⟩ := by
  simp only [subRep, Rep.of_ρ]
  exact LinearMap.restrict_apply _ _

/-- **(S3) The lattice chain.**  Every finite free `ℤ`-module `M` with an action of
`H = ⟨σ̄⟩ ≅ ℤ/2` admits a finite chain of `H`-stable `ℤ`-lattices
`M₀ ⊆ M₁ ⊆ … ⊆ Mₙ = M` in which each step is an index-two extension with trivial action on the
quotient, and whose bottom term `M₀` is *split* (a `ℤ`-basis on which `σ̄` acts diagonally with
eigenvalues `±1`).  Take `M₀ = M^{σ̄} ⊕ M^{-σ̄}` and refine the filtration of the `2`-torsion
quotient `M/M₀`.

Concretely: `Mseq : Fin (n+1) → Rep Coeff ↥H` with finiteness/freeness instances for each term,
`IsSplit (Mseq 0)`, `StepData (Mseq i.castSucc) (Mseq i.succ)` for every `i : Fin n`, and
`Mseq (Fin.last n) ≅ M`. -/
theorem hasseExt1_C2_lattice_chain (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (M : Rep.{0} SSGRoute.PTExt.Coeff ↥(Subgroup.zpowers (SSGRoute.res k K σ)))
    [Module.Finite ℤ M.V] [Module.Free ℤ M.V] :
    ∃ (n : ℕ) (Mseq : Fin (n + 1) → Rep.{0} SSGRoute.PTExt.Coeff
        ↥(Subgroup.zpowers (SSGRoute.res k K σ)))
      (hfin : ∀ i, Module.Finite ℤ (Mseq i).V) (hfree : ∀ i, Module.Free ℤ (Mseq i).V),
      IsSplit (Mseq 0) ∧
      (∀ i : Fin n, StepData (Mseq i.castSucc) (Mseq i.succ)) ∧
      Nonempty (Mseq (Fin.last n) ≅ M) := by
  classical
  -- ### 1. the underlying chain of lattices
  obtain ⟨n, c, hc0, hctop, hcstab, hcstep⟩ :=
    exists_chain_twoStep (eigSum M) (M.ρ (gen (σ := σ)))
      (fun x => sub_rho_gen_mem_eigSum hσ x)
      (fun x => add_self_mem_eigSum hσ x)
      (finite_quotient_of_two_smul_mem (eigSum M) (fun x => add_self_mem_eigSum hσ x))
  -- ### 2. stability of each lattice under all of `H`
  have hcStabH : ∀ (i : Fin (n + 1)) (h : ↥(Subgroup.zpowers (SSGRoute.res k K σ))),
      ∀ x ∈ c i, M.ρ h x ∈ c i := by
    intro i h x hx
    rcases eq_one_or_eq_gen (K := K) hσ h with rfl | rfl
    · rw [map_one]; exact hx
    · exact hcstab i x hx
  -- ### 3. the representations
  let VpRep : Rep.{0} SSGRoute.PTExt.Coeff ↥(Subgroup.zpowers (SSGRoute.res k K σ)) :=
    subRep M (eigPlus M) (fun h x hx => smul_mem_eigPlus hσ h hx)
  let VmRep : Rep.{0} SSGRoute.PTExt.Coeff ↥(Subgroup.zpowers (SSGRoute.res k K σ)) :=
    subRep M (eigMinus M) (fun h x hx => smul_mem_eigMinus hσ h hx)
  let prodRep : Rep.{0} SSGRoute.PTExt.Coeff ↥(Subgroup.zpowers (SSGRoute.res k K σ)) :=
    Rep.of ((Representation.prod VpRep.ρ VmRep.ρ)
      : Representation SSGRoute.PTExt.Coeff ↥(Subgroup.zpowers (SSGRoute.res k K σ))
          (↥(eigPlus M) × ↥(eigMinus M)))
  let crep : Fin (n + 1) → Rep.{0} SSGRoute.PTExt.Coeff
      ↥(Subgroup.zpowers (SSGRoute.res k K σ)) :=
    fun i => subRep M (c i) (fun h x hx => hcStabH i h x hx)
  let Mseq : Fin (n + 2) → Rep.{0} SSGRoute.PTExt.Coeff
      ↥(Subgroup.zpowers (SSGRoute.res k K σ)) :=
    Fin.cases prodRep crep
  have hMseq0 : Mseq 0 = prodRep := Fin.cases_zero
  have hMseqS : ∀ i : Fin (n + 1), Mseq i.succ = crep i := fun i => Fin.cases_succ i
  -- ### 4. `Mseq 0 = VpRep × VmRep` is split
  haveI hfp : Module.Finite ℤ ↥(eigPlus M) := C2Chain.coeff_submodule_finite (eigPlus M)
  haveI hffp : Module.Free ℤ ↥(eigPlus M) := C2Chain.coeff_submodule_free (eigPlus M)
  haveI hfm : Module.Finite ℤ ↥(eigMinus M) := C2Chain.coeff_submodule_finite (eigMinus M)
  haveI hffm : Module.Free ℤ ↥(eigMinus M) := C2Chain.coeff_submodule_free (eigMinus M)
  have hVp_gen : ∀ x : ↥(eigPlus M), VpRep.ρ (gen (σ := σ)) x = x := by
    intro x
    apply Subtype.ext
    rw [subRep_rho_apply]
    exact mem_eigPlus.mp x.2
  have hVm_gen : ∀ x : ↥(eigMinus M), VmRep.ρ (gen (σ := σ)) x = -x := by
    intro x
    apply Subtype.ext
    rw [subRep_rho_apply]
    exact mem_eigMinus.mp x.2
  have hprod_gen : ∀ x : ↥(eigPlus M) × ↥(eigMinus M),
      prodRep.ρ (gen (σ := σ)) x =
        ((VpRep.ρ (gen (σ := σ))) x.1, (VmRep.ρ (gen (σ := σ))) x.2) := by
    intro x
    rw [show prodRep.ρ = Representation.prod VpRep.ρ VmRep.ρ from rfl]
    exact LinearMap.prodMap_apply _ _ _

  have hsplit : IsSplit prodRep := by
    refine ⟨Fin (Module.finrank ℤ ↥(eigPlus M)) ⊕ Fin (Module.finrank ℤ ↥(eigMinus M)),
      inferInstance,
      (Module.finBasis ℤ ↥(eigPlus M)).prod (Module.finBasis ℤ ↥(eigMinus M)), ?_⟩
    intro i
    rcases i with j | j
    · left
      have hb : (Module.finBasis ℤ ↥(eigPlus M)).prod (Module.finBasis ℤ ↥(eigMinus M))
          (Sum.inl j) = ((Module.finBasis ℤ ↥(eigPlus M)) j, 0) := by
        rw [Module.Basis.prod_apply, Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply]
      rw [hb, hprod_gen]
      refine Prod.ext ?_ ?_ <;> simp only [hVp_gen, hVm_gen, map_zero, neg_zero, Prod.fst_neg,
        Prod.snd_neg, Prod.fst_zero, Prod.snd_zero]
    · right
      have hb : (Module.finBasis ℤ ↥(eigPlus M)).prod (Module.finBasis ℤ ↥(eigMinus M))
          (Sum.inr j) = (0, (Module.finBasis ℤ ↥(eigMinus M)) j) := by
        rw [Module.Basis.prod_apply, Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply]
      rw [hb, hprod_gen]
      simp only [Prod.fst_zero, Prod.snd_zero, hVp_gen, hVm_gen, map_zero]
      refine Prod.ext ?_ ?_
      · show (0 : ↥(eigPlus M)) = -((0 : ↥(eigPlus M)))
        rw [neg_zero]
      · show -(Module.finBasis ℤ ↥(eigMinus M) j) = -(Module.finBasis ℤ ↥(eigMinus M) j)
        rfl
  have hmono : ∀ i : Fin (n + 1), c 0 ≤ c i := by
    intro i
    induction i using Fin.induction with
    | zero => exact le_rfl
    | succ j ih => exact le_trans ih (hcstep j).1
  -- ### 5. the step `prodRep → crep 0`
  have hstep0 : StepData prodRep (crep 0) := by
    let φ : (↥(eigPlus M) × ↥(eigMinus M)) →ₗ[SSGRoute.PTExt.Coeff] ↥(c 0) :=
      { toFun := fun q => ⟨(q.1 : M.V) + (q.2 : M.V), by
          rw [hc0]
          exact Submodule.add_mem _ (Submodule.mem_sup_left q.1.2)
            (Submodule.mem_sup_right q.2.2)⟩
        map_add' := by
          intro q r
          apply Subtype.ext
          simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add]
          abel
        map_smul' := by
          intro t q
          apply Subtype.ext
          simp only [Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, smul_add,
            RingHom.id_apply] }
    have hφ : ∀ q : ↥(eigPlus M) × ↥(eigMinus M),
        ((φ q : ↥(c 0)) : M.V) = (q.1 : M.V) + (q.2 : M.V) := fun q => rfl
    have hprod_apply : ∀ h q, prodRep.ρ h q =
        ((VpRep.ρ h) q.1, (VmRep.ρ h) q.2) := by
      intro h q
      rw [show prodRep.ρ = Representation.prod VpRep.ρ VmRep.ρ from rfl]
      exact LinearMap.prodMap_apply _ _ _
    have hVp_apply : ∀ h (x : ↥(eigPlus M)),
        (((VpRep.ρ h) x : ↥(eigPlus M)) : M.V) = M.ρ h (x : M.V) := by
      intro h x
      rw [subRep_rho_apply]
    have hVm_apply : ∀ h (x : ↥(eigMinus M)),
        (((VmRep.ρ h) x : ↥(eigMinus M)) : M.V) = M.ρ h (x : M.V) := by
      intro h x
      rw [subRep_rho_apply]
    have hc_apply : ∀ h (x : ↥(c 0)),
        (((crep 0).ρ h x : ↥(c 0)) : M.V) = M.ρ h (x : M.V) := by
      intro h x
      rw [subRep_rho_apply]
    have hint : ∀ h : ↥(Subgroup.zpowers (SSGRoute.res k K σ)), ∀ q,
        φ ((prodRep.ρ h) q) = (crep 0).ρ h (φ q) := by
      intro h q
      apply Subtype.ext
      rw [hφ ((prodRep.ρ h) q), hc_apply, hφ q, hprod_apply h, hVp_apply, hVm_apply, map_add]
    refine ⟨Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
      prodRep.ρ (crep 0).ρ φ hint), 0, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      have hab' : ((a.1 : M.V) + (a.2 : M.V)) = ((b.1 : M.V) + (b.2 : M.V)) := by
        have h := congrArg (fun y : ↥(c 0) => (y : M.V)) hab
        simpa only [Rep.hom_ofHom, LinearMap.toIntertwiningMap, hφ] using h
      have ha1 : M.ρ (gen (σ := σ)) (a.1 : M.V) = (a.1 : M.V) := mem_eigPlus.mp a.1.2
      have hb1 : M.ρ (gen (σ := σ)) (b.1 : M.V) = (b.1 : M.V) := mem_eigPlus.mp b.1.2
      have ha2 : M.ρ (gen (σ := σ)) (a.2 : M.V) = -(a.2 : M.V) := mem_eigMinus.mp a.2.2
      have hb2 : M.ρ (gen (σ := σ)) (b.2 : M.V) = -(b.2 : M.V) := mem_eigMinus.mp b.2.2
      have hP : (a.1 : M.V) - (b.1 : M.V) ∈ eigPlus M := by
        rw [mem_eigPlus, map_sub, ha1, hb1]
      have hM : (a.1 : M.V) - (b.1 : M.V) ∈ eigMinus M := by
        have hsum : (a.1 : M.V) - (b.1 : M.V) + ((a.2 : M.V) - (b.2 : M.V)) = 0 := by
          rw [show (a.1 : M.V) - (b.1 : M.V) + ((a.2 : M.V) - (b.2 : M.V)) =
              ((a.1 : M.V) + a.2) - ((b.1 : M.V) + b.2) from by abel, hab', sub_self]
        have h2 : (a.1 : M.V) - (b.1 : M.V) = -((a.2 : M.V) - (b.2 : M.V)) :=
          eq_neg_of_add_eq_zero_right (by simpa [add_comm] using hsum)
        rw [mem_eigMinus, h2, map_neg, map_sub, ha2, hb2]
        abel
      have hzero : (a.1 : M.V) - (b.1 : M.V) = 0 := by
        have hmem : (a.1 : M.V) - (b.1 : M.V) ∈ (⊥ : Submodule SSGRoute.PTExt.Coeff M.V) := by
          rw [← inf_eigPlus_eigMinus hσ]
          exact ⟨hP, hM⟩
        simpa using hmem
      have h1 : (a.1 : M.V) = (b.1 : M.V) := sub_eq_zero.mp hzero
      have h2 : (a.2 : M.V) = (b.2 : M.V) := by
        have h := hab'
        rw [h1] at h
        exact add_left_cancel h
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    · intro x
      have hx : (x : M.V) ∈ eigSum M := by rw [← hc0]; exact x.2
      obtain ⟨y1, hy1, y2, hy2, hy12⟩ := Submodule.mem_sup.mp hx
      refine ⟨(⟨y1, hy1⟩, ⟨y2, hy2⟩), Or.inr ?_⟩
      apply Subtype.ext
      show (x : M.V) - ((φ (⟨y1, hy1⟩, ⟨y2, hy2⟩) : ↥(c 0)) : M.V) = 0
      rw [hφ, sub_eq_zero]
      exact hy12.symm
    · refine ⟨0, ?_⟩
      simp
    · refine ⟨0, ?_⟩
      simp
  -- ### 6. the remaining steps `crep i → crep (i+1)`
  have hstepS : ∀ j : Fin n, StepData (crep j.castSucc) (crep j.succ) := by
    intro j
    obtain ⟨hle, m, hm_mem, hm_not, hm_cond⟩ := hcstep j
    let hincl : ↥(c j.castSucc) →ₗ[SSGRoute.PTExt.Coeff] ↥(c j.succ) :=
      Submodule.inclusion hle
    have hincl_val : ∀ (x : ↥(c j.castSucc)), ((hincl x : ↥(c j.succ)) : M.V) = (x : M.V) := by
      intro x
      simp only [hincl, Submodule.coe_inclusion]
    have hsub_apply : ∀ h (x : ↥(c j.castSucc)),
        (((crep j.castSucc).ρ h x : ↥(c j.castSucc)) : M.V) = M.ρ h (x : M.V) := by
      intro h x
      rw [subRep_rho_apply]
    have hsup_apply : ∀ h (x : ↥(c j.succ)),
        (((crep j.succ).ρ h x : ↥(c j.succ)) : M.V) = M.ρ h (x : M.V) := by
      intro h x
      rw [subRep_rho_apply]
    have hint : ∀ h x, hincl ((crep j.castSucc).ρ h x) = (crep j.succ).ρ h (hincl x) := by
      intro h x
      apply Subtype.ext
      rw [hincl_val, hsub_apply, hsup_apply, hincl_val]
    refine ⟨Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
      (crep j.castSucc).ρ (crep j.succ).ρ hincl hint),
      ⟨m, hm_mem⟩, ?_, ?_, ?_, ?_⟩
    · -- injectivity
      intro a b hab
      have hab' : ((a : M.V)) = (b : M.V) := by
        have h := congrArg (fun y : ↥(c j.succ) => (y : M.V)) hab
        simpa only [Rep.hom_ofHom, LinearMap.toIntertwiningMap, hincl_val] using h
      exact Subtype.ext hab'
    · -- the index-two condition
      intro x
      rcases hm_cond (x : M.V) x.2 with hx | hx
      · refine ⟨⟨(x : M.V), hx⟩, Or.inl ?_⟩
        apply Subtype.ext
        simp only [Rep.hom_ofHom, LinearMap.toIntertwiningMap, hincl_val]
      · refine ⟨⟨(x : M.V) - m, hx⟩, Or.inr ?_⟩
        apply Subtype.ext
        show (x : M.V) - ((hincl ⟨(x : M.V) - m, hx⟩ : ↥(c j.succ)) : M.V) = m
        rw [hincl_val]
        exact sub_sub_cancel _ _
    · -- `2 • m = m + m ∈ c j.castSucc`
      have hmD : m + m ∈ eigSum M := add_self_mem_eigSum hσ m
      have hcm : m + m ∈ c j.castSucc := hmono j.castSucc (by rw [hc0]; exact hmD)
      refine ⟨⟨m + m, hcm⟩, ?_⟩
      have hcm2 : m + m ∈ c j.succ := hle hcm
      have h2sm : (2 : ℤ) • (⟨m, hm_mem⟩ : ↥(c j.succ)) = ⟨m + m, hcm2⟩ := by
        rw [two_smul]
        exact Subtype.ext rfl
      rw [h2sm]
      exact Subtype.ext (by
        simp only [Rep.hom_ofHom, LinearMap.toIntertwiningMap]
        rw [hincl_val])
    · -- `σ̄ m - m ∈ c j.castSucc`
      have hmD : M.ρ (gen (σ := σ)) m - m ∈ eigSum M := sub_rho_gen_mem_eigSum hσ m
      have hcm : M.ρ (gen (σ := σ)) m - m ∈ c j.castSucc :=
        hmono j.castSucc (by rw [hc0]; exact hmD)
      refine ⟨⟨M.ρ (gen (σ := σ)) m - m, hcm⟩, ?_⟩
      have hcm2 : M.ρ (gen (σ := σ)) m - m ∈ c j.succ := hle hcm
      have hsm : ((crep j.succ).ρ (gen (σ := σ)) ⟨m, hm_mem⟩ - ⟨m, hm_mem⟩ :
            ↥(c j.succ)) = ⟨M.ρ (gen (σ := σ)) m - m, hcm2⟩ := by
        apply Subtype.ext
        change (((crep j.succ).ρ (gen (σ := σ)) ⟨m, hm_mem⟩ : ↥(c j.succ)) : M.V) -
          ((⟨m, hm_mem⟩ : ↥(c j.succ)) : M.V) = M.ρ (gen (σ := σ)) m - m
        rw [hsup_apply]
      rw [hsm]
      exact Subtype.ext (by
        simp only [Rep.hom_ofHom, LinearMap.toIntertwiningMap]
        rw [hincl_val])
  -- ### 7. the last term is `M`
  refine ⟨n + 1, Mseq, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.cases with
    | zero => rw [hMseq0]; exact inferInstance
    | succ j => rw [hMseqS j]; exact C2Chain.coeff_submodule_finite (c j)
  · intro i
    induction i using Fin.cases with
    | zero => rw [hMseq0]; exact inferInstance
    | succ j => rw [hMseqS j]; exact C2Chain.coeff_submodule_free (c j)
  · rw [hMseq0]; exact hsplit
  · intro i
    induction i using Fin.cases with
    | zero =>
        show StepData prodRep (crep 0)
        exact hstep0
    | succ j =>
        exact hstepS j
  · refine ⟨?_⟩
    have hlast : Mseq (Fin.last (n + 1)) = crep (Fin.last n) := hMseqS (Fin.last n)
    rw [hlast]
    let e : ↥(c (Fin.last n)) ≃ₗ[SSGRoute.PTExt.Coeff] M.V :=
      { toFun := fun x => (x : M.V)
        invFun := fun y => ⟨y, hctop.symm ▸ (by simp : y ∈ (⊤ : Submodule SSGRoute.PTExt.Coeff M.V))⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl
        map_add' := fun x y => rfl
        map_smul' := fun t x => rfl }
    refine Rep.mkIso (Representation.Equiv.mk e ?_)
    intro h
    ext x
    show (((crep (Fin.last n)).ρ h x : ↥(c (Fin.last n))) : M.V) = M.ρ h (x : M.V)
    rw [subRep_rho_apply]

end

end Work.SSGRoute.E1aFinal
