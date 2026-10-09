import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.PT.KrullCorrespondence
import Submission.Work.SSGRoute.PT.exists_level_factors_locConstOnTwo
import Submission.Work.SSGRoute.PT.G1plusOwn.inertiaSub_normalClosure_inf_decomp
import Submission.Work.SSGRoute.PT.G1plusOwn.unramifiedPairClause
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A finite Galois level, unramified at a place, at which a locally constant cocycle factors

`Work.SSGRoute.PT.exists_unramified_level_factors_local` is the arithmetic input of G1⁺'s clause
(6) (`Work.SSGRoute.PT.G1plusOwn.g1FinHalf_unramified`): given a finite place `A` of `Ω` unramified
in `K` and a locally constant `1`-cocycle `b` on the decomposition group `D_A` which vanishes on the
inertia `I_A`, there is a finite Galois level `L ⊇ K`, **unramified at `A`**
(`I_A ≤ L.fixingSubgroup`), on which `b|_(D_A)` factors.

The construction is the one recorded in the docstring of
`Submission/Work/SSGRoute/PT/G1plusOwn/exists_unramified_level_factors`:

* the constancy subgroup of `b` together with the inertia generates an open normal subgroup
  `V ⊇ I_A` of `G_k` whose intersection with `D_A` lies in `{b = 0}`; the last point is the
  **compactness/FIP step** `exists_openNormal_inf_decomp_le`;
* `L := Ω^V` is finite Galois over `k` and unramified at `A`, and `b` is `V ∩ D_A`-invariant
  (`b (g * u) = b g + g • b u = b g`), so `b|_(D_A)` factors through `Gal(L/k)`.
-/

open scoped Pointwise

noncomputable section

namespace Work.SSGRoute.PT

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **The compactness step: an open normal subgroup containing the inertia whose intersection with
the decomposition group lies in a prescribed clopen subset `Z ⊇ I_A` of `D_A`.**

`Z` is a clopen subset of the compact space `D_A = ↥(decomp k A)` containing the inertia; the
conclusion is an open normal `V ⊇ I_A` of `G_k` with `V ∩ D_A ⊆ Z`. -/
theorem exists_openNormal_inf_decomp_le (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (Z : Set ↥(SSGRoute.decomp k A)) (hZc : IsClosed Z) (hZo : IsOpen Z)
    (hIZ : ∀ σ : ↥(SSGRoute.decomp k A), (σ : Ω ≃ₐ[k] Ω) ∈ Work.SSGRoute.inertiaSub k Ω A →
      σ ∈ Z) :
    ∃ V : Subgroup (Ω ≃ₐ[k] Ω), V.Normal ∧ IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
      Work.SSGRoute.inertiaSub k Ω A ≤ V ∧
      ∀ σ : ↥(SSGRoute.decomp k A), (σ : Ω ≃ₐ[k] Ω) ∈ V → σ ∈ Z := by
  classical
  haveI hGalΩ : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  haveI hCpt : CompactSpace (Ω ≃ₐ[k] Ω) := inferInstance
  -- the closure of the normal closure of the inertia
  set C : Subgroup (Ω ≃ₐ[k] Ω) :=
    Subgroup.topologicalClosure
      (Subgroup.normalClosure (Work.SSGRoute.inertiaSub k Ω A)) with hCdef
  have hCclosed : IsClosed (C : Set (Ω ≃ₐ[k] Ω)) := by
    rw [hCdef]; exact Subgroup.isClosed_topologicalClosure _
  have hCnormal : C.Normal := Subgroup.is_normal_topologicalClosure _
  have hIC : Work.SSGRoute.inertiaSub k Ω A ≤ C := by
    rw [hCdef]
    exact le_trans (Subgroup.le_normalClosure) (Subgroup.le_topologicalClosure _)
  -- separation: every `σ ∉ C` is avoided by some open normal subgroup containing `I_A`
  have hsep : ∀ σ : Ω ≃ₐ[k] Ω, σ ∉ C →
      ∃ V : Subgroup (Ω ≃ₐ[k] Ω), V.Normal ∧ IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
        Work.SSGRoute.inertiaSub k Ω A ≤ V ∧ σ ∉ V := by
    intro σ hσC
    -- an open normal `V₀` whose every element `τ` satisfies `σ * τ ∉ C`
    have hs : {τ : Ω ≃ₐ[k] Ω | σ * τ ∉ C} ∈ nhds (1 : Ω ≃ₐ[k] Ω) := by
      have hopen : IsOpen {τ : Ω ≃ₐ[k] Ω | σ * τ ∉ C} :=
        hCclosed.isOpen_compl.preimage (continuous_const_mul σ)
      exact hopen.mem_nhds (by simp [hσC])
    obtain ⟨E, hEfin, hEnorm, hE⟩ :=
      (krullTopology_mem_nhds_one_iff_of_normal k Ω
        {τ : Ω ≃ₐ[k] Ω | σ * τ ∉ C}).mp hs
    haveI hEfd : FiniteDimensional k E := hEfin
    haveI hEn : Normal k E := hEnorm
    haveI hEg : IsGalois k E := inferInstance
    haveI hWn : E.fixingSubgroup.Normal := IsGalois.fixingSubgroup_normal_of_isGalois E
    have hVn : (C ⊔ E.fixingSubgroup).Normal := Subgroup.sup_normal C E.fixingSubgroup
    refine ⟨C ⊔ E.fixingSubgroup, hVn, ?_, le_trans hIC le_sup_left, ?_⟩
    · exact Subgroup.isOpen_mono (le_sup_right : E.fixingSubgroup ≤ C ⊔ E.fixingSubgroup)
        (IntermediateField.fixingSubgroup_isOpen E)
    · intro hmem
      have hmem' : σ ∈ ((C : Set (Ω ≃ₐ[k] Ω)) * (E.fixingSubgroup : Set (Ω ≃ₐ[k] Ω))) := by
        rw [← Subgroup.normal_mul C E.fixingSubgroup]; exact hmem
      obtain ⟨c, hc, v, hv, hcv⟩ := hmem'
      have hvC : σ * v⁻¹ ∈ C := by
        have : σ * v⁻¹ = c := by rw [← hcv]; group
        rw [this]; exact hc
      exact (hE (E.fixingSubgroup.inv_mem hv)) hvC
  -- the intersection of the open normal subgroups containing `I_A` lies in `C`
  have hInter : ∀ σ : Ω ≃ₐ[k] Ω,
      (∀ V : {V : Subgroup (Ω ≃ₐ[k] Ω) // V.Normal ∧ IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
        Work.SSGRoute.inertiaSub k Ω A ≤ V}, σ ∈ (V.1 : Set (Ω ≃ₐ[k] Ω))) → σ ∈ C := by
    intro σ hσ
    by_contra hσC
    obtain ⟨V, hVn, hVo, hVI, hσV⟩ := hsep σ hσC
    exact hσV (hσ ⟨V, hVn, hVo, hVI⟩)
  by_contra hcon
  -- for every `V` in the family there is `x ∈ V ∩ D_A \ Z`
  have hcon' : ∀ V : Subgroup (Ω ≃ₐ[k] Ω), V.Normal → IsOpen (V : Set (Ω ≃ₐ[k] Ω)) →
      Work.SSGRoute.inertiaSub k Ω A ≤ V → ∃ x : ↥(SSGRoute.decomp k A),
        (x : Ω ≃ₐ[k] Ω) ∈ V ∧ x ∉ Z := by
    intro V hVn hVo hVI
    by_contra h
    exact hcon ⟨V, hVn, hVo, hVI, fun x hx => by
      by_contra hxZ
      exact h ⟨x, hx, hxZ⟩⟩
  haveI : CompactSpace ↥(SSGRoute.decomp k A) := by
    have hd : IsClosed ((SSGRoute.decomp k A : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
      Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring (K := k) (K' := Ω) A
    exact isCompact_iff_compactSpace.mp hd.isCompact
  let t : {V : Subgroup (Ω ≃ₐ[k] Ω) // V.Normal ∧ IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
      Work.SSGRoute.inertiaSub k Ω A ≤ V} → Set ↥(SSGRoute.decomp k A) :=
    fun V => {x | (x : Ω ≃ₐ[k] Ω) ∈ (V.1 : Set (Ω ≃ₐ[k] Ω)) ∧ x ∉ Z}
  have htcl : ∀ V, IsClosed (t V) := by
    intro V
    have h1 : IsClosed {x : ↥(SSGRoute.decomp k A) |
        (x : Ω ≃ₐ[k] Ω) ∈ (V.1 : Set (Ω ≃ₐ[k] Ω))} :=
      (Subgroup.isClosed_of_isOpen V.1 V.2.2.1).preimage continuous_subtype_val
    have h2 : IsClosed {x : ↥(SSGRoute.decomp k A) | x ∉ Z} := hZo.isClosed_compl
    exact h1.inter h2
  have htnon : ∀ V, (t V).Nonempty := by
    intro V
    obtain ⟨x, hx⟩ := hcon' V.1 V.2.1 V.2.2.1 V.2.2.2
    exact ⟨x, hx.1, hx.2⟩
  have htd : Directed (· ⊇ ·) t := by
    intro V W
    haveI : V.1.Normal := V.2.1
    haveI : W.1.Normal := W.2.1
    refine ⟨⟨V.1 ⊓ W.1, inferInstance, V.2.2.1.inter W.2.2.1,
      le_inf V.2.2.2 W.2.2.2⟩, ?_, ?_⟩
    · intro x hx; exact ⟨hx.1.1, hx.2⟩
    · intro x hx; exact ⟨hx.1.2, hx.2⟩
  haveI : Nonempty {V : Subgroup (Ω ≃ₐ[k] Ω) // V.Normal ∧
      IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧ Work.SSGRoute.inertiaSub k Ω A ≤ V} :=
    ⟨⟨⊤, inferInstance, isOpen_univ, le_top⟩⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd
    htnon (fun V => (htcl V).isCompact) htcl
  have hxmem : ∀ V, x ∈ t V := Set.mem_iInter.mp hx
  have hmemC : (x : Ω ≃ₐ[k] Ω) ∈ C := hInter _ fun V => (hxmem V).1
  have hmemD : (x : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k A := x.2
  have hmemI : (x : Ω ≃ₐ[k] Ω) ∈ Work.SSGRoute.inertiaSub k Ω A :=
    Work.SSGRoute.PT.G1plusOwn.inertiaSub_normalClosure_inf_decomp k Ω A hA
      (Subgroup.mem_inf.mpr ⟨hmemC, hmemD⟩)
  exact (hxmem ⟨⊤, inferInstance, isOpen_univ, le_top⟩).2 (hIZ x hmemI)

variable (p : ℕ) [Fact p.Prime]

/-- **A finite Galois level, unramified at `A`, at which a locally constant cocycle vanishing on the
inertia factors.**  This is the arithmetic input of G1⁺'s clause (6). -/
theorem exists_unramified_level_factors_local
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hramA : ¬ SSGRoute.IsRamifiedIn k K A)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hiner : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → b σ = 0) :
    ∃ (L : IntermediateField k Ω), ∃ (_ : NumberField ↥L) (_ : FiniteDimensional k L)
      (_ : IsGalois k L),
      K ≤ L ∧ Work.SSGRoute.inertiaSub k Ω A ≤ L.fixingSubgroup ∧
      ∃ b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ) := by
  classical
  haveI hGalΩ : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  -- `I_A ≤ K.fixingSubgroup`: `K/k` is unramified at `A`
  have hIK : Work.SSGRoute.inertiaSub k Ω A ≤ K.fixingSubgroup := by
    intro σ hσ
    rw [Work.SSGRoute.mem_inertiaSub] at hσ
    by_contra hσK
    exact hramA ⟨σ, hσ, hσK⟩
  -- every fibre of `b` on `D_A` is open (`b` is locally constant there)
  have hfib : ∀ c : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      IsOpen {x : ↥(SSGRoute.decomp k A) | b x = c} := by
    intro c
    obtain ⟨U, hUo, hU⟩ := hl
    refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
    have hopen : IsOpen {y : ↥(SSGRoute.decomp k A) |
        ((x : Ω ≃ₐ[k] Ω))⁻¹ * (y : Ω ≃ₐ[k] Ω) ∈ U} :=
      hUo.preimage ((continuous_const_mul ((x : Ω ≃ₐ[k] Ω)⁻¹)).comp continuous_subtype_val)
    refine Filter.mem_of_superset (hopen.mem_nhds ?_) ?_
    · show ((x : Ω ≃ₐ[k] Ω))⁻¹ * (x : Ω ≃ₐ[k] Ω) ∈ U
      rw [inv_mul_cancel]; exact U.one_mem
    · intro y hy
      have hyD : (y : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k A := y.2
      have huD : ((x : Ω ≃ₐ[k] Ω))⁻¹ * (y : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k A :=
        (SSGRoute.decomp k A).mul_mem ((SSGRoute.decomp k A).inv_mem x.2) hyD
      have h1 : b ((x : Ω ≃ₐ[k] Ω) * (((x : Ω ≃ₐ[k] Ω))⁻¹ * (y : Ω ≃ₐ[k] Ω)))
          = b (x : Ω ≃ₐ[k] Ω) := hU _ x.2 _ hy huD
      rw [mul_inv_cancel_left] at h1
      exact h1.trans hx
  -- the zero set on `D_A` is clopen
  let Z : Set ↥(SSGRoute.decomp k A) := {x | b x = 0}
  have hZo : IsOpen Z := hfib 0
  have hZc : IsClosed Z := by
    rw [← isOpen_compl_iff]
    have hcompl : Zᶜ = ⋃ (c : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        ⋃ (_ : c ≠ 0), {x : ↥(SSGRoute.decomp k A) | b x = c} := by
      ext x
      simp only [Z, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
      exact ⟨fun hx => ⟨b x, hx, rfl⟩, fun ⟨c, hc, hcx⟩ => hcx ▸ hc⟩
    rw [hcompl]
    exact isOpen_iUnion fun c => isOpen_iUnion fun _ => hfib c
  -- the inertia lies in the zero set
  have hIZ : ∀ x : ↥(SSGRoute.decomp k A), (x : Ω ≃ₐ[k] Ω) ∈ Work.SSGRoute.inertiaSub k Ω A →
      x ∈ Z := by
    intro x hx
    exact hiner x ((Work.SSGRoute.mem_inertiaSub k Ω A x).mp hx)
  -- the compactness step
  obtain ⟨V, hVn, hVo, hVI, hVZ⟩ :=
    exists_openNormal_inf_decomp_le (k := k) (Ω := Ω) A hA Z hZc hZo hIZ
  -- intersect with `K.fixingSubgroup` so that the fixed field contains `K`
  haveI hVnI : V.Normal := hVn
  haveI hKn : K.fixingSubgroup.Normal := IsGalois.fixingSubgroup_normal_of_isGalois K
  have hWn : (V ⊓ K.fixingSubgroup).Normal := inferInstance
  have hWo : IsOpen ((V ⊓ K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) :
      Set (Ω ≃ₐ[k] Ω)) := hVo.inter K.fixingSubgroup_isOpen
  have hWI : Work.SSGRoute.inertiaSub k Ω A ≤ V ⊓ K.fixingSubgroup := le_inf hVI hIK
  -- the level
  let W : Subgroup (Ω ≃ₐ[k] Ω) := V ⊓ K.fixingSubgroup
  have hWoW : IsOpen (W : Set (Ω ≃ₐ[k] Ω)) := hWo
  have hLfix : (IntermediateField.fixedField W).fixingSubgroup = W :=
    fixingSubgroup_fixedField_of_isOpen W hWoW
  haveI hLfd : FiniteDimensional k (IntermediateField.fixedField W) :=
    finiteDimensional_fixedField_of_isOpen W hWoW
  have hNW : W.Normal := hWn
  haveI hLgal : IsGalois k (IntermediateField.fixedField W) :=
    (InfiniteGalois.normal_iff_isGalois (IntermediateField.fixedField W)).mp (by
      rw [hLfix]; exact hNW)
  have hKL : K ≤ IntermediateField.fixedField W :=
    (IntermediateField.le_iff_le W K).mpr inf_le_right
  have hLI : Work.SSGRoute.inertiaSub k Ω A ≤ (IntermediateField.fixedField W).fixingSubgroup := by
    rw [hLfix]; exact hWI
  -- `b` factors through `L = Ω^W` on the decomposition group
  obtain ⟨b₀, hb₀⟩ := factors_of_fixingSubgroup_le (H := SSGRoute.decomp k A) b
    (IntermediateField.fixedField W) W hLfix.le (fun g hg u hu huD => by
      have hbu : b u = 0 := hVZ ⟨u, huD⟩ hu.1
      rw [hb g hg u huD, hbu, smul_zero, add_zero])
  haveI hLnf : NumberField ↥(IntermediateField.fixedField W) := inferInstance
  exact ⟨IntermediateField.fixedField W, hLnf, hLfd, hLgal, hKL, hLI, b₀, hb₀⟩

/-- **The statement of `PT.G1plusOwn.exists_unramified_level_factors`, proved** from
`exists_unramified_level_factors_local` and the proved bridge
`PT.G1plusOwn.isInertiaAt_eq_one_of_inertiaSub_le` (the `IsInertiaAt (finQW L A hA)` spelling of
`I_A ≤ L.fixingSubgroup`).  This is the drop-in replacement for the still-`sorry`ed
`exists_unramified_level_factors`: only the `obtain` line of
`PT.G1plusOwn.g1FinHalf_unramified` has to be re-pointed. -/
theorem exists_unramified_level_factors_clean
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hramA : ¬ SSGRoute.IsRamifiedIn k K A)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hiner : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → b σ = 0) :
    ∃ (L : IntermediateField k Ω), ∃ (_ : NumberField ↥L) (_ : FiniteDimensional k L)
      (_ : IsGalois k L), K ≤ L ∧
      (∀ σ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt (Work.SSGRoute.PT.finQW L A hA) σ → σ = 1) ∧
      ∃ b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ) := by
  obtain ⟨L, hLnf, hLfd, hLgal, hKL, hLI, b₀, hb₀⟩ :=
    exists_unramified_level_factors_local (p := p) (k := k) (Ω := Ω) K T M A hA hramA b hb hl hiner
  exact ⟨L, hLnf, hLfd, hLgal, hKL,
    fun σ hσ => G1plusOwn.isInertiaAt_eq_one_of_inertiaSub_le k Ω A hA L hLI σ hσ, b₀, hb₀⟩

end Work.SSGRoute.PT
