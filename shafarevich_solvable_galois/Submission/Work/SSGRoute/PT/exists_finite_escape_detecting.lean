import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.finite_X1_S_proved
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

Lead guidance. Design: _lead_design/ssg_pt_design_1002/count_1930/NOTE.md (Claude design pass, 10-04). PT.Pipeline.E9MiddleExactness is FALSE as stated (both directions; counterexamples in the note), so the 'E9 → SubMiddleExactness' passage is RETIRED. COUNT = countingIdentity_of_reciprocity_and_converse once G1⁺ (8) holds; NEVER go through converse_of_countingIdentity (circular). Split: (1) phiAt_orbit_eq_iota (value formula on one orbit, from the proved phiAt_extToClasses_eq + extLoc_yonedaPair + orbit uniqueness); (2) exists_finite_escape_detecting (finitely many split places detect the relaxed dual Selmer condition; Hermite–Minkowski via Finiteness/finite_of_bddDegree_unramifiedOutside, which still carries an unproved axiom transitively); (3) finiteS_converse_canonical (middle exactness over a finite place set: idèle gluing + (1) + e9_glue_phiAt + E6 + pt_extSegment_exact; delegate 'realise a local functional by an unramified class' = local_duality_ext_in (ii) + the Frobenius check); (4) relaxed_converse_of_finiteS (G1⁺ (8) from (3) + (2) by linear algebra). This avoids the 'subB not closed' problem.
Memory: Lean only through the harness; no sleep loops around lake.

Implementation note (prover).  The finiteness input used here is *not* the stub
`Finiteness/finite_of_bddDegree_unramifiedOutside` (that one is axiom-tainted) but its acknowledged
axiom-clean copy `TatePoitouRoute/FinitenessHM.finite_of_bddDegree_unamifiedOutside_clean`, combined
with the field-of-definition lemma `Finiteness.exists_openSubgroup_factors_of_mem_lcCocycles`; this
gives `finite_Z1unr_cochains` below, the finiteness of the *cochain* set `Z1unr S` (Milne I.4.9's
`Ш¹`-side without the local conditions), from which the main theorem is assembled by a pure
conjugacy/orbit argument: `IsCoboundaryOn … (decomp k B) b` is a conjugacy invariant of `B`
(`isCoboundaryOn_decomp_conj`), so one representative place per `G_k`-orbit of the finitely many
bad cocycles detects them all.  Both `hSfin` and `hSram` are not needed by this argument: `T'` is
built out of places that already have the required split/outside-`S` properties by construction.
-/

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000

open scoped Pointwise
open IntermediateField

namespace Work.SSGRoute.PT

/-! # The pieces of the proof of `exists_finite_escape_detecting`

The proof has three layers, isolated here as separate declarations:

* `finite_Z1unr_cochains` — the cochain-level group `H¹(G_S, M)` is finite (Hermite–Minkowski);
* three elementary conjugacy lemmas for a `1`-cocycle (`res_eq_one_iff_mem_fixingSubgroup`,
  `cocycle_conj_of_res_eq_one`, `isCoboundaryOn_decomp_iff_forall_eq_zero`,
  `isCoboundaryOn_decomp_conj`) — "being a coboundary on `D_B`" is a conjugacy invariant of the
  place, which is what lets one take one representative per `G_k`-orbit of places;
* `IsBadCocycle` and the main theorem, which selects one witness place for each *orbit class* of a
  bad cocycle.
-/

/-! ## Finiteness of the cochain-level `H¹(G_S, M)` (Hermite–Minkowski) -/

section Finiteness

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- **The set of locally constant cocycles unramified outside `S` is finite.**

`Work.SSGRoute.PTCore.Z1unr p k Ω K M S` is the set of functions `(Ω ≃ₐ[k] Ω) → M` that are
`1`-cocycles for the action `SSGRoute.res k K : G_k →* Gal(K/k)`, locally constant, and vanish on
the inertia subgroup of every finite place whose conjugacy class does not meet `S`.  This is the
cochain-level `H¹(G_S, M)`; it is finite by Hermite–Minkowski: every such cocycle factors through
an open subgroup `U` with `[G_k : U] ≤ #M` containing the inertia of every place outside `S`, so it
is one of the functions on the coset space `G_k ⧸ U`, and the fixed field `Ω^U` runs through a
finite set of extensions of `k` of degree `≤ #M` unramified outside `S`. -/
theorem finite_Z1unr_cochains
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (S : Finset (ValuationSubring Ω)) :
    (Work.SSGRoute.PTCore.Z1unr p k Ω K M S : Set ((Ω ≃ₐ[k] Ω) → M)).Finite := by
  classical
  -- the finite places of `S` (only those are constrained by `Z1unr`) and the degree bound
  let T : Finset (ValuationSubring Ω) := S.filter (fun A => SSGRoute.IsFinPlace k A)
  let n : ℕ := Nat.card M
  -- the Hermite–Minkowski list of fields of degree `≤ n` ramified only inside `T`
  let 𝓛 : Set {F : IntermediateField k Ω // FiniteDimensional k F} :=
    {L | Module.finrank k L.1 ≤ n ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → SSGRoute.IsRamifiedIn k L.1 B →
        ∃ A ∈ T, SSGRoute.IsConjPlace k A B)}
  have hHM : 𝓛.Finite :=
    Work.SSGRoute.TatePoitouRoute.FinitenessHM.finite_of_bddDegree_unamifiedOutside_clean k Ω T
      (fun A hA => (Finset.mem_filter.mp hA).2) n
  -- the cochains attached to a field `L`: those factoring through `G_k ⧸ Gal(Ω/L)`
  let Cst : {F : IntermediateField k Ω // FiniteDimensional k F} → Set ((Ω ≃ₐ[k] Ω) → M) :=
    fun L => {f | ∀ g u : (Ω ≃ₐ[k] Ω), u ∈ L.1.fixingSubgroup → f (g * u) = f g}
  have hCfin : ∀ L : {F : IntermediateField k Ω // FiniteDimensional k F}, (Cst L).Finite := by
    intro L
    haveI : FiniteDimensional k L.1 := L.2
    have hq : Finite ((Ω ≃ₐ[k] Ω) ⧸ L.1.fixingSubgroup) :=
      Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen L.1)
    exact Work.SSGRoute.TatePoitouRoute.FinitenessHM.finite_rightInvariant_functions
      L.1.fixingSubgroup (Subgroup.finiteIndex_iff_finite_quotient.mpr hq)
  -- every unramified-outside-`S` cocycle lies in the cover set of one of the finitely many fields
  have hZsub : {f : (Ω ≃ₐ[k] Ω) → M | f ∈ Work.SSGRoute.PTCore.Z1unr p k Ω K M S} ⊆
      ⋃ L ∈ 𝓛, Cst L := by
    intro f hf
    obtain ⟨hcoc, hlc, hunr⟩ := hf
    have hflc : f ∈ Work.SSGRoute.lcCocycles p k Ω K M ⊤ :=
      (Work.SSGRoute.mem_lcCocycles p k Ω K M ⊤ f).mpr ⟨hcoc, hlc⟩
    obtain ⟨U, hUfi, hUopen, hinv, hUinertia, hUindex⟩ :=
      Work.SSGRoute.Finiteness.exists_openSubgroup_factors_of_mem_lcCocycles
        p k Ω K M S f hflc hunr
    obtain ⟨L, hLfd, hUL, hLinv, hLfin⟩ :=
      Work.SSGRoute.TatePoitouRoute.FinitenessHM.openSubgroup_fixedField_factoring
        f U hUopen hinv hUfi
    have hLram : ∀ B' : ValuationSubring Ω, SSGRoute.IsFinPlace k B' →
        SSGRoute.IsRamifiedIn k L B' → ∃ A ∈ T, SSGRoute.IsConjPlace k A B' := by
      intro B' hB' hram
      by_contra hno
      obtain ⟨σ, hσin, hσnotin⟩ := hram
      have hconj : ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B' := by
        intro A hAS hAC
        exact hno ⟨A, Finset.mem_filter.mpr ⟨hAS,
          Work.SSGRoute.TatePoitouRoute.FinitenessHM.isFinPlace_of_isConjPlace hAC hB'⟩, hAC⟩
      have hIB : Work.SSGRoute.inertiaSub k Ω B' ≤ U := hUinertia B' hB' hconj
      have hσU : σ ∈ U := hIB ((Work.SSGRoute.mem_inertiaSub k Ω B' σ).mpr hσin)
      exact hσnotin (hUL hσU)
    have hLmem : (⟨L, hLfd⟩ : {F : IntermediateField k Ω // FiniteDimensional k F}) ∈ 𝓛 :=
      ⟨le_trans hLfin hUindex, hLram⟩
    refine Set.mem_iUnion.mpr ⟨⟨L, hLfd⟩, ?_⟩
    refine Set.mem_iUnion.mpr ⟨hLmem, ?_⟩
    intro g u hu
    exact hLinv g u hu
  have hunion : (⋃ L ∈ 𝓛, Cst L).Finite := hHM.biUnion (fun L _ => hCfin L)
  exact hunion.subset hZsub

end Finiteness

/-! ## Conjugacy lemmas for `1`-cocycles -/

section Helpers

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
variable {K : IntermediateField k Ω} [Normal k K]
variable {X : Type} [AddCommGroup X] [DistribMulAction (K ≃ₐ[k] K) X]

/-- An element of `G_k` restricts to `1 ∈ Gal(K/k)` exactly when it lies in `G_K`. -/
theorem res_eq_one_iff_mem_fixingSubgroup (σ : Ω ≃ₐ[k] Ω) :
    SSGRoute.res k K σ = 1 ↔ σ ∈ K.fixingSubgroup := by
  have hfun : SSGRoute.res k K = AlgEquiv.restrictNormalHom K := rfl
  constructor
  · intro h
    rw [hfun] at h
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h1 : (AlgEquiv.restrictNormalHom K σ) ⟨x, hx⟩ = ⟨x, hx⟩ := by
      rw [h]
      rfl
    have h2 := congrArg (fun y : ↥K => (y : Ω)) h1
    rw [AlgEquiv.restrictNormalHom_apply] at h2
    exact h2
  · intro h
    rw [IntermediateField.mem_fixingSubgroup_iff] at h
    rw [hfun]
    ext x
    change ((AlgEquiv.restrictNormalHom K σ) x : Ω) = (x : Ω)
    rw [AlgEquiv.restrictNormalHom_apply]
    exact h x x.2

/-- **Conjugation formula for a `1`-cocycle at an element of the kernel of the action.**  If
`b` is a `1`-cocycle for `SSGRoute.res k K` and `res k K τ = 1` then
`b (γ τ γ⁻¹) = res k K γ • b τ`. -/
theorem cocycle_conj_of_res_eq_one {b : (Ω ≃ₐ[k] Ω) → X}
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) {τ : Ω ≃ₐ[k] Ω}
    (hτ : SSGRoute.res k K τ = 1) (γ : Ω ≃ₐ[k] Ω) :
    b (γ * τ * γ⁻¹) = SSGRoute.res k K γ • b τ := by
  have h1 : b 1 = 0 := by
    have h := hb 1 trivial 1 trivial
    rw [mul_one] at h
    have h3 : b 1 + SSGRoute.res k K 1 • b 1 = b 1 + 0 := by rw [add_zero]; exact h.symm
    simpa using add_left_cancel h3
  have hγinv : SSGRoute.res k K γ • b (γ⁻¹) = - b γ := by
    have h := hb γ trivial γ⁻¹ trivial
    rw [mul_inv_cancel, h1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hτγ : b (τ * γ⁻¹) = b τ + b (γ⁻¹) := by
    have h := hb τ trivial γ⁻¹ trivial
    rw [hτ, one_smul] at h
    exact h
  calc b (γ * τ * γ⁻¹) = b (γ * (τ * γ⁻¹)) := by rw [mul_assoc]
    _ = b γ + SSGRoute.res k K γ • b (τ * γ⁻¹) := hb γ trivial (τ * γ⁻¹) trivial
    _ = b γ + SSGRoute.res k K γ • (b τ + b (γ⁻¹)) := by rw [hτγ]
    _ = b γ + SSGRoute.res k K γ • b τ + SSGRoute.res k K γ • b (γ⁻¹) := by
          rw [smul_add, add_assoc]
    _ = b γ + SSGRoute.res k K γ • b τ + (- b γ) := by rw [hγinv]
    _ = SSGRoute.res k K γ • b τ := by abel

/-- **Being a coboundary on `D_A` is being *zero* on `D_A`**, when `A` is a place whose
decomposition group lies in `G_K` (e.g. a place split in `N`, since `K ≤ N`). -/
theorem isCoboundaryOn_decomp_iff_forall_eq_zero (b : (Ω ≃ₐ[k] Ω) → X)
    {A : ValuationSubring Ω} (hA : SSGRoute.decomp k A ≤ K.fixingSubgroup) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ↔
      ∀ g ∈ SSGRoute.decomp k A, b g = 0 := by
  constructor
  · rintro ⟨m, hm⟩ g hg
    rw [hm g hg, (res_eq_one_iff_mem_fixingSubgroup (K := K) g).mpr (hA hg), one_smul, sub_self]
  · intro h
    exact ⟨0, fun g hg => by rw [h g hg, smul_zero, sub_zero]⟩

/-- **Conjugacy invariance of "being a coboundary on `D_B`"**, for a fixed cocycle, at places whose
decomposition groups lie in `G_K` (which is the case for all places split in `N`).  This is what
allows one to take one representative place per `G_k`-orbit. -/
theorem isCoboundaryOn_decomp_conj {b : (Ω ≃ₐ[k] Ω) → X}
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b)
    {A B : ValuationSubring Ω}
    (hA : SSGRoute.decomp k A ≤ K.fixingSubgroup)
    (hB : SSGRoute.decomp k B ≤ K.fixingSubgroup)
    {σ : Ω ≃ₐ[k] Ω} (hσ : σ • A = B) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ↔
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k B) b := by
  rw [isCoboundaryOn_decomp_iff_forall_eq_zero (K := K) b hA,
    isCoboundaryOn_decomp_iff_forall_eq_zero (K := K) b hB]
  constructor
  · intro h0 g hg
    rw [← hσ] at hg
    rw [Work.SSGRoute.decomp_conj A σ] at hg
    obtain ⟨τ, hτ, hτeq⟩ := Subgroup.mem_map.mp hg
    change MulAut.conj σ τ = g at hτeq
    rw [MulAut.conj_apply] at hτeq
    have hresτ : SSGRoute.res k K τ = 1 :=
      (res_eq_one_iff_mem_fixingSubgroup (K := K) τ).mpr (hA hτ)
    have hkey := cocycle_conj_of_res_eq_one (K := K) hb hresτ σ
    rw [← hτeq, hkey, h0 τ hτ, smul_zero]
  · intro h0 g hg
    have hBA : σ⁻¹ • B = A := by rw [← hσ, smul_smul, inv_mul_cancel, one_smul]
    rw [← hBA] at hg
    rw [Work.SSGRoute.decomp_conj B σ⁻¹] at hg
    obtain ⟨τ, hτ, hτeq⟩ := Subgroup.mem_map.mp hg
    change MulAut.conj σ⁻¹ τ = g at hτeq
    rw [MulAut.conj_apply, inv_inv] at hτeq
    have hresτ : SSGRoute.res k K τ = 1 :=
      (res_eq_one_iff_mem_fixingSubgroup (K := K) τ).mpr (hB hτ)
    have hkey := cocycle_conj_of_res_eq_one (K := K) hb hresτ σ⁻¹
    rw [inv_inv] at hkey
    rw [← hτeq, hkey, h0 τ hτ, smul_zero]

end Helpers

/-- **A bad cocycle.**  A global `1`-cocycle `b` (valued in the finite `ZMod p`-module `X`) is
*bad* if it is unramified outside the classes of `S` (i.e. it lies in `Z1unr`), and it fails to be
a coboundary on the decomposition group of some finite place `B` that is split in `N` and lies over
no prime of `S`. -/
def IsBadCocycle (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K N : IntermediateField k Ω) [Normal k K] (S : Finset (ValuationSubring Ω)) (X : Type)
    [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction (K ≃ₐ[k] K) X]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X] (b : (Ω ≃ₐ[k] Ω) → X) : Prop :=
  b ∈ Work.SSGRoute.PTCore.Z1unr p k Ω K X S ∧
    ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
      SSGRoute.IsSplitIn k N B ∧
      ¬ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k B) b

/-- Finitely many split places detect the relaxed dual Selmer condition.

`S` is a finite set of finite places covering the places over `p` and those ramified in `N`.  There
is a finite set `T'` of finite places, split in `N`, outside the classes of `S`, pairwise
non-conjugate, with this property: a global locally constant cocycle `b` of `X` that vanishes on
inertia outside the classes of `S ∪ T'` and is a coboundary on `D_t` for every `t ∈ T'` is a
coboundary on `D_B` for every finite place `B` split in `N` outside the classes of `S`.

Route.  (1) Such a `b` is unramified outside `S`: at `t ∈ T'` it is a coboundary on `D_t`, so its
restriction to inertia is a coboundary.  So its class lies in the group of classes unramified outside
`S`.  That group is finite by Hermite–Minkowski: finitely many extensions of bounded degree unramified
outside `S` (`Work.SSGRoute.finite_of_bddDegree_unramifiedOutside`), the class being determined by
its restriction to the fixed field of the kernel of the action and that field's character.
(2) For each of the finitely many classes that is *not* a coboundary at some split place `B` outside
`S`, pick one such `B`.  Use one representative per conjugacy class: being a coboundary on `D_B` is
conjugation-invariant up to the `σ`-twist of the cocycle.  Let `T'` be these places.
(3) Then every `b` as in the hypothesis is a coboundary at all of `T'`, so its class is none of the
picked classes.  So it is a coboundary at every split `B` outside `S`. -/
theorem exists_finite_escape_detecting (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (X : Type) [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction (K ≃ₐ[k] K) X]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X] [Finite X] :
    ∃ T' : Finset (ValuationSubring Ω),
      (∀ t ∈ T', SSGRoute.IsFinPlace k t ∧ SSGRoute.IsSplitIn k N t ∧
        ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A t) ∧
      (∀ t ∈ T', ∀ t' ∈ T', SSGRoute.IsConjPlace k t t' → t = t') ∧
      ∀ b : (Ω ≃ₐ[k] Ω) → X,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → (∀ t ∈ T', ¬ SSGRoute.IsConjPlace k t B) →
          ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → b σ = 0) →
        (∀ t ∈ T', SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k t) b) →
        ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k B) b := by
  classical
  -- places split in `N` have decomposition group inside `G_K` (because `K ≤ N`)
  have hGKN : N.fixingSubgroup ≤ K.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hKN
  have hNormN : (N.fixingSubgroup).Normal := IsGalois.fixingSubgroup_normal_of_isGalois N
  have hsplit_le : ∀ B : ValuationSubring Ω, SSGRoute.IsSplitIn k N B →
      SSGRoute.decomp k B ≤ K.fixingSubgroup := fun B hB => le_trans hB hGKN
  -- the finite set of unramified cocycles, and its bad elements
  have hWfin : (Work.SSGRoute.PTCore.Z1unr p k Ω K X S : Set ((Ω ≃ₐ[k] Ω) → X)).Finite :=
    finite_Z1unr_cochains p k Ω K X S
  have hBadfin : {b : (Ω ≃ₐ[k] Ω) → X | IsBadCocycle p k Ω K N S X b}.Finite :=
    hWfin.subset (fun _ hb => hb.1)
  haveI : Finite ↥{b : (Ω ≃ₐ[k] Ω) → X | IsBadCocycle p k Ω K N S X b} := hBadfin.to_subtype
  haveI : Fintype ↥{b : (Ω ≃ₐ[k] Ω) → X | IsBadCocycle p k Ω K N S X b} := Fintype.ofFinite _
  -- a witness place for each bad cocycle
  let w : ↥{b : (Ω ≃ₐ[k] Ω) → X | IsBadCocycle p k Ω K N S X b} → ValuationSubring Ω :=
    fun b => Classical.choose b.2.2
  have hw : ∀ b : ↥{b : (Ω ≃ₐ[k] Ω) → X | IsBadCocycle p k Ω K N S X b},
      SSGRoute.IsFinPlace k (w b) ∧
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A (w b)) ∧
      SSGRoute.IsSplitIn k N (w b) ∧
      ¬ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k (w b)) b.1 :=
    fun b => Classical.choose_spec b.2.2
  let G := Ω ≃ₐ[k] Ω
  let rel : Setoid (ValuationSubring Ω) := MulAction.orbitRel G (ValuationSubring Ω)
  -- one canonical representative per `G`-orbit class occurring among the witnesses
  set T' : Finset (ValuationSubring Ω) :=
    (Finset.univ : Finset ↥{b : (Ω ≃ₐ[k] Ω) → X | IsBadCocycle p k Ω K N S X b}).image
      (fun b => Quotient.out (Quotient.mk rel (w b))) with hT'def
  have hT'wit : ∀ t ∈ T', ∃ b : ↥{b : (Ω ≃ₐ[k] Ω) → X | IsBadCocycle p k Ω K N S X b},
      SSGRoute.IsConjPlace k (w b) t := by
    intro t ht
    rw [hT'def] at ht
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp ht
    refine ⟨b, ?_⟩
    have hrel : rel (Quotient.out (Quotient.mk rel (w b))) (w b) :=
      Quotient.exact (Quotient.out_eq (Quotient.mk rel (w b)))
    have hrel' : MulAction.orbitRel G (ValuationSubring Ω)
        (Quotient.out (Quotient.mk rel (w b))) (w b) := hrel
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel')
    exact ⟨g, hg.trans hb⟩
  have h1 : ∀ t ∈ T', SSGRoute.IsFinPlace k t ∧ SSGRoute.IsSplitIn k N t ∧
      ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A t := by
    intro t ht
    obtain ⟨b, hconj⟩ := hT'wit t ht
    obtain ⟨hfin, hSw, hsplitw, -⟩ := hw b
    obtain ⟨σ, hσ⟩ := hconj
    have hconj' : SSGRoute.IsConjPlace k (w b) t := ⟨σ, hσ⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← hσ]
      exact (Work.SSGRoute.isFinPlace_smul_iff (w b) σ).mpr hfin
    · rw [← hσ]
      exact (Work.SSGRoute.isSplitIn_conj N hNormN (w b) σ).mpr hsplitw
    · intro A hA hAc
      exact hSw A hA (Work.SSGRoute.isConjPlace_trans hAc (Work.SSGRoute.isConjPlace_symm hconj'))
  have h2 : ∀ t ∈ T', ∀ t' ∈ T', SSGRoute.IsConjPlace k t t' → t = t' := by
    intro t ht t' ht' hconj
    rw [hT'def] at ht ht'
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp ht
    obtain ⟨b', -, hb'⟩ := Finset.mem_image.mp ht'
    have hmem : t' ∈ MulAction.orbit G t := MulAction.mem_orbit_iff.mpr hconj
    have hrel : Quotient.mk rel t' = Quotient.mk rel t :=
      Quotient.sound (MulAction.orbitRel_apply.mpr hmem)
    have hcrit : Quotient.mk rel (w b') = Quotient.mk rel (w b) := by
      have hrel'' : Quotient.mk rel (Quotient.out (Quotient.mk rel (w b'))) =
          Quotient.mk rel (Quotient.out (Quotient.mk rel (w b))) := by
        rw [hb', hb]; exact hrel
      rwa [Quotient.out_eq, Quotient.out_eq] at hrel''
    rw [← hb', ← hb, hcrit]
  have h3 : ∀ b : (Ω ≃ₐ[k] Ω) → X,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → (∀ t ∈ T', ¬ SSGRoute.IsConjPlace k t B) →
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → b σ = 0) →
      (∀ t ∈ T', SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k t) b) →
      ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k B) b := by
    intro b hcoc hlc hunr hcob B hBfin hBS hBsplit
    by_contra hnot
    -- `b` is unramified outside `S`: at the places of `T'` the hypothesis gives it, everywhere else
    -- the explicit vanishing hypothesis does.
    have hbW : b ∈ Work.SSGRoute.PTCore.Z1unr p k Ω K X S := by
      rw [Work.SSGRoute.PTCore.mem_Z1unr]
      refine ⟨hcoc, hlc, ?_⟩
      intro B' hB'fin hB'S σ hσ
      by_cases hconjT : ∃ t ∈ T', SSGRoute.IsConjPlace k t B'
      · obtain ⟨t, htT, htconj⟩ := hconjT
        obtain ⟨-, htsplit, -⟩ := h1 t htT
        have hDt : SSGRoute.decomp k t ≤ K.fixingSubgroup := hsplit_le t htsplit
        have hbt : ∀ g ∈ SSGRoute.decomp k t, b g = 0 :=
          (isCoboundaryOn_decomp_iff_forall_eq_zero (K := K) b hDt).mp (hcob t htT)
        obtain ⟨γ, hγ⟩ := htconj
        have hτI : SSGRoute.IsInertia k t (γ⁻¹ * σ * γ) := by
          have h2' : SSGRoute.IsInertia k (γ • t) (γ * (γ⁻¹ * σ * γ) * γ⁻¹) := by
            rw [hγ, show γ * (γ⁻¹ * σ * γ) * γ⁻¹ = σ from by group]
            exact hσ
          exact (Work.SSGRoute.isInertia_conj t γ (γ⁻¹ * σ * γ)).mp h2'
        have hτD : γ⁻¹ * σ * γ ∈ SSGRoute.decomp k t :=
          (Work.SSGRoute.inertiaSub_le_decomp k Ω t) hτI
        have hresτ : SSGRoute.res k K (γ⁻¹ * σ * γ) = 1 :=
          (res_eq_one_iff_mem_fixingSubgroup (K := K) _).mpr (hDt hτD)
        have hkey := cocycle_conj_of_res_eq_one (K := K) hcoc hresτ γ
        rw [show γ * (γ⁻¹ * σ * γ) * γ⁻¹ = σ from by group] at hkey
        rw [hkey, hbt _ hτD, smul_zero]
      · push_neg at hconjT
        exact hunr B' hB'fin hB'S hconjT σ hσ
    have hbBad : IsBadCocycle p k Ω K N S X b :=
      ⟨hbW, B, hBfin, hBS, hBsplit, hnot⟩
    -- the place of `T'` attached to `b`
    let bb : ↥{b : (Ω ≃ₐ[k] Ω) → X | IsBadCocycle p k Ω K N S X b} := ⟨b, hbBad⟩
    have hmemT : Quotient.out (Quotient.mk rel (w bb)) ∈ T' := by
      rw [hT'def]
      exact Finset.mem_image.mpr ⟨bb, Finset.mem_univ bb, rfl⟩
    obtain ⟨hfin, hSw, hsplitw, hnotw⟩ := hw bb
    -- that place is conjugate to the witness, so `b` is still bad there
    have houtconj : SSGRoute.IsConjPlace k (w bb) (Quotient.out (Quotient.mk rel (w bb))) := by
      have hrel : rel (Quotient.out (Quotient.mk rel (w bb))) (w bb) :=
        Quotient.exact (Quotient.out_eq (Quotient.mk rel (w bb)))
      have hrel' : MulAction.orbitRel G (ValuationSubring Ω)
          (Quotient.out (Quotient.mk rel (w bb))) (w bb) := hrel
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel')
      exact ⟨g, hg⟩
    obtain ⟨g, hg⟩ := houtconj
    have hsplit_out : SSGRoute.IsSplitIn k N (Quotient.out (Quotient.mk rel (w bb))) := by
      rw [← hg]
      exact (Work.SSGRoute.isSplitIn_conj N hNormN (w bb) g).mpr hsplitw
    have hnotout : ¬ SSGRoute.IsCoboundaryOn (SSGRoute.res k K)
        (SSGRoute.decomp k (Quotient.out (Quotient.mk rel (w bb)))) b := fun hc =>
      hnotw ((isCoboundaryOn_decomp_conj (K := K) hcoc (hsplit_le (w bb) hsplitw)
        (hsplit_le _ hsplit_out) hg).mpr hc)
    exact hnotout (hcob _ hmemT)
  exact ⟨T', h1, h2, h3⟩

end Work.SSGRoute.PT
