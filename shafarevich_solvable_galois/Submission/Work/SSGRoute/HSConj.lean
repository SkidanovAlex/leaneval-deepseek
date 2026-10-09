import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.h1loc_conjLinearMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The conjugation endomorphisms `conj₀`, `conj₁` and the degree-`0` row

Shared definitions and the degree-zero part of the two-row decomposition
(`Work.SSGRoute.hs_twoRow_decomp`).

* `conj0` — the action of `σ` on `H⁰(I,M) = M^I` (i.e. `m ↦ res σ • m`);
* `conj1` — the conjugation action of `σ` on `H¹(I,M)` (`h1loc_conjLinearMap`);
* `mem_H0loc_decomp_iff` — `H⁰(D,M) = (M^I)^σ` for `D = decomp k A = I ⊔ closure⟨σ⟩`;
* `finrank_H0loc_decomp` — the degree-zero two-row formula
  `dim H⁰(D,M) = dim ker (conj₀ - 1)`.
-/

open scoped Pointwise
open Classical

set_option linter.unusedSectionVars false

namespace Work.SSGRoute

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (A : ValuationSubring Ω)

/-- The subgroup of `D`-elements fixing a given `m : M` is closed: it contains the open subgroup
`ker (res k K)` and is therefore open, hence closed. -/
lemma isClosed_fixingSubgroup (m : M) :
    IsClosed ({g : Ω ≃ₐ[k] Ω | SSGRoute.res k K g • m = m} : Set (Ω ≃ₐ[k] Ω)) := by
  let S : Subgroup (Ω ≃ₐ[k] Ω) :=
    { carrier := {g | SSGRoute.res k K g • m = m}
      one_mem' := by show SSGRoute.res k K 1 • m = m; rw [map_one, one_smul]
      mul_mem' := by
        intro a b ha hb
        show SSGRoute.res k K (a * b) • m = m
        rw [map_mul, mul_smul, hb, ha]
      inv_mem' := by
        intro a ha
        show SSGRoute.res k K a⁻¹ • m = m
        have h : SSGRoute.res k K a⁻¹ • m = SSGRoute.res k K a⁻¹ • (SSGRoute.res k K a • m) := by
          rw [ha]
        rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h
        exact h }
  have hopen : IsOpen ((MonoidHom.ker (SSGRoute.res k K)) : Set (Ω ≃ₐ[k] Ω)) := by
    have h : (MonoidHom.ker (SSGRoute.res k K)) = K.fixingSubgroup :=
      IntermediateField.restrictNormalHom_ker (E := K)
    rw [h]; exact IntermediateField.fixingSubgroup_isOpen K
  have hle : MonoidHom.ker (SSGRoute.res k K) ≤ S := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    show SSGRoute.res k K g • m = m
    rw [hg, one_smul]
  exact Subgroup.isClosed_of_isOpen S (Subgroup.isOpen_mono hle hopen)

/-- If `res σ • m = m` then `res γ • m = m` for every `γ` in the closure of `zpowers σ`. -/
lemma smul_fixed_of_mem_topologicalClosure (m : M)
    (hσ : SSGRoute.res k K σ • m = m) :
    ∀ γ ∈ Subgroup.topologicalClosure (Subgroup.zpowers σ), SSGRoute.res k K γ • m = m := by
  have hclosed := isClosed_fixingSubgroup k Ω K M m
  have hmem : Subgroup.zpowers σ ≤
      ({ carrier := {g | SSGRoute.res k K g • m = m}
         one_mem' := by show SSGRoute.res k K 1 • m = m; rw [map_one, one_smul]
         mul_mem' := by
           intro a b ha hb
           show SSGRoute.res k K (a * b) • m = m
           rw [map_mul, mul_smul, hb, ha]
         inv_mem' := by
           intro a ha
           show SSGRoute.res k K a⁻¹ • m = m
           have h : SSGRoute.res k K a⁻¹ • m
               = SSGRoute.res k K a⁻¹ • (SSGRoute.res k K a • m) := by rw [ha]
           rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h
           exact h } : Subgroup (Ω ≃ₐ[k] Ω)) := Subgroup.zpowers_le.mpr hσ
  exact fun γ hγ => Subgroup.topologicalClosure_minimal _ hmem hclosed hγ

/-- **`H⁰(D,M)`.** For `D = decomp k A = I ⊔ C`, an element of `M` is fixed by `D` iff it is fixed
by `I` and by `σ`. -/
lemma mem_H0loc_decomp_iff (hI : I ≤ SSGRoute.decomp k A)
    (hσ : σ ∈ SSGRoute.decomp k A)
    (hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ))
    {m : M} :
    m ∈ H0loc p k Ω K M (SSGRoute.decomp k A) ↔
      m ∈ H0loc p k Ω K M I ∧ SSGRoute.res k K σ • m = m := by
  constructor
  · intro hm
    exact ⟨fun g hg => hm g (hI hg), hm σ hσ⟩
  · rintro ⟨hmI, hσ'⟩
    have hfix := smul_fixed_of_mem_topologicalClosure k Ω K M σ m hσ'
    have hS : SSGRoute.decomp k A ≤
        ({ carrier := {g | SSGRoute.res k K g • m = m}
           one_mem' := by show SSGRoute.res k K 1 • m = m; rw [map_one, one_smul]
           mul_mem' := by
             intro a b ha hb
             show SSGRoute.res k K (a * b) • m = m
             rw [map_mul, mul_smul, hb, ha]
           inv_mem' := by
             intro a ha
             show SSGRoute.res k K a⁻¹ • m = m
             have h : SSGRoute.res k K a⁻¹ • m
                 = SSGRoute.res k K a⁻¹ • (SSGRoute.res k K a • m) := by rw [ha]
             rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h
             exact h } : Subgroup (Ω ≃ₐ[k] Ω)) :=
      le_trans hsup (sup_le (fun g hg => hmI g hg) hfix)
    exact fun g hg => hS hg

/-- The conjugation-by-`σ` action on `H⁰(I,M) = M^I`, as a `𝔽_p`-linear endomorphism. -/
noncomputable def conj0 (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I) :
    ↥(H0loc p k Ω K M I) →ₗ[ZMod p] ↥(H0loc p k Ω K M I) where
  toFun m := ⟨SSGRoute.res k K σ • (m : M), by
    intro u hu
    show SSGRoute.res k K u • (SSGRoute.res k K σ • (m : M)) = SSGRoute.res k K σ • (m : M)
    rw [← mul_smul, ← map_mul]
    have h : SSGRoute.res k K (u * σ) = SSGRoute.res k K (σ * (σ⁻¹ * u * σ)) := by
      congr 1; group
    rw [h, map_mul, mul_smul, m.2 (σ⁻¹ * u * σ) (hnorm2 u hu)]⟩
  map_add' m n := Subtype.ext (by simp [smul_add])
  map_smul' c m := Subtype.ext (by
    simp only [SetLike.val_smul, RingHom.id_apply]
    exact smul_comm (SSGRoute.res k K σ) c (m : M))

lemma conj0_coe (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I) (m : ↥(H0loc p k Ω K M I)) :
    ((conj0 p k Ω K M I σ hnorm2 m : ↥(H0loc p k Ω K M I)) : M)
      = SSGRoute.res k K σ • (m : M) := rfl

/-- **`dim H⁰(D,M) = dim ker (conj₀ - 1)`** — the degree-zero row of the two-row decomposition. -/
theorem finrank_H0loc_decomp (hI : I ≤ SSGRoute.decomp k A)
    (hσ : σ ∈ SSGRoute.decomp k A)
    (hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ))
    (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I) :
    Module.finrank (ZMod p) ↥(H0loc p k Ω K M (SSGRoute.decomp k A))
      = Module.finrank (ZMod p)
          ↥(LinearMap.ker (conj0 p k Ω K M I σ hnorm2 - LinearMap.id)) := by
  have hle : H0loc p k Ω K M (SSGRoute.decomp k A) ≤ H0loc p k Ω K M I :=
    fun m hm g hg => hm g (hI hg)
  have hker : LinearMap.ker (conj0 p k Ω K M I σ hnorm2 - LinearMap.id)
      = Submodule.comap (H0loc p k Ω K M I).subtype
          (H0loc p k Ω K M (SSGRoute.decomp k A)) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
        Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro hx
      refine (mem_H0loc_decomp_iff p k Ω K M I σ A hI hσ hsup).mpr ⟨x.2, ?_⟩
      have h := congrArg (fun y : ↥(H0loc p k Ω K M I) => (y : M)) hx
      simpa [conj0_coe] using h
    · intro hx
      have hmem := (mem_H0loc_decomp_iff p k Ω K M I σ A hI hσ hsup).mp hx
      exact Subtype.ext (by simpa [conj0_coe] using hmem.2)
  have h1 : Module.finrank (ZMod p)
        ↥(LinearMap.ker (conj0 p k Ω K M I σ hnorm2 - LinearMap.id))
      = Module.finrank (ZMod p)
          ↥(Submodule.comap (H0loc p k Ω K M I).subtype
              (H0loc p k Ω K M (SSGRoute.decomp k A))) := by rw [hker]
  have h2 : Module.finrank (ZMod p)
        ↥(Submodule.comap (H0loc p k Ω K M I).subtype
            (H0loc p k Ω K M (SSGRoute.decomp k A)))
      = Module.finrank (ZMod p) ↥(H0loc p k Ω K M (SSGRoute.decomp k A)) :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)
  exact h2.symm.trans h1.symm



/-- The conjugation action of `σ` on `H¹(I,M)`, realised by `h1loc_conjLinearMap`. -/
noncomputable def conj1 (hnorm1 : ∀ n ∈ I, σ * n * σ⁻¹ ∈ I)
    (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I) :
    H1loc p k Ω K M I →ₗ[ZMod p] H1loc p k Ω K M I :=
  Classical.choose (h1loc_conjLinearMap p k Ω K I σ hnorm1 hnorm2 M)

lemma conj1_spec (hnorm1 : ∀ n ∈ I, σ * n * σ⁻¹ ∈ I)
    (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I)
    (f : (Ω ≃ₐ[k] Ω) → M) (hf : f ∈ lcCocycles p k Ω K M I) :
    conj1 p k Ω K M I σ hnorm1 hnorm2 (toClass p k Ω K M I f) =
      toClass p k Ω K M I (fun n => SSGRoute.res k K σ • f (σ⁻¹ * n * σ)) :=
  Classical.choose_spec (h1loc_conjLinearMap p k Ω K I σ hnorm1 hnorm2 M) f hf

end

end Work.SSGRoute
