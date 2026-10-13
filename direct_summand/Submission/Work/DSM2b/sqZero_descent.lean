import Mathlib
import Submission.Work.DSM2b.SqZeroAux
import Submission.Work.DSM2b.sqZero_flat

/-!
# Square-zero descent for flatness (self-contained)

Let `A` be a commutative ring, `I ⊆ A` an ideal with `I ^ 2 = ⊥` and `M` an `A`-module.
Assume

* the multiplication map `I ⊗[A] M → M`, `i ⊗ m ↦ i • m`, is injective (equivalently
  `Tor₁^A(M, A ⧸ I) = 0`), and
* `M ⧸ I • ⊤` is flat over `A ⧸ I`.

Then `M` is flat over `A`.

The proof follows the standard diagram chase.  For a finitely generated ideal `J ⊆ A` put
`J̄ := idealQuotImage I J ⊆ A ⧸ I` (the image of `J`, an `A ⧸ I`-module) and `N := M ⧸ I • ⊤`.
The main crux `ker_lsmulLift_le_range` shows that an `x ∈ J ⊗[A] M` killed by `M` lies in the
image of `(J ⊓ I) ⊗[A] M → J ⊗[A] M`; the two remaining ingredients are

* `map_id_mkQ_injective_p`: `P ⊗[A] M → P ⊗[A] N` is injective when `P` is killed by `I`, and
* `rTensor_inclusion_injective_p`: `K ⊗[A] M → I ⊗[A] M` is injective for `K ≤ I`,

both proved by cancelling the base change `P ⊗[A] M ≃ P ⊗[A ⧸ I] N` (via `tensorQuotEquiv` and
its naturality) and using flatness of `N` over `A ⧸ I`.
-/

namespace Work.DSM2b

open scoped TensorProduct
open TensorProduct

universe u

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]

/-- **Base-change cancellation, injectivity form.**  Let `I ⊆ A` be an ideal, `M` an `A`-module and
`P` an `A`-module killed by `I`.  Then `P ⊗[A] M → P ⊗[A] (M ⧸ I • ⊤)`, `p ⊗ m ↦ p ⊗ [m]`, is
injective. -/
theorem map_id_mkQ_injective_p (I : Ideal A) {P : Type u} [AddCommGroup P] [Module A P]
    (hP : I • (⊤ : Submodule A P) = ⊥) :
    Function.Injective (TensorProduct.map (LinearMap.id : P →ₗ[A] P)
      (Submodule.mkQ (I • (⊤ : Submodule A M)))) := by
  have htor : Module.IsTorsionBySet A P (I : Set A) := by
    intro p a
    have h : (a : A) • p ∈ I • (⊤ : Submodule A P) :=
      Submodule.smul_mem_smul a.2 Submodule.mem_top
    rwa [hP] at h
  letI : Module (A ⧸ I) P := htor.module
  haveI : IsScalarTower A (A ⧸ I) P := Module.IsTorsionBySet.isScalarTower htor
  have key : TensorProduct.map (LinearMap.id : P →ₗ[A] P)
      (Submodule.mkQ (I • (⊤ : Submodule A M)))
      = (tensorCancelIso I P (M ⧸ I • (⊤ : Submodule A M))).symm.toLinearMap ∘ₗ
        (tensorQuotEquiv I P M).toLinearMap := by
    apply TensorProduct.ext'
    intro p m
    simp [tensorQuotEquiv_tmul, tensorCancelIso_symm_tmul]
  rw [key]
  exact (tensorCancelIso I P (M ⧸ I • (⊤ : Submodule A M))).symm.injective.comp
    (tensorQuotEquiv I P M).injective

/-- **Flatness descent along a square-zero ideal.**  Let `I ⊆ A` with `I ^ 2 = ⊥`, `M` an
`A`-module with `M ⧸ I • ⊤` flat over `A ⧸ I`, and `K ≤ I` an ideal.  Then the map
`K ⊗[A] M → I ⊗[A] M` induced by the inclusion `K ↪ I` is injective. -/
theorem rTensor_inclusion_injective_p (I : Ideal A) (hI : I ^ 2 = ⊥)
    (hβ : Module.Flat (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M)))
    {K : Ideal A} (hK : K ≤ I) :
    Function.Injective (LinearMap.rTensor M (Submodule.inclusion hK)) := by
  have hKtor : Module.IsTorsionBySet A ↥K (I : Set A) := by
    intro k a
    apply Subtype.ext
    show (a : A) * (k : A) = 0
    have h : (a : A) * (k : A) ∈ I ^ 2 := by
      rw [sq]; exact Ideal.mul_mem_mul a.2 (hK k.2)
    rwa [hI] at h
  have hItor : Module.IsTorsionBySet A ↥I (I : Set A) := by
    intro k a
    apply Subtype.ext
    show (a : A) * (k : A) = 0
    have h : (a : A) * (k : A) ∈ I ^ 2 := by rw [sq]; exact Ideal.mul_mem_mul a.2 k.2
    rwa [hI] at h
  letI : Module (A ⧸ I) ↥K := hKtor.module
  haveI : IsScalarTower A (A ⧸ I) ↥K := Module.IsTorsionBySet.isScalarTower hKtor
  letI : Module (A ⧸ I) ↥I := hItor.module
  haveI : IsScalarTower A (A ⧸ I) ↥I := Module.IsTorsionBySet.isScalarTower hItor
  let f : ↥K →ₗ[A ⧸ I] ↥I :=
    (Submodule.inclusion hK).extendScalarsOfSurjective (surjective_algebraMap_quot I)
  have hfincl : f.restrictScalars A = Submodule.inclusion hK := by
    ext x
    rw [LinearMap.restrictScalars_apply, LinearMap.extendScalarsOfSurjective_apply]
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have h' : (f x : A) = (f y : A) := congrArg (fun z : ↥I => (z : A)) h
    simpa [f, LinearMap.extendScalarsOfSurjective_apply, Submodule.coe_inclusion] using h'
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro w hw
  rw [LinearMap.mem_ker] at hw
  have h1 : (tensorQuotEquiv I ↥I M).toLinearMap.restrictScalars A
      (LinearMap.rTensor M (f.restrictScalars A) w) = 0 := by
    rw [hfincl, hw]; simp
  have hnat := LinearMap.congr_fun (tensorQuotEquiv_naturality (A := A) I (N := ↥K) (N' := ↥I)
    (M := M) f) w
  rw [LinearMap.comp_apply, h1, LinearMap.comp_apply] at hnat
  have h4 : (tensorQuotEquiv I ↥K M) w = 0 :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf (by rw [map_zero]; exact hnat.symm)
  exact (tensorQuotEquiv I ↥K M).injective (by rw [h4, map_zero])

/-- The "action" map `L ⊗[A] X → X`, `l ⊗ x ↦ l • x` (with `l` read in `A`). -/
noncomputable def lsmulLift (L : Ideal A) (X : Type u) [AddCommGroup X] [Module A X] :
    ↥L ⊗[A] X →ₗ[A] X :=
  TensorProduct.lift ((LinearMap.lsmul A X).comp L.subtype)

@[simp]
lemma lsmulLift_tmul (L : Ideal A) (X : Type u) [AddCommGroup X] [Module A X]
    (l : ↥L) (x : X) : lsmulLift L X (l ⊗ₜ x) = (l : A) • x := by
  rw [lsmulLift, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.lsmul_apply]
  rfl

/-- Naturality of `lsmulLift` in the ideal. -/
lemma lsmulLift_comp_rTensor {I J : Ideal A} (h : J ≤ I) :
    (lsmulLift I M).comp (LinearMap.rTensor M (Submodule.inclusion h)) = lsmulLift J M := by
  apply TensorProduct.ext'
  intro k m
  simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, lsmulLift_tmul]
  rw [Submodule.coe_inclusion]

/-- If `I` kills an `A`-module `P`, then `I • ⊤ = ⊥`. -/
lemma smul_top_eq_bot_of_isTorsionBySet {I : Ideal A} {P : Type u} [AddCommGroup P]
    [Module A P] (h : Module.IsTorsionBySet A P I) : I • (⊤ : Submodule A P) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro i hi x _
  exact h (x := x) (a := ⟨i, hi⟩)

/-- **Crux.**  The kernel of `J ⊗[A] M → M` is contained in the image of
`(J ⊓ I) ⊗[A] M ⟶ J ⊗[A] M`. -/
theorem ker_lsmulLift_le_range (I : Ideal A) (hI : I ^ 2 = ⊥) (J : Ideal A)
    (hβ : Module.Flat (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))) :
    (lsmulLift J M).ker ≤
      LinearMap.range (LinearMap.rTensor M (Submodule.inclusion (inf_le_left : J ⊓ I ≤ J))) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx
  -- Step 1: `ν (α_J x) = 0`, where `ν` is the action map on `N` and `α_J` is `id ⊗ π`
  have hstep1 : lsmulLift J (M ⧸ I • (⊤ : Submodule A M))
      ((TensorProduct.map (LinearMap.id : ↥J →ₗ[A] ↥J)
        (Submodule.mkQ (I • (⊤ : Submodule A M)))) x) = 0 := by
    have hcomp : (lsmulLift J (M ⧸ I • (⊤ : Submodule A M))).comp
        (TensorProduct.map (LinearMap.id : ↥J →ₗ[A] ↥J)
          (Submodule.mkQ (I • (⊤ : Submodule A M)))) =
        (Submodule.mkQ (I • (⊤ : Submodule A M))).comp (lsmulLift J M) := by
      apply TensorProduct.ext'
      intro j m
      simp [lsmulLift_tmul, TensorProduct.map_tmul]
    rw [← LinearMap.comp_apply, hcomp, LinearMap.comp_apply, hx, map_zero]
  -- Step 2: `p₂ (α_J x) = 0`, where `p₂ = rTensor N (idealQuotImageMap I J)`
  have hstep2 : (LinearMap.rTensor (M ⧸ I • (⊤ : Submodule A M)) (idealQuotImageMap I J))
      ((TensorProduct.map (LinearMap.id : ↥J →ₗ[A] ↥J)
        (Submodule.mkQ (I • (⊤ : Submodule A M)))) x) = 0 := by
    have hkey : ∀ y : ↥J ⊗[A] (M ⧸ I • (⊤ : Submodule A M)),
        theta I J (M ⧸ I • (⊤ : Submodule A M))
          (tensorCancelIso I ↥(idealQuotImage I J) (M ⧸ I • (⊤ : Submodule A M))
            ((LinearMap.rTensor (M ⧸ I • (⊤ : Submodule A M)) (idealQuotImageMap I J)) y)) =
          lsmulLift J (M ⧸ I • (⊤ : Submodule A M)) y := by
      have hmap : ((theta I J (M ⧸ I • (⊤ : Submodule A M))).restrictScalars A) ∘ₗ
          (tensorCancelIso I ↥(idealQuotImage I J) (M ⧸ I • (⊤ : Submodule A M))).toLinearMap ∘ₗ
          (LinearMap.rTensor (M ⧸ I • (⊤ : Submodule A M)) (idealQuotImageMap I J)) =
          lsmulLift J (M ⧸ I • (⊤ : Submodule A M)) := by
        apply TensorProduct.ext'
        intro j n
        simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, idealQuotImageMap_apply,
          tensorCancelIso_tmul, theta_tmul, lsmulLift_tmul]
        exact Module.IsTorsionBySet.mk_smul
          (Module.isTorsionBySet_quotient_ideal_smul M I) (j : A) n
      intro y
      exact congr($hmap y)
    have h2a : theta I J (M ⧸ I • (⊤ : Submodule A M))
        (tensorCancelIso I ↥(idealQuotImage I J) (M ⧸ I • (⊤ : Submodule A M))
          ((LinearMap.rTensor (M ⧸ I • (⊤ : Submodule A M)) (idealQuotImageMap I J))
            ((TensorProduct.map (LinearMap.id : ↥J →ₗ[A] ↥J)
              (Submodule.mkQ (I • (⊤ : Submodule A M)))) x))) = 0 := by
      rw [hkey, hstep1]
    have h2b : tensorCancelIso I ↥(idealQuotImage I J) (M ⧸ I • (⊤ : Submodule A M))
        ((LinearMap.rTensor (M ⧸ I • (⊤ : Submodule A M)) (idealQuotImageMap I J))
          ((TensorProduct.map (LinearMap.id : ↥J →ₗ[A] ↥J)
            (Submodule.mkQ (I • (⊤ : Submodule A M)))) x)) = 0 :=
      theta_injective I J (M ⧸ I • (⊤ : Submodule A M)) hβ (by rw [h2a, map_zero])
    exact (tensorCancelIso I ↥(idealQuotImage I J) (M ⧸ I • (⊤ : Submodule A M))).injective
      (by rw [h2b, map_zero])
  -- Step 3: naturality of `π` with respect to the surjection `J → idealQuotImage I J`
  have hnat : (LinearMap.rTensor (M ⧸ I • (⊤ : Submodule A M)) (idealQuotImageMap I J)) ∘ₗ
        (TensorProduct.map (LinearMap.id : ↥J →ₗ[A] ↥J)
          (Submodule.mkQ (I • (⊤ : Submodule A M)))) =
      (TensorProduct.map (LinearMap.id : ↥(idealQuotImage I J) →ₗ[A] ↥(idealQuotImage I J))
          (Submodule.mkQ (I • (⊤ : Submodule A M)))) ∘ₗ
        (LinearMap.rTensor M (idealQuotImageMap I J)) := by
    apply TensorProduct.ext'
    intro j m
    simp [TensorProduct.map_tmul, LinearMap.rTensor_tmul]
  -- Step 4: conclude using injectivity of `id ⊗ π` on `idealQuotImage I J`
  have hα : Function.Injective
      (TensorProduct.map (LinearMap.id : ↥(idealQuotImage I J) →ₗ[A] ↥(idealQuotImage I J))
        (Submodule.mkQ (I • (⊤ : Submodule A M)))) :=
    map_id_mkQ_injective_p I
      (smul_top_eq_bot_of_isTorsionBySet (isTorsionBySet_idealQuotImage I J))
  have hstep4 : (LinearMap.rTensor M (idealQuotImageMap I J)) x = 0 := by
    refine hα ?_
    rw [map_zero, ← LinearMap.comp_apply, ← hnat, LinearMap.comp_apply, hstep2]
  rw [← Function.Exact.linearMap_ker_eq (exact_rTensor_inclusion_idealQuotImageMap I J M),
    LinearMap.mem_ker]
  exact hstep4

/-- `μ_K : K ⊗[A] M → M` is injective for `K = J ⊓ I`. -/
theorem lsmulLift_inf_injective (I : Ideal A) (hI : I ^ 2 = ⊥) (J : Ideal A)
    (hα : Function.Injective (lsmulLift I M))
    (hβ : Module.Flat (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))) :
    Function.Injective (lsmulLift (J ⊓ I) M) := by
  rw [← lsmulLift_comp_rTensor (M := M) (I := I) (J := J ⊓ I) inf_le_right]
  exact hα.comp (rTensor_inclusion_injective_p I hI hβ inf_le_right)

/-- **Square-zero descent for flatness.**  Let `A` be a commutative ring, `I ⊆ A` with `I ^ 2 = ⊥`
and `M` an `A`-module.  If `I ⊗[A] M → M` is injective and `M ⧸ I • ⊤` is flat over `A ⧸ I`, then
`M` is flat over `A`. -/
theorem flat_of_flat_mod_sqZero_v2 {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (hI : I ^ 2 = ⊥)
    (hα : Function.Injective (TensorProduct.lift ((LinearMap.lsmul A M).comp I.subtype)))
    (hβ : Module.Flat (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))) :
    Module.Flat A M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro J hJ
  change Function.Injective (lsmulLift J M)
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have hx0 : lsmulLift J M x = 0 := hx
  have hxrange := ker_lsmulLift_le_range (M := M) I hI J hβ hx
  rw [LinearMap.mem_range] at hxrange
  obtain ⟨y, rfl⟩ := hxrange
  have hy0 : lsmulLift (J ⊓ I) M y = 0 := by
    rw [← lsmulLift_comp_rTensor (M := M) (I := J) (J := J ⊓ I) inf_le_left,
      LinearMap.comp_apply]
    exact hx0
  have hy : y = 0 :=
    lsmulLift_inf_injective (M := M) I hI J (by simpa [lsmulLift] using hα) hβ hy0
  rw [hy, map_zero]

end Work.DSM2b
