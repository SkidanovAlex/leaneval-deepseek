import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.LTDDefs.DecompAction
import Submission.Work.SSGRoute.mup_local_defs
import Submission.Work.AbsoluteKummer.All
import Submission.Work.SSGRoute.PT.Hilbert90IsAlgClosure
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for local Kummer theory at a decomposition group

Shared definitions for `Work.SSGRoute.PTembedding.h1loc_mup_card_kummer`:

* `MupKummer.muMapOfField` / `MupKummer.instDistribMulActionAddRootsOfUnityOfField` — the
  natural Galois action on the `n`-th roots of unity of a *general* field extension `E/F`
  (the workspace's `Work.AbsoluteKummer.instDistribMulActionAddRootsOfUnity` is hardwired to
  `AlgebraicClosure k`);
* `MupKummer.subDistribMulAction` — the action of a subgroup `H ≤ Ω ≃ₐ[k] Ω` on a
  `Gal(K/k)`-module, through the restriction `res k K`;
* `MupKummer.isClosed_decomp'` / `MupKummer.fixingSubgroup_decompField` — the decomposition group
  of a finite place is closed, so it is the fixing subgroup of its fixed field (the
  *decomposition field* `mup.decompField k Ω A`).
-/

open scoped Classical
open Work.AbsoluteKummer

set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace Work.SSGRoute.PTembedding

noncomputable section

namespace MupKummer

/-! ## The natural Galois action on `μ_n` over a general extension -/

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

/-- The natural action of a field automorphism on the `n`-th roots of unity, as a monoid
homomorphism for each automorphism. -/
def muMapOfField (n : ℕ) (σ : E ≃ₐ[F] E) : rootsOfUnity n E →* rootsOfUnity n E where
  toFun u := ⟨Work.SSGRoute.PT.algEquivUnitsMapOfField F E σ (u : Eˣ), by
    rw [mem_rootsOfUnity']
    show ((Work.SSGRoute.PT.algEquivUnitsMapOfField F E σ (u : Eˣ) : Eˣ) : E) ^ n = 1
    rw [Work.SSGRoute.PT.algEquivUnitsMapOfField_coe, ← map_pow,
      (mem_rootsOfUnity' n (u : Eˣ)).mp u.2, map_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp)

@[simp] theorem muMapOfField_coe (n : ℕ) (σ : E ≃ₐ[F] E) (u : rootsOfUnity n E) :
    ((muMapOfField F E n σ u : rootsOfUnity n E) : Eˣ) =
      Work.SSGRoute.PT.algEquivUnitsMapOfField F E σ (u : Eˣ) := rfl

theorem muMapOfField_one (n : ℕ) :
    muMapOfField F E n (1 : E ≃ₐ[F] E) = MonoidHom.id (rootsOfUnity n E) := by
  refine MonoidHom.ext (fun u => ?_)
  exact Subtype.ext (Work.SSGRoute.PT.algEquivUnitsMapOfField_one (F := F) (E := E) (u : Eˣ))

theorem muMapOfField_mul (n : ℕ) (σ τ : E ≃ₐ[F] E) :
    muMapOfField F E n (σ * τ) = (muMapOfField F E n σ).comp (muMapOfField F E n τ) := by
  refine MonoidHom.ext (fun u => Subtype.ext ?_)
  rw [MonoidHom.comp_apply, muMapOfField_coe, muMapOfField_coe, muMapOfField_coe]
  exact (Work.SSGRoute.PT.algEquivUnitsMapOfField_mul (F := F) (E := E) σ τ (u : Eˣ)).symm

/-- The Galois action of `E ≃ₐ[F] E` on `Additive (rootsOfUnity n E)`. -/
noncomputable instance (priority := 100) instDistribMulActionAddRootsOfUnityOfField (n : ℕ) :
    DistribMulAction (E ≃ₐ[F] E) (Additive (rootsOfUnity n E)) where
  smul σ a := Additive.ofMul (muMapOfField F E n σ (Additive.toMul a))
  one_smul a := by
    show Additive.ofMul (muMapOfField F E n 1 (Additive.toMul a)) = a
    rw [muMapOfField_one F E n]
    rfl
  mul_smul σ τ a := by
    change Additive.ofMul (muMapOfField F E n (σ * τ) (Additive.toMul a)) =
      Additive.ofMul (muMapOfField F E n σ (muMapOfField F E n τ (Additive.toMul a)))
    rw [muMapOfField_mul F E n σ τ, MonoidHom.comp_apply]
  smul_zero σ := by
    show Additive.ofMul (muMapOfField F E n σ 1) = 0
    rw [map_one, ofMul_one]
  smul_add σ a b := by
    show Additive.ofMul (muMapOfField F E n σ (Additive.toMul a * Additive.toMul b)) =
      Additive.ofMul (muMapOfField F E n σ (Additive.toMul a)) +
        Additive.ofMul (muMapOfField F E n σ (Additive.toMul b))
    rw [map_mul, ofMul_mul]

@[simp] theorem addRootsOfUnity_smul_toMul_val (n : ℕ) (σ : E ≃ₐ[F] E)
    (a : Additive (rootsOfUnity n E)) :
    ((Additive.toMul (σ • a) : rootsOfUnity n E) : Eˣ) =
      Work.SSGRoute.PT.algEquivUnitsMapOfField F E σ
        ((Additive.toMul a : rootsOfUnity n E) : Eˣ) := rfl

end MupKummer

/-! ## The action of a subgroup of `G_k` through the restriction `res k K` -/

section SubAction

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- The action of `H ≤ Ω ≃ₐ[k] Ω` on a `Gal(K/k)`-module, through the restriction `res k K`. -/
@[instance_reducible] def subDistribMulAction {K : IntermediateField k Ω} [Normal k K]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (M : Type)
    [AddMonoid M] [DistribMulAction (K ≃ₐ[k] K) M] : DistribMulAction ↥H M where
  smul h m := SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m
  one_smul m := by
    show SSGRoute.res k K ((1 : ↥H) : Ω ≃ₐ[k] Ω) • m = m
    rw [show ((1 : ↥H) : Ω ≃ₐ[k] Ω) = 1 from rfl, map_one, one_smul]
  mul_smul h1 h2 m := by
    show SSGRoute.res k K (((h1 * h2 : ↥H)) : Ω ≃ₐ[k] Ω) • m =
      SSGRoute.res k K (h1 : Ω ≃ₐ[k] Ω) • (SSGRoute.res k K (h2 : Ω ≃ₐ[k] Ω) • m)
    rw [show ((h1 * h2 : ↥H) : Ω ≃ₐ[k] Ω) = (h1 : Ω ≃ₐ[k] Ω) * (h2 : Ω ≃ₐ[k] Ω) from rfl,
      map_mul, mul_smul]
  smul_zero h := smul_zero _
  smul_add h m n := smul_add _ _ _

@[simp] theorem subDistribMulAction_smul {K : IntermediateField k Ω} [Normal k K]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (M : Type) [AddMonoid M] [DistribMulAction (K ≃ₐ[k] K) M]
    (h : ↥H) (m : M) :
    @SMul.smul ↥H M (subDistribMulAction (K := K) H M).toSMul h m =
      SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m := rfl

end SubAction

/-! ## Closedness of the decomposition group and its fixing subgroup -/

section Decomp

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- The decomposition group of a place of `Ω` is closed in the Krull topology. -/
theorem isClosed_decomp' (A : ValuationSubring Ω) :
    IsClosed (SSGRoute.decomp k A : Set (Ω ≃ₐ[k] Ω)) := by
  haveI : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  exact Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring (K := k) (K' := Ω) A

/-- The decomposition group of `A` is the fixing subgroup of the decomposition field
`mup.decompField k Ω A`. -/
theorem fixingSubgroup_decompField (A : ValuationSubring Ω) :
    (Work.SSGRoute.mup.decompField k Ω A).fixingSubgroup = SSGRoute.decomp k A := by
  haveI : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  have h := InfiniteGalois.fixingSubgroup_fixedField (k := k) (K := Ω)
    (⟨SSGRoute.decomp k A, isClosed_decomp' k Ω A⟩ :
      ClosedSubgroup (Ω ≃ₐ[k] Ω))
  simpa [Work.SSGRoute.mup.decompField] using h

end Decomp

end

end Work.SSGRoute.PTembedding
