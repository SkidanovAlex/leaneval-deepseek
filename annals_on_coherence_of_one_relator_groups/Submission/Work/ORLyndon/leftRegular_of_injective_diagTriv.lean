import Mathlib
import Submission.Work.ORTorsion.Main

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped TensorProduct

namespace Work.ORLyndon

/-- **Diagonal action versus left regular action.**

Let `K` be a field, `G` a group, and suppose `K` carries a `K[G]`-module structure compatible
with the `K`-algebra structure (`IsScalarTower`) and such that every group element fixes `1 ∈ K`
(the hypothesis `hone`).  For `L` a torsion datum, `β ∈ K[G]` and `y ∈ D(⊤)`, the diagonal action
of `β` on `K ⊗[K] D(⊤)` (where the first factor is the trivial module) is, under the canonical
identification `K ⊗[K] M ≃ M`, left multiplication by `lift K D(⊤) G genTop β`:

`β • (1 ⊗ y) = 1 ⊗ (lift β * y)`.

Consequently, if the diagonal action of `β` is injective, then `lift β` is a left non-zero-divisor
on `D(⊤)`. -/
theorem leftRegular_of_injective_diagTriv {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Algebra K U] [Module (MonoidAlgebra K G) K] [IsScalarTower K (MonoidAlgebra K G) K]
    (hone : ∀ g : G, (MonoidAlgebra.single g (1 : K) : MonoidAlgebra K G) • (1 : K) = 1)
    (L : Work.ORTorsion.TorsionData K G U) (β : MonoidAlgebra K G)
    (hinj : Function.Injective (fun m : TensorProduct K K (L.D ⊤) => β • m)) :
    ∀ y : (L.D ⊤), MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop β * y = 0 → y = 0 := by
  classical
  intro y hy
  -- The key identity: the diagonal action of `β'` on `1 ⊗ y` is `1 ⊗ (lift β' * y)`.
  have key : ∀ β' : MonoidAlgebra K G,
      (Work.ORTorsion.diagRingHom (MonoidHom.id G) L.genTop β') ((1 : K) ⊗ₜ[K] y)
        = (1 : K) ⊗ₜ[K] (MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop β' * y) := by
    intro β'
    induction β' using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x z hx hz =>
      have hA : (Work.ORTorsion.diagRingHom (MonoidHom.id G) L.genTop (x + z))
            ((1 : K) ⊗ₜ[K] y)
          = (Work.ORTorsion.diagRingHom (MonoidHom.id G) L.genTop x) ((1 : K) ⊗ₜ[K] y)
            + (Work.ORTorsion.diagRingHom (MonoidHom.id G) L.genTop z) ((1 : K) ⊗ₜ[K] y) := by
        rw [map_add]
        rfl
      have hL : MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop (x + z) * y
          = MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop x * y
            + MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop z * y := by
        rw [map_add, add_mul]
      rw [hA, hL, TensorProduct.tmul_add, hx, hz]
    | single g c =>
      rw [Work.ORTorsion.diagRingHom_single_coeff_apply, Work.ORTorsion.diagElem_apply_tmul,
        hone ((MonoidHom.id G) g), MonoidAlgebra.lift_single, smul_mul_assoc,
        TensorProduct.tmul_smul]
  -- `β` kills `1 ⊗ y`, hence by injectivity `1 ⊗ y = 0`, hence `y = 0`.
  have h1 : β • ((1 : K) ⊗ₜ[K] y) = β • (0 : TensorProduct K K (L.D ⊤)) := by
    rw [Work.ORTorsion.TorsionData.instDiagTopSmul_apply,
      Work.ORTorsion.TorsionData.instDiagTopSmul_apply, key β, hy]
    simp
  have h2 : (1 : K) ⊗ₜ[K] y = 0 := hinj h1
  have h3 : y = 0 := by
    have h := congrArg (TensorProduct.lid K ↥(L.D ⊤)) h2
    simpa using h
  exact h3

end Work.ORLyndon
