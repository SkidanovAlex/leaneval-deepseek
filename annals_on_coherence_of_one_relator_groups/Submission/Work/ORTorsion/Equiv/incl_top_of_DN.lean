import Mathlib
import Submission.Work.ORTorsion.Defs

namespace Work.ORTorsion.Equiv

open scoped TensorProduct
open Work.ORTorsion

/-- **The correct (diagonal) form of the intended `incl_top_of_DN`.**

The `K`-linear map `TensorProduct.map LinearMap.id
(Subalgebra.inclusion (L.D_mono (le_top : N ≤ ⊤))).toLinearMap` intertwines the *diagonal* action
of `K[N]` on `V ⊗[K] ↥(L.D N)` with the *diagonal* action of `K[N]` on `V ⊗[K] ↥(L.D ⊤)`, the
latter expressed through `diagRingHom (MonoidHom.id G) L.genTop ∘ mapToG N`.

This is exactly `Work.ORTorsion.Descent.diagAct_map` applied to the inclusion
`↥(L.D N) →ₗ[↥(L.D N)] ↥(L.D ⊤)` (and `x • z` on the source coincides with
`diagAct L N ↥(L.D N) x z`). -/
theorem incl_top_of_DN_diag {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {N : Subgroup G} (x : MonoidAlgebra K N) (z : V ⊗[K] ↥(L.D N)) :
    TensorProduct.map LinearMap.id
        (Subalgebra.inclusion (L.D_mono (le_top : N ≤ ⊤))).toLinearMap (x • z)
      = ((diagRingHom (K := K) (V := V) (MonoidHom.id G) L.genTop) (mapToG N x))
          (TensorProduct.map LinearMap.id
            (Subalgebra.inclusion (L.D_mono (le_top : N ≤ ⊤))).toLinearMap z) := by
  -- Key identity on the group generators: the inclusion intertwines `diagElem` for `N` and for `G`.
  have hdiag : ∀ (h : N) (w : V ⊗[K] ↥(L.D N)),
      TensorProduct.map LinearMap.id (Subalgebra.inclusion (L.D_mono (le_top : N ≤ ⊤))).toLinearMap
          (diagElem N.subtype (L.genD N) h w)
        = diagElem (MonoidHom.id G) L.genTop (h : G)
            (TensorProduct.map LinearMap.id
              (Subalgebra.inclusion (L.D_mono (le_top : N ≤ ⊤))).toLinearMap w) := by
    intro h w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v d =>
        rw [diagElem_apply_tmul, TensorProduct.map_tmul]
        rw [TensorProduct.map_tmul, diagElem_apply_tmul]
        simp only [LinearMap.id_coe, id_eq, MonoidHom.id_apply]
        rw [show (Subalgebra.inclusion (L.D_mono (le_top : N ≤ ⊤))).toLinearMap ((L.genD N) h * d)
              = L.genTop (h : G)
                  * ((Subalgebra.inclusion (L.D_mono (le_top : N ≤ ⊤))).toLinearMap d) from by
            rw [show (Subalgebra.inclusion (L.D_mono (le_top : N ≤ ⊤))).toLinearMap ((L.genD N) h * d)
                  = Subalgebra.inclusion (L.D_mono (le_top : N ≤ ⊤)) ((L.genD N) h * d) from rfl,
              map_mul]
            rfl]
        rfl
    | add w1 w2 ih1 ih2 => simp only [map_add, ih1, ih2]
  have hmapToG : ∀ (h : N) (c : K), mapToG N (MonoidAlgebra.single h c) = MonoidAlgebra.single (h : G) c := by
    intro h c
    rw [mapToG, MonoidAlgebra.lift_single]
    simp [MonoidAlgebra.smul_single]
  have hmain : ∀ (y : MonoidAlgebra K N) (w : V ⊗[K] ↥(L.D N)),
      TensorProduct.map LinearMap.id (Subalgebra.inclusion (L.D_mono (le_top : N ≤ ⊤))).toLinearMap (y • w)
        = ((diagRingHom (K := K) (V := V) (MonoidHom.id G) L.genTop) (mapToG N y))
            (TensorProduct.map LinearMap.id
              (Subalgebra.inclusion (L.D_mono (le_top : N ≤ ⊤))).toLinearMap w) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => intro w; simp
    | add a b ha hb => intro w; simp only [add_smul, map_add, LinearMap.add_apply, ha, hb]
    | single h c =>
        intro w
        have h1 : (MonoidAlgebra.single h c : MonoidAlgebra K N) • w
            = c • diagElem N.subtype (L.genD N) h w := by
          rw [show (MonoidAlgebra.single h c : MonoidAlgebra K N) • w
                = ((diagRingHom (K := K) (V := V) N.subtype (L.genD N))
                    (MonoidAlgebra.single h c)) w from rfl]
          conv_lhs => rw [show (diagRingHom (K := K) (V := V) N.subtype (L.genD N))
                (MonoidAlgebra.single h c) = c • diagElem N.subtype (L.genD N) h from by
              show ((MonoidAlgebra.lift K (Module.End K (V ⊗[K] ↥(L.D N))) ↥N
                    (diagGroupHom N.subtype (L.genD N))) (MonoidAlgebra.single h c)) = _
              rw [MonoidAlgebra.lift_single]; rfl]
          rw [LinearMap.smul_apply]
        have h2 : (diagRingHom (K := K) (V := V) (MonoidHom.id G) L.genTop)
              (mapToG N (MonoidAlgebra.single h c))
            = c • diagElem (MonoidHom.id G) L.genTop (h : G) := by
          rw [hmapToG h c]
          show ((MonoidAlgebra.lift K (Module.End K (V ⊗[K] ↥(L.D ⊤))) G
                (diagGroupHom (MonoidHom.id G) L.genTop)) (MonoidAlgebra.single (h : G) c)) = _
          rw [MonoidAlgebra.lift_single]; rfl
        rw [h1, LinearMap.map_smul, hdiag, h2, LinearMap.smul_apply]
  exact hmain x z

/-! ### The statement used by the descent step

`incl_top_of_DN` is the scalar-multiplication form of `incl_top_of_DN_diag`: since
`instDiagTopSmul` (priority 2000) is the `SMul (MonoidAlgebra K G) (V ⊗[K] ↥(L.D ⊤))` instance
used in the statement, the scalar `mapToG N x` acts *diagonally* and the two statements are
equivalent by `TorsionData.instDiagTopSmul_apply`. -/
theorem incl_top_of_DN {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {N : Subgroup G} (x : MonoidAlgebra K N) (z : V ⊗[K] ↥(L.D N)) :
    TensorProduct.map LinearMap.id
        (Subalgebra.inclusion (L.D_mono (le_top : N ≤ ⊤))).toLinearMap (x • z)
      = (mapToG N x) • (TensorProduct.map LinearMap.id
          (Subalgebra.inclusion (L.D_mono (le_top : N ≤ ⊤))).toLinearMap z) := by
  rw [TorsionData.instDiagTopSmul_apply (L := L) V]
  exact incl_top_of_DN_diag L x z

end Work.ORTorsion.Equiv
