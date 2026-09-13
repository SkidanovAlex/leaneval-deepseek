import Mathlib.Algebra.Field.ZMod
import Submission.Commons.LinearAlgebra.FiniteDim.finrank_comap_of_linearEquiv
import Submission.Commons.LinearAlgebra.Matrix.finrank_antisym_columns_le

namespace Commons.LinearAlgebra.Submodule

open Module
set_option autoImplicit false

/-- `Submodule.comap` along a composition of linear equivalences: preimage under `e1.trans e2`
agrees with iterated preimages. -/
lemma comap_trans_coe {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (e1 e2 : M ≃ₗ[R] M) (K : Submodule R M) :
    Submodule.comap ((e1.trans e2 : M ≃ₗ[R] M) : M →ₗ[R] M) K
      = Submodule.comap (e1 : M →ₗ[R] M) (Submodule.comap (e2 : M →ₗ[R] M) K) := by
  rw [LinearEquiv.coe_trans]
  exact Submodule.comap_comp (e1 : M →ₗ[R] M) (e2 : M →ₗ[R] M) K

/-- **Fibre decomposition of the map `e ↦ comap e K`.**
The map `e ↦ Submodule.comap e K` from `E ≃ₗ E` to the `finrank K`-dimensional subspaces of
`E` is surjective, and all its fibres have the same cardinality
`κ = Nat.card {e // comap e K = K}` (use `Submodule.comap_comp` and the fact that the
`E ≃ₗ E`-action on subspaces of a fixed dimension is transitive).  Hence for any predicate `P`
of subspaces, the number of `e` with `P (comap e K)` equals `κ` times the number of
`finrank K`-dimensional subspaces with `P`.

Proof route: `{e // P (comap e K)} ≃ Σ D : {D // finrank D = finrank K ∧ P D}, {e // comap e K = D}`
(the standard fibre decomposition) and `Nat.card_sigma`. -/
theorem card_comap_linearEquiv {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Fintype E]
    (K : Submodule (ZMod 2) E) (P : Submodule (ZMod 2) E → Prop) [DecidablePred P] :
    Nat.card {e : E ≃ₗ[ZMod 2] E // P (Submodule.comap (e : E →ₗ[ZMod 2] E) K)}
      = Nat.card {e : E ≃ₗ[ZMod 2] E //
            Submodule.comap (e : E →ₗ[ZMod 2] E) K = K}
        * Nat.card {D : Submodule (ZMod 2) E //
            Module.finrank (ZMod 2) D = Module.finrank (ZMod 2) K ∧ P D} := by
  classical
  let Idx : Type _ := {D : Submodule (ZMod 2) E //
      Module.finrank (ZMod 2) D = Module.finrank (ZMod 2) K ∧ P D}
  let FibK : Type _ := {e : E ≃ₗ[ZMod 2] E //
      Submodule.comap (e : E →ₗ[ZMod 2] E) K = K}
  have hf : ∀ e : E ≃ₗ[ZMod 2] E,
      Module.finrank (ZMod 2) (Submodule.comap (e : E →ₗ[ZMod 2] E) K)
        = Module.finrank (ZMod 2) K :=
    fun e => Commons.LinearAlgebra.FiniteDim.finrank_comap_of_linearEquiv e K
  -- Step 1: fibre decomposition `{e // P (comap e K)} ≃ Σ D, {e // comap e K = D}`.
  let Φ1 : {e : E ≃ₗ[ZMod 2] E // P (Submodule.comap (e : E →ₗ[ZMod 2] E) K)} ≃
      (Σ D : Idx, {e : E ≃ₗ[ZMod 2] E //
        Submodule.comap (e : E →ₗ[ZMod 2] E) K = D.1}) :=
    { toFun := fun e =>
        ⟨⟨Submodule.comap (e.1 : E →ₗ[ZMod 2] E) K, hf e.1, e.2⟩, ⟨e.1, rfl⟩⟩
      invFun := fun x => ⟨x.2.1, by rw [x.2.2]; exact x.1.2.2⟩
      left_inv := fun e => Subtype.ext rfl
      right_inv := fun x => by
        obtain ⟨⟨Dval, hDval⟩, e, he⟩ := x
        change Submodule.comap (e : E →ₗ[ZMod 2] E) K = Dval at he
        subst he
        dsimp only }
  -- Step 2: a witness `e0 D` with `comap (e0 D) K = D`, and the fibre equivalence.
  have hex : ∀ D : Idx, ∃ e0 : E ≃ₗ[ZMod 2] E,
      Submodule.comap (e0 : E →ₗ[ZMod 2] E) K = D.1 := by
    intro D
    obtain ⟨w, hw⟩ :=
      Commons.LinearAlgebra.Matrix.exists_linearEquiv_map_eq (K := ZMod 2) (V := E) K D.1 D.2.1.symm
    exact ⟨w.symm, by rw [← Submodule.map_equiv_eq_comap_symm w K]; exact hw⟩
  let e0 : Idx → E ≃ₗ[ZMod 2] E := fun D => Classical.choose (hex D)
  have he0 : ∀ D : Idx, Submodule.comap (e0 D : E →ₗ[ZMod 2] E) K = D.1 :=
    fun D => Classical.choose_spec (hex D)
  have hcancel : ∀ D : Idx,
      Submodule.comap (((e0 D).symm : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E)
        (Submodule.comap ((e0 D) : E →ₗ[ZMod 2] E) K) = K := by
    intro D
    rw [← comap_trans_coe (e0 D).symm (e0 D) K, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, Submodule.comap_id]
  let fibreEquiv : ∀ D : Idx,
      {e : E ≃ₗ[ZMod 2] E // Submodule.comap (e : E →ₗ[ZMod 2] E) K = D.1} ≃ FibK :=
    fun D =>
    { toFun := fun e =>
        ⟨(e0 D).symm.trans e.1, by
          rw [comap_trans_coe (e0 D).symm e.1 K, e.2, ← he0 D, hcancel D]⟩
      invFun := fun g =>
        ⟨(e0 D).trans g.1, by
          rw [comap_trans_coe (e0 D) g.1 K, g.2, he0 D]⟩
      left_inv := fun e => Subtype.ext (by
        show (e0 D).trans ((e0 D).symm.trans e.1) = e.1
        rw [← LinearEquiv.trans_assoc, LinearEquiv.self_trans_symm, LinearEquiv.refl_trans])
      right_inv := fun g => Subtype.ext (by
        show (e0 D).symm.trans ((e0 D).trans g.1) = g.1
        rw [← LinearEquiv.trans_assoc, LinearEquiv.symm_trans_self, LinearEquiv.refl_trans]) }
  -- Step 3: assemble, using `Nat.card (α × β) = Nat.card α * Nat.card β`.
  have hcard : Nat.card {e : E ≃ₗ[ZMod 2] E //
        P (Submodule.comap (e : E →ₗ[ZMod 2] E) K)}
      = Nat.card (FibK × Idx) :=
    Nat.card_congr ((Φ1.trans (Equiv.sigmaCongrRight fibreEquiv)).trans
      ((Equiv.sigmaEquivProd Idx FibK).trans (Equiv.prodComm Idx FibK)))
  rw [hcard, Nat.card_prod]

end Commons.LinearAlgebra.Submodule