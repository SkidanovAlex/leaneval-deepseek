import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Commons.LinearAlgebra.Submodule

open Module
open _root_.Submodule

noncomputable section

/-- Dimension of the preimage of a subspace `T` of `V ⧸ A` under the quotient map:
`finrank (comap A.mkQ T) = finrank T + finrank A`.

Proof: the restriction of `A.mkQ` to `S := comap A.mkQ T` has kernel `A` (because
`A ≤ S` and `ker (A.mkQ) = A`) and range `T` (by surjectivity of `A.mkQ`); apply
the rank-nullity theorem. -/
lemma finrank_comap_mkQ_eq_add {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (A : Submodule K V) (T : Submodule K (V ⧸ A)) :
    Module.finrank K (comap A.mkQ T) = Module.finrank K T + Module.finrank K A := by
  classical
  let S : Submodule K V := comap A.mkQ T
  let g : S →ₗ[K] V ⧸ A := A.mkQ.comp S.subtype
  have hAS : A ≤ S := by
    simpa [S] using (Submodule.le_comap_mkQ (p := A) T)
  have hker_eq : LinearMap.ker g = A.comap S.subtype := by
    dsimp [g]
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hker_finrank : Module.finrank K (LinearMap.ker g) = Module.finrank K A := by
    rw [hker_eq]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (p := A) (q := S) hAS)
  have hrange_eq : LinearMap.range g = T := by
    dsimp [g]
    rw [LinearMap.range_comp, Submodule.range_subtype]
    change map A.mkQ (comap A.mkQ T) = T
    apply Submodule.map_comap_eq_self
    rw [Submodule.range_mkQ]
    exact le_top
  have hrange_finrank : Module.finrank K (LinearMap.range g) = Module.finrank K T := by
    rw [hrange_eq]
  have hranknullity := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange_finrank, hker_finrank] at hranknullity
  simpa [S] using hranknullity.symm

theorem card_superspaces_finrank_eq_quotient {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [Finite V] [Module.Finite K V] (A : Submodule K V)
    {ℓ : ℕ} (hA : Module.finrank K A ≤ ℓ) :
    Nat.card {W : Submodule K V // A ≤ W ∧ Module.finrank K W = ℓ} =
      Nat.card {T : Submodule K (V ⧸ A) // Module.finrank K T = ℓ - Module.finrank K A} := by
  classical
  -- The correspondence theorem: submodules of `V ⧸ A` biject with submodules `W ≥ A` of `V`,
  -- sending `T` to `comap A.mkQ T`.
  let e : Submodule K (V ⧸ A) ≃ {W : Submodule K V // A ≤ W} :=
    (Submodule.comapMkQRelIso (p := A)).toEquiv
  -- Dimension transport: `finrank (comap A.mkQ T) = ℓ` iff `finrank T = ℓ - finrank A`.
  have hp : ∀ T : Submodule K (V ⧸ A),
      Module.finrank K T = ℓ - Module.finrank K A ↔
        Module.finrank K ((e T).1) = ℓ := by
    intro T
    have hdim := finrank_comap_mkQ_eq_add (K := K) (V := V) A T
    constructor
    · intro ht
      change Module.finrank K (comap A.mkQ T) = ℓ
      rw [hdim, ht]
      omega
    · intro hw
      change Module.finrank K (comap A.mkQ T) = ℓ at hw
      rw [hdim] at hw
      omega
  let E : {T : Submodule K (V ⧸ A) // Module.finrank K T = ℓ - Module.finrank K A} ≃
      {W : Submodule K V // A ≤ W ∧ Module.finrank K W = ℓ} :=
    (Equiv.subtypeEquiv e hp).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun W : Submodule K V => A ≤ W)
        (fun W : Submodule K V => Module.finrank K W = ℓ))
  exact (Nat.card_congr E).symm

end

end Commons.LinearAlgebra.Submodule