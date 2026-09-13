import Mathlib
import Submission.Commons.LinearAlgebra.Submodule.card_hom_subtype

namespace Commons.LinearAlgebra.Submodule

set_option linter.style.haveILetI false

open Module

/-- Every submodule of a vector space over a division ring is the range of an endomorphism of the
ambient space.  Concretely, using the (chosen) left inverse of the inclusion `p.subtype`, the map
`p.subtype ∘ p.subtype.leftInverse` is a projection onto `p`. -/
private theorem exists_linearMap_range_eq {K V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] (p : Submodule K V) : ∃ f : V →ₗ[K] V, LinearMap.range f = p := by
  refine ⟨p.subtype.comp p.subtype.leftInverse, ?_⟩
  have hsurj : LinearMap.range p.subtype.leftInverse = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨(y : V), LinearMap.leftInverse_apply_of_inj p.ker_subtype y⟩
  rw [LinearMap.range_comp, hsurj, Submodule.map_subtype_top]

/-- A finite vector space over a finite field has at most `|K| ^ (finrank K V * finrank K V)`
submodules: taking ranges of endomorphisms gives a surjection onto the set of submodules, and
there are only `|K| ^ (finrank K V * finrank K V)` endomorphisms. -/
private theorem natCard_submodule_le_pow {K V : Type*} [Field K] [Fintype K] [AddCommGroup V]
    [Module K V] [Finite V] [Module.Finite K V] :
    Nat.card (Submodule K V) ≤ Nat.card K ^ (Module.finrank K V * Module.finrank K V) := by
  haveI : Finite (V →ₗ[K] V) :=
    Finite.of_injective (fun f : V →ₗ[K] V => (f : V → V)) fun _ _ h => DFunLike.coe_injective h
  calc Nat.card (Submodule K V)
      ≤ Nat.card (V →ₗ[K] V) :=
        Nat.card_le_card_of_surjective (fun f : V →ₗ[K] V => LinearMap.range f)
          (fun T => exists_linearMap_range_eq T)
    _ = Nat.card K ^ (Module.finrank K V * Module.finrank K V) := natCard_linearMap K V V

theorem card_submodule_ge_le_pow {n : ℕ} (W : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Nat.card {W' : Submodule (ZMod 2) (Fin n → ZMod 2) // W ≤ W'} ≤
      2 ^ ((n - Module.finrank (ZMod 2) W) * (n - Module.finrank (ZMod 2) W)) := by
  classical
  haveI : Finite ((Fin n → ZMod 2) ⧸ W) :=
    Finite.of_surjective W.mkQ (Submodule.mkQ_surjective W)
  haveI : Module.Finite (ZMod 2) ((Fin n → ZMod 2) ⧸ W) :=
    Module.Finite.of_surjective W.mkQ (Submodule.mkQ_surjective W)
  -- Correspondence theorem: submodules `W' ≥ W` of `V` are the submodules of `V ⧸ W`.
  have hcard : Nat.card {W' : Submodule (ZMod 2) (Fin n → ZMod 2) // W ≤ W'} =
      Nat.card (Submodule (ZMod 2) ((Fin n → ZMod 2) ⧸ W)) :=
    Nat.card_congr (Submodule.comapMkQRelIso (p := W)).toEquiv.symm
  rw [hcard]
  have hd : Module.finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ W) =
      n - Module.finrank (ZMod 2) W := by
    have h := Submodule.finrank_quotient_add_finrank (R := ZMod 2) (M := Fin n → ZMod 2) W
    rw [Module.finrank_fin_fun] at h
    omega
  calc Nat.card (Submodule (ZMod 2) ((Fin n → ZMod 2) ⧸ W))
      ≤ Nat.card (ZMod 2) ^ (Module.finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ W)
          * Module.finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ W)) :=
        natCard_submodule_le_pow (K := ZMod 2) (V := (Fin n → ZMod 2) ⧸ W)
    _ = 2 ^ ((n - Module.finrank (ZMod 2) W) * (n - Module.finrank (ZMod 2) W)) := by
        rw [hd, Nat.card_zmod]

end Commons.LinearAlgebra.Submodule
