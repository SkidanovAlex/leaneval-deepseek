import Mathlib
import Submission.Commons.Combinatorics.QBinomial.sum_Icc_card_submodule_finrank_eq_indicator
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq

namespace Commons.LinearAlgebra.Submodule

open Module

/-- The number of `i`-dimensional submodules of a finite-dimensional `𝔽₂`-vector space `V'`
equals the Gaussian binomial coefficient `gb (finrank V') i`.  Equivalently, this is the number
of `i`-dimensional subspaces of `V'` (counted as submodules of the ambient space contained
in `V'`). -/
theorem card_submodule_le_finrank_eq_gb (n : ℕ) (V' : Submodule (ZMod 2) (Fin n → ZMod 2)) (i : ℕ) :
    Nat.card {V₁ : Submodule (ZMod 2) (Fin n → ZMod 2) //
        V₁ ≤ V' ∧ Module.finrank (ZMod 2) V₁ = i}
      = Commons.Combinatorics.QBinomial.gb (Module.finrank (ZMod 2) V') i := by
  -- Submodules of `V'` correspond to submodules of the ambient space contained in `V'`.
  have step1 : Nat.card {V₁ : Submodule (ZMod 2) (Fin n → ZMod 2) //
        V₁ ≤ V' ∧ Module.finrank (ZMod 2) V₁ = i}
      = Nat.card {x : {V₁ : Submodule (ZMod 2) (Fin n → ZMod 2) // V₁ ≤ V'} //
          Module.finrank (ZMod 2) x.val = i} :=
    (Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun V₁ : Submodule (ZMod 2) (Fin n → ZMod 2) => V₁ ≤ V')
      (fun V₁ => Module.finrank (ZMod 2) V₁ = i))).symm
  have step2 : Nat.card {x : {V₁ : Submodule (ZMod 2) (Fin n → ZMod 2) // V₁ ≤ V'} //
          Module.finrank (ZMod 2) x.val = i}
      = Nat.card {q : Submodule (ZMod 2) V' // Module.finrank (ZMod 2) q = i} :=
    (Nat.card_congr (Equiv.subtypeEquiv (Submodule.MapSubtype.orderIso V').toEquiv
      (fun q => by
        show Module.finrank (ZMod 2) q = i ↔
          Module.finrank (ZMod 2) (Submodule.map V'.subtype q) = i
        rw [Submodule.finrank_map_subtype_eq]))).symm
  rw [step1, step2]
  -- `gb` counts submodules of `𝔽₂ ^ (finrank V')`, isomorphic to `V'`.
  unfold Commons.Combinatorics.QBinomial.gb
  exact (Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq
    (K := ZMod 2) (V := Fin (Module.finrank (ZMod 2) V') → ZMod 2) (V' := V')
    (by rw [Module.finrank_pi, Fintype.card_fin]) (ℓ := i)).symm

end Commons.LinearAlgebra.Submodule
