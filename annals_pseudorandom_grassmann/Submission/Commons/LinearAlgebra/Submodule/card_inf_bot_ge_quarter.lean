import Mathlib
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_inf_eq
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq
import Submission.Commons.Combinatorics.QBinomial.alt_sum_eq_one
import Submission.Commons.Combinatorics.QBinomial.gb_le_four_mul_pow_mul_gb_sub

namespace Commons.LinearAlgebra.Submodule

open Module
open Finset
set_option autoImplicit false

/-- The number of `m`-dimensional subspaces of a finite `𝔽₂`-space depends only on the
dimension of the ambient space: it is the Gaussian binomial `gb (finrank V) m`. -/
theorem card_submodule_finrank_eq_gb {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (m : ℕ) :
    Nat.card {W : Submodule (ZMod 2) V // Module.finrank (ZMod 2) W = m} =
      Commons.Combinatorics.QBinomial.gb (Module.finrank (ZMod 2) V) m := by
  have hn : Module.finrank (ZMod 2) V =
      Module.finrank (ZMod 2) (Fin (Module.finrank (ZMod 2) V) → ZMod 2) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  exact Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq hn

/-- **The number of `m`-subspaces of `V` meeting a fixed `d`-subspace trivially.**
For `D ≤ V` with `finrank D = d` and `m + d ≤ finrank V`, exactly
`2 ^ (m * d) * [finrank V - d choose m]_2` of the `m`-dimensional subspaces `W ≤ V`
satisfy `W ⊓ D = ⊥`.

This is `Commons.LinearAlgebra.Submodule.card_submodule_finrank_inf_eq` (`L = D`, `ℓ = d`,
`ℓ₀ = m`, `j = 0`), the two Gaussian-binomial factors `[d choose 0]_2 = 1` and
`[finrank V - d choose m]_2` being the count of the `m`-subspaces of a complement. -/
theorem card_inf_bot_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (m d : ℕ) (D : Submodule (ZMod 2) V) (hD : Module.finrank (ZMod 2) D = d)
    (h : m + d ≤ Module.finrank (ZMod 2) V) :
    Nat.card {W : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) W = m ∧ W ⊓ D = ⊥} =
      2 ^ (m * d) * Commons.Combinatorics.QBinomial.gb (Module.finrank (ZMod 2) V - d) m := by
  have hVfin : m ≤ Module.finrank (ZMod 2) V := by omega
  have hgood : Nat.card {W : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) W = m ∧ W ⊓ D = ⊥} =
      Nat.card {L' : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) L' = m ∧ Module.finrank (ZMod 2) ↥(D ⊓ L') = 0} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro W
    constructor
    · rintro ⟨hW, hbot⟩
      refine ⟨hW, ?_⟩
      rw [inf_comm, hbot]
      simp
    · rintro ⟨hW, hfin⟩
      refine ⟨hW, ?_⟩
      rw [inf_comm]
      exact Submodule.finrank_eq_zero.mp hfin
  rw [hgood]
  have hcount := Commons.LinearAlgebra.Submodule.card_submodule_finrank_inf_eq (V := V) D d m 0 hD
    (Nat.zero_le d) (Nat.zero_le m) hVfin
  rw [hcount]
  have e1 : Nat.card {W : Submodule (ZMod 2) (Fin d → ZMod 2) //
      Module.finrank (ZMod 2) W = 0} = 1 := Commons.Combinatorics.QBinomial.gb_zero d
  have e2 : Nat.card {W : Submodule (ZMod 2) (Fin (Module.finrank (ZMod 2) V - d) → ZMod 2) //
      Module.finrank (ZMod 2) W = m} =
      Commons.Combinatorics.QBinomial.gb (Module.finrank (ZMod 2) V - d) m := rfl
  simp only [Nat.sub_zero]
  rw [e1, e2]
  rw [mul_one, Nat.mul_comm d m]

/-- **Most `m`-subspaces of a finite `𝔽₂`-space meet a fixed `d`-subspace trivially.**
If `m + d ≤ finrank V`, then at least a quarter of the `m`-dimensional subspaces `W ≤ V`
satisfy `W ⊓ D = ⊥`.

Hint: the number of `W` with `W ⊓ D = ⊥` is `2^(m d) * [finrank V - d choose m]_2` and the
total is `[finrank V choose m]_2`; their ratio equals
`∏_{i<m} (1 - 2^-(finrank V - d - i)) / (1 - 2^-(finrank V - i)) ≥ ∏_{j≥1} (1 - 2^-j) ≥ 1/4`.
This is a mild generalisation of `Commons.Analysis.Sum.card_good_submodule_ge_quarter` (which
is the case `V = 𝔽₂^n`, `m = ℓ`, `d = n - ℓ`, `D = ker` of the projection to the first `ℓ`
coordinates) and its proof should follow the same route. -/
theorem card_inf_bot_ge_quarter {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (m d : ℕ) (D : Submodule (ZMod 2) V) (hD : Module.finrank (ZMod 2) D = d)
    (h : m + d ≤ Module.finrank (ZMod 2) V) :
    4 * Nat.card {W : Submodule (ZMod 2) V // Module.finrank (ZMod 2) W = m ∧ W ⊓ D = ⊥}
      ≥ Nat.card {W : Submodule (ZMod 2) V // Module.finrank (ZMod 2) W = m} := by
  rw [card_submodule_finrank_eq_gb (V := V) m, card_inf_bot_eq (V := V) m d D hD h]
  rw [← Nat.mul_assoc]
  exact Commons.Combinatorics.QBinomial.gb_le_four_mul_pow_mul_gb_sub
    (Module.finrank (ZMod 2) V) m d h

end Commons.LinearAlgebra.Submodule
