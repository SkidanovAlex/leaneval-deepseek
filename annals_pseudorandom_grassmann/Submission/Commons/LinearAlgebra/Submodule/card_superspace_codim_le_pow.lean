import Mathlib
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_le_pow
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_compl
import Submission.Commons.LinearAlgebra.Submodule.card_superspaces_finrank_eq_quotient

namespace Commons.LinearAlgebra.Submodule

set_option linter.style.haveILetI false

open Module

/-- For a finite `K`-vector space `Q`, the number of submodules of dimension `finrank Q - j`
is at most `q ^ ((finrank Q - j) * j + j)`, where `q = Nat.card K`.

If `j ≤ finrank Q` this is Grassmann duality (`card_submodule_finrank_eq_compl`) combined with
the basic bound `card_submodule_finrank_le_pow`; if `j > finrank Q` there is exactly one such
submodule (`⊥`) and `q ^ j ≥ 1`. -/
theorem card_submodule_finrank_eq_sub_le_pow {K : Type*} [Field K] [Fintype K]
    {Q : Type*} [AddCommGroup Q] [Module K Q] [Finite Q] (j : ℕ) :
    Nat.card {T : Submodule K Q // Module.finrank K T = Module.finrank K Q - j}
      ≤ Nat.card K ^ ((Module.finrank K Q - j) * j + j) := by
  classical
  have hq : 1 ≤ Nat.card K := by
    have h := Fintype.one_lt_card (α := K)
    rw [Nat.card_eq_fintype_card]
    omega
  by_cases hj : j ≤ Module.finrank K Q
  · have heq : Nat.card {T : Submodule K Q // Module.finrank K T = Module.finrank K Q - j}
        = Nat.card {T : Submodule K Q // Module.finrank K T = j} :=
        (card_submodule_finrank_eq_compl (K := K) (V := Q) j hj).symm
    rw [heq]
    calc Nat.card {T : Submodule K Q // Module.finrank K T = j}
        ≤ Nat.card K ^ (j * (Module.finrank K Q - j) + j) :=
          card_submodule_finrank_le_pow (K := K) (V := Q) j
      _ = Nat.card K ^ ((Module.finrank K Q - j) * j + j) := by
          congr 1
          rw [Nat.mul_comm]
  · have h0 : Module.finrank K Q - j = 0 := Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp hj))
    rw [h0]
    calc Nat.card {T : Submodule K Q // Module.finrank K T = 0}
        ≤ Nat.card K ^ (0 * (Module.finrank K Q - 0) + 0) :=
          card_submodule_finrank_le_pow (K := K) (V := Q) 0
      _ = 1 := by simp
      _ ≤ Nat.card K ^ (0 * j + j) := by
          rw [Nat.zero_mul, Nat.zero_add]
          exact Nat.one_le_pow j (Nat.card K) (by omega)

theorem card_superspace_codim_le_pow {K : Type*} [Field K] [Fintype K]
    {V : Type*} [AddCommGroup V] [Module K V] [Finite V] (U : Submodule K V) (j : ℕ) :
    Nat.card {W : Submodule K V // U ≤ W ∧ Module.finrank K W = Module.finrank K V - j}
      ≤ Nat.card K ^ ((Module.finrank K V - Module.finrank K U - j) * j + j) := by
  classical
  haveI : Finite (V ⧸ U) := Finite.of_surjective U.mkQ (Submodule.mkQ_surjective U)
  have hfin : Module.finrank K (V ⧸ U) = Module.finrank K V - Module.finrank K U := by
    have h := Submodule.finrank_quotient_add_finrank (R := K) (M := V) U
    omega
  have hsub : (Module.finrank K V - j) - Module.finrank K U
      = (Module.finrank K V - Module.finrank K U) - j := by
    rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm]
  by_cases hA : Module.finrank K U ≤ Module.finrank K V - j
  · have hcount := card_superspaces_finrank_eq_quotient (K := K) (V := V) U
        (ℓ := Module.finrank K V - j) hA
    have h1 : Nat.card {T : Submodule K (V ⧸ U) //
          Module.finrank K T = (Module.finrank K V - j) - Module.finrank K U}
        = Nat.card {T : Submodule K (V ⧸ U) //
            Module.finrank K T = Module.finrank K (V ⧸ U) - j} := by
      rw [hfin, hsub]
    calc
      Nat.card {W : Submodule K V // U ≤ W ∧ Module.finrank K W = Module.finrank K V - j}
          = Nat.card {T : Submodule K (V ⧸ U) //
              Module.finrank K T = (Module.finrank K V - j) - Module.finrank K U} := hcount
      _ = Nat.card {T : Submodule K (V ⧸ U) //
              Module.finrank K T = Module.finrank K (V ⧸ U) - j} := h1
      _ ≤ Nat.card K ^ ((Module.finrank K (V ⧸ U) - j) * j + j) :=
            card_submodule_finrank_eq_sub_le_pow (K := K) (Q := V ⧸ U) j
      _ = Nat.card K ^ ((Module.finrank K V - Module.finrank K U - j) * j + j) := by
            rw [hfin]
  · haveI : IsEmpty {W : Submodule K V //
        U ≤ W ∧ Module.finrank K W = Module.finrank K V - j} :=
      ⟨fun W => by
        have h1 : Module.finrank K U ≤ Module.finrank K W := Submodule.finrank_mono W.2.1
        rw [W.2.2] at h1
        exact hA h1⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

end Commons.LinearAlgebra.Submodule
