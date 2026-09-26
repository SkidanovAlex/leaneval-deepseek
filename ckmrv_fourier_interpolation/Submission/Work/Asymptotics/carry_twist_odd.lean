/-
# Polynomial bounds for the twisted odd carries

The main theorem `Work.Asymptotics.carry_twist_odd` is assembled in
`Submission.Work.Asymptotics.TwistOddFinal` from the following ingredients:

* `Work.Asymptotics.sigmaHom_entry_bound`: the entries of the explicit odd representation `σ`
  grow at most polynomially in the Frobenius norm (CKMRV Lemma `lem:polynomiallybounded`);
* `Work.Asymptotics.Tblock_spec`/`Tblock_bound` and `Work.Asymptotics.STblock_spec`/`STblock_bound`:
  the twisted carries of the blocks `T^k` (`k : ℤ`) and `S T^k`;
* `Work.Asymptotics.base_carry_spec`: the twisted carries of the base elements `1, -1, S, -S`;
* `Work.Asymptotics.block_letters_data`, `Work.Asymptotics.bAcc_spec` and
  `Work.Asymptotics.bAcc_bound` (`TwistOddLetters`): the cocycle along the word of blocks
  produced by `Work.Asymptotics.block_factorization`.

The twisted carry `(1-z)·rowDiffOdd γ 0` of an arbitrary `γ` is the sum of the accumulated
carry of the product of the blocks of `γ` and the carry of the single base element, and
everything is bounded by `C (1 + ‖γ‖)^N` because the number of blocks is `O(log ‖γ‖)`.
-/
import Mathlib
import Submission.Work.Asymptotics.TwistOddFinal

namespace Work.Asymptotics

theorem carry_twist_odd :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (∀ i : Fin 6, ∀ j : Fin 6,
        ‖Work.Asymptotics.sigmaHom γ i j‖ ≤ C * (1 + Work.Asymptotics.Frob γ) ^ N) ∧
      ∃ A B : Work.Kernels.R,
        (1 - Work.Residues.Rneg) *
            (Work.Asymptotics.ofSL γ
              - (∑ j : Fin 6, (Work.Asymptotics.sigmaHom γ) 0 j • Work.Asymptotics.MpElem j))
          = (Work.Kernels.R_T - 1) ^ 2 * A + Work.Kernels.R_S * (Work.Kernels.R_T - 1) ^ 2 * B
        ∧ Work.Asymptotics.coeffNorm A ≤ C * (1 + Work.Asymptotics.Frob γ) ^ N
        ∧ Work.Asymptotics.coeffNorm B ≤ C * (1 + Work.Asymptotics.Frob γ) ^ N
        ∧ Work.Asymptotics.supportFrobLe A (C * (1 + Work.Asymptotics.Frob γ) ^ N)
        ∧ Work.Asymptotics.supportFrobLe B (C * (1 + Work.Asymptotics.Frob γ) ^ N) :=
  Work.Asymptotics.carry_twist_odd_aux

end Work.Asymptotics
