import Mathlib
import Submission.NK.LocalInputs.PowerQuotient.natCard_quot_maximalIdeal_pow
import Submission.Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.LocalInputs.PowerQuotient

theorem relIndex_maximalIdeal_pow {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (N k : ℕ) :
    ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) ^ (N + k)).toAddSubgroup).relIndex
        ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) ^ N).toAddSubgroup) =
      (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) ^ k := by
  haveI hfin : Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K 𝔭
  haveI hne : Nonempty (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) := ⟨0⟩
  -- The index of the `n`-th power of the maximal ideal is `|κ| ^ n`.
  have hcard : ∀ n : ℕ,
      AddSubgroup.index
          ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)) ^ n).toAddSubgroup =
        (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) ^ n := by
    intro n
    rw [show AddSubgroup.index
          ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)) ^ n).toAddSubgroup =
        Nat.card (↥(𝔭.adicCompletionIntegers K) ⧸
          (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)) ^ n) from rfl]
    exact natCard_quot_maximalIdeal_pow 𝔭 n
  -- Lagrange's theorem for the pair `𝔪 ^ (N + k) ≤ 𝔪 ^ N`.
  have hmul := AddSubgroup.relIndex_mul_index
    (H := ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)) ^ (N + k)).toAddSubgroup)
    (K := ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)) ^ N).toAddSubgroup)
    (Ideal.pow_le_pow_right (Nat.le_add_right N k))
  rw [hcard (N + k), hcard N] at hmul
  -- `hmul : relIndex * |κ| ^ N = |κ| ^ (N + k) = |κ| ^ k * |κ| ^ N`.
  have hkey :
      ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) ^ (N + k)).toAddSubgroup).relIndex
          ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) ^ N).toAddSubgroup) *
        (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) ^ N =
      (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) ^ k *
        (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) ^ N := by
    rw [hmul, pow_add, mul_comm]
  exact Nat.mul_right_cancel (m :=
    (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) ^ N)
    (pow_pos Nat.card_pos N) hkey

end NK.LocalInputs.PowerQuotient
