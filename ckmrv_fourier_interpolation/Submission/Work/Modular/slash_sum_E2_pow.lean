import Mathlib
import Submission.Work.Modular.Basic
import Submission.Work.Modular.slash_defect

/-!
# The slash action on a depth-`d` quasi-modular form

The quasimodular forms of weight `k` and depth at most `d` are, by definition
(`IsQuasiModularFormDepth`), the functions of the shape

  `f = ∑_{j = 0}^{d} E₂ ^ j * m_j`

with `m_j` a holomorphic modular form of weight `k - 2j` for `SL(2, ℤ)`.

The main result of this file, `slash_sum_E2_pow`, says that the slash action of
`SL(2, ℤ)` on such a function is obtained by replacing `E₂` by its slash
`E₂ ∣[2] γ` and leaving the modular coefficients alone:

  `(∑_j E₂ ^ j * m_j) ∣[k] γ = ∑_j (E₂ ∣[2] γ) ^ j * m_j`.

Equivalently, since `E₂ ∣[2] γ = E₂ + (E₂ ∣[2] γ - E₂)`, the slash defect of a
depth-`d` quasimodular form is divisible by the `E₂`-defect
`E₂ ∣[2] γ - E₂`; this is the general form of `Work.Modular.slash_defect` (the
depth-one case), and it is the structural input for the paper's Proposition 3.10
and Proposition 3.11, where the transformation laws of the components
`h₀, h₁, h₂` of an element of the space `(HFE⁺)` are converted into
quasimodularity statements of depth `1` and `2` for `SL(2, ℤ)`.

The proof has two ingredients, both elementary:

* `E₂ ^ n ∣[2n] γ = (E₂ ∣[2] γ) ^ n` for every `n ≥ 0` (induction on `n`, using
  multiplicativity of the slash action `ModularForm.mul_slash_SL2` with the
  weights `2n` and `2` adding up to `2(n+1)`);
* slash invariance of the coefficients, `⇑m_j ∣[k - 2j] γ = ⇑m_j`
  (`Work.Modular.modularForm_slash_eq_self`).

Only bookkeeping is needed on top: the weights `2j + (k - 2j)` and `2n + 2` are
equal to `k` and `2(n+1)` only *propositionally*, so each multiplication step is
transported along `congrArg` of the (weight-indexed) slash operator.
-/

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped Manifold MatrixGroups ModularForm

/-- The slash action on a power of `E₂`: `E₂ ^ n` has weight `2n`, and slashing it replaces it
by the `n`-th power of `E₂ ∣[2] γ`. -/
theorem E2_pow_slash (γ : SL(2, ℤ)) (n : ℕ) :
    (E2 ^ n) ∣[2 * (n : ℤ)] γ = (E2 ∣[(2 : ℤ)] γ) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    rw [show (2 : ℤ) * ((0 : ℕ) : ℤ) = 0 from by norm_num]
    exact ModularForm.is_invariant_one γ
  | succ n ih =>
    rw [pow_succ, pow_succ]
    have h := ModularForm.mul_slash_SL2 (2 * (n : ℤ)) 2 γ (E2 ^ n) E2
    rw [show 2 * (n : ℤ) + 2 = 2 * ((n + 1 : ℕ) : ℤ) from by push_cast; ring] at h
    rw [h, ih]

/-- The slash action on a quasimodular form of depth at most `d`, written on the representing
sum `∑_{j ≤ d} E₂^j m_j`: it simply replaces `E₂` by `E₂ ∣[2] γ` and leaves the modular
coefficients `m_j` alone. -/
theorem slash_sum_E2_pow {d : ℕ} {k : ℤ}
    (m : (j : Fin (d + 1)) → ModularForm 𝒮ℒ (k - 2 * (j : ℤ))) (γ : SL(2, ℤ)) :
    (∑ j : Fin (d + 1), E2 ^ (j : ℕ) * ⇑(m j)) ∣[k] γ
      = ∑ j : Fin (d + 1), (E2 ∣[(2 : ℤ)] γ) ^ (j : ℕ) * ⇑(m j) := by
  simp only [SlashAction.sum_slash]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- the two weights `2j` and `k - 2j` add up to `k`; the slash is multiplicative in them
  have h := ModularForm.mul_slash_SL2 (2 * (j : ℤ)) (k - 2 * (j : ℤ)) γ
    (E2 ^ (j : ℕ)) (⇑(m j))
  rw [show 2 * (j : ℤ) + (k - 2 * (j : ℤ)) = k from by ring] at h
  rw [h, E2_pow_slash γ (j : ℕ), modularForm_slash_eq_self (m j) γ]

end Work.Modular
