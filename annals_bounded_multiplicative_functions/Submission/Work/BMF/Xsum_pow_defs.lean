import Mathlib
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.tent_fourier_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The expansion of `‖Xsum‖^{2s}` : vocabulary

Ford's Lemma 5.1 (`Work.BMF.vkford_lemma51`) expands the `2s`-th power of the inner `b`-sum

  `Xsum k M₂ γ ε c = Σ_{b ∈ [1,M₂]} ε_b e(Σ_{j<k} γ_j b^{j+1} c_j)`

into a sum over pairs of `s`-tuples.  This file isolates the summand `Xterm` and the phase
`Xphase` of `Xsum`, records the elementary identities for the additive character `eZ` and for
the pair-difference `dvec` that the expansion uses, and proves the two expansions of `Xsum^s`
and `(star Xsum)^s` (which are `Fintype.sum_pow`).

The target of this development is `Work.BMF.Xsum_norm_pow`:

  `((‖Xsum k M₂ γ ε c‖ ^ (2 * s) : ℝ) : ℂ)
     = ∑ p : Pair s M₂, epsp ε p * eZ (∑ j, γ_j c_j (dvec (j+1) p))`.
-/

namespace Work.BMF

open Finset
open scoped BigOperators

noncomputable section

/-- The phase `Σ_j γ_j b^{j+1} c_j` appearing in the summand of `Xsum`. -/
def Xphase (k : ℕ) (γ : Fin k → ℝ) (c : Fin k → ℤ) (b : ℕ) : ℝ :=
  ∑ j : Fin k, γ j * (b : ℝ) ^ ((j : ℕ) + 1) * (c j : ℝ)

/-- The summand `ε_b e(Σ_j γ_j b^{j+1} c_j)` of `Xsum`. -/
def Xterm (k : ℕ) (γ : Fin k → ℝ) (ε : ℕ → ℂ) (c : Fin k → ℤ) (b : ℕ) : ℂ :=
  ε b * eZ (Xphase k γ c b)

/-- `Xsum` is the sum of its summands over `[1, M₂]` (definitional). -/
lemma Xsum_eq_sum_Xterm (k M₂ : ℕ) (γ : Fin k → ℝ) (ε : ℕ → ℂ) (c : Fin k → ℤ) :
    Xsum k M₂ γ ε c = ∑ b ∈ Icc 1 M₂, Xterm k γ ε c b := rfl

/-- `Xsum` as a sum over the subtype `[1, M₂]`. -/
lemma Xsum_eq_subtype (k M₂ : ℕ) (γ : Fin k → ℝ) (ε : ℕ → ℂ) (c : Fin k → ℤ) :
    Xsum k M₂ γ ε c = ∑ b : Icc 1 M₂, Xterm k γ ε c b.1 := by
  rw [Xsum_eq_sum_Xterm, ← Finset.sum_coe_sort]

/-- The `s`-th power of `Xsum` as a sum over `s`-tuples. -/
lemma Xterm_pow (k s M₂ : ℕ) (γ : Fin k → ℝ) (ε : ℕ → ℂ) (c : Fin k → ℤ) :
    (Xsum k M₂ γ ε c) ^ s
      = ∑ u : Fin s → Icc 1 M₂, ∏ i : Fin s, Xterm k γ ε c (u i).1 := by
  rw [Xsum_eq_subtype, Fintype.sum_pow]

/-- The `s`-th power of the conjugate of `Xsum` as a sum over `s`-tuples. -/
lemma star_Xsum_pow (k s M₂ : ℕ) (γ : Fin k → ℝ) (ε : ℕ → ℂ) (c : Fin k → ℤ) :
    (star (Xsum k M₂ γ ε c)) ^ s
      = ∑ u : Fin s → Icc 1 M₂, ∏ i : Fin s, star (Xterm k γ ε c (u i).1) := by
  rw [Xsum_eq_subtype, star_sum, Fintype.sum_pow]

/-- `eZ` and `star` : conjugating the character negates the argument. -/
lemma star_eZ (t : ℝ) : star (eZ t) = eZ (-t) := by
  unfold eZ
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- A product of additive characters is the character of the sum. -/
lemma prod_eZ {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    ∏ i, eZ (t i) = eZ (∑ i, t i) := by
  simp only [eZ]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

/-- `Xphase` with the factors reordered, in the shape used by the right-hand side of the
expansion. -/
lemma Xphase_eq (k : ℕ) (γ : Fin k → ℝ) (c : Fin k → ℤ) (b : ℕ) :
    Xphase k γ c b = ∑ j : Fin k, γ j * (c j : ℝ) * (b : ℝ) ^ ((j : ℕ) + 1) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The integer pair-difference `dvec` cast to `ℝ` is the difference of the two real power
sums. -/
lemma dvec_cast {s M₂ : ℕ} (j : ℕ) (p : Pair s M₂) :
    ((dvec j p : ℤ) : ℝ)
      = (∑ i : Fin s, (((p.1 i).1 : ℕ) : ℝ) ^ j)
        - (∑ i : Fin s, (((p.2 i).1 : ℕ) : ℝ) ^ j) := by
  rw [dvec]
  push_cast
  ring

end

end Work.BMF
