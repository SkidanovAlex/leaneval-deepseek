import Mathlib
import Submission.Vdw.FinalAssemblyM
import Submission.Vdw.CaseIICountM

open Polynomial Filter Asymptotics
open scoped BigOperators
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# The challenge theorem from the two classical inputs

With the §4 Fourier input now unconditional (Weyl, `PerIrrWeyl`) and the
region analysis parameterised by `M` (`FinalAssemblyM`, `weylM n = 4n·2^n`),
the last reduction is the Case-II slice.  This module shows that the
slice `SubcaseIM_P2 n (weylM n) H` (`D_f ≤ H^(2+4/weylM n)`, i.e. essentially
`D_f = O(H²)`) is bounded by the *same* Abel-refined field-counting input
`CaseIICountBound n β` as the paper's Case II — and because the threshold
exponent `2 + 4/weylM n` is essentially `2`, the **crude** field counting
suffices in every degree:

* `n = 3`: `β = 1/2` (cyclic cubic field count),
* `n = 4, 5`: `β = 1` (exact quartic/quintic field counts),
* `n ≥ 6`: `β = (n+2)/4` (Schmidt's `#fields of discriminant ≤ Y ≪ Y^((n+2)/4)`),

provided the Lemke Oliver–Thorne per-field fibre bound holds.  The exponent
condition is `1 + (2 + 4/weylM n)·(β − 1/(n(n−1))) < n − 1`, which reduces to
`1 + 2(β − 1/(n(n−1))) < n − 1` and is satisfied by all the values above.

So `theorem_1_of_field_inputs` reduces the challenge statement to

* `PerFieldFibreBound n` (Lemke Oliver–Thorne),
* `FieldCountBound n β` (Schmidt / exact small-degree counts),
* the imprimitive bound `#ImprimitiveBad n H = O(H^(n-1))`
  (vacuous for prime `n`; Widmer's `O(H^(n/2+2))` for `n ≥ 6`; an `O(H^3)`
  input for `n = 4`),

all statements about number fields, with no Fourier analysis left.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-! ## Arithmetic: the Weyl parameter and the Schmidt exponent -/

/-- `n² + n ≤ 2^n` for `n ≥ 6`. -/
lemma sq_add_le_two_pow (n : ℕ) (hn : 6 ≤ n) : n * n + n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      have hmul : (m + 1) * (m + 1) + (m + 1) ≤ 2 * (m * m + m) := by nlinarith
      calc (m + 1) * (m + 1) + (m + 1) ≤ 2 * (m * m + m) := hmul
        _ ≤ 2 * 2 ^ m := by linarith
        _ = 2 ^ (m + 1) := by rw [pow_succ]; ring

/-- The exponent condition for `n = 6` (checked numerically: `weylM 6 = 1536`). -/
lemma weylM_exponent_schmidt_six :
    1 + (2 + 4 / (weylM 6 : ℝ)) * (((6 : ℝ) + 2) / 4 - 1 / ((6 : ℝ) * ((6 : ℝ) - 1)))
      < (6 : ℝ) - 1 := by
  norm_num [weylM]

/-- **The exponent condition for the Schmidt exponent** `β = (n+2)/4` and the
Weyl parameter `M = weylM n`: `1 + (2 + 4/M)(β − 1/(n(n−1))) < n − 1` for
`n ≥ 6`. -/
lemma weylM_exponent_schmidt (n : ℕ) (hn : 6 ≤ n) :
    1 + (2 + 4 / (weylM n : ℝ)) * (((n : ℝ) + 2) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
      < (n : ℝ) - 1 := by
  rcases eq_or_lt_of_le hn with h6 | h7
  · subst h6
    exact weylM_exponent_schmidt_six
  · have hnR : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h7
    have hn1 : (1 : ℝ) < (n : ℝ) := by linarith
    have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by positivity
    have hW : (weylM n : ℝ) = 4 * (n : ℝ) * (2 : ℝ) ^ n := by
      simp only [weylM]; push_cast; ring
    have h2n : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hnat := sq_add_le_two_pow n hn
    have hnatR : (n : ℝ) * (n : ℝ) + (n : ℝ) ≤ (2 : ℝ) ^ n := by
      push_cast; exact_mod_cast hnat
    -- `(n+2)/(4n·2^n) < 2/(n(n-1))`
    have hkey : (((n : ℝ) + 2) / (4 * (n : ℝ) * (2 : ℝ) ^ n))
        < 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
      rw [div_lt_div_iff₀ (by positivity) hden]
      nlinarith
    -- the `εγ` term is bounded by `(n+2)/(4n·2^n)`
    have hA : (4 / (weylM n : ℝ)) * (((n : ℝ) + 2) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
        ≤ ((n : ℝ) + 2) / (4 * (n : ℝ) * (2 : ℝ) ^ n) := by
      rw [hW]
      have h1 : 4 / (4 * (n : ℝ) * (2 : ℝ) ^ n)
            * (((n : ℝ) + 2) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
          ≤ 4 / (4 * (n : ℝ) * (2 : ℝ) ^ n) * (((n : ℝ) + 2) / 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hα : 0 ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by positivity
        linarith
      refine le_trans h1 (le_of_eq ?_)
      field_simp
    have hB : 2 * (((n : ℝ) + 2) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
        = ((n : ℝ) + 2) / 2 - 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by ring
    have hexpand : (2 + 4 / (weylM n : ℝ))
          * (((n : ℝ) + 2) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
        = 2 * (((n : ℝ) + 2) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
          + (4 / (weylM n : ℝ)) * (((n : ℝ) + 2) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1))) := by
      ring
    rw [hexpand, hB]
    linarith

/-! ## The `SubcaseIM_P2` variant of `theorem_1_of_M` -/

/-- **The challenge statement given the parametrised Case-II slice bound**:
the subcase-(i) Case-II slice at the parameter threshold, plus the
imprimitive bound. -/
theorem theorem_1_of_M_P2M (n M c : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M) (hnM : n ≤ M)
    (hM4 : 4 * n ≤ M)
    (hMn : (2 : ℝ) + 4 / (M : ℝ) < 2 * (n : ℝ) - 1)
    (hMn2 : (2 : ℝ) + 2 / (M : ℝ) < 2 * (n : ℝ) - 1)
    (hc : 1 ≤ c) (hper : PerIrrBoundTheta n ((2 : ℝ) / (M : ℝ)) c)
    (h2 : (fun H : ℕ => ((SubcaseIM_P2 n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  E_isBigO_of_irrBad n hn (irreducibleBad_isBigO_of_M n M hn hM hnM
    (SubcaseIM_isBigO_of_P2M n M c hn hM hnM hM4 hMn hMn2 hc hper h2) h4)

/-! ## The final reduction -/

/-- **The challenge statement from the classical number-field-counting
inputs.**  For `3 ≤ n`, given

* `PerFieldFibreBound n` — Lemke Oliver–Thorne's per-field fibre bound,
* `FieldCountBound n β` — the count of degree-`n` fields of discriminant
  `≤ Y` (Schmidt / exact small-degree counts),
* the exponent condition `1 + (2 + 4/weylM n)(β − 1/(n(n−1))) < n − 1`,
* the imprimitive bound,

the van der Waerden bound follows.  The §4 Fourier input and the whole region
analysis are unconditional. -/
theorem theorem_1_of_field_inputs (n : ℕ) (hn : 3 ≤ n) (β : ℝ)
    (hβ : 1 / ((n : ℝ) * ((n : ℝ) - 1)) < β)
    (hexp : 1 + (2 + 4 / (weylM n : ℝ)) * (β - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
      < (n : ℝ) - 1)
    (hLOT : PerFieldFibreBound n (by omega : 1 ≤ n))
    (hSC : FieldCountBound n (by omega : 1 ≤ n) β)
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨c, hc, hper⟩ := perIrrBoundTheta_weyl n hn
  have hper' : PerIrrBoundTheta n ((2 : ℝ) / (weylM n : ℝ)) c := by
    rw [two_div_weylM n hn]; exact hper
  have h2 : (fun H : ℕ => ((SubcaseIM_P2 n (weylM n) H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
    SubcaseIM_P2_isBigO_of_countBound n (weylM n) β hn (four_mul_le_weylM n) hβ hexp
      (caseIICountBound_of_field_inputs n (by omega) β hβ hLOT hSC)
  exact theorem_1_of_M_P2M n (weylM n) c hn (one_le_weylM n hn) (le_weylM n)
    (four_mul_le_weylM n) (weylM_exponentM n hn) (weylM_exponentM2 n hn) hc hper' h2 h4

/-! ## Degree-wise endpoints -/

lemma weylM_exponent_three :
    1 + (2 + 4 / (weylM 3 : ℝ)) * ((1 / 2 : ℝ) - 1 / ((3 : ℝ) * ((3 : ℝ) - 1)))
      < (3 : ℝ) - 1 := by
  norm_num [weylM]

lemma weylM_exponent_four :
    1 + (2 + 4 / (weylM 4 : ℝ)) * ((1 : ℝ) - 1 / ((4 : ℝ) * ((4 : ℝ) - 1)))
      < (4 : ℝ) - 1 := by
  norm_num [weylM]

lemma weylM_exponent_five :
    1 + (2 + 4 / (weylM 5 : ℝ)) * ((1 : ℝ) - 1 / ((5 : ℝ) * ((5 : ℝ) - 1)))
      < (5 : ℝ) - 1 := by
  norm_num [weylM]

/-- **Degree 3**: the challenge theorem from Lemke Oliver–Thorne's per-field
fibre bound and the counting of cyclic cubic fields of bounded discriminant
(`β = 1/2`).  (Degree 3 is prime, so the imprimitive input is vacuous.) -/
theorem theorem_1_of_literature_three
    (hLOT : PerFieldFibreBound 3 (by omega : 1 ≤ 3))
    (hSC : FieldCountBound 3 (by omega : 1 ≤ 3) (1 / 2)) :
    (fun H : ℕ => (E 3 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (3 - 1) : ℝ)) :=
  theorem_1_of_field_inputs 3 (by omega) (1 / 2) (by norm_num) weylM_exponent_three hLOT hSC
    (ImprimitiveBad_isBigO_of_prime 3 (by norm_num))

/-- **Degree 4**: the challenge theorem from the per-field fibre bound, the
exact quartic field count (`β = 1`) and an `O(H^3)` bound for the imprimitive
quartics.  (`H^(n/2+2) = H^4` is *not* enough here, so Widmer's bound does not
suffice in degree 4.) -/
theorem theorem_1_of_literature_four
    (hLOT : PerFieldFibreBound 4 (by omega : 1 ≤ 4))
    (hSC : FieldCountBound 4 (by omega : 1 ≤ 4) 1)
    (h4 : (fun H : ℕ => ((ImprimitiveBad 4 H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (4 - 1) : ℝ))) :
    (fun H : ℕ => (E 4 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (4 - 1) : ℝ)) :=
  theorem_1_of_field_inputs 4 (by omega) 1 (by norm_num) weylM_exponent_four hLOT hSC h4

/-- **Degree 5**: the challenge theorem from the per-field fibre bound and the
exact quintic field count (`β = 1`; `5` is prime, so no imprimitive input). -/
theorem theorem_1_of_literature_five
    (hLOT : PerFieldFibreBound 5 (by omega : 1 ≤ 5))
    (hSC : FieldCountBound 5 (by omega : 1 ≤ 5) 1) :
    (fun H : ℕ => (E 5 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (5 - 1) : ℝ)) :=
  theorem_1_of_field_inputs 5 (by omega) 1 (by norm_num) weylM_exponent_five hLOT hSC
    (ImprimitiveBad_isBigO_of_prime 5 (by norm_num))

/-- **Degrees `n ≥ 6`**: the challenge theorem from the per-field fibre bound,
Schmidt's field count (`β = (n+2)/4`) and Widmer's imprimitive bound. -/
theorem theorem_1_of_literature_six (n : ℕ) (hn : 6 ≤ n)
    (hLOT : PerFieldFibreBound n (by omega : 1 ≤ n))
    (hSC : FieldCountBound n (by omega : 1 ≤ n) (((n : ℝ) + 2) / 4))
    (hw : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ ((n : ℝ) / 2 + 2))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hβ : 1 / ((n : ℝ) * ((n : ℝ) - 1)) < ((n : ℝ) + 2) / 4 := by
    have hnR : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    rw [div_lt_iff₀ hden]
    nlinarith
  exact theorem_1_of_field_inputs n (by omega) (((n : ℝ) + 2) / 4) hβ
    (weylM_exponent_schmidt n hn) hLOT hSC (ImprimitiveBad_isBigO_of_widmer n hn hw)

/-- **Prime degrees `n ≥ 7`**: no imprimitive input is needed (a prime-degree
transitive group is primitive). -/
theorem theorem_1_of_literature_prime_degree (n : ℕ) (hn : 7 ≤ n) (hp : Nat.Prime n)
    (hLOT : PerFieldFibreBound n (by omega : 1 ≤ n))
    (hSC : FieldCountBound n (by omega : 1 ≤ n) (((n : ℝ) + 2) / 4)) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hβ : 1 / ((n : ℝ) * ((n : ℝ) - 1)) < ((n : ℝ) + 2) / 4 := by
    have hnR : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    rw [div_lt_iff₀ hden]
    nlinarith
  exact theorem_1_of_field_inputs n (by omega) (((n : ℝ) + 2) / 4) hβ
    (weylM_exponent_schmidt n (by omega)) hLOT hSC
    (ImprimitiveBad_isBigO_of_prime n hp)

end

end Submission.Vdw
