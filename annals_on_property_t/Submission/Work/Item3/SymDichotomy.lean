import Submission.Work.Item3.SymEnergy
import Submission.Work.Item3.EnergyDigits
import Submission.Commons.Data.List.ofDigits_lt_pow_base
import Submission.Commons.Data.Nat.pow_dichotomy

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
open scoped BigOperators
set_option autoImplicit false

/-!
# SymDichotomy: the pure arithmetic core of the symmetric-energy balanced step

With `C = ebase n` and `k = |A| = |B|`, the words of the two halves and of their
inverse-reversals all have length `k`, so their positional energies are all
`< C^k`.  The machine-exhaustive analysis (`/tmp/fg5/pure3.py`, `9 750 000`
three-block configurations over `3` generators) shows that the symmetric-energy
dichotomy

    E B + C^{|X|} E (invRev B) < C^{|X|} E A + E (invRev A)
      ∨  C^{|Z|} E A + E (invRev A) < C^{|Z|} E (invRev B) + E B

holds **exactly** away from the degenerate case
`E A = E (invRev B) ∧ E B = E (invRev A)`.  This module proves the two
ingredients that make it a pure ℕ statement:

* `lweight_lt_ebase`, `wordEnergy_lt_pow_ebase` — the bounds
  `E W < C^{|W|}`;
* `sym_energy_dichotomy` — the dichotomy, from the general commons lemma
  `Commons.Data.Nat.pow_dichotomy`.

The degenerate case is `rankseq B = rev (rankseq A)` (digit injectivity) and is
excluded by the primitivity of basis images (see `Submission/Status.lean`).

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- Every letter rank is below the base. -/
lemma lweight_lt_ebase {n : ℕ} (l : Fin n × Bool) : lweight l < ebase n := by
  unfold lweight ebase
  have := l.1.isLt
  omega

/-- A word of length `|W|` has positional energy below `C^{|W|}`. -/
lemma wordEnergy_lt_pow_ebase {n : ℕ} (W : List (Fin n × Bool)) :
    wordEnergy (ebase n) (lweight) W < (ebase n) ^ W.length := by
  rw [wordEnergy_eq_ofDigits]
  have h := Commons.Data.List.ofDigits_lt_pow_base (B := ebase n) (by unfold ebase; omega)
    (d := W.reverse.map lweight) (by
      intro x hx
      rcases List.mem_map.mp hx with ⟨l, _, rfl⟩
      exact lweight_lt_ebase l)
  rwa [List.length_map, List.length_reverse] at h

/-- **The symmetric-energy dichotomy (pure arithmetic).**  For reduced halves
`A`, `B` of equal length `k`, excesses `X`, `Z` with `k ≤ |X|`, `k ≤ |Z|`, and
away from the degenerate case
`E A = E (invRev B) ∧ E B = E (invRev A)`, the two cut-slide energy
comparisons cannot both fail. -/
theorem sym_energy_dichotomy {n : ℕ} (A B X Z : List (Fin n × Bool))
    (hAB : A.length = B.length) (hX : A.length ≤ X.length) (hZ : A.length ≤ Z.length)
    (hnd : ¬ (wordEnergy (ebase n) (lweight) A =
                wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) ∧
              wordEnergy (ebase n) (lweight) B =
                wordEnergy (ebase n) (lweight) (FreeGroup.invRev A))) :
    wordEnergy (ebase n) (lweight) B
        + (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
      < (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) A
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) ∨
    (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) A
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A)
      < (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
        + wordEnergy (ebase n) (lweight) B := by
  have hA : wordEnergy (ebase n) (lweight) A < (ebase n) ^ A.length :=
    wordEnergy_lt_pow_ebase A
  have hA' : wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) < (ebase n) ^ A.length := by
    have h := wordEnergy_lt_pow_ebase (FreeGroup.invRev A)
    rwa [FreeGroup.invRev_length] at h
  have hB : wordEnergy (ebase n) (lweight) B < (ebase n) ^ A.length := by
    have h := wordEnergy_lt_pow_ebase B
    rw [hAB]
    exact h
  have hB' : wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) < (ebase n) ^ A.length := by
    have h := wordEnergy_lt_pow_ebase (FreeGroup.invRev B)
    rw [FreeGroup.invRev_length] at h
    rw [hAB]
    exact h
  exact Commons.Data.Nat.pow_dichotomy (C := ebase n) (k := A.length)
    (p := X.length) (q := Z.length) (a := wordEnergy (ebase n) (lweight) A)
    (a' := wordEnergy (ebase n) (lweight) (FreeGroup.invRev A))
    (b := wordEnergy (ebase n) (lweight) B)
    (b' := wordEnergy (ebase n) (lweight) (FreeGroup.invRev B))
    (by unfold ebase; omega) hX hZ hA hA' hB hB' hnd

end Submission.Nielsen
