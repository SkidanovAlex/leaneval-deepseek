import Submission.Work.Item3.EnergyStepGeneral
import Submission.Work.SignedClosure

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
open scoped BigOperators
set_option autoImplicit false

/-!
# EnergyInvert: the single-coordinate inversion as an energy fallback

In a residual state at a balanced factor with halves `A`, `B` (`|A| = |B|`),
the two classical cut-slides of `EnergyStepGeneral`/`EnergyStepGeneralMinus`
carry *energy comparisons* which need not both be satisfiable: with `E` the
positional energy on words, the left cut-slides need `E B < E (invRev A)`
resp. `E (invRev B) < E A` and the right ones the complementary inequalities,
and for `k ≥ 2` there are configurations where *all four* fail (e.g. rank
sequences `(2,1)`, `(3,1)`).

In that situation the classical fallback is to **invert the balanced
coordinate** `w_p ↦ w_p⁻¹` (the Nielsen inversion `sigma p`, in `AutClosure n`
by `sigma_mem_AutGen`).  The energy effect of the inversion is

    eEnergy (α·sigma p) − eEnergy α = C^k·(E (invRev B) − E A) + (E (invRev A) − E B),

with `C = ebase n`, `k = |A| = |B|` — so it is `≤ 0` exactly when both
`E (invRev A) ≤ E B` and `E (invRev B) ≤ E A`, i.e. precisely when both
classical comparisons fail.  `N` is *always* preserved by an inversion
(`norm_inv_eq`), so the inversion is a legal fallback (`N`-preserving) energy
step.  Hence the four cut-slides together with the inversion give a complete
"balanced side" analysis in the positive orientation.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-! ## The effect of `sigma p` -/

/-- The coordinate word of `α * sigma p` at `p` is the inverse-reversal of the
one of `α`. -/
lemma coordWord_mul_sigma_self {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (p : Fin n) :
    coordWord (α * sigma p) p = FreeGroup.invRev (coordWord α p) := by
  show ((α * sigma p) (FreeGroup.of p)).toWord = _
  have h : (α * sigma p) (FreeGroup.of p) = (α (FreeGroup.of p))⁻¹ := by
    show α ((sigma p) (FreeGroup.of p)) = _
    rw [sigma_apply_self]
    exact map_inv (α : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of p)
  rw [h, FreeGroup.toWord_inv]
  rfl

/-- The coordinate word of `α * sigma p` at `k ≠ p` is unchanged. -/
lemma coordWord_mul_sigma_other {n : ℕ} (α : MulAut (FreeGroup (Fin n))) {p k : Fin n}
    (hk : k ≠ p) :
    coordWord (α * sigma p) k = coordWord α k := by
  show ((α * sigma p) (FreeGroup.of k)).toWord = _
  have h : (α * sigma p) (FreeGroup.of k) = α (FreeGroup.of k) := by
    show α ((sigma p) (FreeGroup.of k)) = α (FreeGroup.of k)
    rw [show (sigma p) (FreeGroup.of k) = FreeGroup.of k from by
      rw [sigma_apply_of, if_neg]; exact hk]
  rw [h]
  rfl

/-- `N` is unchanged by a single-coordinate inversion. -/
lemma N_mul_sigma {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (p : Fin n) :
    N (α * sigma p) = N α := by
  classical
  let g : Fin n → ℕ := fun k => FreeGroup.norm ((α * sigma p) (FreeGroup.of k))
  let h : Fin n → ℕ := fun k => FreeGroup.norm (α (FreeGroup.of k))
  have hmain : ∀ k : Fin n, k ≠ p → g k = h k := by
    intro k hk
    exact congrArg FreeGroup.norm (by
      show α ((sigma p) (FreeGroup.of k)) = α (FreeGroup.of k)
      rw [show (sigma p) (FreeGroup.of k) = FreeGroup.of k from by
        rw [sigma_apply_of, if_neg]; exact hk])
  have hgp : g p = h p := by
    have h1 : (α * sigma p) (FreeGroup.of p) = (α (FreeGroup.of p))⁻¹ := by
      show α ((sigma p) (FreeGroup.of p)) = _
      rw [sigma_apply_self]
      exact map_inv (α : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of p)
    show FreeGroup.norm ((α * sigma p) (FreeGroup.of p)) = FreeGroup.norm (α (FreeGroup.of p))
    rw [h1, norm_inv_eq]
  rw [N_eq_sum, N_eq_sum]
  have hsplit : ∀ (w : Fin n → ℕ),
      (∑ k : Fin n, w k) = (∑ k ∈ (Finset.univ.erase p : Finset (Fin n)), w k) + w p := by
    intro w
    exact (Finset.sum_erase_add (Finset.univ : Finset (Fin n)) w (Finset.mem_univ p)).symm
  rw [hsplit g, hsplit h, hgp]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact hmain k (Finset.mem_erase.mp hk).1

/-- Energy update for the single-coordinate inversion: only the `p`-th word
changes, to `W`. -/
lemma eEnergy_mul_sigma {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (p : Fin n)
    (W : List (Fin n × Bool)) (hW : coordWord (α * sigma p) p = W) :
    eEnergy (α * sigma p) + wordEnergy (ebase n) (lweight) (coordWord α p) =
      eEnergy α + wordEnergy (ebase n) (lweight) W := by
  rw [eEnergy_eq_sum_erase (α * sigma p) p, eEnergy_eq_sum_erase α p, hW]
  have hrest : (∑ k ∈ (Finset.univ.erase p : Finset (Fin n)),
      wordEnergy (ebase n) (lweight) (coordWord (α * sigma p) k)) =
      (∑ k ∈ (Finset.univ.erase p : Finset (Fin n)),
        wordEnergy (ebase n) (lweight) (coordWord α k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkp : k ≠ p := (Finset.mem_erase.mp hk).1
    rw [coordWord_mul_sigma_other α hkp]
  rw [hrest]
  ring

/-! ## The energy comparison -/

/-- Splitting the energy of the inverted word: `invRev (A ++ B)` unfolds to
`invRev B ++ invRev A`. -/
lemma wordEnergy_invRev_append' {n : ℕ} (A B : List (Fin n × Bool)) :
    wordEnergy (ebase n) (lweight) (FreeGroup.invRev (A ++ B)) =
      (ebase n) ^ A.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) := by
  rw [FreeGroup.invRev_append, wordEnergy_append, FreeGroup.invRev_length]

/-- Splitting the energy of `A ++ B`. -/
lemma wordEnergy_append' {n : ℕ} (A B : List (Fin n × Bool)) :
    wordEnergy (ebase n) (lweight) (A ++ B) =
      (ebase n) ^ B.length * wordEnergy (ebase n) (lweight) A
        + wordEnergy (ebase n) (lweight) B :=
  wordEnergy_append (ebase n) (lweight) A B

/-- **Inversion is energy-non-increasing at a balanced coordinate.**  If
`coordWord α p = A ++ B` with `|A| = |B|` and both classical comparisons fail
(`E (invRev A) ≤ E B`, `E (invRev B) ≤ E A`), then inverting the `p`-th
coordinate does not increase the positional energy. -/
theorem wordEnergy_invRev_le_of_halves {n : ℕ} {A B : List (Fin n × Bool)}
    (hAB : A.length = B.length)
    (h1 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) ≤
      wordEnergy (ebase n) (lweight) B)
    (h2 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) ≤
      wordEnergy (ebase n) (lweight) A) :
    wordEnergy (ebase n) (lweight) (FreeGroup.invRev (A ++ B)) ≤
      wordEnergy (ebase n) (lweight) (A ++ B) := by
  rw [wordEnergy_invRev_append', wordEnergy_append', ← hAB]
  have hmul : (ebase n) ^ A.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
      ≤ (ebase n) ^ A.length * wordEnergy (ebase n) (lweight) A :=
    Nat.mul_le_mul_left _ h2
  omega

/-- **Strict form** of `wordEnergy_invRev_le_of_halves`: strict as soon as one
of the two comparisons is strict. -/
theorem wordEnergy_invRev_lt_of_halves {n : ℕ} {A B : List (Fin n × Bool)}
    (hAB : A.length = B.length)
    (h1 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) ≤
      wordEnergy (ebase n) (lweight) B)
    (h2 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) ≤
      wordEnergy (ebase n) (lweight) A)
    (hstrict : wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) <
        wordEnergy (ebase n) (lweight) B ∨
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) <
        wordEnergy (ebase n) (lweight) A) :
    wordEnergy (ebase n) (lweight) (FreeGroup.invRev (A ++ B)) <
      wordEnergy (ebase n) (lweight) (A ++ B) := by
  rw [wordEnergy_invRev_append', wordEnergy_append', ← hAB]
  rcases hstrict with hs | hs
  · have hmul : (ebase n) ^ A.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
        ≤ (ebase n) ^ A.length * wordEnergy (ebase n) (lweight) A :=
      Nat.mul_le_mul_left _ h2
    omega
  · have hmul : (ebase n) ^ A.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
        < (ebase n) ^ A.length * wordEnergy (ebase n) (lweight) A :=
      Nat.mul_lt_mul_of_pos_left hs (pow_ebase_pos (n := n) A.length)
    omega

/-! ## State-level fallback -/

/-- **The inversion fallback (weak form).**  In *any* state, if the `p`-th
coordinate word is `A ++ B` with `|A| = |B|` and both classical comparisons
fail, then `sigma p ∈ AutClosure n` preserves `N` and does not increase the
energy. -/
theorem energy_invert_pos {n : ℕ} (α : MulAut (FreeGroup (Fin n))) {p : Fin n}
    {A B : List (Fin n × Bool)} (hAB : A.length = B.length)
    (hp : coordWord α p = A ++ B)
    (h1 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) ≤
      wordEnergy (ebase n) (lweight) B)
    (h2 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) ≤
      wordEnergy (ebase n) (lweight) A) :
    sigma p ∈ AutClosure n ∧ N (α * sigma p) = N α ∧ eEnergy (α * sigma p) ≤ eEnergy α := by
  refine ⟨Subgroup.subset_closure (sigma_mem_AutGen n p), N_mul_sigma α p, ?_⟩
  have hEu := eEnergy_mul_sigma α p (FreeGroup.invRev (coordWord α p))
    (coordWord_mul_sigma_self α p)
  rw [hp] at hEu
  have hcmp := wordEnergy_invRev_le_of_halves hAB h1 h2
  omega

/-- **The inversion fallback (strict form).**  As `energy_invert_pos`, but with
the conclusion strict whenever at least one of the two comparisons is strict. -/
theorem energy_invert_pos_strict {n : ℕ} (α : MulAut (FreeGroup (Fin n))) {p : Fin n}
    {A B : List (Fin n × Bool)} (hAB : A.length = B.length)
    (hp : coordWord α p = A ++ B)
    (h1 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) ≤
      wordEnergy (ebase n) (lweight) B)
    (h2 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) ≤
      wordEnergy (ebase n) (lweight) A)
    (hstrict : wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) <
        wordEnergy (ebase n) (lweight) B ∨
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) <
        wordEnergy (ebase n) (lweight) A) :
    sigma p ∈ AutClosure n ∧ N (α * sigma p) = N α ∧ eEnergy (α * sigma p) < eEnergy α := by
  refine ⟨Subgroup.subset_closure (sigma_mem_AutGen n p), N_mul_sigma α p, ?_⟩
  have hEu := eEnergy_mul_sigma α p (FreeGroup.invRev (coordWord α p))
    (coordWord_mul_sigma_self α p)
  rw [hp] at hEu
  have hcmp := wordEnergy_invRev_lt_of_halves hAB h1 h2 hstrict
  omega

/-- **The inversion fallback in the negative orientation (strict form).**  If
`coordWord α p = invRev B ++ invRev A` (the inverse of the factor word
`A ++ B`) with `|A| = |B|` and both classical comparisons fail
(`E B ≤ E (invRev A)`, `E A ≤ E (invRev B)`), with at least one strict, then
inverting the `p`-th coordinate preserves `N` and strictly decreases the
energy. -/
theorem energy_invert_neg_strict {n : ℕ} (α : MulAut (FreeGroup (Fin n))) {p : Fin n}
    {A B : List (Fin n × Bool)} (hAB : A.length = B.length)
    (hp : coordWord α p = FreeGroup.invRev B ++ FreeGroup.invRev A)
    (h1 : wordEnergy (ebase n) (lweight) B ≤
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev A))
    (h2 : wordEnergy (ebase n) (lweight) A ≤
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev B))
    (hstrict : wordEnergy (ebase n) (lweight) B <
        wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) ∨
      wordEnergy (ebase n) (lweight) A <
        wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)) :
    sigma p ∈ AutClosure n ∧ N (α * sigma p) = N α ∧ eEnergy (α * sigma p) < eEnergy α := by
  refine ⟨Subgroup.subset_closure (sigma_mem_AutGen n p), N_mul_sigma α p, ?_⟩
  have hEu := eEnergy_mul_sigma α p (FreeGroup.invRev (coordWord α p))
    (coordWord_mul_sigma_self α p)
  rw [hp] at hEu
  have h2' : (FreeGroup.invRev (FreeGroup.invRev B ++ FreeGroup.invRev A)) = A ++ B := by
    rw [FreeGroup.invRev_append, FreeGroup.invRev_invRev, FreeGroup.invRev_invRev]
  rw [h2'] at hEu
  have hthis : wordEnergy (ebase n) (lweight) (FreeGroup.invRev B ++ FreeGroup.invRev A) =
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev (A ++ B)) := by
    rw [FreeGroup.invRev_append]
  rw [hthis] at hEu
  have hcmp : wordEnergy (ebase n) (lweight) (A ++ B) <
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev (A ++ B)) := by
    rw [wordEnergy_invRev_append', wordEnergy_append', ← hAB]
    have hm : (ebase n) ^ A.length * wordEnergy (ebase n) (lweight) A
        ≤ (ebase n) ^ A.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) :=
      Nat.mul_le_mul_left _ h2
    rcases hstrict with hs | hs
    · omega
    · have hm2 : (ebase n) ^ A.length * wordEnergy (ebase n) (lweight) A
          < (ebase n) ^ A.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) :=
        Nat.mul_lt_mul_of_pos_left hs (pow_ebase_pos (n := n) A.length)
      omega
  omega

end Submission.Nielsen
