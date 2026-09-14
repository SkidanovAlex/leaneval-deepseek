import Mathlib
import Submission.Vdw.ResidueIndex
import Submission.Vdw.ResidueFiber
import Submission.Vdw.DiscZeroCount

/-!
# Box polynomials whose reduction mod `p` has vanishing discriminant

Bridges the finite-field count `monic_disc_zero_ncard_eq` /
`monic_disc_zero_ncard_le` of `DiscZeroCount.lean` to the box language of
the corpus (`Box n H`, `boxResidue`, `reductionPoly`):

**`box_disc_zero_ncard_le`** — for a prime `p`, at most
`p^(n-1) · ((2H+1)/p + 1)^n` box polynomials `f ∈ Box n H` (monic,
degree `n`, coefficients `|a_i| ≤ H`) have `Disc(f mod p) = 0` in `𝔽_p`:

`Nat.card {f : ↥(Box n H) // Polynomial.discr (reductionPoly p n H f) = 0}
   ≤ p^(n-1) · ((2H+1)/p + 1)^n`

Chain: `reductionPoly f = monicOfTrail n (boxResidue f)`
(`reductionPoly_eq_monicOfTrail`), so the condition depends only on the
residue vector `boxResidue f ∈ S`,
`S = {v | Disc(monicOfTrail n v) = 0}`; the residue-transfer lemma
`box_residue_set_le` bounds the count by `S.ncard · ((2H+1)/p+1)^n`, and
the vector count `S.ncard` is at most the monic degree-`n` Disc-zero count
`q^(n-1)` (`disc_zero_vec_ncard_le`), because `monicOfTrail` is injective and
maps `S` into the set counted by `monic_disc_zero_ncard_le`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Submission.Vdw

noncomputable section

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The set of coefficient vectors `v : Fin n → F` whose monic degree-`n`
polynomial `monicOfTrail n v` has vanishing discriminant. -/
def discZeroVecSet (n : ℕ) : Set (Fin n → F) :=
  {v : Fin n → F | Polynomial.discr (monicOfTrail n v) = 0}

/-- `monicOfTrail` is injective (recovered by `toFn`). -/
theorem monicOfTrail_injective (n : ℕ) :
    Function.Injective (fun v : Fin n → F => monicOfTrail n v) := by
  intro v w h
  simpa [toFn_monicOfTrail] using (congrArg (Polynomial.toFn n) h)

/-- At most `q^(n-1)` coefficient vectors (of monic degree-`n` polynomials
over a finite field with `q` elements) give vanishing discriminant,
for `2 ≤ n`. -/
theorem disc_zero_vec_ncard_le (n : ℕ) (hn : 2 ≤ n) :
    (discZeroVecSet (F := F) n).ncard ≤ Fintype.card F ^ (n - 1) := by
  classical
  let T : Set F[X] := {p : F[X] | p.Monic ∧ p.natDegree = n ∧ Polynomial.discr p = 0}
  have hallF : ({p : F[X] | p.Monic ∧ p.natDegree = n} : Set F[X]).Finite :=
    monicDeg_finite (F := F) n
  have hsubT : T ⊆ ({p : F[X] | p.Monic ∧ p.natDegree = n} : Set F[X]) := by
    intro p hp
    exact ⟨hp.1, hp.2.1⟩
  have hfinT : T.Finite := hallF.subset hsubT
  -- monicOfTrail maps the counted vectors into T
  have hIm_sub : monicOfTrail n '' discZeroVecSet (F := F) n ⊆ T := by
    intro q hq
    rcases hq with ⟨v, hv, rfl⟩
    exact ⟨monicOfTrail_monic n v, monicOfTrail_natDegree n v, by simpa [discZeroVecSet] using hv⟩
  have hIm_card : (monicOfTrail n '' discZeroVecSet (F := F) n).ncard =
      (discZeroVecSet (F := F) n).ncard := by
    exact Set.ncard_image_of_injective (discZeroVecSet (F := F) n) (monicOfTrail_injective n)
  calc
    (discZeroVecSet (F := F) n).ncard
        = (monicOfTrail n '' discZeroVecSet (F := F) n).ncard := hIm_card.symm
    _ ≤ T.ncard := Set.ncard_le_ncard hIm_sub hfinT
    _ ≤ Fintype.card F ^ (n - 1) := by
      simpa [T] using (monic_disc_zero_ncard_le (F := F) n hn)

/-- **Main (box transfer):** for a prime `p`, the number of box polynomials
whose reduction mod `p` has vanishing discriminant is at most
`p^(n-1) · ((2H+1)/p + 1)^n`. -/
theorem box_disc_zero_ncard_le (p : ℕ) [Fact (Nat.Prime p)] (n H : ℕ) (hn : 2 ≤ n) :
    Nat.card {f : ↥(Box n H) // Polynomial.discr (reductionPoly p n H f) = 0} ≤
      p ^ (n - 1) * ((2 * H + 1) / p + 1) ^ n := by
  classical
  have hp1 : 1 ≤ p := by
    exact (Nat.Prime.one_lt (Fact.out : Nat.Prime p)).le
  let S : Set (Fin n → ZMod p) := discZeroVecSet (F := ZMod p) n
  have e : {f : ↥(Box n H) // Polynomial.discr (reductionPoly p n H f) = 0} ≃
      {f : ↥(Box n H) // boxResidue n H p f ∈ S} := by
    refine {
      toFun := fun f => ⟨f.1, ?_⟩
      invFun := fun f => ⟨f.1, ?_⟩
      left_inv := by
        intro f
        apply Subtype.ext
        rfl
      right_inv := by
        intro f
        apply Subtype.ext
        rfl }
    · -- boxResidue f ∈ S, from discr (reductionPoly f) = 0
      have hrec : reductionPoly p n H f.1 = monicOfTrail n (boxResidue n H p f.1) :=
        reductionPoly_eq_monicOfTrail p n H f.1
      simpa [S, discZeroVecSet, hrec] using f.2
    · -- discr (reductionPoly f) = 0, from boxResidue f ∈ S
      have hrec : reductionPoly p n H f.1 = monicOfTrail n (boxResidue n H p f.1) :=
        reductionPoly_eq_monicOfTrail p n H f.1
      simpa [S, discZeroVecSet, hrec] using f.2
  have hcardS : S.ncard ≤ p ^ (n - 1) := by
    have h := disc_zero_vec_ncard_le (F := ZMod p) n hn
    simpa [S] using h
  have hle : Nat.card {f : ↥(Box n H) // boxResidue n H p f ∈ S} ≤
      S.ncard * ((2 * H + 1) / p + 1) ^ n := by
    exact box_residue_set_le n H p hp1 S
  calc
    Nat.card {f : ↥(Box n H) // Polynomial.discr (reductionPoly p n H f) = 0}
        = Nat.card {f : ↥(Box n H) // boxResidue n H p f ∈ S} := Nat.card_congr e
    _ ≤ S.ncard * ((2 * H + 1) / p + 1) ^ n := hle
    _ ≤ p ^ (n - 1) * ((2 * H + 1) / p + 1) ^ n := by
      exact Nat.mul_le_mul_right _ hcardS

end

end Submission.Vdw
