import Mathlib
import Submission.Work.PieceHomology.CircCover
import Submission.Work.HomologyIso.Algebra
import Submission.Work.HomologyMV.Model

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The arithmetic of the ranks `rankCirc`, `rankPt`, `rankT2`, `rankT`, and free-module splittings

`rankCirc k = (1,1,0,…)` is the rank of `H_k(S¹)`, `rankPt k = (1,0,…)` the rank of `H_k(pt)`,
`rankT2 k = (1,2,1,0,…)` the rank of `H_k(T²)` and `rankT k = (1,3,3,1,0,…)` the rank of
`H_k(S¹ × T²)`.  All four sequences are of the form "one `1` plus a shift", and consequently they
satisfy the *same* arithmetic identity

`rank_{n}(X × S¹) = rank_n(X) + rank_{n-1}(X)`

for **all** integers `n`, with `X = pt`, `S¹`, `T²` respectively: this is the Künneth/tensor
identity `H_n(X × S¹) ≅ (H_n(X) ⊕ H_{n-1}(X))` on ranks, expressed as an identity of the
floor functions `rankCirc`, `rankPt`, `rankT2`, `rankT` on `ℤ`:

* `rankCirc n = rankPt n + rankPt (n-1)`,
* `rankT2 n = rankCirc n + rankCirc (n-1)`,
* `rankT n = rankT2 n + rankT2 (n-1)`.

Specializing at `n = k+1` (`k : ℕ`) turns each of these into the corresponding identity in the
requested statement, and additionally handles the degree `0` identities
`rankT2 0 = rankCirc 0`, `rankT 0 = rankT2 0` (both sides `1`).

The last two conjuncts are the algebraic backbone of the decomposition of the model groups: the
free `ℤ`-modules `ℤ^a` and `ℤ^b` split off a direct summand of `ℤ^{a+b}` (biproduct form), and
`ℤ^0` is the zero module, i.e. `ℤ^0 ≅ PUnit`-module.

## Main results

* `concatLin` — `ℤ^a × ℤ^b ≃ ℤ^{a+b}`, the concatenation of tuples;
* `rankCirc_eq_add`, `rankT2_eq_add`, `rankT_eq_add` — the shift identities above;
* `freeMod_rank_arith` — the requested statement.
-/

namespace Work.PieceHomology

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- `ℤ^{a+b} ≃ ℤ^a × ℤ^b`: cut a `Fin (a+b)`-tuple into its first `a` and last `b` coordinates,
equivalently concatenate a `Fin a`-tuple and a `Fin b`-tuple.  Obtained from the linear
equivalence `(Fin a ⊕ Fin b → ℤ) ≃ (Fin a → ℤ) × (Fin b → ℤ)` and the reindexing
`Fin a ⊕ Fin b ≃ Fin (a+b)`. -/
def concatLin (a b : ℕ) : ((Fin a → ℤ) × (Fin b → ℤ)) ≃ₗ[ℤ] (Fin (a + b) → ℤ) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℤ ℤ).symm.trans
    (LinearEquiv.funCongrLeft ℤ ℤ (finSumFinEquiv (m := a) (n := b))).symm

/-! ## §1  The shift identities for the ranks -/

/-- `rankCirc n = rankPt n + rankPt (n-1)`: `H_n(S¹) ≅ H_n(pt) ⊕ H_{n-1}(pt)`, i.e. the rank
sequence `S¹ → pt → pt` shifted by one. -/
theorem rankCirc_eq_add (n : ℤ) : rankCirc n = rankPt n + rankPt (n - 1) := by
  rcases eq_or_ne n 0 with h | h
  · subst h; norm_num [rankCirc, rankPt]
  rcases eq_or_ne n 1 with h1 | h1
  · subst h1; norm_num [rankCirc, rankPt]
  · rw [rankCirc_eq_zero n h h1, rankPt_eq_zero n h, rankPt_eq_zero (n - 1) (by omega)]

/-- `rankT2 n = rankCirc n + rankCirc (n-1)`: `H_n(T²) ≅ H_n(S¹) ⊕ H_{n-1}(S¹)`, the rank
sequence `(1,2,1)` displayed as `(1,1) + (0,1)` shifted. -/
theorem rankT2_eq_add (n : ℤ) :
    Work.HomologyIso.rankT2 n = rankCirc n + rankCirc (n - 1) := by
  rcases eq_or_ne n 0 with h | h
  · subst h; norm_num [Work.HomologyIso.rankT2, rankCirc]
  rcases eq_or_ne n 1 with h1 | h1
  · subst h1; norm_num [Work.HomologyIso.rankT2, rankCirc]
  rcases eq_or_ne n 2 with h2 | h2
  · subst h2; norm_num [Work.HomologyIso.rankT2, rankCirc]
  · rw [Work.HomologyIso.rankT2_eq_zero n h h1 h2, rankCirc_eq_zero n h h1,
      rankCirc_eq_zero (n - 1) (by omega) (by omega)]

/-- `rankT n = rankT2 n + rankT2 (n-1)`: `H_n(S¹ × T²) ≅ H_n(T²) ⊕ H_{n-1}(T²)`, the rank
sequence `(1,3,3,1)` displayed as `(1,2,1) + (0,1,2,1)` shifted. -/
theorem rankT_eq_add (n : ℤ) :
    Work.HomologyIso.rankT n = Work.HomologyIso.rankT2 n + Work.HomologyIso.rankT2 (n - 1) := by
  rcases eq_or_ne n 0 with h | h
  · subst h; norm_num [Work.HomologyIso.rankT, Work.HomologyIso.rankT2]
  rcases eq_or_ne n 1 with h1 | h1
  · subst h1; norm_num [Work.HomologyIso.rankT, Work.HomologyIso.rankT2]
  rcases eq_or_ne n 2 with h2 | h2
  · subst h2; norm_num [Work.HomologyIso.rankT, Work.HomologyIso.rankT2]
  rcases eq_or_ne n 3 with h3 | h3
  · subst h3; norm_num [Work.HomologyIso.rankT, Work.HomologyIso.rankT2]
  · rw [Work.HomologyIso.rankT_eq_zero n h h1 h2 h3, Work.HomologyIso.rankT2_eq_zero n h h1 h2,
      Work.HomologyIso.rankT2_eq_zero (n - 1) (by omega) (by omega) (by omega)]

theorem freeMod_rank_arith :
    (∀ k : ℕ, Work.PieceHomology.rankCirc ((k : ℤ) + 1)
        = Work.PieceHomology.rankPt ((k : ℤ) + 1) + Work.PieceHomology.rankPt (k : ℤ)) ∧
    (∀ k : ℕ, Work.HomologyIso.rankT2 ((k : ℤ) + 1)
        = Work.PieceHomology.rankCirc ((k : ℤ) + 1) + Work.PieceHomology.rankCirc (k : ℤ)) ∧
    (∀ k : ℕ, Work.HomologyIso.rankT ((k : ℤ) + 1)
        = Work.HomologyIso.rankT2 ((k : ℤ) + 1) + Work.HomologyIso.rankT2 (k : ℤ)) ∧
    Work.HomologyIso.rankT2 0 = Work.PieceHomology.rankCirc 0 ∧
    Work.HomologyIso.rankT 0 = Work.HomologyIso.rankT2 0 ∧
    (∀ a b : ℕ, Nonempty (CategoryTheory.Limits.biprod (Work.HomologyMV.freeMod a)
        (Work.HomologyMV.freeMod b) ≅ Work.HomologyMV.freeMod (a + b))) ∧
    Nonempty (Work.HomologyMV.freeMod 0 ≅ ModuleCat.of ℤ PUnit) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [rankCirc_eq_add ((k : ℤ) + 1)]
    simp
  · intro k
    rw [rankT2_eq_add ((k : ℤ) + 1)]
    simp
  · intro k
    rw [rankT_eq_add ((k : ℤ) + 1)]
    simp
  · norm_num [Work.HomologyIso.rankT2, Work.PieceHomology.rankCirc]
  · norm_num [Work.HomologyIso.rankT, Work.HomologyIso.rankT2]
  · intro a b
    exact ⟨ModuleCat.biprodIsoProd (Work.HomologyMV.freeMod a) (Work.HomologyMV.freeMod b)
      ≪≫ LinearEquiv.toModuleIso (concatLin a b)⟩
  · exact ⟨LinearEquiv.toModuleIso (Classical.choice
      (Work.HomologyMV.linearEquiv_of_subsingleton (M := Fin 0 → ℤ) (N := PUnit)))⟩

end

end Work.PieceHomology
