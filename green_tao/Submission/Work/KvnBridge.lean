import Submission.Work.KvnStep

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Bridging the `ℕ`-indexed and `Fin`-indexed presentations of the §7 σ-algebras

`kpartExt d C ε n G α Fnew αnew` is the `ℕ`-indexed presentation (via `Function.update`) of the
join `B_{n+1} = B_n ∨ B_{ε,η}(𝒟F_{n+1})`, whereas the transference machinery
(`Commons.Combinatorics.Transference.bohr_sigma_atom_gen_poly_max` and every other commons
lemma about the `bohr-sigma` estimate) is stated for a `Fin K`-indexed family of generators.
This file records the (elementary) identification of the two, which is the only bookkeeping
needed to apply the `Fin`-indexed commons lemmas to the tower.
-/

open Finset
open scoped BigOperators

namespace GTTrans

open Commons.Combinatorics.Transference
open FinSigma

variable {p : ℕ} [Fact p.Prime]

/-- `kpartExt` is the `Fin (n+1)`-indexed join of the level sets of the updated generators. -/
lemma kpartExt_eq_fin_filter (d : ℕ) (C ε : ℝ) (n : ℕ) (G : ℕ → ZMod p → ℝ) (α : ℕ → ℝ)
    (Fnew : ZMod p → ℝ) (αnew : ℝ) (x : ZMod p) :
    kpartExt d C ε n G α Fnew αnew x = Finset.univ.filter (fun y =>
      ∀ j : Fin (n + 1), ⌊(davg d (fun z => (Function.update G n Fnew) (j : ℕ) z / (2 * C)) y
          - (Function.update α n αnew) (j : ℕ)) / ε⌋
        = ⌊(davg d (fun z => (Function.update G n Fnew) (j : ℕ) z / (2 * C)) x
          - (Function.update α n αnew) (j : ℕ)) / ε⌋) := by
  rw [kpartExt, kpart]
  apply Finset.filter_congr
  intro y _
  exact ⟨fun h j => h (j : ℕ) j.isLt, fun h j hj => h ⟨j, hj⟩⟩

end GTTrans
