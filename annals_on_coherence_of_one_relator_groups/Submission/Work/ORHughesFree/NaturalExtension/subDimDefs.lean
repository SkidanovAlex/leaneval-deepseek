/-
# A dimension for submodules of free modules over a von Neumann regular ring

For a von Neumann regular ring `R` with a Sylvester rank function `rk`, and an `R`-submodule
`W ≤ R^n` (with `R^n = Fin n → R`), we define

  `subDim W := sSup { rk G : G is a matrix whose columns lie in W }`.

This is the value at `W` of the normalized length function associated with `rk`.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.DivisionRank.regular_leftIdeal_idempotent
import Submission.Work.ORHughesFree.RankAPI.rk_add_le
import Submission.Work.ORHughesFree.RankAPI.rk_le_left
import Submission.Work.ORHughesFree.RankAPI.rk_le_right

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

/-- The set of ranks of matrices whose columns lie in a submodule `W ≤ R^n`. -/
def subDimSet (R : Type u) [Ring R] (rk : SylvesterRank R) {n : ℕ}
    (W : Submodule R (Fin n → R)) : Set ℝ :=
  {x : ℝ | ∃ (m : ℕ) (g : Fin m → Fin n → R), (∀ j, g j ∈ W) ∧ x = rk.rk n m (fun i j => (g j) i)}

/-- For a von Neumann regular ring `R` with Sylvester rank function `rk`, the dimension of an
`R`-submodule `W` of `R^n` is the supremum of the ranks of the matrices whose columns lie
in `W`. -/
noncomputable def subDim (R : Type u) [Ring R] (rk : SylvesterRank R) {n : ℕ}
    (W : Submodule R (Fin n → R)) : ℝ :=
  sSup (subDimSet R rk W)

variable {R : Type u} [Ring R] (rk : SylvesterRank R)

theorem subDim_bddAbove {n : ℕ} (W : Submodule R (Fin n → R)) :
    BddAbove (subDimSet R rk W) :=
  ⟨(n : ℝ), by
    rintro x ⟨m, g, _, rfl⟩
    exact RankAPI.rk_le_left rk _⟩

theorem subDim_nonempty {n : ℕ} (W : Submodule R (Fin n → R)) :
    (subDimSet R rk W).Nonempty :=
  ⟨0, 1, fun _ => 0, fun _ => W.zero_mem, (rk.rk_zero n 1).symm⟩

theorem subDim_le_card {n : ℕ} (W : Submodule R (Fin n → R)) :
    subDim R rk W ≤ (n : ℝ) :=
  csSup_le (subDim_nonempty rk W) (by
    rintro x ⟨m, g, _, rfl⟩
    exact RankAPI.rk_le_left rk _)

theorem subDim_mono {n : ℕ} {W W' : Submodule R (Fin n → R)} (h : W ≤ W') :
    subDim R rk W ≤ subDim R rk W' :=
  csSup_le (subDim_nonempty rk W) (by
    rintro x ⟨m, g, hg, rfl⟩
    exact le_csSup (subDim_bddAbove rk W') ⟨m, g, fun j => h (hg j), rfl⟩)

theorem subDim_top (n : ℕ) : subDim R rk (⊤ : Submodule R (Fin n → R)) = (n : ℝ) := by
  refine le_antisymm (subDim_le_card rk ⊤) ?_
  have hmem : rk.rk n n (1 : Matrix (Fin n) (Fin n) R) ∈ subDimSet R rk
      (⊤ : Submodule R (Fin n → R)) :=
    ⟨n, fun j i => if i = j then (1 : R) else 0, fun j => Submodule.mem_top, rfl⟩
  have h2 := le_csSup (subDim_bddAbove rk ⊤) hmem
  rw [RankAPI.rk_identity_eq rk n] at h2
  exact h2

end Work.ORHughesFree.NaturalExtension
