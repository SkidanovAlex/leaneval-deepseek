/-
# Slicing the colouring space along a set of coordinates

This module collects the elementary "slicing" vocabulary used by the concentration proof of
`Work.Deep.Sparse.ncp_concentration`.

The uniform colouring `f : V → Fin k` (`colSpace`, `Submission/Work/Deep/Sparse/ProbBasic.lean`)
is a product measure, so for a fixed finite set `A` of vertices one may condition on the colours
outside `A` ("the fibre") and average over the colours on `A`.

* `graft A g f` — the colouring obtained from `f` by replacing the `A`-coordinates by `g`.
* `fibreMean A Y f` — the mean of `Y` over the fibre through `f`, i.e. the average of
  `Y (graft A g f)` over all `g : ↥A → Fin k`.
* `occRaw A f j` — the number of colours occurring at least `j` times among `f` on `A`
  (the *unretained* occupancy count; the retained occupancy count
  `Work.Deep.Sparse.occCount G f v j` of `ncp_concentration.lean` is `≤ occRaw (N v) f j`).
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbBasic

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Grafting**: replace the `A`-coordinates of `f` by `g`. -/
def graft {k : ℕ} (A : Finset V) (g : ↥A → Fin k) (f : V → Fin k) : V → Fin k :=
  fun u => if h : u ∈ A then g ⟨u, h⟩ else f u

lemma graft_apply_of_mem {k : ℕ} {A : Finset V} (g : ↥A → Fin k) (f : V → Fin k)
    {u : V} (h : u ∈ A) : graft A g f u = g ⟨u, h⟩ := by
  simp [graft, h]

lemma graft_apply_of_notMem {k : ℕ} {A : Finset V} (g : ↥A → Fin k) (f : V → Fin k)
    {u : V} (h : u ∉ A) : graft A g f u = f u := by
  simp [graft, h]

/-- Grafting is idempotent on the `A`-coordinates: `graft A g (graft A g' f) = graft A g f`. -/
lemma graft_graft {k : ℕ} {A : Finset V} (g g' : ↥A → Fin k) (f : V → Fin k) :
    graft A g (graft A g' f) = graft A g f := by
  funext u
  by_cases hu : u ∈ A <;> simp [graft, hu]

/-- Updating an `A`-coordinate of a grafted colouring is the same as grafting the updated
function. -/
lemma graft_update {k : ℕ} {A : Finset V} (g : ↥A → Fin k) (f : V → Fin k)
    (a : ↥A) (x : Fin k) :
    graft A (Function.update g a x) f = Function.update (graft A g f) a.val x := by
  funext w
  by_cases hw : w = a.val
  · subst hw
    simp [graft]
  · rw [Function.update_of_ne hw]
    by_cases hwA : w ∈ A
    · have hwa' : (⟨w, hwA⟩ : ↥A) ≠ a := fun h => hw (congrArg Subtype.val h)
      simp [graft, hwA, Function.update_of_ne hwa']
    · simp [graft, hwA, hw]

/-- The mean of `Y` over the fibre through `f` (the coordinates outside `A` fixed). -/
noncomputable def fibreMean {k : ℕ} (A : Finset V) (Y : (V → Fin k) → ℝ) (f : V → Fin k) : ℝ :=
  (1 / (k : ℝ) ^ A.card) * ∑ g : ↥A → Fin k, Y (graft A g f)

/-- `fibreMean` only depends on the coordinates outside `A`. -/
lemma fibreMean_graft {k : ℕ} (A : Finset V) (Y : (V → Fin k) → ℝ) (f : V → Fin k)
    (g : ↥A → Fin k) : fibreMean A Y (graft A g f) = fibreMean A Y f := by
  unfold fibreMean
  congr 1
  refine Finset.sum_congr rfl fun g' _ => ?_
  rw [graft_graft]

/-- The number of colours occurring at least `j` times among the values of `f` on `A`. -/
noncomputable def occRaw {k : ℕ} (A : Finset V) (f : V → Fin k) (j : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter (fun c => j ≤ (A.filter (fun x => f x = c)).card)).card

lemma occRaw_mono {k : ℕ} {A : Finset V} (f : V → Fin k) {j j' : ℕ} (h : j ≤ j') :
    occRaw A f j' ≤ occRaw A f j := by
  classical
  unfold occRaw
  refine Finset.card_le_card fun c hc => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  exact le_trans h hc

end Work.Deep.Sparse
