import Mathlib
import Submission.Work.OROneRel.GaugeDefs

/-!
# The level list and the label list of a decorated word

The decorated word `decor c i M` of `Submission/Work/OROneRel/MagnusGenDefs.lean` is a walk on the
levels `ℤ`: the `k`-th decorated letter has *source level* `coverSrc c` and *target level*
`coverTgt c`, and the target level of the `k`-th letter is the source level of the `(k+1)`-st one.

This file records that walk in two plain lists:

* `lv c i M : List ℤ`, of length `M.length + 1`, whose `k`-th entry is the source level of the
  `k`-th decorated letter (`lv c i M = [i, i + d₀, i + d₀ + d₁, …]` where `dₖ = linc c Mₖ`);
  in particular the last entry is `i + lsig c M`;
* `lab M : List (FreeGroup α)`, of length `M.length`, whose `k`-th entry is the element of the free
  group read at the `k`-th decorated letter (`coverLetter ∘ (decor c i M)`).

With these, the loop class of the `k`-th decorated letter is
`W (lv c i M)[k] * (lab M)[k] * (W (lv c i M)[k+1])⁻¹`, so that the loop classes are determined by
the walk `lv` and the labels `lab` alone.  This is the input to the gauge construction of
`Submission/Work/OROneRel/gauge_nontrivial_bound.lean`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The increment of the level when a letter of a word is read: `+c a` for the positive letter `a`
and `-c a` for its inverse. -/
def linc (c : α → ℤ) (p : α × Bool) : ℤ := if p.2 then c p.1 else -c p.1

/-- The list of levels of the decorated word `decor c i M`: its `k`-th entry is the source level of
the `k`-th decorated letter, and its length is `M.length + 1`. -/
def lv (c : α → ℤ) (i : ℤ) (M : List (α × Bool)) : List ℤ :=
  (M.map (linc c)).scanl (· + ·) i

/-- The labels read at the decorated letters of a word. -/
def lab (M : List (α × Bool)) : List (FreeGroup α) :=
  M.map (fun p => if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹)

theorem lv_length (c : α → ℤ) (i : ℤ) (M : List (α × Bool)) :
    (lv c i M).length = M.length + 1 := by
  simp [lv, List.length_scanl]

theorem lv_head (c : α → ℤ) (i : ℤ) (M : List (α × Bool)) : (lv c i M).head? = some i := by
  simp [lv, List.head?_scanl]

theorem lab_length (M : List (α × Bool)) : (lab M).length = M.length := by
  simp [lab]

theorem lv_zero_getD (c : α → ℤ) (M : List (α × Bool)) : (lv c 0 M).getD 0 0 = 0 := by
  obtain ⟨ys, hy⟩ := List.head?_eq_some_iff.mp (lv_head c 0 M)
  rw [hy]
  simp

theorem lv_cons (c : α → ℤ) (i : ℤ) (p : α × Bool) (M : List (α × Bool)) :
    lv c i (p :: M) = i :: lv c (i + linc c p) M := by
  simp [lv, List.scanl_cons]

/-- The decorated word of a word has the same length as the word. -/
theorem decor_length (c : α → ℤ) (i : ℤ) (M : List (α × Bool)) :
    (decor c i M).length = M.length := by
  induction M generalizing i with
  | nil => rfl
  | cons p M ih =>
      obtain ⟨a, b⟩ := p
      cases b <;> simp [decor, ih]

end Work.OROneRel
