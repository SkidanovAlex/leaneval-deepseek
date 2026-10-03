import Mathlib
import Submission.Work.Peluse.SwapC.cprocNodup

/-!
# `HasSplit Λ ↔ Λ.length < 2 ^ s` for a leaf list with `cellSum Λ = 2 ^ s`

Write `cellSize l = 2 ^ (s - l.dep)` for the size of the cell of a leaf and
`cellSum Λ = ∑_{l ∈ Λ} cellSize l`.  Since `l.dep ≤ s` we always have `1 ≤ cellSize l`:

* `cellSum Λ ≥ Λ.length` — hence a list with `cellSum Λ = 2 ^ s` has at most `2 ^ s` leaves;
* a splittable leaf (`l.dep < s`) contributes at least `2`, so `HasSplit Λ` forces
  `cellSum Λ ≥ Λ.length + 1`, i.e. `Λ.length < 2 ^ s`;
* if no leaf is splittable then `l.dep = s` for every leaf, so `cellSize l = 1` and
  `cellSum Λ = Λ.length`, i.e. `Λ.length = 2 ^ s`.

The last two combine to the stated equivalence.
-/

namespace Work.Peluse.SwapC

set_option autoImplicit false

variable {s : ℕ}

/-- `cellSum` on a cons. -/
private lemma cellSum_cons (l : CLeaf s) (Λ : List (CLeaf s)) :
    cellSum (l :: Λ) = 2 ^ (s - l.dep) + cellSum Λ := rfl

/-- Every leaf of `{0,1}^s` has cell size at least `1`. -/
private lemma one_le_cellSize (l : CLeaf s) : 1 ≤ 2 ^ (s - l.dep) :=
  Nat.one_le_two_pow

/-- The number of leaves never exceeds the cell sum. -/
private lemma length_le_cellSum (Λ : List (CLeaf s)) : Λ.length ≤ cellSum Λ := by
  induction Λ with
  | nil => simp [cellSum]
  | cons l rest ih =>
    rw [cellSum_cons, List.length_cons]
    have := one_le_cellSize l
    omega

/-- A splittable leaf contributes `≥ 2`, so `HasSplit Λ` forces a strict surplus. -/
private lemma length_add_one_le_cellSum_of_hasSplit {Λ : List (CLeaf s)} (h : HasSplit Λ) :
    Λ.length + 1 ≤ cellSum Λ := by
  induction Λ with
  | nil => rw [HasSplit] at h; simp at h
  | cons l rest ih =>
    rw [HasSplit] at h
    rcases h with ⟨m, hm, hmd⟩
    rw [cellSum_cons, List.length_cons]
    rcases List.mem_cons.mp hm with rfl | hmrest
    · have h2 : 2 ≤ 2 ^ (s - m.dep) := by
        have hlt : 1 ≤ s - m.dep := by omega
        calc (2 : ℕ) = 2 ^ 1 := rfl
          _ ≤ 2 ^ (s - m.dep) := Nat.pow_le_pow_right (by norm_num) hlt
      have := length_le_cellSum rest
      omega
    · have hh : HasSplit rest := ⟨m, hmrest, hmd⟩
      have := ih hh
      have h1 := one_le_cellSize l
      omega

/-- If no leaf is splittable then every leaf has depth `s`, hence cell size `1`. -/
private lemma cellSum_eq_length_of_all_dep {Λ : List (CLeaf s)} (h : ∀ l ∈ Λ, l.dep = s) :
    cellSum Λ = Λ.length := by
  induction Λ with
  | nil => simp [cellSum]
  | cons l rest ih =>
    rw [cellSum_cons, List.length_cons, h l (List.mem_cons_self ..), Nat.sub_self, pow_zero]
    rw [ih (fun m hm => h m (List.mem_cons_of_mem l hm))]
    omega

theorem hasSplitIffLengthLt {s : ℕ} {Λ : List (Work.Peluse.SwapC.CLeaf s)}
    (hc : Work.Peluse.SwapC.cellSum Λ = 2 ^ s) :
    Work.Peluse.SwapC.HasSplit Λ ↔ Λ.length < 2 ^ s := by
  constructor
  · intro h
    have := length_add_one_le_cellSum_of_hasSplit h
    omega
  · intro h
    by_contra hcon
    rw [HasSplit] at hcon
    push Not at hcon
    have hdep : ∀ l ∈ Λ, l.dep = s := by
      intro l hl
      have := hcon l hl
      have := l.dep_le
      omega
    have heq := cellSum_eq_length_of_all_dep hdep
    omega

end Work.Peluse.SwapC
