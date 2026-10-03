/-
# The low-rank (blind) inversion of the Gowers-transform relation

Algebraic heart of `Work.Peluse.Ulower.StepLe.blindConvertK`, the "blind conversion" step of
Peluse's degree-lowering argument (Peluse, arXiv:1909.00309, §8; Peluse--Prendiville,
arXiv:1903.02592, §6, where the same step appears as "the right-hand side of this identity is
*low rank*").

Let `β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ` be a phase function (`β u v` for a pair of shift vectors),
`h` a **frozen** vector and `v₀` a real number (the *pinned value* of the Gowers transform).  For
`ω : Fin σ → Bool` let `mixv h v ω` be the coordinatewise mixture
`(mixv h v ω) i = if ω i then v i else h i`, and let

  `gowersDiff β h u v = ∑ ω, (-1) ^ weight ω * β u (mixv h v ω)`

be the Gowers transform of `β u ·` over the two *levels* `h` and `v`.

The functions `blindPhase β h v₀ u v i₀ i` (i = 1…σ) are obtained by grouping the patterns
`ω ≠ (fun _ ⇒ true)` according to the **first** coordinate in which `ω` is `false`, and adding the
pinned value to the group `i₀`:

* `blindPhase_blind`: `blindPhase … i` does **not depend on the `i`-th coordinate of `v`**;
* `sum_blindPhase`: for every `v`,
  `∑ i, blindPhase β h v₀ u v i₀ i = β u v - (-1)^σ * (gowersDiff β h u v - v₀)`,

so on the pairs where the Gowers transform equals the pinned value `v₀` the phase `β u v` is
*exactly* the sum of the `σ` blind functions.

## Reference

`NOTES_degree_lowering_SESSION5.md` §1 (steps 3-4); `NOTES_lemma74_denseSet_chain.md`.
-/

import Mathlib
import Submission.Work.Peluse.Basic

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe

noncomputable section

/-- The coordinatewise mixture of the frozen vector `h` and the varying vector `v`. -/
def mixv {σ : ℕ} (h v : Fin σ → ℤ) (ω : Fin σ → Bool) : Fin σ → ℤ :=
  fun i => if ω i then v i else h i

@[simp] lemma mixv_apply {σ : ℕ} (h v : Fin σ → ℤ) (ω : Fin σ → Bool) (i : Fin σ) :
    mixv h v ω i = if ω i then v i else h i := rfl

/-- The "all varying" pattern. -/
lemma mixv_true {σ : ℕ} (h v : Fin σ → ℤ) : mixv h v (fun _ => true) = v := by
  funext i; simp [mixv]

/-- The "all frozen" pattern. -/
lemma mixv_false {σ : ℕ} (h v : Fin σ → ℤ) : mixv h v (fun _ => false) = h := by
  funext i; simp [mixv]

/-- The Gowers transform of `β u ·` over the two levels `h` and `v`. -/
def gowersDiff {σ : ℕ} (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ)
    (h : Fin σ → ℤ) (u v : Fin σ → ℤ) : ℝ :=
  ∑ ω : Fin σ → Bool, (-1 : ℝ) ^ (Work.Peluse.weight ω) * β u (mixv h v ω)

/-- `Sset i` is the set of patterns `ω` whose *first* coordinate at which `ω` is `false` is `i`.
On `Sset i` the `i`-th coordinate of the mixture is the frozen value `h i`. -/
def Sset {σ : ℕ} (i : Fin σ) : Finset (Fin σ → Bool) :=
  Finset.univ.filter (fun ω => ω i = false ∧ ∀ j : Fin σ, j < i → ω j = true)

lemma mem_Sset {σ : ℕ} {i : Fin σ} {ω : Fin σ → Bool} :
    ω ∈ Sset i ↔ ω i = false ∧ ∀ j : Fin σ, j < i → ω j = true := by
  simp [Sset]

/-- On `Sset i` the `i`-th coordinate of the mixture is the frozen value. -/
lemma mixv_Sset {σ : ℕ} {i : Fin σ} {ω : Fin σ → Bool} (hω : ω ∈ Sset i)
    (h v : Fin σ → ℤ) : mixv h v ω i = h i := by
  rw [mixv_apply, (mem_Sset.mp hω).1]; simp

/-- A pattern other than the all-true pattern has a `false` coordinate. -/
lemma exists_false_of_ne_true {σ : ℕ} {ω : Fin σ → Bool} (h : ω ≠ (fun _ => true)) :
    ∃ i : Fin σ, ω i = false := by
  by_contra hc
  push_neg at hc
  exact h (funext fun i => by
    cases hb : ω i with
    | false => exact absurd hb (hc i)
    | true => rfl)

/-- Every pattern other than the all-true pattern lies in some `Sset i`. -/
lemma exists_mem_Sset_of_ne_true {σ : ℕ} {ω : Fin σ → Bool} (h : ω ≠ (fun _ => true)) :
    ∃ i : Fin σ, ω ∈ Sset i := by
  obtain ⟨i, hi⟩ := exists_false_of_ne_true h
  let s : Finset (Fin σ) := Finset.univ.filter (fun j : Fin σ => ω j = false)
  have hsne : s.Nonempty := ⟨i, by simp [s, hi]⟩
  refine ⟨s.min' hsne, ?_⟩
  rw [mem_Sset]
  have hmin : (s.min' hsne) ∈ s := Finset.min'_mem s hsne
  have hfalse : ω (s.min' hsne) = false := (Finset.mem_filter.mp hmin).2
  refine ⟨hfalse, ?_⟩
  intro j hj
  have hjs : j ∉ s := by
    intro hjs
    have hle : s.min' hsne ≤ j := Finset.min'_le s j hjs
    exact absurd (lt_of_lt_of_le hj hle) (lt_irrefl j)
  have hnf : ¬ (ω j = false) := by
    intro hf
    exact hjs (by simp [s, hf])
  cases hb : ω j with
  | false => exact absurd hb hnf
  | true => rfl

/-- Distinct `Sset i` are disjoint. -/
lemma Sset_disjoint {σ : ℕ} {i j : Fin σ} (hij : i ≠ j) : Disjoint (Sset i) (Sset j) := by
  rw [Finset.disjoint_left]
  intro ω hi hj'
  rw [mem_Sset] at hi hj'
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have h2 := hj'.2 i hlt
    rw [hi.1] at h2
    exact Bool.false_ne_true h2
  · have h2 := hi.2 j hgt
    rw [hj'.1] at h2
    exact Bool.false_ne_true h2

/-- The patterns other than the all-true one are the disjoint union of the `Sset i`.  Consequently
a sum over them is the sum of the sums over the `Sset i`. -/
lemma sum_Sset_eq {σ : ℕ} (F : (Fin σ → Bool) → ℝ) :
    ∑ ω ∈ Finset.univ.filter (fun ω : Fin σ → Bool => ω ≠ (fun _ => true)), F ω
      = ∑ i : Fin σ, ∑ ω ∈ Sset i, F ω := by
  classical
  rw [← Finset.sum_biUnion (s := (Finset.univ : Finset (Fin σ)))
    (t := fun i : Fin σ => Sset i) (f := F) (by
      intro i _ j _ hij
      exact Sset_disjoint hij)]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ω
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · intro h
    exact exists_mem_Sset_of_ne_true h
  · rintro ⟨i, hi⟩ htop
    have h1 := (mem_Sset.mp hi).1
    rw [htop] at h1
    simp at h1

/-- **The blind phases.**  Group the patterns `ω ≠ (fun _ ⇒ true)` by the first coordinate in
which `ω` is `false`; the `i`-th group is blind in the `i`-th coordinate of `v`.  The pinned value
`v₀` (with the sign `(-1)^σ`) is added to the group indexed by `i₀`. -/
def blindPhase {σ : ℕ} (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) (h : Fin σ → ℤ)
    (v₀ : ℝ) (u v : Fin σ → ℤ) (i₀ : Fin σ) (i : Fin σ) : ℝ :=
  -((-1 : ℝ) ^ σ) * (∑ ω ∈ Sset i, (-1 : ℝ) ^ (Work.Peluse.weight ω) * β u (mixv h v ω))
    + (if i = i₀ then ((-1 : ℝ) ^ σ) * v₀ else 0)

lemma blindPhase_zero {σ : ℕ} (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) (h : Fin σ → ℤ)
    (v₀ : ℝ) (u v : Fin σ → ℤ) (i₀ i : Fin σ) :
    blindPhase β h v₀ u v i₀ i
      = -((-1 : ℝ) ^ σ) * (∑ ω ∈ Sset i, (-1 : ℝ) ^ (Work.Peluse.weight ω) * β u (mixv h v ω))
        + (if i = i₀ then ((-1 : ℝ) ^ σ) * v₀ else 0) := rfl

/-- The `i`-th blind phase does not depend on the `i`-th coordinate of `v`. -/
theorem blindPhase_blind {σ : ℕ} (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) (h : Fin σ → ℤ)
    (v₀ : ℝ) (u : Fin σ → ℤ) (i₀ i : Fin σ) (a b : ℤ) (v : Fin σ → ℤ) :
    blindPhase β h v₀ u (Function.update v i a) i₀ i
      = blindPhase β h v₀ u (Function.update v i b) i₀ i := by
  classical
  have key : ∀ ω ∈ Sset i,
      mixv h (Function.update v i a) ω = mixv h (Function.update v i b) ω := by
    intro ω hω
    funext j
    rw [mixv_apply, mixv_apply]
    by_cases hj : j = i
    · subst hj
      rw [(mem_Sset.mp hω).1]
      simp
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  rw [blindPhase_zero, blindPhase_zero,
    Finset.sum_congr rfl (fun ω hω => by rw [key ω hω])]

/-- **The low-rank identity.**  The sum of the blind phases equals `β u v` minus the signed defect
of the Gowers transform from the pinned value `v₀`. -/
theorem sum_blindPhase {σ : ℕ} (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) (h : Fin σ → ℤ)
    (v₀ : ℝ) (u v : Fin σ → ℤ) (i₀ : Fin σ) :
    ∑ i : Fin σ, blindPhase β h v₀ u v i₀ i
      = β u v - (-1 : ℝ) ^ σ * (gowersDiff β h u v - v₀) := by
  classical
  -- the non-all-true part of the Gowers transform
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin σ → Bool)))
    (p := fun ω : Fin σ → Bool => ω ≠ (fun _ => true))
    (f := fun ω => (-1 : ℝ) ^ (Work.Peluse.weight ω) * β u (mixv h v ω))
  have hcompl : (Finset.univ.filter
      (fun ω : Fin σ → Bool => ¬ (ω ≠ (fun _ => true)))) = {(fun _ => true)} := by
    ext ω; simp
  have hweight : Work.Peluse.weight (fun _ : Fin σ => true) = σ := by
    simp [Work.Peluse.weight]
  have hmixv : mixv h v (fun _ : Fin σ => true) = v := mixv_true h v
  rw [hcompl, Finset.sum_singleton] at hsplit
  have hsplit' : (∑ ω : Fin σ → Bool, (-1 : ℝ) ^ (Work.Peluse.weight ω) * β u (mixv h v ω))
      = (∑ ω ∈ Finset.univ.filter (fun ω : Fin σ → Bool => ω ≠ (fun _ => true)),
            (-1 : ℝ) ^ (Work.Peluse.weight ω) * β u (mixv h v ω)) + (-1 : ℝ) ^ σ * β u v := by
    rw [← hsplit, hweight, hmixv]
  have hG : gowersDiff β h u v
      = (∑ ω ∈ Finset.univ.filter (fun ω : Fin σ → Bool => ω ≠ (fun _ => true)),
            (-1 : ℝ) ^ (Work.Peluse.weight ω) * β u (mixv h v ω)) + (-1 : ℝ) ^ σ * β u v := by
    simpa only [gowersDiff] using hsplit'
  -- the sum of the blind phases
  have hconst : (∑ i : Fin σ, (if i = i₀ then ((-1 : ℝ) ^ σ) * v₀ else 0))
      = ((-1 : ℝ) ^ σ) * v₀ := by
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hexp : (∑ i : Fin σ, blindPhase β h v₀ u v i₀ i)
      = ∑ i : Fin σ, (-((-1 : ℝ) ^ σ) *
            (∑ ω ∈ Sset i, (-1 : ℝ) ^ (Work.Peluse.weight ω) * β u (mixv h v ω))
          + (if i = i₀ then ((-1 : ℝ) ^ σ) * v₀ else 0)) := rfl
  have hL : (∑ i : Fin σ, blindPhase β h v₀ u v i₀ i)
      = -((-1 : ℝ) ^ σ) * (∑ i : Fin σ, ∑ ω ∈ Sset i,
            (-1 : ℝ) ^ (Work.Peluse.weight ω) * β u (mixv h v ω)) + ((-1 : ℝ) ^ σ) * v₀ := by
    rw [hexp, Finset.sum_add_distrib, hconst, ← Finset.mul_sum]
  have hsq : (-1 : ℝ) ^ σ * (-1 : ℝ) ^ σ = 1 := by
    have h2 : (-1 : ℝ) ^ (σ * 2) = 1 := by
      have : Even (σ * 2) := ⟨σ, by ring⟩
      simpa using Even.neg_one_pow this
    rw [← pow_add, show σ + σ = σ * 2 by ring, h2]
  rw [hL, hG, sum_Sset_eq (fun ω => (-1 : ℝ) ^ (Work.Peluse.weight ω) * β u (mixv h v ω))]
  linear_combination (β u v) * hsq

end

end Work.Peluse.Ulower.StepLe
