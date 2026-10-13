/-
  Area G4b: **the fibre of `StarSet` over a bad `x` is nonempty**.

  The augmented choice set `StarSet f c d M` is the set which the definable-choice step of
  the source's argument is applied to; its `Ω`-format is independent of `M`.  This file
  supplies the point-level fact making that choice step meaningful: if `x` is a point of the
  exceptional set `badSet f s` of `G4_bdd_dx` (so `∂₀ f` is unbounded on the fibre over `x`)
  and the `y`-partials are bounded on that fibre off `s`, then the fibre of `StarSet` over `x`
  is nonempty.

  The mathematics is elementary: `badCore` gives a point `y` of the open cube with
  `|∂₀ f (x,y)|` as large as we like, and `hs` gives a bound `B` for the `y`-partials at `y`.
  Taking `u = |B|`, the point `(x, y, f (x,y), u)` lies in `StarSet f c d M`.  All the work is
  index bookkeeping with `Fin.snoc`/`Fin.init`, isolated in the lemmas below.
-/
import Mathlib
import Submission.Work.WilG4b.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4b
open WilkiesDesign WilkiesConjecture

/-! ## Index bookkeeping for the doubly-`snoc`ed vector `(x, y, w, u)`

For `Y : Fin (n+1) → ℝ`, `w u : ℝ`, the vector `snoc2 Y w u : Fin (n+3) → ℝ` encodes
`(Y 0, …, Y n, w, u)`.  Since `Fin.snoc` is a dependently typed function, every statement
about it needs an explicit expected type; `snoc2` provides one once and for all. -/

/-- `snoc2 Y w u = (Y 0, …, Y n, w, u)`: the point of `ℝ^{n+3}` whose first `n+1` coordinates
are `Y`, followed by `w` and then `u`. -/
def snoc2 {n : ℕ} (Y : Fin (n + 1) → ℝ) (w u : ℝ) : Fin (n + 3) → ℝ :=
  Fin.snoc (Fin.snoc Y w) u

lemma snoc2_zero {n : ℕ} (Y : Fin (n + 1) → ℝ) (w u : ℝ) :
    snoc2 Y w u 0 = Y 0 := by
  simp only [snoc2, Fin.snoc_apply_zero]

lemma snoc2_castAdd_succ {n : ℕ} (Y : Fin (n + 1) → ℝ) (w u : ℝ) (i : Fin n) :
    snoc2 Y w u (Fin.castAdd 2 i.succ) = Y i.succ := by
  show snoc2 Y w u (Fin.castSucc (Fin.castSucc i.succ)) = Y i.succ
  simp only [snoc2, Fin.snoc_castSucc]

lemma snoc2_init {n : ℕ} (Y : Fin (n + 1) → ℝ) (w u : ℝ) :
    Fin.init (snoc2 Y w u) = Fin.snoc Y w := by
  simp only [snoc2, Fin.init_snoc]

lemma snoc2_init_init {n : ℕ} (Y : Fin (n + 1) → ℝ) (w u : ℝ) :
    Fin.init (Fin.init (snoc2 Y w u)) = Y := by
  simp only [snoc2, Fin.init_snoc]

lemma snoc2_last {n : ℕ} (Y : Fin (n + 1) → ℝ) (w u : ℝ) :
    snoc2 Y w u (Fin.last (n + 2)) = u := by
  simp only [snoc2, Fin.snoc_last]

/-! ## The fibre is nonempty -/

theorem starFibre_nonempty {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ} (hn : 1 ≤ n) {s : Finset ℝ}
    (hs : ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ∉ s → ∃ B : ℝ, ∀ y ∈ WilkiesDesign.openCube n,
      Fin.cons x y ∈ interior {z | ContDiffAt ℝ 1 f z} →
        ∀ i : Fin n, |fderiv ℝ f (Fin.cons x y) (Pi.single i.succ 1)| ≤ B)
    {c d M : ℝ} {x : Fin 1 → ℝ} (hx : x 0 ∈ Set.Ioo c d) (hxbad : x ∈ Work.WilG4b.badSet f s) :
    ∃ V : Fin (n + 3) → ℝ, V ∈ Work.WilG4b.StarSet f c d M ∧ V 0 = x 0 := by
  -- ## Unpack the bad point: `x ∈ (0,1) \ s` and `∂₀ f` is unbounded over the fibre of `x`
  obtain ⟨hx01, hxs, hxbc⟩ := hxbad
  -- ## The uniform bound `B` for the `y`-partials at `x`
  obtain ⟨B, hB⟩ := hs (x 0) hx01 (by simpa using hxs)
  -- ## A point `y` of the cube over which `∂₀ f` beats `M * (1 + n * |B|)`
  obtain ⟨y, hycube, hc1, hbig⟩ := (badCore_iff f x).mp hxbc (M * (1 + (n : ℝ) * |B|))
  -- ## The witness `(x, y, f (x,y), |B|)`
  refine ⟨snoc2 (Fin.cons (x 0) y) (f (Fin.cons (x 0) y)) |B|, ?_, ?_⟩
  · simp only [StarSet, Set.mem_ofPred_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- `x ∈ (c,d)`
      simpa only [snoc2_zero, Fin.cons_zero] using hx
    · -- `y` lies in the open cube
      intro i
      show snoc2 (Fin.cons (x 0) y) (f (Fin.cons (x 0) y)) |B| (Fin.castAdd 2 i.succ)
        ∈ Set.Ioo 0 1
      rw [snoc2_castAdd_succ, Fin.cons_succ]
      exact hycube i
    · -- the point is on the graph of `f`
      simp only [graphOf, Set.mem_ofPred_eq, snoc2_init, Fin.init_snoc, Fin.snoc_last]
    · -- `u = |B| ≥ 0`
      rw [snoc2_last]
      exact abs_nonneg B
    · -- the `x`-derivative dominates `M * (1 + n*u)`
      refine ⟨dDir f 0 (Fin.cons (x 0) y), ?_, ?_⟩
      · simp only [derivGraph, Set.mem_ofPred_eq, snoc2_init, Fin.init_snoc, Fin.snoc_last]
        exact ⟨hc1, trivial⟩
      · rw [snoc2_last]
        exact hbig
    · -- the `y`-partials are bounded by `u`
      intro j
      refine ⟨dDir f j.succ (Fin.cons (x 0) y), ?_, ?_⟩
      · simp only [derivGraph, Set.mem_ofPred_eq, snoc2_init, Fin.init_snoc, Fin.snoc_last]
        exact ⟨hc1, trivial⟩
      · rw [snoc2_last]
        exact le_trans (hB y hycube hc1 j) (le_abs_self B)
  · -- the first coordinate is `x 0`
    simp only [snoc2_zero, Fin.cons_zero]

end Work.WilG4b
