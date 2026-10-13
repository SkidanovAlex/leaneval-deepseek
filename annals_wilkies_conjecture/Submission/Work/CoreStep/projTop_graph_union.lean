import Mathlib
import Submission.Work.WilE7.MainDesignDefs

set_option linter.unusedVariables false

open WilkiesDesign.E

namespace Work.CoreStep

/-! ### Elementary facts used to identify the projection map of the statement

The map `z ↦ (fun i : Fin (n+1) => if i < n then z i else z (last))` sending `ℝ^{n+(m+1)}` to
`ℝ^{n+1}` keeps the first `n` coordinates and the *last* coordinate of `z`.  It is therefore the
`Fin.snoc` of the base projection `projFirst n (m+1) z` with the last entry of the fibre
`projSnd n (m+1) z`. -/

private lemma projFirst_append {p q : ℕ} (x : Fin p → ℝ) (y : Fin q → ℝ) :
    projFirst p q (Fin.append x y) = x := by
  funext i; simp [projFirst, Fin.append_left]

private lemma projSnd_append {p q : ℕ} (x : Fin p → ℝ) (y : Fin q → ℝ) :
    projSnd p q (Fin.append x y) = y := by
  funext i; simp [projSnd, Fin.append_right]

private lemma projTop_eq_snoc {n m : ℕ} (z : Fin (n + (m + 1)) → ℝ) :
    (fun i : Fin (n + 1) =>
        if h : (i : ℕ) < n then z ⟨i, by omega⟩ else z ⟨n + m, by omega⟩)
      = Fin.snoc (projFirst n (m + 1) z) (projSnd n (m + 1) z (Fin.last m)) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last, dite_eq_right (by simp : ¬ ((Fin.last n : Fin (n + 1)) : ℕ) < n)]
    simp only [projSnd, Fin.last]
    rw [Fin.natAdd_mk]
  · intro i'
    rw [Fin.snoc_castSucc, dite_eq_left (by simp : ((i'.castSucc : Fin (n + 1)) : ℕ) < n)]
    simp only [projFirst]
    exact congrArg z (Fin.ext rfl)

theorem projTop_graph_union {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ)) (k : ℕ) (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ (j : Fin k) (x : Fin n → ℝ), x ∈ C →
      Fin.append x (s j x) ∈ Work.WilE7.MainDesign.absSet T)
    (hcov : ∀ z ∈ Work.WilE7.MainDesign.absSet T,
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst n (m + 1) z) =
        WilkiesDesign.E.projSnd n (m + 1) z) :
    (fun z : Fin (n + (m + 1)) → ℝ => fun i : Fin (n + 1) =>
        if h : (i : ℕ) < n then z ⟨i, by omega⟩ else z ⟨n + m, by omega⟩) ''
        (Work.WilE7.MainDesign.absSet T ∩ {z | WilkiesDesign.E.projFirst n (m + 1) z ∈ C})
      = ⋃ j : Fin k, {y : Fin (n + 1) → ℝ | Fin.init y ∈ C ∧
          y (Fin.last n) = (s j (Fin.init y)) (Fin.last m)} := by
  have hP : (fun z : Fin (n + (m + 1)) → ℝ => fun i : Fin (n + 1) =>
        if h : (i : ℕ) < n then z ⟨i, by omega⟩ else z ⟨n + m, by omega⟩)
      = fun z => Fin.snoc (WilkiesDesign.E.projFirst n (m + 1) z)
          (WilkiesDesign.E.projSnd n (m + 1) z (Fin.last m)) :=
    funext fun z => projTop_eq_snoc z
  rw [hP]
  ext y
  constructor
  · -- every point of the source set is the graph of a section `s j` over its base point
    rintro ⟨z, hz, rfl⟩
    obtain ⟨j, hj⟩ := hcov z hz.1 hz.2
    refine Set.mem_iUnion.2 ⟨j, ?_, ?_⟩
    · simp only [Fin.init_snoc]; exact hz.2
    · simp only [Fin.init_snoc, Fin.snoc_last]; rw [hj]
  · -- conversely, a graph point over `C` is the image of the point obtained by appending `s j`
    intro hmem
    rw [Set.mem_iUnion] at hmem
    obtain ⟨j, hjc, hjlast⟩ := hmem
    refine ⟨Fin.append (Fin.init y) (s j (Fin.init y)),
      ⟨hsub j (Fin.init y) hjc, ?_⟩, ?_⟩
    · rw [Set.mem_ofPred_eq, projFirst_append]; exact hjc
    · simp only [projFirst_append, projSnd_append]
      rw [← hjlast]
      exact Fin.snoc_init_self y

end Work.CoreStep
