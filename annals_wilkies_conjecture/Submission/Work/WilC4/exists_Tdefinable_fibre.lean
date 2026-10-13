import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4

open FirstOrder FirstOrder.Language

/-- If `y` is definable from `T ∪ {δ}` (as a singleton, with parameters), then the graph of
"the `T`-definable function defined by the same formula" is `T`-definable over `LRc`, contains
`(y, δ)`, and has singleton fibre over `δ`.

Concretely: `DefinableElt T {δ} y` gives a `LRc`-formula `φ` with parameters in `T ∪ {δ}` whose
`T ∪ {δ}`-instance cuts out `{y}`.  Replacing the parameter `δ` by the second free variable and
viewing `φ` as a formula over `T` produces a `2`-ary `T`-definable set `Z` whose `δ`-fibre is
exactly `{y}`. -/
theorem exists_Tdefinable_fibre {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M] {T : Set M} {δ y : M} (hyd : DefinableElt T {δ} y) : ∃ Z : Set (M × M), T.Definable₂ WilkiesDesign.CG.LRc Z ∧ (y, δ) ∈ Z ∧ ∀ v : M, (v, δ) ∈ Z → v = y := by
  classical
  -- Unfold `DefinableElt` and extract the defining formula.
  unfold DefinableElt at hyd
  rw [Set.definable_iff_exists_formula_sum] at hyd
  obtain ⟨φ, hφ⟩ := hyd
  -- `φ : LRc.Formula (↑(T ∪ {δ}) ⊕ Fin 1)` and
  -- `hφ : {fun _ => y} = {v | φ.Realize (Sum.elim (↑) v)}`.
  -- The map sending the parameter `δ` to the second free variable and the free variable
  -- `Fin 1` to the first free variable; all other parameters stay constants.
  let g : (↑(T ∪ {δ}) ⊕ Fin 1) → (↑T ⊕ Fin 2) :=
    Sum.elim (fun p : ↑(T ∪ {δ}) =>
        if h : (p : M) = δ then Sum.inr (1 : Fin 2)
        else Sum.inl ⟨(p : M),
          (Set.mem_or_mem_of_mem_union p.2).resolve_right
            (fun hc => h (Set.mem_singleton_iff.mp hc))⟩)
      (fun _ => Sum.inr (0 : Fin 2))
  -- Evaluation identity: substituting `δ ↦ b` in the parameters and setting the free variable to
  -- `a` is the same as evaluating `φ` at the parameters `T ∪ {δ}` with the free variable `a`,
  -- provided `b = δ`.
  have key : ∀ a : M,
      (Sum.elim (Subtype.val : ↑T → M) ![a, δ]) ∘ g =
        Sum.elim (Subtype.val : ↑(T ∪ {δ}) → M) (fun _ : Fin 1 => a) := by
    intro a
    funext s
    rcases s with p | i
    · by_cases hp : (p : M) = δ
      · simp only [Function.comp_apply, g, Sum.elim_inl, dif_pos hp]
        simp [hp]
      · simp only [Function.comp_apply, g, Sum.elim_inl, dif_neg hp]
    · simp only [Function.comp_apply, g, Sum.elim_inr]
      simp
  -- `φ` holds at the parameters `T ∪ {δ}` with free variable `y`.
  have hmem : φ.Realize (Sum.elim (Subtype.val : ↑(T ∪ {δ}) → M) (fun _ : Fin 1 => y)) := by
    have h : (fun _ : Fin 1 => y) ∈ ({fun _ : Fin 1 => y} : Set (Fin 1 → M)) := rfl
    rw [hφ] at h
    exact h
  -- The formula over `T` obtained by turning the `δ`-parameter into the second variable.
  let ψ : WilkiesDesign.CG.LRc.Formula (↑T ⊕ Fin 2) := φ.relabel g
  -- The definable set with singleton `δ`-fibre.
  let Z : Set (M × M) := {p | ψ.Realize (Sum.elim (Subtype.val : ↑T → M) ![p.1, p.2])}
  refine ⟨Z, ?_, ?_, ?_⟩
  · -- `Z` is `T`-definable.
    unfold Set.Definable₂
    rw [Set.definable_iff_exists_formula_sum]
    refine ⟨ψ, ?_⟩
    ext x
    simp only [Z, Set.mem_setOf_eq]
    have hv : ![x 0, x 1] = x := by funext i; fin_cases i <;> simp
    rw [hv]
  · -- `(y, δ) ∈ Z`.
    simp only [Z, ψ, Set.mem_setOf_eq]
    rw [Formula.realize_relabel, key y]
    exact hmem
  · -- The `δ`-fibre is a singleton.
    intro v hv
    simp only [Z, ψ, Set.mem_setOf_eq] at hv
    rw [Formula.realize_relabel, key v] at hv
    have h : (fun _ : Fin 1 => v) ∈ ({fun _ : Fin 1 => y} : Set (Fin 1 → M)) := by
      rw [hφ]; exact hv
    have h2 := Set.mem_singleton_iff.mp h
    simpa using congrFun h2 0

end Work.WilC4
