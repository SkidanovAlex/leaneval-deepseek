/-
  WilG4a : `cont_off_finite` — a one-variable function whose graph is `Ω`-definable has only
  finitely many points of discontinuity.

  Route (cell decomposition, no `SharpDeriv` needed).

  * `S.SharpCD` supplies, for the graph `Γ ⊆ ℝ²` of `g`, a finite cylindrical decomposition
    `C` of `ℝ²` refining `Γ`: every cell is either contained in `Γ` or disjoint from it.
  * Each `x : ℝ` therefore lies in a cell `φ x` (the one containing `pt x = (x, g x)`) which
    is contained in `Γ`; the projection `ℝ² → ℝ` is injective on that cell.
  * A 2-dimensional cell contained in a graph is the graph of a function `ψ` continuous on
    its one-dimensional base cell `C0` (`isCell_two_graph`).
  * A one-dimensional cell is either a singleton or open (`isCell_one_dichotomy`); in the
    second case `g` is continuous at `x` (`continuousAt_of_graphCell`).
  * Hence `x` is a point of discontinuity only if the base cell of `φ x` is the singleton
    `{x}`; those `x` are finite because `x ↦ φ x` is injective on them and `C` is finite.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.sharpCD_fintype
import Submission.Work.WilG4a.isCell_fiber
import Submission.Work.WilG4a.isCell_one_dichotomy
import Submission.Work.WilG4a.isCell_two_graph
import Submission.Work.WilG4a.continuousAt_of_graphCell

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a

open WilkiesDesign

theorem cont_off_finite (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) {F D : ℕ} (g : ℝ → ℝ)
    (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) :
    {x : ℝ | ¬ ContinuousAt g x}.Finite := by
  classical
  -- The sharp cell decomposition, in dimension `2`, of the family consisting of the graph.
  obtain ⟨a, b, c, H⟩ := hcd F 2
  obtain ⟨C, hdec, hsh, -, -⟩ :=
    H D 1 (fun _ : Fin 1 => WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)))
      (fun _ => hg)
  have hcells : (∀ c ∈ C, WilkiesDesign.IsCell 2 c ∧ c.Nonempty) ∧
      (C : Set (Set (Fin 2 → ℝ))).PairwiseDisjoint id ∧
      (∀ z : Fin 2 → ℝ, ∃ c ∈ C, z ∈ c) ∧
      WilkiesDesign.IsCylDecomp 1 (C.image (fun c : Set (Fin 2 → ℝ) => Fin.init '' c)) :=
    hdec
  obtain ⟨hcell2, -, hcover2, -⟩ := hcells
  -- The point of the graph above `x`, and the cell of the decomposition containing it.
  let pt : ℝ → (Fin 2 → ℝ) := fun x => Fin.snoc (fun _ : Fin 1 => x) (g x)
  have hpt_mem : ∀ x : ℝ,
      pt x ∈ WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) := by
    intro x
    simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq, pt, Fin.init_snoc, Fin.snoc_last]
  let φ : ℝ → Set (Fin 2 → ℝ) := fun x => (hcover2 (pt x)).choose
  have hφ_mem : ∀ x : ℝ, φ x ∈ C := fun x => (hcover2 (pt x)).choose_spec.1
  have hφ_pt : ∀ x : ℝ, pt x ∈ φ x := fun x => (hcover2 (pt x)).choose_spec.2
  -- The candidate exceptional set: `φ x` projects to the single point `x`.
  let P : Set ℝ := {x | Fin.init '' (φ x) = {fun _ : Fin 1 => x}}
  have hPfin : P.Finite := by
    refine Set.Finite.of_finite_image (s := P) (f := φ) ?_ ?_
    · refine C.finite_toSet.subset ?_
      rintro c ⟨x, -, rfl⟩
      exact hφ_mem x
    · intro x hx y hy hxy
      have hx1 : Fin.init '' (φ x) = {fun _ : Fin 1 => x} := hx
      have hy1 : Fin.init '' (φ y) = {fun _ : Fin 1 => y} := hy
      have hEqSet : ({fun _ : Fin 1 => x} : Set (Fin 1 → ℝ)) = {fun _ : Fin 1 => y} := by
        rw [← hx1, hxy, hy1]
      have hmem : (fun _ : Fin 1 => x) ∈ ({fun _ : Fin 1 => y} : Set (Fin 1 → ℝ)) := by
        rw [← hEqSet]; exact Set.mem_singleton _
      have hEq : (fun _ : Fin 1 => x) = (fun _ : Fin 1 => y) := Set.mem_singleton_iff.mp hmem
      simpa using congrFun hEq 0
  -- Off `P`, the cell above `x` has an open base, and `g` is continuous at `x`.
  have hcont : ∀ x : ℝ, x ∉ P → ContinuousAt g x := by
    intro x hxP
    set κ : Set (Fin 2 → ℝ) := φ x with hκdef
    have hκC : κ ∈ C := hφ_mem x
    have hptκ : pt x ∈ κ := hφ_pt x
    have hsubG : κ ⊆ WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) := by
      rcases hsh 0 κ hκC with h | h
      · exact h
      · exact absurd (hpt_mem x) (Set.disjoint_left.mp h hptκ)
    have hcellκ : WilkiesDesign.IsCell 2 κ := (hcell2 κ hκC).1
    obtain ⟨C0, ψ, hC0, hψcont, hκeq, hproj, hagree⟩ :=
      isCell_two_graph hcellκ ⟨pt x, hptκ⟩ hsubG
    have hbase : (fun _ : Fin 1 => x) ∈ C0 := by
      rw [← hproj]
      exact ⟨pt x, hptκ, by simp [pt]⟩
    rcases isCell_one_dichotomy hC0 with ⟨q, hq⟩ | hopen
    · -- the base is a singleton, i.e. `x ∈ P`, contradicting the hypothesis
      exfalso
      apply hxP
      have hq' : q = (fun _ : Fin 1 => x) := by
        have hbase' := hbase
        rw [hq] at hbase'
        exact (Set.mem_singleton_iff.mp hbase').symm
      calc Fin.init '' (φ x) = Fin.init '' κ := rfl
        _ = C0 := hproj
        _ = {q} := hq
        _ = {fun _ : Fin 1 => x} := by rw [hq']
    · -- the base is open, so `g` agrees locally with `ψ` along the diagonal
      refine continuousAt_of_graphCell hopen hψcont hbase ?_
      intro p hp
      exact hagree p hp
  exact hPfin.subset (fun x hx => by
    by_contra hxP
    exact hx (hcont x hxP))

end Work.WilG4a
