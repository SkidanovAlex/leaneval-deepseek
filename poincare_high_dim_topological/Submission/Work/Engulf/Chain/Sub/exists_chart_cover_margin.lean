import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Defs
import Submission.Work.Cells.Connell.cubeChart_isOpen_image_openCube

/-!
# A finite smoothing-chart cover of a compact set, with a margin

`Work.Engulf.Tame n p X Γ L f` produces, through every point `x : M`, a cube chart `ψ` whose
open `1/2`-cube contains `x` and which is a `SmoothChart` (Newman (9.3)).  A compact set `S`
can therefore be covered by finitely many *balls* `ball (y j) (ρ j)`, each of which is doubled
into the image of the open `1/2`-cube of the corresponding chart:

`ball (y j) (2 * ρ j) ⊆ (ψ j).toFun '' PL.openCube (1/2)`.

This margin (`2 * ρ j`) is what makes the chart cover usable in `E5`: an `f`-image of diameter
`< λ` lying inside the ball of radius `ρ j` is then well inside the chart, so that the
clause `f '' simp (τ₀ ∪ τ₁) ⊆ ψ.toFun '' openCube (1/2)` of `L7c` can be produced from a
Lebesgue number.

The only topological input is that `(ψ).toFun '' PL.openCube (1/2)` is open in `M`
(`Work.Cells.Connell.cubeChart_isOpen_image_openCube`).
-/

open Set Metric PL

namespace Work.Engulf.Chain.Sub

theorem exists_chart_cover_margin {n : ℕ} {M : Type*} [MetricSpace M] {p : ℕ} {X : Set M}
    {N : ℕ} {Γ : PL.Cx N} {L : Set (PL.E N)} {f : PL.E N → M} {S : Set M}
    (hS : IsCompact S) (hSne : S.Nonempty) (htame : Work.Engulf.Tame n p X Γ L f) :
    ∃ (m : ℕ) (_ : 0 < m) (ψ : Fin m → PL.CubeChart n M) (y : Fin m → M) (ρ : Fin m → ℝ),
      (∀ j, 0 < ρ j) ∧ (∀ j, Work.Engulf.SmoothChart p X Γ L f (ψ j)) ∧
      S ⊆ ⋃ j, Metric.ball (y j) (ρ j) ∧
        ∀ j, Metric.ball (y j) (2 * ρ j) ⊆ (ψ j).toFun '' PL.openCube (1 / 2) := by
  classical
  -- A smoothing chart through every point of `M`.
  choose ψ hψmem hψsm using htame
  -- Shrink each chart image to a ball whose *doubled* radius is still inside the chart.
  have hshrink : ∀ x : M, ∃ r : ℝ, 0 < r ∧
      Metric.ball x (2 * r) ⊆ (ψ x).toFun '' PL.openCube (n := n) (1 / 2) := by
    intro x
    have hopen : IsOpen ((ψ x).toFun '' PL.openCube (n := n) (1 / 2 : ℝ)) :=
      Work.Cells.Connell.cubeChart_isOpen_image_openCube (ψ x) (by norm_num) (by norm_num)
    obtain ⟨ε, hε, hεsub⟩ := (Metric.isOpen_iff.mp hopen) x (hψmem x)
    refine ⟨ε / 2, by linarith, ?_⟩
    have htwo : 2 * (ε / 2) = ε := by ring
    rw [htwo]
    exact hεsub
  choose ρ hρ hρsub using hshrink
  -- The balls `ball x (ρ x)` cover `M`, hence `S`.
  have hcover : S ⊆ ⋃ x, Metric.ball x (ρ x) :=
    fun a _ => mem_iUnion.2 ⟨a, Metric.mem_ball_self (hρ a)⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun x : M => Metric.ball x (ρ x))
    (fun _ => Metric.isOpen_ball) hcover
  -- `S` is nonempty, so the finite subcover is nonempty.
  have htne : t.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    obtain ⟨a, ha⟩ := hSne
    have hmem := ht ha
    rw [hcon] at hmem
    simp at hmem
  -- Reindex the finite subcover by `Fin t.card`.
  let e : ↥t ≃ Fin t.card := Finset.equivFin t
  refine ⟨t.card, Finset.card_pos.mpr htne, fun j => ψ ((e.symm j : ↥t) : M),
    fun j => ((e.symm j : ↥t) : M), fun j => ρ ((e.symm j : ↥t) : M),
    fun j => hρ _, fun j => hψsm _, ?_, fun j => hρsub _⟩
  intro a ha
  obtain ⟨x, hx, hax⟩ := mem_iUnion₂.1 (ht ha)
  refine mem_iUnion.2 ⟨e ⟨x, hx⟩, ?_⟩
  have hy : (((e.symm (e ⟨x, hx⟩) : ↥t)) : M) = x := by
    simp
  dsimp only
  rw [hy]
  exact hax

end Work.Engulf.Chain.Sub
