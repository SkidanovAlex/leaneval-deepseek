import Mathlib
import Submission.Lib.Unif2.Work.Topology.Engulf.exists_isOpen_isConnected_isCompact_closure_no_bounded_component

/-!
# The Runge exhaustion of a non-compact Riemann surface

The classical Behnke--Stein / Mittag--Leffler induction on an open Riemann surface runs along an
exhaustion `D 0 ⊆ D 1 ⊆ ⋯` by relatively compact connected open sets whose complements have no
*relatively compact* connected component — the Runge condition that makes the approximation theorem
"extension of holomorphic functions across a bigger domain" true.

The one-step ingredient is already proved in this workspace:
`Work.Topology.Engulf.exists_isOpen_isConnected_isCompact_closure_no_bounded_component` produces, for
any compact `K`, an open connected relatively compact `Ω ⊇ K` with no relatively compact components
in `Ωᶜ`.  Iterating that lemma along a compact exhaustion `K n` of `X` (available because `X` is
σ-compact) gives the exhaustion below.
-/

open Set
open scoped Topology Manifold

set_option linter.unusedVariables false

noncomputable section

namespace Work.Analysis.RiemannSurface

/-- **The Runge exhaustion of a non-compact Riemann surface.**  There is an increasing sequence of
relatively compact connected open sets `D n` covering `X`, containing `x₀`, with `closure (D n) ⊆
D (n+1)`, and such that the complement of each `D n` has no relatively compact connected component.
This is the exhaustion along which the Behnke--Stein/Mittag--Leffler induction runs; it is obtained
by iterating `Work.Topology.Engulf.exists_isOpen_isConnected_isCompact_closure_no_bounded_component`
along a compact exhaustion of `X` (using `SigmaCompactSpace.exists_compact_covering` for coverage). -/
theorem runge_exhaustion {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [LocallyCompactSpace X] [LocallyConnectedSpace X] [LocallyPathConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] (hX : ¬ CompactSpace X) (x₀ : X) :
    ∃ D : ℕ → Set X,
      (∀ n, IsOpen (D n)) ∧ (∀ n, IsConnected (D n)) ∧ (∀ n, IsCompact (closure (D n))) ∧
        (∀ n, closure (D n) ⊆ D (n + 1)) ∧ x₀ ∈ D 0 ∧ (⋃ n, D n) = (Set.univ : Set X) ∧
        (∀ n (x : X), x ∉ D n → ¬ IsCompact (closure (connectedComponentIn (D n)ᶜ x))) := by
  classical
  obtain ⟨K, hKc, hKcov⟩ := SigmaCompactSpace.exists_compact_covering (X := X)
  -- the one-step engulfing property
  have hstep : ∀ A : Set X, IsCompact A → ∃ Ω : Set X,
      IsOpen Ω ∧ IsConnected Ω ∧ IsCompact (closure Ω) ∧ A ⊆ Ω ∧
        ∀ x ∉ Ω, ¬ IsCompact (closure (connectedComponentIn Ωᶜ x)) :=
    fun A hA => Work.Topology.Engulf.exists_isOpen_isConnected_isCompact_closure_no_bounded_component
      (X := X) hA
  let F : Set X → Set X :=
    fun A => if h : IsCompact A then Classical.choose (hstep A h) else Set.univ
  have hF : ∀ A : Set X, IsCompact A → IsOpen (F A) ∧ IsConnected (F A) ∧
      IsCompact (closure (F A)) ∧ A ⊆ F A ∧
        ∀ x ∉ F A, ¬ IsCompact (closure (connectedComponentIn (F A)ᶜ x)) := by
    intro A hA
    have := Classical.choose_spec (hstep A hA)
    simpa only [F, dif_pos hA] using this
  let D : ℕ → Set X := Nat.rec (F ({x₀} ∪ K 0)) (fun n A => F (closure A ∪ K n.succ))
  have hDzero : D 0 = F ({x₀} ∪ K 0) := rfl
  have hDsucc : ∀ n, D n.succ = F (closure (D n) ∪ K n.succ) := fun n => rfl
  have hbase : IsCompact ({x₀} ∪ K 0) := isCompact_singleton.union (hKc 0)
  -- the four structural properties
  have hcomp : ∀ n, IsCompact (closure (D n)) := by
    intro n
    induction n with
    | zero => rw [hDzero]; exact (hF ({x₀} ∪ K 0) hbase).2.2.1
    | succ n ih => rw [hDsucc n]; exact (hF (closure (D n) ∪ K n.succ) (ih.union (hKc n.succ))).2.2.1
  have hopen : ∀ n, IsOpen (D n) := by
    intro n
    cases n with
    | zero => rw [hDzero]; exact (hF ({x₀} ∪ K 0) hbase).1
    | succ n => rw [hDsucc n]; exact (hF (closure (D n) ∪ K n.succ) (hcomp n |>.union (hKc n.succ))).1
  have hconn : ∀ n, IsConnected (D n) := by
    intro n
    cases n with
    | zero => rw [hDzero]; exact (hF ({x₀} ∪ K 0) hbase).2.1
    | succ n => rw [hDsucc n]
                exact (hF (closure (D n) ∪ K n.succ) (hcomp n |>.union (hKc n.succ))).2.1
  have hnc : ∀ n, ∀ x ∉ D n, ¬ IsCompact (closure (connectedComponentIn (D n)ᶜ x)) := by
    intro n
    cases n with
    | zero => rw [hDzero]; exact (hF ({x₀} ∪ K 0) hbase).2.2.2.2
    | succ n => rw [hDsucc n]
                exact (hF (closure (D n) ∪ K n.succ) (hcomp n |>.union (hKc n.succ))).2.2.2.2
  have hsub : ∀ n, closure (D n) ⊆ D n.succ := by
    intro n
    rw [hDsucc n]
    exact subset_union_left.trans (hF (closure (D n) ∪ K n.succ)
      (hcomp n |>.union (hKc n.succ))).2.2.2.1
  have hx0 : x₀ ∈ D 0 := by
    rw [hDzero]
    exact (hF ({x₀} ∪ K 0) hbase).2.2.2.1 (mem_union_left _ (mem_singleton x₀))
  have hKmem : ∀ n, K n ⊆ D n := by
    intro n
    cases n with
    | zero =>
      intro x hx
      rw [hDzero]
      exact (hF ({x₀} ∪ K 0) hbase).2.2.2.1 (mem_union_right _ hx)
    | succ n =>
      intro x hx
      rw [hDsucc n]
      exact (hF (closure (D n) ∪ K n.succ) (hcomp n |>.union (hKc n.succ))).2.2.2.1
        (mem_union_right _ hx)
  have hcover : (⋃ n, D n) = (Set.univ : Set X) := by
    ext x
    constructor
    · intro _; exact mem_univ x
    · intro _
      have hx : x ∈ (⋃ n, K n) := by rw [hKcov]; exact mem_univ x
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨n, hKmem n hn⟩
  refine ⟨D, hopen, hconn, hcomp, fun n => ?_, hx0, hcover, fun n => hnc n⟩
  intro x hx
  simpa only [Nat.succ_eq_add_one] using hsub n hx

end Work.Analysis.RiemannSurface
