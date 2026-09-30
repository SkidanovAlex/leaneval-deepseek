import Submission.Work.RiemLib.JacobiCover
import Submission.Work.RiemLib.JacobiGlobal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Rauch
open Submission.RauchGlobal
open Submission.GExpFlow
open Submission.JacobiCoords
open Submission.BonnetMyers
open Submission.IntrinsicVariation
open Submission.JacobiGlobal

/-!
# A finite partition carrying `C^∞` chart data of a *smooth field* along a curve

`Submission.JacobiCover.exists_partition_jacobiCoords` produces such a cover when the field is a
*Jacobi* field (its chart data come from `IsJacobiAt`).  The energy side of `σ ≤ κ`
(Roadmap §101.6 items 2–3) needs the same for an *arbitrary* field `V` that is smooth along the
curve (`∀ s, SmoothAlongAt γ V s`), because the family there is
`Φ(σ,t) = GExp(γ t)(σ • V t)` with `V` a bump field or a combination of Jacobi fields.

The chart attached to each piece here is the chart at the *base point* `γ s` of the local datum,
which makes the local step trivial: `SmoothAlongAt γ V s` is *by definition* the `C^∞` statement of
the chart-`γ s` coordinates of `V` on a neighbourhood of `s`.
-/

namespace Submission.SmoothFieldCover

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **A finite partition of `[a,b]` carrying `C^∞` chart data of a smooth field along the curve.**
For each piece `[c k, c (k+1)]` there is a chart `z k` and a *local interval* `Icc (S k) (E k)`
with `S k < c k < c (k+1) < E k` on which the curve stays in the chart source, the curve's chart
coordinates and the field's chart coordinates are `C^∞`, and the frame vector of the coordinates is
the field. -/
theorem exists_partition_smoothField
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (a - 1) (b + 1)))
    (hV : ∀ s ∈ Icc a b, SmoothAlongAt (I := I) γ V s) :
    ∃ (N : ℕ) (c S E : ℕ → ℝ) (z : ℕ → M),
      c 0 = a ∧ c N = b ∧ (∀ k < N, c k < c (k + 1)) ∧
      (∀ k < N, S k < c k ∧ c (k + 1) < E k) ∧
      (∀ k < N, ∀ t ∈ Icc (S k) (E k), γ t ∈ (chartAt H (z k)).source) ∧
      (∀ k < N, ContDiffOn ℝ ∞ (chartCoord (I := I) (z k) γ) (Icc (S k) (E k))) ∧
      (∀ k < N, ContDiffOn ℝ ∞ (chartCoords (I := I) (z k) γ V) (Icc (S k) (E k))) ∧
      (∀ k < N, ∀ t ∈ Icc (S k) (E k),
        frameVector (I := I) (z k) (γ t) (chartCoords (I := I) (z k) γ V t) = V t) ∧
      (∀ k < N, Icc (S k) (E k) ⊆ Ioo (a - 1) (b + 1)) := by
  classical
  -- the local datum at every point of `[a,b]`
  have hloc : ∀ s : ℝ, ∃ (x : M) (η : ℝ), s ∈ Icc a b → 0 < η ∧
      (∀ t ∈ Icc (s - η) (s + η), γ t ∈ (chartAt H x).source) ∧
      ContDiffOn ℝ ∞ (chartCoord (I := I) x γ) (Icc (s - η) (s + η)) ∧
      ContDiffOn ℝ ∞ (chartCoords (I := I) x γ V) (Icc (s - η) (s + η)) ∧
      (∀ t ∈ Icc (s - η) (s + η), frameVector (I := I) x (γ t) (chartCoords (I := I) x γ V t)
        = V t) ∧
      Icc (s - η) (s + η) ⊆ Ioo (a - 1) (b + 1) := by
    intro s
    by_cases hs : s ∈ Icc a b
    · obtain ⟨U, hUopen, hsU, hUsrc, hUcd⟩ := hV s hs
      obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hsU)
      set η : ℝ := min r 1 / 2 with hηdef
      have hη : 0 < η := by rw [hηdef]; positivity
      have hηr : η < r := by
        rw [hηdef]; have h : min r 1 ≤ r := min_le_left _ _; linarith
      have hsub : Icc (s - η) (s + η) ⊆ U := by
        intro t ht
        refine hrsub ?_
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [ht.1, hηr], by linarith [ht.2, hηr]⟩
      have hη1 : η < 1 := by
        rw [hηdef]; have h : min r 1 ≤ 1 := min_le_right _ _; linarith
      have hsubI : Icc (s - η) (s + η) ⊆ Ioo (a - 1) (b + 1) := by
        intro t ht
        exact ⟨by linarith [ht.1, hs.1], by linarith [ht.2, hs.2]⟩
      refine ⟨γ s, η, fun _ => ⟨hη, ?_, ?_, ?_, ?_, hsubI⟩⟩
      · intro t ht
        exact hUsrc t (hsub ht)
      · refine (Submission.SecondVarGlobal.contDiffOn_chartCoord (I := I) (z₀ := γ s)
          (hγ.mono hsubI) (fun t ht => hUsrc t (hsub ht))).mono (Subset.refl _)
      · exact hUcd.mono hsub
      · intro t ht
        exact frameVector_chartCoords (I := I) (hUsrc t (hsub ht))
    · exact ⟨γ a, (1 : ℝ), fun h => False.elim (absurd h hs)⟩
  choose x η hη using hloc
  -- the induced open cover of `[a,b]`
  have hcov : Icc a b ⊆ ⋃ s : {s : ℝ // s ∈ Icc a b}, Ioo ((s : ℝ) - η s) ((s : ℝ) + η s) := by
    intro t ht
    refine Set.mem_iUnion.mpr ⟨⟨t, ht⟩, ?_⟩
    simp only [Set.mem_Ioo]
    exact ⟨by linarith [(hη t ht).1], by linarith [(hη t ht).1]⟩
  obtain ⟨sf, hsf⟩ := isCompact_Icc.elim_finite_subcover
    (fun s : {s : ℝ // s ∈ Icc a b} => Ioo ((s : ℝ) - η s) ((s : ℝ) + η s))
    (fun _ => isOpen_Ioo) hcov
  -- the subordinate partition
  obtain ⟨N, c, hc0, hcN, hmono, hpiece⟩ :=
    Commons.Topology.Order.exists_partition_subordinate_Icc
      (U := fun i : {s : {s : ℝ // s ∈ Icc a b} // s ∈ sf} =>
        Ioo (((i : {s : ℝ // s ∈ Icc a b}) : ℝ) - η i) (((i : {s : ℝ // s ∈ Icc a b}) : ℝ) + η i))
      (fun _ => isOpen_Ioo) hab (by
        intro t ht
        obtain ⟨s, hst, hts⟩ := Set.mem_iUnion₂.mp (hsf ht)
        exact Set.mem_iUnion.mpr ⟨⟨s, hst⟩, hts⟩)
  have hex : ∀ k : ℕ, ∃ i : {s : {s : ℝ // s ∈ Icc a b} // s ∈ sf},
      k < N → Icc (c k) (c (k + 1)) ⊆
        Ioo (((i : {s : ℝ // s ∈ Icc a b}) : ℝ) - η i)
          (((i : {s : ℝ // s ∈ Icc a b}) : ℝ) + η i) := by
    intro k
    by_cases hk : k < N
    · obtain ⟨i, hi⟩ := hpiece k hk
      exact ⟨i, fun _ => hi⟩
    · have hsne : sf.Nonempty := by
        obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.mp (hsf (left_mem_Icc.mpr hab : a ∈ Icc a b))
        exact ⟨i, hi⟩
      obtain ⟨t₀, ht₀⟩ := hsne
      exact ⟨⟨t₀, ht₀⟩, fun h => absurd h hk⟩
  choose w hw using hex
  refine ⟨N, c, fun k => ((w k).val.val : ℝ) - η (w k).val,
    fun k => ((w k).val.val : ℝ) + η (w k).val, fun k => x (w k).val.val, hc0, hcN, hmono, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · -- the local interval contains the piece
    intro k hk
    have h := hw k hk
    exact ⟨(Set.mem_Ioo.mp (h (left_mem_Icc.mpr (hmono k hk).le))).1,
      (Set.mem_Ioo.mp (h (right_mem_Icc.mpr (hmono k hk).le))).2⟩
  · -- the source condition
    intro k hk t ht
    exact (hη (w k).val (w k).val.property).2.1 t ht
  · -- `C^∞` of the curve's chart coordinates
    intro k hk
    exact (hη (w k).val (w k).val.property).2.2.1
  · -- `C^∞` of the field's chart coordinates
    intro k hk
    exact (hη (w k).val (w k).val.property).2.2.2.1
  · -- the identification of the field
    intro k hk t ht
    exact (hη (w k).val (w k).val.property).2.2.2.2.1 t ht
  · -- the rooms are inside the window `(a-1, b+1)`
    intro k hk
    exact (hη (w k).val (w k).val.property).2.2.2.2.2

end

end Submission.SmoothFieldCover
