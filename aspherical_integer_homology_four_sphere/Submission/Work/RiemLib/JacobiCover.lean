import Submission.Work.RiemLib.JacobiCoords
import Submission.Work.RiemLib.JacobiCoordsEq

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
open Submission.JacobiTensor
open Submission.RauchGlobal
open Submission.GExpFlow
open Submission.JacobiCoords
open Submission.BonnetMyers
open Submission.IntrinsicVariation


/-!
# A finite partition carrying `C^∞` chart data of a Jacobi field

`Submission.JacobiCoords.exists_chartCoords_contDiffOn` gives, at every point `s` of a curve which is
smooth near `s`, a chart in which the coordinates of a Jacobi field `J` are `C^∞` on a *symmetric
interval* around `s`.  **`exists_partition_jacobiCoords`** turns this pointwise information on a closed
interval `[a,b]` into a finite partition `a = c 0 < … < c N = b`, a chart `z k` for each piece and a
**room** `[A k, B k] ⊇ [c k, c (k+1)]` such that on each room
* the curve stays in the chart source,
* the global chart coordinates `chartCoords (z k) γ J` are `C^∞`,
* their frame vector is `J`,
* the chart coordinates `chartCoord (z k) γ` of the curve are `C^∞`,
* **the Jacobi equation holds** in the `DtDsP` form of `IsJacobiPiece`.

The construction follows `Submission.ChartPieces.exists_chart_pieces`: a choice function at every point,
a finite subcover of `[a,b]` by the local intervals, and
`Commons.Topology.Order.exists_partition_subordinate_Icc` for the partition; the rooms are the
midpoints of the piece endpoints with the containing interval's endpoints.

This is item 1 of Roadmap §100.8 and §101.6: the per-piece data for the `σ ≤ κ` application.
-/

namespace Submission.JacobiCover

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

/-- **A finite partition of a minimising segment carrying `C^∞` chart data of a Jacobi field. -/
theorem exists_partition_jacobiCoords (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)} {a b ρ₀ : ℝ} (hab : a ≤ b) (hρ₀ : 0 < ρ₀)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (a - ρ₀) (b + ρ₀)))
    (hJ : ∀ s ∈ Icc a b, IsJacobiAt cov γ J s) :
    ∃ (N : ℕ) (c S E A B : ℕ → ℝ) (z : ℕ → M),
      c 0 = a ∧ c N = b ∧ (∀ k < N, c k < c (k + 1)) ∧
      (∀ k < N, S k < c k ∧ c (k + 1) < E k) ∧
      (∀ k < N, A k < c k ∧ c (k + 1) < B k) ∧
      (∀ k < N, Icc (A k) (B k) ⊆ Ioo (S k) (E k)) ∧
      (∀ k < N, Icc (A k) (B k) ⊆ Icc (a - ρ₀) (b + ρ₀)) ∧
      (∀ k < N, ∀ t ∈ Icc (S k) (E k), γ t ∈ (chartAt H (z k)).source) ∧
      (∀ k < N, ContDiffOn ℝ ∞ (chartCoord (I := I) (z k) γ) (Icc (S k) (E k))) ∧
      (∀ k < N, ContDiffOn ℝ ∞ (chartCoords (I := I) (z k) γ J) (Icc (S k) (E k))) ∧
      (∀ k < N, ∀ t ∈ Icc (S k) (E k),
        frameVector (I := I) (z k) (γ t) (chartCoords (I := I) (z k) γ J t) = J t) ∧
      (∀ k < N, ∀ t ∈ Icc (S k) (E k),
        DtDsP cov (z k) (chartCoord (I := I) (z k) γ) (chartCoords (I := I) (z k) γ J)
          (deriv (chartCoord (I := I) (z k) γ)) (deriv (chartCoords (I := I) (z k) γ J)) t
        + chartCurv cov (z k) ((extChartAt I (z k)).symm (chartCoord (I := I) (z k) γ t))
            (chartCoords (I := I) (z k) γ J t) (deriv (chartCoord (I := I) (z k) γ) t) = 0) := by
  classical
  have hloc : ∀ s : ℝ, ∃ (x : M) (η : ℝ), s ∈ Icc a b → 0 < η ∧ η ≤ ρ₀ ∧
      (∀ t ∈ Icc (s - η) (s + η), γ t ∈ (chartAt H x).source) ∧
      ContDiffOn ℝ ∞ (chartCoord (I := I) x γ) (Icc (s - η) (s + η)) ∧
      ContDiffOn ℝ ∞ (chartCoords (I := I) x γ J) (Icc (s - η) (s + η)) ∧
      (∀ t ∈ Icc (s - η) (s + η), frameVector (I := I) x (γ t) (chartCoords (I := I) x γ J t)
        = J t) ∧
      (∀ t ∈ Icc (s - η) (s + η),
        DtDsP cov x (chartCoord (I := I) x γ) (chartCoords (I := I) x γ J)
          (deriv (chartCoord (I := I) x γ)) (deriv (chartCoords (I := I) x γ J)) t
        + chartCurv cov x ((extChartAt I x).symm (chartCoord (I := I) x γ t))
            (chartCoords (I := I) x γ J t) (deriv (chartCoord (I := I) x γ) t) = 0) := by
    intro s
    by_cases hs : s ∈ Icc a b
    · have hγ' : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (s - ρ₀) (s + ρ₀)) := by
        refine hγ.mono ?_
        intro t ht
        exact ⟨by linarith [ht.1, hs.1], by linarith [ht.2, hs.2]⟩
      obtain ⟨x, η, hconj⟩ :=
        Submission.JacobiCoordsEq.exists_chartCoords_contDiffOn_eq (cov := cov) htor hρ₀ hγ' (hJ s hs)
      exact ⟨x, η, fun _ => hconj⟩
    · exact ⟨γ a, 1, fun h => absurd h hs⟩
  choose x η hη using hloc
  have hcov : Icc a b ⊆ ⋃ s : {s : ℝ // s ∈ Icc a b}, Ioo ((s : ℝ) - η s) ((s : ℝ) + η s) := by
    intro t ht
    refine Set.mem_iUnion.mpr ⟨⟨t, ht⟩, ?_⟩
    simp only [Set.mem_Ioo]
    exact ⟨by linarith [(hη t ht).1], by linarith [(hη t ht).1]⟩
  obtain ⟨sf, hsf⟩ := isCompact_Icc.elim_finite_subcover
    (fun s : {s : ℝ // s ∈ Icc a b} => Ioo ((s : ℝ) - η s) ((s : ℝ) + η s))
    (fun _ => isOpen_Ioo) hcov
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
  have hchain : ∀ l ≤ N, ∀ k ≤ l, c k ≤ c l := by
    intro l hl k hkl
    induction l with
    | zero =>
      simp only [Nat.le_zero] at hkl
      rw [hkl]
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hkl with h | h
      · rw [h]
      · have hj : j < N := Nat.lt_of_succ_le hl
        exact le_trans (ih (le_of_lt hj) (Nat.lt_succ_iff.mp h)) (le_of_lt (hmono j hj))
  set S : ℕ → ℝ := fun k => ((w k).val.val : ℝ) - η (w k).val with hSdef
  set E : ℕ → ℝ := fun k => ((w k).val.val : ℝ) + η (w k).val with hEdef
  set A : ℕ → ℝ := fun k => (c k + ((w k).val.val : ℝ) - η (w k).val) / 2 with hAdef
  set B : ℕ → ℝ := fun k => (c (k + 1) + ((w k).val.val : ℝ) + η (w k).val) / 2 with hBdef
  set Z : ℕ → M := fun k => x (w k).val.val with hZdef
  have hS_exp : ∀ k, S k = ((w k).val.val : ℝ) - η (w k).val := fun k => rfl
  have hE_exp : ∀ k, E k = ((w k).val.val : ℝ) + η (w k).val := fun k => rfl
  have hA_exp : ∀ k, A k = (c k + ((w k).val.val : ℝ) - η (w k).val) / 2 := fun k => rfl
  have hB_exp : ∀ k, B k = (c (k + 1) + ((w k).val.val : ℝ) + η (w k).val) / 2 := fun k => rfl
  refine ⟨N, c, S, E, A, B, Z, hc0, hcN, hmono, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the local interval contains the piece
    intro k hk
    have hconv := hw k hk
    have h1 : S k < c k :=
      (Set.mem_Ioo.mp (hconv (left_mem_Icc.mpr (hmono k hk).le))).1
    have h2 : c (k + 1) < E k :=
      (Set.mem_Ioo.mp (hconv (right_mem_Icc.mpr (hmono k hk).le))).2
    exact ⟨h1, h2⟩
  · -- the room contains the piece
    intro k hk
    have hconv := hw k hk
    have h1 : S k < c k :=
      (Set.mem_Ioo.mp (hconv (left_mem_Icc.mpr (hmono k hk).le))).1
    have h2 : c (k + 1) < E k :=
      (Set.mem_Ioo.mp (hconv (right_mem_Icc.mpr (hmono k hk).le))).2
    have hA := hA_exp k
    have hB := hB_exp k
    constructor <;> linarith
  · -- the room is inside the local interval
    intro k hk
    have hconv := hw k hk
    have h1 : S k < c k :=
      (Set.mem_Ioo.mp (hconv (left_mem_Icc.mpr (hmono k hk).le))).1
    have h2 : c (k + 1) < E k :=
      (Set.mem_Ioo.mp (hconv (right_mem_Icc.mpr (hmono k hk).le))).2
    intro t ht
    have hA := hA_exp k
    have hB := hB_exp k
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · -- the room is inside `[a - ρ₀, b + ρ₀]`
    intro k hk
    have hconv := hw k hk
    have h1 : S k < c k :=
      (Set.mem_Ioo.mp (hconv (left_mem_Icc.mpr (hmono k hk).le))).1
    have h2 : c (k + 1) < E k :=
      (Set.mem_Ioo.mp (hconv (right_mem_Icc.mpr (hmono k hk).le))).2
    have hmem : (w k).val.val ∈ Icc a b := (w k).val.property
    have hηρ : η (w k).val ≤ ρ₀ := (hη (w k).val hmem).2.1
    have hck : a ≤ c k := hc0 ▸ hchain k (le_of_lt hk) 0 (Nat.zero_le k)
    have hck1 : c (k + 1) ≤ b := hcN ▸ hchain N le_rfl (k + 1) (Nat.succ_le_of_lt hk)
    have hSk : a - ρ₀ ≤ S k := by rw [hS_exp k]; linarith [hmem.1, hηρ]
    have hEk : E k ≤ b + ρ₀ := by rw [hE_exp k]; linarith [hmem.2, hηρ]
    have hA := hA_exp k
    have hB := hB_exp k
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · -- the source condition
    intro k hk t ht
    exact (hη (w k).val (w k).val.property).2.2.1 t ht
  · -- `C^∞` of the curve's chart coordinates
    intro k hk
    exact (hη (w k).val (w k).val.property).2.2.2.1
  · -- `C^∞` of the field's chart coordinates
    intro k hk
    exact (hη (w k).val (w k).val.property).2.2.2.2.1
  · -- the identification of the field
    intro k hk t ht
    exact (hη (w k).val (w k).val.property).2.2.2.2.2.1 t ht
  · -- the Jacobi equation
    intro k hk t ht
    exact (hη (w k).val (w k).val.property).2.2.2.2.2.2 t ht

end

end Submission.JacobiCover
