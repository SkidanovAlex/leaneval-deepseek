/-
  Area E7, BV Lemma 8 ("effective fibre cutting"): the critical-point witness over a *closed*
  fibre (the input `Work.WilE7.CritWitness` of `FiberCutCover.lean`, "Claim A" of
  `NOTES_S13_fiber_cut.md`).

  If `x` is not in the projection of the fibrewise frontier of a `Good` stratum `S`, then the
  fibre `K = fiber S.X.set x` is closed in `ℝ^q`, hence compact (it sits in the cube).  Pick a
  connected component `C` of `K` on which some fibre coordinate `y_l` is non-constant
  (`component_variation`), let `y*` be a point of `C` where `y_l` is maximal.  Since the `Good`
  germ of `K` at `(x, y*)` fills a neighbourhood of `y*` inside `K`
  (`fiber_germ_subset_component`), `y*` is a *local* maximum of `y_l` on `K`, so
  `critSet_of_localMax` puts `z = (x, y*)` into `critSet S l`; and a point of `C` with a smaller
  `y_l`-value is the required witness.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.WilE7.critSet_of_localMax
import Submission.Work.WilE7.fiber_germ_subset_component
import Submission.Work.WilE7.Wit.component_variation

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped Topology

namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-! ## Elementary fibre facts -/

/-- The fibre of `X` over a base point outside the projection of the fibrewise frontier is
closed (it is the fibre of a closed condition: a limit of fibre points whose value is not in `X`
would exhibit `x` as the projection of a frontier point). -/
private theorem cw_fiber_isClosed {p q : ℕ} (X : Set (Fin (p + q) → ℝ)) (x : Fin p → ℝ)
    (h : x ∉ projFirst p q '' (fiberClosure X \ X)) : IsClosed (fiber X x) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  change Fin.append x y ∈ X
  by_contra hyX
  refine h ⟨Fin.append x y, ⟨?_, hyX⟩, ?_⟩
  · show projSnd p q (Fin.append x y) ∈ closure (fiber X (projFirst p q (Fin.append x y)))
    rw [show projFirst p q (Fin.append x y) = x from by
          funext i; simp [projFirst, Fin.append_left],
        show projSnd p q (Fin.append x y) = y from by
          funext i; simp [projSnd, Fin.append_right]]
    exact hy
  · funext i
    simp [projFirst, Fin.append_left]

/-- The cube as a product of closed intervals. -/
private theorem cw_cubeC_eq (q : ℕ) :
    cubeC q = Set.univ.pi (fun _ : Fin q => Set.Icc (-1 : ℝ) 1) := by
  ext y
  simp only [cubeC, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
    abs_le]

/-- The fibre of a stratum over a base point lies in the cube. -/
private theorem cw_fiber_subset_cubeC {p q : ℕ} (S : Stratum p q) (x : Fin p → ℝ) :
    fiber S.X.set x ⊆ cubeC q := by
  intro y hy
  have hy1 : Fin.append x y ∈ cubeC (p + q) := by
    have hy' : Fin.append x y ∈ S.X.set := hy
    rw [SemiPf.set, Set.mem_ofPred_eq] at hy'
    exact hy'.1
  intro d
  have h2 : |(Fin.append x y) (Fin.natAdd p d)| ≤ 1 := by
    have hh := hy1
    rw [cubeC, Set.mem_ofPred_eq] at hh
    exact hh (Fin.natAdd p d)
  rwa [Fin.append_right] at h2

/-! ## The fibre-coordinate variation (proved in `Work.WilE7.Wit.component_variation`) -/

private theorem cw_component_variation {p q : ℕ} (S : Stratum p q) (hGood : S.Good)
    (hj : S.j < q) (z : Fin (p + q) → ℝ) (hz : z ∈ S.X.set) :
    ∃ (l : Fin q) (w : Fin q → ℝ),
      w ∈ fiber S.X.set (projFirst p q z) ∧
      w ∈ connectedComponentIn (fiber S.X.set (projFirst p q z)) (projSnd p q z) ∧
      w l ≠ projSnd p q z l :=
  Work.WilE7.Wit.component_variation S hGood hj z hz

/-! ## The main argument, given the variation of a fibre coordinate in a component -/

/-- **The critical-point witness**, with the "some fibre component carries a non-constant fibre
coordinate" input `hcv` taken as a hypothesis (it is `component_variation` below). -/
private theorem cw_witness_of_variation {p q : ℕ} (S : Stratum p q)
    (hGood : S.Good) (x : Fin p → ℝ)
    (hclosed : x ∉ projFirst p q '' (fiberClosure S.X.set \ S.X.set))
    (hcv : ∀ z ∈ S.X.set, ∃ (l : Fin q) (w : Fin q → ℝ),
      w ∈ fiber S.X.set (projFirst p q z) ∧
      w ∈ connectedComponentIn (fiber S.X.set (projFirst p q z)) (projSnd p q z) ∧
      w l ≠ projSnd p q z l) :
    (fiber S.X.set x).Nonempty →
    ∃ (l : Fin q) (z : Fin (p + q) → ℝ), z ∈ (critSet S l).set ∧
      projFirst p q z = x ∧
      ∃ w ∈ fiber S.X.set x,
        w ∈ connectedComponentIn (fiber S.X.set x) (projSnd p q z) ∧
        w l ≠ z (fibDir p q l) := by
  intro hne
  obtain ⟨y₀, hy₀⟩ := hne
  -- the fibre is closed and bounded, hence compact
  have hKclosed : IsClosed (fiber S.X.set x) := cw_fiber_isClosed S.X.set x hclosed
  have hKsub : fiber S.X.set x ⊆ cubeC q := cw_fiber_subset_cubeC S x
  have hKcompact : IsCompact (fiber S.X.set x) := by
    refine (isCompact_univ_pi (fun _ : Fin q => isCompact_Icc (a := (-1 : ℝ)) (b := 1))).of_isClosed_subset
      hKclosed ?_
    simpa [cw_cubeC_eq] using hKsub
  -- a fibre component in which some coordinate is non-constant
  have hz₀ : Fin.append x y₀ ∈ S.X.set := hy₀
  have hpf : projFirst p q (Fin.append x y₀) = x := by
    funext i; simp [projFirst, Fin.append_left]
  have hps : projSnd p q (Fin.append x y₀) = y₀ := by
    funext i; simp [projSnd, Fin.append_right]
  obtain ⟨l, w₁, hw₁fib, hw₁comp, hw₁ne⟩ := hcv (Fin.append x y₀) hz₀
  rw [hpf] at hw₁fib
  rw [hpf, hps] at hw₁comp
  rw [hps] at hw₁ne
  -- the component `C` of `y₀` is closed in the compact fibre, hence compact
  have hCsub : connectedComponentIn (fiber S.X.set x) y₀ ⊆ fiber S.X.set x :=
    connectedComponentIn_subset _ _
  have hCclosed : IsClosed (connectedComponentIn (fiber S.X.set x) y₀) := by
    rw [← closure_subset_iff_isClosed]
    refine (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn ?_ ?_
    · exact subset_closure (mem_connectedComponentIn hy₀)
    · exact (closure_mono hCsub).trans (le_of_eq hKclosed.closure_eq)
  have hCcompact : IsCompact (connectedComponentIn (fiber S.X.set x) y₀) :=
    hKcompact.of_isClosed_subset hCclosed hCsub
  have hCne : (connectedComponentIn (fiber S.X.set x) y₀).Nonempty :=
    ⟨y₀, mem_connectedComponentIn hy₀⟩
  -- a point `y'` of `C` maximising the coordinate `l`
  obtain ⟨y', hy'C, hy'max⟩ :=
    hCcompact.exists_isMaxOn hCne (continuous_apply l).continuousOn
  have hy'fib : y' ∈ fiber S.X.set x := hCsub hy'C
  -- the witness point `z := (x, y')`
  have hzpf : projFirst p q (Fin.append x y') = x := by
    funext i; simp [projFirst, Fin.append_left]
  have hzps : projSnd p q (Fin.append x y') = y' := by
    funext i; simp [projSnd, Fin.append_right]
  have hzval : (Fin.append x y') (fibDir p q l) = y' l := Fin.append_right x y' l
  -- `z` is fibre-critical for the coordinate `l`
  have hcrit : Fin.append x y' ∈ (critSet S l).set := by
    have hzS : Fin.append x y' ∈ S.X.set := hy'fib
    obtain ⟨ε, hεpos, hε⟩ := fiber_germ_subset_component S hGood (Fin.append x y') hzS
    refine critSet_of_localMax S hGood (Fin.append x y') hzS l (Metric.ball y' ε)
      Metric.isOpen_ball ?_ ?_
    · rw [hzps]; exact Metric.mem_ball_self hεpos
    · intro y'' hy''ball hy''fib
      have h1 : y'' ∈ connectedComponentIn (fiber S.X.set (projFirst p q (Fin.append x y')))
          (projSnd p q (Fin.append x y')) :=
        hε y'' (by rw [hzps]; exact Metric.mem_ball.mp hy''ball) hy''fib
      rw [hzpf, hzps] at h1
      rw [← connectedComponentIn_eq hy'C] at h1
      rw [hzps]
      exact isMaxOn_iff.mp hy'max y'' h1
  refine ⟨l, Fin.append x y', hcrit, hzpf, ?_⟩
  -- one of `y₀`, `w₁` (both in `C`) has a strictly smaller `l`-th coordinate than `y'`
  by_cases hl : y₀ l = y' l
  · refine ⟨w₁, hw₁fib, ?_, ?_⟩
    · rw [hzps, ← connectedComponentIn_eq hy'C]
      exact hw₁comp
    · rw [hzval]
      exact fun h => hw₁ne (h.trans hl.symm)
  · refine ⟨y₀, hy₀, ?_, ?_⟩
    · rw [hzps, ← connectedComponentIn_eq hy'C]
      exact mem_connectedComponentIn hy₀
    · rw [hzval]
      exact hl

/-! ## The target -/

theorem exists_critSet_witness_of_closed_fiber {p q : ℕ} (S : WilkiesDesign.E.Stratum p q)
    (hGood : S.Good) (hj : S.j < q) (x : Fin p → ℝ)
    (hclosed : x ∉ WilkiesDesign.E.projFirst p q ''
      (WilkiesDesign.E.fiberClosure S.X.set \ S.X.set)) :
    (WilkiesDesign.E.fiber S.X.set x).Nonempty →
    ∃ (l : Fin q) (z : Fin (p + q) → ℝ), z ∈ (Work.WilE7.critSet S l).set ∧
      WilkiesDesign.E.projFirst p q z = x ∧
      ∃ w ∈ WilkiesDesign.E.fiber S.X.set x,
        w ∈ connectedComponentIn (WilkiesDesign.E.fiber S.X.set x)
          (WilkiesDesign.E.projSnd p q z) ∧
        w l ≠ z (Work.WilE7.fibDir p q l) :=
  cw_witness_of_variation S hGood x hclosed
    (fun z hz => cw_component_variation S hGood hj z hz)

end Work.WilE7
