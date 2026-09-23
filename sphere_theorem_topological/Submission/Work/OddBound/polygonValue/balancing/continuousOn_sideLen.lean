import Mathlib
import Submission.Distance
import Submission.EDist
import Submission.Work.OddBound.polygonValue.balancing.Defs
import Submission.Work.OddBound.polygon.riemannianDist_eq_toReal

/-!
# Continuity of the side lengths of the balanced broken-geodesic family

The length of the `i`-th side of the slice `τ` of a polygon family `w` is the Riemannian distance of
two consecutive vertices of that slice,

`sideLen p w τ i = d (gonVert p (w τ) i) (gonVert p (w τ) (i+1))`.

Continuity of `τ ↦ w τ` is *not* assumed.  Instead the hypothesis is that the side curves `S i · τ`
are jointly continuous in `(r, τ)` on the unit square and that at `r = 0` and `r = 1` they sit at the
vertices of the slice.  Reading the joint continuity on the lines `r = 0` and `r = 1` gives
continuity of `τ ↦ gonVert p (w τ) m` for every `m`, and the Riemannian distance of two continuous
families is continuous: on the diagonal the extended Riemannian distance vanishes, hence is
`toReal`-continuous there (`riemannianDist_eq_toReal`), and the triangle inequality
(`Submission.Distance.riemannianDist_triangle`, with the existence of piecewise smooth paths on a
path-connected manifold) converts that into continuity along two families.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set Metric Filter

namespace Work.OddBound.polygonValue.balancing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
  [IsManifold I (WithTop.some (⊤ : ENat)) M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I (WithTop.some (⊤ : ENat)) E
    (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]

noncomputable section

/-! ## 1. Elementary properties of the Riemannian distance -/

/-- The Riemannian distance of this development is symmetric: the extended Riemannian distance is
symmetric and `toReal` is a function of its value alone. -/
theorem riemannianDist_comm_toReal (x y : M) :
    Submission.Distance.riemannianDist (I := I) x y
      = Submission.Distance.riemannianDist (I := I) y x := by
  rw [Work.OddBound.polygon.riemannianDist_eq_toReal (I := I) x y,
    Work.OddBound.polygon.riemannianDist_eq_toReal (I := I) y x,
    Manifold.riemannianEDist_comm]

/-- The triangle inequality for the Riemannian distance, unconditionally on a path-connected
manifold (the nonemptiness of the set of lengths of piecewise smooth paths provides the two
nonemptiness hypotheses of `Submission.Distance.riemannianDist_triangle`). -/
theorem riemannianDist_triangle_pathConnected (x y z : M) :
    Submission.Distance.riemannianDist (I := I) x z
      ≤ Submission.Distance.riemannianDist (I := I) x y
        + Submission.Distance.riemannianDist (I := I) y z :=
  Submission.Distance.riemannianDist_triangle (x := x) (y := y) (z := z)
    (Work.OddBound.polygon.PwLengthSet_nonempty (I := I) x y)
    (Work.OddBound.polygon.PwLengthSet_nonempty (I := I) y z)

/-! ## 2. Continuity of the Riemannian distance along convergent families -/

/-- **Joint continuity of the Riemannian distance along two convergent families of points**, at a
pair of points at finite extended distance.  The finiteness hypothesis is what `toReal`-continuity
needs; it holds in particular on the diagonal, where the extended distance vanishes. -/
theorem tendsto_riemannianDist_of_tendsto_ne_top {α : Type*} {l : Filter α} {q r : α → M} {x y : M}
    (hfin : Manifold.riemannianEDist I x y ≠ ⊤)
    (hq : Filter.Tendsto q l (𝓝 x)) (hr : Filter.Tendsto r l (𝓝 y)) :
    Filter.Tendsto (fun a : α => Submission.Distance.riemannianDist (I := I) (q a) (r a)) l
      (𝓝 (Submission.Distance.riemannianDist (I := I) x y)) := by
  haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have hcont : Continuous fun p : M × M => Manifold.riemannianEDist I p.1 p.2 :=
    continuous_edist.congr fun p => Submission.EDist.edist_eq_riemannianEDist (I := I) p.1 p.2
  have hpq : Filter.Tendsto (fun a : α => (q a, r a)) l (𝓝 (x, y)) := by
    rw [nhds_prod_eq]; exact hq.prodMk hr
  have hcomp : Filter.Tendsto (fun a : α => Manifold.riemannianEDist I (q a) (r a)) l
      (𝓝 (Manifold.riemannianEDist I x y)) := by
    have h := (hcont.tendsto (x, y)).comp hpq
    rw [Function.comp_def] at h
    exact h
  have h3 : Filter.Tendsto (fun a : α => (Manifold.riemannianEDist I (q a) (r a)).toReal) l
      (𝓝 ((Manifold.riemannianEDist I x y).toReal)) := by
    have h := (ENNReal.continuousAt_toReal hfin).tendsto.comp hcomp
    rw [Function.comp_def] at h
    exact h
  simpa only [Work.OddBound.polygon.riemannianDist_eq_toReal] using h3

/-- **Continuity of the Riemannian distance between two continuous families of points** on the unit
interval: the diagonal is continuous (the extended distance vanishes there), and the triangle
inequality bounds the variation of `d (A τ) (B τ)` by `d (A τ) (A τ₀) + d (B τ₀) (B τ)`. -/
theorem continuousOn_riemannianDist_pair {A B : ℝ → M}
    (hA : ContinuousOn A (Set.Icc (0 : ℝ) 1))
    (hB : ContinuousOn B (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun τ : ℝ => Submission.Distance.riemannianDist (I := I) (A τ) (B τ))
      (Set.Icc (0 : ℝ) 1) := by
  intro τ₀ hτ₀
  have hA' : Filter.Tendsto A (𝓝[Set.Icc (0 : ℝ) 1] τ₀) (𝓝 (A τ₀)) :=
    hA.continuousWithinAt hτ₀
  have hB' : Filter.Tendsto B (𝓝[Set.Icc (0 : ℝ) 1] τ₀) (𝓝 (B τ₀)) :=
    hB.continuousWithinAt hτ₀
  have hdA : Filter.Tendsto
      (fun τ : ℝ => Submission.Distance.riemannianDist (I := I) (A τ) (A τ₀))
      (𝓝[Set.Icc (0 : ℝ) 1] τ₀) (𝓝 0) := by
    have hfin : Manifold.riemannianEDist I (A τ₀) (A τ₀) ≠ ⊤ := by
      rw [Manifold.riemannianEDist_self]
      exact ENNReal.zero_ne_top
    have h := tendsto_riemannianDist_of_tendsto_ne_top (I := I) (q := A)
      (r := fun _ : ℝ => A τ₀) (x := A τ₀) (y := A τ₀) hfin hA' tendsto_const_nhds
    simpa [Submission.Distance.riemannianDist_self] using h
  have hdB : Filter.Tendsto
      (fun τ : ℝ => Submission.Distance.riemannianDist (I := I) (B τ₀) (B τ))
      (𝓝[Set.Icc (0 : ℝ) 1] τ₀) (𝓝 0) := by
    have hfin : Manifold.riemannianEDist I (B τ₀) (B τ₀) ≠ ⊤ := by
      rw [Manifold.riemannianEDist_self]
      exact ENNReal.zero_ne_top
    have h := tendsto_riemannianDist_of_tendsto_ne_top (I := I) (q := fun _ : ℝ => B τ₀)
      (r := B) (x := B τ₀) (y := B τ₀) hfin tendsto_const_nhds hB'
    simpa [Submission.Distance.riemannianDist_self] using h
  have hsum : Filter.Tendsto
      (fun τ : ℝ => Submission.Distance.riemannianDist (I := I) (A τ) (A τ₀)
        + Submission.Distance.riemannianDist (I := I) (B τ₀) (B τ))
      (𝓝[Set.Icc (0 : ℝ) 1] τ₀) (𝓝 0) := by
    have h := hdA.add hdB
    simpa using h
  have hbound : ∀ τ : ℝ, ‖Submission.Distance.riemannianDist (I := I) (A τ) (B τ)
      - Submission.Distance.riemannianDist (I := I) (A τ₀) (B τ₀)‖
      ≤ Submission.Distance.riemannianDist (I := I) (A τ) (A τ₀)
        + Submission.Distance.riemannianDist (I := I) (B τ₀) (B τ) := by
    intro τ
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have h1 := riemannianDist_triangle_pathConnected (I := I) (A τ₀) (A τ) (B τ)
      have h2 := riemannianDist_triangle_pathConnected (I := I) (A τ₀) (B τ) (B τ₀)
      have hs1 := riemannianDist_comm_toReal (I := I) (A τ₀) (A τ)
      have hs2 := riemannianDist_comm_toReal (I := I) (B τ) (B τ₀)
      linarith
    · have h1 := riemannianDist_triangle_pathConnected (I := I) (A τ) (A τ₀) (B τ₀)
      have h2 := riemannianDist_triangle_pathConnected (I := I) (A τ) (B τ₀) (B τ)
      have hs := riemannianDist_comm_toReal (I := I) (B τ₀) (B τ)
      linarith
  have hmain : Filter.Tendsto (fun τ : ℝ =>
      Submission.Distance.riemannianDist (I := I) (A τ) (B τ)
        - Submission.Distance.riemannianDist (I := I) (A τ₀) (B τ₀))
      (𝓝[Set.Icc (0 : ℝ) 1] τ₀) (𝓝 0) :=
    squeeze_zero_norm hbound hsum
  have hfin : Filter.Tendsto
      (fun τ : ℝ => Submission.Distance.riemannianDist (I := I) (A τ) (B τ))
      (𝓝[Set.Icc (0 : ℝ) 1] τ₀)
      (𝓝 (Submission.Distance.riemannianDist (I := I) (A τ₀) (B τ₀))) := by
    simpa using hmain.add_const (Submission.Distance.riemannianDist (I := I) (A τ₀) (B τ₀))
  exact hfin

/-! ## 3. Continuity of the vertices, from the side curves -/

/-- **Continuity of the vertices of a polygon family.**  The vertex `m` of the slice `τ` is the
`r = 0` endpoint of a side curve (or the base point, if `m ≥ N`), so its continuity follows from the
joint continuity of the side curves on the unit square. -/
theorem continuousOn_gonVert_of_continuousOn
    {p : M} {N : ℕ} {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M}
    (hN : 0 < N)
    (hScont : ∀ i : Fin N, ContinuousOn (fun u : ℝ × ℝ => S i u.1 u.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ)) (m : ℕ) :
    ContinuousOn (fun τ : ℝ => Work.OddBound.gonVert p (w τ) m) (Set.Icc (0 : ℝ) 1) := by
  rcases lt_or_ge m N with hm | hm
  · have hcomp : ContinuousOn (fun τ : ℝ => S ⟨m, hm⟩ 0 τ) (Set.Icc (0 : ℝ) 1) := by
      have h := (hScont ⟨m, hm⟩).comp
        ((continuous_const (y := (0 : ℝ))).prodMk continuous_id).continuousOn
        (fun τ hτ => by
          simp only [Set.mem_prod, Set.mem_Icc]
          exact ⟨⟨le_rfl, zero_le_one⟩, hτ⟩)
      rw [Function.comp_def] at h
      exact h
    refine hcomp.congr fun τ hτ => ?_
    exact (hS0 ⟨m, hm⟩ τ hτ).symm
  · refine (continuousOn_const (c := p)).congr fun τ _ => ?_
    exact Work.OddBound.gonVert_of_le p (w τ) hm

/-! ## 4. The side length is continuous -/

theorem continuousOn_sideLen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I (WithTop.some (⊤ : ENat)) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I (WithTop.some (⊤ : ENat)) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {p : M} {N : ℕ} {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M}
    (hScont : ∀ i : Fin N, ContinuousOn (fun u : ℝ × ℝ => S i u.1 u.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1)) :
    ∀ i : Fin N, ContinuousOn
      (fun τ : ℝ => Work.OddBound.polygonValue.sideLen (I := I) p w τ (i : ℕ))
      (Set.Icc (0 : ℝ) 1) := by
  intro i
  have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le (i : ℕ)) i.2
  have hgoal : ContinuousOn (fun τ : ℝ => Submission.Distance.riemannianDist (I := I)
      (Work.OddBound.gonVert p (w τ) (i : ℕ))
      (Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_riemannianDist_pair (I := I)
      (A := fun τ : ℝ => Work.OddBound.gonVert p (w τ) (i : ℕ))
      (B := fun τ : ℝ => Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
      (continuousOn_gonVert_of_continuousOn hN hScont hS0 (i : ℕ))
      (continuousOn_gonVert_of_continuousOn hN hScont hS0 ((i : ℕ) + 1))
  exact hgoal

end

end Work.OddBound.polygonValue.balancing
