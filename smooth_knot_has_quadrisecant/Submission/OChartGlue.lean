import Mathlib
import Submission.OChartMonotone
import Submission.OSubChart

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# Milestone-2 (iv) step 6, brick (b) — the chain-gluing local step:
monotone neighbourhoods of transitions

`OChartMonotone.lean` (S101) proved the monotone-coordinate engine
(`interval_inj_continuous_monotone`: an injective continuous real map on an
open interval is strictly monotone, via the fleet commons L28).  This
module applies it to the transitions between the interval charts of `O`
(S98): every transition parameter has a connected open interval
neighbourhood on which the coordinate relabelling is strictly monotone —
the local gluing datum of the ordering along chart chains.

1. **the transition read as a real map** — `oChartTransitionReal` (the
   real value of the transported parameter of `ch₂`), continuous
   (`continuous_oChartTransitionReal`) and injective
   (`injective_oChartTransitionReal`) on the whole transition domain (the
   transition is a homeomorphism and the real coordinate of the target
   chart is injective);
2. **the interval-piece transition map** — `oChartTransitionOnInterval`
   (the transition real value of a parameter of an open piece interval
   lying inside the chart interval and inside the transition domain),
   continuous and injective (`continuous_oChartTransitionOnInterval`,
   `injective_oChartTransitionOnInterval`);
3. **the monotone neighbourhood** — `OChartMonotoneNbhd` (a bundle: an
   open real interval `(lo,hi)` containing the parameter of `x₀`, inside
   the chart interval of `ch₁`, all of whose parameters lie in the
   transition domain, together with the monotonicity clause) and the
   theorem **`exists_oChartMonotoneNbhd`**: every transition parameter has
   such a neighbourhood (shrink the metric ball of the open transition
   domain to stay inside the chart interval, then apply
   `interval_inj_continuous_monotone` to the interval-piece map);
4. **orientation interpretation** — `oChartNbhd_piece_coordinate`: on the
   neighbourhood, the interval-piece value of a parameter is the `ch₂`-
   coordinate of the *same* trisecant class (the transition preserves the
   class, S98), so the monotonicity direction of the neighbourhood
   compares the `ch₁`-order and the `ch₂`-order of the same classes: the
   two interval coordinates agree or are reversed coherently along the
   overlap.

This is the local statement of the chain gluing; the next step assembles
it along the chart chains of `OChartChain.lean` (S99): fixing an
orientation per chart, consecutive overlaps transport the coordinates
monotonically, giving a coherent (possibly reversed, on a Möbius-type
return) global order — the input to the arc/circle classification of the
components and to the once/twice-winding dichotomy.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- The real value of the transition parameter in the target chart. -/
noncomputable def oChartTransitionReal {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    (x : OChartTransitionDomain ch₁ ch₂) : ℝ :=
  (((oChartTransitionTo ch₁ ch₂ x : OChartTransitionDomain ch₂ ch₁) :
      ChartInterval ch₂.lo ch₂.hi) : ℝ)

lemma continuous_oChartTransitionReal {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) :
    Continuous (oChartTransitionReal ch₁ ch₂) := by
  exact continuous_subtype_val.comp
    (continuous_subtype_val.comp (continuous_oChartTransitionTo ch₁ ch₂))

lemma injective_oChartTransitionReal {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) :
    Function.Injective (oChartTransitionReal ch₁ ch₂) := by
  intro x y h
  have hT : oChartTransitionTo ch₁ ch₂ x = oChartTransitionTo ch₁ ch₂ y := by
    apply Subtype.ext
    apply Subtype.ext
    exact h
  exact (oChartTransitionHomeo ch₁ ch₂).injective hT

noncomputable def oChartTransitionOnInterval {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) {lo hi : ℝ}
    (hsub : Set.Ioo lo hi ⊆ Set.Ioo ch₁.lo ch₁.hi)
    (hdom : ∀ u : ChartInterval ch₁.lo ch₁.hi, (u : ℝ) ∈ Set.Ioo lo hi →
      (oChartLift ch₁ u : OpenMobius) ∈ ch₂.W) :
    ChartInterval lo hi → ℝ := fun u =>
  oChartTransitionReal ch₁ ch₂
    ⟨⟨(u : ℝ), hsub u.2⟩, hdom ⟨(u : ℝ), hsub u.2⟩ u.2⟩

lemma continuous_oChartTransitionOnInterval {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) {lo hi : ℝ}
    (hsub : Set.Ioo lo hi ⊆ Set.Ioo ch₁.lo ch₁.hi)
    (hdom : ∀ u : ChartInterval ch₁.lo ch₁.hi, (u : ℝ) ∈ Set.Ioo lo hi →
      (oChartLift ch₁ u : OpenMobius) ∈ ch₂.W) :
    Continuous (oChartTransitionOnInterval ch₁ ch₂ hsub hdom) := by
  let emb : ChartInterval lo hi → ChartInterval ch₁.lo ch₁.hi := fun u => ⟨(u : ℝ), hsub u.2⟩
  have hemb : Continuous emb := by
    dsimp [emb]
    exact Continuous.subtype_mk continuous_subtype_val (fun u => hsub u.2)
  let pkg : ChartInterval lo hi → OChartTransitionDomain ch₁ ch₂ := fun u =>
    ⟨emb u, hdom (emb u) u.2⟩
  have hpkg : Continuous pkg := by
    dsimp [pkg]
    exact Continuous.subtype_mk hemb (fun u => hdom (emb u) u.2)
  have hgoal : oChartTransitionOnInterval ch₁ ch₂ hsub hdom =
      (fun u : ChartInterval lo hi => oChartTransitionReal ch₁ ch₂ (pkg u)) := by
    funext u
    rfl
  rw [hgoal]
  exact (continuous_oChartTransitionReal ch₁ ch₂).comp hpkg

lemma injective_oChartTransitionOnInterval {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) {lo hi : ℝ}
    (hsub : Set.Ioo lo hi ⊆ Set.Ioo ch₁.lo ch₁.hi)
    (hdom : ∀ u : ChartInterval ch₁.lo ch₁.hi, (u : ℝ) ∈ Set.Ioo lo hi →
      (oChartLift ch₁ u : OpenMobius) ∈ ch₂.W) :
    Function.Injective (oChartTransitionOnInterval ch₁ ch₂ hsub hdom) := by
  intro u v h
  have hinjR := injective_oChartTransitionReal ch₁ ch₂
  have hmain : (⟨⟨(u : ℝ), hsub u.2⟩, hdom ⟨(u : ℝ), hsub u.2⟩ u.2⟩ :
        OChartTransitionDomain ch₁ ch₂) =
      (⟨⟨(v : ℝ), hsub v.2⟩, hdom ⟨(v : ℝ), hsub v.2⟩ v.2⟩ :
        OChartTransitionDomain ch₁ ch₂) :=
    hinjR (by simpa [oChartTransitionOnInterval] using h)
  have hval : (u : ℝ) = (v : ℝ) := by
    have := congrArg (fun y : OChartTransitionDomain ch₁ ch₂ =>
        ((y : ChartInterval ch₁.lo ch₁.hi) : ℝ)) hmain
    simpa using this
  apply Subtype.ext
  exact hval

/-- **A monotone interval neighbourhood of a transition parameter.**  A
parameter `x₀` of the transition domain `ch₁ → ch₂` carries an open real
interval `(lo,hi)` containing its parameter that lies inside the chart
interval of `ch₁`, all of whose parameters lie in the transition domain,
and on which the interval-piece transition map is strictly monotone
(order-preserving or order-reversing).  This is the local statement that
the coordinate relabelling between overlapping interval charts is
monotone on a neighbourhood of every overlap — the elementary gluing
datum of the ordering along chart chains. -/
structure OChartMonotoneNbhd {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    (x₀ : OChartTransitionDomain ch₁ ch₂) where
  lo : ℝ
  hi : ℝ
  lo_lt_hi : lo < hi
  x₀_mem : ((x₀.1 : ChartInterval ch₁.lo ch₁.hi) : ℝ) ∈ Set.Ioo lo hi
  subset : Set.Ioo lo hi ⊆ Set.Ioo ch₁.lo ch₁.hi
  dom : ∀ u : ChartInterval ch₁.lo ch₁.hi, (u : ℝ) ∈ Set.Ioo lo hi →
    (oChartLift ch₁ u : OpenMobius) ∈ ch₂.W
  monotone :
    (∀ a b : ChartInterval lo hi, (a : ℝ) < (b : ℝ) →
        oChartTransitionOnInterval ch₁ ch₂ subset dom a <
          oChartTransitionOnInterval ch₁ ch₂ subset dom b) ∨
    (∀ a b : ChartInterval lo hi, (a : ℝ) < (b : ℝ) →
        oChartTransitionOnInterval ch₁ ch₂ subset dom b <
          oChartTransitionOnInterval ch₁ ch₂ subset dom a)

theorem exists_oChartMonotoneNbhd {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    (x₀ : OChartTransitionDomain ch₁ ch₂) :
    Nonempty (OChartMonotoneNbhd ch₁ ch₂ x₀) := by
  classical
  let t₀ : ℝ := ((x₀.1 : ChartInterval ch₁.lo ch₁.hi) : ℝ)
  have ht₀lo : ch₁.lo < t₀ := (x₀.1 : ChartInterval ch₁.lo ch₁.hi).2.1
  have ht₀hi : t₀ < ch₁.hi := (x₀.1 : ChartInterval ch₁.lo ch₁.hi).2.2
  have hdom0 : IsOpen {x : ChartInterval ch₁.lo ch₁.hi | (oChartLift ch₁ x : OpenMobius) ∈ ch₂.W} :=
    isOpen_oChartTransitionDomain ch₁ ch₂
  have hmem0 : (x₀.1 : ChartInterval ch₁.lo ch₁.hi) ∈
      {x : ChartInterval ch₁.lo ch₁.hi | (oChartLift ch₁ x : OpenMobius) ∈ ch₂.W} := x₀.2
  have hnhd : ({x : ChartInterval ch₁.lo ch₁.hi | (oChartLift ch₁ x : OpenMobius) ∈ ch₂.W}) ∈
      𝓝 (x₀.1 : ChartInterval ch₁.lo ch₁.hi) := hdom0.mem_nhds hmem0
  rcases (Metric.mem_nhds_iff.mp hnhd) with ⟨ε₀, hε₀pos, hball₀⟩
  let δ₀ : ℝ := min (t₀ - ch₁.lo) (ch₁.hi - t₀)
  have hδ₀pos : 0 < δ₀ := lt_min (sub_pos.mpr ht₀lo) (sub_pos.mpr ht₀hi)
  let η : ℝ := min ε₀ δ₀
  have hηpos : 0 < η := lt_min hε₀pos hδ₀pos
  have hη₂ε : η / 2 ≤ ε₀ := by
    dsimp [η]
    have h1 : min ε₀ δ₀ ≤ ε₀ := min_le_left ε₀ δ₀
    have h2 : min ε₀ δ₀ / 2 ≤ min ε₀ δ₀ := by
      exact le_of_lt (half_lt_self (lt_min hε₀pos hδ₀pos))
    linarith
  have hη₂δ : η / 2 ≤ δ₀ := by
    dsimp [η]
    have h1 : min ε₀ δ₀ ≤ δ₀ := min_le_right ε₀ δ₀
    have h2 : min ε₀ δ₀ / 2 ≤ min ε₀ δ₀ := by
      exact le_of_lt (half_lt_self (lt_min hε₀pos hδ₀pos))
    linarith
  let lo : ℝ := t₀ - η / 2
  let hi : ℝ := t₀ + η / 2
  have hlo_lt_hi : lo < hi := by
    dsimp [lo, hi]
    linarith [hηpos]
  have hx₀_mem : t₀ ∈ Set.Ioo lo hi := by
    dsimp [lo, hi]
    constructor <;> linarith [hηpos]
  have hsub : Set.Ioo lo hi ⊆ Set.Ioo ch₁.lo ch₁.hi := by
    intro t ht
    constructor
    · have hd : δ₀ ≤ t₀ - ch₁.lo := by
        dsimp [δ₀]
        exact min_le_left (t₀ - ch₁.lo) (ch₁.hi - t₀)
      dsimp [lo] at ht ⊢
      linarith [ht.1, hη₂δ, hd, ht₀lo]
    · have hd : δ₀ ≤ ch₁.hi - t₀ := by
        dsimp [δ₀]
        exact min_le_right (t₀ - ch₁.lo) (ch₁.hi - t₀)
      dsimp [hi] at ht ⊢
      linarith [ht.2, hη₂δ, hd, ht₀hi]
  have hdom : ∀ u : ChartInterval ch₁.lo ch₁.hi, (u : ℝ) ∈ Set.Ioo lo hi →
      (oChartLift ch₁ u : OpenMobius) ∈ ch₂.W := by
    intro u hu
    have hball : u ∈ Metric.ball (x₀.1 : ChartInterval ch₁.lo ch₁.hi) ε₀ := by
      rw [Metric.mem_ball]
      have hdist : dist u (x₀.1 : ChartInterval ch₁.lo ch₁.hi) < ε₀ := by
        change dist (u : ℝ) t₀ < ε₀
        rw [Real.dist_eq, abs_lt]
        dsimp [lo, hi] at hu
        constructor <;> linarith [hu.1, hu.2, hη₂ε]
      exact hdist
    have hdomm := hball₀ hball
    simpa using hdomm
  have hmono0 :
      (∀ a b : ChartInterval lo hi, (a : ℝ) < (b : ℝ) →
          oChartTransitionOnInterval ch₁ ch₂ hsub hdom a <
            oChartTransitionOnInterval ch₁ ch₂ hsub hdom b) ∨
      (∀ a b : ChartInterval lo hi, (a : ℝ) < (b : ℝ) →
          oChartTransitionOnInterval ch₁ ch₂ hsub hdom b <
            oChartTransitionOnInterval ch₁ ch₂ hsub hdom a) :=
    interval_inj_continuous_monotone (oChartTransitionOnInterval ch₁ ch₂ hsub hdom)
      (continuous_oChartTransitionOnInterval ch₁ ch₂ hsub hdom)
      (injective_oChartTransitionOnInterval ch₁ ch₂ hsub hdom)
  exact ⟨⟨lo, hi, hlo_lt_hi, by simpa [t₀] using hx₀_mem, hsub, hdom, hmono0⟩⟩



/-- **The piece value is the `ch₂`-coordinate of the same class.**  For a
parameter of a monotone transition neighbourhood, the interval-piece
transition value is the parameter of `ch₂` that describes the same
trisecant class as the corresponding parameter of `ch₁` — so the
monotonicity direction of the neighbourhood is exactly the comparison of
the `ch₁`-order and the `ch₂`-order of the same classes: the two interval
coordinates agree (or are reversed) coherently along the overlap. -/
lemma oChartNbhd_piece_coordinate {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    (x₀ : OChartTransitionDomain ch₁ ch₂) (nb : OChartMonotoneNbhd ch₁ ch₂ x₀)
    (a : ChartInterval nb.lo nb.hi) :
    ∃ y : OChartTransitionDomain ch₂ ch₁,
      oChartLift ch₂ ((y : OChartTransitionDomain ch₂ ch₁) : ChartInterval ch₂.lo ch₂.hi) =
        oChartLift ch₁ (⟨(a : ℝ), nb.subset a.2⟩ : ChartInterval ch₁.lo ch₁.hi) ∧
      (((y : OChartTransitionDomain ch₂ ch₁) : ChartInterval ch₂.lo ch₂.hi) : ℝ) =
        oChartTransitionOnInterval ch₁ ch₂ nb.subset nb.dom a := by
  let u : ChartInterval ch₁.lo ch₁.hi := ⟨(a : ℝ), nb.subset a.2⟩
  let x : OChartTransitionDomain ch₁ ch₂ := ⟨u, nb.dom u a.2⟩
  let y : OChartTransitionDomain ch₂ ch₁ := oChartTransitionTo ch₁ ch₂ x
  refine ⟨y, ?_, ?_⟩
  · have hp := oChartTransition_preserves ch₁ ch₂ x
    simpa [y, x, u] using hp
  · have hy : (((y : OChartTransitionDomain ch₂ ch₁) : ChartInterval ch₂.lo ch₂.hi) : ℝ) =
        oChartTransitionReal ch₁ ch₂ x := by rfl
    rw [hy]
    simp [oChartTransitionOnInterval, x, u]

end LeanEval.KnotTheory.Quadrisecant
