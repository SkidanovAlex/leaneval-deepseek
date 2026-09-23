/-
# Bookkeeping for the arclength-balanced broken-geodesic loop

This module collects the elementary facts about the polygon model of
`Submission.Work.OddBound.polygonValue.balancing.Defs` (the balanced loop family `gFam` and its
building blocks `gIdx`, `gPrm`, `gPt`, `gLoop`) that the proof of
`Work.OddBound.polygonValue.balancedBrokenLoopSpec` needs.
-/
import Mathlib
import Submission.Work.OddBound.polygonValue.balancing.Defs

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

namespace Work.OddBound.polygonValue

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]

noncomputable section

/-! ## 1. The Riemannian distance along continuous families -/

/-- **Continuity of the Riemannian distance.**  If `q → x` and `r → y` and the extended Riemannian
distance between `x` and `y` is finite, then the Riemannian distances tend to the distance of the
limits. -/
theorem tendsto_riemannianDist_of_tendsto {α : Type*} {l : Filter α} {q r : α → M} {x y : M}
    (hx : Manifold.riemannianEDist I x y ≠ ⊤)
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
  have hcomp := (hcont.tendsto (x, y)).comp hpq
  have hfun : ((fun p : M × M => Manifold.riemannianEDist I p.1 p.2) ∘ fun a : α => (q a, r a))
      = fun a : α => Manifold.riemannianEDist I (q a) (r a) := by
    funext a; rfl
  rw [hfun] at hcomp
  have h3 : Filter.Tendsto (fun a : α => (Manifold.riemannianEDist I (q a) (r a)).toReal) l
      (𝓝 ((Manifold.riemannianEDist I x y).toReal)) :=
    (ENNReal.continuousAt_toReal hx).tendsto.comp hcomp
  simpa only [Work.OddBound.polygon.riemannianDist_eq_toReal] using h3

/-- **Finiteness of the extended distance between consecutive vertices.**  The side curve `S i · τ`
joins `gonVert p (w τ) i` to `gonVert p (w τ) (i+1)` and has finite length, so the extended distance
between the two vertices is finite. -/
theorem riemannianEDist_gonVert_ne_top {p : M} {N : ℕ}
    {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M} {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (i : Fin N) :
    Manifold.riemannianEDist I (Work.OddBound.gonVert p (w τ) (i : ℕ))
      (Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1)) ≠ ⊤ := by
  have hle := Manifold.riemannianEDist_le_pathELength (I := I)
    (x := Work.OddBound.gonVert p (w τ) (i : ℕ))
    (y := Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (a := 0) (b := 1) (γ := fun r : ℝ => S i r τ)
    (hSsm i τ hτ) (hS0 i τ hτ) (hS1 i τ hτ) (by norm_num)
  have hpl := (Work.OddBound.longHomotopy.curveLength_toolkit (I := I)
    (h := fun r : ℝ => S i r τ) (S := 1) (hSsm i τ hτ)).2.2 0 1
    (by norm_num) (by norm_num) (by norm_num)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hpl ▸ hle)

/-! ## 2. Vertices -/

/-- **Continuity of the vertices** in the family parameter, on the unit interval. -/
theorem continuousOn_gonVert {p : M} {N : ℕ} {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M}
    (hN : 0 < N)
    (hScont : ∀ i : Fin N, ContinuousOn (fun u : ℝ × ℝ => S i u.1 u.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ)) (m : ℕ) :
    ContinuousOn (fun τ : ℝ => Work.OddBound.gonVert p (w τ) m) (Set.Icc (0 : ℝ) 1) := by
  rcases lt_or_ge m N with hm | hm
  · have hf : ContinuousOn (fun τ : ℝ => (0, τ) : ℝ → ℝ × ℝ) (Set.Icc (0 : ℝ) 1) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hcomp : ContinuousOn (fun τ : ℝ => S ⟨m, hm⟩ 0 τ) (Set.Icc (0 : ℝ) 1) :=
      (hScont ⟨m, hm⟩).comp hf (fun τ hτ => ⟨by norm_num, hτ⟩)
    exact hcomp.congr fun τ hτ => (hS0 ⟨m, hm⟩ τ hτ).symm
  · have hcoe : ∀ τ : ℝ, Work.OddBound.gonVert p (w τ) m = p := fun τ =>
      Work.OddBound.gonVert_of_le p (w τ) hm
    exact (continuousOn_const (c := p)).congr fun τ _ => hcoe τ

/-! ## 3. Vertices of the polygon family -/

/-- **Vanishing side length means coincident vertices.** -/
theorem eq_gonVert_of_sideLen_eq_zero {p : M} {N : ℕ}
    {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M} {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    {k : ℕ} (hk : k + 1 ≤ N) (h0 : sideLen (I := I) p w τ k = 0) :
    Work.OddBound.gonVert p (w τ) k = Work.OddBound.gonVert p (w τ) (k + 1) := by
  have hkN : k < N := by omega
  haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  have h0' : Work.OddBound.gonSideLen (I := I) p (w τ) k = 0 := h0
  have hcl : Submission.Length.curveLength (I := I) (fun r : ℝ => S ⟨k, hkN⟩ r τ) 0 1 = 0 := by
    rw [hSlen ⟨k, hkN⟩ τ hτ 0 1 (by norm_num) (by norm_num) (by norm_num)]
    simp only [Fin.val_mk]
    rw [h0']
    ring
  have hle := Manifold.riemannianEDist_le_pathELength (I := I)
    (x := Work.OddBound.gonVert p (w τ) k) (y := Work.OddBound.gonVert p (w τ) (k + 1))
    (a := 0) (b := 1) (γ := fun r : ℝ => S ⟨k, hkN⟩ r τ)
    (hSsm ⟨k, hkN⟩ τ hτ) (hS0 ⟨k, hkN⟩ τ hτ) (hS1 ⟨k, hkN⟩ τ hτ) (by norm_num)
  have hpl := (Work.OddBound.longHomotopy.curveLength_toolkit (I := I)
    (h := fun r : ℝ => S ⟨k, hkN⟩ r τ) (S := 1) (hSsm ⟨k, hkN⟩ τ hτ)).2.2 0 1
    (by norm_num) (by norm_num) (by norm_num)
  have hzero : Manifold.riemannianEDist I (Work.OddBound.gonVert p (w τ) k)
      (Work.OddBound.gonVert p (w τ) (k + 1)) = 0 := by
    rw [hpl, hcl] at hle
    simp only [ENNReal.ofReal_zero] at hle
    exact le_antisymm hle (by simp)
  exact (Submission.EDist.riemannianEDist_eq_zero_iff (I := I)).mp hzero

/-- **Equal cumulative lengths mean coincident vertices.** -/
theorem eq_gonVert_of_cumLen_eq {p : M} {N : ℕ}
    {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M} {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    {i j : ℕ} (hij : i ≤ j) (hjN : j ≤ N)
    (h : cumLen (I := I) p w τ i = cumLen (I := I) p w τ j) :
    Work.OddBound.gonVert p (w τ) i = Work.OddBound.gonVert p (w τ) j := by
  refine Nat.le_induction (P := fun n _ =>
      cumLen (I := I) p w τ i = cumLen (I := I) p w τ n → n ≤ N →
        Work.OddBound.gonVert p (w τ) i = Work.OddBound.gonVert p (w τ) n)
    (fun _ _ => rfl) ?_ j hij h hjN
  intro n hmn ih hnc hnN
  have hstep : cumLen (I := I) p w τ n = cumLen (I := I) p w τ (n + 1) := by
    have h1 := cumLen_mono (I := I) p w τ (Nat.le_succ n)
    have h2 := cumLen_mono (I := I) p w τ hmn
    linarith
  have hside : sideLen (I := I) p w τ n = 0 := by
    rw [sideLen_eq_sub]; linarith
  have hgv : Work.OddBound.gonVert p (w τ) n = Work.OddBound.gonVert p (w τ) (n + 1) :=
    eq_gonVert_of_sideLen_eq_zero (I := I) hτ hSsm hS0 hS1 hSlen (k := n) (by omega) hside
  rw [← hgv]
  exact ih (hnc.trans hstep.symm) (by omega)

/-! ## 4. The point of the balanced loop at a breakpoint -/

/-- **At a breakpoint the balanced loop sits at the corresponding vertex.** -/
theorem gPt_cumLen_eq_gonVert {p : M} {N : ℕ}
    {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M} {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hN : 0 < N) {j : ℕ} (hjN : j ≤ N) :
    gPt (I := I) p hN w S τ (cumLen (I := I) p w τ j) = Work.OddBound.gonVert p (w τ) j := by
  set a : ℝ := cumLen (I := I) p w τ j with ha
  set i : ℕ := gIdx (I := I) p w τ a with hi
  have hiN' : i < N := by rw [hi]; exact gIdx_lt (I := I) p hN w τ a
  have hle1 : cumLen (I := I) p w τ i ≤ a := by
    rw [hi, ha]; exact cumLen_gIdx_le (I := I) p hN w τ _ (cumLen_nonneg (I := I) p w τ j)
  have hle2 : a ≤ cumLen (I := I) p w τ (i + 1) := by
    rw [hi, ha]
    refine le_cumLen_gIdx_succ (I := I) p hN w τ _ ?_
    rw [totLen_eq_cumLen]; exact cumLen_mono (I := I) p w τ hjN
  have hfin : gFin (I := I) p hN w τ a = ⟨i, hiN'⟩ := by
    apply Fin.ext
    show gIdx (I := I) p w τ a = i
    exact hi.symm
  have hPrm : gPrm (I := I) p w τ a
      = clamp01 ((a - cumLen (I := I) p w τ i) / sideLen (I := I) p w τ i) := by
    rw [gPrm_def]
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hcum1 : cumLen (I := I) p w τ (i + 1) = a := by
      have h := cumLen_mono (I := I) p w τ (by omega : i + 1 ≤ j)
      rw [ha]
      exact le_antisymm h hle2
    rcases lt_or_eq_of_le hle1 with hlt' | heq'
    · have hpos : 0 < sideLen (I := I) p w τ i := by
        rw [sideLen_eq_sub, hcum1]; linarith
      have hPrm1 : gPrm (I := I) p w τ a = 1 := by
        rw [hPrm]
        have hq : (a - cumLen (I := I) p w τ i) / sideLen (I := I) p w τ i = 1 := by
          rw [div_eq_one_iff_eq (ne_of_gt hpos), sideLen_eq_sub, hcum1]
        rw [hq, clamp01_eq_one_of_one_le le_rfl]
      rw [gPt_def, hfin, hPrm1, hS1 ⟨i, hiN'⟩ τ hτ]
      show Work.OddBound.gonVert p (w τ) (i + 1) = Work.OddBound.gonVert p (w τ) j
      exact eq_gonVert_of_cumLen_eq (I := I) hτ hSsm hS0 hS1 hSlen (by omega) hjN (hcum1.trans ha)
    · have hPrm0 : gPrm (I := I) p w τ a = 0 := by
        rw [hPrm, heq', sub_self, zero_div]
        exact clamp01_eq_zero_of_nonpos le_rfl
      rw [gPt_def, hfin, hPrm0, hS0 ⟨i, hiN'⟩ τ hτ]
      show Work.OddBound.gonVert p (w τ) i = Work.OddBound.gonVert p (w τ) j
      exact eq_gonVert_of_cumLen_eq (I := I) hτ hSsm hS0 hS1 hSlen (le_of_lt hlt) hjN (by rw [heq', ha])
  · have hcum : cumLen (I := I) p w τ i = a := by rw [heq, ha]
    have hPrm0 : gPrm (I := I) p w τ a = 0 := by
      rw [hPrm, hcum, sub_self, zero_div]
      exact clamp01_eq_zero_of_nonpos le_rfl
    rw [gPt_def, hfin, hPrm0, hS0 ⟨i, hiN'⟩ τ hτ]
    show Work.OddBound.gonVert p (w τ) i = Work.OddBound.gonVert p (w τ) j
    exact heq ▸ rfl
  · have hcum : cumLen (I := I) p w τ i = cumLen (I := I) p w τ j :=
      le_antisymm (by rw [ha] at hle1; exact hle1) (cumLen_mono (I := I) p w τ (le_of_lt hgt))
    have hcum' : cumLen (I := I) p w τ i = a := by rw [hcum, ha]
    have hPrm0 : gPrm (I := I) p w τ a = 0 := by
      rw [hPrm, hcum', sub_self, zero_div]
      exact clamp01_eq_zero_of_nonpos le_rfl
    rw [gPt_def, hfin, hPrm0, hS0 ⟨i, hiN'⟩ τ hτ]
    show Work.OddBound.gonVert p (w τ) i = Work.OddBound.gonVert p (w τ) j
    exact (eq_gonVert_of_cumLen_eq (I := I) hτ hSsm hS0 hS1 hSlen (i := j) (j := i)
      (le_of_lt hgt) (by omega) hcum.symm).symm

/-- At the base point: `gPt τ 0 = p`. -/
theorem gPt_zero_eq_p {p : M} {N : ℕ}
    {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M} {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hN : 0 < N) :
    gPt (I := I) p hN w S τ 0 = p := by
  rw [← cumLen_zero (I := I) p w τ]
  rw [gPt_cumLen_eq_gonVert (I := I) hτ hSsm hS0 hS1 hSlen hN (j := 0) (by omega)]
  exact Work.OddBound.gonVert_zero p (w τ)

/-- At the end of the slice: `gPt τ totLen = p`. -/
theorem gPt_totLen_eq_p {p : M} {N : ℕ}
    {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M} {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hN : 0 < N) :
    gPt (I := I) p hN w S τ (totLen (I := I) p w τ) = p := by
  rw [totLen_eq_cumLen]
  rw [gPt_cumLen_eq_gonVert (I := I) hτ hSsm hS0 hS1 hSlen hN (j := N) le_rfl]
  exact Work.OddBound.gonVert_of_le p (w τ) le_rfl

/-- The initial point of the arclength parametrisation is `p`. -/
theorem gLoop_zero_eq_p {p : M} {N : ℕ}
    {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M} {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hN : 0 < N) :
    gLoop (I := I) p hN w S τ 0 = p := by
  rw [gLoop_def, mul_zero]
  exact gPt_zero_eq_p (I := I) hτ hSsm hS0 hS1 hSlen hN

/-- The final point of the arclength parametrisation is `p`. -/
theorem gLoop_one_eq_p {p : M} {N : ℕ}
    {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M} {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hN : 0 < N) :
    gLoop (I := I) p hN w S τ 1 = p := by
  rw [gLoop_def, mul_one]
  exact gPt_totLen_eq_p (I := I) hτ hSsm hS0 hS1 hSlen hN
/-! ## 5. The periodic family and the closed geodesic -/

/-- **On `[0,1]` the periodic family `gFam` agrees with the arclength parametrisation.** -/
theorem gFam_eq_gLoop {p : M} {N : ℕ} (hN : 0 < N)
    {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M}
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    {t s : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    gFam (I := I) p hN w S s t = gLoop (I := I) p hN w S (clamp01 t) s := by
  have hτ : clamp01 t ∈ Set.Icc (0 : ℝ) 1 := clamp01_mem t
  rw [gFam_def]
  rcases lt_or_eq_of_le hs.2 with hs1 | hs1
  · rw [Int.fract_eq_self.mpr ⟨hs.1, hs1⟩]
  · subst hs1
    rw [Int.fract_one,
      gLoop_zero_eq_p (I := I) hτ hSsm hS0 hS1 hSlen hN,
      gLoop_one_eq_p (I := I) hτ hSsm hS0 hS1 hSlen hN]

/-- **`γ 0 = p`.** -/
theorem gamma_zero_eq_p {p : M} {N : ℕ} (hN : 0 < N)
    {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M} {γ : ℝ → M} {L : ℝ}
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS0slice : ∀ (i : Fin N) (r : ℝ), r ∈ Set.Icc (0 : ℝ) 1 →
      S i r 0 = γ (L * ((i : ℕ) + r) / N)) :
    γ 0 = p := by
  have h1 := hS0slice ⟨0, hN⟩ 0 (by norm_num)
  have h2 := hS0 ⟨0, hN⟩ 0 (by norm_num)
  rw [h2, Work.OddBound.gonVert_zero] at h1
  rw [h1]
  simp

/-- **Periodicity of `s ↦ γ (L s)` under the fractional part.** -/
theorem gamma_mul_fract {γ : ℝ → M} {L : ℝ} (hper : ∀ t : ℝ, γ (t + L) = γ t)
    (s : ℝ) : γ (L * Int.fract s) = γ (L * s) := by
  have hper' : Function.Periodic γ L := hper
  have hmul := hper'.int_mul ⌊s⌋
  have hx : L * Int.fract s + (⌊s⌋ : ℝ) * L = L * s := by
    have h := Int.fract_add_floor s
    calc L * Int.fract s + (⌊s⌋ : ℝ) * L = L * (Int.fract s + (⌊s⌋ : ℝ)) := by ring
      _ = L * s := by rw [h]
  rw [← hx]
  exact (hmul (L * Int.fract s)).symm

/-! ## 6. The two end slices -/

/-- **The breakpoints at `τ = 0`.** -/
theorem cumLen_zero_slice_eq {p : M} {N : ℕ} (hN : 0 < N)
    {w : ℝ → Fin (N - 1) → M} {L : ℝ}
    (hside0 : ∀ i : Fin N, Work.OddBound.gonSideLen (I := I) p (w 0) i = L / N)
    {j : ℕ} (hj : j ≤ N) :
    cumLen (I := I) p w 0 j = j * (L / N) := by
  calc cumLen (I := I) p w 0 j = ∑ k ∈ Finset.range j, sideLen (I := I) p w 0 k := rfl
    _ = ∑ _k ∈ Finset.range j, (L / N) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' : k < N := lt_of_lt_of_le (Finset.mem_range.mp hk) hj
      exact hside0 ⟨k, hk'⟩
    _ = j * (L / N) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The total length at `τ = 0` is `L`.** -/
theorem totLen_zero_slice_eq {p : M} {N : ℕ} (hN : 0 < N)
    {w : ℝ → Fin (N - 1) → M} {L : ℝ}
    (hside0 : ∀ i : Fin N, Work.OddBound.gonSideLen (I := I) p (w 0) i = L / N) :
    totLen (I := I) p w 0 = L := by
  rw [totLen_eq_cumLen, cumLen_zero_slice_eq (I := I) hN hside0 le_rfl]
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  field_simp

/-- **The slice at `τ = 0` is the geodesic `γ`.** -/
theorem gLoop_zero_slice_eq_gamma {p : M} {N : ℕ} (hN : 0 < N)
    {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M} {L : ℝ} (hL : 0 < L)
    {γ : ℝ → M} (hper : ∀ t : ℝ, γ (t + L) = γ t)
    (hside0 : ∀ i : Fin N, Work.OddBound.gonSideLen (I := I) p (w 0) i = L / N)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hS0slice : ∀ (i : Fin N) (r : ℝ), r ∈ Set.Icc (0 : ℝ) 1 →
      S i r 0 = γ (L * ((i : ℕ) + r) / N))
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    gLoop (I := I) p hN w S 0 u = γ (L * u) := by
  have hT : totLen (I := I) p w 0 = L := totLen_zero_slice_eq (I := I) hN hside0
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hLNNpos : 0 < L / N := div_pos hL hNpos
  rcases lt_or_eq_of_le hu.2 with hu1 | hu1
  · -- `u < 1`
    set i : ℕ := gIdx (I := I) p w 0 (L * u) with hi
    have hgle : i ≤ N := by
      rw [hi]; exact le_trans (gIdx_le (I := I) p w 0 _) (by omega)
    have hgle1 : i + 1 ≤ N := by
      rw [hi]
      have := gIdx_le (I := I) p w 0 (L * u)
      omega
    have hcum_i : cumLen (I := I) p w 0 i = i * (L / N) :=
      cumLen_zero_slice_eq (I := I) hN hside0 hgle
    have hcum_ip1 : cumLen (I := I) p w 0 (i + 1) = (i + 1) * (L / N) :=
      (cumLen_zero_slice_eq (I := I) hN hside0 hgle1).trans (by push_cast; ring)
    have hlth : L * u < totLen (I := I) p w 0 := by
      rw [hT]
      simpa using mul_lt_mul_of_pos_left hu1 hL
    have hlow0 : cumLen (I := I) p w 0 (gIdx (I := I) p w 0 (L * u)) ≤ L * u :=
      cumLen_gIdx_le (I := I) p hN w 0 _ (mul_nonneg hL.le hu.1)
    have hlow : (i : ℝ) * (L / N) ≤ L * u := by
      rw [← hi, hcum_i] at hlow0; exact hlow0
    have hhigh0 : L * u < cumLen (I := I) p w 0 (i + 1) := by
      have h := lt_cumLen_gIdx_succ (I := I) p hN w 0 (L * u) hlth
      rw [← hi] at h
      exact h
    have hhigh : L * u < (i : ℝ) * (L / N) + L / N := by
      rw [hcum_ip1] at hhigh0
      have : ((i + 1 : ℕ) : ℝ) * (L / N) = (i : ℝ) * (L / N) + L / N := by
        push_cast; ring
      linarith [hhigh0, this]
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    have hiu : (i : ℝ) ≤ N * u := by
      have h2 : (N : ℝ) * u * (L / N) = L * u := by field_simp
      rw [← h2] at hlow
      exact (mul_le_mul_iff_of_pos_right hLNNpos).mp hlow
    have hui : N * u < (i : ℝ) + 1 := by
      have h3 : ((i : ℝ) + 1) * (L / N) = (i : ℝ) * (L / N) + L / N := by ring
      have h2 : (N : ℝ) * u * (L / N) = L * u := by field_simp
      rw [← h3] at hhigh
      rw [← h2] at hhigh
      exact (mul_lt_mul_iff_of_pos_right hLNNpos).mp hhigh
    have hiN : i < N := by
      have hNu : N * u < (N : ℝ) := by simpa using mul_lt_mul_of_pos_left hu1 hNpos
      have h1 : (i : ℝ) < (N : ℝ) := lt_of_le_of_lt hiu hNu
      exact_mod_cast h1
    have hfin_i : gFin (I := I) p hN w 0 (L * u) = ⟨i, hiN⟩ := by
      apply Fin.ext
      show gIdx (I := I) p w 0 (L * u) = i
      exact hi.symm
    have hprm : gPrm (I := I) p w 0 (L * u) = N * u - i := by
      rw [gPrm_def, ← hi]
      have hsL : sideLen (I := I) p w 0 i = L / N := hside0 ⟨i, hiN⟩
      have hq : (L * u - cumLen (I := I) p w 0 i) / sideLen (I := I) p w 0 i = N * u - i := by
        rw [hcum_i, hsL]
        field_simp
      rw [hq, clamp01_eq_self (by linarith) (by linarith)]
    rw [gLoop_def, hT, gPt_def, hfin_i, hprm]
    rw [hS0slice ⟨i, hiN⟩ (N * u - i) ⟨by linarith, by linarith⟩]
    have harg : (((⟨i, hiN⟩ : Fin N) : ℕ) : ℝ) + (N * u - i) = N * u := by
      simp
    rw [harg]
    have hLN : L * (N * u) / N = L * u := by field_simp
    rw [hLN]
  · -- `u = 1`
    subst hu1
    rw [gLoop_def]
    rw [show totLen (I := I) p w 0 * 1 = totLen (I := I) p w 0 from mul_one _]
    rw [gPt_totLen_eq_p (I := I) (by norm_num) hSsm hS0 hS1 hSlen hN]
    have hγ0 : γ 0 = p := gamma_zero_eq_p hN hS0 hS0slice
    rw [← hγ0]
    rw [show L * 1 = 0 + L from by ring, hper 0]

/-- **At `τ = 1` every vertex is the base point.** -/
theorem gonVert_one_slice_eq_p {p : M} {N : ℕ} {w : ℝ → Fin (N - 1) → M}
    (hw1 : ∀ i : Fin (N - 1), w 1 i = p) (m : ℕ) :
    Work.OddBound.gonVert p (w 1) m = p := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; exact Work.OddBound.gonVert_zero p (w 1)
  rcases lt_or_ge m N with hmN | hmN
  · have hm1 : m - 1 < N - 1 := by omega
    rw [show m = (m - 1) + 1 from by omega]
    rw [Work.OddBound.gonVert_succ p (w 1) hm1]
    exact hw1 ⟨m - 1, hm1⟩
  · exact Work.OddBound.gonVert_of_le p (w 1) hmN

/-- **The total length of the slice `τ = 1` vanishes.** -/
theorem totLen_one_slice_eq_zero {p : M} {N : ℕ} {w : ℝ → Fin (N - 1) → M}
    (hw1 : ∀ i : Fin (N - 1), w 1 i = p) :
    totLen (I := I) p w 1 = 0 := by
  change Work.OddBound.gonLength (I := I) p (w 1) = 0
  rw [Work.OddBound.gonLength]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  show Submission.Distance.riemannianDist (I := I) (Work.OddBound.gonVert p (w 1) (i : ℕ))
    (Work.OddBound.gonVert p (w 1) ((i : ℕ) + 1)) = 0
  rw [gonVert_one_slice_eq_p hw1 (i : ℕ), gonVert_one_slice_eq_p hw1 ((i : ℕ) + 1)]
  exact Submission.Distance.riemannianDist_self (I := I) p

/-- **The slice at `τ = 1` is constant at `p`.** -/
theorem gLoop_one_slice_eq_p {p : M} {N : ℕ} (hN : 0 < N)
    {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M}
    (hw1 : ∀ i : Fin (N - 1), w 1 i = p)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (u : ℝ) :
    gLoop (I := I) p hN w S 1 u = p := by
  have hT : totLen (I := I) p w 1 = 0 := totLen_one_slice_eq_zero hw1
  rw [gLoop_def, hT, zero_mul]
  exact gPt_zero_eq_p (I := I) (by norm_num) hSsm hS0 hS1 hSlen hN

end

end Work.OddBound.polygonValue
