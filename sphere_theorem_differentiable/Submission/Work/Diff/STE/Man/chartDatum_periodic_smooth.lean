import Mathlib
import Submission.Work.Diff.STE.Man.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The periodised chart datum: smoothness, periodicity, agreement and symmetry

This file proves `Work.Diff.STE.Man.chartDatum_periodic_smooth`: the periodisation
`chartDatum g x₀ r = chartDatumC g x₀ r` of the localised chart matrix

`chartDatumLoc g x₀ r z = torBump r z • (flatChartMat g x₀ z - flatChartMat g x₀ 0)`

of a metric `g` in the torus coordinate of a chart at `x₀` is

* smooth (`C^∞`) on the flat torus coordinate space,
* `1`-periodic in every coordinate,
* equal to the (complexified) chart matrix of `g` on the ball of radius `r/2`,
* symmetric in the matrix indices.

The proof of the first three points is the general periodisation lemma
`Work.Diff.STE.periodization_contDiff_periodic` applied entrywise to `chartDatumLoc`; the only
input needed is that the localised datum is smooth on *all* of `(Fin n → ℝ)` (it is a bump times
the chart matrix, so it vanishes off `ball 0 r` and `flatChartMat` is smooth on
`ball 0 (2r) ⊇ supp`), and that its support lies in the open unit cube (which holds because
`r ≤ 1/2`).  Symmetry is the symmetry of the Gram matrix `chartMatFun g x₀`.

## Main statements

* `Work.Diff.STE.Man.flatChartMat_symm` — the chart matrix is symmetric.
* `Work.Diff.STE.Man.chartDatumLoc_symm` — so is the localised datum.
* `Work.Diff.STE.Man.contDiff_chartDatumLoc`,
  `Work.Diff.STE.Man.contDiff_chartDatumLocC` — smoothness of the localised datum (and of its
  entries).
* `Work.Diff.STE.Man.support_chartDatumLocC` — its support lies in the open unit cube.
* `Work.Diff.STE.Man.chartDatumLocC_eq_on_ball` — its value on the closed ball of radius `r/2`.
* `Work.Diff.STE.Man.chartDatumR_eq` — the real datum as a real periodisation.
* `Work.Diff.STE.Man.chartDatum_periodic_smooth` — the target.
-/

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.Man

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Symmetry of the chart matrix and of the localised datum -/

/-- The chart matrix of a metric in the torus coordinate is symmetric: it is the Gram matrix of
the coordinate frame. -/
lemma flatChartMat_symm (g : Submission.Diff.SMet I M) (x₀ : M)
    (z : Fin (dim E) → ℝ) (i j : Fin (dim E)) :
    flatChartMat g x₀ z i j = flatChartMat g x₀ z j i :=
  g.symm _ _ _

/-- The localised chart datum is symmetric in its matrix indices. -/
lemma chartDatumLoc_symm (g : Submission.Diff.SMet I M) (x₀ : M) (r : ℝ) (hr : 0 < r)
    (w : Fin (dim E) → ℝ) (i j : Fin (dim E)) :
    (chartDatumLoc g x₀ r hr w) i j = (chartDatumLoc g x₀ r hr w) j i := by
  show (torBump (E := E) r hr w • (flatChartMat g x₀ w - flatChartMat g x₀ 0)) i j
      = (torBump (E := E) r hr w • (flatChartMat g x₀ w - flatChartMat g x₀ 0)) j i
  simp only [Pi.smul_apply, Pi.sub_apply, flatChartMat_symm g x₀ w i j,
    flatChartMat_symm g x₀ (0 : Fin (dim E) → ℝ) i j]

/-! ## Smoothness of the localised chart datum -/

/-- **The localised chart matrix is smooth** on all of `(Fin n → ℝ)`: it is a smooth bump times
the chart matrix, which is smooth on the ball of radius `2r` containing the support of the
bump.  Off that ball the product vanishes identically near every point. -/
lemma contDiff_chartDatumLoc (g : Submission.Diff.SMet I M) (x₀ : M) (r : ℝ) (hr : 0 < r)
    (hcont : ContDiffOn ℝ (⊤ : ℕ∞) (flatChartMat g x₀)
      (Metric.ball (0 : Fin (dim E) → ℝ) (2 * r))) :
    ContDiff ℝ (⊤ : ℕ∞) (chartDatumLoc g x₀ r hr) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ Metric.ball (0 : Fin (dim E) → ℝ) (2 * r)
  · -- at a point of the ball of radius `2r` both factors are smooth
    have hf : ContDiffAt ℝ (⊤ : ℕ∞) (flatChartMat g x₀) z :=
      hcont.contDiffAt (Metric.isOpen_ball.mem_nhds hz)
    have hb : ContDiffAt ℝ (⊤ : ℕ∞) (torBump (E := E) r hr) z :=
      (torBump_contDiff (E := E) r hr).contDiffAt
    have hsub : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun w => flatChartMat g x₀ w
          - flatChartMat g x₀ (0 : Fin (dim E) → ℝ)) z :=
      hf.sub (contDiffAt_const (c := flatChartMat g x₀ (0 : Fin (dim E) → ℝ)))
    change ContDiffAt ℝ (⊤ : ℕ∞) (fun w => torBump (E := E) r hr w
      • (flatChartMat g x₀ w - flatChartMat g x₀ (0 : Fin (dim E) → ℝ))) z
    exact hb.smul hsub
  · -- off the ball of radius `2r` the bump vanishes on a whole neighbourhood
    have hz2 : 2 * r ≤ ‖z‖ := by
      rw [Metric.mem_ball, not_lt] at hz
      simpa [dist_eq_norm] using hz
    have hnb : Metric.ball z r ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)
    have hev : (fun w : Fin (dim E) → ℝ => chartDatumLoc g x₀ r hr w)
        =ᶠ[nhds z] (fun _ => (0 : Work.Diff.EXT.MatE (E := E))) := by
      filter_upwards [hnb] with w hw
      have hwr : r ≤ Dist.dist w (0 : Fin (dim E) → ℝ) := by
        have h2 : Dist.dist z w < r := by
          rw [dist_comm]
          simpa [dist_eq_norm] using hw
        have h4 := dist_triangle z w (0 : Fin (dim E) → ℝ)
        have h3 : Dist.dist z (0 : Fin (dim E) → ℝ) = ‖z‖ := by
          simp [dist_eq_norm]
        rw [h3] at h4
        linarith
      show chartDatumLoc g x₀ r hr w = 0
      rw [chartDatumLoc, torBump_zero (E := E) r hr hwr, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The entries of the localised chart datum, viewed as complex-valued functions, are smooth. -/
lemma contDiff_chartDatumLocC (g : Submission.Diff.SMet I M) (x₀ : M) (r : ℝ) (hr : 0 < r)
    (hcont : ContDiffOn ℝ (⊤ : ℕ∞) (flatChartMat g x₀)
      (Metric.ball (0 : Fin (dim E) → ℝ) (2 * r))) (i j : Fin (dim E)) :
    ContDiff ℝ (⊤ : ℕ∞) (chartDatumLocC g x₀ r hr i j) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (chartDatumLoc g x₀ r hr) :=
    contDiff_chartDatumLoc g x₀ r hr hcont
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z => chartDatumLoc g x₀ r hr z i j) :=
    contDiff_pi.mp (contDiff_pi.mp h i) j
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (Complex.ofRealCLM ∘ fun z => chartDatumLoc g x₀ r hr z i j) :=
    (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp h1
  exact h2

/-! ## The support and the value of the localised datum -/

/-- On the closed ball of radius `r/2` the bump equals `1`, so the localised datum is the
difference of the chart matrix and its value at `0`. -/
lemma chartDatumLocC_eq_on_ball (g : Submission.Diff.SMet I M) (x₀ : M) (r : ℝ) (hr : 0 < r)
    (z : Fin (dim E) → ℝ) (hz : z ∈ Metric.closedBall (0 : Fin (dim E) → ℝ) (r / 2))
    (i j : Fin (dim E)) :
    chartDatumLocC g x₀ r hr i j z
      = ((flatChartMat g x₀ z - flatChartMat g x₀ 0) i j : ℂ) := by
  have h1 : torBump (E := E) r hr z = 1 := torBump_one (E := E) r hr hz
  show (((torBump (E := E) r hr) z
    • (flatChartMat g x₀ z - flatChartMat g x₀ (0 : Fin (dim E) → ℝ))) i j : ℂ) = _
  rw [h1, one_smul]

/-- The support of the localised chart datum (entrywise, as a complex-valued function) is
contained in the open unit cube, because the bump is supported in `ball 0 r` and `r ≤ 1/2`. -/
lemma support_chartDatumLocC (g : Submission.Diff.SMet I M) (x₀ : M) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1 / 2) (i j : Fin (dim E)) :
    Function.support (chartDatumLocC g x₀ r hr i j) ⊆
      Set.pi Set.univ (fun _ : Fin (dim E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
  intro z hz
  rw [Function.mem_support] at hz
  have hzij : (chartDatumLoc g x₀ r hr z) i j ≠ 0 := by
    intro h
    refine hz ?_
    show (((chartDatumLoc g x₀ r hr z) i j : ℝ) : ℂ) = 0
    rw [h, Complex.ofReal_zero]
  have htb : (torBump (E := E) r hr) z ≠ 0 := by
    intro h
    apply hzij
    show ((torBump (E := E) r hr) z
      • (flatChartMat g x₀ z - flatChartMat g x₀ (0 : Fin (dim E) → ℝ))) i j = 0
    rw [h, zero_smul]
    rfl
  have hball : z ∈ Metric.ball (0 : Fin (dim E) → ℝ) r :=
    torBump_support_subset (E := E) r hr (Function.mem_support.mpr htb)
  rw [Set.mem_pi]
  intro c _
  rw [Set.mem_Ioo]
  have hnorm : ‖z‖ < r := by
    rw [Metric.mem_ball] at hball
    simpa [dist_eq_norm] using hball
  have hzi : |z c| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm z c
  exact abs_lt.mp (by linarith)

/-! ## The real datum as a real periodisation -/

/-- The real part of the periodised datum, written as the real periodisation of the real entries of
the localised datum.  This is what makes the symmetry of `chartDatumR` immediate (the real part of
the complex periodisation is the periodisation of the real parts, `Complex.ofReal_tsum`). -/
lemma chartDatumR_eq (g : Submission.Diff.SMet I M) (x₀ : M) (r : ℝ) (hr : 0 < r)
    (z : Fin (dim E) → ℝ) (i j : Fin (dim E)) :
    chartDatumR g x₀ r hr z i j
      = flatChartMat g x₀ (0 : Fin (dim E) → ℝ) i j
        + ∑' m : Fin (dim E) → ℤ, (chartDatumLoc g x₀ r hr (z + iVec m)) i j := by
  have hC : chartDatumC (I := I) g x₀ r hr z i j
      = (((flatChartMat g x₀ (0 : Fin (dim E) → ℝ) i j)
          + ∑' m : Fin (dim E) → ℤ, (chartDatumLoc g x₀ r hr (z + iVec m)) i j : ℝ) : ℂ) := by
    have htsum : (∑' m : Fin (dim E) → ℤ, chartDatumLocC g x₀ r hr i j (z + iVec m))
        = (((∑' m : Fin (dim E) → ℤ,
            (chartDatumLoc g x₀ r hr (z + iVec m)) i j) : ℝ) : ℂ) :=
      (Complex.ofReal_tsum (fun m : Fin (dim E) → ℤ =>
        (chartDatumLoc g x₀ r hr (z + iVec m)) i j)).symm
    show (flatChartMat g x₀ (0 : Fin (dim E) → ℝ) i j : ℂ)
        + ∑' m : Fin (dim E) → ℤ, chartDatumLocC g x₀ r hr i j (z + iVec m)
      = (((flatChartMat g x₀ (0 : Fin (dim E) → ℝ) i j)
          + ∑' m : Fin (dim E) → ℤ, (chartDatumLoc g x₀ r hr (z + iVec m)) i j : ℝ) : ℂ)
    rw [htsum, ← Complex.ofReal_add]
  show (chartDatumC (I := I) g x₀ r hr z i j).re
      = flatChartMat g x₀ (0 : Fin (dim E) → ℝ) i j
        + ∑' m : Fin (dim E) → ℤ, (chartDatumLoc g x₀ r hr (z + iVec m)) i j
  rw [hC, Complex.ofReal_re]

/-! ## The target -/

theorem chartDatum_periodic_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x₀ : M) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1 / 2)
    (hcont : ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.Man.flatChartMat g x₀)
      (Metric.ball (0 : Fin (Work.Diff.STE.Man.dim E) → ℝ) (2 * r))) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.Man.chartDatum g x₀ r hr) ∧
    Work.Diff.STE.Periodic1 (Work.Diff.STE.Man.chartDatum g x₀ r hr) ∧
    (∀ z ∈ Metric.ball (0 : Fin (Work.Diff.STE.Man.dim E) → ℝ) (r / 2),
      Work.Diff.STE.Man.chartDatum g x₀ r hr z
        = Work.Diff.STE.Man.ofRealMat (Work.Diff.STE.Man.flatChartMat g x₀ z)) ∧
    (∀ (z : Fin (Work.Diff.STE.Man.dim E) → ℝ) (i j : Fin (Work.Diff.STE.Man.dim E)),
      Work.Diff.STE.Man.chartDatumR g x₀ r hr z i j
        = Work.Diff.STE.Man.chartDatumR g x₀ r hr z j i) := by
  have hlocC : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (chartDatumLocC g x₀ r hr i j) :=
    fun i j => contDiff_chartDatumLocC g x₀ r hr hcont i j
  have hsupp : ∀ i j, Function.support (chartDatumLocC g x₀ r hr i j) ⊆
      Set.pi Set.univ (fun _ : Fin (dim E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    fun i j => support_chartDatumLocC g x₀ r hr hr1 i j
  have hper : ∀ i j, Work.Diff.STE.Periodic1
      (fun z => ∑' m : Fin (dim E) → ℤ, chartDatumLocC g x₀ r hr i j (z + iVec m)) :=
    fun i j => Work.Diff.STE.periodization_periodic (chartDatumLocC g x₀ r hr i j)
  have hcd : ∀ i j, ContDiff ℝ (⊤ : ℕ∞)
      (fun z => ∑' m : Fin (dim E) → ℤ, chartDatumLocC g x₀ r hr i j (z + iVec m)) :=
    fun i j => (Work.Diff.STE.periodization_contDiff_periodic (chartDatumLocC g x₀ r hr i j)
      (hlocC i j) (hsupp i j)).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- smoothness, entrywise from the periodisation lemma
    change ContDiff ℝ (⊤ : ℕ∞) (chartDatumC (I := I) g x₀ r hr)
    rw [contDiff_pi]
    intro i
    rw [contDiff_pi]
    intro j
    have h : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (dim E) → ℝ =>
        (flatChartMat g x₀ (0 : Fin (dim E) → ℝ) i j : ℂ)
          + ∑' m : Fin (dim E) → ℤ, chartDatumLocC g x₀ r hr i j (z + iVec m)) :=
      contDiff_const.add (hcd i j)
    exact h
  · -- periodicity, entrywise from the reindexing of the sum
    intro c x
    funext i j
    show chartDatumC (I := I) g x₀ r hr (x + Pi.single c 1) i j
        = chartDatumC (I := I) g x₀ r hr x i j
    show (flatChartMat g x₀ (0 : Fin (dim E) → ℝ) i j : ℂ)
          + ∑' m : Fin (dim E) → ℤ, chartDatumLocC g x₀ r hr i j ((x + Pi.single c 1) + iVec m)
        = (flatChartMat g x₀ (0 : Fin (dim E) → ℝ) i j : ℂ)
          + ∑' m : Fin (dim E) → ℤ, chartDatumLocC g x₀ r hr i j (x + iVec m)
    rw [show (∑' m : Fin (dim E) → ℤ,
          chartDatumLocC g x₀ r hr i j ((x + Pi.single c 1) + iVec m))
        = (∑' m : Fin (dim E) → ℤ, chartDatumLocC g x₀ r hr i j (x + iVec m))
        from hper i j c x]
  · -- the datum agrees with the chart matrix on the ball of radius `r/2`
    intro z hz
    funext i j
    have hzt : ∀ c : Fin (dim E), z c ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
      intro c
      rw [Set.mem_Ioo]
      have h1 : ‖z‖ < r / 2 := by
        rw [Metric.mem_ball] at hz
        simpa [dist_eq_norm] using hz
      have h2 : |z c| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm z c
      exact abs_lt.mp (by linarith)
    have hzc : z ∈ Metric.closedBall (0 : Fin (dim E) → ℝ) (r / 2) := by
      rw [Metric.mem_closedBall]
      rw [Metric.mem_ball] at hz
      exact le_of_lt hz
    show chartDatumC (I := I) g x₀ r hr z i j = (flatChartMat g x₀ z i j : ℂ)
    show (flatChartMat g x₀ (0 : Fin (dim E) → ℝ) i j : ℂ)
          + ∑' m : Fin (dim E) → ℤ, chartDatumLocC g x₀ r hr i j (z + iVec m)
        = (flatChartMat g x₀ z i j : ℂ)
    rw [show (∑' m : Fin (dim E) → ℤ, chartDatumLocC g x₀ r hr i j (z + iVec m))
        = chartDatumLocC g x₀ r hr i j z from
          Work.Diff.STE.periodization_eq_self (hsupp i j) hzt,
      chartDatumLocC_eq_on_ball g x₀ r hr z hzc i j]
    simp only [Pi.sub_apply, Complex.ofReal_sub]
    ring
  · -- symmetry: both sides are the same real periodisation
    intro z i j
    rw [chartDatumR_eq g x₀ r hr z i j, chartDatumR_eq g x₀ r hr z j i]
    congr 1
    · exact flatChartMat_symm g x₀ (0 : Fin (dim E) → ℝ) i j
    · exact tsum_congr (fun m => chartDatumLoc_symm g x₀ r hr (z + iVec m) i j)

end Work.Diff.STE.Man
