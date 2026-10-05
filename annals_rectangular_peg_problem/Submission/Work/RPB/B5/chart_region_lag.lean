import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B2.chordSurf_lagrangian
import Submission.Work.RPB.B5.chartChain
import Submission.Work.RPB.B5.chart_deriv_x
import Submission.Work.RPB.B5.chart_deriv_t

/-!
# B5: the chart region of `lagPt` is Lagrangian

For `x` in the open chart interval `(-√2, 0)` the point `lagPt W Γc Ac rho τ x t` is the chart
value `W τ t (rho τ x t)`.  On that interval `D.hrhoval` gives `0 < rho τ x t ≤ π²/4`, so with
`r = √(rho τ x t) ∈ (0, π/2]` the identification `D.hWchord` applies and *both* coordinates are
reparametrisations of the chord annulus `r ↦ chordSurf CI.c a τ t r`:

* `deriv (fun y => W τ t (rho τ y t)) x = (d/dy √(rho τ y ·)) x • ∂_r chordSurf`,
* `deriv (fun s => W τ s (rho τ x s)) t = ∂_t chordSurf + (d/ds √(rho τ x ·)) t • ∂_r chordSurf`

(these are the sibling lemmas `chart_deriv_x` / `chart_deriv_t`).  Both tangent vectors therefore
lie in the span of the two partials of the chord annulus, whose `symp`-pairing vanishes by
`Work.RPB.B2.chordSurf_lagrangian`; bilinearity and skewness of `symp` finish the computation.
-/

namespace Work.RPB.B5

/-- `Work.RPV.symp` is alternating (skew-symmetric). -/
private theorem symp_skew (u v : Work.RPV.PS) : Work.RPV.symp u v = -Work.RPV.symp v u := by
  simp only [Work.RPV.symp]; ring

theorem chart_region_lag (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Ioo (-Real.sqrt 2) 0, ∀ t,
      Work.RPV.symp
        (deriv (fun y => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ y t) x)
        (deriv (fun s => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x s) t) = 0 := by
  intro τ hτ x hx t
  obtain ⟨hx1, hx2⟩ := hx
  have hxle : x ≤ 0 := le_of_lt hx2
  have hxge : ¬ x ≤ -Real.sqrt 2 := not_le.mpr hx1
  -- bounds on `rho` on the chart region
  have hρmem : 0 < D.rho τ x t ∧ D.rho τ x t ≤ Real.pi ^ 2 / 4 :=
    D.hrhoval τ hτ x ⟨hx1, hxle⟩ t
  have hr₀pos : 0 < Real.sqrt (D.rho τ x t) := Real.sqrt_pos.mpr hρmem.1
  have hr₀lt : Real.sqrt (D.rho τ x t) < Real.pi := by
    have h2 : Real.sqrt (D.rho τ x t) ≤ Real.sqrt ((Real.pi / 2) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [hρmem.2, Real.pi_pos])
    rw [Real.sqrt_sq (by positivity)] at h2
    linarith [Real.pi_pos]
  have hr₀mem : Real.sqrt (D.rho τ x t) ∈ Set.Ioo (0 : ℝ) Real.pi := ⟨hr₀pos, hr₀lt⟩
  -- the chord annulus is Lagrangian at the chord radius `r₀`
  have hLag : Work.RPV.symp
      (deriv (fun s => Work.RPB.chordSurf CI.c a τ s (Real.sqrt (D.rho τ x t))) t)
      (deriv (fun s => Work.RPB.chordSurf CI.c a τ t s) (Real.sqrt (D.rho τ x t))) = 0 :=
    Work.RPB.B2.chordSurf_lagrangian CI a ha τ hτ t (Real.sqrt (D.rho τ x t)) hr₀mem
  -- reduce `lagPt` to its chart branch
  have hred1 : deriv (fun y => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ y t) x
      = deriv (fun y => D.W τ t (D.rho τ y t)) x := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioo_mem_nhds hx1 hx2] with y hy
    rw [Work.RPB.B5.lagPt, if_pos (le_of_lt hy.2), Work.RPB.B5.basePt,
      if_neg (not_le.mpr hy.1)]
  have hred2 : deriv (fun s => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x s) t
      = deriv (fun s => D.W τ s (D.rho τ x s)) t := by
    congr 1
    funext s
    rw [Work.RPB.B5.lagPt, if_pos hxle, Work.RPB.B5.basePt, if_neg hxge]
  -- the two tangent vectors, as reparametrisations of the chord annulus
  rw [hred1, hred2, Work.RPB.B5.chart_deriv_x CI a ha D τ hτ t x ⟨hx1, hx2⟩,
    Work.RPB.B5.chart_deriv_t CI a ha D τ hτ x ⟨hx1, hx2⟩ t]
  rw [Work.RPB.B5.symp_smul_add]
  have hBrBr : Work.RPV.symp
      (deriv (fun r => Work.RPB.chordSurf CI.c a τ t r) (Real.sqrt (D.rho τ x t)))
      (deriv (fun r => Work.RPB.chordSurf CI.c a τ t r) (Real.sqrt (D.rho τ x t))) = 0 :=
    Work.RPB.B5.symp_self _
  have hBrBt : Work.RPV.symp
      (deriv (fun r => Work.RPB.chordSurf CI.c a τ t r) (Real.sqrt (D.rho τ x t)))
      (deriv (fun u => Work.RPB.chordSurf CI.c a τ u (Real.sqrt (D.rho τ x t))) t) = 0 := by
    rw [symp_skew]
    rw [hLag]
    ring
  rw [hBrBr, hBrBt, mul_zero, add_zero, mul_zero]

end Work.RPB.B5
