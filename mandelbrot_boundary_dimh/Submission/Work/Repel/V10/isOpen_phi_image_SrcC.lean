import Mathlib
import Submission.Work.Repel.V10.chain_v9_src
import Submission.Work.Repel.V10.Raw_open
import Submission.Work.Repel.V10.SrcC_sub_Dflat

namespace Work.Repel.V10

open MandelDim Complex Set Metric Filter Topology

/-- **The `φ₀`-image of a §6 source region is open.**  `V.SrcC j k n` is the round-box source
region of the cell `(j,k,n)`; it is open and lies in `Dflat η`, hence in `Dsm η`, where `V.P₀.φ`
is injective (`PertData.φ_inj_up`) and holomorphic (`PertData.φ_holo` on `Dφ ⊇ Dsm η`).  At every
point of `SrcC j k n` the map `P₀.φ` is therefore injective on a neighbourhood with non-vanishing
derivative, hence a local biholomorphism there (inverse function principle, as used in
`Work.Repel.invFunOn_differentiableOn`); alternatively the open mapping property applies directly.
Relevant helpers: `V.SrcC_sub_Dflat`, `Work.Repel.Dflat_subset_Dsm` (`chain_v9_geom.lean`),
`V.Raw_open`, and `Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn`. -/
theorem isOpen_phi_image_SrcC (V : Work.Repel.V10) {j : ℕ} {k n : ℤ}
    (hSm : V.fib j k ⊆ V.Sm1) (hn : |((n : ℤ) : ℝ)| ≤ V.η / 10 + 1) :
    IsOpen (V.P₀.φ '' V.SrcC j k n) := by
  -- the source region is open: `Raw` is open and the round box is a ball
  have hSrc_open : IsOpen (V.SrcC j k n) :=
    (Work.Repel.Raw_open V hSm).inter Metric.isOpen_ball
  -- it sits in `Dsm η` and therefore in the domain `Dφ` of `φ`
  have hSrcDsm : V.SrcC j k n ⊆ Dsm V.η :=
    fun w hw => Dflat_subset_Dsm V.η (Work.Repel.SrcC_sub_Dflat V hSm hn hw)
  have hSrcDφ : V.SrcC j k n ⊆ V.P₀.Dφ :=
    fun w hw => V.P₀.D_sub (Or.inl (hSrcDsm hw))
  have hinj : Set.InjOn V.P₀.φ (V.SrcC j k n) := V.P₀.φ_inj_up.mono hSrcDsm
  have hanal₀ : AnalyticOnNhd ℂ V.P₀.φ V.P₀.Dφ :=
    V.P₀.φ_holo.analyticOnNhd V.P₀.Dφ_open
  -- at every point `y = φ w` of the image, find a ball around `y` inside the image
  rw [Metric.isOpen_iff]
  rintro y ⟨w, hw, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hSrc_open w hw
  -- `φ` is analytic on the ball `ball w ε ⊆ SrcC`, and injective hence non-constant there
  have hBanal : AnalyticOnNhd ℂ V.P₀.φ (Metric.ball w ε) :=
    hanal₀.mono fun z hz => hSrcDφ (hball hz)
  have hBpre : IsPreconnected (Metric.ball w ε) := (convex_ball w ε).isPreconnected
  rcases hBanal.is_constant_or_isOpen hBpre with ⟨c, hc⟩ | hopen
  · -- a constant function on a ball cannot be injective: the ball has two distinct points
    exfalso
    have hwmem : w ∈ Metric.ball w ε := Metric.mem_ball_self hε
    have hεhalf : (0 : ℝ) < ε / 2 := half_pos hε
    have hmem2 : w + ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball w ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : w + ((ε / 2 : ℝ) : ℂ) - w = ((ε / 2 : ℝ) : ℂ) := by ring
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hεhalf]
      linarith
    have hne : w + ((ε / 2 : ℝ) : ℂ) ≠ w := by
      intro h
      have h0 : ((ε / 2 : ℝ) : ℂ) = 0 := by
        have := congrArg (fun z : ℂ => z - w) h
        simpa using this
      exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hεhalf)) h0
    exact hne (hinj (hball hmem2) (hball hwmem) ((hc _ hmem2).trans (hc _ hwmem).symm))
  · -- the open mapping theorem on the ball does the rest
    have hopenB : IsOpen (V.P₀.φ '' Metric.ball w ε) := hopen _ Subset.rfl Metric.isOpen_ball
    obtain ⟨δ, hδ, hδsub⟩ :=
      Metric.isOpen_iff.mp hopenB (V.P₀.φ w) ⟨w, Metric.mem_ball_self hε, rfl⟩
    exact ⟨δ, hδ, fun z hz => Set.image_mono hball (hδsub hz)⟩

end Work.Repel.V10
