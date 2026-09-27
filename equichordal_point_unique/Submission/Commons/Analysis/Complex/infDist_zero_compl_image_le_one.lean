import Mathlib
import Submission.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

noncomputable section

open Metric Set Filter
open scoped Topology ComplexConjugate

namespace Commons.Analysis.Complex

/-- If `f` is holomorphic and injective on the unit disc with `f 0 = 0` and `f'(0) = 1`,
then the complement of its image comes within distance `1` of the origin.

Proof: if some radius `> 1` around `0` were contained in `f '' ball 0 1`, the (set-theoretic)
inverse `g` of `f` would be a holomorphic self-map of the unit disc with `g 0 = 0`,
`g'(0) = 1`; the equality case of the Schwarz lemma forces `g = id`, hence `f = id` on the
disc, contradiction. -/
theorem infDist_zero_compl_image_le_one {f : ℂ → ℂ}
    (hf : ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z)
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    Metric.infDist 0 ((f '' Metric.ball (0 : ℂ) 1)ᶜ) ≤ 1 := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : 1 < infDist 0 ((f '' ball 0 1)ᶜ)`, hence the closed unit disc lies in the image.
  have hS : Metric.closedBall (0 : ℂ) 1 ⊆ f '' Metric.ball (0 : ℂ) 1 := by
    intro w hw
    by_contra hwS
    have hle : Metric.infDist 0 ((f '' Metric.ball (0 : ℂ) 1)ᶜ) ≤ dist 0 w :=
      Metric.infDist_le_dist_of_mem (s := (f '' Metric.ball (0 : ℂ) 1)ᶜ) (by simpa using hwS)
    rw [Complex.dist_eq] at hle
    have hnorm : ‖(0 : ℂ) - w‖ = ‖w‖ := by simp
    rw [hnorm] at hle
    have hwle : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw
    linarith
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  -- The set-theoretic inverse of `f` on the closed unit disc.
  let g : ℂ → ℂ := fun w =>
    if h : ∃ z ∈ Metric.ball (0 : ℂ) 1, f z = w then Classical.choose h else 0
  have hg_spec : ∀ w ∈ Metric.closedBall (0 : ℂ) 1,
      g w ∈ Metric.ball (0 : ℂ) 1 ∧ f (g w) = w := by
    intro w hw
    have hex : ∃ z ∈ Metric.ball (0 : ℂ) 1, f z = w := hS hw
    have hgw : g w = Classical.choose hex := by
      simp only [g]
      rw [dif_pos hex]
    rw [hgw]
    exact Classical.choose_spec hex
  have hg0 : g 0 = 0 := by
    obtain ⟨hgball, hgval⟩ := hg_spec 0 (mem_closedBall_self (by norm_num))
    exact hinj hgball h0mem (by rw [hgval, h0])
  -- `g` is holomorphic on the disc: near any point it agrees with the local inverse of `f`.
  have hgd : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1) := by
    intro w₀ hw₀
    have hw₀' : ‖w₀‖ < 1 := mem_ball_zero_iff.mp hw₀
    obtain ⟨hgwball, hgwval⟩ := hg_spec w₀ (mem_closedBall_zero_iff.mpr (le_of_lt hw₀'))
    set z₀ : ℂ := g w₀ with hz₀def
    have hz₀mem : z₀ ∈ Metric.ball (0 : ℂ) 1 := hgwball
    have hfz₀ : AnalyticAt ℂ f z₀ := hf z₀ hz₀mem
    have hfz₀val : f z₀ = w₀ := hgwval
    have hz₀norm : ‖z₀‖ < 1 := mem_ball_zero_iff.mp hz₀mem
    -- the derivative of `f` at `z₀` does not vanish, by injectivity
    have hdne : deriv f z₀ ≠ 0 := by
      have hsub : Metric.ball z₀ (1 - ‖z₀‖) ⊆ Metric.ball (0 : ℂ) 1 := by
        intro a ha
        rw [Metric.mem_ball, Complex.dist_eq] at ha ⊢
        have h1 : ‖a - 0‖ ≤ ‖a - z₀‖ + ‖z₀‖ := by
          calc ‖a - 0‖ = ‖(a - z₀) + z₀‖ := by ring_nf
            _ ≤ ‖a - z₀‖ + ‖z₀‖ := norm_add_le _ _
        linarith
      refine Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn
        (c := z₀) (r := 1 - ‖z₀‖) (by linarith) hfz₀ ?_
      exact fun a ha b hb hab => hinj (hsub ha) (hsub hb) hab
    -- `g ∘ f = id` eventually at `z₀`, so `g` is analytic at `f z₀` by the inverse function rule
    have hev : (g ∘ f) =ᶠ[𝓝 z₀] id := by
      have hb : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (f z₀) :=
        Metric.isOpen_ball.mem_nhds (by rw [hfz₀val]; exact mem_ball_zero_iff.mpr hw₀')
      have hcont : ∀ᶠ z in 𝓝 z₀, f z ∈ Metric.ball (0 : ℂ) 1 :=
        Filter.Tendsto.eventually hfz₀.continuousAt hb
      filter_upwards [hcont, Metric.isOpen_ball.mem_nhds hz₀mem] with z hfz hzmem
      simp only [Function.comp_apply, id]
      obtain ⟨hgzball, hgzval⟩ := hg_spec (f z) (Metric.ball_subset_closedBall hfz)
      exact hinj hgzball hzmem hgzval
    have hAnal : AnalyticAt ℂ (g ∘ f) z₀ := analyticAt_id.congr hev.symm
    have hAnalg : AnalyticAt ℂ g (f z₀) :=
      (analyticAt_comp_iff_of_deriv_ne_zero hfz₀ hdne).mp hAnal
    rw [hfz₀val] at hAnalg
    exact hAnalg.differentiableAt.differentiableWithinAt
  have hgmaps : Set.MapsTo g (Metric.ball (0 : ℂ) 1) (Metric.closedBall (0 : ℂ) 1) := by
    intro w hw
    rw [mem_closedBall_zero_iff]
    have hw' : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have := (hg_spec w (mem_closedBall_zero_iff.mpr (le_of_lt hw'))).1
    rw [mem_ball_zero_iff] at this
    linarith
  have hgdiff0 : DifferentiableAt ℂ g 0 :=
    (hgd 0 h0mem).differentiableAt (Metric.isOpen_ball.mem_nhds h0mem)
  have hfdiffg0 : DifferentiableAt ℂ f (g 0) := by
    rw [hg0]; exact (hf 0 h0mem).differentiableAt
  have hfid : (f ∘ g) =ᶠ[𝓝 (0 : ℂ)] id := by
    filter_upwards [Metric.isOpen_ball.mem_nhds h0mem] with w hw
    simp only [Function.comp_apply, id]
    exact (hg_spec w (Metric.ball_subset_closedBall hw)).2
  have hderivg : deriv g 0 = 1 := by
    have hcomp := deriv_comp (x := (0 : ℂ)) hfdiffg0 hgdiff0
    have hone : deriv (f ∘ g) 0 = 1 := by
      rw [hfid.deriv_eq]; simp
    rw [hone, hg0, h1, one_mul] at hcomp
    exact hcomp.symm
  -- Apply the equality case of the Schwarz lemma to `g`.
  have h_eq : ‖dslope g 0 0‖ = (1 : ℝ) / 1 := by
    rw [dslope_same, hderivg]; norm_num
  have hgmaps' : Set.MapsTo g (Metric.ball (0 : ℂ) 1) (Metric.closedBall (g 0) 1) := by
    rw [hg0]; exact hgmaps
  have heqon := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div
    (f := g) (c := 0) (z₀ := 0) (R₁ := 1) (R₂ := 1) hgd hgmaps' h0mem h_eq
  have hfun : (fun z => g 0 + (z - 0) • dslope g 0 0) = fun z => z := by
    funext z
    rw [hg0, dslope_same, hderivg]
    simp
  rw [hfun] at heqon
  have hgid : ∀ z ∈ Metric.ball (0 : ℂ) 1, g z = z := fun z hz => heqon hz
  have hfidball : ∀ z ∈ Metric.ball (0 : ℂ) 1, f z = z := by
    intro z hz
    have := (hg_spec z (Metric.ball_subset_closedBall hz)).2
    rw [hgid z hz] at this
    exact this
  -- `f = id` on the disc, contradicting `1 ∈ f '' ball 0 1`.
  have h1mem : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff]; norm_num
  obtain ⟨z, hz, hfz⟩ := hS h1mem
  have hz1 : z = 1 := by rw [← hfz]; exact (hfidball z hz).symm
  rw [hz1] at hz
  have : ‖(1 : ℂ)‖ < 1 := mem_ball_zero_iff.mp hz
  norm_num at this

end Commons.Analysis.Complex
