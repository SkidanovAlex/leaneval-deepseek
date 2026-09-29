import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.setup
import Submission.Work.A14D.uh_ode
import Submission.Work.A14D.uh_defs
import Submission.Work.A14D.uh_hasSum
import Submission.Work.C17g.linear_ode_convex
import Submission.Work.A14D.PZ_mul_wron_const
import Submission.Work.A14D.exists_smul_of_wron_eq_zero

namespace Work.A14D

open Complex Metric Filter
open scoped BigOperators Topology

/-- `PZ` does not vanish on the disc `ball 1 δ` (`δ < 8/9`) away from the singular point `z = 1`.

Indeed `PZ z = z (1-z) (1-9z)` vanishes only at `0`, `1` and `1/9`, and the latter two points are
at distance `1 > 8/9` and `8/9 > δ` from the centre `1`. -/
lemma PZ_ne_zero_of_mem_ball_one {δ : ℝ} (hδ : δ < 8 / 9) {z : ℂ}
    (hz : z ∈ Metric.ball (1 : ℂ) δ) (hz1 : z ≠ 1) : PZ z ≠ 0 := by
  have hdist : dist z 1 < 8 / 9 := lt_of_lt_of_le (Metric.mem_ball.mp hz) (le_of_lt hδ)
  intro h
  simp only [PZ] at h
  have h' : (z = 0 ∨ 1 - z = 0) ∨ 1 - 9 * z = 0 := by simpa using h
  rcases h' with (hz0 | h1z) | h9z
  · rw [hz0] at hdist
    norm_num at hdist
  · exact hz1 (by linear_combination -h1z)
  · have hz9 : z = 1 / 9 := by linear_combination (-(1 / 9)) * h9z
    rw [hz9] at hdist
    rw [Complex.dist_eq] at hdist
    norm_num at hdist

/-- There is a disc around `1`, contained in `ball 1 δ'`, on which `uh` does not vanish (because
`uh` is holomorphic on `ball 1 (8/9)` and `uh 1 = 1`). -/
lemma exists_ball_uh_ne_zero {δ' : ℝ} (hδ' : 0 < δ') :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (1 : ℂ) ρ ⊆ Metric.ball (1 : ℂ) δ' ∧
      ∀ z ∈ Metric.ball (1 : ℂ) ρ, uh z ≠ 0 := by
  obtain ⟨huhd, huh1, -⟩ := uh_ode
  have hmem : (1 : ℂ) ∈ Metric.ball (1 : ℂ) (8 / 9) := Metric.mem_ball_self (by norm_num)
  have hcont : ContinuousAt uh 1 :=
    (huhd.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)).continuousAt
  have hs : {z : ℂ | uh z ≠ 0} ∈ 𝓝 (1 : ℂ) := by
    refine hcont.eventually_ne ?_
    rw [huh1]; norm_num
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨min (δ' / 2) ε, lt_min (by linarith) hε, ?_, ?_⟩
  · exact Metric.ball_subset_ball (le_trans (min_le_left _ _) (by linarith))
  · intro z hz
    exact hεsub (Metric.ball_subset_ball (min_le_right _ _) hz)

/-- The space of functions holomorphic on `ball 1 δ'` (`0 < δ' < 8/9`) solving `LZ f = 0` is
one-dimensional, spanned by the holomorphic solution `uh` at `z = 1`. -/
theorem hol_sol_at_one_smul {δ' : ℝ} (hδ' : 0 < δ') (hδ'89 : δ' < 8 / 9) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 1 δ'))
    (hode : ∀ z ∈ Metric.ball 1 δ', LZ f z = 0) :
    ∃ c : ℂ, ∀ z ∈ Metric.ball 1 δ', f z = c * uh z := by
  -- `uh` is a holomorphic solution on the whole disc, with `uh 1 = 1`
  obtain ⟨huhd, huh1, huhode⟩ := uh_ode
  have hsub : Metric.ball (1 : ℂ) δ' ⊆ Metric.ball (1 : ℂ) (8 / 9) :=
    Metric.ball_subset_ball (le_of_lt hδ'89)
  have huhd' : DifferentiableOn ℂ uh (Metric.ball (1 : ℂ) δ') := huhd.mono hsub
  have huhode' : ∀ z ∈ Metric.ball (1 : ℂ) δ', LZ uh z = 0 := fun z hz => huhode z (hsub hz)
  -- Abel's identity: `PZ · wron f uh` is constant on the disc
  obtain ⟨C, hC⟩ := PZ_mul_wron_const Metric.isOpen_ball
    (convex_ball (1 : ℂ) δ').isPreconnected hf huhd' hode huhode'
  -- evaluating at the singular point `z = 1` (where `PZ 1 = 0`) gives `C = 0`
  have hC0 : C = 0 := by
    have h1 : (1 : ℂ) ∈ Metric.ball (1 : ℂ) δ' := Metric.mem_ball_self hδ'
    have h := hC 1 h1
    have hPZ1 : PZ (1 : ℂ) = 0 := by simp [PZ]
    rw [hPZ1, zero_mul] at h
    exact h.symm
  -- hence the Wronskian vanishes off the singular point
  have hW : ∀ z ∈ Metric.ball (1 : ℂ) δ', z ≠ 1 → wron f uh z = 0 := by
    intro z hz hz1
    have h := hC z hz
    rw [hC0] at h
    exact (mul_eq_zero.mp h).resolve_left (PZ_ne_zero_of_mem_ball_one hδ'89 hz hz1)
  -- on a small disc around `1` where `uh` does not vanish, `f / uh` is holomorphic with
  -- vanishing derivative, hence `f = c · uh` there
  obtain ⟨ρ, hρ, hρsub, hρne⟩ := exists_ball_uh_ne_zero hδ'
  obtain ⟨c, hc⟩ := exists_smul_of_wron_eq_zero hρ (hf.mono hρsub) (huhd'.mono hρsub) hρne
    (fun z hz hz1 => hW z (hρsub hz) hz1)
  -- and the identity theorem extends the proportionality to the whole disc
  refine ⟨c, ?_⟩
  have h1mem : (1 : ℂ) ∈ Metric.ball (1 : ℂ) δ' := Metric.mem_ball_self hδ'
  have hAnF : AnalyticOnNhd ℂ f (Metric.ball (1 : ℂ) δ') :=
    (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2 hf
  have hAnG : AnalyticOnNhd ℂ (fun z : ℂ => c * uh z) (Metric.ball (1 : ℂ) δ') :=
    ((differentiableOn_const c).mul huhd').analyticOnNhd Metric.isOpen_ball
  have hev : f =ᶠ[𝓝 (1 : ℂ)] fun z : ℂ => c * uh z := by
    filter_upwards [Metric.ball_mem_nhds (1 : ℂ) hρ] with z hz
    exact hc z hz
  intro z hz
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hAnF hAnG
    (convex_ball (1 : ℂ) δ').isPreconnected h1mem hev hz

end Work.A14D
