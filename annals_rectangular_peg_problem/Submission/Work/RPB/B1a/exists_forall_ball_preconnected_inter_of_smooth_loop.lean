import Mathlib
import Submission.Work.RPB.B1a.Defs
import Submission.Work.RPB.B1a.HalfBallDefs
import Submission.Work.RPB.B1a.halfBall_up_down_preconnected
import Submission.Work.RPB.B1a.local_identification_of_smooth_loop
import Submission.Work.RPB.Port.Drive.curve_localSep
import Submission.Work.RPB.Port.Drive.curve_straightening

namespace Work.RPB.B1a

open Complex Set Metric
open scoped ContDiff Real

/-- **The domain of a smooth Jordan loop is locally a half-disk.**  If `D` is an open connected
set whose frontier is the image of the smooth loop `v`, then near any point `p` of the loop the
intersection `D ∩ ball p ρ` is preconnected, uniformly for all small `ρ`.

The proof combines two independent inputs: the local identification of `D ∩ ball p ρ` with one of
the two "straightening half-balls" `local_identification_of_smooth_loop`, and the elementary
analysis fact that both half-balls are preconnected (`halfBall_up_down_preconnected`). -/
theorem exists_forall_ball_preconnected_inter_of_smooth_loop (v : ℝ → ℂ) (hv : Work.RPB.B1a.IsSmoothLoop v)
    {D : Set ℂ} (hDo : IsOpen D) (hDc : IsConnected D)
    (hDfr : closure D \ interior D = Set.range v) {p : ℂ} (hp : p ∈ Set.range v) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → IsPreconnected (D ∩ Metric.ball p ρ) := by
  obtain ⟨t₀, ht₀⟩ := hp
  have hw : deriv v t₀ ≠ 0 := hv.2.2.2 t₀
  obtain ⟨ρ₁, hρ₁pos, hB⟩ := local_identification_of_smooth_loop v hv t₀
  have hg0 : (fun x : ℝ => v (t₀ + x) - v t₀) 0 = 0 := by simp
  have hgd : HasDerivAt (fun x : ℝ => v (t₀ + x) - v t₀) (deriv v t₀) 0 := by
    have hv' : HasDerivAt v (deriv v t₀) t₀ := (hv.1.differentiable (by simp) t₀).hasDerivAt
    have hcomp' : HasDerivAt (fun x : ℝ => v (t₀ + x)) (deriv v t₀) 0 :=
      HasDerivAt.comp_const_add t₀ 0 (by simpa using hv')
    exact HasDerivAt.sub_const (v t₀) hcomp'
  have hg2 : ContDiff ℝ 2 (fun x : ℝ => v (t₀ + x) - v t₀) := by
    have hv2 : ContDiff ℝ 2 v := hv.1.of_le (by norm_num)
    have hcomp2 : ContDiff ℝ 2 (fun x : ℝ => v (t₀ + x)) :=
      hv2.comp (by fun_prop : ContDiff ℝ 2 (fun x : ℝ => t₀ + x))
    exact ContDiff.sub hcomp2 contDiff_const
  obtain ⟨ρ₀A, hρ₀Apos, hA⟩ :=
    halfBall_up_down_preconnected (fun x : ℝ => v (t₀ + x) - v t₀) (deriv v t₀) hw hg0 hgd hg2
  refine ⟨min ρ₁ ρ₀A, lt_min hρ₁pos hρ₀Apos, ?_⟩
  intro ρ hρ hρle
  have hρ₁ : ρ ≤ ρ₁ := le_trans hρle (min_le_left _ _)
  have hρA : ρ ≤ ρ₀A := le_trans hρle (min_le_right _ _)
  have hcont : Continuous (straightenMap v t₀) := by
    unfold straightenMap
    exact (hv.1.continuous.comp (continuous_const.add continuous_fst)).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  rw [← ht₀]
  rcases hB ρ hρ hρ₁ D hDo hDc hDfr with h | h
  · rw [h]
    exact (hA ρ hρ hρA).1.image _ hcont.continuousOn
  · rw [h]
    exact (hA ρ hρ hρA).2.image _ hcont.continuousOn

end Work.RPB.B1a
