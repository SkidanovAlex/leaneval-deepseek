import Mathlib
import Submission.Work.RPB1a.differentiableOn_of_compl_sphere
import Submission.Work.RPB1a.Caratheodory.ReflDefs
import Submission.Work.RPB1a.Caratheodory.mem_closure_ball_sphere_diff
import Submission.Work.RPB1a.Caratheodory.differentiableOn_diskReflect_off_sphere
import Submission.Work.RPB1a.Caratheodory.continuousOn_diskReflect

namespace Work.RPB1a.Caratheodory

open Complex Set Metric
open scoped ContDiff Real Topology ComplexConjugate

/-- A holomorphic function `f` on the unit disc that is continuous on the closed disc and injective
on the open disc cannot be constant on a relatively open nonempty piece of the unit circle.

Suppose `f ≡ a` on `V ∩ sphere 0 1` with `V` open.  Around a point `z₀` of that set the *reflection*
`diskReflect f a` (equal to `f - a` inside the circle and to `conj (f (1 / conj z)) - conj a`
outside) is continuous (both branches tend to `0` on the arc) and holomorphic off the circle, so by
Painlevé removability across the circle it is holomorphic near `z₀`; it vanishes on the arc, which
accumulates at `z₀`, so it vanishes identically on a ball around `z₀` by the identity theorem.  In
particular `f ≡ a` on a nonempty open piece of the disc, whence `f ≡ a` on the whole disc by the
identity theorem again, contradicting injectivity (`0` and `1/2` have the same image). -/
theorem not_eqOn_const_sphere_of_injOn {f : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hne : (V ∩ sphere 0 1).Nonempty) (a : ℂ)
    (hc : ContinuousOn f (closedBall 0 1)) (hd : DifferentiableOn ℂ f (ball 0 1))
    (hi : InjOn f (ball 0 1)) : ¬ EqOn f (fun _ => a) (V ∩ sphere 0 1) := by
  intro hf
  obtain ⟨z₀, hz₀⟩ := hne
  have hz₀V : z₀ ∈ V := hz₀.1
  have hz₀sph : z₀ ∈ sphere 0 1 := hz₀.2
  have hz₀norm : ‖z₀‖ = 1 := by
    have h := mem_sphere.mp hz₀sph
    rwa [dist_eq_norm, sub_zero] at h
  -- a ball around `z₀` contained in `V`
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hz₀V)
  set δ : ℝ := min δ₀ 1 with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos one_pos
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hδle1 : δ ≤ 1 := min_le_right _ _
  have hballV : ball z₀ δ ⊆ V := fun z hz => hδ₀sub (ball_subset_ball hδle hz)
  have hsph : ∀ z : ℂ, z ∈ sphere 0 1 → dist z z₀ < δ → f z = a := by
    intro z hzsph hzdist
    have hzball : z ∈ ball z₀ δ := by rwa [mem_ball]
    exact hf ⟨hballV hzball, hzsph⟩
  -- the reflection is holomorphic on `ball z₀ δ`, by removability across the circle
  have hcont : ContinuousOn (diskReflect f a) (ball z₀ δ) := continuousOn_diskReflect hc hsph
  have hdiff : DifferentiableOn ℂ (diskReflect f a) (ball z₀ δ \ sphere 0 1) :=
    differentiableOn_diskReflect_off_sphere a hd
  have hG : DifferentiableOn ℂ (diskReflect f a) (ball z₀ δ) :=
    Work.RPB1a.differentiableOn_of_compl_sphere isOpen_ball hcont hdiff
  have han : AnalyticOnNhd ℂ (diskReflect f a) (ball z₀ δ) :=
    (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).mpr hG
  have hpre : IsPreconnected (ball z₀ δ) := (convex_ball z₀ δ).isPreconnected
  have hz₀mem : z₀ ∈ ball z₀ δ := mem_ball_self hδpos
  -- `z₀` is an accumulation point of the arc on which the reflection vanishes
  have hacc : z₀ ∈ closure ({u : ℂ | diskReflect f a u = 0} \ {z₀}) := by
    refine closure_mono ?_ (mem_closure_ball_sphere_diff hz₀sph hδpos)
    rintro z ⟨⟨hzb, hzsph⟩, hzne⟩
    refine ⟨?_, hzne⟩
    have hza : f z = a := hf ⟨hballV hzb, hzsph⟩
    have hznorm : ‖z‖ = 1 := by
      have h := mem_sphere.mp hzsph
      rwa [dist_eq_norm, sub_zero] at h
    show diskReflect f a z = 0
    rw [diskReflect_of_le_one (le_of_eq hznorm), hza, sub_self]
  have hzero : EqOn (diskReflect f a) 0 (ball z₀ δ) :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure han hpre hz₀mem hacc
  -- hence `f = a` on `ball z₀ δ ∩ ball 0 1`
  have hfin : ∀ z : ℂ, z ∈ ball z₀ δ → z ∈ ball 0 1 → f z = a := by
    intro z hzb hz1
    have hzle : ‖z‖ ≤ 1 := by
      have h := mem_ball.mp hz1
      rw [dist_eq_norm, sub_zero] at h
      exact le_of_lt h
    have h0 := hzero hzb
    rw [diskReflect_of_le_one hzle] at h0
    exact sub_eq_zero.mp h0
  -- an explicit point of that intersection
  set t : ℝ := min δ 1 / 2 with htdef
  have htpos : 0 < t := by
    have : 0 < min δ 1 := lt_min hδpos one_pos
    rw [htdef]; linarith
  have htδ : t < δ := by
    have h : t ≤ δ / 2 := by rw [htdef]; linarith [min_le_left δ 1]
    linarith
  have ht1 : t < 1 := by
    have h : t ≤ 1 / 2 := by rw [htdef]; linarith [min_le_right δ 1]
    linarith
  set w : ℂ := ((1 - t : ℝ) : ℂ) * z₀ with hwdef
  have hw1 : w ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_eq_norm, sub_zero, hwdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      hz₀norm, mul_one, abs_of_pos (by linarith : (0 : ℝ) < 1 - t)]
    linarith
  have hwδ : w ∈ ball z₀ δ := by
    rw [mem_ball, dist_eq_norm, hwdef]
    have hsub : z₀ - ((1 - t : ℝ) : ℂ) * z₀ = (t : ℂ) * z₀ := by push_cast; ring
    rw [norm_sub_rev, hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, hz₀norm, mul_one,
      abs_of_pos htpos]
    linarith
  -- the identity theorem on the unit disc
  have hfa : EqOn (fun z : ℂ => f z - a) 0 (ball (0 : ℂ) 1) := by
    have hd2 : DifferentiableOn ℂ (fun z : ℂ => f z - a) (ball (0 : ℂ) 1) := hd.sub_const a
    have han2 : AnalyticOnNhd ℂ (fun z : ℂ => f z - a) (ball (0 : ℂ) 1) :=
      (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).mpr hd2
    have hpre2 : IsPreconnected (ball (0 : ℂ) 1) := (convex_ball (0 : ℂ) 1).isPreconnected
    refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero han2 hpre2 hw1 ?_
    have hU : ball z₀ δ ∩ ball (0 : ℂ) 1 ∈ 𝓝 w :=
      Filter.inter_mem (isOpen_ball.mem_nhds hwδ) (isOpen_ball.mem_nhds hw1)
    filter_upwards [hU] with z hz
    exact sub_eq_zero.mpr (hfin z hz.1 hz.2)
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self (by norm_num)
  have h12mem : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_eq_norm, sub_zero]; norm_num
  have h0a : f 0 = a := sub_eq_zero.mp (hfa h0mem)
  have h12a : f (1 / 2) = a := sub_eq_zero.mp (hfa h12mem)
  exact absurd (hi h0mem h12mem (by rw [h0a, h12a])) (by norm_num)

end Work.RPB1a.Caratheodory
