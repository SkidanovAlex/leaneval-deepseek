import Mathlib
import Submission.Work.A14D.H_cont
import Submission.Work.A14.defs
import Submission.Work.A14D.LC_setup
import Submission.Work.A14D.pullback_rel_disc_A
import Submission.Work.A14D.fourteen_coeff_bounds
import Submission.Work.A14D.preconnected_SU_diff_two

/-!
# `Work.A14D.SU_relation_two`

The `SU`-branch of the pullback relation of Theorem A, with the point `z = 2` removed from the
half-plane `SU`: given the `ℚ[y]`-relation `Σᵢ Pᵢ · fourteenᵢ = 0` among the fourteen `y`-series
and, for each `i`, a function `BU i` holomorphic on `SU \ {2}` agreeing with the pullback
`Σ' k [yᵏ] fourteenᵢ · (yC z)ᵏ` on `SU ∩ ball 0 (34/100) ∩ {Re z < 1/2}`, the relation
`Σᵢ Pᵢ(y(z))·BUᵢ(z) = 0` holds on all of `SU \ {2}`.

This is the exact analogue of the proved `Work.A14D.SU_relation`, but with the domain
`SU \ {2}` in place of the convex half plane `SU`.  The identity theorem
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` is applied on the *punctured*
half plane, which is preconnected (but not convex): the point `2` is deleted before the
continuation, and `Work.A14D.preconnected_SU_diff_two` supplies the connectivity.
-/

open Complex Metric Filter Polynomial
open scoped Topology BigOperators

noncomputable section
namespace Work.A14D

/-- `yC z = z²/(z−1)` is holomorphic on `SU`, which avoids its pole `1`. -/
private lemma yC_diffOn_SU : DifferentiableOn ℂ yC SU := by
  have h1 : (1 : ℂ) ∉ SU := by rw [mem_SU_iff]; norm_num
  unfold yC
  exact (differentiableOn_id.pow 2).div (differentiableOn_id.sub (differentiableOn_const 1))
    (fun z hz => sub_ne_zero.mpr (fun hz1 => h1 (by rwa [hz1] at hz)))

/-- `p(yC ·)` is holomorphic on `SU` for every polynomial `p ∈ ℚ[X]`. -/
private lemma pAtY_diffOn_SU (p : Polynomial ℚ) : DifferentiableOn ℂ (pAtY p) SU := by
  have h : pAtY p = fun z => ((p.map (algebraMap ℚ ℂ)).eval (yC z)) := by
    funext z
    rw [pAtY, Polynomial.eval₂_eq_eval_map]
  rw [h]
  exact (Polynomial.differentiable (p.map (algebraMap ℚ ℂ))).differentiableOn.comp yC_diffOn_SU
    (fun _ _ => Set.mem_univ _)

theorem SU_relation_two (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c)
    (P : Fin 14 → Polynomial ℚ)
    (hrel : ∑ i : Fin 14, (P i : PowerSeries ℚ) * Submission.CDTPlan.fourteen a b c i = 0)
    (BU : Fin 14 → ℂ → ℂ)
    (hBUd : ∀ i : Fin 14, DifferentiableOn ℂ (BU i) (SU \ ({2} : Set ℂ)))
    (hBUeq : ∀ i : Fin 14, ∀ z ∈ SU ∩ Metric.ball (0 : ℂ) ((34 : ℝ) / 100) ∩ {z : ℂ | z.re < 1 / 2},
      BU i z = ∑' k : ℕ, ((PowerSeries.coeff k (Submission.CDTPlan.fourteen a b c i) : ℚ) : ℂ)
          * (yC z) ^ k) :
    ∀ z ∈ SU \ ({2} : Set ℂ), ∑ i : Fin 14, pAtY (P i) z * BU i z = 0 := by
  have hbou := fourteen_coeff_bounds a b c h
  have hpull := pullback_rel_disc_A a b c h P hrel hbou
  have hFdiff : DifferentiableOn ℂ (fun z => ∑ i : Fin 14, pAtY (P i) z * BU i z)
      (SU \ ({2} : Set ℂ)) :=
    DifferentiableOn.fun_sum (fun i _ =>
      ((pAtY_diffOn_SU (P i)).mono Set.sdiff_subset).mul (hBUd i))
  have hFana : AnalyticOnNhd ℂ (fun z => ∑ i : Fin 14, pAtY (P i) z * BU i z)
      (SU \ ({2} : Set ℂ)) :=
    hFdiff.analyticOnNhd (isOpen_SU_H_cont.sdiff isClosed_singleton)
  -- the relation on the small disc, where the `BU i` are the pullback series
  have hzero_on : ∀ z ∈ SU ∩ Metric.ball (0 : ℂ) ((34 : ℝ) / 100) ∩ {z : ℂ | z.re < 1 / 2},
      (∑ i : Fin 14, pAtY (P i) z * BU i z) = 0 := by
    intro z hz
    obtain ⟨⟨hzSU, hzball⟩, hzre⟩ := hz
    have hnorm : ‖z‖ ≤ (34 : ℝ) / 100 := by
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero] at hzball
      exact le_of_lt hzball
    have hp := hpull z hnorm
    have hbu : ∀ i : Fin 14, BU i z = ∑' k : ℕ,
        ((PowerSeries.coeff k (Submission.CDTPlan.fourteen a b c i) : ℚ) : ℂ) * (yC z) ^ k :=
      fun i => hBUeq i z ⟨⟨hzSU, hzball⟩, hzre⟩
    rw [Finset.sum_congr rfl (fun i _ => by rw [hbu i])]
    simpa only [pAtY] using hp
  -- the base point `i/4` of the identity theorem
  have hz0SU : ((1 / 4 : ℂ) * Complex.I) ∈ SU := by
    rw [mem_SU_iff]; simp; norm_num
  have hz0ne : ((1 / 4 : ℂ) * Complex.I) ≠ (2 : ℂ) := by
    intro hcon
    have hre := congrArg Complex.re hcon
    simp at hre
  have hz0mem : ((1 / 4 : ℂ) * Complex.I) ∈ SU \ ({2} : Set ℂ) :=
    ⟨hz0SU, by simpa using hz0ne⟩
  have hz0T : ((1 / 4 : ℂ) * Complex.I) ∈
      SU ∩ Metric.ball (0 : ℂ) ((34 : ℝ) / 100) ∩ {z : ℂ | z.re < 1 / 2} := by
    refine ⟨⟨hz0SU, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq, sub_zero]
      have hh : ‖((1 / 4 : ℂ) * Complex.I)‖ = 1 / 4 := by
        rw [norm_mul, Complex.norm_I, mul_one]; norm_num
      rw [hh]; norm_num
    · simp
  have hev : (fun z => ∑ i : Fin 14, pAtY (P i) z * BU i z)
      =ᶠ[𝓝 ((1 / 4 : ℂ) * Complex.I)] 0 := by
    have hTopen : IsOpen (SU ∩ Metric.ball (0 : ℂ) ((34 : ℝ) / 100) ∩ {z : ℂ | z.re < 1 / 2}) :=
      (isOpen_SU_H_cont.inter Metric.isOpen_ball).inter (isOpen_lt continuous_re continuous_const)
    filter_upwards [hTopen.mem_nhds hz0T] with w hw
    simpa using hzero_on w hw
  have hfinal := hFana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    preconnected_SU_diff_two hz0mem hev
  intro z hz
  simpa using hfinal hz

end Work.A14D
