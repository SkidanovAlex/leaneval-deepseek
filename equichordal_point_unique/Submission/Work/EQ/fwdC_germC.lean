import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.HeteroGerm
import Submission.Work.EQ.HeteroChain
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.germC_apply_ne
import Submission.Work.EQ.H0_tail_bounded

/-!
# The principal forward branch acts on the stable germ by scaling the parameter

`fwdC a (germC a h u) = germC a h (λ u)` for all `u` in a neighbourhood of `0`, where
`λ = eqLam a = (1-a)/(1+a)`.

The proof is by continuation along the connected ball.  On a small ball the stable germ is
`RegPair`-related to its image under `u ↦ λ u`, so by `fwd_pair_dichotomy` the point
`germC a h (λ u)` is *either* the principal forward branch *or* the other one; the two are
separated by the distance `1` (`fwd_branch_separation`) and the choice is continuous in `u`,
hence constant on the connected ball; it is the principal one at `u = 0`.
-/

namespace Work.EQ

open Complex Metric Filter
open scoped Topology

noncomputable section

lemma continuous_bsq : Continuous bsq := by
  change Continuous (fun P : ℂ × ℂ => P.1 ^ 2 + P.2 ^ 2)
  fun_prop

lemma continuous_subO2 (a : ℝ) : Continuous (subO2 a) := by
  change Continuous (fun P : ℂ × ℂ => (P.1 - ((a / 2 : ℝ) : ℂ), P.2))
  fun_prop

/-- The principal forward branch fixes `A₁ = (-1/2, 0)`. -/
theorem fwdC_neg_half {a : ℝ} (ha0 : 0 < a) :
    fwdC a ((-1 / 2 : ℂ), (0 : ℂ)) = ((-1 / 2 : ℂ), (0 : ℂ)) := by
  have hcpos : (0 : ℝ) < (1 + a) / 2 := by linarith
  have hcne : (((1 + a) / 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hcpos)
  have hbrho : brho (subO2 a ((-1 / 2 : ℂ), (0 : ℂ))) = (((1 + a) / 2 : ℝ) : ℂ) := by
    rw [brho, subO2, bsq]
    have hsq : ((-1 / 2 : ℂ) - ((a / 2 : ℝ) : ℂ)) ^ 2 + (0 : ℂ) ^ 2
        = ((((1 + a) / 2) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hsq, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ ((1 + a) / 2) ^ 2) (1 / 2)]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (le_of_lt hcpos)]
  have hsub : subO2 a ((-1 / 2 : ℂ), (0 : ℂ)) = (-(((1 + a) / 2 : ℝ) : ℂ), (0 : ℂ)) := by
    rw [subO2]; congr 1; push_cast; ring
  have key : fwdC a ((-1 / 2 : ℂ), (0 : ℂ)) =
      -(((-1 / 2 : ℂ), (0 : ℂ))) +
        ((((1 + a) / 2 : ℝ) : ℂ))⁻¹ • (-(((1 + a) / 2 : ℝ) : ℂ), (0 : ℂ)) := by
    rw [fwdC_eq, hbrho, hsub]
  have hsc : ((((1 + a) / 2 : ℝ) : ℂ))⁻¹ • (-(((1 + a) / 2 : ℝ) : ℂ), (0 : ℂ))
      = ((-1 : ℂ), (0 : ℂ)) := by
    simp only [Prod.smul_mk, smul_eq_mul]
    rw [mul_neg, inv_mul_cancel₀ hcne]
    simp
  rw [key, hsc]
  refine Prod.ext ?_ ?_ <;> norm_num

/-- There is a ball around `0` on which the bilinear square of `germC - O₂` stays in the slit
plane (hence `brho` is analytic/continuous there). -/
theorem exists_ball_bsq_slitPlane {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ,
      bsq (subO2 a (germC a h u)) ∈ Complex.slitPlane := by
  obtain ⟨ρg, hρg, hAnC, hC0, -, -, -⟩ := germC_facts ha0 ha1 hh
  have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρg := by simpa using hρg
  have hgc0 : ContinuousAt (fun u => germC a h u) 0 := (hAnC 0 hmem).continuousAt
  have hcont : ContinuousAt (fun u => bsq (subO2 a (germC a h u))) 0 := by
    have h1 : ContinuousAt (fun u => subO2 a (germC a h u)) 0 := by
      have := (continuous_subO2 a).continuousAt.comp hgc0
      simpa [Function.comp_def] using this
    have h2 := continuous_bsq.continuousAt.comp h1
    simpa [Function.comp_def] using h2
  have hval : bsq (subO2 a (germC a h 0)) ∈ Complex.slitPlane := by
    rw [hC0]
    have hb : bsq (subO2 a ((-1 / 2 : ℂ), (0 : ℂ))) = ((((1 + a) / 2) ^ 2 : ℝ) : ℂ) := by
      rw [bsq, subO2]; push_cast; ring
    rw [hb]
    exact Complex.ofReal_mem_slitPlane.mpr (by positivity)
  have hev : ∀ᶠ u in 𝓝 (0 : ℂ), bsq (subO2 a (germC a h u)) ∈ Complex.slitPlane :=
    hcont.eventually (Complex.isOpen_slitPlane.mem_nhds hval)
  exact exists_ball_of_eventually hev

/-- Continuity of `u ↦ brho (subO2 (germC u))` on a ball where the base stays in the slit plane. -/
theorem continuousOn_brho_subO2_germC {a : ℝ} {h : ℂ → ℂ} {ρ : ℝ}
    (hgc : ContinuousOn (fun u => germC a h u) (Metric.ball (0 : ℂ) ρ))
    (hslit : ∀ u ∈ Metric.ball (0 : ℂ) ρ,
      bsq (subO2 a (germC a h u)) ∈ Complex.slitPlane) :
    ContinuousOn (fun u => brho (subO2 a (germC a h u))) (Metric.ball (0 : ℂ) ρ) := by
  have hw : ContinuousOn (fun u => bsq (subO2 a (germC a h u))) (Metric.ball (0 : ℂ) ρ) :=
    continuous_bsq.comp_continuousOn ((continuous_subO2 a).comp_continuousOn hgc)
  have h := hw.cpow_const (b := (1 / 2 : ℂ)) hslit
  simpa [brho] using h

/-- Continuity of the principal forward branch composed with the stable germ. -/
theorem continuousOn_fwdC_germC {a : ℝ} {h : ℂ → ℂ} {ρ : ℝ}
    (hgc : ContinuousOn (fun u => germC a h u) (Metric.ball (0 : ℂ) ρ))
    (hslit : ∀ u ∈ Metric.ball (0 : ℂ) ρ,
      bsq (subO2 a (germC a h u)) ∈ Complex.slitPlane) :
    ContinuousOn (fun u => fwdC a (germC a h u)) (Metric.ball (0 : ℂ) ρ) := by
  have hbrho := continuousOn_brho_subO2_germC hgc hslit
  have hne : ∀ u ∈ Metric.ball (0 : ℂ) ρ, brho (subO2 a (germC a h u)) ≠ 0 :=
    fun u hu => brho_ne_zero (Complex.slitPlane_ne_zero (hslit u hu))
  have hinv : ContinuousOn (fun u => (brho (subO2 a (germC a h u)))⁻¹)
      (Metric.ball (0 : ℂ) ρ) := hbrho.inv₀ hne
  have hsub : ContinuousOn (fun u => subO2 a (germC a h u)) (Metric.ball (0 : ℂ) ρ) :=
    (continuous_subO2 a).comp_continuousOn hgc
  have hrew : (fun u => fwdC a (germC a h u)) =
      fun u => -germC a h u + (brho (subO2 a (germC a h u)))⁻¹ • subO2 a (germC a h u) := by
    funext u; rw [fwdC_eq]
  rw [hrew]
  exact (hgc.neg).add (hinv.smul hsub)

/-- Continuity of the other forward branch composed with the stable germ. -/
theorem continuousOn_fwdAlt_germC {a : ℝ} {h : ℂ → ℂ} {ρ : ℝ}
    (hgc : ContinuousOn (fun u => germC a h u) (Metric.ball (0 : ℂ) ρ))
    (hslit : ∀ u ∈ Metric.ball (0 : ℂ) ρ,
      bsq (subO2 a (germC a h u)) ∈ Complex.slitPlane) :
    ContinuousOn (fun u => fwdAlt a (germC a h u)) (Metric.ball (0 : ℂ) ρ) := by
  have hbrho := continuousOn_brho_subO2_germC hgc hslit
  have hne : ∀ u ∈ Metric.ball (0 : ℂ) ρ, brho (subO2 a (germC a h u)) ≠ 0 :=
    fun u hu => brho_ne_zero (Complex.slitPlane_ne_zero (hslit u hu))
  have hinv : ContinuousOn (fun u => (brho (subO2 a (germC a h u)))⁻¹)
      (Metric.ball (0 : ℂ) ρ) := hbrho.inv₀ hne
  have hsub : ContinuousOn (fun u => subO2 a (germC a h u)) (Metric.ball (0 : ℂ) ρ) :=
    (continuous_subO2 a).comp_continuousOn hgc
  have hrew : (fun u => fwdAlt a (germC a h u)) =
      fun u => -germC a h u - (brho (subO2 a (germC a h u)))⁻¹ • subO2 a (germC a h u) := by
    funext u; rw [fwdAlt]
  rw [hrew]
  exact (hgc.neg).sub (hinv.smul hsub)

theorem fwdC_germC {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ} {Γ : ℝ → ℂ}
    (hh : IsStableGerm a h r) (hΓ : IsHeteroclinic a h r Γ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ,
      fwdC a (germC a h u) = germC a h ((eqLam a : ℂ) * u) := by
  obtain ⟨ρg, hρg, hAnC, hC0, hRP, hInjY, hderivY⟩ := germC_facts ha0 ha1 hh
  obtain ⟨ρs, hρs, hslitS⟩ := exists_ball_bsq_slitPlane ha0 ha1 hh
  have hρpos : 0 < min ρg ρs := lt_min hρg hρs
  have hρle_g : min ρg ρs ≤ ρg := min_le_left _ _
  have hρle_s : min ρg ρs ≤ ρs := min_le_right _ _
  have hslit : ∀ u ∈ Metric.ball (0 : ℂ) (min ρg ρs),
      bsq (subO2 a (germC a h u)) ∈ Complex.slitPlane :=
    fun u hu => hslitS u (Metric.ball_subset_ball hρle_s hu)
  have hgc : ContinuousOn (fun u => germC a h u) (Metric.ball (0 : ℂ) (min ρg ρs)) :=
    hAnC.continuousOn.mono (Metric.ball_subset_ball hρle_g)
  refine ⟨min ρg ρs, hρpos, ?_⟩
  intro u hu
  have hl0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  -- continuity of `u ↦ germC (λ u)`
  have hgcl : ContinuousOn (fun w => germC a h ((eqLam a : ℂ) * w))
      (Metric.ball (0 : ℂ) (min ρg ρs)) := by
    have hlin : ContinuousOn (fun w : ℂ => (eqLam a : ℂ) * w) (Metric.ball (0 : ℂ) (min ρg ρs)) :=
      (by fun_prop : Continuous fun w : ℂ => (eqLam a : ℂ) * w).continuousOn
    refine ContinuousOn.comp hAnC.continuousOn hlin ?_
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx ⊢
    exact lt_of_lt_of_le (norm_mul_lt_of_lt hl0 hl1 hρpos hx) hρle_g
  have hphi : ContinuousOn
      (fun w => ‖germC a h ((eqLam a : ℂ) * w) - fwdC a (germC a h w)‖)
      (Metric.ball (0 : ℂ) (min ρg ρs)) :=
    (hgcl.sub (continuousOn_fwdC_germC hgc hslit)).norm
  -- the dichotomy: the distance is either `0` or at least `1`
  have hkey : ∀ w ∈ Metric.ball (0 : ℂ) (min ρg ρs),
      ‖germC a h ((eqLam a : ℂ) * w) - fwdC a (germC a h w)‖ = 0 ∨
      1 ≤ ‖germC a h ((eqLam a : ℂ) * w) - fwdC a (germC a h w)‖ := by
    intro w hw
    have hwg : w ∈ Metric.ball (0 : ℂ) ρg := Metric.ball_subset_ball hρle_g hw
    obtain ⟨⟨hEq, hPnd, hQnd⟩, -⟩ := hRP w hwg
    rcases fwd_pair_dichotomy hEq hPnd with hcase | hcase
    · left; rw [hcase]; simp
    · right
      rw [hcase]
      have h2 : ‖fwdAlt a (germC a h w) - fwdC a (germC a h w)‖
          = ‖fwdC a (germC a h w) - fwdAlt a (germC a h w)‖ := by
        rw [show fwdAlt a (germC a h w) - fwdC a (germC a h w)
            = -(fwdC a (germC a h w) - fwdAlt a (germC a h w)) by rw [neg_sub]]
        exact norm_neg _
      rw [h2]
      exact fwd_branch_separation a (germC a h w) hPnd
  have hphi_ne : ∀ w ∈ Metric.ball (0 : ℂ) (min ρg ρs),
      ‖germC a h ((eqLam a : ℂ) * w) - fwdC a (germC a h w)‖ ≠ 1 / 2 := by
    intro w hw hc
    rcases hkey w hw with h | h <;> linarith
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (min ρg ρs) := by
    simpa using hρpos
  have hphi0 : ‖germC a h ((eqLam a : ℂ) * 0) - fwdC a (germC a h 0)‖ < 1 / 2 := by
    rw [mul_zero, hC0, fwdC_neg_half ha0]
    simp
  have hpre : IsPreconnected (Metric.ball (0 : ℂ) (min ρg ρs)) :=
    (convex_ball (0 : ℂ) (min ρg ρs)).isPreconnected
  have hlt := hpre.gt_of_ne hphi hphi_ne ⟨0, h0mem, hphi0⟩ (x := u) hu
  have hzero : ‖germC a h ((eqLam a : ℂ) * u) - fwdC a (germC a h u)‖ = 0 := by
    rcases hkey u hu with h | h
    · exact h
    · linarith
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

end

end Work.EQ
