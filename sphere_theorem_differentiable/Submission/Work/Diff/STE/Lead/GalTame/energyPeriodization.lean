import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.tmA_props
import Submission.Work.Diff.STE.pd_periodization
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.B3.CSq_period_le_integral_deriv
import Submission.Work.Diff.STE.B3.boxIdx_iUnion
import Submission.Work.Diff.STE.B3.boxIdx_pairwiseDisjoint
import Submission.Work.Diff.STE.Lead.GalTame.boxSumIntegral
import Submission.Work.Diff.STE.Lead.GalTame.normSumSqSubsingleton

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

open MeasureTheory

/-! ## Auxiliary: the pointwise identity on the unit cube

The heart of the proof of `energyPeriodization`.  Let `f` be smooth with `tsupport f` inside the
open ball of radius `1/2`, and put `F = ((· : ℝ) : ℂ) ∘ f`.  For `x` in the half open unit cube
`(0,1]^n` the periodisation of `f` is the finite sum of the translates `F (· + k)`,
`k ∈ csqp_boxIdx (Fin n) = {-1,0}^n`, on a neighbourhood of `x`
(`Work.Diff.STE.csqp_periodization_eventuallyEq_sum_boxIdx`), so the same is true of the
complexification of `Work.Diff.STE.B3.tmPer f` — the real part commutes with the finite sum.
Differentiating and translating the argument gives

`∂^β (tmPer f) x = Σ_{k ∈ boxIdx} ∂^β F (x + k)`.

Finally, two distinct such translates cannot both lie in `tsupport F ⊆ ball 0 (1/2)`
(`Work.Diff.STE.B3.eq_of_mem_ball`), so at most one summand is non-zero, and the squared norm of
the sum is the sum of the squared norms (`normSumSqSubsingleton`). -/

/-- **The pointwise energy identity on the unit cube.**  For `x` in `(0,1]^n` the squared norm of
`∂^β` of the complexification of `tmPer f` is the sum, over the `2^n` translates of the unit cube
meeting the ball, of the squared norms of `∂^β` of the complexification of `f`. -/
lemma energyPointwise {n m : ℕ} (f : (Fin n → ℝ) → ℝ) (β : Fin m → Fin n)
    (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f)
    (hts : tsupport f ⊆ Metric.ball 0 (1 / 2)) :
    ∀ x ∈ Work.Diff.STE.unitCube (ι := Fin n),
      ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((Work.Diff.STE.B3.tmPer f y : ℝ) : ℂ)) x‖ ^ 2
        = ∑ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n),
            ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
              (x + Work.Diff.STE.iVec k)‖ ^ 2 := by
  have hf' : ContDiff ℝ (⊤ : ℕ∞) f := hf
  set F : (Fin n → ℝ) → ℂ := fun y => ((f y : ℝ) : ℂ) with hF
  have hFsmooth : ContDiff ℝ (⊤ : ℕ∞) F := Complex.ofRealCLM.contDiff.comp hf'
  have hFsupp : Function.support F ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    have hzf : f z ≠ 0 := by
      intro h0
      have hz0 : F z = 0 := by
        rw [hF]
        show ((f z : ℝ) : ℂ) = 0
        rw [h0]; simp
      exact hz hz0
    exact Work.Diff.STE.B3.ball_subset_cube (le_refl (1 / 2))
      (hts (subset_tsupport f (Function.mem_support.mpr hzf)))
  have hFts : tsupport F ⊆ Metric.ball 0 (1 / 2) := by
    have heq : Function.support F = Function.support f := by
      ext z; simp only [hF, Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
    show closure (Function.support F) ⊆ Metric.ball 0 (1 / 2)
    rw [heq]; exact hts
  intro x hx
  have hP := Work.Diff.STE.csqp_periodization_eventuallyEq_sum_boxIdx (ι := Fin n) hFsupp hx
  have hP' : (fun y : Fin n → ℝ => ∑' k : Fin n → ℤ, F (y + Work.Diff.STE.iVec k))
      =ᶠ[nhds x] (fun y => ∑ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n),
        F (y + Work.Diff.STE.iVec k)) := hP
  have hEv : (fun y : Fin n → ℝ => ((Work.Diff.STE.B3.tmPer f y : ℝ) : ℂ))
      =ᶠ[nhds x] (fun y => ∑ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n),
        F (y + Work.Diff.STE.iVec k)) := by
    have h1 : (fun y : Fin n → ℝ => ((Work.Diff.STE.B3.tmPer f y : ℝ) : ℂ))
        = fun y => (((∑' k : Fin n → ℤ, F (y + Work.Diff.STE.iVec k)).re : ℝ) : ℂ) := by
      funext y
      simp only [Work.Diff.STE.B3.tmPer, hF]
    rw [h1]
    filter_upwards [hP'] with y hy
    rw [hy, Complex.re_sum, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun k _ => by simp only [hF, Complex.ofReal_re])
  have hpd : Work.Diff.STE.pdVec m β
        (fun y : Fin n → ℝ => ((Work.Diff.STE.B3.tmPer f y : ℝ) : ℂ)) x
      = ∑ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n),
          Work.Diff.STE.pdVec m β F (x + Work.Diff.STE.iVec k) := by
    rw [Work.Diff.STE.csqp_pdVec_congr β hEv]
    rw [Work.Diff.STE.csqp_pdVec_finset_sum β _ (fun k y => F (y + Work.Diff.STE.iVec k)) x
      (fun k _ => hFsmooth.comp (contDiff_id.add contDiff_const))]
    exact Finset.sum_congr rfl (fun k _ => Work.Diff.STE.csqp_pdVec_comp_add_right β F _ x)
  rw [hpd]
  refine normSumSqSubsingleton _ _ ?_
  intro k hk k' hk' hkne hk'ne
  exact Work.Diff.STE.B3.eq_of_mem_ball (z := x) (le_refl (1 / 2))
    (hFts (Work.Diff.STE.csqp_support_pdList_subset_closure (List.ofFn β) F
      (Function.mem_support.mpr hkne)))
    (hFts (Work.Diff.STE.csqp_support_pdList_subset_closure (List.ofFn β) F
      (Function.mem_support.mpr hk'ne)))

/-- **The `L²` energy of the jets of a periodisation equals the whole-space energy of the function.**

For a smooth real-valued `f : (Fin n → ℝ) → ℝ` whose topological support is contained in the open
ball of radius `1/2`, the `L²(unitCube)` norm squared of the `m`-th jet of the periodisation
`Work.Diff.STE.B3.tmPer f` equals the whole-space (`L²(ℝⁿ)`) norm squared of the `m`-th jet of `f`:

`∫_{unitCube} ‖∂^m_β (tmPer f)‖² = ∫_{ℝⁿ} ‖∂^m_β f‖²`,

where the complexification `((· : ℝ) : ℂ)` is inserted because `pdVec` acts on `ℂ`-valued functions.

PROOF ROUTE.  `tmPer f = re ∘ (periodisation of the complexification of f)` by definition
(`Submission/Work/Diff/STE/B3/transport_tame_defs.lean`), and partial derivatives commute with the
periodisation: at every point `z` the periodisation agrees with a *finite* sum
`Σ_{m ∈ S} f (· + iVec m)` on a neighbourhood of `z`
(`Work.Diff.STE.B3.tmPer_eventuallyEq_finset`,
`Submission/Work/Diff/STE/B3/tmA_props.lean`), so `pdVec m β (tmPer f) z` is the sum of
`pdVec m β f (z + iVec m)` over the translates that meet the support (iterate
`pd_periodization`/`fderiv_comp_add_right`, or reuse the argument of
`Work.Diff.STE.B3.tmPer_pdR_le_tsupport` in `tmA_props.lean`, which proves the first-derivative
case).  Moreover, for `z` in the half-open cube `(-1/2,1/2]^n` at most *one* translate
`z + iVec m` lies in the open ball of radius `1/2`
(`Work.Diff.STE.B3.eq_of_mem_ball`, `Submission/Work/Diff/STE/B3/tmA_props.lean`), so the square of
the sum is the sum of the squares.  Therefore both sides are
`Σ_{m : Fin n → ℤ} ∫_{unitCube} ‖∂^m_β f (z + iVec m)‖²` (the translates of the support are
disjoint and each lies in exactly one translate of the cube; alternatively the cube integral may be
replaced by the integral over the half-open centred cube `(-1/2,1/2]^n` since the integrand is
`1`-periodic), which is `∫_{ℝⁿ} ‖∂^m_β f‖²` because the whole support of `f` is contained in
`⋃_{m} ((-1/2,1/2]^n + iVec m)`.  Helper facts already in the workspace:
`Work.Diff.STE.periodization_eq_self`, `pd_periodization`, `Work.Diff.STE.iVec`,
`Work.Diff.STE.B3.tmPer_eq_of_support`. -/
theorem energyPeriodization {n m : ℕ} (f : (Fin n → ℝ) → ℝ) (β : Fin m → Fin n)
    (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f)
    (hts : tsupport f ⊆ Metric.ball 0 (1 / 2)) :
    ∫ z in Work.Diff.STE.unitCube (ι := Fin n),
        ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ =>
          ((Work.Diff.STE.B3.tmPer f y : ℝ) : ℂ)) z‖ ^ 2
      = ∫ z : Fin n → ℝ,
        ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) z‖ ^ 2 := by
  have hf' : ContDiff ℝ (⊤ : ℕ∞) f := hf
  set F : (Fin n → ℝ) → ℂ := fun y => ((f y : ℝ) : ℂ) with hF
  have hFsmooth : ContDiff ℝ (⊤ : ℕ∞) F := Complex.ofRealCLM.contDiff.comp hf'
  have hFts : tsupport F ⊆ Metric.ball 0 (1 / 2) := by
    have heq : Function.support F = Function.support f := by
      ext z; simp only [hF, Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
    show closure (Function.support F) ⊆ Metric.ball 0 (1 / 2)
    rw [heq]; exact hts
  have hpdcd : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pdVec m β F) := by
    simpa only [Work.Diff.STE.pdVec] using
      Work.Diff.STE.csqp_contDiff_pdList_top (List.ofFn β) hFsmooth
  refine Eq.trans (b := ∫ z in Work.Diff.STE.unitCube (ι := Fin n),
      (∑ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n),
        ‖Work.Diff.STE.pdVec m β F (z + Work.Diff.STE.iVec k)‖ ^ 2)) ?_ ?_
  · refine setIntegral_congr_fun BesselCont.measSet_unitCube (fun z hz => ?_)
    have h := energyPointwise f β hf hts z hz
    simpa only [hF] using h
  · refine Eq.trans (b := ∫ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec m β F z‖ ^ 2) ?_ ?_
    · refine boxSumIntegral (fun z => ‖Work.Diff.STE.pdVec m β F z‖ ^ 2)
        (hpdcd.continuous.norm.pow 2) ?_
      intro z hz
      have hznot : z ∉ tsupport F := by
        intro hmem
        have h2 := hFts hmem
        rw [Metric.mem_ball, dist_zero_right] at h2
        linarith
      have h0 : Work.Diff.STE.pdVec m β F z = 0 := by
        by_contra hne
        exact hznot (Work.Diff.STE.csqp_support_pdList_subset_closure (List.ofFn β) F
          (Function.mem_support.mpr hne))
      rw [h0]; simp
    · rfl

end Work.Diff.STE.Lead.GalTame
