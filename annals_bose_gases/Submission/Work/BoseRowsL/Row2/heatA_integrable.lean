import Mathlib
import Submission.Work.BoseRowsL.Row2.hA_heat_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.Row2.heatA_integrable`

The **integrability** of the heat-kernel row of the `hA` bookkeeping: for `ℓ > 0` and the box
lattice `p n = Work.BoseBoxFock.kmomInt ℓ n`, the function

    t ↦ (ℓ³)⁻¹ ( Σ_n ĉ(p_n) e^{−t‖p_n‖²} − ĉ(0) ) ,     ĉ = Work.BoseFixR.chat h,

is integrable on `(0, ∞)` as soon as `Σ_n |ĉ(p_n)| / ‖p_n‖²` converges.  This is the
integrability input of the subordination identity `Work.BoseRowsL.Row2.hA_heat_integral`: the
pointwise integral `∫_{t>0} e^{−tc} dt = c⁻¹` gives, termwise, `∫_{t>0} |ĉ(p_n)| e^{−t‖p_n‖²} dt
= |ĉ(p_n)|/‖p_n‖²`, whose total is exactly the hypothesis.

The proof is the abstract statement `integrable_heat_tsum`: for a countable index type `ι` with a
distinguished point `z` at which `C` vanishes and `C > 0` elsewhere, `Σ_n |A n|/C n < ∞` implies
integrability of `t ↦ (Σ_n A n e^{−t C n}) − A z` on `(0, ∞)`.  The family is written as the
pointwise sum of the a.e. integrable summands `F n t = if n = z then 0 else A n e^{−t C n}`
(the point at `z` is subtracted), each of which is handled by Mathlib's `L^1`-summation theory:
the `L^1` norms `∫_{t>0} ‖F n t‖ = |A n|/C n` are summable by hypothesis, so the sum converges in
`L¹` (`MeasureTheory.Lp.coeFn_tsum`) and its pointwise a.e. representative is integrable.
-/

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal BigOperators Topology

namespace Work.BoseRowsL.Row2

/-- **Integrability of the subordinated heat sum.**  Let `ι` be countable, `z : ι` a distinguished
index with `C z = 0`, `C` positive off `z`, and `Σ_n |A n| / C n < ∞`.  Then

    t ↦ (Σ_n A n e^{−t C n}) − A z

is integrable for Lebesgue measure restricted to `(0, ∞)`. -/
theorem integrable_heat_tsum {ι : Type*} [Countable ι] {z : ι} {A C : ι → ℝ}
    (hC0 : C z = 0) (hCpos : ∀ n, n ≠ z → 0 < C n)
    (hsumm : Summable (fun n => |A n| / C n)) :
    Integrable (fun t : ℝ => (∑' n, A n * Real.exp (-(t * C n))) - A z)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  classical
  set μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ)) with hμ
  set F : ι → ℝ → ℝ := fun n t => if n = z then 0 else A n * Real.exp (-(t * C n)) with hF
  -- each summand (with the `z`-term removed) is integrable
  have hFint : ∀ n, Integrable (F n) μ := by
    intro n
    by_cases hn : n = z
    · rw [hF]
      simp only [hn]
      simp
    · refine ((exp_neg_integrableOn_Ioi (0 : ℝ) (b := C n) (hCpos n hn)).const_mul (A n)).congr ?_
      filter_upwards with s
      show A n * Real.exp (-C n * s) = F n s
      rw [hF]
      simp only [if_neg hn]
      rw [show -C n * s = -(s * C n) by ring]
  -- the `L¹` norm of each summand
  have hFnorm : ∀ n, (∫ t, ‖F n t‖ ∂μ) = |A n| / C n := by
    intro n
    by_cases hn : n = z
    · rw [show (fun t : ℝ => ‖F n t‖) = fun _ => (0 : ℝ) from funext (fun t => by
        rw [hF]; simp only [hn]; simp)]
      simp [hC0, hn]
    · have hpt : ∀ t, ‖F n t‖ = |A n| * Real.exp (-(t * C n)) := by
        intro t
        rw [hF]
        simp only [if_neg hn, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact HA.integral_mul_exp_neg (a := |A n|) (c := C n) (hCpos n hn)
  -- view the summands as elements of `L¹` and sum them there
  have hmemLp : ∀ n, MemLp (F n) 1 μ := fun n => memLp_one_iff_integrable.mpr (hFint n)
  set g : ι → Lp ℝ 1 μ := fun n => (hmemLp n).toLp (F n) with hg
  have hgnorm : ∀ n, ‖g n‖ₑ = ENNReal.ofReal (|A n| / C n) := by
    intro n
    rw [hg]
    show ‖(hmemLp n).toLp (F n)‖ₑ = _
    rw [Lp.enorm_toLp, eLpNorm_one_eq_lintegral_enorm]
    have hcongr : (fun t : ℝ => ‖F n t‖ₑ) = fun t : ℝ => ENNReal.ofReal ‖F n t‖ :=
      funext (fun t => (ofReal_norm (F n t)).symm)
    rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal (hFint n).norm
      (Filter.Eventually.of_forall (fun t => norm_nonneg (F n t))), hFnorm n]
    all_goals first | fun_prop | (apply Continuous.aestronglyMeasurable; fun_prop) | (apply Continuous.aemeasurable; fun_prop) | (apply Continuous.measurable; fun_prop) | measurability
  have hCnn : ∀ n, 0 ≤ C n := by
    intro n
    by_cases hn : n = z
    · rw [hn, hC0]
    · exact (hCpos n hn).le
  -- the `L¹` norms are summable, so the series converges in `L¹`
  have hsumm_enorm : (∑' n, ‖g n‖ₑ) ≠ ⊤ := by
    have h2 : (∑' n, ENNReal.ofReal (|A n| / C n)) = ENNReal.ofReal (∑' n, |A n| / C n) :=
      (ENNReal.ofReal_tsum_of_nonneg (f := fun n => |A n| / C n)
        (fun n => div_nonneg (abs_nonneg _) (hCnn n)) hsumm).symm
    rw [tsum_congr hgnorm, h2]
    exact ENNReal.ofReal_ne_top
  -- the `L¹` limit is an integrable representative of the pointwise series
  have hcoe : (fun t : ℝ => ⇑(∑' n, g n) t) =ᵐ[μ] (fun t : ℝ => ∑' n, ⇑(g n) t) :=
    MeasureTheory.Lp.coeFn_tsum (f := g) hsumm_enorm
  have hint1 : Integrable (fun t : ℝ => ⇑(∑' n, g n) t) μ :=
    memLp_one_iff_integrable.mp (Lp.memLp (∑' n, g n))
  have hint2 : Integrable (fun t : ℝ => ∑' n, ⇑(g n) t) μ := hint1.congr hcoe
  -- replace the `L¹` representatives by the summands themselves
  have hFF : (fun t : ℝ => ∑' n, ⇑(g n) t) =ᵐ[μ] (fun t : ℝ => ∑' n, F n t) := by
    filter_upwards [ae_all_iff.mpr (fun n => MemLp.coeFn_toLp (hmemLp n))] with t ht
    exact tsum_congr (fun n => ht n)
  have hint3 : Integrable (fun t : ℝ => ∑' n, F n t) μ := hint2.congr hFF
  -- and the pointwise series is the difference appearing in the statement
  have hfin : (fun t : ℝ => ∑' n, F n t) =ᵐ[μ]
      (fun t : ℝ => (∑' n, A n * Real.exp (-(t * C n))) - A z) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hsumm_t := HA.summable_heat ht hC0 hCpos hsumm
    have hsplit := hsumm_t.tsum_eq_add_tsum_ite z
    rw [hC0, mul_zero, neg_zero, Real.exp_zero, mul_one] at hsplit
    have h1 : (∑' n, F n t) = ∑' n, (if n = z then 0 else A n * Real.exp (-(t * C n))) :=
      tsum_congr (fun n => by rw [hF])
    rw [h1, hsplit]
    ring
  exact hint3.congr hfin

theorem heatA_integrable {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hsumm : Summable (fun n : Fin 3 → ℤ => |Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n)| / ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2)) :
    MeasureTheory.Integrable (fun t : ℝ => (ℓ ^ 3)⁻¹ * ((∑' n : Fin 3 → ℤ,
        Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n) * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))) - Work.BoseFixR.chat h 0))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hmain := integrable_heat_tsum (z := (0 : Fin 3 → ℤ))
    (A := fun n => Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n))
    (C := fun n => ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2)
    (by simp [HA.kmomInt_zero]) (fun n hn => HA.normSq_pos hℓ hn) hsumm
  rw [HA.kmomInt_zero] at hmain
  exact hmain.const_mul ((ℓ ^ 3)⁻¹)

end Work.BoseRowsL.Row2
