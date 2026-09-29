import Mathlib
import Submission.Work.TMC14Core.RatRot

/-!
# The lifted rotation number at a rational frequency is the average of the `q`-step one

For `α = p/q` the Prüfer `q`-step map `qMap p q lam E x` is the monodromy of the cocycle over a
period, and its rotation number `rotQ p q lam E x` is a function of the phase `x`.  The lifted
rotation number `rotLift α lam E` of the *full* cocycle is the mean over the phases of that
`q`-step rotation number, normalised by `q`:

  `rotLift (p/q) lam E = (1/q) * ∫₀¹ rotQ p q lam E x dx`.

The proof passes to the subsequence `n = q·m` of the defining limit of `rotLift` (which exists by
Fekete, `rotLift_tendsto`) and uses the `1/m` uniform-in-`x` rate of convergence of the `q`-step
rotation numbers (`rotQ_rate`) to interchange the limit over `m` with the integral over `x`.
-/

open MeasureTheory Filter Topology
open scoped Topology

noncomputable section

namespace Work.TMC14Core

/-- The `m`-th `q`-iterate `x ↦ qIter p q lam E x m` is continuous in the space variable. -/
theorem qIter_continuous_x (p : ℤ) (q : ℕ) (lam E : ℝ) (hq : 1 ≤ q) (m : ℕ) :
    Continuous (fun x : ℝ => qIter p q lam E x m) := by
  have h : (fun x : ℝ => qIter p q lam E x m)
      = fun x : ℝ => Work.TMContract.pruferIter ((p : ℝ) / (q : ℝ)) lam E (q * m) x 0 := by
    funext x
    show (qMap p q lam E x)^[m] 0
        = Work.TMContract.pruferIter ((p : ℝ) / (q : ℝ)) lam E (q * m) x 0
    exact (pruferIter_q_mul p q lam E x hq m 0).symm
  rw [h]
  exact (Work.TMComp.RotBasics.pruferIter_continuous_xt ((p : ℝ) / (q : ℝ)) lam E (q * m)).comp
    (continuous_id.prodMk continuous_const)

/-- `m ↦ qIter p q lam E x m / m` converges to `rotQ p q lam E x` *uniformly in* `x`. -/
theorem tendstoUniformly_qIter_div (p : ℤ) (q : ℕ) (lam E : ℝ) (hq : 1 ≤ q) :
    TendstoUniformly (fun m : ℕ => fun x : ℝ => qIter p q lam E x m / (m : ℝ))
      (fun x : ℝ => rotQ p q lam E x) atTop := by
  intro u hu
  rw [Metric.mem_uniformity_dist] at hu
  obtain ⟨ε, hε, hεu⟩ := hu
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (Iio_mem_nhds hε)]
      with m hm1 hmε
  intro x
  apply hεu
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (rotQ_rate p q lam E x hq hm1) hmε

/-- The `q`-step rotation number `x ↦ rotQ p q lam E x` is continuous. -/
theorem rotQ_continuous_x (p : ℤ) (q : ℕ) (lam E : ℝ) (hq : 1 ≤ q) :
    Continuous (fun x : ℝ => rotQ p q lam E x) :=
  (tendstoUniformly_qIter_div p q lam E hq).continuous
    ((Filter.Eventually.of_forall fun m =>
      (qIter_continuous_x p q lam E hq m).div_const _).frequently)

/-- The interchange of the limit `m → ∞` with the integral over the phase `x`. -/
theorem tendsto_integral_qIter_div (p : ℤ) (q : ℕ) (lam E : ℝ) (hq : 1 ≤ q) :
    Tendsto (fun m : ℕ => ∫ x in (0 : ℝ)..1, qIter p q lam E x m / (m : ℝ)) atTop
      (nhds (∫ x in (0 : ℝ)..1, rotQ p q lam E x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun m => norm_nonneg _) ?_
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hGm : IntervalIntegrable (fun x : ℝ => qIter p q lam E x m / (m : ℝ)) volume 0 1 :=
    ((qIter_continuous_x p q lam E hq m).div_const _).intervalIntegrable 0 1
  have hG : IntervalIntegrable (fun x : ℝ => rotQ p q lam E x) volume 0 1 :=
    (rotQ_continuous_x p q lam E hq).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_sub hGm hG]
  have hb : ∀ x ∈ Set.uIoc (0 : ℝ) 1,
      ‖qIter p q lam E x m / (m : ℝ) - rotQ p q lam E x‖ ≤ 1 / (m : ℝ) := by
    intro x _
    rw [Real.norm_eq_abs]
    have h := rotQ_rate p q lam E x hq hm
    rwa [abs_sub_comm] at h
  calc ‖∫ x in (0 : ℝ)..1, (qIter p q lam E x m / (m : ℝ) - rotQ p q lam E x)‖
      ≤ (1 / (m : ℝ)) * |1 - (0 : ℝ)| := intervalIntegral.norm_integral_le_of_norm_le_const hb
    _ = 1 / (m : ℝ) := by rw [sub_zero, abs_one, mul_one]

theorem rotLift_eq_rotQ (p : ℤ) (q : ℕ) (lam E : ℝ) (hq : 1 ≤ q) :
    Work.TMContract.rotLift ((p : ℝ) / (q : ℝ)) lam E
      = (1 / (q : ℝ)) * ∫ x in (0 : ℝ)..1, Work.TMC14Core.rotQ p q lam E x := by
  set α : ℝ := (p : ℝ) / (q : ℝ) with hα
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hq
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  -- The subsequence `n = q·m` of the defining limit of `rotLift`.
  have hqm : Tendsto (fun m : ℕ => q * m) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun m hm => le_trans hm (Nat.le_mul_of_pos_left m (by omega))⟩
  have hsub : Tendsto
      (fun m : ℕ => Work.TMComp.RotBasics.sn α lam E (q * m) / ((q * m : ℕ) : ℝ)) atTop
      (nhds (Work.TMContract.rotLift α lam E)) := by
    have hcomp := (Work.TMComp.RotBasics.rotLift_tendsto α lam E).comp hqm
    simpa [Function.comp_def, Work.TMComp.RotBasics.sn] using hcomp
  -- The integrals of the `q`-step rotation numbers.
  have hint : Tendsto (fun m : ℕ => ∫ x in (0 : ℝ)..1, qIter p q lam E x m / (m : ℝ)) atTop
      (nhds (∫ x in (0 : ℝ)..1, rotQ p q lam E x)) :=
    tendsto_integral_qIter_div p q lam E hq
  have hint' := hint.const_mul (1 / (q : ℝ))
  -- The two sequences agree eventually.
  have hev : (fun m : ℕ => Work.TMComp.RotBasics.sn α lam E (q * m) / ((q * m : ℕ) : ℝ))
      =ᶠ[atTop] (fun m : ℕ => (1 / (q : ℝ)) *
        ∫ x in (0 : ℝ)..1, qIter p q lam E x m / (m : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
    have hcast : ((q * m : ℕ) : ℝ) = (q : ℝ) * (m : ℝ) := by push_cast; ring
    have hsn : Work.TMComp.RotBasics.sn α lam E (q * m)
        = ∫ x in (0 : ℝ)..1, qIter p q lam E x m := by
      show (∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E (q * m) x 0)
        = ∫ x in (0 : ℝ)..1, qIter p q lam E x m
      apply intervalIntegral.integral_congr
      intro x _
      exact pruferIter_q_mul p q lam E x hq m 0
    calc Work.TMComp.RotBasics.sn α lam E (q * m) / ((q * m : ℕ) : ℝ)
        = (∫ x in (0 : ℝ)..1, qIter p q lam E x m) / ((q : ℝ) * (m : ℝ)) := by
          rw [hsn, hcast]
      _ = (1 / (q : ℝ)) * ((∫ x in (0 : ℝ)..1, qIter p q lam E x m) / (m : ℝ)) := by
          field_simp
      _ = (1 / (q : ℝ)) * ∫ x in (0 : ℝ)..1, qIter p q lam E x m / (m : ℝ) := by
          rw [intervalIntegral.integral_div]
  have hcongr := Tendsto.congr' hev.symm hint'
  exact tendsto_nhds_unique hsub hcongr

end Work.TMC14Core
