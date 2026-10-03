import Mathlib
import Submission.Work.KMTAreas.A7.lacDilTriVarDefs
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

noncomputable section

/-!
# From the `ℓ¹ ∩ ℓᵖ` bound to the `ℓᵖ` bound for `latVarSupR`

The martingale (Lépingle) estimate for the reversed-chain variation `latVarSupR r L τ h` is
naturally proved for *integrable* `h`.  This file upgrades such a bound to all `h ∈ ℓᵖ(ℤ)` by an
approximation argument: truncating `h` to the finite intervals `[-n,n]` produces integrable
functions `truncOn h n` converging pointwise to `h`, and `latVarSupR` is *pointwise lower
semicontinuous* in the input (it is a supremum of continuous functions of finitely many lattice
averages), so Fatou's lemma gives the bound in the limit.
-/

/-! ## Fatou for `ℝ≥0∞`-valued functions on `ℤ` -/

/-- **Fatou's lemma for the `ℒᵖ`-seminorm**, `ℝ≥0∞`-valued form.  If `U` is pointwise dominated by
the pointwise `liminf` of the sequence `u`, then `‖U‖_{ℓᵖ} ≤ liminf ‖u n‖_{ℓᵖ}`.  (The functions
live on `ℤ` with the counting measure, so all measurability hypotheses are automatic.) -/
private lemma eLpNorm_le_liminf_of_le {p : ℝ} (hp : 0 < p) {u : ℕ → ℤ → ℝ≥0∞} {U : ℤ → ℝ≥0∞}
    (hU : ∀ x, U x ≤ liminf (fun n => u n x) atTop) :
    eLpNorm U (ENNReal.ofReal p) (Measure.count : Measure ℤ)
      ≤ liminf (fun n => eLpNorm (u n) (ENNReal.ofReal p) (Measure.count : Measure ℤ)) atTop := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hpT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := AEStronglyMeasurable.of_discrete) hp0 hpT,
    ENNReal.toReal_ofReal hp.le]
  have hLM : (∫⁻ x, ‖U x‖ₑ ^ p ∂(Measure.count : Measure ℤ))
      ≤ liminf (fun n => ∫⁻ x, ‖u n x‖ₑ ^ p ∂(Measure.count : Measure ℤ)) atTop := by
    calc (∫⁻ x, ‖U x‖ₑ ^ p ∂(Measure.count : Measure ℤ))
        ≤ ∫⁻ x, (liminf (fun n => ‖u n x‖ₑ) atTop) ^ p ∂(Measure.count : Measure ℤ) :=
          lintegral_mono (fun x => ENNReal.rpow_le_rpow (hU x) hp.le)
      _ = ∫⁻ x, liminf (fun n => ‖u n x‖ₑ ^ p) atTop ∂(Measure.count : Measure ℤ) := by
          refine lintegral_congr (fun x => ?_)
          have key : ENNReal.orderIsoRpow p hp (liminf (fun n => ‖u n x‖ₑ) atTop)
              = liminf (fun n => ENNReal.orderIsoRpow p hp (‖u n x‖ₑ)) atTop := by
            refine (ENNReal.orderIsoRpow p hp).liminf_apply ?_ ?_ ?_ ?_
            all_goals isBoundedDefault
          simpa only [ENNReal.orderIsoRpow_apply] using key
      _ ≤ liminf (fun n => ∫⁻ x, ‖u n x‖ₑ ^ p ∂(Measure.count : Measure ℤ)) atTop := by
          refine lintegral_liminf_le' (fun n => ?_)
          exact (Measurable.of_discrete : Measurable (fun x : ℤ => ‖u n x‖ₑ ^ p)).aemeasurable
  calc (∫⁻ x, ‖U x‖ₑ ^ p ∂(Measure.count : Measure ℤ)) ^ (1 / p)
      ≤ (liminf (fun n => ∫⁻ x, ‖u n x‖ₑ ^ p ∂(Measure.count : Measure ℤ)) atTop) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hLM (by positivity)
    _ = liminf (fun n => (∫⁻ x, ‖u n x‖ₑ ^ p ∂(Measure.count : Measure ℤ)) ^ (1 / p)) atTop := by
        have key : ENNReal.orderIsoRpow (1 / p) (by positivity)
              (liminf (fun n => ∫⁻ x, ‖u n x‖ₑ ^ p ∂(Measure.count : Measure ℤ)) atTop)
            = liminf (fun n => ENNReal.orderIsoRpow (1 / p) (by positivity)
                (∫⁻ x, ‖u n x‖ₑ ^ p ∂(Measure.count : Measure ℤ))) atTop := by
          refine (ENNReal.orderIsoRpow (1 / p) (by positivity)).liminf_apply ?_ ?_ ?_ ?_
          all_goals isBoundedDefault
        simpa only [ENNReal.orderIsoRpow_apply] using key

/-! ## Lower semicontinuity of `latVarSupR` -/

/-- The `τ`-shifted dyadic conditional expectation is continuous with respect to pointwise
convergence of the input. -/
private lemma latticeExpR_tendsto {A : ℕ → ℤ → ℝ} {B : ℤ → ℝ}
    (hconv : ∀ n : ℤ, Tendsto (fun j : ℕ => A j n) atTop (nhds (B n)))
    (k : ℕ) (τ : ℤ) (x : ℤ) :
    Tendsto (fun j : ℕ => Work.Analysis.Hilbert.latticeExpR k τ (A j) x) atTop
      (nhds (Work.Analysis.Hilbert.latticeExpR k τ B x)) := by
  have h : Tendsto (fun j : ℕ => ∑ d ∈ Finset.range (2 ^ k),
      A j (Work.Analysis.Hilbert.latticeBase k τ x + d)) atTop
      (nhds (∑ d ∈ Finset.range (2 ^ k),
        B (Work.Analysis.Hilbert.latticeBase k τ x + d))) :=
    tendsto_finsetSum _ (fun d _ => hconv _)
  simpa only [Work.Analysis.Hilbert.latticeExpR] using h.const_mul (((2 : ℝ) ^ k)⁻¹)

/-- **Lower semicontinuity of `latVarSupR`**: if `A j → B` pointwise then
`latVarSupR r L τ B x ≤ liminf_j latVarSupR r L τ (A j) x`. -/
private lemma latVarSupR_le_liminf {r : NNReal} {L : ℕ} {τ : ℤ}
    {A : ℕ → ℤ → ℝ} {B : ℤ → ℝ}
    (hconv : ∀ n : ℤ, Tendsto (fun j : ℕ => A j n) atTop (nhds (B n))) (x : ℤ) :
    latVarSupR r L τ B x ≤ liminf (fun j : ℕ => latVarSupR r L τ (A j) x) atTop := by
  refine iSup_le fun u => iSup_le fun J => ?_
  have hsum : Tendsto (fun j : ℕ => ∑ i ∈ Finset.range J,
      |Work.Analysis.Hilbert.latticeExpR (L - u.1 (i + 1)) τ (A j) x
        - Work.Analysis.Hilbert.latticeExpR (L - u.1 i) τ (A j) x| ^ (r : ℝ)) atTop
      (nhds (∑ i ∈ Finset.range J,
      |Work.Analysis.Hilbert.latticeExpR (L - u.1 (i + 1)) τ B x
        - Work.Analysis.Hilbert.latticeExpR (L - u.1 i) τ B x| ^ (r : ℝ))) := by
    refine tendsto_finsetSum _ (fun i _ => ?_)
    exact ((latticeExpR_tendsto hconv (L - u.1 (i + 1)) τ x).sub
      (latticeExpR_tendsto hconv (L - u.1 i) τ x)).abs.rpow_const (Or.inr r.coe_nonneg)
  have hchain : Tendsto (fun j : ℕ => ENNReal.ofReal ((∑ i ∈ Finset.range J,
      |Work.Analysis.Hilbert.latticeExpR (L - u.1 (i + 1)) τ (A j) x
        - Work.Analysis.Hilbert.latticeExpR (L - u.1 i) τ (A j) x| ^ (r : ℝ))
        ^ (1 / (r : ℝ)))) atTop
      (nhds (ENNReal.ofReal ((∑ i ∈ Finset.range J,
      |Work.Analysis.Hilbert.latticeExpR (L - u.1 (i + 1)) τ B x
        - Work.Analysis.Hilbert.latticeExpR (L - u.1 i) τ B x| ^ (r : ℝ))
        ^ (1 / (r : ℝ))))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (hsum.rpow_const (Or.inr (div_nonneg zero_le_one r.coe_nonneg)))
  rw [← hchain.liminf_eq]
  refine (le_liminf_iff).mpr (fun y hy => ?_)
  rw [hchain.liminf_eq] at hy
  filter_upwards [(tendsto_order.1 hchain).1 _ hy] with n hn
  exact hn.trans_le (le_iSup_of_le u (le_iSup_of_le J le_rfl))

/-! ## The truncation -/

/-- Truncation of `h` to the finite interval `[-n,n]`. -/
private def truncOn (h : ℤ → ℝ) (n : ℕ) : ℤ → ℝ := (Set.Icc (-(n : ℤ)) (n : ℤ)).indicator h

private lemma truncOn_apply (h : ℤ → ℝ) (n : ℕ) (m : ℤ) :
    truncOn h n m = if m ∈ Set.Icc (-(n : ℤ)) (n : ℤ) then h m else 0 := by
  rw [truncOn, Set.indicator_apply]

private lemma measurableSet_Icc_int (a b : ℤ) : MeasurableSet (Set.Icc a b : Set ℤ) :=
  (Set.finite_Icc a b).measurableSet

private lemma truncOn_tendsto (h : ℤ → ℝ) (m : ℤ) :
    Tendsto (fun n : ℕ => truncOn h n m) atTop (nhds (h m)) := by
  have hev : ∀ᶠ n : ℕ in atTop, m ∈ Set.Icc (-(n : ℤ)) (n : ℤ) := by
    filter_upwards [eventually_ge_atTop m.natAbs] with n hn
    have h2 : (m.natAbs : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    have h1 : m ≤ (n : ℤ) := le_trans Int.le_natAbs h2
    have h3 : -m ≤ (m.natAbs : ℤ) := by
      rw [Int.natCast_natAbs]; exact neg_le_abs m
    exact ⟨by linarith, h1⟩
  have heq : (fun _ : ℕ => h m) =ᶠ[atTop] (fun n : ℕ => truncOn h n m) := by
    filter_upwards [hev] with n hn
    rw [truncOn_apply, if_pos hn]
  exact Tendsto.congr' heq tendsto_const_nhds

private lemma truncOn_integrable (h : ℤ → ℝ) (n : ℕ) :
    Integrable (truncOn h n) (Measure.count : Measure ℤ) := by
  rw [integrable_count_iff]
  refine summable_of_hasFiniteSupport ((Set.finite_Icc (-(n : ℤ)) (n : ℤ)).subset ?_)
  intro m hm
  by_contra hmn
  rw [Function.mem_support] at hm
  have hz : truncOn h n m = 0 := by
    rw [truncOn_apply, if_neg hmn]
  rw [hz, norm_zero] at hm
  exact hm rfl

/-! ## The main upgrade -/

theorem latVarSupR_le_of_integrable_case (p : ℝ) (hp : 1 < p) (r : NNReal) {C : ℝ}
    (hC : ∀ (h : ℤ → ℝ),
      MeasureTheory.MemLp h (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) →
      MeasureTheory.Integrable h (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) →
      ∀ (L : ℕ) (τ : ℤ),
      MeasureTheory.eLpNorm (Work.KMTAreas.A7.latVarSupR r L τ h) (ENNReal.ofReal p)
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm h (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) :
    ∀ (h : ℤ → ℝ),
      MeasureTheory.MemLp h (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) →
      ∀ (L : ℕ) (τ : ℤ),
      MeasureTheory.eLpNorm (Work.KMTAreas.A7.latVarSupR r L τ h) (ENNReal.ofReal p)
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm h (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  intro h hh L τ
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hconv : ∀ m : ℤ, Tendsto (fun n : ℕ => truncOn h n m) atTop (nhds (h m)) :=
    truncOn_tendsto h
  have hmem : ∀ n : ℕ, MemLp (truncOn h n) (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
    fun n => hh.indicator (measurableSet_Icc_int _ _)
  have hle : ∀ n : ℕ, eLpNorm (truncOn h n) (ENNReal.ofReal p) (Measure.count : Measure ℤ)
      ≤ eLpNorm h (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
    intro n
    refine eLpNorm_mono (hf := by pw_aesm) (fun m => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hm : m ∈ Set.Icc (-(n : ℤ)) (n : ℤ)
    · rw [truncOn_apply, if_pos hm]
    · rw [truncOn_apply, if_neg hm, abs_zero]
      exact abs_nonneg _
  have hbound : ∀ n : ℕ,
      eLpNorm (latVarSupR r L τ (truncOn h n)) (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal C * eLpNorm h (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
    intro n
    refine le_trans (hC (truncOn h n) (hmem n) (truncOn_integrable h n) L τ) ?_
    exact mul_le_mul_right (hle n) (ENNReal.ofReal C)
  have hliminf_bound : liminf (fun n : ℕ => eLpNorm (latVarSupR r L τ (truncOn h n))
        (ENNReal.ofReal p) (Measure.count : Measure ℤ)) atTop
      ≤ ENNReal.ofReal C * eLpNorm h (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
    refine liminf_le_of_le ?_ (fun b hb => ?_)
    · isBoundedDefault
    · obtain ⟨n, hn⟩ := hb.exists
      exact le_trans hn (hbound n)
  refine le_trans ?_ hliminf_bound
  exact eLpNorm_le_liminf_of_le hp0 (fun x => latVarSupR_le_liminf hconv x)

end

end Work.KMTAreas.A7
