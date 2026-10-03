import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.varRhoFrom_r_le_liminf
import Submission.Work.KMTAreas.A7Hi.LowpassDefs
import Submission.Commons.Analysis.Hilbert.eLpNorm_le_liminf_of_le_liminf
import Submission.Port.Aesm

/-!
# Finitely supported inputs to all inputs for the `r`-variation of the low-pass IW walk

The target `Work.KMTAreas.A7LoPoly.varRhoFromGeneral` upgrades the `ℓᵖ`-bound for the `r`-variation
`varRhoFrom r κ` of the low-pass Ionescu--Wainger walk `n ↦ lpf ρ l₁ m₀ n f` from *finitely
supported* inputs `f : ℤ →₀ ℂ` to *all* inputs `f : ℤ → ℂ`, with the constant unchanged.  The
variation exponent `r > 0` and the exponent `p > 0` are both arbitrary.

The proof is the standard density/extension argument:

* the finitely supported truncations `truncZ K f` are pointwise convergent under every IW projection
  `kmtProj ρ l k` (`Work.KMTContract.kmtProj_tendsto_truncZ` proves this for `ℓᵖ`-inputs with
  `1 < p`; the generalisation to `p > 0` is `kmtProj_tendsto_truncZ_of_pos` below, whose only extra
  ingredient is that `ℓᵖ(ℤ)`-functions are *bounded* for **every** `p ≠ 0` — the `ℓᵖ ⊆ ℓ^∞`
  inclusion, `bound_of_memLp_count_ne_zero`);
* the `r`-variation is lower semicontinuous along pointwise convergence
  (`Work.BourgainPlan.IonescuWainger.varRhoFrom_r_le_liminf`);
* Fatou for `eLpNorm` in the form `Commons.Analysis.Hilbert.eLpNorm_le_liminf_of_le_liminf`;
* `‖truncZ K f x‖ ≤ ‖f x‖` and the finitely supported bound applied to the `Finsupp` underlying
  each truncation.
-/

namespace Work.KMTAreas.A7LoPoly

open MeasureTheory Filter Finset
open scoped ENNReal NNReal BigOperators

set_option maxHeartbeats 1000000

/-- Monotonicity of `liminf` for `ℝ≥0∞`-valued sequences (the general `Filter.liminf_le_liminf`
carries coboundedness side conditions that are awkward here). -/
lemma liminf_le_liminf_ennreal_of_eventually {u v : ℕ → ℝ≥0∞}
    (h : ∀ᶠ n in Filter.atTop, u n ≤ v n) :
    Filter.liminf u Filter.atTop ≤ Filter.liminf v Filter.atTop := by
  rw [Filter.liminf_eq, Filter.liminf_eq]
  refine sSup_le fun a ha => le_sSup ((ha.and h).mono fun n hn => le_trans hn.1 hn.2)

/-- The truncations `truncZ K f` are coercions of `Finsupp`s. -/
lemma exists_finsupp_coe_truncZ_aux (K : ℕ) (f : ℤ → ℂ) :
    ∃ F : ℤ →₀ ℂ, ⇑F = Work.KMTContract.truncZ K f := by
  refine ⟨Finsupp.ofSupportFinite (Work.KMTContract.truncZ K f) ?_,
    Finsupp.ofSupportFinite_coe⟩
  refine (Finset.finite_toSet (Finset.Icc (-(K : ℤ)) (K : ℤ))).subset ?_
  intro x hx
  rw [Finset.mem_coe, Finset.mem_Icc]
  simp only [Function.mem_support] at hx
  by_cases h : |x| ≤ (K : ℤ)
  · exact abs_le.mp h
  · rw [Work.KMTContract.truncZ_of_gt (lt_of_not_ge h)] at hx
    exact absurd rfl hx

/-- `truncZ` does not increase the pointwise norm. -/
lemma norm_truncZ_le (K : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    ‖Work.KMTContract.truncZ K f x‖ ≤ ‖f x‖ := by
  rw [Work.KMTContract.truncZ_apply]
  split <;> simp

/-- The counting measure on `ℤ` dominates the Dirac mass at every point. -/
lemma dirac_le_count_int_aux (x : ℤ) : Measure.dirac x ≤ Measure.count := by
  rw [Measure.count]
  exact Measure.le_sum Measure.dirac x

/-- **A function in `ℓ^p(ℤ)` is bounded, for every `p ≠ 0`.**

This is the `ℓ^p ⊆ ℓ^∞` inclusion for the counting measure on `ℤ`
(`Work.KMTContract.bound_of_memLp_count` is the case `1 < p`; its proof only ever uses `p ≠ 0`). -/
lemma bound_of_memLp_count_ne_zero {p : ENNReal} (hp : p ≠ 0) {f : ℤ → ℂ}
    (hf : MeasureTheory.MemLp f p MeasureTheory.Measure.count) :
    ∃ M : NNReal, ∀ x : ℤ, ‖f x‖ ≤ M := by
  refine ⟨(MeasureTheory.eLpNorm f p MeasureTheory.Measure.count).toNNReal, fun x => ?_⟩
  have h1 : ‖f x‖ₑ ≤ MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    rw [← MeasureTheory.eLpNorm_dirac f x hp]
    exact MeasureTheory.eLpNorm_mono_measure f (dirac_le_count_int_aux x)
  have h2 := ENNReal.toNNReal_mono hf.eLpNorm_lt_top.ne h1
  exact_mod_cast h2

/-- **Pointwise convergence of the truncated Ionescu--Wainger projections for `ℓ^p`-inputs with
any `p > 0`** (the `1 < p` hypothesis of `Work.KMTContract.kmtProj_tendsto_truncZ` is not needed:
`ℓ^p(ℤ)` is contained in `ℓ^∞(ℤ)` for every `p ≠ 0`, and the IW kernel is absolutely summable by
`Work.KMTContract.kmtKernel_decay`). -/
lemma kmtProj_tendsto_truncZ_of_pos (ρ : ℝ) (l : ℕ) (k : ℤ) {p : ℝ} (hp : 0 < p)
    {f : ℤ → ℂ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal p) MeasureTheory.Measure.count) (n : ℤ) :
    Filter.Tendsto
      (fun K : ℕ => Work.KMTContract.kmtProj ρ l k (Work.KMTContract.truncZ K f) n)
      Filter.atTop (nhds (Work.KMTContract.kmtProj ρ l k f n)) := by
  obtain ⟨C, _hC, hdec⟩ := Work.KMTContract.kmtKernel_decay ρ l k
  have hk : Summable (fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j‖) :=
    Work.KMTContract.kernel_l1_of_decay hdec
  obtain ⟨M, hM⟩ := bound_of_memLp_count_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hp) hf
  have hg : Summable (fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j * f (n - j)) := by
    refine Summable.of_norm_bounded (hk.mul_left (M : ℝ)) (fun j => ?_)
    rw [norm_mul]
    calc ‖Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize
                (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j‖
          * ‖f (n - j)‖
        ≤ ‖Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize
                (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j‖ * (M : ℝ) :=
          mul_le_mul_of_nonneg_left (hM (n - j)) (norm_nonneg _)
      _ = (M : ℝ) * ‖Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize
                (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j‖ :=
          mul_comm _ _
  have hsum := Work.KMTContract.tendsto_sum_Icc_atTop hg n
  have h1 : (fun K : ℕ => Work.KMTContract.kmtProj ρ l k (Work.KMTContract.truncZ K f) n)
      = fun K : ℕ => ∑ j ∈ Finset.Icc (n - (K : ℤ)) (n + (K : ℤ)),
          Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize
                (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j
            * f (n - j) :=
    funext fun K => Work.KMTContract.kmtProj_truncZ_eq_sumIcc ρ l k K f n
  rw [h1, Work.KMTContract.kmtProj_apply]
  exact hsum

/-- **Finitely supported inputs to all inputs for the `r`-variation of the low-pass
Ionescu--Wainger walk.** -/
theorem varRhoFromGeneral (ρ : ℝ) (hρ : 0 < ρ) (r : ℝ) (hr : 0 < r) (p : ℝ) (hp : 0 < p)
    (Cρ C : ℝ) (hC : 0 < C)
    (hfin : ∀ (l₁ m₀ κ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) →
      ∀ f : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun y : ℤ => Work.BourgainPlan.Maximal.varRhoFrom r κ
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n (⇑f) y))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C *
          MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal p) MeasureTheory.Measure.count) :
    ∀ (l₁ m₀ κ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun y : ℤ => Work.BourgainPlan.Maximal.varRhoFrom r κ
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f y))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C *
          MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  intro l₁ m₀ κ hgood f
  rcases eq_or_ne (MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count) ⊤
    with htop | hne
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hC)]
    exact le_top
  · have hfmem : MeasureTheory.MemLp f (ENNReal.ofReal p) MeasureTheory.Measure.count :=
      (MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hne))
    -- the variation is lower semicontinuous along the truncations
    have hpoint : ∀ y : ℤ,
        Work.BourgainPlan.Maximal.varRhoFrom r κ
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f y)
        ≤ Filter.liminf (fun K : ℕ => Work.BourgainPlan.Maximal.varRhoFrom r κ
            (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n
              (Work.KMTContract.truncZ K f) y)) Filter.atTop := by
      intro y
      refine Work.BourgainPlan.IonescuWainger.varRhoFrom_r_le_liminf hr κ
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f y)
        (fun K n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n
          (Work.KMTContract.truncZ K f) y) ?_
      intro n
      simpa only [Work.KMTAreas.A7Hi.lpf] using
        kmtProj_tendsto_truncZ_of_pos ρ l₁ (-((m₀ : ℤ) + (n : ℤ))) hp hfmem y
    -- Fatou for `eLpNorm`
    have hFat := Commons.Analysis.Hilbert.eLpNorm_le_liminf_of_le_liminf
      (fun K y => Work.BourgainPlan.Maximal.varRhoFrom r κ
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n
          (Work.KMTContract.truncZ K f) y))
      (fun y => Work.BourgainPlan.Maximal.varRhoFrom r κ
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f y))
      hp hpoint
    refine hFat.trans ?_
    -- the finitely supported bound, uniformly in the truncation parameter
    have hK : ∀ K : ℕ, MeasureTheory.eLpNorm (fun y : ℤ =>
          Work.BourgainPlan.Maximal.varRhoFrom r κ
            (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n
              (Work.KMTContract.truncZ K f) y))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
      intro K
      obtain ⟨F, hF⟩ := exists_finsupp_coe_truncZ_aux K f
      have hb := hfin l₁ m₀ κ hgood F
      rw [hF] at hb
      refine hb.trans (mul_le_mul_right (MeasureTheory.eLpNorm_mono (hf := by pw_aesm) (norm_truncZ_le K f))
        (ENNReal.ofReal C))
    calc Filter.liminf (fun K : ℕ => MeasureTheory.eLpNorm (fun y : ℤ =>
            Work.BourgainPlan.Maximal.varRhoFrom r κ
              (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n
                (Work.KMTContract.truncZ K f) y))
            (ENNReal.ofReal p) MeasureTheory.Measure.count) Filter.atTop
        ≤ Filter.liminf (fun _ : ℕ => ENNReal.ofReal C *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count)
            Filter.atTop :=
          liminf_le_liminf_ennreal_of_eventually (Filter.Eventually.of_forall hK)
      _ = ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := Filter.liminf_const _

end Work.KMTAreas.A7LoPoly
