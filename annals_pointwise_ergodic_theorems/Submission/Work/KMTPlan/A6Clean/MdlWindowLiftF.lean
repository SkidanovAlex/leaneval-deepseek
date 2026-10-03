/-
# The model window-piece lifts (`f`- and `g`-side)

Instantiation of the abstract lift `Work.KMTPlan.A6Clean.windowPieceLift_abs`
(`MdlWindowLiftND.lean`) at the two model packet families:

* `mdlWindowLiftF` — the `f`-side family `mdlSliceF n`, with window `mStarF U` and band
  `γ₁ n = 2^{k₁ - logN ⌊a n⌋}`;
* `mdlWindowLiftG` — the `g`-side family `mdlSliceG n`, with window `mStargF d U` and band
  `γ₂ n = 2^{d(k₂ - logN ⌊a n⌋)}`.

Both use the *exact-height* band of the model input, which is available from the proved functional
calculus `Work.KMTPlan.A6.Tle_mdlF_eq_Tm_ssu` (resp. `Tle_mdlG_eq_Tm_ssu`) composed with
`Work.KMTPlan.A6Clean.tmBandOfArc` and `Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew` — this
avoids the (unusable) `Tle_exact_band`, whose separation hypothesis `δ + η < ‖α - β‖` is not
available at the model's scales (the input's band and the shell's band are both of size `2^{-U}`,
whereas the separation is only known to be `2^{-U}`).

The vanishing of the window pieces at the non-exact heights is the proved
`Work.KMTPlan.A6Clean.winConvR_eq_zero_of_not_exact`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.MdlWindowLiftND
import Submission.Work.KMTPlan.A6Clean.WinConvRZero
import Submission.Work.KMTPlan.A6Clean.tmBandOfArc
import Submission.Work.KMTPlan.A6.MdlSliceSsuGain
import Submission.Work.KMTAreas.A7.MixedGSideAux
import Submission.Work.KMTPlan.A6.VarphitildeNtjPeriodizeAux
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.KMTPlan.A6Clean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- `Memℓp` (the `ℓ²`-summability predicate on `ℤ`) upgrades to `MemLp` for the counting measure. -/
private theorem memLpCount_of_memlp_two {f : ℤ → ℂ} (hf : Memℓp f 2) :
    MeasureTheory.MemLp f 2 MeasureTheory.Measure.count := by
  refine MeasureTheory.memLp_iff.mpr ?_
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (hf := by pw_aesm) (by norm_num) (by norm_num),
    MeasureTheory.lintegral_count]
  have hsum : Summable (fun n : ℤ => ‖f n‖ ^ (2 : ℝ)) := by simpa [Memℓp] using hf
  have hpt : ∀ a : ℤ, ‖f a‖ₑ ^ (2 : ℝ≥0∞).toReal = ENNReal.ofReal (‖f a‖ ^ (2 : ℝ)) := by
    intro a
    rw [ENNReal.toReal_ofNat, ← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  simp_rw [hpt]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => Real.rpow_nonneg (norm_nonneg _) _) hsum]
  exact ENNReal.ofReal_lt_top

/-- **The `f`-side window-piece lift of the model.**  See `MdlWindowLiftND.lean` for the corrected
band (`γ₁ n`, not the window's support radius). -/
theorem mdlWindowLiftF (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (C₀ : ℕ) (a : ℕ → NNReal) (f : ℤ → ℂ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₁ : k₁ = 0 → j₁ ≠ -1)
    (t : ℝ) (n : ℕ) (hN : 1 ≤ Nat.floor (a n)) (hl₁ : l₁ ≠ 0)
    (hrad : (2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))
        ≤ (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) - 1))
    (hnA : Work.Analysis.IonescuWainger.NonAliasing
        (-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁))
    (hΦ : Work.Analysis.IonescuWainger.SupportedInArc
        (-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ) - 1)
        (Work.Analysis.IonescuWainger.periodize (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t)))
    (hsepU : ∀ ⦃α β : Work.Analysis.IonescuWainger.Circle⦄,
        α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ →
        β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ → α ≠ β →
        (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
          + (2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))
          < ‖α - β‖) :
    ∃ W : Work.Analysis.IonescuWainger.Circle → ℝ → ℂ,
      (∀ α, Measurable (W α)) ∧
      (∀ α, Work.KMTAreas.A7Rep.HasRealFreqSupport (W α)
        (Set.Icc (-((2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))))
          ((2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))))) ∧
      (∀ α, α ∉ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁ → W α = 0) ∧
      (∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁, ∀ x : ℤ,
        W α (x : ℝ) = Work.KMTAreas.A7.winConvR
          (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
          (Work.KMTAreas.A7.winModR (-α)
            (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n)) x) ∧
      (∀ z : ℤ, Summable (fun j : ℤ =>
        Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) j *
          Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n (z - j))) := by
  classical
  set U : ℕ := Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) with hU
  set N : ℕ := Nat.floor (a n) with hNdef
  set γ : ℝ := (2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) with hγdef
  have hγpos : 0 < γ := by rw [hγdef]; positivity
  have hU1 : 1 ≤ U := Work.KMTAreas.A7.one_le_uScale ρ hρ.le _
  have h2U : (2 : ℝ) ^ (-(2 * (U : ℤ))) = 2 * ((2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) := by
    rw [show (-(2 * (U : ℤ)) : ℤ) = (-(2 * (U : ℤ)) - 1) + 1 by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    ring
  have hγhalf : γ < 1 / 2 := by
    have hle : γ ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) := by
      rw [hγdef] at hrad ⊢
      exact hrad
    have h1 : (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) ≤ (8 : ℝ)⁻¹ := by
      have h2 : (-(2 * (U : ℤ)) - 1 : ℤ) ≤ -3 := by
        have hUZ : (1 : ℤ) ≤ (U : ℤ) := by exact_mod_cast hU1
        omega
      have h3 := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h2
      have h4 : (2 : ℝ) ^ ((-3 : ℤ)) = (8 : ℝ)⁻¹ := by norm_num
      rw [h4] at h3
      exact h3
    have h12 : (8 : ℝ)⁻¹ < 1 / 2 := by norm_num
    linarith
  have hm : Integrable (Work.KMTAreas.A7.mStarF U) := Work.KMTAreas.A7.kmt_integrable_mStarF U
  have hmsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j‖) :=
    Work.KMTAreas.A7.summable_cw_mStarF U
  have hmsup : ∀ θ : Circ, Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.mStarF U) θ
      ≠ 0 → θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 ((2 : ℝ) ^ (-(2 * (U : ℤ)))) :=
    fun θ hθ => Work.KMTAreas.A7.periodize_mStarF_mem_arcSet (U := U) hθ
  by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · -- the model input is the exact-height multiplier of the modified bump
    obtain ⟨M, hM0, hMb, hper, harc⟩ :=
      Work.KMTPlan.A6.varphiNtjPeriodize_aux N k₁ j₁ t hj₁ hk₁ hN
    have hfℓ : Memℓp f 2 := Work.KMTPlan.A6.memlpOfMemLpCount (by norm_num) (by norm_num) hf
    have heq : Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTPlan.A6.varphiNtj N k₁ j₁ t)
        (Work.KMTPlan.A6.mdlF ρ U l₁ f) = Work.KMTAreas.A7.Tm ρ l₁
          (Work.KMTPlan.A6.varphiNtj N k₁ j₁ t) f :=
      Work.KMTPlan.A6.Tle_mdlF_eq_Tm_ssu ρ hρ hρ1 U l₁ hU1 (Work.KMTPlan.A6.varphiNtj N k₁ j₁ t)
        hper hf hnA hΦ
    obtain ⟨hwT, hbandT⟩ := tmBandOfArc ρ l₁ (Work.KMTPlan.A6.varphiNtj N k₁ j₁ t) γ hper harc
      f hfℓ
    rw [Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew hl₁] at hbandT
    have hfun : Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n =
        Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTPlan.A6.varphiNtj N k₁ j₁ t) f := by
      rw [Work.KMTPlan.A6.mdlSliceF, if_pos hc]
      exact heq
    have hh : Memℓp (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) 2 :=
      hfun.symm ▸ hwT
    have hbandh : Work.BourgainPlan.IonescuWainger.HasFreqSupport
        (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) hh
        (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
          Work.BourgainPlan.IonescuWainger.arcSet α γ) := by
      simp only [Work.BourgainPlan.IonescuWainger.HasFreqSupport] at hbandT ⊢
      filter_upwards [hbandT] with ξ hξ hmem
      rw [show Work.BourgainPlan.IonescuWainger.ftLp
            (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) hh
          = Work.BourgainPlan.IonescuWainger.ftLp
            (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTPlan.A6.varphiNtj N k₁ j₁ t) f) hwT from
        (Work.BourgainPlan.IonescuWainger.ftLp_congr hfun.symm hwT hh).symm]
      exact hξ hmem
    -- the lift
    obtain ⟨W, hWmeas, hWband, hWzero, hWsample⟩ :=
      windowPieceLift_abs (m := Work.KMTAreas.A7.mStarF U) hm hmsum hmsup hγpos hγhalf
        (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁)
        (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) hh hbandh
        (fun α hα β hβ hne => hsepU (Work.KMTAreas.A7.mem_iwArithFreqsNew_le hα)
          (Work.KMTAreas.A7.mem_iwArithFreqsNew_le hβ) hne)
    refine ⟨W, hWmeas, hWband, hWzero, ?_, ?_⟩
    · intro α hα x
      by_cases hx : α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁
      · exact hWsample α hx x
      · have hz : Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStarF U)
            (Work.KMTAreas.A7.winModR (-α)
              (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n)) = 0 := by
          have hδ : (0 : ℝ) < (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) := by positivity
          have hmsupp : ∀ θ : ℝ, 2 * (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) < |θ| →
              Work.KMTAreas.A7.mStarF U θ = 0 := by
            intro θ hθ
            by_contra hne
            have h1 := Work.KMTAreas.A7.arithSymbSpike_mStarF_support U θ hne
            rw [← h2U] at hθ
            linarith
          have hhE' : Work.BourgainPlan.IonescuWainger.HasFreqSupport
              (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) hh
              (⋃ β ∈ Work.KMTAreas.A7.diffFreqs ρ l₁,
                Work.BourgainPlan.IonescuWainger.arcSet β γ) := by
            rw [Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew hl₁]
            exact hbandh
          have hsepW : ∀ α' ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
              ∀ β ∈ Work.KMTAreas.A7.diffFreqs ρ l₁, α' ≠ β →
              2 * (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) + γ < ‖α' - β‖ := by
            intro α' hα' β hβ hne
            have hβ' : β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ := by
              rw [Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew hl₁] at hβ
              exact Work.KMTAreas.A7.mem_iwArithFreqsNew_le hβ
            have h := hsepU hα' hβ' hne
            rw [← h2U]
            exact h
          have hx' : α ∉ Work.KMTAreas.A7.diffFreqs ρ l₁ := by
            rwa [Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew hl₁]
          exact Work.KMTPlan.A6Clean.winConvR_eq_zero_of_not_exact ρ hρ hρ1 l₁
            (Work.KMTAreas.A7.mStarF U) ((2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) γ hδ hγpos hm hmsum
            hmsupp (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) hh hhE' hsepW
            α hα hx'
        rw [hWzero α hx, hz]
        rfl
    · intro z
      exact Work.KMTAreas.A7.summable_cw_mul_of_memℓp hmsum hh z
  · -- off the core the input vanishes
    have hzero : Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n = 0 := by
      rw [Work.KMTPlan.A6.mdlSliceF, if_neg hc]
    have hmp : ∀ α : Circ, Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStarF U)
        (Work.KMTAreas.A7.winModR (-α) (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n))
        = 0 := by
      intro α
      rw [hzero]
      funext x
      simp [Work.KMTAreas.A7.winModR, Work.KMTAreas.A7.winConvR]
    refine ⟨fun _ _ => 0, fun _ => measurable_const, fun α => hasRealFreqSupport_zero _,
      fun α _ => rfl, ?_, ?_⟩
    · intro α hα x
      rw [hmp α]
      rfl
    · intro z
      rw [hzero]
      simp

/-- **The `g`-side window-piece lift of the model** (the twin of `mdlWindowLiftF`, with the window
`mStargF d U` and the band `γ₂ = 2^{d(k₂-Log N)}`). -/
theorem mdlWindowLiftG (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (C₀ : ℕ) (a : ℕ → NNReal) (g : ℤ → ℂ) (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₂ : k₂ = 0 → j₂ ≠ -1)
    (t : ℝ) (n : ℕ) (hN : 1 ≤ Nat.floor (a n)) (hl₂ : l₂ ≠ 0)
    (hrad : (2 : ℝ) ^ ((P.natDegree : ℝ) *
          ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))
        ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 *
          (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) - 1))
    (hnA : Work.Analysis.IonescuWainger.NonAliasing
        (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂))
    (hΦ : Work.Analysis.IonescuWainger.SupportedInArc
        (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) - 1)
        (Work.Analysis.IonescuWainger.periodize
          (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)))
    (hsepU : ∀ ⦃α β : Work.Analysis.IonescuWainger.Circle⦄,
        α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ →
        β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ → α ≠ β →
        (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 *
            (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
          + (2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))
          < ‖α - β‖) :
    ∃ W : Work.Analysis.IonescuWainger.Circle → ℝ → ℂ,
      (∀ β, Measurable (W β)) ∧
      (∀ β, Work.KMTAreas.A7Rep.HasRealFreqSupport (W β)
        (Set.Icc (-((2 : ℝ) ^ ((P.natDegree : ℝ) *
            ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))))
          ((2 : ℝ) ^ ((P.natDegree : ℝ) *
            ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))))) ∧
      (∀ β, β ∉ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ → W β = 0) ∧
      (∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂, ∀ x : ℤ,
        W β (x : ℝ) = Work.KMTAreas.A7.winConvR
          (Work.KMTAreas.A7.mStargF P.natDegree
            (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
          (Work.KMTAreas.A7.winModR (-β)
            (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n)) x) ∧
      (∀ z : ℤ, Summable (fun j : ℤ =>
        Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree
            (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) j *
          Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n (z - j))) := by
  classical
  set U : ℕ := Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) with hU
  set N : ℕ := Nat.floor (a n) with hNdef
  set γ : ℝ := (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
    with hγdef
  have hd1 : 1 ≤ P.natDegree := le_trans (by norm_num) hd
  have hγpos : 0 < γ := by rw [hγdef]; positivity
  have hU1 : 1 ≤ U := Work.KMTAreas.A7.one_le_uScale ρ hρ.le _
  have h2U : (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ)))
      = 2 * ((2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ)) - 1)) := by
    rw [show (-((P.natDegree : ℤ) * 2 * (U : ℤ)) : ℤ)
        = (-((P.natDegree : ℤ) * 2 * (U : ℤ)) - 1) + 1 by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    ring
  have hγhalf : γ < 1 / 2 := by
    have hle : γ ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ)) - 1) := by
      rw [hγdef] at hrad ⊢
      exact hrad
    have h1 : (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ)) - 1) ≤ (8 : ℝ)⁻¹ := by
      have h2 : (-((P.natDegree : ℤ) * 2 * (U : ℤ)) - 1 : ℤ) ≤ -3 := by
        have hdZ : (1 : ℤ) ≤ (P.natDegree : ℤ) := by exact_mod_cast hd1
        have hUZ : (1 : ℤ) ≤ (U : ℤ) := by exact_mod_cast hU1
        nlinarith
      have h3 := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h2
      have h4 : (2 : ℝ) ^ ((-3 : ℤ)) = (8 : ℝ)⁻¹ := by norm_num
      rw [h4] at h3
      exact h3
    have h12 : (8 : ℝ)⁻¹ < 1 / 2 := by norm_num
    linarith
  have hm : Integrable (Work.KMTAreas.A7.mStargF P.natDegree U) :=
    Work.KMTAreas.A7.kmt_integrable_mStargF P.natDegree U
  have hmsum : Summable (fun j : ℤ =>
      ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree U) j‖) :=
    Work.KMTAreas.A7.summable_cw_mStargF P.natDegree U
  have hmsup : ∀ θ : Circ, Work.Analysis.IonescuWainger.periodize
      (Work.KMTAreas.A7.mStargF P.natDegree U) θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0
        ((2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ)))) := by
    intro θ hθ
    rw [mStargF_eq_mStarF P.natDegree U] at hθ
    have h1 := Work.KMTAreas.A7.periodize_mStarF_mem_arcSet (U := P.natDegree * U) hθ
    have he : (2 : ℝ) ^ (-(2 * (((P.natDegree * U : ℕ)) : ℤ)))
        = (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ))) := by
      congr 1
      push_cast
      ring
    rwa [he] at h1
  by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · obtain ⟨M, hM0, hMb, hper, harc⟩ :=
      Work.KMTPlan.A6.VarphitildeNtjPeriodizeAux P N k₂ j₂ t hj₂ hk₂ hN
    have hgℓ : Memℓp g 2 := Work.KMTPlan.A6.memlpOfMemLpCount (by norm_num) (by norm_num) hg
    have heq : Work.KMTAreas.A7.Tle ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t)
        (Work.KMTPlan.A6.mdlG ρ P U l₂ g) = Work.KMTAreas.A7.Tm ρ l₂
          (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t) g :=
      Work.KMTPlan.A6.Tle_mdlG_eq_Tm_ssu ρ hρ hρ1 P U l₂ hd1 hU1
        (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t) hper hg hnA hΦ
    obtain ⟨hwT, hbandT⟩ := tmBandOfArc ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t) γ
      hper harc g hgℓ
    rw [Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew hl₂] at hbandT
    have hfun : Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n =
        Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t) g := by
      rw [Work.KMTPlan.A6.mdlSliceG, if_pos hc]
      exact heq
    have hh : Memℓp (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) 2 :=
      hfun.symm ▸ hwT
    have hbandh : Work.BourgainPlan.IonescuWainger.HasFreqSupport
        (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) hh
        (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
          Work.BourgainPlan.IonescuWainger.arcSet α γ) := by
      simp only [Work.BourgainPlan.IonescuWainger.HasFreqSupport] at hbandT ⊢
      filter_upwards [hbandT] with ξ hξ hmem
      rw [show Work.BourgainPlan.IonescuWainger.ftLp
            (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) hh
          = Work.BourgainPlan.IonescuWainger.ftLp
            (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t) g) hwT from
        (Work.BourgainPlan.IonescuWainger.ftLp_congr hfun.symm hwT hh).symm]
      exact hξ hmem
    obtain ⟨W, hWmeas, hWband, hWzero, hWsample⟩ :=
      windowPieceLift_abs (m := Work.KMTAreas.A7.mStargF P.natDegree U) hm hmsum hmsup
        hγpos hγhalf (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂)
        (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) hh hbandh
        (fun α hα β hβ hne => hsepU (Work.KMTAreas.A7.mem_iwArithFreqsNew_le hα)
          (Work.KMTAreas.A7.mem_iwArithFreqsNew_le hβ) hne)
    refine ⟨W, hWmeas, hWband, hWzero, ?_, ?_⟩
    · intro β hβ x
      by_cases hx : β ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂
      · exact hWsample β hx x
      · have hz : Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStargF P.natDegree U)
            (Work.KMTAreas.A7.winModR (-β)
              (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n)) = 0 := by
          have hδ : (0 : ℝ) < (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ)) - 1) := by
            positivity
          have hmsupp : ∀ θ : ℝ,
              2 * (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ)) - 1) < |θ| →
              Work.KMTAreas.A7.mStargF P.natDegree U θ = 0 := by
            intro θ hθ
            by_contra hne
            have h1 := Work.KMTAreas.A7.arithSymbSpike_mStargF_support P.natDegree U θ hne
            rw [← h2U] at hθ
            linarith
          have hhE' : Work.BourgainPlan.IonescuWainger.HasFreqSupport
              (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) hh
              (⋃ β' ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
                Work.BourgainPlan.IonescuWainger.arcSet β' γ) := by
            rw [Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew hl₂]
            exact hbandh
          have hsepW : ∀ β' ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
              ∀ β₂ ∈ Work.KMTAreas.A7.diffFreqs ρ l₂, β' ≠ β₂ →
              2 * (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ)) - 1) + γ < ‖β' - β₂‖ := by
            intro β' hβ' β₂ hβ₂ hne
            have hβ₂' : β₂ ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ := by
              rw [Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew hl₂] at hβ₂
              exact Work.KMTAreas.A7.mem_iwArithFreqsNew_le hβ₂
            have h := hsepU hβ' hβ₂' hne
            rw [← h2U]
            exact h
          have hx' : β ∉ Work.KMTAreas.A7.diffFreqs ρ l₂ := by
            rwa [Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew hl₂]
          exact Work.KMTPlan.A6Clean.winConvR_eq_zero_of_not_exact ρ hρ hρ1 l₂
            (Work.KMTAreas.A7.mStargF P.natDegree U)
            ((2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ)) - 1)) γ hδ hγpos hm hmsum
            hmsupp (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) hh hhE' hsepW
            β hβ hx'
        rw [hWzero β hx, hz]
        rfl
    · intro z
      exact Work.KMTAreas.A7.summable_cw_mul_of_memℓp hmsum hh z
  · have hzero : Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n = 0 := by
      rw [Work.KMTPlan.A6.mdlSliceG, if_neg hc]
    have hmp : ∀ β : Circ, Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStargF P.natDegree U)
        (Work.KMTAreas.A7.winModR (-β) (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n))
        = 0 := by
      intro β
      rw [hzero]
      funext x
      simp [Work.KMTAreas.A7.winModR, Work.KMTAreas.A7.winConvR]
    refine ⟨fun _ _ => 0, fun _ => measurable_const, fun β => hasRealFreqSupport_zero _,
      fun β _ => rfl, ?_, ?_⟩
    · intro β hβ x
      rw [hmp β]
      rfl
    · intro z
      rw [hzero]
      simp

end Work.KMTPlan.A6Clean
