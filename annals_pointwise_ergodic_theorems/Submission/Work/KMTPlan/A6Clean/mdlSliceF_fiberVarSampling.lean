/-
# `Work.KMTPlan.A6Clean.mdlSliceF_fiberVarSampling` — the fibre variational sampling
estimate for the A6 slice family `mdlSliceF`

The target is the `A6`-carrier version of the §8 fibre variational sampling estimate of
Krause--Mirek--Tao (*Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals **195** (2022)): for the packet family

  `h n = mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n`
       `= if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then Tle ρ l₁ (φ_{N,k₁,j₁,t}) (mdlF ρ U l₁ f) else 0`,
  `N = Nat.floor (a n)`, `U = uScale ρ L`, `L = lcL l₁ l₂ k₁ k₂`,

and `f ∈ ℓ²(ℤ)`, the `ℓᵖ`-norm of the residue average of the variational norms of the fibres
`fiberOp ρ l₁ (mStarF U) n₀ (h n)` is bounded by `C · lossWeight A ρ l₁ l₂ k₁ k₂` times the
`ℓᵖ`-norm of the variational norm of `h`.

## Route

* `l₁ = 0`: `iwArithFreqsNew ρ 0 = ∅`, so every fibre vanishes identically and the inequality is
  `0 ≤ _`;
* `L ≤ B` (`B` a `ρ`-dependent constant): the crude Young/kernel bound
  `Work.KMTAreas.A7.fiberOpVarNonFareyBounded`, averaged over the residues by the Tonelli
  identity `Work.KMTAreas.A7Hi.eLpNormResidueLpEq`;
* `L > B`: the band-limited estimate `Work.KMTAreas.A7Rescue.fibreVarSampling_quarter`.  On the
  core the family is the exact-height multiplier of the modified bump,
  `h n = Tm ρ l₁ (φ_{N,k₁,j₁,t}) f` (`Work.KMTPlan.A6.Tle_piExact_eq_Tm_ssu`), so its band is
  the union of the `W n`-arcs around `diffFreqs ρ l₁ = iwArithFreqsNew ρ l₁`; the Shannon
  condition `W n · q ≤ 1/4` and the plateau condition `W n ≤ 2^{-2U-1}` come from
  `Work.KMTAreas.A7.farey_and_strict_of_large_L`, and the separation `2·2^{-2U}` from the good
  major-arcs count `Work.A7Hi.sep_iwArithFreqsNew_of_goodMajorArcs`.

## The delegated arithmetic/analytic inputs

Four helper lemmas are proved in sibling files and imported here:

* `Work.KMTPlan.A6Clean.tmBandOfArc` — the band of the exact-height multiplier `Tm` is the
  union of the `δ`-arcs around `diffFreqs ρ l`;
* `Work.KMTPlan.A6Clean.goodMajorArcs_uScale_of_large` — for `L` large and `l ≤ L` the good
  major-arcs condition holds at the model scales `-(uScale ρ L)` and `-(2·uScale ρ L)`;
* `Work.KMTPlan.A6Clean.bandRadius_le` — the Farey and plateau conditions control the packet
  radius `2^{k - Log N}`;
* `Work.KMTPlan.A6Clean.fiberVarSampling_crude` — the crude Young/kernel bound for the fibre
  estimate at bounded scales, for an arbitrary family.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Rescue.FiberVarSamplingRep
import Submission.Work.KMTPlan.A6.MdlSlicePktLinF
import Submission.Work.KMTPlan.A6Clean.AdelicPacketFam
import Submission.Work.KMTPlan.A6.MdlSliceSsuGain
import Submission.Work.KMTPlan.A6.MdlSliceGband
import Submission.Work.A7Hi.fiberBumpPositivity
import Submission.Work.KMTPlan.A6Clean.tmBandOfArc
import Submission.Work.KMTPlan.A6Clean.goodMajorArcs_uScale_of_large
import Submission.Work.KMTPlan.A6Clean.fiberVarSampling_crude
import Submission.Work.KMTPlan.A6Clean.bandRadius_le

set_option maxHeartbeats 1600000

namespace Work.KMTPlan.A6Clean

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTPlan.A6

noncomputable section

/-! ## Temporary local copies of the delegated lemmas -/

/-! ## Elementary helpers -/

/-- The fibre operator at arithmetic level `0` vanishes identically: the frequency set
`iwArithFreqsNew ρ 0` is empty. -/
lemma fiberOp_level_zero (ρ : ℝ) (m : ℝ → ℂ) (n₀ : ℤ) (u : ℤ → ℂ) :
    Work.KMTAreas.A7.fiberOp ρ 0 m n₀ u = fun _ : ℤ => (0 : ℂ) := by
  funext x
  simp only [Work.KMTAreas.A7.fiberOp]
  have h0 : Work.Analysis.IonescuWainger.iwArithFreqsNew ρ 0
      = (∅ : Finset Work.Analysis.IonescuWainger.Circle) := by
    rw [Work.Analysis.IonescuWainger.iwArithFreqsNew]
    simp
  simp only [h0, Finset.sum_empty, zero_mul, tsum_zero]

/-- The `residueLp` of the zero family vanishes. -/
lemma residueLp_zero_eq (p : ℝ) (hp : 0 < p) (q : ℕ) :
    Work.KMTAreas.A7.residueLp p q (fun _ _ => (0 : ENNReal)) = fun _ : ℤ => 0 := by
  funext x
  simp only [Work.KMTAreas.A7.residueLp]
  have hsum : (∑ n₀ ∈ Finset.range q, ENNReal.rpow (0 : ENNReal) p) = 0 := by
    rw [show (∑ n₀ ∈ Finset.range q, ENNReal.rpow (0 : ENNReal) p)
        = ∑ _n₀ ∈ Finset.range q, (0 : ENNReal) from
        Finset.sum_congr rfl (fun n₀ _ => ENNReal.zero_rpow_of_pos hp)]
    simp
  rw [hsum, mul_zero]
  exact ENNReal.zero_rpow_of_pos (by positivity : (0 : ℝ) < 1 / p)

/-- `SupportedInArc` from an arc-support at a radius below `2^{-U-1}`. -/
lemma supportedInArc_of_arcSet_le (U : ℕ) (Φ : Work.Analysis.IonescuWainger.Circle → ℂ) (δ : ℝ)
    (h : ∀ θ, Φ θ ≠ 0 → θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ)
    (hle : δ ≤ (2 : ℝ) ^ (-(U : ℤ) - 1)) :
    Work.Analysis.IonescuWainger.SupportedInArc (-(U : ℤ) - 1) Φ := by
  intro ξ hξ
  obtain ⟨t, ht, htx⟩ := h ξ hξ
  refine ⟨t, ?_, ?_⟩
  · rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
    exact abs_le.mp (le_trans ht hle)
  · simpa using htx.symm

/-- On the core condition the A6 slice is the exact-height multiplier of the modified bump. -/
lemma mdlSliceF_eq_Tm (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (t : ℝ) (f : ℤ → ℂ) (n : ℕ)
    (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₁ : k₁ = 0 → j₁ ≠ -1)
    (hc : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hnA : Work.Analysis.IonescuWainger.NonAliasing
      (-(Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁))
    (hΦ : Work.Analysis.IonescuWainger.SupportedInArc
      (-(Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ) - 1)
      (Work.Analysis.IonescuWainger.periodize (varphiNtj (Nat.floor (a n)) k₁ j₁ t))) :
    mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n
      = Work.KMTAreas.A7.Tm ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t) f := by
  have hN : 1 ≤ Nat.floor (a n) := by
    have hlt : Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) < Nat.floor (a n) :=
      ((mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hc).2.1
    have h1 : 1 ≤ Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ l₂) := by
      rw [Work.KMTAreas.A7.splitCut]; exact Nat.one_le_two_pow
    omega
  obtain ⟨M, hM0, hMbd, hMper, hMarc⟩ :=
    varphiNtjPeriodize_aux (Nat.floor (a n)) k₁ j₁ t hj₁ hk₁ hN
  have hcplt : (2 : ℝ) ^ (-(Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)) ≤ 1 / 2 := by
    rw [zpow_neg, zpow_natCast]
    have h1 : 1 ≤ Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) :=
      Work.KMTAreas.A7.one_le_uScale ρ hρ.le _
    have h2u : (2 : ℝ) ≤ (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)) := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h1
    simpa [one_div] using one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num) h2u
  rw [mdlSliceF, if_pos hc]
  exact Work.KMTPlan.A6.Tle_piExact_eq_Tm_ssu ρ hρ hρ1 l₁
    (-(Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)) (varphiNtj (Nat.floor (a n)) k₁ j₁ t)
    hMper hf hcplt hnA hΦ

/-! ## The main theorem -/

theorem mdlSliceF_fiberVarSampling (r : NNReal) (hr : 2 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤), ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (C₀ : ℕ) (a : ℕ → NNReal) (Λ : NNReal) (hΛ : 1 < Λ)
          (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n)
          (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (j₁ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ))
          (hk₁ : k₁ = 0 → j₁ ≠ -1) (f : ℤ → ℂ),
          MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
          t ∈ Set.Icc (1 / 2 : ℝ) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.KMTAreas.A7.residueLp p.toReal (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
                (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  Work.KMTAreas.A7.fiberOp ρ l₁
                    (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
                      (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
                    n₀ (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) y)) x) p
              MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm (fun x : ℤ =>
                  PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                    Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n x)) p
                  MeasureTheory.Measure.count := by
  refine ⟨0, le_refl 0, 1, one_pos, ?_⟩
  intro p hp hptop ρ hρ hρ1
  have hpR : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hptop.ne).mpr hp
  have hp0R : (0 : ℝ) < p.toReal := lt_trans zero_lt_one hpR
  have hpne : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  -- the large-scale thresholds
  obtain ⟨Bf, hBf⟩ := Work.KMTAreas.A7.farey_and_strict_of_large_L ρ hρ hρ1
  obtain ⟨Cρ₁, hCρ₁pos, hCρ₁⟩ := Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing hρ
  obtain ⟨B₁, hB₁⟩ := goodMajorArcs_uScale_of_large ρ hρ Cρ₁ hCρ₁pos
  obtain ⟨Cρ₂, hCρ₂pos, hCρ₂⟩ := Work.A7Hi.sep_iwArithFreqsNew_of_goodMajorArcs ρ hρ hρ1
  obtain ⟨B₂, hB₂⟩ := goodMajorArcs_uScale_of_large ρ hρ Cρ₂ hCρ₂pos
  let B : ℕ := max Bf (max B₁ B₂)
  obtain ⟨Cqa, hCqa_pos, hCqa⟩ :=
    Work.KMTAreas.A7.fibreVarSampling_quarter ρ p.toReal hpR r hr
  obtain ⟨Ccr, hCcr_pos, hCcr⟩ :=
    fiberVarSampling_crude r hr ρ hρ hρ1 p hp hptop (fun _ => B)
  refine ⟨max Cqa Ccr, lt_max_of_lt_left hCqa_pos, ?_⟩
  intro C₀ a Λ hΛ ha ha1 l₁ l₂ k₁ k₂ t j₁ hj₁ hk₁ f hf2 ht
  let L : ℕ := lcL l₁ l₂ k₁ k₂
  let U : ℕ := Work.KMTAreas.A7.uScale ρ L
  let q : ℕ := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)
  let h : ℕ → ℤ → ℂ := mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f
  have hqpos : 0 < q := Work.KMTAreas.A7.arithQ_pos ρ _
  have hU1 : 1 ≤ U := Work.KMTAreas.A7.one_le_uScale ρ hρ.le L
  have hLW : Work.KMTAreas.A7.lossWeight 0 ρ l₁ l₂ k₁ k₂ = 1 := by
    rw [Work.KMTAreas.A7.lossWeight]
    simp
  have hgoal : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal q
        (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Work.KMTAreas.A7.fiberOp ρ l₁ (Work.KMTAreas.A7.mStarF U) n₀ (h n) y)) x) p
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (max Cqa Ccr * Work.KMTAreas.A7.lossWeight 0 ρ l₁ l₂ k₁ k₂) *
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => h n x)) p MeasureTheory.Measure.count := by
    rcases eq_or_ne l₁ 0 with hl₁ | hl₁
    · -- the arithmetic level is `0`: every fibre vanishes
      subst hl₁
      have hVr : ∀ (x : ℤ) (n₀ : ℤ), PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Work.KMTAreas.A7.fiberOp ρ 0 (Work.KMTAreas.A7.mStarF U) n₀ (h n) x) = 0 := by
        intro x n₀
        rw [show (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ 0 (Work.KMTAreas.A7.mStarF U)
              (n₀ : ℤ) (h n) x) = fun _ : ℕ => (0 : ℂ) from
            funext fun n => congrFun (fiberOp_level_zero ρ (Work.KMTAreas.A7.mStarF U)
              n₀ (h n)) x]
        exact variationalNorm_zero (le_trans (by norm_num : (1 : NNReal) ≤ 2) (le_of_lt hr))
      have hfunW : (fun y : ℤ => fun n₀ : ℕ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ 0 (Work.KMTAreas.A7.mStarF U)
              (n₀ : ℤ) (h n) y))
          = (fun y : ℤ => fun n₀ : ℕ => (0 : ENNReal)) := by
        funext y
        funext n₀
        exact hVr y (n₀ : ℤ)
      have hfun : (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal q
          (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            Work.KMTAreas.A7.fiberOp ρ 0 (Work.KMTAreas.A7.mStarF U) (n₀ : ℤ) (h n) y)) x)
          = fun _ : ℤ => (0 : ENNReal) := by
        rw [hfunW]
        exact residueLp_zero_eq p.toReal hp0R q
      rw [hfun, show MeasureTheory.eLpNorm (fun _ : ℤ => (0 : ENNReal)) p
          MeasureTheory.Measure.count = 0 from eLpNorm_zero]
      exact bot_le
    · -- the arithmetic level is positive
      have hl₁1 : 1 ≤ l₁ := Nat.one_le_iff_ne_zero.mpr hl₁
      have hBf_le : Bf ≤ B := le_max_left _ _
      have hB₁_le : B₁ ≤ B := le_trans (le_max_left _ _) (le_max_right _ _)
      have hB₂_le : B₂ ≤ B := le_trans (le_max_right _ _) (le_max_right _ _)
      have hLl₁ : l₁ ≤ L := by
        show l₁ ≤ max (max l₁ l₂) (max k₁ k₂)
        omega
      by_cases hcase : L ≤ B
      · -- bounded scales: the crude Young bound
        have hcrude := hCcr l₁ l₂ k₁ k₂ (show max (max l₁ l₂) (max k₁ k₂) ≤ B from hcase) h
        refine hcrude.trans ?_
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
        rw [hLW, mul_one]
        exact le_max_right _ _
      · -- large scales: the band-limited estimate
        push_neg at hcase
        have hNpos : ∀ n : ℕ, mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → 0 < Nat.floor (a n) := by
          intro n hc
          have hlt : Work.KMTAreas.A7.splitCut ρ L < Nat.floor (a n) :=
            ((mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hc).2.1
          have h1 : 1 ≤ Work.KMTAreas.A7.splitCut ρ L := by
            rw [Work.KMTAreas.A7.splitCut]; exact Nat.one_le_two_pow
          omega
        have hcore : ∀ n : ℕ, mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n →
            (2 : ℝ) ^ k₁ * ((Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℕ) : ℝ) * 8
                ≤ ((Nat.floor (a n) : ℕ) : ℝ) ∧
              k₁ + 2 * U + 1 ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat := by
          intro n hc
          have hsplit : Work.KMTAreas.A7.splitCut ρ L < Nat.floor (a n) :=
            ((mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hc).2.1
          have hBlt : Bf < max (max l₁ l₂) (max k₁ k₂) := lt_of_le_of_lt hBf_le hcase
          exact hBf l₁ l₂ k₁ k₂ (Nat.floor (a n)) hsplit hBlt
        set W : ℕ → ℝ := fun n => if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
              (2 : ℝ) ^ ((k₁ : ℝ) - (((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ)) : ℝ))
            else min ((2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) (1 / (8 * (q : ℝ))) with hWdef
        have hWpos : ∀ n : ℕ, 0 < W n := by
          intro n
          simp only [hWdef]
          by_cases hc : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
          · simp only [hc, if_true]; positivity
          · simp only [hc, if_false]
            exact lt_min (by positivity) (by positivity)
        have hWq : ∀ n : ℕ, W n * (q : ℝ) ≤ 1 / 4 := by
          intro n
          simp only [hWdef]
          by_cases hc : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
          · simp only [hc, if_true]
            exact (bandRadius_le k₁ U (Nat.floor (a n)) q (hNpos n hc)
              (hcore n hc).1 (hcore n hc).2).2
          · simp only [hc, if_false]
            have hqposR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
            calc min ((2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) (1 / (8 * (q : ℝ))) * (q : ℝ)
                ≤ (1 / (8 * (q : ℝ))) * (q : ℝ) :=
                  mul_le_mul_of_nonneg_right (min_le_right _ _) hqposR.le
              _ = 1 / 8 := by field_simp
              _ ≤ 1 / 4 := by norm_num
        have hWle : ∀ n : ℕ, W n ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) := by
          intro n
          simp only [hWdef]
          by_cases hc : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
          · simp only [hc, if_true]
            exact (bandRadius_le k₁ U (Nat.floor (a n)) q (hNpos n hc)
              (hcore n hc).1 (hcore n hc).2).1
          · simp only [hc, if_false]
            exact min_le_left _ _
        have hsep : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
            ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁, α ≠ β →
              2 * (2 : ℝ) ^ (-(2 * (U : ℤ))) ≤ ‖α - β‖ := by
          intro α hα β hβ hne
          have hgma : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ₂ l₁ (-(2 * (U : ℤ))) :=
            (hB₂ l₁ L hLl₁ (le_of_lt (lt_of_le_of_lt hB₂_le hcase))).2
          have h4 := hCρ₂ l₁ (-(2 * (U : ℤ))) (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁)
            hgma Finset.Subset.rfl α hα β hβ hne
          have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(2 * (U : ℤ))) := zpow_pos (by norm_num) _
          linarith
        have htors : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁, q • α = 0 := by
          intro α hα
          exact Work.KMTAreas.A7.arithQ_nsmul_eq_zero
            (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 (le_max_left l₁ l₂)
              (Work.KMTAreas.A7.mem_iwArithFreqsNew_le hα))
        have hband : ∀ n : ℕ, ∃ hw : Memℓp (h n) 2,
            Work.BourgainPlan.IonescuWainger.HasFreqSupport (h n) hw
              (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
                Work.BourgainPlan.IonescuWainger.arcSet α (W n)) := by
          intro n
          by_cases hc : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
          · have hN := hNpos n hc
            obtain ⟨M, hM0, hMbd, hMper, hMarc⟩ :=
              varphiNtjPeriodize_aux (Nat.floor (a n)) k₁ j₁ t hj₁ hk₁ hN
            have hrad : (2 : ℝ) ^ ((k₁ : ℝ) -
                  (((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ)) : ℝ))
                ≤ (2 : ℝ) ^ (-(U : ℤ) - 1) := by
              have h1 := (bandRadius_le k₁ U (Nat.floor (a n)) q hN
                (hcore n hc).1 (hcore n hc).2).1
              exact le_trans h1 (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))
            have hΦ : Work.Analysis.IonescuWainger.SupportedInArc (-(U : ℤ) - 1)
                (Work.Analysis.IonescuWainger.periodize (varphiNtj (Nat.floor (a n)) k₁ j₁ t)) :=
              supportedInArc_of_arcSet_le U _ _ hMarc hrad
            have hnA : Work.Analysis.IonescuWainger.NonAliasing (-(U : ℤ))
                (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁) :=
              hCρ₁ l₁ (-(U : ℤ))
                ((hB₁ l₁ L hLl₁ (le_of_lt (lt_of_le_of_lt hB₁_le hcase))).1)
            have heq : h n = Work.KMTAreas.A7.Tm ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t) f :=
              mdlSliceF_eq_Tm ρ hρ hρ1 C₀ a l₁ l₂ k₁ k₂ j₁ t f n hj₁ hk₁ hc hf2 hnA hΦ
            rw [heq]
            obtain ⟨hw, hsup⟩ := tmBandOfArc ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t)
              ((2 : ℝ) ^ ((k₁ : ℝ) -
                (((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ)) : ℝ)))
              hMper hMarc f (memlpOfMemLpCount (p := 2) (by norm_num) (by norm_num) hf2)
            refine ⟨hw, ?_⟩
            rw [Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew hl₁] at hsup
            simp only [hWdef, hc, if_true]
            exact hsup
          · have hzero : h n = 0 := by
              show mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n = 0
              simp only [mdlSliceF, hc, if_false]
            rw [hzero]
            exact Work.KMTPlan.A6.zero_hasFreqSupport _
        have hm := hCqa l₁ U hU1 q hqpos W h hWpos hWq hWle hsep htors hband
        rw [ENNReal.ofReal_toReal hptop.ne] at hm
        exact hm.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by
          rw [hLW, mul_one]; exact le_max_left _ _)) bot_le)
  exact hgoal

end

end Work.KMTPlan.A6Clean
