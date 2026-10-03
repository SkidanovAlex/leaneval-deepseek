import Mathlib
import Submission.Work.KMTPlan.A6.mdlF_two_le
import Submission.Work.KMTPlan.A6.iwP_pred_le
import Submission.Work.KMTPlan.A6.iwConv_finsetSum_of_l2

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTContract

noncomputable section

/-- `Tle ρ l` vanishes on the zero symbol. -/
lemma Tle_zero_symbol (ρ : ℝ) (l : ℕ) (f : ℤ → ℂ) :
    Work.KMTAreas.A7.Tle ρ l (0 : ℝ → ℂ) f = 0 := by
  rw [Work.KMTAreas.A7.Tle]
  have hpz : periodize (0 : ℝ → ℂ) = 0 := by
    funext ξ
    simp [periodize]
  rw [hpz]
  funext y
  rw [iwConv_apply, iwSymbolSet_zero]
  simp [iwKernel, fourierCoeff]

theorem mdlComposite_uniformSigns_le
    (ρ : ℝ) (l₁ u : ℕ) (k : ℤ) (hk : (2 : ℝ) ^ k < 1 / 2)
    (Q : ℕ) (hQ : ∀ q ∈ Work.Analysis.IonescuWainger.iwP ρ l₁, q ≤ Q)
    (Φ : ℕ → ℝ → ℂ) (hΦm : ∀ n, Measurable (Φ n))
    (hΦsupp : ∀ n ξ, Φ n ξ ≠ 0 → ξ ∈ Work.Analysis.IonescuWainger.realArc k)
    (M : ℝ) (hM : 0 ≤ M)
    (hsup : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (ξ : ℝ),
      ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * Φ n ξ‖ ≤ M)
    (U : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ) :
    MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
        Work.KMTAreas.A7.Tle ρ l₁ (Φ n) (Work.KMTPlan.A6.mdlF ρ u l₁ f) x)
      2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((1 + 2 * (2 : ℝ) ^ k * (Q : ℝ) ^ 2) * M
          * (2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2)))
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  set A : Finset Circle := iwArithFreqs ρ l₁ with hA
  set c : ℕ → ℂ := fun n => if ω n then (1 : ℂ) else -1 with hc
  set Ψ : ℝ → ℂ := fun ξ => ∑ n ∈ U, c n * Φ n ξ with hΨ
  -- the pointwise bound on each `Φ n`
  have hΦbd : ∀ n ξ, ‖Φ n ξ‖ ≤ M := by
    intro n ξ
    have h := hsup {n} (fun _ => true) ξ
    simpa using h
  -- the sup bound on the combined symbol
  have hΨm : Measurable Ψ := by
    rw [hΨ]
    exact Finset.measurable_sum U fun n _ => (hΦm n).const_mul _
  have hΨsupp : ∀ ξ : ℝ, Ψ ξ ≠ 0 → ξ ∈ realArc k := by
    intro ξ hξ
    by_contra hcon
    refine hξ ?_
    rw [hΨ]
    refine Finset.sum_eq_zero fun n _ => ?_
    have : Φ n ξ = 0 := by
      by_contra hne
      exact hcon (hΦsupp n ξ hne)
    rw [this, mul_zero]
  have hΨsupp' : ∀ ξ : ℝ, Ψ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ k := by
    intro ξ hξ
    have h := hΨsupp ξ hξ
    rw [realArc, Set.mem_Icc] at h
    exact abs_le.mpr ⟨h.1, h.2⟩
  have hΨbd : ∀ ξ : ℝ, ‖Ψ ξ‖ ≤ M := by
    intro ξ
    rw [hΨ]
    exact hsup U ω ξ
  have hsymbol : ∀ θ : Circle,
      ‖iwSymbolSet A (periodize Ψ) θ‖ ≤ (1 + 2 * (2 : ℝ) ^ k * (Q : ℝ) ^ 2) * M := by
    intro θ
    have h := mdlIwSymbolSet_sup_le ρ l₁ k hk Q hQ M hM Ψ hΨm hΨsupp' hΨbd θ
    simpa only [hA] using h
  have hsymbolMem : MemLp (iwSymbolSet A (periodize Ψ)) ⊤ circleMeasure := by
    rw [hA]
    exact memLp_iwSymbolSet _ (memLp_periodize_of_narrow hk hΨm hΨsupp hΨbd)
  by_cases hM0 : M = 0
  · -- ## the degenerate case `M = 0`: all the symbols vanish
    have hΦzero : ∀ n ξ, Φ n ξ = 0 := by
      intro n ξ
      have h := hΦbd n ξ
      rw [hM0] at h
      exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
    have hfun0 : (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
        Work.KMTAreas.A7.Tle ρ l₁ (Φ n) (mdlF ρ u l₁ f) x) = 0 := by
      funext x
      refine Finset.sum_eq_zero fun n _ => ?_
      have hΦn : Φ n = 0 := funext (hΦzero n)
      rw [hΦn, Tle_zero_symbol]
      simp
    rw [hfun0, hM0]
    simp
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    by_cases hf : eLpNorm f 2 Measure.count = ⊤
    · -- ## non-`ℓ²` input: the right-hand side is `⊤`
      have hcoe : (0 : ℝ) < (1 + 2 * (2 : ℝ) ^ k * (Q : ℝ) ^ 2) * M
          * (2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2)) := by
        have h1 : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
        have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(u : ℤ)) := zpow_pos (by norm_num) _
        have h3 : (0 : ℝ) ≤ (Q : ℝ) ^ 2 := sq_nonneg _
        have h4 : (0 : ℝ) < 1 + 2 * (2 : ℝ) ^ k * (Q : ℝ) ^ 2 := by nlinarith
        have h5 : (0 : ℝ) < 1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2 := by nlinarith
        exact mul_pos (mul_pos h4 hMpos) (by linarith)
      rw [hf, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hcoe)]
      exact le_top
    · -- ## the main case: `f ∈ ℓ²`
      have hfmem : MemLp f 2 Measure.count :=
        MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hf)
      have hFmem : MemLp (mdlF ρ u l₁ f) 2 Measure.count := memLp_mdlF ρ u l₁ hfmem
      -- the periodisation of the combined symbol
      have hP : periodize Ψ = fun ξ => ∑ n ∈ U, c n * periodize (Φ n) ξ := by
        have h1 : (∑ n ∈ U, c n • Φ n) = Ψ := by
          funext ξ
          simp only [hΨ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        have h2 := periodize_finset_smul U c (fun n => Φ n)
          (fun n _ x => summable_shift_of_narrow hk (hΦsupp n) x)
        rw [h1] at h2
        rw [h2]
        funext ξ
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      -- the combination of the signed sum into a single multiplier
      have hcombine : (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          Work.KMTAreas.A7.Tle ρ l₁ (Φ n) (mdlF ρ u l₁ f) x)
          = iwConv A (periodize Ψ) (mdlF ρ u l₁ f) := by
        have h1 : (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            Work.KMTAreas.A7.Tle ρ l₁ (Φ n) (mdlF ρ u l₁ f) x)
            = ∑ n ∈ U, c n • iwConv A (periodize (Φ n)) (mdlF ρ u l₁ f) := by
          funext x
          rw [Finset.sum_apply]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hc]
          simp only [Pi.smul_apply, smul_eq_mul]
          rfl
        rw [h1]
        have hInt : ∀ n ∈ U, Integrable (iwSymbolSet A (periodize (Φ n))) circleMeasure :=
          fun n _ => (memLp_iwSymbolSet A (memLp_periodize_of_narrow hk (hΦm n) (hΦsupp n)
            (hΦbd n))).integrable le_top
        have hκ : ∀ n ∈ U, Summable fun j : ℤ =>
            ‖iwKernel (iwSymbolSet A (periodize (Φ n))) j‖ ^ 2 := by
          intro n _
          have hmem2 : MemLp (iwSymbolSet A (periodize (Φ n))) 2 circleMeasure :=
            (memLp_iwSymbolSet A (memLp_periodize_of_narrow hk (hΦm n) (hΦsupp n)
              (hΦbd n))).mono_exponent le_top
          have hae := hmem2.coeFn_toLp
          have hsum := (hasSum_sq_fourierCoeff (hmem2.toLp
            (iwSymbolSet A (periodize (Φ n))))).summable
          refine hsum.congr fun j => ?_
          simp only [iwKernel]
          rw [congrFun (fourierCoeff_congr_ae hae) j]
        rw [iwConv_finsetSum_of_l2 A U c (fun n => periodize (Φ n)) (mdlF ρ u l₁ f)
          hFmem hInt hκ, hP]
      -- the two estimates
      have hstep1 : eLpNorm (iwConv A (periodize Ψ) (mdlF ρ u l₁ f)) 2 Measure.count
          ≤ ENNReal.ofReal ((1 + 2 * (2 : ℝ) ^ k * (Q : ℝ) ^ 2) * M)
            * eLpNorm (mdlF ρ u l₁ f) 2 Measure.count :=
        eLpNorm_iwConv_two_le_of_symbol_bound A (periodize Ψ)
          ((1 + 2 * (2 : ℝ) ^ k * (Q : ℝ) ^ 2) * M)
          (by positivity) hsymbol hsymbolMem (mdlF ρ u l₁ f) hFmem
      have hstep2 : eLpNorm (mdlF ρ u l₁ f) 2 Measure.count
          ≤ ENNReal.ofReal (2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2))
            * eLpNorm f 2 Measure.count :=
        mdlF_two_le ρ u l₁ Q hQ (iwP_pred_le ρ l₁ Q hQ) f
      rw [hcombine]
      calc eLpNorm (iwConv A (periodize Ψ) (mdlF ρ u l₁ f)) 2 Measure.count
          ≤ ENNReal.ofReal ((1 + 2 * (2 : ℝ) ^ k * (Q : ℝ) ^ 2) * M)
              * eLpNorm (mdlF ρ u l₁ f) 2 Measure.count := hstep1
        _ ≤ ENNReal.ofReal ((1 + 2 * (2 : ℝ) ^ k * (Q : ℝ) ^ 2) * M)
              * (ENNReal.ofReal (2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2))
                * eLpNorm f 2 Measure.count) := by
              gcongr
        _ = ENNReal.ofReal ((1 + 2 * (2 : ℝ) ^ k * (Q : ℝ) ^ 2) * M
              * (2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2)))
              * eLpNorm f 2 Measure.count := by
              have hsplit : ENNReal.ofReal ((1 + 2 * (2 : ℝ) ^ k * (Q : ℝ) ^ 2) * M
                    * (2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2)))
                  = ENNReal.ofReal ((1 + 2 * (2 : ℝ) ^ k * (Q : ℝ) ^ 2) * M)
                    * ENNReal.ofReal (2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2)) := by
                exact ENNReal.ofReal_mul (by
                  have h6 : (0 : ℝ) < 1 + 2 * (2 : ℝ) ^ k * (Q : ℝ) ^ 2 := by
                    have h1 : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
                    nlinarith [sq_nonneg (Q : ℝ)]
                  exact le_of_lt (mul_pos h6 hMpos))
              rw [hsplit, ← mul_assoc]

end

end Work.KMTPlan.A6
