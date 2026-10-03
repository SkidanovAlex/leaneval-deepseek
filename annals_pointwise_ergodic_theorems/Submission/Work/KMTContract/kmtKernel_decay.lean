import Mathlib
import Submission.Work.KMTContract.etaCutRegular
import Submission.Work.KMTContract.fourierDecayRefl
import Submission.Work.KMTContract.periodizeCoeEqTsum
import Submission.Work.KMTContract.summableShiftRestrict

namespace Work.KMTContract

open MeasureTheory

/-- **Decay of the Ionescu--Wainger kernel.** The kernel on `ℤ` of the IW projection
`kmtProj ρ l k` (the Fourier coefficients of the symbol `iwSymbolSet (iwArithFreqs ρ l) Φ` with
`Φ = periodize (etaCut kmtEta k)`, the periodisation of the fixed smooth compactly supported
cutoff `kmtEta` rescaled by `2^k`) decays like `j^{-2}`, uniformly in `j`, with a constant
depending on the (fixed) parameters `ρ, l, k`.

Suggested route: (i) `etaCut kmtEta k` is `C^∞` with compact support (`ContDiff.contDiffBump`,
`kmtEta`'s support is in `[-2^k, 2^k]`); (ii) its periodisation is `C^∞` on the circle; (iii) for a
`C^2` function `g` on the circle, integrate by parts twice
(`fourierCoeffOn_of_hasDerivAt`, `fourierCoeff_eq_intervalIntegral`) to get
`∃ C, ∀ n, ‖fourierCoeff g n‖ ≤ C / (1 + |n|)^2`; (iv) `fourierCoeff` of a translate
`ξ ↦ g (ξ - α)` is a unimodular phase times that, so the finite sum `iwSymbolSet` costs a factor
`(iwArithFreqs ρ l).card`. Any constant is fine; only the `j^{-2}` rate matters. Helper lemmas are
welcome (same file, or new files under `Submission/Work/KMTContract/`). -/
theorem kmtKernel_decay (ρ : ℝ) (l : ℕ) (k : ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℤ,
      ‖Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize
            (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j‖
        ≤ C / (1 + |(j : ℝ)|) ^ 2 := by
  -- The rescaled cutoff `F = η_{≤k}`, its properties (`etaCutRegular`), the finite frequency set
  -- `A = (ℚ/ℤ)_{≤l}`, and a real representative `a α ∈ [0,1)` of each `α ∈ A`.
  set F : ℝ → ℂ := Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k with hF
  have hFcd : ContDiff ℝ (↑(⊤ : ℕ∞)) F := by rw [hF]; exact (etaCutRegular k).1
  have hF2 : ContDiff ℝ 2 F := hFcd.of_le (WithTop.coe_le_coe.mpr le_top)
  have hFcont : Continuous F := hFcd.continuous
  have hFzero : ∀ θ : ℝ, (2:ℝ)^k ≤ |θ| → F θ = 0 := by
    rw [hF]; exact (etaCutRegular k).2.2
  set A : Finset Work.Analysis.IonescuWainger.Circle :=
    Work.Analysis.IonescuWainger.iwArithFreqs ρ l with hA
  set a : Work.Analysis.IonescuWainger.Circle → ℝ :=
    fun α => (AddCircle.equivIco (1:ℝ) 0 α).val with ha
  have ha_coe : ∀ α : Work.Analysis.IonescuWainger.Circle,
      ((a α : ℝ) : Work.Analysis.IonescuWainger.Circle) = α := by
    intro α; rw [ha]; exact AddCircle.coe_equivIco
  have ha_mem : ∀ α : Work.Analysis.IonescuWainger.Circle, a α ∈ Set.Ico (0:ℝ) 1 := by
    intro α; rw [ha]; simpa using (AddCircle.equivIco (1:ℝ) 0 α).2
  have ha_abs : ∀ α : Work.Analysis.IonescuWainger.Circle, |a α| ≤ 1 := by
    intro α
    obtain ⟨h1, h2⟩ := ha_mem α
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- The single function on `ℝ` whose periodisation is the IW symbol:
  -- `G y = ∑_{α ∈ A} F (y - a α)`.
  set G : ℝ → ℂ := fun y => ∑ α ∈ A, F (y - a α) with hG
  have hGcont : Continuous G := by
    rw [hG]
    exact continuous_finsetSum _ (fun α _ => hFcont.comp (continuous_id.sub continuous_const))
  have hGcd : ContDiff ℝ 2 G := by
    rw [hG]; exact ContDiff.sum (fun α _ => hF2.comp (contDiff_id.sub contDiff_const))
  have hGzero : ∀ y : ℝ, (2:ℝ)^k + 1 ≤ |y| → G y = 0 := by
    rw [hG]; intro y hy
    refine Finset.sum_eq_zero (fun α _ => hFzero _ ?_)
    have h1 : |a α| ≤ 1 := ha_abs α
    have h2 : |y| - |a α| ≤ |y - a α| := abs_sub_abs_le_abs_sub y (a α)
    linarith
  have hGcs : HasCompactSupport G := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (-((2:ℝ)^k + 1)) ((2:ℝ)^k + 1)) isCompact_Icc ?_
    intro y hy
    have h : ¬ ((2:ℝ)^k + 1 ≤ |y|) := fun hh => hy (hGzero y hh)
    rw [not_le, abs_lt] at h
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  -- Local uniform summability of the translates of `G` (used both for the Poisson-summation
  -- identity of Mathlib and for evaluating the `tsum` of continuous maps).
  have hGsumm : ∀ K : TopologicalSpace.Compacts ℝ, Summable fun n : ℤ =>
      ‖((⟨G, hGcont⟩ : ContinuousMap ℝ ℂ).comp (ContinuousMap.addRight (n : ℝ))).restrict K‖ :=
    fun K => summableShiftRestrict hGcont hGzero K
  -- Two integrations by parts on `ℝ` for `G` (`fourierDecayRefl`).
  obtain ⟨C, hCpos, hC⟩ := fourierDecayRefl hGcd hGcs
  have hper : Function.Periodic (⇑(∑' n : ℤ,
      (⟨G, hGcont⟩ : ContinuousMap ℝ ℂ).comp (ContinuousMap.addRight (n • (1:ℝ))))) 1 :=
    (⟨G, hGcont⟩ : ContinuousMap ℝ ℂ).periodic_tsum_comp_add_zsmul 1
  have hsum : Summable (fun n : ℤ =>
      (⟨G, hGcont⟩ : ContinuousMap ℝ ℂ).comp (ContinuousMap.addRight (n • (1:ℝ)))) :=
    ContinuousMap.summable_of_locally_summable_norm (fun K => by
      simpa [Int.smul_one_eq_cast] using hGsumm K)
  -- The cutoff `S` outside which all terms of the `tsum`s below vanish.
  set N : ℤ := ⌊(2:ℝ)^k⌋ + 2 with hN
  have hNnn : (0:ℝ) ≤ (N:ℝ) := by
    have h1 : (0:ℤ) ≤ ⌊(2:ℝ)^k⌋ := by
      rw [Int.le_floor]
      simp only [Int.cast_zero]
      exact le_of_lt (zpow_pos (by norm_num : (0:ℝ) < 2) k)
    have h2 : (0:ℤ) ≤ N := by rw [hN]; linarith
    exact_mod_cast h2
  set S : Finset ℤ := Finset.Icc (-N) N with hS
  have hvan : ∀ (t : ℝ) (n : ℤ), |t| < 1 → n ∉ S → F (t + n) = 0 := by
    intro t n ht hn
    apply hFzero
    have hnot : ¬ ((-N : ℤ) ≤ n ∧ n ≤ N) := by simpa [hS, Finset.mem_Icc] using hn
    rw [not_and_or, not_le, not_le] at hnot
    have habs : ((N:ℝ)) < |(n:ℝ)| := by
      rcases hnot with h | h
      · have h' : (n:ℝ) < -((N:ℝ)) := by exact_mod_cast h
        rw [abs_of_neg (by linarith : (n:ℝ) < 0)]
        linarith
      · have h' : ((N:ℝ)) < (n:ℝ) := by exact_mod_cast h
        rw [abs_of_pos (by linarith : (0:ℝ) < n)]
        linarith
    have hNlt : (2:ℝ)^k + 1 < ((N:ℝ)) := by
      rw [hN]; push_cast; linarith [Int.lt_floor_add_one ((2:ℝ)^k)]
    have h5 := abs_sub_abs_le_abs_sub (n:ℝ) (-t)
    rw [abs_neg, sub_neg_eq_add] at h5
    have h6 : (2:ℝ)^k < |(n:ℝ) + t| := by linarith
    rw [add_comm] at h6
    exact le_of_lt h6
  -- **The symbol is the periodisation of `G`.**  Evaluating at `ξ = (u : ℝ/ℤ)` and using
  -- `periodizeCoeEqTsum` on each translate, both sides reduce (after `tsum_eq_sum` on `S`) to
  -- the same finite double sum.
  have hSymb : Work.Analysis.IonescuWainger.iwSymbolSet A (Work.Analysis.IonescuWainger.periodize F)
      = Function.Periodic.lift hper := by
    funext ξ
    set u : ℝ := (AddCircle.equivIco (1:ℝ) 0 ξ).val with hudef
    have huξ : ((u : ℝ) : Work.Analysis.IonescuWainger.Circle) = ξ := by
      rw [hudef]; exact AddCircle.coe_equivIco
    have hu_mem : u ∈ Set.Ico (0:ℝ) 1 := by
      rw [hudef]; simpa using (AddCircle.equivIco (1:ℝ) 0 ξ).2
    have hsmall : ∀ α : Work.Analysis.IonescuWainger.Circle, |u - a α| < 1 := by
      intro α
      obtain ⟨h1, h2⟩ := ha_mem α
      obtain ⟨h3, h4⟩ := hu_mem
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    have hLHS : Work.Analysis.IonescuWainger.iwSymbolSet A
          (Work.Analysis.IonescuWainger.periodize F) ξ
        = ∑ α ∈ A, ∑' n : ℤ, F (u - a α + n) := by
      simp only [Work.Analysis.IonescuWainger.iwSymbolSet]
      refine Finset.sum_congr rfl (fun α _ => ?_)
      have hcoe : (((u - a α) : ℝ) : Work.Analysis.IonescuWainger.Circle)
          = ((u:ℝ) : Work.Analysis.IonescuWainger.Circle)
            - ((a α : ℝ) : Work.Analysis.IonescuWainger.Circle) :=
        AddCircle.coe_sub (1:ℝ) u (a α)
      have harg : ξ - α = (((u - a α) : ℝ) : Work.Analysis.IonescuWainger.Circle) := by
        conv_lhs => rw [huξ.symm, (ha_coe α).symm, ← hcoe]
      rw [harg, periodizeCoeEqTsum]
    have hRHS : Function.Periodic.lift hper ξ = ∑' n : ℤ, ∑ α ∈ A, F (u + n - a α) := by
      rw [← huξ, Function.Periodic.lift_coe]
      rw [← ContinuousMap.tsum_apply hsum u]
      refine tsum_congr (fun n => ?_)
      have h1 : ((⟨G, hGcont⟩ : ContinuousMap ℝ ℂ).comp
            (ContinuousMap.addRight (n • (1:ℝ)))) u = G (u + (n:ℝ)) := by
        simp only [ContinuousMap.comp_apply, ContinuousMap.coe_addRight, Int.smul_one_eq_cast]
        rfl
      rw [h1, hG]
    rw [hLHS, hRHS]
    have h1 : ∀ α : Work.Analysis.IonescuWainger.Circle,
        (∑' n : ℤ, F (u - a α + n)) = ∑ n ∈ S, F (u - a α + n) := by
      intro α
      exact tsum_eq_sum (fun n hn => hvan (u - a α) n (hsmall α) hn)
    have h2 : (∑' n : ℤ, ∑ α ∈ A, F (u + n - a α))
        = ∑ n ∈ S, ∑ α ∈ A, F (u + n - a α) := by
      refine tsum_eq_sum (fun n hn => ?_)
      refine Finset.sum_eq_zero (fun α _ => ?_)
      have hthis : F ((u - a α) + (n:ℝ)) = 0 := hvan (u - a α) n (hsmall α) hn
      rwa [show (u - a α) + (n:ℝ) = u + (n:ℝ) - a α from by ring] at hthis
    rw [Finset.sum_congr rfl (fun α _ => h1 α), h2, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun α _ => ?_))
    congr 1
    ring
  -- The Fourier coefficient of the symbol is the Fourier transform of `G` (Poisson summation).
  have hfourier : ∀ j : ℤ, Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.Analysis.IonescuWainger.periodize F)) j
      = FourierTransform.fourier G (j:ℝ) := by
    intro j
    rw [Work.Analysis.IWMultiplier.iwKernel, hSymb]
    exact Real.fourierCoeff_tsum_comp_add (f := (⟨G, hGcont⟩ : ContinuousMap ℝ ℂ))
      (fun K => hGsumm K) j
  exact ⟨C, hCpos, fun j => by rw [hfourier j]; exact hC (j:ℝ)⟩

end Work.KMTContract
