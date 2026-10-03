import Mathlib
import Submission.Work.KMTContract.kmtKernel_decay

namespace Work.KMTAreas.A7

open MeasureTheory

/-
# The Ionescu--Wainger kernel as the Fourier transform of a sum of translates

For the symbol `Φ_k = periodize (etaCut kmtEta k)` (the periodisation of the rescaled cutoff
`η_{≤k}`) and the frequency set `A = iwArithFreqs ρ l`, the `j`-th Fourier coefficient
`iwKernel (iwSymbolSet A Φ_k) j` of the IW symbol is the value at `j ∈ ℤ ⊂ ℝ` of the Fourier
transform of

  `G(y) = ∑_{α ∈ A} η_{≤k} (y - a_α)`,   `a_α = (AddCircle.equivIco 1 0 α).val ∈ [0,1)`,

i.e. the Poisson-summation identity used verbatim at lines 100--135 of
`Submission/Work/KMTContract/kmtKernel_decay.lean` (the steps named `hSymb` and `hfourier`).
No hypothesis on `ρ` is needed. Copying that file's proof of those two steps (with `A`, `F`, `a`,
`G` and the helpers `etaCutRegular`, `periodizeCoeEqTsum`, `summableShiftRestrict`,
`Real.fourierCoeff_tsum_comp_add`) gives this statement almost verbatim.
-/
theorem IwKernelEqFourier (ρ : ℝ) (l : ℕ) (k : ℤ) (j : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize
            (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j
      = FourierTransform.fourier (fun y : ℝ =>
          ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
            Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k
              (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)) (j : ℝ) := by
  -- The rescaled cutoff `F = η_{≤k}`, its properties (`etaCutRegular`), the finite frequency set
  -- `A = (ℚ/ℤ)_{≤l}`, and a real representative `a α ∈ [0,1)` of each `α ∈ A`.
  set F : ℝ → ℂ := Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k with hF
  have hFcd : ContDiff ℝ (↑(⊤ : ℕ∞)) F := by rw [hF]; exact (Work.KMTContract.etaCutRegular k).1
  have hFcont : Continuous F := hFcd.continuous
  have hFzero : ∀ θ : ℝ, (2:ℝ)^k ≤ |θ| → F θ = 0 := by
    rw [hF]; exact (Work.KMTContract.etaCutRegular k).2.2
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
  have hGzero : ∀ y : ℝ, (2:ℝ)^k + 1 ≤ |y| → G y = 0 := by
    rw [hG]; intro y hy
    refine Finset.sum_eq_zero (fun α _ => hFzero _ ?_)
    have h1 : |a α| ≤ 1 := ha_abs α
    have h2 : |y| - |a α| ≤ |y - a α| := abs_sub_abs_le_abs_sub y (a α)
    linarith
  -- Local uniform summability of the translates of `G` (used both for the Poisson-summation
  -- identity of Mathlib and for evaluating the `tsum` of continuous maps).
  have hGsumm : ∀ K : TopologicalSpace.Compacts ℝ, Summable fun n : ℤ =>
      ‖((⟨G, hGcont⟩ : ContinuousMap ℝ ℂ).comp (ContinuousMap.addRight (n : ℝ))).restrict K‖ :=
    fun K => Work.KMTContract.summableShiftRestrict hGcont hGzero K
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
      rw [harg, Work.KMTContract.periodizeCoeEqTsum]
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
  rw [Work.Analysis.IWMultiplier.iwKernel, hSymb]
  exact Real.fourierCoeff_tsum_comp_add (f := (⟨G, hGcont⟩ : ContinuousMap ℝ ℂ))
    (fun K => hGsumm K) j

end Work.KMTAreas.A7
