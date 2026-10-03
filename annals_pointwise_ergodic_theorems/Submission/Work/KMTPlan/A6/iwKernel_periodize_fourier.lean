import Mathlib
import Submission.Work.KMTAreas.A7.IwKernelEqFourier
import Submission.Work.KMTAreas.A7.ModelOps

/-!
# The IW kernel of `iwSymbolSet A (periodize F)` is the Fourier transform of a sum of translates

Generalises the Poisson-summation identity `iwKernel_periodize` from a single periodised cutoff to
the Ionescu--Wainger symbol built from a finite set `A ⊆ ℝ/ℤ` of arithmetic frequencies: for
continuous compactly supported `F : ℝ → ℂ` and `a_α = (AddCircle.equivIco 1 0 α).val ∈ [0,1)`,

`iwKernel (iwSymbolSet A (periodize F)) j = 𝓕 (fun y => ∑_{α ∈ A} F (y - a_α)) j`.

The proof is the Fourier-coefficient half of Poisson summation (Mathlib's
`Real.fourierCoeff_tsum_comp_add`) applied to the continuous compactly supported function
`G y = ∑_{α ∈ A} F (y - a_α)`: the point is that `iwSymbolSet A (periodize F)` is exactly the
periodisation of `G`, i.e. the periodic lift of the sum of all integer translates of `G`, and
compact support supplies the local uniform summability hypothesis.

The same argument, specialised to `F = etaCut kmtEta k` and `A = iwArithFreqs ρ l`, is
`Work.KMTAreas.A7.IwKernelEqFourier`; here `F` is arbitrary and the support radius is abstract.
-/

set_option autoImplicit false

open MeasureTheory

namespace Work.KMTPlan.A6

/-- A function with compact support on `ℝ` vanishes beyond some radius. -/
private lemma exists_radius_of_hasCompactSupport_aux {ψ : ℝ → ℂ} (hs : HasCompactSupport ψ) :
    ∃ R : ℝ, ∀ y : ℝ, R ≤ |y| → ψ y = 0 := by
  obtain ⟨K, hK, hK0⟩ := (exists_compact_iff_hasCompactSupport (f := ψ)).mpr hs
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hK.isBounded
  refine ⟨r + 1, fun y hy => hK0 y fun hyK => ?_⟩
  have hyr : |y| ≤ r := by
    have h := hr hyK
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
  linarith

theorem iwKernel_periodize_fourier (A : Finset Work.Analysis.IonescuWainger.Circle) {F : ℝ → ℂ}
    (hFc : Continuous F) (hFcs : HasCompactSupport F) (j : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet A
          (Work.Analysis.IonescuWainger.periodize F)) j
      = FourierTransform.fourier (fun y : ℝ =>
          ∑ α ∈ A, F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)) (j : ℝ) := by
  -- A radius `R` outside which `F` vanishes.
  obtain ⟨R, hR⟩ := exists_radius_of_hasCompactSupport_aux hFcs
  -- A real representative `a α ∈ [0,1)` of each arithmetic frequency.
  set a : Work.Analysis.IonescuWainger.Circle → ℝ :=
    fun α => (AddCircle.equivIco (1 : ℝ) 0 α).val with ha
  have ha_coe : ∀ α : Work.Analysis.IonescuWainger.Circle,
      ((a α : ℝ) : Work.Analysis.IonescuWainger.Circle) = α := by
    intro α; rw [ha]; exact AddCircle.coe_equivIco
  have ha_mem : ∀ α : Work.Analysis.IonescuWainger.Circle, a α ∈ Set.Ico (0 : ℝ) 1 := by
    intro α; rw [ha]; simpa using (AddCircle.equivIco (1 : ℝ) 0 α).2
  have ha_abs : ∀ α : Work.Analysis.IonescuWainger.Circle, |a α| ≤ 1 := by
    intro α
    obtain ⟨h1, h2⟩ := ha_mem α
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- The single function on `ℝ` whose periodisation is the IW symbol:
  -- `G y = ∑_{α ∈ A} F (y - a α)`.
  set G : ℝ → ℂ := fun y => ∑ α ∈ A, F (y - a α) with hG
  have hGcont : Continuous G := by
    rw [hG]
    exact continuous_finsetSum _ (fun α _ => hFc.comp (continuous_id.sub continuous_const))
  have hGzero : ∀ y : ℝ, R + 1 ≤ |y| → G y = 0 := by
    rw [hG]; intro y hy
    refine Finset.sum_eq_zero (fun α _ => hR _ ?_)
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
  set N : ℤ := ⌊R⌋ + 2 with hN
  set S : Finset ℤ := Finset.Icc (-N) N with hS
  have hRltN : R + 1 < ((N : ℤ) : ℝ) := by
    have h := Int.lt_floor_add_one R
    rw [hN]; push_cast; linarith
  have hvan : ∀ (t : ℝ) (n : ℤ), |t| < 1 → n ∉ S → F (t + n) = 0 := by
    intro t n ht hn
    apply hR
    have hnot : ¬ ((-N : ℤ) ≤ n ∧ n ≤ N) := by simpa [hS, Finset.mem_Icc] using hn
    rw [not_and_or, not_le, not_le] at hnot
    have habs : ((N:ℝ)) < |(n:ℝ)| := by
      rcases hnot with h | h
      · have h' : ((N:ℝ)) < -((n:ℝ)) := by
          have : (n:ℝ) < -((N:ℝ)) := by exact_mod_cast h
          linarith
        linarith [neg_le_abs (n:ℝ)]
      · have h' : ((N:ℝ)) < (n:ℝ) := by exact_mod_cast h
        linarith [le_abs_self (n:ℝ)]
    have h5 := abs_sub_abs_le_abs_sub (n:ℝ) (-t)
    rw [abs_neg, sub_neg_eq_add] at h5
    have h6 : R < |(n:ℝ) + t| := by linarith
    rw [add_comm] at h6
    exact le_of_lt h6
  -- **The symbol is the periodisation of `G`.**  Evaluating at `ξ = (u : ℝ/ℤ)` and using
  -- `periodizeCoeEqTsum` on each translate, both sides reduce (after `tsum_eq_sum` on `S`) to
  -- the same finite double sum.
  have hSymb : Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize F) = Function.Periodic.lift hper := by
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

end Work.KMTPlan.A6
