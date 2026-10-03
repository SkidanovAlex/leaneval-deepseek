import Mathlib
import Submission.Work.KMTAreas.A7.SmallKernMassBasics

set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

local notation "Circ" => AddCircle (1 : ℝ)

/-! ## Auxiliary lemmas for `coeff_arithSymb_mul_iwSymbol` -/

lemma kmt_integral_mul_fourier_eq_fourierCoeff (Ψ : Circ → ℂ) (a : ℤ) :
    (∫ θ : Circ, Ψ θ * fourier (T := 1) (-a) θ ∂circleMeasure) = fourierCoeff Ψ a := by
  rw [fourierCoeff]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [smul_eq_mul]
  ring

lemma kmt_fourierCoeff_mul_periodize_sub {Ψ : Circ → ℂ} {m : ℝ → ℂ}
    (hΨ2 : MemLp Ψ 2 circleMeasure) (hm2 : MemLp (periodize m) 2 circleMeasure)
    (hΨs : Summable (fun n : ℤ => ‖fourierCoeff Ψ n‖)) (hm : Integrable m)
    (α : Circ) (a : ℤ) :
    fourierCoeff (fun θ : Circ => Ψ θ * periodize m (θ - α)) a
      = ∑' j : ℤ, fourierCoeff Ψ (a - j) * fourier (T := 1) (-j) α * cw m j := by
  have hm2' : MemLp (fun θ : Circ => periodize m (θ - α)) 2 circleMeasure := by
    have hmp := MeasureTheory.measurePreserving_add_right circleMeasure (-α)
    have h := hm2.comp_measurePreserving hmp
    rwa [show (periodize m ∘ fun x : Circ => x + -α)
        = (fun θ : Circ => periodize m (θ - α)) from by
          funext θ; simp [sub_eq_add_neg]] at h
  have hkey := Work.KMTAreas.A5.fourierCoeff_mul_eq_tsum_conv hΨ2 hm2' hΨs a
  rw [hkey]
  simp only [Work.KMTAreas.A7.fourierCoeff_comp_sub,
    Work.KMTPlan.A6.fourierCoeff_periodize_eq_cw hm]
  rw [← Equiv.tsum_eq (Equiv.subLeft a)
    (fun j : ℤ => fourierCoeff Ψ (a - j) * fourier (T := 1) (-j) α * cw m j)]
  refine tsum_congr (fun n => ?_)
  have h : a - (a - n) = n := by ring
  rw [Equiv.subLeft_apply, h]
  ring

lemma kmt_memLp_mul_fourier {f : Circ → ℂ} (hf : MemLp f ⊤ circleMeasure) (n : ℤ) :
    MemLp (fun θ : Circ => f θ * fourier (T := 1) n θ) ⊤ circleMeasure := by
  haveI : IsFiniteMeasure circleMeasure := inferInstance
  have hfou : MemLp (fun θ : Circ => fourier (T := 1) n θ) ⊤ circleMeasure :=
    MemLp.of_bound (fourier n).continuous.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun θ => by
        rw [fourier_apply]
        exact le_of_eq (_root_.Circle.norm_coe _))
  have h : MemLp (fun θ : Circ => f θ * fourier (T := 1) n θ) ⊤ circleMeasure := hf.mul hfou
  simpa only [Pi.mul_apply] using h

lemma kmt_MemLp_shift {F : Circ → ℂ} (hF : MemLp F ⊤ circleMeasure) (α : Circ) :
    MemLp (fun θ : Circ => F (θ - α)) ⊤ circleMeasure := by
  have h := hF.comp_measurePreserving
    (MeasureTheory.measurePreserving_add_right circleMeasure (-α))
  rwa [show (F ∘ fun x : Circ => x + -α) = (fun θ : Circ => F (θ - α)) from by
    funext θ; simp [sub_eq_add_neg]] at h

lemma kmt_norm_varphitildeN_le_two (d N k : ℕ) (x : ℝ) : ‖varphitildeN d N k x‖ ≤ 2 := by
  rw [varphitildeN]
  split_ifs with hk
  · exact le_trans (Work.KMTContract.norm_kmtEta_le _) (by norm_num)
  · calc ‖Work.KMTContract.kmtEta
            ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * x)
          - Work.KMTContract.kmtEta
            ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * x)‖
        ≤ ‖Work.KMTContract.kmtEta
              ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * x)‖
          + ‖Work.KMTContract.kmtEta
              ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * x)‖ :=
          norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (Work.KMTContract.norm_kmtEta_le _)
          (Work.KMTContract.norm_kmtEta_le _)
      _ = 2 := by norm_num

lemma kmt_MemLp_periodize_mStarF (u : ℕ) : MemLp (periodize (mStarF u)) ⊤ circleMeasure := by
  simpa only [mStarF] using memLp_periodize_etaCut (-(2 * (u : ℤ)))

lemma kmt_MemLp_periodize_mStargF (d u : ℕ) :
    MemLp (periodize (mStargF d u)) ⊤ circleMeasure := by
  simpa only [mStargF] using memLp_periodize_etaCut (-((d : ℤ) * 2 * (u : ℤ)))

lemma kmt_MemLp_periodize_varphiNt (N k : ℕ) (t : ℝ) :
    MemLp (periodize (varphiNt N k t)) ⊤ circleMeasure := by
  refine memLp_periodize (contDiff_varphiNt N k t).continuous.measurable
    (R := (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) (C := 2)
    (Real.rpow_nonneg (by norm_num) _) ?_ ?_
  · intro x hx
    by_contra hne
    exact absurd (varphiNt_support N k t x hne) (not_le.mpr hx)
  · intro x
    rw [varphiNt, norm_mul, norm_ee, mul_one]
    exact norm_varphiN_le_two N k x

lemma kmt_MemLp_periodize_varphitildeNt (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    MemLp (periodize (varphitildeNt P d N k t)) ⊤ circleMeasure := by
  obtain ⟨R, hR⟩ :=
    exists_abs_le_of_hasCompactSupport (hasCompactSupport_varphitildeNt_aux P d N k t)
  refine memLp_periodize (contDiff_varphitildeNt_aux P d N k t).continuous.measurable
    (R := max R 0) (C := 2) (le_max_right _ _) ?_ ?_
  · intro x hx
    exact hR x (le_of_lt (lt_of_le_of_lt (le_max_left R 0) hx))
  · intro x
    rw [varphitildeNt, norm_mul, norm_ee, mul_one]
    exact kmt_norm_varphitildeN_le_two d N k x

lemma kmt_integrable_mStarF (u : ℕ) : Integrable (mStarF u) := by
  simpa only [mStarF] using
    (contDiff_etaCut (-(2 * (u : ℤ)))).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_etaCut (-(2 * (u : ℤ))))

lemma kmt_integrable_mStargF (d u : ℕ) : Integrable (mStargF d u) := by
  have h : mStargF d u = mStarF (d * u) := by
    unfold mStargF mStarF
    congr 1
    push_cast
    ring
  rw [h]
  exact kmt_integrable_mStarF (d * u)

lemma kmt_summable_tmKernel_varphiNt (ρ : ℝ) (l N k : ℕ) (t : ℝ) :
    Summable (fun j : ℤ => ‖tmKernel ρ l (varphiNt N k t) j‖) := by
  refine summable_tmKernel_of_bump ρ l (contDiff_varphiNt N k t) (hasCompactSupport_varphiNt N k t)
    (S := max (∫ y, ‖varphiNt N k t y‖) (∫ y, ‖iteratedDeriv 2 (varphiNt N k t) y‖)) ?_ ?_ ?_
  · exact le_max_of_le_left (integral_nonneg fun y => norm_nonneg _)
  · exact le_max_left _ _
  · exact le_max_right _ _

lemma kmt_summable_tmKernel_varphitildeNt (ρ : ℝ) (P : Polynomial ℤ) (l N k : ℕ) (t : ℝ) :
    Summable (fun j : ℤ => ‖tmKernel ρ l (varphitildeNt P P.natDegree N k t) j‖) := by
  refine summable_tmKernel_of_bump ρ l (contDiff_varphitildeNt_aux P P.natDegree N k t)
    (hasCompactSupport_varphitildeNt_aux P P.natDegree N k t)
    (S := max (∫ y, ‖varphitildeNt P P.natDegree N k t y‖)
      (∫ y, ‖iteratedDeriv 2 (varphitildeNt P P.natDegree N k t) y‖)) ?_ ?_ ?_
  · exact le_max_of_le_left (integral_nonneg fun y => norm_nonneg _)
  · exact le_max_left _ _
  · exact le_max_right _ _

lemma kmt_fourierCoeff_varphiNt_mul_mStarF (ρ : ℝ) (l N k : ℕ) (t : ℝ) (u : ℕ)
    (α : Circ) (a : ℤ) :
    fourierCoeff (fun θ : Circ => iwSymbolSet (diffFreqs ρ l) (periodize (varphiNt N k t)) θ
        * periodize (mStarF u) (θ - α)) a
      = ∑' j : ℤ, tmKernel ρ l (varphiNt N k t) (a - j) * fourier (T := 1) (-j) α
          * cw (mStarF u) j := by
  have h := kmt_fourierCoeff_mul_periodize_sub
    (Ψ := iwSymbolSet (diffFreqs ρ l) (periodize (varphiNt N k t))) (m := mStarF u)
    ((Work.Analysis.IWMultiplier.memLp_iwSymbolSet _ (kmt_MemLp_periodize_varphiNt N k t)).mono_exponent
      (by norm_num : (2 : ℝ≥0∞) ≤ ⊤))
    ((kmt_MemLp_periodize_mStarF u).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ⊤))
    (by simpa only [tmKernel, Work.Analysis.IWMultiplier.iwKernel] using
      kmt_summable_tmKernel_varphiNt ρ l N k t)
    (kmt_integrable_mStarF u) α a
  simpa only [tmKernel, Work.Analysis.IWMultiplier.iwKernel] using h

lemma kmt_fourierCoeff_varphitildeNt_mul_mStargF (ρ : ℝ) (P : Polynomial ℤ) (l N k : ℕ)
    (t : ℝ) (u : ℕ) (α : Circ) (b : ℤ) :
    fourierCoeff (fun θ : Circ =>
        iwSymbolSet (diffFreqs ρ l) (periodize (varphitildeNt P P.natDegree N k t)) θ
        * periodize (mStargF P.natDegree u) (θ - α)) b
      = ∑' j : ℤ, tmKernel ρ l (varphitildeNt P P.natDegree N k t) (b - j)
          * fourier (T := 1) (-j) α * cw (mStargF P.natDegree u) j := by
  have h := kmt_fourierCoeff_mul_periodize_sub
    (Ψ := iwSymbolSet (diffFreqs ρ l) (periodize (varphitildeNt P P.natDegree N k t)))
    (m := mStargF P.natDegree u)
    ((Work.Analysis.IWMultiplier.memLp_iwSymbolSet _ (kmt_MemLp_periodize_varphitildeNt P P.natDegree N k t)).mono_exponent
      (by norm_num : (2 : ℝ≥0∞) ≤ ⊤))
    ((kmt_MemLp_periodize_mStargF P.natDegree u).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ⊤))
    (by simpa only [tmKernel, Work.Analysis.IWMultiplier.iwKernel] using
      kmt_summable_tmKernel_varphitildeNt ρ P l N k t)
    (kmt_integrable_mStargF P.natDegree u) α b
  simpa only [tmKernel, Work.Analysis.IWMultiplier.iwKernel] using h

lemma kmt_summable_shift_mul {f g : ℤ → ℝ} (hf : Summable f) (hg : Summable g)
    (hf0 : 0 ≤ f) (hg0 : 0 ≤ g) (a : ℤ) : Summable (fun j : ℤ => f (a - j) * g j) := by
  have h := (hf.mul_of_nonneg hg hf0 hg0).comp_injective (i := fun j : ℤ => (a - j, j))
    (fun x y hxy => congrArg Prod.snd hxy)
  exact h

lemma kmt_finset_mul_tsum_tsum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (X Y : ι → ℤ → ℂ)
    (hX : ∀ p ∈ s, Summable (fun j : ℤ => X p j)) (hY : ∀ p ∈ s, Summable (fun j : ℤ => Y p j)) :
    ∑ p ∈ s, c p * (∑' j : ℤ, X p j) * (∑' j : ℤ, Y p j)
      = ∑' j₁ : ℤ, ∑' j₂ : ℤ, ∑ p ∈ s, c p * X p j₁ * Y p j₂ := by
  have h1 : ∀ j₁ : ℤ, (∑' j₂ : ℤ, ∑ p ∈ s, c p * X p j₁ * Y p j₂)
      = ∑ p ∈ s, c p * X p j₁ * (∑' j₂ : ℤ, Y p j₂) := by
    intro j₁
    rw [Summable.tsum_finsetSum (f := fun p (j₂ : ℤ) => c p * X p j₁ * Y p j₂)
      (fun p hp => (hY p hp).mul_left (c p * X p j₁))]
    exact Finset.sum_congr rfl (fun p hp => by rw [tsum_mul_left])
  have h2 : (∑' j₁ : ℤ, ∑ p ∈ s, c p * X p j₁ * (∑' j₂ : ℤ, Y p j₂))
      = ∑ p ∈ s, c p * (∑' j₁ : ℤ, X p j₁) * (∑' j₂ : ℤ, Y p j₂) := by
    rw [Summable.tsum_finsetSum (f := fun p (j₁ : ℤ) => c p * X p j₁ * (∑' j₂ : ℤ, Y p j₂))
      (fun p hp => ((hX p hp).mul_left (c p)).mul_right (∑' j₂ : ℤ, Y p j₂))]
    exact Finset.sum_congr rfl (fun p hp => by rw [tsum_mul_right, tsum_mul_left])
  rw [tsum_congr h1, h2]

end

end Work.KMTAreas.A7
