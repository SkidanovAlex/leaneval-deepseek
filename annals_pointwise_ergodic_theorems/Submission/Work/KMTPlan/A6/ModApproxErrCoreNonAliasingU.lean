import Mathlib
import Submission.Work.KMTPlan.A6.ModApproxErrCoreExact
import Submission.Work.KMTPlan.A6.UModApprox.mdlPart_eq_bilinOp_symM
import Submission.Work.KMTPlan.A6.UModApprox.symD_mass_bound
import Submission.Work.KMTPlan.A6.UModApprox.mainPartTuple_eq_bilinOp_symC
import Submission.Work.KMTPlan.A6.UModApprox.arc_support

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7
open Work.Analysis.EndVar

/-- `1 ≤ a n` implies `1 ≤ ⌊a n⌋`. -/
private lemma one_le_floor_of_one_le {a : ℕ → NNReal} {n : ℕ} (h : 1 ≤ a n) :
    1 ≤ Nat.floor (a n) := by
  have h1 : (1 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast h
  exact Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr h1).ne'

theorem ModApproxErrCoreNonAliasingU (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ A : ℝ, 0 ≤ A ∧ ∃ C : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        (k₁ = 0 ∨ k₂ = 0) →
        MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp g 2 MeasureTheory.Measure.count → ∀ n : ℕ,
        Work.Analysis.IonescuWainger.NonAliasing
          (-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁
            ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) →
        max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) + 1
            ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat →
        MeasureTheory.eLpNorm (fun x : ℤ =>
            Work.KMTPlan.A6.modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          1 MeasureTheory.Measure.count
          ≤ (C Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂)
              * ENNReal.ofReal (((Nat.floor (a n) : ℕ) : ℝ)⁻¹)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨ρs, hρs, hρs1, Hmass⟩ := Work.KMTPlan.A6.UModApprox.symD_mass_bound P hd
  refine ⟨min ρs 1, lt_min hρs one_pos, ?_⟩
  intro ρ hρ hρle
  have hρs' : ρ ≤ ρs := le_trans hρle (min_le_left _ _)
  have hρ1 : ρ ≤ 1 := le_trans hρle (min_le_right _ _)
  obtain ⟨A, hA, C, hC1, Hmass'⟩ := Hmass ρ hρ hρs'
  set Ck : NNReal := ⟨C, le_trans (by norm_num) hC1⟩ with hCk
  refine ⟨A, hA, fun _ => Ck, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hk hf hg n hnA hplat
  have hN1 : 1 ≤ Nat.floor (a n) := one_le_floor_of_one_le (ha1 n)
  have hfbd : Work.KMTAreas.A5.BoundedZ f :=
    Work.KMTAreas.A5.boundedZ_of_memLp (by norm_num : (1 : ℝ≥0∞) < 2) hf
  have hgbd : Work.KMTAreas.A5.BoundedZ g :=
    Work.KMTAreas.A5.boundedZ_of_memLp (by norm_num : (1 : ℝ≥0∞) < 2) hg
  by_cases hcore : Work.KMTAreas.A7.loGuard ρ C₀ a l₁ l₂ k₁ k₂ n
  · -- **the good case**: on the core the error is the bilinear convolution with `coeff2 symD`
    have hnA₁ : Work.Analysis.IonescuWainger.NonAliasing
        (-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁) :=
      Work.KMTAreas.A7.NonAliasing_of_subset hnA Finset.subset_union_left
    have hnA₂ : Work.Analysis.IonescuWainger.NonAliasing
        (-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) :=
      Work.KMTAreas.A7.NonAliasing_of_subset hnA Finset.subset_union_right
    have hmono : (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
        ≤ (-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) := by
      have h0 : (0 : ℤ) ≤ (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ) :=
        Int.natCast_nonneg _
      linarith
    have hnAc₁ : Work.Analysis.IonescuWainger.NonAliasing
        (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁) :=
      Work.KMTPlan.A6.NonAliasing.mono hmono (Finset.Subset.refl _) hnA₁
    have hnAc₂ : Work.Analysis.IonescuWainger.NonAliasing
        (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) :=
      Work.KMTPlan.A6.NonAliasing.mono hmono (Finset.Subset.refl _) hnA₂
    have hna2u : Work.Analysis.IonescuWainger.NonAliasing
        (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁
          ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) :=
      Work.KMTPlan.A6.NonAliasing.mono hmono (Finset.Subset.refl _) hnA
    have hΦ₁ := Work.KMTPlan.A6.UModApprox.varphiNt_supportedInArc ρ (Nat.floor (a n))
      l₁ l₂ k₁ k₂ hplat
    have hΦ₂ := Work.KMTPlan.A6.UModApprox.varphitildeNt_supportedInArc ρ P hd
      (Nat.floor (a n)) l₁ l₂ k₁ k₂ hplat
    have hs₁ := Work.KMTPlan.A6.UModApprox.varphiNt_realArc_support ρ (Nat.floor (a n))
      l₁ l₂ k₁ k₂ hplat
    have hs₂ := Work.KMTPlan.A6.UModApprox.varphitildeNt_realArc_support ρ P hd
      (Nat.floor (a n)) l₁ l₂ k₁ k₂ hplat
    have hsumCM := Work.KMTPlan.A6.symC_symM_summable ρ hρ hρ1 P (Nat.floor (a n)) l₁ l₂ k₁ k₂
    have hpt : (fun x : ℤ => Work.KMTPlan.A6.modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        = fun x : ℤ => Work.KMTAreas.A7.bilinOp (fun u v => Work.KMTPlan.A6.coeff2
            (Work.KMTPlan.A6.symD ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂) u v) f g x := by
      funext x
      rw [Work.KMTPlan.A6.modApproxErr]
      rw [Work.KMTPlan.A6.UModApprox.mainPartTuple_eq_bilinOp_symC ρ hρ hρ1 P C₀ a f g
          l₁ l₂ k₁ k₂ n x hf hg hcore,
        Work.KMTPlan.A6.UModApprox.mdlPart_eq_bilinOp_symM ρ hρ hρ1 P hd C₀ a f g
          l₁ l₂ k₁ k₂ n x hf hg hN1 hcore hnA₁ hnA₂ hΦ₁ hΦ₂ hnAc₁ hnAc₂ hs₁ hs₂,
        Work.KMTPlan.A6.bilinOp_sub_kernel hsumCM.1 hsumCM.2 hfbd.choose_spec
          hgbd.choose_spec]
      congr 1
      funext u v
      exact Work.KMTPlan.A6.coeff2_symC_sub_symM_eq_coeff2_symD P (le_trans (by norm_num) hd)
        ρ hρ hρ1 (Nat.floor (a n)) l₁ l₂ k₁ k₂ hN1 hplat hna2u u v
    rw [hpt]
    obtain ⟨hsumD, hmassD⟩ := Hmass' (Nat.floor (a n)) l₁ l₂ k₁ k₂ hN1 hplat
    have hLP := Work.KMTAreas.A7.BilinOpLp
      (K := fun u v => Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symD ρ P (Nat.floor (a n))
        l₁ l₂ k₁ k₂) u v) (p := 1) (p₁ := 2) (p₂ := 2)
      (by rw [ENNReal.inv_two_add_inv_two, inv_one]) le_rfl hsumD f g
    refine hLP.trans ?_
    have hCnn : (0 : ℝ) ≤ C := le_trans (by norm_num) hC1
    have hWnn : 0 ≤ Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂ :=
      Work.KMTAreas.A7.modelWeight_nonneg A ρ hA l₁ l₂ k₁ k₂
    have hineq : ENNReal.ofReal (∑' q : ℤ × ℤ,
          ‖Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symD ρ P (Nat.floor (a n))
            l₁ l₂ k₁ k₂) q.1 q.2‖)
        ≤ (Ck : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂)
          * ENNReal.ofReal (((Nat.floor (a n) : ℕ) : ℝ)⁻¹) := by
      have h1 : ENNReal.ofReal (∑' q : ℤ × ℤ,
            ‖Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symD ρ P (Nat.floor (a n))
              l₁ l₂ k₁ k₂) q.1 q.2‖)
          ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂
              * ((Nat.floor (a n) : ℕ) : ℝ)⁻¹) :=
        ENNReal.ofReal_le_ofReal hmassD
      have hcoe : (Ck : ENNReal) = ENNReal.ofReal C := ENNReal.coe_nnreal_eq Ck
      refine h1.trans (le_of_eq ?_)
      rw [hcoe]
      rw [← ENNReal.ofReal_mul hCnn, ← ENNReal.ofReal_mul (mul_nonneg hCnn hWnn)]
    exact mul_le_mul' (mul_le_mul' hineq le_rfl) le_rfl
  · -- off the core both tuples vanish
    have h0 : (fun x : ℤ => Work.KMTPlan.A6.modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 :=
      Work.KMTPlan.A6.modApproxErr_eq_zero_of_not_core ρ P C₀ a f g l₁ l₂ k₁ k₂ n hcore
    rw [h0, MeasureTheory.eLpNorm_zero]
    exact bot_le

end Work.KMTPlan.A6
