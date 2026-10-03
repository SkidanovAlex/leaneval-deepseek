import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicDefs
import Submission.Port.Aesm

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Helper lemmas of `MdlSliceCoreGainAll.lean`, in their own module so that the sibling lane
(`A6Clean/…`) can import them without importing the target file (which would create an import
cycle with its consumers).  The statements are unchanged. -/

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7
open Work.Analysis.EndVar

lemma lmaxR_nonneg (l₁ l₂ k₁ k₂ : ℕ) : 0 ≤ lmaxR l₁ l₂ k₁ k₂ := by
  rw [lmaxR]
  have : (0 : ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
    rw [Work.Analysis.EndVar.lmax]
    exact le_trans (Int.natCast_nonneg l₁)
      (le_trans (le_max_left _ _) (le_max_left _ _))
  exact_mod_cast this

lemma eLpNorm_one_count_eq_tsum_vr (g : ℤ → ENNReal) :
    eLpNorm g 1 (Measure.count : Measure ℤ) = ∑' x : ℤ, g x := by
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), MeasureTheory.lintegral_count]
  exact tsum_congr fun x => enorm_eq_self _

lemma eLpNorm_one_count_variationalNorm (r : ℝ≥0) (c : ℕ → ℤ → ℂ) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => c n x)) 1 (Measure.count : Measure ℤ)
      = ∑' x : ℤ, variationalNorm r (fun n : ℕ => c n x) :=
  eLpNorm_one_count_eq_tsum_vr _

lemma variationalNorm_zero_vr (r : ℝ≥0) (hr : 1 ≤ r) :
    variationalNorm r (0 : ℕ → ℂ) = 0 := by
  have hs := variationalNorm_smul (r := r) hr (0 : ℂ) (0 : ℕ → ℂ)
  rwa [zero_smul, enorm_zero, zero_mul] at hs

lemma eLpNorm_variationalNorm_zero_local (r : ℝ≥0) (hr : 1 ≤ r) :
    eLpNorm (fun _ : ℤ => variationalNorm r (fun _ : ℕ => (0 : ℂ))) 1
      (Measure.count : Measure ℤ) = 0 := by
  rw [show (fun _ : ℤ => variationalNorm r (fun _ : ℕ => (0 : ℂ)))
      = (fun _ : ℤ => (0 : ENNReal)) from by
    funext x
    exact variationalNorm_zero_vr r hr]
  simp

lemma zmodAvg_add₁ (P : ℤ[X]) (Q : ℕ) (u u' v : ZMod Q → ℂ) :
    zmodAvg P Q (u + u') v = zmodAvg P Q u v + zmodAvg P Q u' v := by
  funext θ
  simp only [zmodAvg, Pi.add_apply]
  rw [show (∑ y ∈ Finset.range Q,
        (u (θ + (y : ZMod Q)) + u' (θ + (y : ZMod Q)))
          * v (θ + ((P.eval (y : ℤ) : ℤ) : ZMod Q)))
      = ∑ y ∈ Finset.range Q,
        (u (θ + (y : ZMod Q)) * v (θ + ((P.eval (y : ℤ) : ℤ) : ZMod Q))
          + u' (θ + (y : ZMod Q)) * v (θ + ((P.eval (y : ℤ) : ℤ) : ZMod Q))) from
    Finset.sum_congr rfl fun y _ => by ring]
  rw [Finset.sum_add_distrib]
  ring

lemma zmodAvg_add₂ (P : ℤ[X]) (Q : ℕ) (u v v' : ZMod Q → ℂ) :
    zmodAvg P Q u (v + v') = zmodAvg P Q u v + zmodAvg P Q u v' := by
  funext θ
  simp only [zmodAvg, Pi.add_apply]
  rw [show (∑ y ∈ Finset.range Q,
        u (θ + (y : ZMod Q))
          * (v (θ + ((P.eval (y : ℤ) : ℤ) : ZMod Q))
            + v' (θ + ((P.eval (y : ℤ) : ℤ) : ZMod Q))))
      = ∑ y ∈ Finset.range Q,
        (u (θ + (y : ZMod Q)) * v (θ + ((P.eval (y : ℤ) : ℤ) : ZMod Q))
          + u (θ + (y : ZMod Q)) * v' (θ + ((P.eval (y : ℤ) : ℤ) : ZMod Q))) from
    Finset.sum_congr rfl fun y _ => by ring]
  rw [Finset.sum_add_distrib]
  ring

lemma one_le_lossWeight_vr (A ρ : ℝ) (hA : 0 ≤ A) (hρ : 0 ≤ ρ)
    (l₁ l₂ k₁ k₂ : ℕ) : 1 ≤ lossWeight A ρ l₁ l₂ k₁ k₂ := by
  have hL : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := lmaxR_nonneg l₁ l₂ k₁ k₂
  rw [lossWeight]
  have h1 : (1 : ℝ) ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ A := Real.one_le_rpow (by linarith) hA
  have h2 : (0 : ℝ) ≤ A * ρ * lmaxR l₁ l₂ k₁ k₂ := by positivity
  have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (A * ρ * lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) h2
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ A * (2 : ℝ) ^ (A * ρ * lmaxR l₁ l₂ k₁ k₂) :=
        mul_le_mul h1 h3 (by norm_num) (by positivity)

lemma lossWeight_pos_vr (A ρ : ℝ) (hA : 0 ≤ A) (hρ : 0 ≤ ρ)
    (l₁ l₂ k₁ k₂ : ℕ) : 0 < lossWeight A ρ l₁ l₂ k₁ k₂ :=
  lt_of_lt_of_le zero_lt_one (one_le_lossWeight_vr A ρ hA hρ l₁ l₂ k₁ k₂)

lemma mdlCore_zero_of_eq_zero (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (n : ℕ) :
    (mdlCore ρ C₀ a 0 0 0 0 n)
      ↔ (Work.KMTAreas.A7.splitCut ρ 0 < Nat.floor (a n)
          ∧ Work.KMTAreas.A7.mainRegime ρ 0 0 (Nat.floor (a n))) := by
  rw [mdlCore_iff, lcL]
  constructor
  · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, h2⟩
    simp only [Work.Analysis.EndVar.inIndexSet]
    exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _, Int.natCast_nonneg _⟩

lemma not_inIndexSet_zero_of_ne (l₁ l₂ k₁ k₂ : ℕ)
    (h : ¬(l₁ = 0 ∧ l₂ = 0 ∧ k₁ = 0 ∧ k₂ = 0)) (N : ℕ) :
    ¬ Work.Analysis.EndVar.inIndexSet 0 (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) N := by
  intro hii
  have hmax : max (l₁ : ℤ) (l₂ : ℤ) ≤ 0 := by
    have h' := hii.1
    simp only [Work.Analysis.EndVar.inIndexSet, Work.Analysis.EndVar.heightScale,
      zero_mul] at h'
    simpa using h'
  have hk₁ : (k₁ : ℤ) ≤ 0 := by
    have h' := hii.2.1
    simp only [Work.Analysis.EndVar.inIndexSet, Work.Analysis.EndVar.heightScale,
      zero_mul] at h'
    simpa using h'
  have hk₂ : (k₂ : ℤ) ≤ 0 := by
    have h' := hii.2.2
    simp only [Work.Analysis.EndVar.inIndexSet, Work.Analysis.EndVar.heightScale,
      zero_mul] at h'
    simpa using h'
  by_cases hl₁ : l₁ = 0
  · by_cases hl₂ : l₂ = 0
    · by_cases hk₁' : k₁ = 0
      · by_cases hk₂' : k₂ = 0
        · exact h ⟨hl₁, hl₂, hk₁', hk₂'⟩
        · omega
      · omega
    · omega
  · omega

end

end Work.KMTPlan.A6
