import Mathlib
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea7.sum_abs_inv_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `‖(z/|z|)^k‖ ≤ 1`: the elementary size bound for the Grossencharacter factor (16.14). -/
lemma S16_psiK_le_one (k : ℤ) (z : GaussianInt) : ‖Work.FIArea6.psiK k z‖ ≤ 1 := by
  have h := Work.FIArea5.S16Hecke.norm_div_sqrt_zpow_le_one z k
  simpa only [Work.FIArea6.psiK] using h

/-- The indicator `unitInd` has modulus at most `1`. -/
lemma S16_unitInd_le_one (Q : ℕ) (z : GaussianInt) : ‖Work.FIArea7.unitInd Q z‖ ≤ 1 := by
  rw [Work.FIArea7.unitInd]
  split_ifs <;> simp

/-- `|jacobiSym a b| ≤ 1`. -/
lemma S16_abs_jacobiSym_le_one (a : ℤ) (b : ℕ) : |jacobiSym a b| ≤ 1 := by
  rcases jacobiSym.trichotomy a b with h | h | h <;> simp [h]

/-- The `ω`-detection sum is bounded by the number of classes: `‖omegaDet d‖ ≤ 4d`. -/
lemma S16_omegaDet_le (d : ℕ) (z1 z2 : GaussianInt) :
    ‖Work.FIArea6.omegaDet d z1 z2‖ ≤ 4 * (d : ℝ) := by
  rw [Work.FIArea6.omegaDet]
  unfold Work.FIArea7.omegaDetect
  split_ifs with hQ
  · simp
  · haveI : NeZero (4 * d) := ⟨hQ⟩
    have h1 : ∀ ω : ZMod (4 * d),
        ‖(if ((z1.re : ZMod (4 * d)) = ω * (z2.re : ZMod (4 * d))) ∧
            ((z1.im : ZMod (4 * d)) = ω * (z2.im : ZMod (4 * d)))
          then ((jacobiSym (ω.val : ℤ) d : ℤ) : ℂ) else 0)‖ ≤ 1 := by
      intro ω
      split_ifs with hc
      · rw [Complex.norm_intCast]
        exact_mod_cast S16_abs_jacobiSym_le_one ((ω.val : ℤ)) d
      · simp
    refine le_trans (norm_sum_le _ _) ?_
    calc (∑ ω : ZMod (4 * d),
            ‖(if ((z1.re : ZMod (4 * d)) = ω * (z2.re : ZMod (4 * d))) ∧
                ((z1.im : ZMod (4 * d)) = ω * (z2.im : ZMod (4 * d)))
              then ((jacobiSym (ω.val : ℤ) d : ℤ) : ℂ) else 0)‖)
        ≤ ∑ _ω : ZMod (4 * d), (1 : ℝ) := Finset.sum_le_sum (fun ω _ => h1 ω)
      _ = ((4 * d : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
      _ = 4 * (d : ℝ) := by push_cast; ring

/-- **The trivial bound for the `ω`-detected pair sum**: `‖DetSum‖ ≤ 4d·(Σ_z ‖β z‖)²`. -/
theorem norm_DetSum_le (Pa : Work.FITop.Params) (d : ℕ) (k : ℤ) (β : GaussianInt → ℂ) :
    ‖Work.FIArea6.DetSum Pa d k β‖
      ≤ 4 * (d : ℝ) * (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖) ^ 2 := by
  rw [Work.FIArea6.DetSum]
  have hterm : ∀ z1 ∈ Work.FITop.boxN Pa, ∀ z2 ∈ Work.FITop.boxN Pa,
      ‖Work.FIArea7.unitInd (4 * d) z1 * Work.FIArea7.unitInd (4 * d) z2
        * ((β z1 * Work.FIArea6.psiK k z1) * star (β z2 * Work.FIArea6.psiK k z2))
        * Work.FIArea6.omegaDet d z1 z2‖
      ≤ ‖β z1‖ * (‖β z2‖ * (4 * (d : ℝ))) := by
    intro z1 _ z2 _
    simp only [norm_mul, norm_star]
    have h1 := S16_unitInd_le_one (4 * d) z1
    have h2 := S16_unitInd_le_one (4 * d) z2
    have h3 := S16_psiK_le_one k z1
    have h4 := S16_psiK_le_one k z2
    have h5 := S16_omegaDet_le d z1 z2
    calc ‖Work.FIArea7.unitInd (4 * d) z1‖ * ‖Work.FIArea7.unitInd (4 * d) z2‖
          * (‖β z1‖ * ‖Work.FIArea6.psiK k z1‖ * (‖β z2‖ * ‖Work.FIArea6.psiK k z2‖))
          * ‖Work.FIArea6.omegaDet d z1 z2‖
        ≤ 1 * 1 * (‖β z1‖ * 1 * (‖β z2‖ * 1)) * (4 * (d : ℝ)) := by
          gcongr
      _ = ‖β z1‖ * (‖β z2‖ * (4 * (d : ℝ))) := by ring
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun z1 _ => norm_sum_le _ _)) ?_
  refine le_trans (Finset.sum_le_sum (fun z1 hz1 => Finset.sum_le_sum (fun z2 hz2 => hterm z1 hz1 z2 hz2))) ?_
  have e1 : ∀ i ∈ Work.FITop.boxN Pa,
      (∑ j ∈ Work.FITop.boxN Pa, ‖β i‖ * (‖β j‖ * (4 * (d : ℝ))))
        = ‖β i‖ * ((∑ j ∈ Work.FITop.boxN Pa, ‖β j‖) * (4 * (d : ℝ))) := by
    intro i _
    rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hcollapse : (∑ i ∈ Work.FITop.boxN Pa, ∑ j ∈ Work.FITop.boxN Pa,
        ‖β i‖ * (‖β j‖ * (4 * (d : ℝ))))
      = 4 * (d : ℝ) * (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖) ^ 2 := by
    rw [Finset.sum_congr rfl e1, ← Finset.sum_mul]
    ring
  rw [hcollapse]

/-- `|c_k| ≤ 1/|k|` for the Fourier coefficients of the log-sine expansion. -/
lemma S16_fcoeff_abs_le (k : ℤ) (hk : k ≠ 0) :
    |Work.FIArea6.fcoeff k| ≤ 1 / |(k : ℝ)| := by
  rw [Work.FIArea6.fcoeff]
  simp only [if_neg hk]
  split_ifs with h2
  · rw [abs_of_nonneg (by positivity)]
  · rw [abs_zero]
    positivity

/-- **The frequency weight** `Σ_{|k| ≤ M} |c_k| ≤ log 16 + 2(1 + log M)`. -/
theorem fcoeff_sum_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |Work.FIArea6.fcoeff k|
      ≤ Real.log 16 + 2 * (1 + Real.log (M : ℝ)) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc (-(M : ℤ)) (M : ℤ))
    (fun k : ℤ => k = 0) (fun k => |Work.FIArea6.fcoeff k|)]
  have hA : ∑ k ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun k : ℤ => k = 0),
      |Work.FIArea6.fcoeff k| ≤ Real.log 16 := by
    have hsub : (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun k : ℤ => k = 0)
        ⊆ ({0} : Finset ℤ) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_singleton] at hk ⊢
      exact hk.2
    calc ∑ k ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun k : ℤ => k = 0),
            |Work.FIArea6.fcoeff k|
        ≤ ∑ k ∈ ({0} : Finset ℤ), |Work.FIArea6.fcoeff k| :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
      _ = Real.log 16 := by
          simp only [Finset.sum_singleton, Work.FIArea6.fcoeff, if_true]
          exact abs_of_nonneg (Real.log_nonneg (by norm_num))
  have hB : ∑ k ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun k : ℤ => ¬ k = 0),
      |Work.FIArea6.fcoeff k| ≤ 2 * (1 + Real.log (M : ℝ)) := by
    have hstep : ∑ k ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun k : ℤ => ¬ k = 0),
          |Work.FIArea6.fcoeff k|
        ≤ ∑ k ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun k : ℤ => ¬ k = 0),
            1 / |(k : ℝ)| := by
      apply Finset.sum_le_sum
      intro k hk
      have hk0 : k ≠ 0 := by
        have := (Finset.mem_filter.mp hk).2
        simpa using this
      exact S16_fcoeff_abs_le k hk0
    refine le_trans hstep (Work.FIArea7.sum_abs_inv_le M _ ?_)
    intro k hk
    obtain ⟨hkS, hk0⟩ := Finset.mem_filter.mp hk
    obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hkS
    refine ⟨by simpa using hk0, ?_⟩
    rw [abs_le]
    exact ⟨by exact_mod_cast hl, by exact_mod_cast hr⟩
  linarith

/-- `Σ_{d ≤ X} φ(d) ≤ X²`. -/
theorem totient_sum_le (X : ℕ) (hX : 1 ≤ X) :
    ∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) ≤ (X : ℝ) ^ (2 : ℕ) := by
  have h1 : ∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) ≤ ∑ d ∈ Finset.Icc 1 X, (d : ℝ) :=
    Finset.sum_le_sum (fun d _ => by exact_mod_cast Nat.totient_le d)
  have h2 : ∑ d ∈ Finset.Icc 1 X, (d : ℝ) ≤ (X : ℝ) ^ (2 : ℕ) := by
    have h3 : ∑ d ∈ Finset.Icc 1 X, (d : ℝ) ≤ ∑ _d ∈ Finset.Icc 1 X, (X : ℝ) :=
      Finset.sum_le_sum (fun d hd => by
        have := (Finset.mem_Icc.mp hd).2
        exact_mod_cast this)
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at h3
    have h4 : ((X + 1 - 1 : ℕ) : ℝ) = (X : ℝ) := by
      rw [show X + 1 - 1 = X by omega]
    rw [h4] at h3
    calc ∑ d ∈ Finset.Icc 1 X, (d : ℝ) ≤ (X : ℝ) * (X : ℝ) := h3
      _ = (X : ℝ) ^ (2 : ℕ) := by ring
  linarith

end

end Work.FIArea6
