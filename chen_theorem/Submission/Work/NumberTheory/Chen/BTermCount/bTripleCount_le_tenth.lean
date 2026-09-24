import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_powLog
import Submission.Work.NumberTheory.Chen.BTermCount.Basic
import Submission.Work.NumberTheory.Chen.BTermCount.pi_upper_sharp
import Submission.Work.NumberTheory.Chen.BTermCount.prime_sum_le_integral
import Submission.Work.NumberTheory.Chen.BTermCount.cbar_integral_le
import Submission.Work.NumberTheory.Chen.BTermCount.bTripleCount_le_sum_pi_div
import Submission.Work.NumberTheory.Chen.BTermCount.sum_primes_inv_le_loglog
import Submission.Work.NumberTheory.Chen.BTermCount.integral_log_div_log
import Submission.Work.NumberTheory.Chen.BTermCount.innerIntegral_bound
import Submission.Work.NumberTheory.Chen.BTermCount.phi_antitone
import Submission.Work.NumberTheory.Chen.BTermCount.cbar_integral_le_relaxed
import Submission.Work.NumberTheory.Chen.BTermCount.hasDerivAt_abelF
import Submission.Work.NumberTheory.Chen.BTermCount.innerSum_le
import Submission.Work.NumberTheory.Chen.BTermCount.undershoot_le
import Submission.Work.NumberTheory.Chen.BTermCount.min_div_le_floor_cbrt
import Submission.Work.NumberTheory.Chen.BTermCount.undershoot_le_tenth
import Submission.Work.NumberTheory.Chen.BTermCount.cbar_integral_le_half_sharp

open Finset
open scoped BigOperators
open MeasureTheory intervalIntegral Filter

set_option maxHeartbeats 2000000

namespace Work.NumberTheory.Chen.BTermCount



-- The outer sum bound, in the `x^{1/10}` form: identical to `outerSum_le`
-- (`Submission.Work.NumberTheory.Chen.BTermCount.outerSum_le`) except that the
-- undershoot hypothesis is `1/10 - δ` instead of `1/14 - δ` and the integral bound
-- used is `cbar_integral_le_half_sharp` (`≤ 0.496 + 10δ`) instead of
-- `cbar_integral_le_relaxed` (`≤ 0.75 + 10δ`).  Hence the conclusion is `0.496 + 10δ + 2.8E`.
-- The proof is the same proof, with `hβ' : 1/10 - δ ≤ log(M-1)/log(x+2)`.

attribute [local instance] Classical.propDecidable

/-- Derivative of the BJS weight `φ(s) = log (2 − 3s)/(1 − s)` at a point where neither
denominator vanishes. -/
theorem hasDerivAt_phiWeight {s : ℝ} (h1 : 2 - 3*s ≠ 0) (h2 : 1 - s ≠ 0) :
    HasDerivAt (fun s : ℝ => Real.log (2 - 3*s)/(1 - s))
      ((((-3)/(2-3*s))*(1-s) - Real.log (2-3*s)*(-1))/(1-s)^2) s := by
  have hnum : HasDerivAt (fun s : ℝ => 2 - 3*s) (-3) s := by
    have h : HasDerivAt (fun s : ℝ => 2 - 3*s) (-(3*1)) s :=
      ((hasDerivAt_id s).const_mul (3:ℝ)).const_sub (2:ℝ)
    simpa using h
  have hden : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
    have h : HasDerivAt (fun s : ℝ => 1 - s) (-(1:ℝ)) s :=
      (hasDerivAt_id s).const_sub (1:ℝ)
    simpa using h
  exact (hnum.log h1).div hden h2

theorem outerSum_le_tenth (x M C : ℕ) (E L₀ δ : ℝ) (hx : 1 < x) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/700)
    (hE : 0 ≤ E)
    (hM : Real.exp 1 ≤ (M : ℝ) - 1) (hMC : M - 1 ≤ C)
    (hC : (C : ℝ) ≤ ((x : ℝ) + 2) ^ ((1:ℝ)/3))
    (hβ : (1:ℝ)/10 - δ ≤ Real.log ((M : ℝ) - 1) / Real.log ((x : ℝ) + 2))
    (hmer : ∀ t : ℝ, ((M : ℝ) - 1) ≤ t →
      |(∑ p ∈ (⌊t⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log t) - L₀| ≤ E) :
    (∑ q ∈ (Finset.Icc M C).filter Nat.Prime,
        Real.log (2 - 3 * (Real.log (q : ℝ) / Real.log ((x : ℝ) + 2))) /
          (1 - Real.log (q : ℝ) / Real.log ((x : ℝ) + 2)) / (q : ℝ))
      ≤ 0.496 + 10 * δ + 2.8 * E := by
  -- ## numeric preliminaries
  have hxR : (1:ℝ) < (x:ℝ) := by exact_mod_cast hx
  have hX1 : (1:ℝ) < (x:ℝ) + 2 := by linarith
  have hX0 : (0:ℝ) < (x:ℝ) + 2 := by linarith
  have hLpos : 0 < Real.log ((x:ℝ) + 2) := Real.log_pos hX1
  have hLne : Real.log ((x:ℝ) + 2) ≠ 0 := ne_of_gt hLpos
  have hM4 : 4 ≤ M := by
    have h3 : (3:ℝ) < (M:ℝ) := by linarith [Real.exp_one_gt_d9]
    have h3' : 3 < M := by exact_mod_cast h3
    omega
  have hAc : (((M - 1 : ℕ) : ℝ)) = (M:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ M)]
    norm_num
  have hA2 : 2 ≤ M - 1 := by omega
  have hA3 : (3:ℝ) ≤ (((M-1:ℕ):ℝ)) := by exact_mod_cast (by omega : 3 ≤ M - 1)
  have hCpos : (0:ℝ) < (C:ℝ) := by exact_mod_cast (by omega : 0 < C)
  have hab : (((M-1:ℕ):ℝ)) ≤ (C:ℝ) := by exact_mod_cast hMC
  have hβ' : (1:ℝ)/10 - δ ≤ Real.log (((M-1:ℕ):ℝ)) / Real.log ((x:ℝ)+2) := by
    rw [hAc]; exact hβ
  have hub : Real.log ((C:ℝ)) / Real.log ((x:ℝ)+2) ≤ 1/3 := by
    have h1 : Real.log (C:ℝ) ≤ Real.log (((x:ℝ)+2)^((1:ℝ)/3)) := Real.log_le_log hCpos hC
    rw [Real.log_rpow hX0] at h1
    rw [div_le_iff₀ hLpos]
    linarith
  have hαγ : Real.log (((M-1:ℕ):ℝ)) / Real.log ((x:ℝ)+2) ≤ Real.log ((C:ℝ)) / Real.log ((x:ℝ)+2) :=
    div_le_div_of_nonneg_right (Real.log_le_log (by linarith) hab) hLpos.le
  have hub_t : ∀ t : ℝ, (((M-1:ℕ):ℝ)) ≤ t → t ≤ (C:ℝ) → Real.log t / Real.log ((x:ℝ)+2) ≤ 1/3 := by
    intro t ht1 ht2
    have htpos : (0:ℝ) < t := by linarith
    have h1 : Real.log t ≤ Real.log (C:ℝ) := Real.log_le_log htpos ht2
    have h2 := div_le_div_of_nonneg_right h1 hLpos.le
    linarith [hub, h2]
  -- ## the two functions: `f = φ ∘ (log / L)` and its derivative `g`
  set F : ℝ → ℝ := fun s => Real.log (2 - 3*s)/(1 - s) with hF
  set f : ℝ → ℝ := fun t => F (Real.log t / Real.log ((x:ℝ)+2)) with hf
  set g : ℝ → ℝ := fun t => (((-3)/(2 - 3*(Real.log t / Real.log ((x:ℝ)+2))))*(1 - Real.log t / Real.log ((x:ℝ)+2)) - Real.log (2 - 3*(Real.log t / Real.log ((x:ℝ)+2)))*(-1))/(1 - Real.log t / Real.log ((x:ℝ)+2))^2 * (1/(t * Real.log ((x:ℝ)+2))) with hg
  have hmer' : ∀ t : ℝ, (((M-1:ℕ):ℝ)) ≤ t →
      |(∑ p ∈ (⌊t⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log t) - L₀| ≤ E := by
    intro t ht
    have ht' : (M:ℝ) - 1 ≤ t := by rw [← hAc]; exact ht
    exact hmer t ht'
  have hderiv : ∀ t ∈ Set.uIcc (((M-1:ℕ):ℝ)) ((C:ℝ)), HasDerivAt f (g t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have htpos : 0 < t := by linarith [ht.1, hA3]
    have hu3 : Real.log t / Real.log ((x:ℝ)+2) ≤ 1/3 := hub_t t ht.1 ht.2
    have hu1 : 2 - 3*(Real.log t / Real.log ((x:ℝ)+2)) ≠ 0 := by
      exact ne_of_gt (by linarith)
    have hu2 : 1 - Real.log t / Real.log ((x:ℝ)+2) ≠ 0 := by
      exact ne_of_gt (by linarith)
    have h1 : HasDerivAt (fun t : ℝ => Real.log t / Real.log ((x:ℝ)+2)) (1/(t * Real.log ((x:ℝ)+2))) t := by
      have h := (Real.hasDerivAt_log (ne_of_gt htpos)).div_const (Real.log ((x:ℝ)+2))
      refine h.congr_deriv ?_
      field_simp
    have h2 : HasDerivAt F ((((-3)/(2 - 3*(Real.log t / Real.log ((x:ℝ)+2))))*(1 - Real.log t / Real.log ((x:ℝ)+2)) - Real.log (2 - 3*(Real.log t / Real.log ((x:ℝ)+2)))*(-1))/(1 - Real.log t / Real.log ((x:ℝ)+2))^2) (Real.log t / Real.log ((x:ℝ)+2)) := by
      simpa only [hF] using hasDerivAt_phiWeight (s := Real.log t / Real.log ((x:ℝ)+2)) hu1 hu2
    have hcomp := h2.comp t h1
    simpa only [hf, hg, Function.comp_def] using hcomp
  have hfnn : ∀ t ∈ Set.Icc (((M-1:ℕ):ℝ)) ((C:ℝ)), 0 ≤ f t := by
    intro t ht
    have hu3 : Real.log t / Real.log ((x:ℝ)+2) ≤ 1/3 := hub_t t ht.1 ht.2
    simp only [hf, hF]
    exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  have hg_nonpos : ∀ t ∈ Set.Icc (((M-1:ℕ):ℝ)) ((C:ℝ)), g t ≤ 0 := by
    intro t ht
    have htpos : 0 < t := by linarith [ht.1, hA3]
    have ht1 : (1:ℝ) ≤ t := by linarith [ht.1, hA3]
    have hu3 : Real.log t / Real.log ((x:ℝ)+2) ≤ 1/3 := hub_t t ht.1 ht.2
    set u : ℝ := Real.log t / Real.log ((x:ℝ)+2) with hu
    have hu0 : 0 ≤ u := by rw [hu]; exact div_nonneg (Real.log_nonneg ht1) hLpos.le
    have hu30 : 0 < 2 - 3*u := by rw [hu]; linarith
    have hu10 : 0 < 1 - u := by rw [hu]; linarith
    have hkey : (2 - 3*u) * Real.log (2 - 3*u) - 3*(1-u) ≤ 0 := by
      have hlog_le : Real.log (2 - 3*u) ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos hu30
        linarith
      have := mul_le_mul_of_nonneg_left hlog_le hu30.le
      linarith
    have hnum : (((-3)/(2 - 3*u))*(1-u) - Real.log (2 - 3*u)*(-1)) ≤ 0 := by
      have heq : ((-3)/(2 - 3*u))*(1-u) - Real.log (2 - 3*u)*(-1)
          = ((2 - 3*u) * Real.log (2 - 3*u) - 3*(1-u))/(2 - 3*u) := by
        field_simp
        ring
      rw [heq]
      exact div_nonpos_of_nonpos_of_nonneg hkey hu30.le
    have hdiv : (((-3)/(2 - 3*u))*(1-u) - Real.log (2 - 3*u)*(-1))/(1-u)^2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
    simp only [hg]
    rw [← hu]
    exact mul_nonpos_of_nonpos_of_nonneg hdiv (div_nonneg zero_le_one (le_of_lt (mul_pos htpos hLpos)))
  have hfint : IntervalIntegrable g volume (((M-1:ℕ):ℝ)) ((C:ℝ)) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hg, Set.uIcc_of_le hab]
    have huc : ContinuousOn (fun t : ℝ => Real.log t / Real.log ((x:ℝ)+2))
        (Set.Icc (((M-1:ℕ):ℝ)) (C:ℝ)) := by
      refine ContinuousOn.div (ContinuousOn.log continuousOn_id ?_) continuousOn_const ?_
      · intro t ht
        have ht0 : (0:ℝ) < t := by linarith [ht.1, hA3]
        exact ne_of_gt ht0
      · intro t ht; exact hLne
    have h2u : ContinuousOn (fun t : ℝ => 2 - 3*(Real.log t / Real.log ((x:ℝ)+2)))
        (Set.Icc (((M-1:ℕ):ℝ)) (C:ℝ)) :=
      continuousOn_const.sub (huc.const_mul 3)
    have hne2 : ∀ t ∈ Set.Icc (((M-1:ℕ):ℝ)) (C:ℝ), 2 - 3*(Real.log t / Real.log ((x:ℝ)+2)) ≠ 0 := by
      intro t ht
      have h := hub_t t ht.1 ht.2
      exact ne_of_gt (by linarith)
    have hlogu : ContinuousOn (fun t : ℝ => Real.log (2 - 3*(Real.log t / Real.log ((x:ℝ)+2))))
        (Set.Icc (((M-1:ℕ):ℝ)) (C:ℝ)) := h2u.log hne2
    have h1u : ContinuousOn (fun t : ℝ => 1 - Real.log t / Real.log ((x:ℝ)+2))
        (Set.Icc (((M-1:ℕ):ℝ)) (C:ℝ)) := continuousOn_const.sub huc
    have hnumc : ContinuousOn (fun t : ℝ => ((-3)/(2 - 3*(Real.log t / Real.log ((x:ℝ)+2))))*(1 - Real.log t / Real.log ((x:ℝ)+2)) - Real.log (2 - 3*(Real.log t / Real.log ((x:ℝ)+2)))*(-1))
        (Set.Icc (((M-1:ℕ):ℝ)) (C:ℝ)) :=
      ((continuousOn_const.div h2u hne2).mul h1u).sub (hlogu.mul continuousOn_const)
    have hden : ContinuousOn (fun t : ℝ => (1 - Real.log t / Real.log ((x:ℝ)+2))^2)
        (Set.Icc (((M-1:ℕ):ℝ)) (C:ℝ)) := h1u.pow 2
    have hne1 : ∀ t ∈ Set.Icc (((M-1:ℕ):ℝ)) (C:ℝ), (1 - Real.log t / Real.log ((x:ℝ)+2))^2 ≠ 0 := by
      intro t ht
      have h := hub_t t ht.1 ht.2
      have hpos : (0:ℝ) < 1 - Real.log t / Real.log ((x:ℝ)+2) := by linarith
      exact pow_ne_zero 2 (ne_of_gt hpos)
    have hqc := hnumc.div hden hne1
    have hinv : ContinuousOn (fun t : ℝ => 1/(t * Real.log ((x:ℝ)+2)))
        (Set.Icc (((M-1:ℕ):ℝ)) (C:ℝ)) := by
      refine ContinuousOn.div continuousOn_const (continuousOn_id.mul continuousOn_const) ?_
      intro t ht
      have ht0 : t ≠ 0 := by linarith [ht.1, hA3]
      exact mul_ne_zero ht0 hLne
    exact hqc.mul hinv
  -- ## Abel / Mertens
  have habel := prime_sum_le_integral (A := M-1) (B := C) (f := f) (g := g) (L₀ := L₀) (E := E)
      hA2 hMC hderiv hfint hfnn (Or.inr hg_nonpos) hE hmer'
  -- ## the integral
  have hFcont : ContinuousOn F (Set.Icc (Real.log (((M-1:ℕ):ℝ)) / Real.log ((x:ℝ)+2)) (Real.log ((C:ℝ)) / Real.log ((x:ℝ)+2))) := by
    rw [hF]
    refine ContinuousOn.div (ContinuousOn.log (by fun_prop) ?_) (by fun_prop) ?_
    · intro s hs
      have h3 : s ≤ 1/3 := le_trans hs.2 hub
      linarith
    · intro s hs
      have h3 : s ≤ 1/3 := le_trans hs.2 hub
      linarith
  have hint_eq : (∫ t in (((M-1:ℕ):ℝ))..((C:ℝ)), f t / (t * Real.log t))
      = ∫ s in (Real.log (((M-1:ℕ):ℝ)) / Real.log ((x:ℝ)+2))..(Real.log ((C:ℝ)) / Real.log ((x:ℝ)+2)), F s / s := by
    have h2 : (∫ t in (((M-1:ℕ):ℝ))..((C:ℝ)), f t / (t * Real.log t))
        = ∫ t in (((M-1:ℕ):ℝ))..((C:ℝ)), F (Real.log t / Real.log ((x:ℝ)+2)) / (t * Real.log t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [hf]
    rw [h2]
    exact integral_log_div_log ((x:ℝ)+2) (((M-1:ℕ):ℝ)) ((C:ℝ)) hX1 (by linarith) (by linarith) hab F hFcont
  have hcb : (∫ s in (Real.log (((M-1:ℕ):ℝ)) / Real.log ((x:ℝ)+2))..(Real.log ((C:ℝ)) / Real.log ((x:ℝ)+2)), F s / s) ≤ 0.496 + 10*δ := by
    have hcongr : (∫ s in (Real.log (((M-1:ℕ):ℝ)) / Real.log ((x:ℝ)+2))..(Real.log ((C:ℝ)) / Real.log ((x:ℝ)+2)), F s / s)
        = ∫ s in (Real.log (((M-1:ℕ):ℝ)) / Real.log ((x:ℝ)+2))..(Real.log ((C:ℝ)) / Real.log ((x:ℝ)+2)), Real.log (2 - 3*s)/(s*(1-s)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hαγ] at hs
      have hspos : (0:ℝ) < s := by
        have h1 : (1:ℝ)/10 - δ ≤ s := le_trans hβ' hs.1
        linarith [h1, hδ]
      have hs1 : s ≠ 1 := by
        have h3 : s ≤ 1/3 := le_trans hs.2 hub
        linarith
      simp only [hF]
      field_simp
    rw [hcongr]
    refine cbar_integral_le_half_sharp hδ0 hδ hβ' ?_ hub hαγ
    linarith [hβ', hδ]
  -- ## the Abel error
  have hphi_le : ∀ s ∈ Set.Icc (0:ℝ) (1/3), Real.log (2 - 3*s)/(1-s) ≤ Real.log 2 := by
    intro s hs
    have h := phi_antitone (show (0:ℝ) ∈ Set.Icc (0:ℝ) (1/3) by norm_num) hs hs.1
    simpa using h
  have hfa : f (((M-1:ℕ):ℝ)) ≤ Real.log 2 := by
    have h0 : (0:ℝ) ≤ Real.log (((M-1:ℕ):ℝ)) / Real.log ((x:ℝ)+2) := by linarith [hβ', hδ]
    have h3 : Real.log (((M-1:ℕ):ℝ)) / Real.log ((x:ℝ)+2) ≤ 1/3 := by linarith [hub, hαγ]
    have := hphi_le _ ⟨h0, h3⟩
    simpa only [hf, hF] using this
  have hfc : f ((C:ℝ)) ≤ Real.log 2 := by
    have h0 : (0:ℝ) ≤ Real.log ((C:ℝ)) / Real.log ((x:ℝ)+2) := le_trans (by linarith [hβ', hδ]) hαγ
    have := hphi_le _ ⟨h0, hub⟩
    simpa only [hf, hF] using this
  have hlog2 : 4 * Real.log 2 ≤ 2.8 := by linarith [Real.log_two_lt_d9]
  have herr : 2 * E * (f (((M-1:ℕ):ℝ)) + f ((C:ℝ))) ≤ 2.8 * E := by
    have hsum : f (((M-1:ℕ):ℝ)) + f ((C:ℝ)) ≤ 2 * Real.log 2 := by linarith [hfa, hfc]
    have h2E : (0:ℝ) ≤ 2 * E := by linarith [hE]
    calc 2 * E * (f (((M-1:ℕ):ℝ)) + f ((C:ℝ))) ≤ 2 * E * (2 * Real.log 2) :=
          mul_le_mul_of_nonneg_left hsum h2E
      _ = 4 * Real.log 2 * E := by ring
      _ ≤ 2.8 * E := mul_le_mul_of_nonneg_right hlog2 hE
  -- ## reassembling the outer sum
  have hidx : Finset.Ioc (M-1) C = Finset.Icc M C := by
    ext q
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hsum_eq : (∑ q ∈ (Finset.Icc M C).filter Nat.Prime,
        Real.log (2 - 3 * (Real.log (q : ℝ) / Real.log ((x : ℝ) + 2))) /
          (1 - Real.log (q : ℝ) / Real.log ((x : ℝ) + 2)) / (q : ℝ))
      = ∑ p ∈ (Finset.Ioc (M-1) C).filter Nat.Prime, f (p:ℝ)/(p:ℝ) := by
    rw [← hidx]
  have h2 : (∑ q ∈ (Finset.Icc M C).filter Nat.Prime,
        Real.log (2 - 3 * (Real.log (q : ℝ) / Real.log ((x : ℝ) + 2))) /
          (1 - Real.log (q : ℝ) / Real.log ((x : ℝ) + 2)) / (q : ℝ))
      ≤ (∫ t in (((M-1:ℕ):ℝ))..((C:ℝ)), f t/(t*Real.log t)) + 2 * E * (f (((M-1:ℕ):ℝ)) + f ((C:ℝ))) := by
    rw [hsum_eq]
    exact habel
  have h3 : (∫ t in (((M-1:ℕ):ℝ))..((C:ℝ)), f t/(t*Real.log t)) ≤ 0.496 + 10*δ := by
    rw [hint_eq]
    exact hcb
  linarith [h2, h3, herr]

end Work.NumberTheory.Chen.BTermCount

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-! ## Helper lemmas -/

/-- `x ↦ x / log x` is non-decreasing on `[e, ∞)`. -/
private lemma div_log_le_div_log {a b : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    a / Real.log a ≤ b / Real.log b := by
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 1) ha
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hla : 1 ≤ Real.log a := by
    have h := Real.log_le_log (Real.exp_pos 1) ha
    rwa [Real.log_exp] at h
  have hlb : 1 ≤ Real.log b := le_trans hla (Real.log_le_log ha0 hab)
  have hb1 : b ∈ Set.Ici (Real.exp 1) := le_trans ha hab
  have h1 : Real.log b / b ≤ Real.log a / a := Real.log_div_self_antitoneOn ha hb1 hab
  have h2 : 0 < Real.log a / a := div_pos (by linarith) ha0
  have h3 : 0 < Real.log b / b := div_pos (by linarith) hb0
  have key1 : a / Real.log a = 1 / (Real.log a / a) := by field_simp
  have key2 : b / Real.log b = 1 / (Real.log b / b) := by field_simp
  rw [key1, key2]
  exact one_div_le_one_div_of_le h3 h1

/-- `x / log x ≤ (1 + 2/x) · x / log x`-style comparison used to pass from `x + 2` to `x`. -/
private lemma addTwo_div_log_le (x : ℕ) (hx : 1 < x) :
    ((x : ℝ) + 2) / Real.log ((x : ℝ) + 2) ≤ (1 + 2 / (x : ℝ)) * ((x : ℝ) / Real.log (x : ℝ)) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) < x := by exact_mod_cast hx
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hlog2 : Real.log (x : ℝ) ≤ Real.log ((x : ℝ) + 2) :=
    Real.log_le_log hx0 (by linarith)
  have h3 : ((x : ℝ) + 2) / Real.log ((x : ℝ) + 2) ≤ ((x : ℝ) + 2) / Real.log (x : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hlogx hlog2
  have h4 : ((x : ℝ) + 2) / Real.log (x : ℝ) = (1 + 2 / (x : ℝ)) * ((x : ℝ) / Real.log (x : ℝ)) := by
    rw [show ((x : ℝ) + 2) = (1 + 2 / (x : ℝ)) * (x : ℝ) by field_simp]
    rw [mul_div_assoc]
  linarith [h3, h4.le, h4.ge]

/-- `Real.log 5 ≤ 1.7`, used to bound the `log log` difference in the reciprocal-prime estimate. -/
private lemma log_five_le : Real.log 5 ≤ 1.7 := by
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have h54 : Real.log (5/4) ≤ 5/4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hmul : Real.log 5 = Real.log 4 + Real.log (5/4) := by
    rw [← Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (5:ℝ)/4 ≠ 0)]
    norm_num
  linarith

theorem bTripleCount_le_tenth :
    ∀ᶠ x : ℕ in Filter.atTop, ∀ M Y : ℕ,
      (x : ℝ) ^ ((1 : ℝ) / 10) ≤ (M : ℝ) →
      (x : ℝ) ^ ((1 : ℝ) / 3) ≤ (Y : ℝ) →
      (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 3) →
      (Work.NumberTheory.Chen.BTermCount.bTripleCount x M Y : ℝ)
        ≤ (1 / 2 : ℝ) * (x : ℝ) / Real.log (x : ℝ) := by
  set δ : ℝ := 1/10000 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; norm_num
  have hδle : δ ≤ 1/200 := by rw [hδdef]; norm_num
  set δ₁ : ℝ := δ / 100 with hδ₁def
  have hδ₁pos : 0 < δ₁ := by rw [hδ₁def]; positivity
  have hδ₁nn : 0 ≤ δ₁ := le_of_lt hδ₁pos
  set δ₂ : ℝ := δ / 100 with hδ₂def
  have hδ₂le700 : δ₂ ≤ 1/700 := by rw [hδ₂def, hδdef]; norm_num
  have hδ₂pos : 0 < δ₂ := by rw [hδ₂def]; positivity
  have hδ₂nn : 0 ≤ δ₂ := le_of_lt hδ₂pos
  have hδ₂le : δ₂ ≤ δ / 100 := by rw [hδ₂def]
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 (pi_upper_sharp δ₁ hδ₁pos)
  obtain ⟨L₀, C, hCpos, hCb⟩ :=
    Commons.NumberTheory.Mertens.primeRecips_sub_loglog_powLog 2 (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop ⌈((T₀:ℝ)+2)^3⌉₊,
                  Filter.eventually_ge_atTop ⌈(13:ℝ)^14⌉₊,
                  Filter.eventually_ge_atTop ⌈(Real.exp (Real.sqrt (1000*C/δ)) + 2)^14⌉₊,
                  Filter.eventually_ge_atTop ⌈(10/δ₂)^10⌉₊,
                  Filter.eventually_ge_atTop ⌈(2000/δ)^3⌉₊,
                  Filter.eventually_ge_atTop ⌈(1000/δ)^6⌉₊,
                  Filter.eventually_ge_atTop 1000] with x hxT0 hx13 hxE hxU hxkap hxL
                    hx1000
  intro M Y hM hYge hY2
  have hx1 : (1:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hx0 : (0:ℝ) < (x:ℝ) := by linarith
  have hx10 : (10:ℝ) ≤ (x:ℝ)^((1:ℝ)/3) := by
    have h1000 : ((1000:ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast hx1000
    calc (10:ℝ) = ((1000:ℝ))^((1:ℝ)/3) := by
          rw [show ((1000:ℝ)) = (10:ℝ)^3 by norm_num,
            ← Real.rpow_natCast (10:ℝ) 3, ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ (x:ℝ)^((1:ℝ)/3) := Real.rpow_le_rpow (by norm_num) h1000 (by norm_num)
  have hY10 : (10:ℝ) ≤ (Y:ℝ) := le_trans hx10 hYge
  have hY3 : 3 ≤ Y := by exact_mod_cast (by linarith : (3:ℝ) ≤ (Y:ℝ))
  set Xr : ℝ := (x:ℝ) + 2 with hXrdef
  have hcast : ((x + 2 : ℕ) : ℝ) = Xr := by rw [hXrdef]; push_cast; ring
  have hXr1 : 1 < Xr := by rw [hXrdef]; linarith
  have hXr0 : 0 < Xr := by linarith
  set L : ℝ := Real.log Xr with hLdef
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos hXr1
  have hXrL : Xr / L = ((x:ℝ)+2) / Real.log ((x:ℝ)+2) := by rw [hXrdef, hLdef]
  -- T₀ ≤ x^{1/3} - 1
  have hxcbrt : (T₀:ℝ) + 2 ≤ (x:ℝ)^((1:ℝ)/3) := by
    have h1 : ((T₀:ℝ)+2)^3 ≤ (x:ℝ) := by
      have h2 : ((⌈((T₀:ℝ)+2)^3⌉₊ : ℕ) : ℝ) ≤ (x:ℝ) := by exact_mod_cast hxT0
      linarith [Nat.le_ceil (((T₀:ℝ)+2)^3)]
    have h3 : ((((T₀:ℝ)+2))^3)^((1:ℝ)/3) ≤ ((x:ℝ))^((1:ℝ)/3) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h4 : ((((T₀:ℝ)+2))^3)^((1:ℝ)/3) = (T₀:ℝ)+2 := by
      rw [← Real.rpow_natCast ((T₀:ℝ)+2) 3, ← Real.rpow_mul (by positivity)]
      norm_num
    linarith [h3, h4.le, h4.ge]
  have hpi : ∀ t : ℕ, (x:ℝ)^((1:ℝ)/3) - 1 ≤ (t:ℝ) →
      ((Nat.primesLE t).card : ℝ) ≤ (1+δ₁)*(t:ℝ)/Real.log (t:ℝ) := by
    intro t ht
    have ht' : T₀ ≤ t := by
      have : (T₀:ℝ) ≤ (t:ℝ) := by linarith
      exact_mod_cast this
    exact hT₀ t ht'
  -- x^{1/14} ≥ 13
  have hxq13 : (13:ℝ) ≤ (x:ℝ)^((1:ℝ)/14) := by
    have h1 : ((13:ℝ)^14) ≤ (x:ℝ) := by
      have h2 : ((⌈(13:ℝ)^14⌉₊ : ℕ) : ℝ) ≤ (x:ℝ) := by exact_mod_cast hx13
      linarith [Nat.le_ceil ((13:ℝ)^14)]
    have h3 : (((13:ℝ)^14))^((1:ℝ)/14) ≤ ((x:ℝ))^((1:ℝ)/14) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h4 : (((13:ℝ)^14))^((1:ℝ)/14) = 13 := by
      rw [← Real.rpow_natCast (13:ℝ) 14, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith [h3, h4.le, h4.ge]
  -- the Mertens error E
  set E : ℝ := C / (Real.log ((x:ℝ)^((1:ℝ)/14) - 1)) ^ (2:ℝ) with hEdef
  have hxq13a : (1:ℝ) < (x:ℝ)^((1:ℝ)/14) - 1 := by linarith
  have hlogqpos : 0 < Real.log ((x:ℝ)^((1:ℝ)/14) - 1) := Real.log_pos hxq13a
  have hEnn : 0 ≤ E := by rw [hEdef]; positivity
  have hEsmall : E ≤ δ/1000 := by
    rw [hEdef]
    have h1 : Real.exp (Real.sqrt (1000*C/δ)) + 2 ≤ (x:ℝ)^((1:ℝ)/14) := by
      have h2 : ((Real.exp (Real.sqrt (1000*C/δ)) + 2)^14) ≤ (x:ℝ) := by
        have h3 : ((⌈(Real.exp (Real.sqrt (1000*C/δ)) + 2)^14⌉₊ : ℕ) : ℝ) ≤ (x:ℝ) := by
          exact_mod_cast hxE
        linarith [Nat.le_ceil ((Real.exp (Real.sqrt (1000*C/δ)) + 2)^14)]
      have h4 : (((Real.exp (Real.sqrt (1000*C/δ)) + 2)^14))^((1:ℝ)/14) ≤ ((x:ℝ))^((1:ℝ)/14) :=
        Real.rpow_le_rpow (by positivity) h2 (by norm_num)
      have h5 : (((Real.exp (Real.sqrt (1000*C/δ)) + 2)^14))^((1:ℝ)/14)
          = Real.exp (Real.sqrt (1000*C/δ)) + 2 := by
        rw [← Real.rpow_natCast (Real.exp (Real.sqrt (1000*C/δ)) + 2) 14,
          ← Real.rpow_mul (by positivity)]
        norm_num
      linarith [h4, h5.le, h5.ge]
    have h6 : Real.sqrt (1000*C/δ) ≤ Real.log ((x:ℝ)^((1:ℝ)/14) - 1) := by
      have h7 : Real.exp (Real.sqrt (1000*C/δ)) ≤ (x:ℝ)^((1:ℝ)/14) - 1 := by linarith
      calc Real.sqrt (1000*C/δ) = Real.log (Real.exp (Real.sqrt (1000*C/δ))) :=
            (Real.log_exp _).symm
        _ ≤ Real.log ((x:ℝ)^((1:ℝ)/14) - 1) := Real.log_le_log (Real.exp_pos _) h7
    have h8 : 1000*C/δ ≤ (Real.log ((x:ℝ)^((1:ℝ)/14) - 1)) ^ (2:ℝ) := by
      have h9 : (0:ℝ) ≤ 1000*C/δ := by positivity
      rw [Real.rpow_two]
      nlinarith [h6, Real.sqrt_nonneg (1000*C/δ), Real.sq_sqrt h9]
    have h10 : (0:ℝ) < 1000*C/δ := by positivity
    calc C / (Real.log ((x:ℝ)^((1:ℝ)/14) - 1)) ^ (2:ℝ) ≤ C / (1000*C/δ) :=
          div_le_div_of_nonneg_left (le_of_lt hCpos) h10 h8
      _ = δ/1000 := by field_simp
  -- the Mertens hypothesis, uniform for t ≥ x^{1/14}-1
  have hmer : ∀ t : ℝ, (x:ℝ)^((1:ℝ)/14) - 1 ≤ t →
      |(∑ p ∈ (⌊t⌋₊).primesLE, (1:ℝ)/(p:ℝ)) - Real.log (Real.log t) - L₀| ≤ E := by
    intro t ht
    have ht11 : (11:ℝ) ≤ t := by linarith
    have h1 := hCb t ht11
    have hlogt : Real.log ((x:ℝ)^((1:ℝ)/14) - 1) ≤ Real.log t :=
      Real.log_le_log (by linarith) ht
    have hsq : (Real.log ((x:ℝ)^((1:ℝ)/14) - 1)) ^ (2:ℝ) ≤ (Real.log t) ^ (2:ℝ) :=
      Real.rpow_le_rpow (le_of_lt hlogqpos) hlogt (by norm_num)
    rw [hEdef]
    exact le_trans h1 (div_le_div_of_nonneg_left (le_of_lt hCpos) (by positivity) hsq)
  -- the undershoot
  have hxU' : (10/δ₂)^10 ≤ (x:ℝ) := by
    have h2 : ((⌈(10/δ₂)^10⌉₊ : ℕ) : ℝ) ≤ (x:ℝ) := by exact_mod_cast hxU
    linarith [Nat.le_ceil ((10/δ₂)^10)]
  have hUnd : (1:ℝ)/10 - δ₂ ≤ Real.log ((M:ℝ) - 1) / L := by
    rw [hLdef, hXrdef]
    exact undershoot_le_tenth x M δ₂ hδ₂pos hδ₂le700 hxU' hM
  have hx14le10 : (x:ℝ)^((1:ℝ)/14) ≤ (x:ℝ)^((1:ℝ)/10) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ x)) (by norm_num)
  have hM13n : 13 ≤ M := by
    have h : (13:ℝ) ≤ (M:ℝ) := le_trans hxq13 (le_trans hx14le10 hM)
    exact_mod_cast h
  have hx2 : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 2 ≤ x)
  have hMcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : (1:ℕ) ≤ M)]; norm_num
  have hMminus : (x:ℝ)^((1:ℝ)/14) - 1 ≤ (M:ℝ) - 1 := by linarith [hM, hx14le10]
  have hUnd' : ((1:ℝ)/10 - δ₂)*L ≤ Real.log ((M:ℝ) - 1) := by
    have h3 : (1:ℝ)/10 - δ₂ ≤ Real.log ((M:ℝ) - 1) / L := hUnd
    rwa [le_div_iff₀ hLpos] at h3
  -- C1
  set C1 : ℕ := min (Y - 1) ((x + 2) / (Y * Y)) with hC1def
  have hC1leY : C1 ≤ Y - 1 := by rw [hC1def]; exact min_le_left _ _
  have hC1leQ : C1 ≤ (x + 2) / (Y * Y) := by rw [hC1def]; exact min_le_right _ _
  have hC1cbrt : (C1:ℝ) ≤ Xr^((1:ℝ)/3) := by
    have h1 : C1 ≤ ⌊Xr^((1:ℝ)/3)⌋₊ := by
      rw [hC1def, hXrdef]
      exact min_div_le_floor_cbrt x Y (by omega : 1 ≤ x) hYge
    have h2 : ((⌊Xr^((1:ℝ)/3)⌋₊ : ℕ) : ℝ) ≤ Xr^((1:ℝ)/3) :=
      Nat.floor_le (Real.rpow_nonneg (le_of_lt hXr0) _)
    have h3 : (C1:ℝ) ≤ ((⌊Xr^((1:ℝ)/3)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  set κ : ℝ := 1000 / ((x:ℝ)^((1:ℝ)/3) * L) with hκdef
  set numF : ℕ → ℝ := fun q => Real.log (2 - 3*(Real.log (q:ℝ)/L)) / (1 - Real.log (q:ℝ)/L)
    with hnumFdef
  set SS : Finset ℕ := (Finset.Icc M C1).filter Nat.Prime with hSSdef
  set RQ : ℝ := Xr / L with hRQdef
  have hRQnn : 0 ≤ RQ := by rw [hRQdef]; positivity
  set InS : ℝ := ∑ q ∈ SS, (1:ℝ)/(q:ℝ) with hInSdef
  set OutS : ℝ := ∑ q ∈ SS, numF q / (q:ℝ) with hOutSdef
  -- per-q bound
  have hper : ∀ q ∈ SS,
      (((∑ q₂ ∈ (Finset.Icc Y ((x+2)/q).sqrt).filter Nat.Prime,
        (Nat.primesLE ((x+2)/(q*q₂))).card : ℕ)) : ℝ)
      ≤ (1+δ₁) * (Xr/((q:ℝ)*L) * numF q + Xr/(q:ℝ) * κ + 24*E*(Xr/((q:ℝ)*L))) := by
    intro q hq
    rw [hSSdef, Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hqM, hqC1⟩, hqprime⟩ := hq
    have hqpos : 0 < q := hqprime.pos
    have hq3 : ((q:ℝ))^3 ≤ (x:ℝ)+2 := by
      have h1 : (q:ℝ) ≤ Xr^((1:ℝ)/3) := le_trans (by exact_mod_cast hqC1) hC1cbrt
      have h2 : ((q:ℝ))^3 ≤ (Xr^((1:ℝ)/3))^3 := pow_le_pow_left₀ (by positivity) h1 3
      have h3 : (Xr^((1:ℝ)/3))^3 = Xr := by
        rw [← Real.rpow_natCast (Xr^((1:ℝ)/3)) 3, ← Real.rpow_mul (le_of_lt hXr0)]
        norm_num
      rw [hXrdef] at h3
      linarith [h2, h3.le, h3.ge]
    have hByq : Y ≤ ((x+2)/q).sqrt := by
      have h1 : q * (Y*Y) ≤ x+2 := by
        have h2 : q ≤ (x+2)/(Y*Y) := le_trans hqC1 hC1leQ
        calc q * (Y*Y) ≤ ((x+2)/(Y*Y)) * (Y*Y) := Nat.mul_le_mul_right _ h2
          _ ≤ x+2 := Nat.div_mul_le_self _ _
      have h3 : Y^2 * q ≤ x+2 := by
        calc Y^2 * q = q * (Y*Y) := by ring
          _ ≤ x+2 := h1
      have h4 : Y^2 ≤ (x+2)/q := (Nat.le_div_iff_mul_le hqpos).mpr h3
      exact Nat.le_sqrt'.mpr h4
    have hinner := innerSum_le x Y ((x+2)/q).sqrt q δ₁ E L₀ hδ₁nn hEnn hx1000 hqpos hYge hY2
      hq3 rfl hByq hpi hmer
    have hEq : (1+δ₁) * (Xr/((q:ℝ)*L) * numF q + Xr/(q:ℝ) * κ + 24*E*(Xr/((q:ℝ)*L)))
        = (1+δ₁) * (((x:ℝ)+2)/((q:ℝ)*Real.log ((x:ℝ)+2)) *
              Real.log (2 - 3*(Real.log (q:ℝ)/Real.log ((x:ℝ)+2))) /
                (1 - Real.log (q:ℝ)/Real.log ((x:ℝ)+2))
            + ((x:ℝ)+2)/(q:ℝ) * (1000/((x:ℝ)^((1:ℝ)/3)*Real.log ((x:ℝ)+2)))
            + 24*E*(((x:ℝ)+2)/((q:ℝ)*Real.log ((x:ℝ)+2)))) := by
      rw [hκdef, hnumFdef, hLdef, hXrdef]
      ring_nf
    rw [hEq]
    exact hinner
  -- summation
  have hTdecomp : (∑ q ∈ SS, (Xr/((q:ℝ)*L) * numF q + Xr/(q:ℝ) * κ + 24*E*(Xr/((q:ℝ)*L))))
      = RQ * OutS + (Xr*κ) * InS + (24*E*RQ) * InS := by
    have hOut : OutS = ∑ q ∈ SS, numF q / (q:ℝ) := hOutSdef
    have hIn : InS = ∑ q ∈ SS, (1:ℝ)/(q:ℝ) := hInSdef
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hOut, hIn, hRQdef]
    have e1 : (∑ q ∈ SS, Xr/((q:ℝ)*L) * numF q) = (Xr/L) * (∑ q ∈ SS, numF q/(q:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [hSSdef, Finset.mem_filter] at hq
      have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast hq.2.ne_zero
      field_simp
    have e2 : (∑ q ∈ SS, Xr/(q:ℝ) * κ) = (Xr*κ) * (∑ q ∈ SS, (1:ℝ)/(q:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [hSSdef, Finset.mem_filter] at hq
      have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast hq.2.ne_zero
      field_simp
    have e3 : (∑ q ∈ SS, 24*E*(Xr/((q:ℝ)*L))) = (24*E*(Xr/L)) * (∑ q ∈ SS, (1:ℝ)/(q:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    rw [e1, e2, e3]
  have hsum : ((∑ q ∈ SS, ∑ q₂ ∈ (Finset.Icc Y ((x+2)/q).sqrt).filter Nat.Prime,
        (Nat.primesLE ((x+2)/(q*q₂))).card : ℕ) : ℝ)
      ≤ (1+δ₁) * (RQ * OutS + (Xr*κ) * InS + (24*E*RQ) * InS) := by
    have h1 : ((∑ q ∈ SS, ∑ q₂ ∈ (Finset.Icc Y ((x+2)/q).sqrt).filter Nat.Prime,
        (Nat.primesLE ((x+2)/(q*q₂))).card : ℕ) : ℝ)
        = ∑ q ∈ SS, (((∑ q₂ ∈ (Finset.Icc Y ((x+2)/q).sqrt).filter Nat.Prime,
            (Nat.primesLE ((x+2)/(q*q₂))).card : ℕ)) : ℝ) := by
      rw [Nat.cast_sum]
    rw [h1]
    have h2 : (∑ q ∈ SS, (((∑ q₂ ∈ (Finset.Icc Y ((x+2)/q).sqrt).filter Nat.Prime,
            (Nat.primesLE ((x+2)/(q*q₂))).card : ℕ)) : ℝ))
        ≤ ∑ q ∈ SS, (1+δ₁) * (Xr/((q:ℝ)*L) * numF q + Xr/(q:ℝ) * κ + 24*E*(Xr/((q:ℝ)*L))) :=
      Finset.sum_le_sum hper
    refine le_trans h2 (le_of_eq ?_)
    rw [← Finset.mul_sum, hTdecomp]
  -- outer sum bound
  have hOuter1 : OutS ≤ 0.496 + 10*δ₂ + 2.8*E := by
    rw [hOutSdef]
    by_cases hMC : M - 1 ≤ C1
    · have hOuterLem := outerSum_le_tenth x M C1 E L₀ δ₂ (by omega : 1 < x) hδ₂nn hδ₂le700 hEnn ?_ hMC ?_ ?_ ?_
      · have hEq : (∑ q ∈ (Finset.Icc M C1).filter Nat.Prime,
            Real.log (2 - 3 * (Real.log (q : ℝ) / Real.log ((x : ℝ) + 2))) /
              (1 - Real.log (q : ℝ) / Real.log ((x : ℝ) + 2)) / (q : ℝ))
            = ∑ q ∈ (Finset.Icc M C1).filter Nat.Prime, numF q / (q:ℝ) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [hnumFdef, hLdef, hXrdef]
        rw [← hEq]
        exact hOuterLem
      · have h1 : Real.exp 1 ≤ (12:ℝ) := le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num))
        have h2 : (13:ℝ) ≤ (M:ℝ) := le_trans hxq13 (le_trans hx14le10 hM)
        linarith
      · rw [hXrdef] at hC1cbrt; exact hC1cbrt
      · have h := hUnd
        rw [hLdef, hXrdef] at h
        exact h
      · intro t ht
        exact hmer t (le_trans (by linarith [hM] : (x:ℝ)^((1:ℝ)/14) - 1 ≤ (M:ℝ)-1) ht)
    · have hzero : (∑ q ∈ (Finset.Icc M C1).filter Nat.Prime, numF q / (q:ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro q hq
        rw [Finset.mem_filter, Finset.mem_Icc] at hq
        omega
      rw [hzero]
      linarith [hδ₂nn, hEnn]
  -- reciprocal sum bound
  have hInv1 : InS ≤ 2 := by
    rw [hInSdef]
    by_cases hMC1 : M ≤ C1
    · have hM11 : 11 ≤ M - 1 := by omega
      have hMC : M - 1 ≤ C1 := by omega
      have hInvLem := sum_primes_inv_le_loglog (M - 1) C1 hM11 hMC L₀ E hEnn ?_
      · have heq : (Finset.Ioc (M-1) C1).filter Nat.Prime = (Finset.Icc M C1).filter Nat.Prime := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩
            have h4 : M ≤ z := by
              have h5 : M - 1 + 1 ≤ z := Nat.succ_le_of_lt h1
              rw [Nat.sub_add_cancel (by omega : (1:ℕ) ≤ M)] at h5
              exact h5
            exact ⟨⟨h4, h2⟩, h3⟩
          · rintro ⟨⟨h1, h2⟩, h3⟩
            exact ⟨⟨lt_of_lt_of_le (Nat.sub_one_lt (by omega : M ≠ 0)) h1, h2⟩, h3⟩
        rw [heq] at hInvLem
        refine le_trans hInvLem ?_
        have hlogC1 : Real.log (C1:ℝ) ≤ L/3 := by
          have h2 : Real.log ((C1:ℝ)) ≤ Real.log (Xr^((1:ℝ)/3)) :=
            Real.log_le_log (by exact_mod_cast (by omega : 0 < C1)) hC1cbrt
          rw [Real.log_rpow hXr0] at h2
          rw [hLdef]
          linarith
        have hlogMpos : 0 < Real.log ((M:ℝ) - 1) := by
          have h4 : (0:ℝ) < ((1:ℝ)/10 - δ₂)*L := by nlinarith [hδ₂le700, hLpos]
          linarith [hUnd']
        have hlogC1pos : 0 < Real.log (C1:ℝ) :=
          Real.log_pos (by exact_mod_cast (by omega : 1 < C1))
        have hratio : Real.log (C1:ℝ) / Real.log ((M:ℝ) - 1) ≤ 5 := by
          rw [div_le_iff₀ hlogMpos]
          have h7 : ((7:ℝ)/100) * L ≤ ((1:ℝ)/10 - δ₂)*L := by nlinarith [hδ₂le700, hLpos]
          nlinarith [hlogC1, hUnd', h7, hLpos]
        have hloglog : Real.log (Real.log (C1:ℝ)) - Real.log (Real.log ((M:ℝ) - 1)) ≤ 1.7 := by
          have h8 : Real.log (C1:ℝ) ≠ 0 := ne_of_gt hlogC1pos
          have h9 : Real.log ((M:ℝ) - 1) ≠ 0 := ne_of_gt hlogMpos
          have h10 : Real.log (Real.log (C1:ℝ)) - Real.log (Real.log ((M:ℝ)-1))
              = Real.log (Real.log (C1:ℝ) / Real.log ((M:ℝ)-1)) :=
            (Real.log_div h8 h9).symm
          rw [h10]
          exact le_trans (Real.log_le_log (by positivity) hratio) log_five_le
        have h11 : 4*E ≤ 0.3 := by linarith [hEsmall, hδle]
        have h12 : Real.log (Real.log (((M-1 : ℕ) : ℝ))) = Real.log (Real.log ((M:ℝ)-1)) := by
          rw [hMcast]
        rw [h12]
        linarith [hloglog, h11]
      · intro t ht
        rw [hMcast] at ht
        exact hmer t (le_trans hMminus ht)
    · have hzero : (∑ q ∈ (Finset.Icc M C1).filter Nat.Prime, (1:ℝ)/(q:ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro q hq
        rw [Finset.mem_filter, Finset.mem_Icc] at hq
        omega
      rw [hzero]; norm_num
  -- the kappa term is small
  have hκ2 : 2 * (Xr*κ) ≤ δ * RQ := by
    have h1 : (2000:ℝ) ≤ δ * (x:ℝ)^((1:ℝ)/3) := by
      have h2 : ((⌈(2000/δ)^3⌉₊ : ℕ) : ℝ) ≤ (x:ℝ) := by exact_mod_cast hxkap
      have h3 : (2000/δ)^3 ≤ (x:ℝ) := le_trans (Nat.le_ceil _) h2
      have h4 : 2000/δ ≤ (x:ℝ)^((1:ℝ)/3) := by
        have h5 : ((2000/δ)^3)^((1:ℝ)/3) ≤ (x:ℝ)^((1:ℝ)/3) :=
          Real.rpow_le_rpow (by positivity) h3 (by norm_num)
        have h6 : ((2000/δ)^3)^((1:ℝ)/3) = 2000/δ := by
          rw [← Real.rpow_natCast (2000/δ) 3, ← Real.rpow_mul (le_of_lt (by positivity : (0:ℝ) < 2000/δ))]
          norm_num
        linarith [h5, h6.le, h6.ge]
      rw [div_le_iff₀ hδpos] at h4
      linarith
    have h7 : 2 * (Xr*κ) = (Xr/L) * (2000 / (x:ℝ)^((1:ℝ)/3)) := by
      rw [hκdef]
      field_simp
      ring
    rw [h7, hRQdef]
    have h8 : (0:ℝ) ≤ Xr/L := div_nonneg (le_of_lt hXr0) (le_of_lt hLpos)
    have h9 : 2000 / (x:ℝ)^((1:ℝ)/3) ≤ δ := by
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hx0 _)]; linarith
    calc Xr / L * (2000 / (x:ℝ)^((1:ℝ)/3)) = (2000 / (x:ℝ)^((1:ℝ)/3)) * (Xr/L) := by ring
      _ ≤ δ * (Xr/L) := mul_le_mul_of_nonneg_right h9 h8
  -- the E-term and the tail are small
  have hE2 : (24*E*RQ)*2 ≤ δ * RQ := by
    have h1 : 48*E ≤ δ := by
      have h2 : E ≤ δ/1000 := hEsmall
      have h3 : (48:ℝ)*E ≤ 48*(δ/1000) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      have h4 : (48:ℝ)*(δ/1000) ≤ δ := by rw [hδdef]; norm_num
      exact le_trans h3 h4
    have h3 : (24*E*RQ)*2 = (48*E) * RQ := by ring
    rw [h3]
    exact mul_le_mul_of_nonneg_right h1 hRQnn
  -- final assembly
  have hmain : ((∑ q ∈ SS, ∑ q₂ ∈ (Finset.Icc Y ((x+2)/q).sqrt).filter Nat.Prime,
        (Nat.primesLE ((x+2)/(q*q₂))).card : ℕ) : ℝ)
      ≤ (1+δ₁) * ((0.496 + 10*δ₂ + 2.8*E + 2*δ) * RQ) := by
    refine le_trans hsum ?_
    have h1 : RQ * OutS ≤ RQ * (0.496 + 10*δ₂ + 2.8*E) := mul_le_mul_of_nonneg_left hOuter1 hRQnn
    have h2 : (Xr*κ) * InS ≤ (Xr*κ) * 2 := by
      apply mul_le_mul_of_nonneg_left hInv1
      rw [hκdef]; positivity
    have h3 : (24*E*RQ) * InS ≤ (24*E*RQ) * 2 := by
      apply mul_le_mul_of_nonneg_left hInv1
      positivity
    have h6 : (Xr*κ)*2 ≤ δ*RQ := by linarith [hκ2]
    have h7 : (24*E*RQ)*2 ≤ δ*RQ := hE2
    have hA : (Xr*κ) * InS ≤ δ * RQ := le_trans h2 h6
    have hB : (24*E*RQ) * InS ≤ δ * RQ := le_trans h3 h7
    have hbr : RQ * OutS + (Xr*κ) * InS + (24*E*RQ) * InS
        ≤ (0.496 + 10*δ₂ + 2.8*E + 2*δ) * RQ := by
      have hsum2 : RQ * OutS + (Xr*κ) * InS + (24*E*RQ) * InS
          ≤ RQ * (0.496 + 10*δ₂ + 2.8*E) + δ * RQ + δ * RQ :=
        add_le_add (add_le_add h1 hA) hB
      have hEq : RQ * (0.496 + 10*δ₂ + 2.8*E) + δ * RQ + δ * RQ
          = (0.496 + 10*δ₂ + 2.8*E + 2*δ) * RQ := by ring
      calc RQ * OutS + (Xr*κ) * InS + (24*E*RQ) * InS
          ≤ RQ * (0.496 + 10*δ₂ + 2.8*E) + δ * RQ + δ * RQ := hsum2
        _ = (0.496 + 10*δ₂ + 2.8*E + 2*δ) * RQ := hEq
    exact mul_le_mul_of_nonneg_left hbr (by linarith [hδ₁pos])
  have htail : (12:ℝ) * Xr^((2:ℝ)/3) ≤ δ * RQ := by
    have hXr16 : Xr^((1:ℝ)/6) ≤ 2 * (x:ℝ)^((1:ℝ)/6) := by
      have h1 : Xr ≤ 2 * (x:ℝ) := by rw [hXrdef]; linarith
      calc Xr^((1:ℝ)/6) ≤ (2 * (x:ℝ))^((1:ℝ)/6) :=
            Real.rpow_le_rpow (le_of_lt hXr0) h1 (by norm_num)
        _ = (2:ℝ)^((1:ℝ)/6) * (x:ℝ)^((1:ℝ)/6) := Real.mul_rpow (by norm_num) (le_of_lt hx0)
        _ ≤ 2 * (x:ℝ)^((1:ℝ)/6) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt hx0) _)
            calc (2:ℝ)^((1:ℝ)/6) ≤ (2:ℝ)^(1:ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
    have hlog : L ≤ 6 * Xr^((1:ℝ)/6) := by
      have h1 : Real.log Xr ≤ Xr^((1:ℝ)/6) / ((1:ℝ)/6) :=
        Real.log_le_rpow_div (x := Xr) (le_of_lt hXr0) (by norm_num : (0:ℝ) < (1:ℝ)/6)
      have h2 : Xr^((1:ℝ)/6) / ((1:ℝ)/6) = 6 * Xr^((1:ℝ)/6) := by ring
      rw [hLdef]
      linarith [h1, h2.le, h2.ge]
    have hx6 : (144/δ) ≤ (x:ℝ)^((1:ℝ)/6) := by
      have h2 : ((⌈(1000/δ)^6⌉₊ : ℕ) : ℝ) ≤ (x:ℝ) := by exact_mod_cast hxL
      have h3 : (1000/δ)^6 ≤ (x:ℝ) := le_trans (Nat.le_ceil _) h2
      have h4 : ((1000/δ)^6)^((1:ℝ)/6) ≤ (x:ℝ)^((1:ℝ)/6) :=
        Real.rpow_le_rpow (by positivity) h3 (by norm_num)
      have h5 : ((1000/δ)^6)^((1:ℝ)/6) = 1000/δ := by
        rw [← Real.rpow_natCast (1000/δ) 6, ← Real.rpow_mul (le_of_lt (by positivity : (0:ℝ) < 1000/δ))]
        norm_num
      have h6 : (1000/δ) ≤ (x:ℝ)^((1:ℝ)/6) := by linarith [h4, h5.le, h5.ge]
      have h7 : (144:ℝ)/δ ≤ 1000/δ := by
        apply div_le_div_of_nonneg_right (by norm_num) (le_of_lt hδpos)
      linarith
    have hx6pos : 0 < (x:ℝ)^((1:ℝ)/6) := Real.rpow_pos_of_pos hx0 _
    have h14 : (144:ℝ) ≤ δ * (x:ℝ)^((1:ℝ)/6) := by
      have h2 : δ * (144/δ) ≤ δ * (x:ℝ)^((1:ℝ)/6) :=
        mul_le_mul_of_nonneg_left hx6 (le_of_lt hδpos)
      rwa [mul_div_cancel₀ _ (ne_of_gt hδpos)] at h2
    have hsq : (x:ℝ)^((1:ℝ)/6) * (x:ℝ)^((1:ℝ)/6) = (x:ℝ)^((1:ℝ)/3) := by
      rw [← Real.rpow_add hx0]; norm_num
    have hx13 : (x:ℝ)^((1:ℝ)/3) ≤ Xr^((1:ℝ)/3) := by
      apply Real.rpow_le_rpow (le_of_lt hx0) _ (by norm_num)
      rw [hXrdef]; linarith
    have h1 : 12 * L ≤ δ * Xr^((1:ℝ)/3) := by
      have h2 : 12 * L ≤ 12 * (6 * Xr^((1:ℝ)/6)) := by linarith [hlog]
      have h3 : 12 * (6 * Xr^((1:ℝ)/6)) ≤ 144 * (x:ℝ)^((1:ℝ)/6) := by
        have h4 : Xr^((1:ℝ)/6) ≤ 2 * (x:ℝ)^((1:ℝ)/6) := hXr16
        linarith
      have h5 : 144 * (x:ℝ)^((1:ℝ)/6) ≤ δ * Xr^((1:ℝ)/3) := by
        have h6 : (144:ℝ) * (x:ℝ)^((1:ℝ)/6) ≤ (δ * (x:ℝ)^((1:ℝ)/6)) * (x:ℝ)^((1:ℝ)/6) :=
          mul_le_mul_of_nonneg_right h14 (Real.rpow_nonneg (le_of_lt hx0) _)
        have h7 : (δ * (x:ℝ)^((1:ℝ)/6)) * (x:ℝ)^((1:ℝ)/6) = δ * (x:ℝ)^((1:ℝ)/3) := by
          rw [← hsq]; ring
        linarith [h6, h7.le, h7.ge, mul_le_mul_of_nonneg_left hx13 (le_of_lt hδpos)]
      linarith
    rw [hRQdef]
    rw [show δ * (Xr / L) = δ * Xr / L by ring]
    rw [le_div_iff₀ hLpos]
    have h25 : Xr^((1:ℝ)/3) * Xr^((2:ℝ)/3) = Xr := by
      rw [← Real.rpow_add hXr0, show (1:ℝ)/3 + 2/3 = 1 by norm_num, Real.rpow_one]
    have hsem : 12 * Xr^((2:ℝ)/3) * L = (12*L) * Xr^((2:ℝ)/3) := by ring
    rw [hsem]
    calc (12*L) * Xr^((2:ℝ)/3)
        ≤ (δ * Xr^((1:ℝ)/3)) * Xr^((2:ℝ)/3) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (le_of_lt hXr0) _)
      _ = δ * Xr := by rw [mul_assoc, h25]
  have hfinal : ((∑ q ∈ SS, ∑ q₂ ∈ (Finset.Icc Y ((x+2)/q).sqrt).filter Nat.Prime,
        (Nat.primesLE ((x+2)/(q*q₂))).card : ℕ) : ℝ) ≤ 0.4963 * RQ := by
    have hstep : (1+δ₁) * (0.496 + 10*δ₂ + 2.8*E + 2*δ) ≤ 0.4963 := by
      rw [hδdef, hδ₁def, hδ₂def] at *
      nlinarith [hEsmall]
    calc ((∑ q ∈ SS, ∑ q₂ ∈ (Finset.Icc Y ((x+2)/q).sqrt).filter Nat.Prime,
        (Nat.primesLE ((x+2)/(q*q₂))).card : ℕ) : ℝ)
        ≤ (1+δ₁) * ((0.496 + 10*δ₂ + 2.8*E + 2*δ) * RQ) := hmain
      _ = ((1+δ₁) * (0.496 + 10*δ₂ + 2.8*E + 2*δ)) * RQ := by ring
      _ ≤ 0.4963 * RQ := mul_le_mul_of_nonneg_right hstep hRQnn
  -- convert back to `bTripleCount`
  have hb1 : (bTripleCount x M Y : ℝ) ≤ 0.4963 * RQ := by
    have hcount := bTripleCount_le_sum_pi_div x M Y
    have hcountR : (bTripleCount x M Y : ℝ)
        ≤ ((∑ q ∈ (Finset.Icc M (Y-1)).filter Nat.Prime,
            ∑ q₂ ∈ (Finset.Icc Y ((x+2)/q).sqrt).filter Nat.Prime,
              (Nat.primesLE ((x+2)/(q*q₂))).card : ℕ) : ℝ) := by
      exact_mod_cast hcount
    have hN : (∑ q ∈ (Finset.Icc M (Y-1)).filter Nat.Prime,
            ∑ q₂ ∈ (Finset.Icc Y ((x+2)/q).sqrt).filter Nat.Prime,
              (Nat.primesLE ((x+2)/(q*q₂))).card)
        = (∑ q ∈ SS, ∑ q₂ ∈ (Finset.Icc Y ((x+2)/q).sqrt).filter Nat.Prime,
              (Nat.primesLE ((x+2)/(q*q₂))).card) := by
      rw [hSSdef]
      refine (Finset.sum_subset (s₁ := (Finset.Icc M C1).filter Nat.Prime)
        (s₂ := (Finset.Icc M (Y-1)).filter Nat.Prime) ?_ ?_).symm
      · intro q hq
        rw [Finset.mem_filter, Finset.mem_Icc] at hq ⊢
        exact ⟨⟨hq.1.1, le_trans hq.1.2 hC1leY⟩, hq.2⟩
      · intro q hq hqnot
        rw [Finset.mem_filter, Finset.mem_Icc] at hq
        obtain ⟨⟨hqM, hqY⟩, hqprime⟩ := hq
        have hqC1 : C1 < q := by
          by_contra hcon
          have hqle : q ≤ C1 := not_lt.mp hcon
          exact hqnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hqM, hqle⟩, hqprime⟩)
        have hC1eq : C1 = (x + 2) / (Y * Y) := by
          have hlt : C1 < Y - 1 := lt_of_lt_of_le hqC1 hqY
          rcases min_cases (Y - 1) ((x + 2) / (Y * Y)) with ⟨h, _⟩ | ⟨h, _⟩
          · have h1 : C1 = Y - 1 := by rw [hC1def, h]
            omega
          · rw [hC1def]; exact h
        have hqY2 : x + 2 < q * (Y * Y) := by
          have h : C1 < q := hqC1
          rw [hC1eq] at h
          rw [Nat.div_lt_iff_lt_mul (by positivity : 0 < Y * Y)] at h
          exact h
        have hsq : (x+2)/q < Y^2 := by
          have h1 : (((x+2)/q : ℕ) : ℝ) ≤ ((x:ℝ)+2) / (q:ℝ) := by
            have h0 := Nat.cast_div_le (m := x+2) (n := q) (α := ℝ)
            push_cast at h0
            exact h0
          have h2 : ((x:ℝ)+2)/(q:ℝ) < (((Y^2 : ℕ)) : ℝ) := by
            rw [div_lt_iff₀ (by exact_mod_cast hqprime.pos)]
            have h3 : ((x+2 : ℕ):ℝ) < ((q*(Y*Y) : ℕ) : ℝ) := by exact_mod_cast hqY2
            push_cast at h3 ⊢
            nlinarith [h3]
          have h4 : (((x+2)/q : ℕ) : ℝ) < (((Y^2 : ℕ)) : ℝ) := lt_of_le_of_lt h1 h2
          exact_mod_cast h4
        have hzero : (∑ z ∈ (Finset.Icc Y ((x+2)/q).sqrt).filter Nat.Prime,
            (Nat.primesLE ((x + 2) / (q * z))).card) = 0 := by
          apply Finset.sum_eq_zero
          intro z hz
          rw [Finset.mem_filter, Finset.mem_Icc] at hz
          have hB : ((x+2)/q).sqrt < Y := Nat.sqrt_lt'.mpr hsq
          omega
        rw [hzero]

    have hrestrict : ((∑ q ∈ (Finset.Icc M (Y-1)).filter Nat.Prime,
            ∑ q₂ ∈ (Finset.Icc Y ((x+2)/q).sqrt).filter Nat.Prime,
              (Nat.primesLE ((x+2)/(q*q₂))).card : ℕ) : ℝ)
        = ((∑ q ∈ SS, ∑ q₂ ∈ (Finset.Icc Y ((x+2)/q).sqrt).filter Nat.Prime,
              (Nat.primesLE ((x+2)/(q*q₂))).card : ℕ) : ℝ) := by
      rw [hN]
    exact le_trans hcountR (hrestrict ▸ hfinal)
  -- final comparison with `x / log x`
  have hcomp : 0.4963 * RQ ≤ (1/2 : ℝ) * ((x:ℝ) / Real.log (x:ℝ)) := by
    have h1 : RQ ≤ (1 + 2/(x:ℝ)) * ((x:ℝ) / Real.log (x:ℝ)) := by
      rw [hRQdef, hXrdef, hLdef]
      exact addTwo_div_log_le x (by omega : 1 < x)
    have h2 : (0:ℝ) ≤ (x:ℝ) / Real.log (x:ℝ) :=
      div_nonneg (le_of_lt hx0) (le_of_lt (Real.log_pos hx1))
    have h3 : 0.4963 * (1 + 2/(x:ℝ)) ≤ 1/2 := by
      have hx1000' : (1000:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx1000
      have h4 : 0.4963 * 2 / (x:ℝ) ≤ 0.4963 * 2 / 1000 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx1000'
      calc 0.4963 * (1 + 2/(x:ℝ)) = 0.4963 + 0.4963*2/(x:ℝ) := by ring
        _ ≤ 0.4963 + 0.4963*2/1000 := add_le_add (le_refl _) h4
        _ ≤ 1/2 := by norm_num
    calc 0.4963 * RQ
        ≤ 0.4963 * ((1 + 2/(x:ℝ)) * ((x:ℝ)/Real.log (x:ℝ))) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = (0.4963 * (1 + 2/(x:ℝ))) * ((x:ℝ)/Real.log (x:ℝ)) := by ring
      _ ≤ (1/2) * ((x:ℝ) / Real.log (x:ℝ)) := mul_le_mul_of_nonneg_right h3 h2
  have hfin : (bTripleCount x M Y : ℝ) ≤ (1/2) * ((x:ℝ) / Real.log (x:ℝ)) :=
    le_trans hb1 hcomp
  rw [mul_div_assoc]
  exact hfin

end Work.NumberTheory.Chen.BTermCount
