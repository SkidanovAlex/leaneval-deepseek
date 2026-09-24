import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.prime_sum_le_integral
import Submission.Work.NumberTheory.Chen.BTermCount.integral_log_div_log
import Submission.Work.NumberTheory.Chen.BTermCount.cbar_integral_le_relaxed
import Submission.Work.NumberTheory.Chen.BTermCount.phi_antitone

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace Work.NumberTheory.Chen.BTermCount

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

/-- The outer (`q`) sum of the `B`-term estimate. With `L = log(x+2)`, `β_q = log q / L`, the sum `∑_{M ≤ q ≤ C, q prime} φ(log q/L)/q`, `φ(s) = log(2−3s)/(1−s)`, is at most `0.75 + 10δ + 2.8E`, where `δ` bounds the undershoot of `log(M−1)/L` below `1/14` and `E` is a uniform second-Mertens error on `[(M−1), ∞)`.

Route: Abel/Mertens (`prime_sum_le_integral`) with `f(t) = φ(log t/L)`, which is non-negative and non-increasing on `[M−1, C]` (because `M−1 ≥ e` and `C ≤ (x+2)^{1/3}`, so `log t/L ∈ (0, 1/3]` there, where `φ ≥ 0` and `φ` is antitone — module `phi_antitone`); the integral `∫_{M−1}^{C} φ(log t/L)/(t log t) dt` becomes `∫_{s₀}^{s₁} φ(s)/s ds` by the change of variable `t = (x+2)^s` (module `integral_log_div_log`), with `s₀ = log(M−1)/L ≥ 1/14 − δ` and `s₁ = log C/L ≤ 1/3`; that is exactly the integrand of `cbar_integral_le_relaxed` (module `cbar_integral_le_relaxed`), giving `≤ 0.75 + 10δ`. The Abel error is `2E(φ(s₀) + φ(s₁)) ≤ 2E(2 log 2) ≤ 2.8E` since `φ ≤ log 2`. -/
theorem outerSum_le (x M C : ℕ) (E L₀ δ : ℝ) (hx : 1 < x) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/700)
    (hE : 0 ≤ E)
    (hM : Real.exp 1 ≤ (M : ℝ) - 1) (hMC : M - 1 ≤ C)
    (hC : (C : ℝ) ≤ ((x : ℝ) + 2) ^ ((1:ℝ)/3))
    (hβ : (1:ℝ)/14 - δ ≤ Real.log ((M : ℝ) - 1) / Real.log ((x : ℝ) + 2))
    (hmer : ∀ t : ℝ, ((M : ℝ) - 1) ≤ t →
      |(∑ p ∈ (⌊t⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log t) - L₀| ≤ E) :
    (∑ q ∈ (Finset.Icc M C).filter Nat.Prime,
        Real.log (2 - 3 * (Real.log (q : ℝ) / Real.log ((x : ℝ) + 2))) /
          (1 - Real.log (q : ℝ) / Real.log ((x : ℝ) + 2)) / (q : ℝ))
      ≤ 0.75 + 10 * δ + 2.8 * E := by
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
  have hβ' : (1:ℝ)/14 - δ ≤ Real.log (((M-1:ℕ):ℝ)) / Real.log ((x:ℝ)+2) := by
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
  have hcb : (∫ s in (Real.log (((M-1:ℕ):ℝ)) / Real.log ((x:ℝ)+2))..(Real.log ((C:ℝ)) / Real.log ((x:ℝ)+2)), F s / s) ≤ 0.75 + 10*δ := by
    have hcongr : (∫ s in (Real.log (((M-1:ℕ):ℝ)) / Real.log ((x:ℝ)+2))..(Real.log ((C:ℝ)) / Real.log ((x:ℝ)+2)), F s / s)
        = ∫ s in (Real.log (((M-1:ℕ):ℝ)) / Real.log ((x:ℝ)+2))..(Real.log ((C:ℝ)) / Real.log ((x:ℝ)+2)), Real.log (2 - 3*s)/(s*(1-s)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hαγ] at hs
      have hspos : (0:ℝ) < s := by
        have h1 : (1:ℝ)/14 - δ ≤ s := le_trans hβ' hs.1
        linarith [h1, hδ]
      have hs1 : s ≠ 1 := by
        have h3 : s ≤ 1/3 := le_trans hs.2 hub
        linarith
      simp only [hF]
      field_simp
    rw [hcongr]
    refine cbar_integral_le_relaxed hδ0 hδ hβ' ?_ hub hαγ
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
  have h3 : (∫ t in (((M-1:ℕ):ℝ))..((C:ℝ)), f t/(t*Real.log t)) ≤ 0.75 + 10*δ := by
    rw [hint_eq]
    exact hcb
  linarith [h2, h3, herr]

end Work.NumberTheory.Chen.BTermCount
