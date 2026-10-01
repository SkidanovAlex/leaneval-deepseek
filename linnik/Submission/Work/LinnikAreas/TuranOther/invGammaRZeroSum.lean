import Mathlib
import Submission.Work.LinnikAreas.TuranOther.PFZeroSumDefs
import Submission.Work.LinnikAreas.FarRepel.digammaDerivSeries
import Submission.Work.LinnikAreas.FarRepel.digammaDerivSeriesSummable
import Submission.Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole

namespace Work.LinnikAreas.TuranOther

open Complex Filter
open scoped Topology BigOperators Classical

noncomputable section

/-! ## The reciprocal archimedean factor `(Γ_ℝ ·)⁻¹` -/

/-- `Γ_ℝ 2 = π⁻¹`. -/
lemma invGammaR_two : Complex.Gammaℝ 2 = ((Real.pi : ℂ))⁻¹ := by
  rw [Complex.Gammaℝ_def]
  norm_num [Complex.cpow_neg_one, Complex.Gamma_one]

/-- `(Γ_ℝ 2)⁻¹ = π`. -/
lemma invGammaRInv_two : (Complex.Gammaℝ 2)⁻¹ = (Real.pi : ℂ) := by
  rw [invGammaR_two, inv_inv]

/-- The recurrence `(Γ_ℝ z)⁻¹ = (z/(2π)) · (Γ_ℝ (z+2))⁻¹`, valid for every `z`. -/
lemma invGammaR_inv_shift (z : ℂ) :
    (Complex.Gammaℝ z)⁻¹ = (z / (2 * (Real.pi : ℂ))) * (Complex.Gammaℝ (z + 2))⁻¹ := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rcases eq_or_ne z 0 with rfl | hz
  · have h0 : Complex.Gammaℝ 0 = 0 := Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by norm_num⟩
    rw [h0, inv_zero]; simp
  · have hadd := Complex.Gammaℝ_add_two hz
    rcases eq_or_ne (Complex.Gammaℝ z) 0 with hzG | hzG
    · have h2 : Complex.Gammaℝ (z + 2) = 0 := by rw [hadd, hzG]; ring
      rw [hzG, h2, inv_zero, mul_zero]
    · rw [hadd]
      field_simp

/-- `Γ_ℝ` is differentiable at every point with positive real part. -/
lemma invGammaR_differentiableAt_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s := by
    have hf : DifferentiableAt ℂ (fun y : ℂ => (Real.pi : ℂ) ^ y) (-s / 2) :=
      (Complex.hasStrictDerivAt_const_cpow (x := (Real.pi : ℂ)) (y := -s / 2)
        (Or.inl hpi)).hasDerivAt.differentiableAt
    exact hf.comp s (by fun_prop)
  have h2 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) s := by
    have hg : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
      Complex.differentiableAt_Gamma (s / 2) (fun m hm => by
        have hre : (s / 2).re = -((m : ℝ)) := by rw [hm]; simp
        have hpos : 0 < (s / 2).re := by rw [Complex.div_re]; simp; linarith
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith)
    exact hg.comp s (by fun_prop)
  have h3 : DifferentiableAt ℂ
      (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) s := h1.mul h2
  exact h3

/-- An entire function which is not identically zero has finite vanishing order everywhere. -/
lemma invGammaR_analyticOrderAt_ne_top {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0)
    (u : ℂ) : analyticOrderAt f u ≠ ⊤ := by
  intro htop
  have hf_an : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have h0_an : AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ := fun z _ => analyticAt_const
  have hev : f =ᶠ[𝓝 u] (0 : ℂ → ℂ) := analyticOrderAt_eq_top.mp htop
  exact hne (hf_an.eq_of_eventuallyEq h0_an hev)

/-- The vanishing order of a pointwise product of two entire functions which do not vanish
identically is the sum of the vanishing orders. -/
lemma invGammaR_analyticOrderNatAt_mul {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f ≠ 0) (hg0 : g ≠ 0) (u : ℂ) :
    analyticOrderNatAt (f * g) u = analyticOrderNatAt f u + analyticOrderNatAt g u :=
  analyticOrderNatAt_mul (hf.analyticAt u) (hg.analyticAt u)
    (invGammaR_analyticOrderAt_ne_top hf hf0 u) (invGammaR_analyticOrderAt_ne_top hg hg0 u)

/-- Shifting the argument by a constant does not change the vanishing order. -/
lemma invGammaR_analyticOrderNatAt_comp_add_const (f : ℂ → ℂ) (c u : ℂ) :
    analyticOrderNatAt (fun z : ℂ => f (z + c)) u = analyticOrderNatAt f (u + c) := by
  have hg : AnalyticAt ℂ (fun z : ℂ => z + c) u := analyticAt_id.add analyticAt_const
  have hd : deriv (fun z : ℂ => z + c) u ≠ 0 := by simp
  have h : analyticOrderAt (f ∘ fun z : ℂ => z + c) u = analyticOrderAt f (u + c) :=
    analyticOrderAt_comp_of_deriv_ne_zero (𝕜 := ℂ) (f := f) (g := fun z : ℂ => z + c) hg hd
  rw [show (fun z : ℂ => f (z + c)) = (f ∘ fun z : ℂ => z + c) from rfl]
  simp only [analyticOrderNatAt]
  rw [h]

/-- `(Γ_ℝ ·)⁻¹` vanishes to order one at `-2n` and nowhere else. -/
lemma invGammaRInv_order_two_mul (n : ℕ) :
    analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) (-(2 * (n : ℂ))) = 1 := by
  have hdiff : Differentiable ℂ (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) :=
    Complex.differentiable_Gammaℝ_inv
  have hne : (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) ≠ 0 := by
    intro h
    have h2 := congr_fun h 2
    simp only [Pi.zero_apply] at h2
    rw [invGammaRInv_two] at h2
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero h2
  induction n with
  | zero =>
    have hbase : analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) 0 = 1 := by
      refine ((hdiff.analyticAt 0).analyticOrderNatAt_eq_iff
        (invGammaR_analyticOrderAt_ne_top hdiff hne 0)).mpr ?_
      refine ⟨fun z : ℂ => (2 * (Real.pi : ℂ))⁻¹ * (Complex.Gammaℝ (z + 2))⁻¹,
        ?_, ?_, ?_⟩
      · exact ((Complex.differentiable_Gammaℝ_inv.comp
          (differentiable_id.add_const 2)).const_mul _).analyticAt 0
      · have hval : (Complex.Gammaℝ (0 + 2))⁻¹ = (Real.pi : ℂ) := by
          rw [zero_add, invGammaRInv_two]
        simp only [Pi.mul_apply]
        rw [hval]
        exact mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      · filter_upwards with z
        rw [invGammaR_inv_shift]
        simp only [sub_zero, pow_one, smul_eq_mul, div_eq_mul_inv]
        ring
    simpa using hbase
  | succ n ih =>
    have hprod : (fun z : ℂ => (z / (2 * (Real.pi : ℂ))) * (Complex.Gammaℝ (z + 2))⁻¹)
        = (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) := by
      funext z; exact (invGammaR_inv_shift z).symm
    have hf0 : (fun z : ℂ => z / (2 * (Real.pi : ℂ))) ≠ 0 := by
      intro h
      have h1 := congr_fun h 1
      rw [Pi.zero_apply] at h1
      change (1 : ℂ) / (2 * (Real.pi : ℂ)) = 0 at h1
      exact (div_ne_zero one_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))) h1
    have hg0 : (fun z : ℂ => (Complex.Gammaℝ (z + 2))⁻¹) ≠ 0 := by
      intro h
      have h1 := congr_fun h 0
      rw [Pi.zero_apply] at h1
      change (Complex.Gammaℝ (0 + 2))⁻¹ = 0 at h1
      rw [zero_add, invGammaRInv_two] at h1
      exact (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) h1
    have h1 : analyticOrderNatAt
        (fun z : ℂ => (z / (2 * (Real.pi : ℂ))) * (Complex.Gammaℝ (z + 2))⁻¹)
        (-(2 * ((n + 1 : ℕ) : ℂ))) = 1 := by
      have hmul := invGammaR_analyticOrderNatAt_mul (f := fun z : ℂ => z / (2 * (Real.pi : ℂ)))
        (g := fun z : ℂ => (Complex.Gammaℝ (z + 2))⁻¹)
        (differentiable_id.div_const _) (hdiff.comp (differentiable_id.add_const 2)) hf0 hg0
        (-(2 * ((n + 1 : ℕ) : ℂ)))
      rw [show (fun z : ℂ => (z / (2 * (Real.pi : ℂ))) * (Complex.Gammaℝ (z + 2))⁻¹)
          = ((fun z : ℂ => z / (2 * (Real.pi : ℂ)))
              * (fun z : ℂ => (Complex.Gammaℝ (z + 2))⁻¹)) from rfl]
      rw [hmul]
      have hfirst : analyticOrderNatAt (fun z : ℂ => z / (2 * (Real.pi : ℂ)))
          (-(2 * ((n + 1 : ℕ) : ℂ))) = 0 := by
        have hval : (fun z : ℂ => z / (2 * (Real.pi : ℂ)))
            (-(2 * ((n + 1 : ℕ) : ℂ))) ≠ 0 := by
          have hne0 : (-(2 * ((n + 1 : ℕ) : ℂ))) ≠ 0 := by
            exact neg_ne_zero.mpr (mul_ne_zero two_ne_zero
              (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)))
          exact div_ne_zero hne0 (mul_ne_zero two_ne_zero
            (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        have han : AnalyticAt ℂ (fun z : ℂ => z / (2 * (Real.pi : ℂ)))
            (-(2 * ((n + 1 : ℕ) : ℂ))) :=
          (differentiable_id.div_const _).analyticAt _
        have h0 : analyticOrderAt (fun z : ℂ => z / (2 * (Real.pi : ℂ)))
            (-(2 * ((n + 1 : ℕ) : ℂ))) = 0 := (han.analyticOrderAt_eq_zero).mpr hval
        show (analyticOrderAt (fun z : ℂ => z / (2 * (Real.pi : ℂ)))
            (-(2 * ((n + 1 : ℕ) : ℂ)))).toNat = 0
        rw [h0]
        exact ENat.toNat_zero
      have hsecond : analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + 2))⁻¹)
          (-(2 * ((n + 1 : ℕ) : ℂ))) = 1 := by
        have hshift := invGammaR_analyticOrderNatAt_comp_add_const (fun y : ℂ => (Complex.Gammaℝ y)⁻¹) 2
          (-(2 * ((n + 1 : ℕ) : ℂ)))
        rw [show (fun z : ℂ => (Complex.Gammaℝ (z + 2))⁻¹)
            = (fun z : ℂ => (fun y : ℂ => (Complex.Gammaℝ y)⁻¹) (z + 2)) from rfl, hshift]
        have harith : -(2 * ((n + 1 : ℕ) : ℂ)) + 2 = -(2 * (n : ℂ)) := by push_cast; ring
        rw [harith]
        exact ih
      rw [hfirst, hsecond]
    rwa [hprod] at h1

/-- `(Γ_ℝ ·)⁻¹` does not vanish at points which are not even negative integers. -/
lemma invGammaRInv_order_of_not (u : ℂ) (h : ∀ n : ℕ, u ≠ -(2 * (n : ℂ))) :
    analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) u = 0 := by
  have hdiff : Differentiable ℂ (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) :=
    Complex.differentiable_Gammaℝ_inv
  have hu : Complex.Gammaℝ u ≠ 0 := by
    intro h0
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h0
    exact h n hn
  have hval : (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) u ≠ 0 := by
    change (Complex.Gammaℝ u)⁻¹ ≠ 0
    exact inv_ne_zero hu
  have h0 : analyticOrderAt (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) u = 0 :=
    (hdiff.analyticAt u).analyticOrderAt_eq_zero.mpr hval
  simp [analyticOrderNatAt, h0]

/-- Vanishing order of `(Γ_ℝ (· + a))⁻¹`. -/
lemma invGammaRInv_order_shifted (a : ℕ) (u : ℂ) :
    analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) u
      = if ∃ n : ℕ, u + (a : ℂ) = -(2 * (n : ℂ)) then 1 else 0 := by
  have hshift := invGammaR_analyticOrderNatAt_comp_add_const (fun y : ℂ => (Complex.Gammaℝ y)⁻¹)
    (a : ℂ) u
  rw [show (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹)
      = (fun z : ℂ => (fun y : ℂ => (Complex.Gammaℝ y)⁻¹) (z + (a : ℂ))) from rfl, hshift]
  by_cases h : ∃ n : ℕ, u + (a : ℂ) = -(2 * (n : ℂ))
  · rw [if_pos h]
    obtain ⟨n, hn⟩ := h
    rw [hn]
    exact invGammaRInv_order_two_mul n
  · rw [if_neg h]
    exact invGammaRInv_order_of_not (u + (a : ℂ)) (fun n hn => h ⟨n, hn⟩)

/-! ## The zero-sum reindexing -/

/-- `z ^ (-(k+1)) = (1/z) ^ (k+1)`. -/
lemma invGammaR_neg_zpow_eq (z : ℂ) (k : ℕ) :
    z ^ (-(k + 1) : ℤ) = (1 / z) ^ (k + 1) := by
  rw [show (-(k + 1) : ℤ) = -((k + 1 : ℕ) : ℤ) by push_cast; ring]
  rw [zpow_neg, zpow_natCast, one_div, inv_pow]

/-- Rewriting `(1/(s+2n))^{k+1}` as `(s+2n)^{-(k+1)}`. -/
lemma invGammaR_one_div_two_mul (s : ℂ) (k n : ℕ) :
    (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1) = (s + 2 * (n : ℂ)) ^ (-(k + 1) : ℤ) := by
  rw [show s + ((2 * n : ℕ) : ℂ) = s + 2 * (n : ℂ) by push_cast; ring,
    invGammaR_neg_zpow_eq (s + 2 * (n : ℂ)) k]

/-- The trivial-zero series of `(Γ_ℝ (· + a))⁻¹` is summable. -/
lemma invGammaR_summable_series (a : ℕ) (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 1 < t.re) :
    Summable (fun n : ℕ => (t + (a : ℂ) + 2 * (n : ℂ)) ^ (-(k + 1) : ℤ)) := by
  rw [show (fun n : ℕ => (t + (a : ℂ) + 2 * (n : ℂ)) ^ (-(k + 1) : ℤ))
      = (fun n : ℕ => (1 / (t + (a : ℂ) + 2 * (n : ℂ))) ^ (k + 1)) from
    funext (fun n => invGammaR_neg_zpow_eq _ k)]
  refine Summable.of_norm_bounded (g := fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ (k + 1)) ?_ ?_
  · have h := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (k + 1)) 1).mpr
      ((Real.summable_one_div_nat_pow (p := k + 1)).mpr (by omega : 1 < k + 1))
    simpa [Nat.cast_add, Nat.cast_one] using h
  · intro n
    have hge : ((n : ℝ) + 1) ≤ ‖t + (a : ℂ) + 2 * (n : ℂ)‖ := by
      have hre : (t + (a : ℂ) + 2 * (n : ℂ)).re = t.re + (a : ℝ) + 2 * (n : ℝ) := by
        simp [Complex.add_re]
      have h1 : ((n : ℝ) + 1) ≤ t.re + (a : ℝ) + 2 * (n : ℝ) := by
        have h2 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
        linarith
      calc ((n : ℝ) + 1) ≤ t.re + (a : ℝ) + 2 * (n : ℝ) := h1
        _ = (t + (a : ℂ) + 2 * (n : ℂ)).re := hre.symm
        _ ≤ ‖t + (a : ℂ) + 2 * (n : ℂ)‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
    rw [norm_pow, norm_div, norm_one, ← one_div_pow]
    exact pow_le_pow_left₀ (by positivity)
      (one_div_le_one_div_of_le (by positivity) hge) (k + 1)

/-- The zero sum of `(Γ_ℝ (· + a))⁻¹` is the trivial-zero series. -/
lemma invGammaR_zeroSum_eq (a : ℕ) (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 1 < t.re) :
    Summable (fun u : ℂ =>
        ((analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) u : ℕ) : ℂ)
          * (t - u) ^ (-(k + 1) : ℤ))
      ∧ zeroSumK (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) t k
          = ∑' n : ℕ, (t + (a : ℂ) + 2 * (n : ℂ)) ^ (-(k + 1) : ℤ) := by
  classical
  have hz_ne : ∀ n : ℕ, t + (a : ℂ) + 2 * (n : ℂ) ≠ 0 := by
    intro n h0
    have hre : (t + (a : ℂ) + 2 * (n : ℂ)).re = t.re + (a : ℝ) + 2 * (n : ℝ) := by
      simp [Complex.add_re]
    have hzero : (t + (a : ℂ) + 2 * (n : ℂ)).re = 0 := by rw [h0]; simp
    rw [hre] at hzero
    have h2 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    have h3 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hGsum : Summable (fun n : ℕ => (t + (a : ℂ) + 2 * (n : ℂ)) ^ (-(k + 1) : ℤ)) :=
    invGammaR_summable_series a k hk ht
  have hGne : ∀ n : ℕ, (t + (a : ℂ) + 2 * (n : ℂ)) ^ (-(k + 1) : ℤ) ≠ 0 := by
    intro n
    rw [invGammaR_neg_zpow_eq]
    exact pow_ne_zero _ (div_ne_zero one_ne_zero (hz_ne n))
  have hinj : Function.Injective (fun n : ℕ => -((a : ℂ)) - 2 * (n : ℂ)) := by
    intro m n hmn
    have h2 : (2 : ℂ) * ((m : ℂ)) = 2 * ((n : ℂ)) := by linear_combination -hmn
    have h3 : ((m : ℂ)) = ((n : ℂ)) := mul_left_cancel₀ two_ne_zero h2
    exact_mod_cast h3
  have hsub : Function.support (fun u : ℂ =>
        ((analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) u : ℕ) : ℂ)
          * (t - u) ^ (-(k + 1) : ℤ))
      ⊆ Set.range (fun x : ↑(Function.support
          (fun n : ℕ => (t + (a : ℂ) + 2 * (n : ℂ)) ^ (-(k + 1) : ℤ))) =>
            -((a : ℂ)) - 2 * (((x : ℕ)) : ℂ)) := by
    intro u hu
    rw [Function.mem_support] at hu
    have hord : analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) u ≠ 0 := by
      intro h0
      exact hu (by rw [h0]; simp)
    rw [invGammaRInv_order_shifted] at hord
    split_ifs at hord with h
    · obtain ⟨n, hn⟩ := h
      refine ⟨⟨n, ?_⟩, ?_⟩
      · rw [Function.mem_support]; exact hGne n
      · have hu : u = -((a : ℂ)) - 2 * ((n : ℂ)) := by
          linear_combination hn
        exact hu.symm
    · exact absurd rfl hord
  have hval : ∀ x : ↑(Function.support
        (fun n : ℕ => (t + (a : ℂ) + 2 * (n : ℂ)) ^ (-(k + 1) : ℤ))),
      (fun u : ℂ => ((analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) u : ℕ) : ℂ)
          * (t - u) ^ (-(k + 1) : ℤ)) (-((a : ℂ)) - 2 * ((x : ℕ) : ℂ))
        = (t + (a : ℂ) + 2 * ((x : ℕ) : ℂ)) ^ (-(k + 1) : ℤ) := by
    intro x
    have hord : analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹)
        (-((a : ℂ)) - 2 * ((x : ℕ) : ℂ)) = 1 := by
      rw [invGammaRInv_order_shifted]
      rw [if_pos ⟨(x : ℕ), by ring⟩]
    have harg : t - (-((a : ℂ)) - 2 * ((x : ℕ) : ℂ))
        = t + (a : ℂ) + 2 * ((x : ℕ) : ℂ) := by ring
    show ((analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹)
        (-((a : ℂ)) - 2 * ((x : ℕ) : ℂ)) : ℕ) : ℂ) * _ = _
    rw [hord, harg]
    norm_num
  have key : HasSum (fun u : ℂ =>
      ((analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) u : ℕ) : ℂ)
        * (t - u) ^ (-(k + 1) : ℤ))
      (∑' n : ℕ, (t + (a : ℂ) + 2 * (n : ℂ)) ^ (-(k + 1) : ℤ)) ↔
      HasSum (fun n : ℕ => (t + (a : ℂ) + 2 * (n : ℂ)) ^ (-(k + 1) : ℤ))
        (∑' n : ℕ, (t + (a : ℂ) + 2 * (n : ℂ)) ^ (-(k + 1) : ℤ)) :=
    hasSum_iff_hasSum_of_ne_zero_bij
      (fun x : ↑(Function.support
          (fun n : ℕ => (t + (a : ℂ) + 2 * (n : ℂ)) ^ (-(k + 1) : ℤ))) =>
            -((a : ℂ)) - 2 * ((x : ℕ) : ℂ))
      (fun x y hxy => Subtype.ext (hinj hxy)) hsub hval
  have hsum : Summable (fun u : ℂ =>
      ((analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) u : ℕ) : ℂ)
        * (t - u) ^ (-(k + 1) : ℤ)) := (key.mpr hGsum.hasSum).summable
  refine ⟨hsum, ?_⟩
  have htsum : (∑' u : ℂ, ((analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) u : ℕ) : ℂ)
        * (t - u) ^ (-(k + 1) : ℤ))
      = ∑' n : ℕ, (t + (a : ℂ) + 2 * (n : ℂ)) ^ (-(k + 1) : ℤ) :=
    (key.mpr hGsum.hasSum).tsum_eq
  rw [zeroSumK]
  exact htsum

/-! ## The derivative side -/

/-- The `k`-th derivative of `z ↦ ψ(z/2)`, `ψ = digamma`. -/
lemma invGammaR_digamma_div_two (m : ℕ) {s : ℂ} (hs : 0 < s.re) :
    iteratedDeriv m (fun z : ℂ => Complex.digamma (z / 2)) s
      = (1 / 2 : ℂ) ^ m * iteratedDeriv m Complex.digamma (s / 2) := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hUdef
  have hU : IsOpen U := by rw [hUdef]; exact isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ U := hs
  have huniq : UniqueDiffOn ℂ U := hU.uniqueDiffOn
  have hmaps : Set.MapsTo (fun x : ℂ => (1 / 2) * x) U U := by
    intro x hx
    rw [hUdef] at hx ⊢
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Complex.mul_re]
    norm_num
    linarith
  have hdG : DifferentiableOn ℂ Complex.Gamma U := by
    intro z hz
    rw [hUdef] at hz
    simp only [Set.mem_setOf_eq] at hz
    apply (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m hm
    have hre : z.re = -((m : ℝ)) := by have := congrArg Complex.re hm; simpa using this
    have hlt : (0 : ℝ) < -((m : ℝ)) := by rw [← hre]; exact hz
    have hle : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hdD : DifferentiableOn ℂ (deriv Complex.Gamma) U := hdG.deriv hU
  have hne : ∀ z ∈ U, Complex.Gamma z ≠ 0 := by
    intro z hz; rw [hUdef] at hz; simp only [Set.mem_setOf_eq] at hz
    exact Complex.Gamma_ne_zero_of_re_pos hz
  have hquot : DifferentiableOn ℂ (fun z => deriv Complex.Gamma z / Complex.Gamma z) U :=
    hdD.div hdG hne
  have hdig : DifferentiableOn ℂ Complex.digamma U :=
    hquot.congr (fun z hz => by simp [Complex.digamma_def, logDeriv_apply])
  have hcont : ContDiffOn ℂ (↑m) Complex.digamma U := DifferentiableOn.contDiffOn hdig hU
  have hcomp := iteratedDerivWithin_comp_const_smul (s := U) (x := s) hsU huniq
    (f := Complex.digamma) hcont (1 / 2 : ℂ) hmaps
  have hfun : Set.EqOn (fun z : ℂ => Complex.digamma (z / 2))
      (fun x : ℂ => Complex.digamma ((1 / 2) * x)) U := fun z _ => by congr 1; ring
  rw [← iteratedDerivWithin_of_isOpen hU hsU (n := m)
    (f := fun z : ℂ => Complex.digamma (z / 2))]
  rw [(iteratedDerivWithin_congr hfun) hsU]
  rw [hcomp]
  rw [show (1 / 2 : ℂ) * s = s / 2 by ring]
  have hs2U : s / 2 ∈ U := by
    rw [hUdef]; simp only [Set.mem_setOf_eq]; rw [Complex.div_re]; simp; linarith
  rw [iteratedDerivWithin_of_isOpen hU hs2U (n := m) (f := Complex.digamma)]
  rw [smul_eq_mul]

/-- The `k`-th derivative of `logDeriv Γ_ℝ` is the Hurwitz-type series
`(-1)^{k+1} k! Σ_n (1/(s+2n))^{k+1}`. -/
lemma invGammaR_iteratedDeriv_logDeriv_gen (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re) :
    iteratedDeriv k (logDeriv Complex.Gammaℝ) s
      = (-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ)
        * (∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1)) := by
  have hk0 : 0 < k := hk
  have hs2 : 0 < (s / 2).re := by rw [Complex.div_re]; simp; linarith
  have hev : logDeriv Complex.Gammaℝ =ᶠ[𝓝 s]
      fun z : ℂ => (-(Complex.log (Real.pi : ℂ)) / 2) + (1 / 2) * Complex.digamma (z / 2) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    have hz2 : ∀ m : ℕ, z / 2 ≠ -((m : ℕ) : ℂ) := by
      intro m h
      have hre : (z / 2).re = -((m : ℝ)) := by rw [h]; simp
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hzre : 0 < (z / 2).re := by rw [Complex.div_re]; simp; linarith
      linarith only [hre, hm, hzre]
    rw [Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole z hz2]
    ring
  rw [hev.iteratedDeriv_eq k]
  rw [iteratedDeriv_const_add hk0]
  rw [iteratedDeriv_const_mul_field]
  rw [invGammaR_digamma_div_two k hs]
  set T : ℂ := ∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1) with hT
  have hHas := Work.LinnikAreas.FarRepel.digammaDerivSeries k hk hs2
  have hterm : ∀ n : ℕ, (1 / (s / 2 + (n : ℂ))) ^ (k + 1)
      = (2 : ℂ) ^ (k + 1) * (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1) := by
    intro n
    have hden : s / 2 + (n : ℂ) = (s + ((2 * n : ℕ) : ℂ)) / 2 := by push_cast; ring
    rw [hden, div_div_eq_mul_div, one_mul,
      show (2 : ℂ) / (s + ((2 * n : ℕ) : ℂ)) = 2 * (1 / (s + ((2 * n : ℕ) : ℂ))) by ring,
      mul_pow]
  have hHas' : HasSum (fun n : ℕ =>
      ((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ) * (2 : ℂ) ^ (k + 1))
        * (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1))
      (iteratedDeriv k Complex.digamma (s / 2)) :=
    hHas.congr_fun (fun n => by rw [hterm n]; ring)
  have hval : iteratedDeriv k Complex.digamma (s / 2)
      = ((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ) * (2 : ℂ) ^ (k + 1)) * T := by
    rw [← hHas'.tsum_eq, tsum_mul_left]
  rw [hval]
  have hpow : (1 / 2 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (k + 1) = 1 := by
    rw [← mul_pow]; norm_num
  have hkey : (1 / 2 : ℂ) * ((1 / 2) ^ k * (((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ)
        * (2 : ℂ) ^ (k + 1)) * T))
      = ((1 / 2 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (k + 1))
          * ((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ) * T) := by
    rw [pow_succ]; ring
  rw [hkey, hpow, one_mul]

/-- The `k`-th derivative of `logDeriv (Γ_ℝ (· + a))⁻¹` in terms of the trivial-zero series. -/
lemma invGammaR_iteratedDeriv_logDeriv_invGamma (a : ℕ) (k : ℕ) (hk : 1 ≤ k) {t : ℂ}
    (ht : 1 < t.re) :
    iteratedDeriv k (logDeriv (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹)) t =
      (-1 : ℂ) ^ k * (k.factorial : ℂ)
        * (∑' n : ℕ, (t + (a : ℂ) + 2 * (n : ℂ)) ^ (-(k + 1) : ℤ)) := by
  have ht0 : 0 < (t + (a : ℂ)).re := by
    have hre : (t + (a : ℂ)).re = t.re + (a : ℝ) := by simp [Complex.add_re]
    have h2 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    linarith
  have hev1 : logDeriv (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) =ᶠ[𝓝 t]
      fun z => -logDeriv (fun z : ℂ => Complex.Gammaℝ (z + a)) z := by
    have hop : IsOpen {z : ℂ | 0 < (z + (a : ℂ)).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.add continuous_const)
    filter_upwards [hop.mem_nhds ht0] with z hz
    have hne : Complex.Gammaℝ (z + (a : ℂ)) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hz
    have hdg : DifferentiableAt ℂ (fun z : ℂ => Complex.Gammaℝ (z + (a : ℂ))) z :=
      (invGammaR_differentiableAt_of_re_pos hz).comp z (differentiableAt_id.add_const _)
    have hdf : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) (Complex.Gammaℝ (z + (a : ℂ))) := by
      fun_prop (disch := exact hne)
    have hcomp := logDeriv_comp (f := fun w : ℂ => w⁻¹)
      (g := fun z : ℂ => Complex.Gammaℝ (z + (a : ℂ))) (x := z) hdf hdg
    rw [show (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹)
        = ((fun w : ℂ => w⁻¹) ∘ fun z : ℂ => Complex.Gammaℝ (z + (a : ℂ))) from rfl]
    rw [hcomp, logDeriv_inv, logDeriv_apply]
    field_simp
  have hev3 : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + a))
      = (fun z : ℂ => logDeriv Complex.Gammaℝ (z + (a : ℂ))) := by
    funext z
    show deriv (fun z : ℂ => Complex.Gammaℝ (z + (a : ℂ))) z / Complex.Gammaℝ (z + (a : ℂ))
        = deriv Complex.Gammaℝ (z + (a : ℂ)) / Complex.Gammaℝ (z + (a : ℂ))
    rw [deriv_comp_add_const]
  rw [hev1.iteratedDeriv_eq k]
  rw [iteratedDeriv_fun_neg]
  rw [hev3]
  have hcomp2 : iteratedDeriv k (fun z : ℂ => logDeriv Complex.Gammaℝ (z + (a : ℂ))) t
      = iteratedDeriv k (logDeriv Complex.Gammaℝ) (t + (a : ℂ)) := by
    have h := congrFun (iteratedDeriv_comp_add_const k (logDeriv Complex.Gammaℝ) (a : ℂ)) t
    simpa using h
  rw [hcomp2, invGammaR_iteratedDeriv_logDeriv_gen k hk ht0]
  have hser : (∑' n : ℕ, (1 / ((t + (a : ℂ)) + ((2 * n : ℕ) : ℂ))) ^ (k + 1))
      = ∑' n : ℕ, (t + (a : ℂ) + 2 * (n : ℂ)) ^ (-(k + 1) : ℤ) :=
    tsum_congr (fun n => invGammaR_one_div_two_mul (t + (a : ℂ)) k n)
  rw [hser]
  have hsign : (-1 : ℂ) ^ (k + 1) = -(-1 : ℂ) ^ k := by rw [pow_succ]; ring
  rw [hsign]; ring

end

theorem invGammaRZeroSum (a : ℕ) (ha : a = 0 ∨ a = 1) (k : ℕ) (hk : 1 ≤ k) {t : ℂ}
    (ht : 1 < t.re) :
    Summable (fun u : ℂ =>
        ((analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) u : ℕ) : ℂ)
          * (t - u) ^ (-(k + 1) : ℤ)) ∧
      iteratedDeriv k (logDeriv (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹)) t =
        (-1 : ℂ) ^ k * (k.factorial : ℂ)
          * Work.LinnikAreas.TuranOther.zeroSumK (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) t k := by
  obtain ⟨hsum, hzs⟩ := invGammaR_zeroSum_eq a k hk ht
  refine ⟨hsum, ?_⟩
  rw [invGammaR_iteratedDeriv_logDeriv_invGamma a k hk ht, hzs]

end Work.LinnikAreas.TuranOther
