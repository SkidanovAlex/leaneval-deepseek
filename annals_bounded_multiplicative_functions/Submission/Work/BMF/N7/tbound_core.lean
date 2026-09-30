import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.VKdenom
import Submission.Work.BMF.primeSum_mangoldt_le
import Submission.Work.BMF.prime_exp_sum_arith
import Submission.Work.BMF.N7.vk_interface

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The prime exponential sum bound of N7, wired to the fleet's Vinogradov–Korobov chain

`Work.BMF.zeta_prime_sum_twist` (node **V6** of the lead's `N10` chain, DESIGN.md Addendum
"V0 exponent") supplies the twisted von Mangoldt asymptotic for `ζ`:

`Σ_{n ≤ x} Λ(n) n^{-iu} = x^{1-iu}/(1-iu) + O(x exp(−c (log x)^{1/12}))`, uniformly for
`|u| ≤ exp((log x)^{21/20})`, `x ≥ 2`.

This file turns that into the *prime exponential sum bound* consumed by N7 (`mixing_count`):
for `P ≥ P₀` and `|η| ≤ exp((log P)^{21/20})/(2π)`,

`‖Σ_{P ≤ p ≤ 2P} p^{2πiη}‖ ≤ K π₀(P) (1/(1+|η|) + 1/log P)`.

The derivation (interval form of the twisted asymptotic, Abel summation of the von Mangoldt
weight, and absorption of the error) is the same one as in
`Submission.Work.BMF.prime_exp_sum_bound`; only the deep input differs — the local "ppsb"
Vinogradov–Korobov subtree there is replaced by the lead's V6, so that N7 does not duplicate the
fleet's `V0 → … → V4 → V6` chain.
-/

namespace Work.BMF

open Polynomial Filter
open scoped Topology

noncomputable section

/-! ## Absorption of the VK error term -/

/-- For every `c > 0` and `β > 0`, a fixed power of `log` is eventually swallowed by
`exp(−c (log P)^β)`. -/
lemma log_exp_neg_rpow_le_one (c : ℝ) (hc : 0 < c) (β : ℝ) (hβ : 0 < β) :
    ∃ P₀ : ℝ, 2 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      Real.log P * Real.exp (-c * Real.log P ^ β) ≤ 1 := by
  have h1β : (0 : ℝ) < 1 / β := by positivity
  have hbase : Tendsto (fun P : ℝ => Real.log P ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp Real.tendsto_log_atTop
  have hcomp : Tendsto (fun P : ℝ => (Real.log P ^ β) ^ (1 / β) *
      Real.exp (-c * Real.log P ^ β)) atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / β) c hc).comp hbase
  have hEq : (fun P : ℝ => (Real.log P ^ β) ^ (1 / β) * Real.exp (-c * Real.log P ^ β))
      =ᶠ[atTop] (fun P : ℝ => Real.log P * Real.exp (-c * Real.log P ^ β)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with P hP
    have hlog : 0 ≤ Real.log P := Real.log_nonneg hP
    rw [← Real.rpow_mul hlog β (1 / β), mul_one_div, div_self (ne_of_gt hβ), Real.rpow_one]
  have hlim : Tendsto (fun P : ℝ => Real.log P * Real.exp (-c * Real.log P ^ β)) atTop (𝓝 0) :=
    Tendsto.congr' hEq hcomp
  have hev : ∀ᶠ P : ℝ in atTop, Real.log P * Real.exp (-c * Real.log P ^ β) ≤ 1 :=
    (hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun P hP => le_of_lt hP)
  obtain ⟨P₁, hP₁⟩ := eventually_atTop.mp hev
  exact ⟨max P₁ 2, le_max_right _ _, fun P hP => hP₁ P (le_trans (le_max_left _ _) hP)⟩

/-- The five elementary asymptotic facts of `prime_exp_sum_arith`, but with the error exponent
`1/12` (the exponent delivered by V6). -/
lemma log_exp_neg_rpow_p12_arith (c : ℝ) (hc : 0 < c) :
    ∃ P₀ : ℝ, 2 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      Real.log P * Real.exp (-c * Real.log P ^ (1 / 12 : ℝ)) ≤ 1 ∧
      Real.sqrt P * (Real.log P) ^ 3 ≤ P ∧
      1 ≤ P / (Real.log P) ^ 2 ∧
      Real.log (2 * P) ≤ 2 * Real.log P ∧
      4 ≤ P := by
  obtain ⟨Q₀, hQ₀, hQ⟩ := prime_exp_sum_arith c hc
  obtain ⟨R₀, hR₀, hR⟩ := log_exp_neg_rpow_le_one c hc (1 / 12) (by norm_num)
  refine ⟨max Q₀ R₀, le_trans hQ₀ (le_max_left _ _), fun P hP => ?_⟩
  obtain ⟨-, h2, h3, h4, h5⟩ := hQ P (le_trans (le_max_left _ _) hP)
  exact ⟨hR P (le_trans (le_max_right _ _) hP), h2, h3, h4, h5⟩



lemma mtb_cpow_twist_eq_eC (n : ℕ) (hn : 1 ≤ n) (η : ℝ) :
    (n : ℂ) ^ (-(Complex.I * (-(2 * Real.pi * η)))) = eC (η * Real.log n) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    have : 0 < n := by omega
    exact_mod_cast (Nat.pos_iff_ne_zero.mp this)
  rw [Complex.cpow_def_of_ne_zero hn0]
  rw [show Complex.log (n : ℂ) = (Real.log n : ℂ) by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp]
    rw [← Complex.ofReal_log (Nat.cast_nonneg n)]]
  rw [eC]
  congr 1
  push_cast
  ring

lemma mtb_norm_cpow_twist (n : ℕ) (hn : 1 ≤ n) (u : ℝ) :
    ‖(n : ℂ) ^ (-(Complex.I * u))‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

lemma mtb_sum_Ioc_eq_sub (f : ℕ → ℂ) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc a b, f n = ∑ n ∈ Finset.Icc 1 b, f n - ∑ n ∈ Finset.Icc 1 a, f n := by
  have hsub : Finset.Icc 1 a ⊆ Finset.Icc 1 b := Finset.Icc_subset_Icc_right hab
  have hdiff : Finset.Icc 1 b \ Finset.Icc 1 a = Finset.Ioc a b := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have h := Finset.sum_sdiff hsub (f := f)
  rw [hdiff] at h
  exact eq_sub_iff_add_eq.mpr h

lemma mtb_norm_one_sub_I_mul_ge (η : ℝ) :
    (1 + |η|) / 2 ≤ ‖(1 : ℂ) - Complex.I * (((-(2 * Real.pi * η)) : ℝ) : ℂ)‖ := by
  have heq : (1 : ℂ) - Complex.I * (((-(2 * Real.pi * η)) : ℝ) : ℂ)
      = 1 + Complex.I * (((2 * Real.pi * η) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq]
  have hre : (1 + Complex.I * (((2 * Real.pi * η) : ℝ) : ℂ)).re = 1 := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have him : (1 + Complex.I * (((2 * Real.pi * η) : ℝ) : ℂ)).im = 2 * Real.pi * η := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  have h1 : (1 : ℝ) ≤ ‖(1 + Complex.I * (((2 * Real.pi * η) : ℝ) : ℂ))‖ := by
    have := Complex.abs_re_le_norm (1 + Complex.I * (((2 * Real.pi * η) : ℝ) : ℂ))
    rw [hre] at this
    simpa using this
  have h2 : |2 * Real.pi * η| ≤ ‖(1 + Complex.I * (((2 * Real.pi * η) : ℝ) : ℂ))‖ := by
    have := Complex.abs_im_le_norm (1 + Complex.I * (((2 * Real.pi * η) : ℝ) : ℂ))
    rw [him] at this
    simpa using this
  have hmax : (1 + |η|) / 2 ≤ max 1 |2 * Real.pi * η| := by
    by_cases h : 1 ≤ |η|
    · have hle : |η| ≤ |2 * Real.pi * η| := by
        rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        nlinarith [abs_nonneg η, Real.pi_gt_three]
      have : (1 + |η|) / 2 ≤ |η| := by nlinarith
      exact le_trans this (le_trans hle (le_max_right _ _))
    · have h' : |η| < 1 := not_le.mp h
      have : (1 + |η|) / 2 ≤ 1 := by nlinarith
      exact le_trans this (le_max_left _ _)
  exact le_trans hmax (max_le h1 h2)

/-- **The Vinogradov–Korobov twisted von Mangoldt asymptotic** (N10 with `q = 1`, `χ = 1`),
the single deep analytic input consumed by `prime_exp_sum_bound_of`: for `x ≥ 3` and
`|u| ≤ exp((log x)^{21/20})`,
`‖Σ_{n ≤ x} Λ(n) n^{-iu} − x^{1-iu}/(1-iu)‖ ≤ C x exp(−c (log x)^{1/12})`. -/
def TwistedLambdaVK12 : Prop :=
  ∃ c C : ℝ, 0 < c ∧ ∀ x : ℝ, 3 ≤ x → ∀ u : ℝ,
    |u| ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ)) →
    ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u)))
      - (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖
      ≤ C * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))

/-- **Prime exponential sum bound**, from the twisted von Mangoldt asymptotic. -/
theorem mixing_tbound_of (hVK : TwistedLambdaVK12) :
    ∃ K P₀ : ℝ, 0 < K ∧ ∀ (P η : ℝ), P₀ ≤ P →
      |η| ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)) / (2 * Real.pi) →
      ‖∑ p ∈ primesIn P (2 * P), eC (η * Real.log p)‖ ≤
        K * pi0 P * (1 / (1 + |η|) + 1 / Real.log P) := by
  obtain ⟨cvk, Cvk, hcvk, hvk⟩ := hVK
  obtain ⟨Ccmp, Pcmp, hCcmp, hcmp⟩ := primeSum_mangoldt_le
  obtain ⟨Par, hPar2, har⟩ := log_exp_neg_rpow_p12_arith cvk hcvk
  have hCcmp0 : 0 ≤ Ccmp := le_of_lt hCcmp
  set Cv : ℝ := max Cvk 1 with hCvdef
  have hCv1 : (1:ℝ) ≤ Cv := le_max_right _ _
  have hCv0 : 0 < Cv := lt_of_lt_of_le zero_lt_one hCv1
  have hCvk_le : Cvk ≤ Cv := le_max_left _ _
  have hKpos : 0 < max 6 (3*Ccmp + 3*Cv) + 1 := by
    have h1 : (6:ℝ) ≤ max 6 (3*Ccmp + 3*Cv) := le_max_left _ _
    linarith
  refine ⟨max 6 (3*Ccmp + 3*Cv) + 1, max 10 (max Par Pcmp) + 1, hKpos, ?_⟩
  intro P η hPle hη
  have hP10 : (10:ℝ) ≤ P := by
    have h1 : (10:ℝ) ≤ max 10 (max Par Pcmp) := le_max_left _ _
    linarith
  have hPar_le : Par ≤ P := by
    have h1 : Par ≤ max 10 (max Par Pcmp) :=
      le_trans (le_max_left Par Pcmp) (le_max_right (10:ℝ) (max Par Pcmp))
    linarith
  have hPcmp_le : Pcmp ≤ P := by
    have h1 : Pcmp ≤ max 10 (max Par Pcmp) :=
      le_trans (le_max_right Par Pcmp) (le_max_right (10:ℝ) (max Par Pcmp))
    linarith
  have hPpos : (0:ℝ) < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlogP1 : (1:ℝ) ≤ Real.log P :=
    (Real.le_log_iff_exp_le hPpos).mpr (by nlinarith [Real.exp_one_lt_d9])
  have hlog2P_ge : Real.log P ≤ Real.log (2*P) := Real.log_le_log hPpos (by linarith)
  have hmodP : (1:ℝ) ≤ Real.log P := hlogP1
  have hmod2P : (1:ℝ) ≤ Real.log (2*P) := le_trans hlogP1 hlog2P_ge
  obtain ⟨har1, har2, har3, har4, har5⟩ := har P hPar_le
  set u : ℝ := -(2 * Real.pi * η) with hudef
  have hS : (∑ p ∈ primesIn P (2 * P), eC (η * Real.log p))
      = ∑ p ∈ primesIn P (2 * P), (p : ℂ) ^ (-(Complex.I * u)) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hpprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hp1 : 1 ≤ p := hpprime.one_le
    rw [hudef]
    rw [show (((-(2 * Real.pi * η)) : ℝ) : ℂ) = -(2 * (Real.pi : ℂ) * (η : ℂ)) by
      push_cast; ring]
    exact (mtb_cpow_twist_eq_eC p hp1 η).symm
  rw [hS]
  have huP : |u| ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)) := by
    rw [hudef]
    have h1 : |-(2 * Real.pi * η)| = 2 * Real.pi * |η| := by
      rw [abs_neg, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
        abs_of_pos (by norm_num : (0:ℝ) < (2:ℝ))]
    rw [h1]
    calc 2 * Real.pi * |η|
        ≤ 2 * Real.pi * (Real.exp (Real.log P ^ (21 / 20 : ℝ)) / (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hη (by positivity)
      _ = Real.exp (Real.log P ^ (21 / 20 : ℝ)) := by field_simp
  have hu2P : |u| ≤ Real.exp (Real.log (2 * P) ^ (21 / 20 : ℝ)) := by
    refine le_trans huP ?_
    apply Real.exp_le_exp.mpr
    exact Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlog2P_ge (by norm_num)
  have hvk1 : ∀ (x : ℝ) (u : ℝ), 3 ≤ x →
      |u| ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ)) →
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))
        - (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖
        ≤ Cv * (x * Real.exp (-cvk * Real.log x ^ (1 / 12 : ℝ))) := by
    intro x u hx3 hu
    have h := hvk x hx3 u hu
    refine le_trans h ?_
    calc Cvk * x * Real.exp (-cvk * Real.log x ^ (1 / 12 : ℝ))
        = Cvk * (x * Real.exp (-cvk * Real.log x ^ (1 / 12 : ℝ))) := by ring
      _ ≤ Cv * (x * Real.exp (-cvk * Real.log x ^ (1 / 12 : ℝ))) :=
          mul_le_mul_of_nonneg_right hCvk_le (by positivity)
  have hvk2P := hvk1 (2*P) u (by linarith) hu2P
  have hvkP := hvk1 P u (by linarith) huP
  have hexp_re : (1 - Complex.I * (u : ℂ)).re = 1 := by
    rw [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      Complex.ofReal_re, Complex.one_re]
    ring
  have hun2 : ‖(((2 * P : ℝ)) : ℂ) ^ (1 - Complex.I * u)‖ = 2*P := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), hexp_re, Real.rpow_one]
  have hunP : ‖(((P : ℝ)) : ℂ) ^ (1 - Complex.I * u)‖ = P := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hPpos, hexp_re, Real.rpow_one]
  have hden : (1 + |η|)/2 ≤ ‖(1 : ℂ) - Complex.I * (u : ℂ)‖ := by
    rw [hudef]; exact mtb_norm_one_sub_I_mul_ge η
  have hdpos : 0 < ‖(1 : ℂ) - Complex.I * (u : ℂ)‖ := by
    have h0 : 0 < (1 + |η|)/2 := by positivity
    linarith
  have hmain : ‖(((2 * P : ℝ)) : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)
      - (((P : ℝ)) : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖ ≤ 6 * P / (1 + |η|) := by
    have hnum : ‖(((2 * P : ℝ)) : ℂ) ^ (1 - Complex.I * u)
        - (((P : ℝ)) : ℂ) ^ (1 - Complex.I * u)‖ ≤ 2*P + P := by
      refine (norm_sub_le _ _).trans ?_
      rw [hun2, hunP]
    rw [← sub_div, norm_div]
    calc ‖(((2 * P : ℝ)) : ℂ) ^ (1 - Complex.I * u)
            - (((P : ℝ)) : ℂ) ^ (1 - Complex.I * u)‖
          / ‖(1 : ℂ) - Complex.I * (u : ℂ)‖
        ≤ (2*P + P) / ‖(1 : ℂ) - Complex.I * (u : ℂ)‖ := div_le_div_of_nonneg_right hnum hdpos.le
      _ = 3*P / ‖(1 : ℂ) - Complex.I * (u : ℂ)‖ := by ring
      _ ≤ 3*P / ((1 + |η|)/2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 6*P / (1 + |η|) := by field_simp <;> ring
  have hIoc : ∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))
      = (∑ n ∈ Finset.Icc 1 ⌊2 * P⌋₊,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u)))
        - (∑ n ∈ Finset.Icc 1 ⌊P⌋₊,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))) := by
    refine mtb_sum_Ioc_eq_sub _ ?_ ?_
    · exact (Nat.one_le_floor_iff P).mpr (by linarith)
    · exact Nat.floor_mono (by linarith)
  have hT : ‖∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))‖
      ≤ Cv * ((2*P) * Real.exp (-cvk * Real.log (2*P) ^ (1 / 12 : ℝ)))
        + Cv * (P * Real.exp (-cvk * Real.log P ^ (1 / 12 : ℝ)))
        + 6 * P / (1 + |η|) := by
    set A : ℂ := ∑ n ∈ Finset.Icc 1 ⌊2 * P⌋₊,
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u)) with hA
    set B : ℂ := ∑ n ∈ Finset.Icc 1 ⌊P⌋₊,
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u)) with hB
    set M2 : ℂ := (((2 * P : ℝ)) : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u) with hM2
    set M1 : ℂ := (((P : ℝ)) : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u) with hM1
    rw [hIoc]
    have hab : A - B = (A - M2) + (M2 - M1) + (M1 - B) := by ring
    have hA2 : ‖A - M2‖ ≤ Cv * ((2*P) * Real.exp (-cvk * Real.log (2*P) ^ (1 / 12 : ℝ))) := by
      rw [hA, hM2]; exact hvk2P
    have hB1 : ‖M1 - B‖ ≤ Cv * (P * Real.exp (-cvk * Real.log P ^ (1 / 12 : ℝ))) := by
      rw [hM1, hB, norm_sub_rev]; exact hvkP
    have hAB2 : ‖M2 - M1‖ ≤ 6 * P / (1 + |η|) := by
      rw [hM2, hM1]; exact hmain
    rw [hab]
    have h1 : ‖(A - M2) + (M2 - M1) + (M1 - B)‖ ≤ ‖(A - M2) + (M2 - M1)‖ + ‖M1 - B‖ :=
      norm_add_le _ _
    have h2 : ‖(A - M2) + (M2 - M1)‖ ≤ ‖A - M2‖ + ‖M2 - M1‖ := norm_add_le _ _
    linarith
  have hcmpP := hcmp P u hPcmp_le
  have hnorm : ‖(1 / Real.log P) * (∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u)))‖
      = (1 / Real.log P) * ‖∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))‖ := by
    rw [norm_mul]
    congr 1
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogP.le]
  have hE2 : Real.exp (-cvk * Real.log (2*P) ^ (1 / 12 : ℝ))
      ≤ Real.exp (-cvk * Real.log P ^ (1 / 12 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h3 : Real.log P ^ (1 / 12 : ℝ) ≤ Real.log (2*P) ^ (1 / 12 : ℝ) :=
      Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlog2P_ge (by norm_num)
    rw [neg_mul, neg_mul]
    exact neg_le_neg (mul_le_mul_of_nonneg_left h3 hcvk.le)
  have hE1log : Real.exp (-cvk * Real.log P ^ (1 / 12 : ℝ)) ≤ 1 / Real.log P := by
    rw [le_div_iff₀ hlogP]
    linarith [har1]
  have hE2log : Real.exp (-cvk * Real.log (2*P) ^ (1 / 12 : ℝ)) ≤ 1 / Real.log P :=
    le_trans hE2 hE1log
  have hbound : (1 / Real.log P) * ‖∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))‖
      ≤ (2*Ccmp + 3*Cv) * P / (Real.log P)^2 + 6 * P / ((1 + |η|) * Real.log P) := by
    have h2P : Cv * ((2*P) * Real.exp (-cvk * Real.log (2*P) ^ (1/12:ℝ))) ≤ Cv*((2*P)*(1/Real.log P)) := by
      apply mul_le_mul_of_nonneg_left _ hCv0.le
      exact mul_le_mul_of_nonneg_left hE2log (by positivity)
    have hP : Cv * (P * Real.exp (-cvk * Real.log P ^ (1/12:ℝ))) ≤ Cv*(P*(1/Real.log P)) := by
      apply mul_le_mul_of_nonneg_left _ hCv0.le
      exact mul_le_mul_of_nonneg_left hE1log (by positivity)
    have hstep : ‖∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))‖
        ≤ 3*Cv*P*(1/Real.log P) + 6*P/(1+|η|) := by
      have e2 : Cv*((2*P)*(1/Real.log P)) + Cv*(P*(1/Real.log P)) = 3*Cv*P*(1/Real.log P) := by ring
      calc ‖∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))‖
          ≤ Cv * ((2*P) * Real.exp (-cvk * Real.log (2*P) ^ (1 / 12 : ℝ)))
            + Cv * (P * Real.exp (-cvk * Real.log P ^ (1 / 12 : ℝ)))
            + 6 * P / (1 + |η|) := hT
        _ ≤ Cv*((2*P)*(1/Real.log P)) + Cv*(P*(1/Real.log P)) + 6*P/(1+|η|) := by
            exact add_le_add (add_le_add h2P hP) (le_refl _)
        _ = 3*Cv*P*(1/Real.log P) + 6*P/(1+|η|) := by rw [e2]
    have h1 : 3*Cv*P*(1/Real.log P)*(1/Real.log P) = 3*Cv*P/(Real.log P)^2 := by
      field_simp
    have h2 : (1/Real.log P) * (6*P/(1+|η|)) = 6*P/((1+|η|)*Real.log P) := by
      field_simp
    calc (1 / Real.log P) * ‖∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))‖
        ≤ (1 / Real.log P) * (3*Cv*P*(1/Real.log P) + 6*P/(1+|η|)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 3*Cv*P*(1/Real.log P)*(1/Real.log P) + (1/Real.log P)*(6*P/(1+|η|)) := by ring
      _ = 3*Cv*P/(Real.log P)^2 + 6*P/((1+|η|)*Real.log P) := by rw [h1, h2]
      _ ≤ (2*Ccmp + 3*Cv) * P / (Real.log P)^2 + 6 * P / ((1 + |η|) * Real.log P) := by
          apply add_le_add
          · apply div_le_div_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ hPpos.le
            linarith [hCcmp0]
          · exact le_refl _
  have hfin : ‖∑ p ∈ primesIn P (2 * P), (p : ℂ) ^ (-(Complex.I * u))‖
      ≤ (3*Ccmp + 3*Cv) * P / (Real.log P)^2 + 6 * P / ((1 + |η|) * Real.log P) := by
    have htri : ‖∑ p ∈ primesIn P (2 * P), (p : ℂ) ^ (-(Complex.I * u))‖
        ≤ ‖(∑ p ∈ primesIn P (2 * P), (p : ℂ) ^ (-(Complex.I * u)))
            - ((1 / Real.log P) * ∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2*P⌋₊,
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u)))‖
          + ‖(1 / Real.log P) * ∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2*P⌋₊,
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))‖ := by
      have h := norm_add_le ((∑ p ∈ primesIn P (2 * P), (p : ℂ) ^ (-(Complex.I * u)))
            - ((1 / Real.log P) * ∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2*P⌋₊,
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))))
          ((1 / Real.log P) * ∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2*P⌋₊,
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u)))
      have heq : ((∑ p ∈ primesIn P (2 * P), (p : ℂ) ^ (-(Complex.I * u)))
            - ((1 / Real.log P) * ∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2*P⌋₊,
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))))
          + ((1 / Real.log P) * ∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2*P⌋₊,
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u)))
          = ∑ p ∈ primesIn P (2 * P), (p : ℂ) ^ (-(Complex.I * u)) := by ring
      rw [heq] at h
      exact h
    rw [hnorm] at htri
    have h2 : (1 / Real.log P) * ‖∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))‖
        ≤ (2*Ccmp + 3*Cv) * P / (Real.log P)^2 + 6 * P / ((1 + |η|) * Real.log P) := hbound
    have hsum : Ccmp * P / (Real.log P)^2 + ((2*Ccmp + 3*Cv) * P / (Real.log P)^2
        + 6 * P / ((1 + |η|) * Real.log P))
        = (3*Ccmp + 3*Cv) * P / (Real.log P)^2 + 6 * P / ((1 + |η|) * Real.log P) := by ring
    exact (le_trans htri (add_le_add hcmpP h2)).trans (le_of_eq hsum)
  have hpi0nn : 0 ≤ pi0 P := by rw [pi0]; positivity
  have hlogne : Real.log P ≠ 0 := ne_of_gt hlogP
  have hAeq : (3*Ccmp + 3*Cv) * P / (Real.log P)^2 = (3*Ccmp + 3*Cv) * (pi0 P / Real.log P) := by
    rw [pi0]; field_simp
  have hBeq : 6 * P / ((1 + |η|) * Real.log P) = 6 * (pi0 P / (1 + |η|)) := by
    rw [pi0]; field_simp
  have hK6 : (6:ℝ) ≤ max 6 (3*Ccmp + 3*Cv) + 1 := by
    linarith [le_max_left (6:ℝ) (3*Ccmp + 3*Cv)]
  have hKC : 3*Ccmp + 3*Cv ≤ max 6 (3*Ccmp + 3*Cv) + 1 := by
    linarith [le_max_right (6:ℝ) (3*Ccmp + 3*Cv)]
  calc ‖∑ p ∈ primesIn P (2 * P), (p : ℂ) ^ (-(Complex.I * u))‖
      ≤ (3*Ccmp + 3*Cv) * P / (Real.log P)^2 + 6 * P / ((1 + |η|) * Real.log P) := hfin
    _ = (3*Ccmp + 3*Cv) * (pi0 P / Real.log P) + 6 * (pi0 P / (1 + |η|)) := by
        rw [hAeq, hBeq]
    _ ≤ (max 6 (3*Ccmp + 3*Cv) + 1) * (pi0 P / Real.log P)
          + (max 6 (3*Ccmp + 3*Cv) + 1) * (pi0 P / (1 + |η|)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hKC (div_nonneg hpi0nn hlogP.le)
        · exact mul_le_mul_of_nonneg_right hK6 (div_nonneg hpi0nn (by positivity))
    _ = (max 6 (3*Ccmp + 3*Cv) + 1) * pi0 P * (1 / (1 + |η|) + 1 / Real.log P) := by ring

/-- **Prime exponential sum bound** (the input of N7). For `P ≥ P₀` and
`|η| ≤ exp((log P)^{21/20})/(2π)`,
`‖Σ_{P ≤ p ≤ 2P} p^{2πiη}‖ ≤ K π₀(P) (1/(1+|η|) + 1/log P)`, where `π₀(P) = P/log P`. -/
theorem prime_exp_sum_bound_21_of (hVK : TwistedLambdaVK12) :
    ∃ K P₀ : ℝ, 0 < K ∧ ∀ (P η : ℝ), P₀ ≤ P →
      |η| ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)) / (2 * Real.pi) →
      ‖∑ p ∈ primesIn P (2 * P), eC (η * Real.log p)‖ ≤
        K * pi0 P * (1 / (1 + |η|) + 1 / Real.log P) :=
  mixing_tbound_of hVK

end

end Work.BMF
