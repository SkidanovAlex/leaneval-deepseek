import Mathlib
import Submission.Work.KMTAreas.A7.gProfile_deriv_bounds
import Submission.Work.KMTAreas.A7.gScale_arith
import Submission.Work.KMTAreas.A7.gScale_lacunary_sum
import Submission.Work.KMTAreas.A7.randSymbG_d0
import Submission.Work.KMTAreas.A7.randSymbG_window
import Submission.Work.KMTAreas.A7.abs_PevalR_mul_le

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.deprecated false

namespace Work.KMTAreas.A7

open Finset Polynomial
open scoped BigOperators

noncomputable section

/-! ## The Mikhlin bound for the randomised `g`-side symbol

The helper estimates (`rSG_norm_ee`, `rSG_deriv_modulatedBump_p`, `rSG_abel_sum_bound`,
`rSG_bump_bounds`, ...) live in `Submission.Work.KMTAreas.A7.randSymbG_prep`.
-/

/-! ## The main auxiliary estimate -/

/-- **The `d ≥ 1` case of the Mikhlin bound for the randomised `g`-side symbol.**  The arithmetic
input (`hSum`) and the profile bounds (`hprof`) are supplied as explicit hypotheses, so that this
statement is independent of the auxiliary files that supply them. -/
private theorem mikhlin_aux
    (P : Polynomial ℤ) (d : ℕ) (hd1 : 1 ≤ d) (hdP : P.natDegree ≤ d) (Λ : NNReal) (hΛ : 1 < Λ)
    (M0 M1 M2 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hbd0 : ∀ k₂ : ℕ, ∀ u : ℝ, ‖gProfile d k₂ u‖ ≤ M0)
    (hbd1 : ∀ k₂ : ℕ, ∀ u : ℝ, ‖deriv (gProfile d k₂) u‖ ≤ M1)
    (hbd2 : ∀ k₂ : ℕ, ∀ u : ℝ, ‖iteratedDeriv 2 (gProfile d k₂) u‖ ≤ M2)
    (hv0 : ∀ k₂ : ℕ, ∀ u : ℝ, 1 ≤ |u| → gProfile d k₂ u = 0)
    (hv1 : ∀ k₂ : ℕ, ∀ u : ℝ, 1 ≤ |u| → deriv (gProfile d k₂) u = 0)
    (hv2 : ∀ k₂ : ℕ, ∀ u : ℝ, 1 ≤ |u| → iteratedDeriv 2 (gProfile d k₂) u = 0)
    (hdv0 : ∀ k₂ : ℕ, ∀ u : ℝ, HasDerivAt (gProfile d k₂) (deriv (gProfile d k₂) u) u)
    (hdv1 : ∀ k₂ : ℕ, ∀ u : ℝ,
      HasDerivAt (deriv (gProfile d k₂)) (iteratedDeriv 2 (gProfile d k₂) u) u)
    (hScalePos : ∀ N k₂ : ℕ, 0 < gScale d N k₂)
    (hScaleMono : ∀ N N' k₂ : ℕ, N ≤ N' → gScale d N k₂ ≤ gScale d N' k₂)
    (hScaleFac : ∀ N k₂ : ℕ, gScale d N k₂ = gScale d N 0 * (2 : ℝ) ^ (-((d * k₂ : ℕ) : ℤ)))
    (hScalePow : ∀ N k₂ : ℕ, (N : ℝ) ^ d ≤ (2 : ℝ) ^ d * (2 : ℝ) ^ (d * k₂) * gScale d N k₂)
    (Csum : ℝ) (hCsum : 0 ≤ Csum)
    (hSum : ∀ (a : ℕ → NNReal), PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      ∀ (c : ℝ) (L : ℕ), ∑ m ∈ Finset.range L,
        (if c * gScale d (Nat.floor (a m)) 0 ≤ 1 then c * gScale d (Nat.floor (a m)) 0 else 0)
          ≤ Csum) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (a : ℕ → NNReal)
        (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (K : ℕ) (c : ℕ → ℂ) (hc : ∀ u v : ℕ, ‖∑ m ∈ Finset.Icc u v, c m‖ ≤ 4),
        MikhlinBound (fun ξ : ℝ => ∑ m ∈ Finset.range (K + 1),
            c m * varphitildeNt P d (Nat.floor (a m)) k₂ t ξ)
          (C * (1 + (2 : ℝ) ^ (d * k₂)) ^ 2) := by
  classical
  set cP : ℝ := ∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)| with hcP
  have hcPnn : 0 ≤ cP := by rw [hcP]; exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  set Sq : ℝ := M0 + M1 + M2 + 1 with hSq
  have hSqnn : 0 ≤ Sq := by rw [hSq]; linarith
  set P1 : ℝ := cP + 1 with hP1
  set A2 : ℝ := (2 : ℝ) ^ (2 * d) + 1 with hA2
  set CS : ℝ := Csum + 1 with hCS
  set Cst : ℝ := (10 : ℝ) ^ 16 * Sq * P1 ^ 4 * A2 ^ 4 * CS ^ 4 with hCst
  have hCstnn : 0 ≤ Cst := by rw [hCst]; positivity
  refine ⟨Cst, hCstnn, ?_⟩
  intro k₂ t ht a ha ha1 K c hc
  set sig : ℕ → ℝ := fun m => gScale d (Nat.floor (a m)) k₂ with hsig
  set lam : ℕ → ℝ := fun m => PevalR P ((Nat.floor (a m) : ℝ) * t) with hlam
  have ha_lt : ∀ m : ℕ, a m < a (m + 1) := by
    intro m
    have hpos : (0 : NNReal) < a m := lt_of_lt_of_le zero_lt_one (ha1 m)
    have h1 : (Λ : NNReal) * a m < (a (m + 1) / a m) * a m :=
      mul_lt_mul_of_pos_right (ha m) hpos
    rw [div_mul_cancel₀ _ hpos.ne'] at h1
    calc a m = 1 * a m := (one_mul _).symm
      _ < Λ * a m := mul_lt_mul_of_pos_right hΛ hpos
      _ < a (m + 1) := h1
  have hNmono : ∀ m : ℕ, Nat.floor (a m) ≤ Nat.floor (a (m + 1)) :=
    fun m => Nat.floor_mono (le_of_lt (ha_lt m))
  have hsigmono : ∀ m : ℕ, sig m ≤ sig (m + 1) := by
    intro m
    simp only [hsig]
    exact hScaleMono _ _ k₂ (hNmono m)
  have hsigpos : ∀ m : ℕ, 0 < sig m := by
    intro m; simp only [hsig]; exact hScalePos _ k₂
  have hNpos : ∀ m : ℕ, 1 ≤ Nat.floor (a m) := by
    intro m
    have h1 : (1 : NNReal) ≤ a m := ha1 m
    have h2 : Nat.floor (1 : NNReal) ≤ Nat.floor (a m) := Nat.floor_mono h1
    simpa using h2
  have htabs : |t| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
  have hlam_bound : ∀ m : ℕ, |lam m| ≤ cP * (1 + (Nat.floor (a m) : ℝ)) ^ P.natDegree := by
    intro m
    simp only [hlam, hcP]
    exact abs_PevalR_mul_le P (Nat.floor (a m)) (t := t) htabs
  have hlam_bound2 : ∀ m : ℕ, |lam m| ≤ cP * (2 : ℝ) ^ d * ((Nat.floor (a m) : ℝ)) ^ d := by
    intro m
    refine (hlam_bound m).trans ?_
    have hN1 : (1 : ℝ) ≤ (Nat.floor (a m) : ℝ) := by exact_mod_cast hNpos m
    have h2 : (1 + (Nat.floor (a m) : ℝ)) ≤ 2 * (Nat.floor (a m) : ℝ) := by linarith
    have h3 : (1 + (Nat.floor (a m) : ℝ)) ^ P.natDegree
        ≤ (2 * (Nat.floor (a m) : ℝ)) ^ P.natDegree :=
      pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + (Nat.floor (a m) : ℝ)) h2 _
    have h4 : (2 * (Nat.floor (a m) : ℝ)) ^ P.natDegree
        ≤ (2 * (Nat.floor (a m) : ℝ)) ^ d :=
      pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 2 * (Nat.floor (a m) : ℝ)) hdP
    calc cP * (1 + (Nat.floor (a m) : ℝ)) ^ P.natDegree
        ≤ cP * (2 * (Nat.floor (a m) : ℝ)) ^ P.natDegree :=
          mul_le_mul_of_nonneg_left h3 hcPnn
      _ ≤ cP * (2 * (Nat.floor (a m) : ℝ)) ^ d := mul_le_mul_of_nonneg_left h4 hcPnn
      _ = cP * (2 : ℝ) ^ d * ((Nat.floor (a m) : ℝ)) ^ d := by rw [mul_pow]; ring
  have hlam_bound3 : ∀ m : ℕ, |lam m| ≤ cP * (2 : ℝ) ^ (2 * d) * (2 : ℝ) ^ (d * k₂) * sig m := by
    intro m
    refine (hlam_bound2 m).trans ?_
    have h3 : (Nat.floor (a m) : ℝ) ^ d ≤ (2 : ℝ) ^ d * (2 : ℝ) ^ (d * k₂) * sig m := by
      have := hScalePow (Nat.floor (a m)) k₂
      simpa only [hsig] using this
    calc cP * (2 : ℝ) ^ d * (Nat.floor (a m) : ℝ) ^ d
        ≤ cP * (2 : ℝ) ^ d * ((2 : ℝ) ^ d * (2 : ℝ) ^ (d * k₂) * sig m) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = cP * (2 : ℝ) ^ (2 * d) * (2 : ℝ) ^ (d * k₂) * sig m := by
          have h2d : (2 : ℝ) ^ d * (2 : ℝ) ^ d = (2 : ℝ) ^ (2 * d) := by
            rw [← pow_add]; congr 1; omega
          rw [← h2d]; ring
  set K2 : ℝ := cP * (2 : ℝ) ^ (2 * d) * (2 : ℝ) ^ (d * k₂) with hK2
  have hK2nn : 0 ≤ K2 := by
    rw [hK2]
    exact mul_nonneg (mul_nonneg hcPnn (by positivity)) (by positivity)
  set T : ℝ := 1 + (2 : ℝ) ^ (d * k₂) with hT
  have hT1 : (1 : ℝ) ≤ T := by rw [hT]; exact le_add_of_nonneg_right (by positivity)
  have hglip : ∀ x y : ℝ, ‖gProfile d k₂ x - gProfile d k₂ y‖ ≤ M1 * |x - y| := by
    intro x y
    have hdiff : ∀ z ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ (gProfile d k₂) z :=
      fun z _ => (hdv0 k₂ z).differentiableAt
    have hbd : ∀ z ∈ (Set.univ : Set ℝ), ‖deriv (gProfile d k₂) z‖ ≤ M1 := fun z _ => hbd1 k₂ z
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := gProfile d k₂) (s := Set.univ)
      (x := y) (y := x) hdiff hbd convex_univ (Set.mem_univ y) (Set.mem_univ x)
    rwa [Real.norm_eq_abs] at h
  have hrangeIcc : ∀ v : ℕ, Finset.range (v + 1) = Finset.Icc 0 v := by
    intro v
    ext m
    simp only [Finset.mem_range, Finset.mem_Icc]
    omega
  have hcrange : ∀ v : ℕ, ‖∑ m ∈ Finset.range (v + 1), c m‖ ≤ 4 := by
    intro v; rw [hrangeIcc v]; exact hc 0 v
  set L : ℝ := Sq * (K2 + 1) ^ 2 * 4 * 10 ^ 6 with hL
  have hLnn : 0 ≤ L := by rw [hL]; positivity
  have hKsq1 : (1 : ℝ) ≤ (K2 + 1) ^ 2 := by nlinarith [hK2nn]
  have hK2sq : K2 ≤ (K2 + 1) ^ 2 := by nlinarith
  have hK2sq2 : K2 ^ 2 ≤ (K2 + 1) ^ 2 := by nlinarith
  have hM0S : M0 ≤ Sq := by rw [hSq]; linarith
  have hM1S : M1 ≤ Sq := by rw [hSq]; linarith
  have hM2S : M2 ≤ Sq := by rw [hSq]; linarith
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hpi0 : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hSqKnn : (0 : ℝ) ≤ Sq * (K2 + 1) ^ 2 := mul_nonneg hSqnn (by positivity)
  have hquarter : Sq * (K2 + 1) ^ 2 ≤ L / 4 := by
    rw [hL, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    nlinarith [hSqKnn]
  have hSQ4 : Sq ≤ L / 4 :=
    le_trans (le_mul_of_one_le_right hSqnn hKsq1) hquarter
  have hQ : ∀ a b : ℝ, 0 ≤ a → a ≤ Sq → 0 ≤ b → b ≤ (K2 + 1) ^ 2 → a * b * 200 ≤ L / 4 := by
    intro a b ha0 ha hb0 hb
    have h1 : a * b ≤ Sq * (K2 + 1) ^ 2 := mul_le_mul ha hb hb0 hSqnn
    have h2 : Sq * (K2 + 1) ^ 2 * 200 ≤ L / 4 := by
      rw [hL, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      nlinarith [hSqKnn]
    calc a * b * 200 ≤ Sq * (K2 + 1) ^ 2 * 200 := mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ ≤ L / 4 := h2
  have hLM0 : M0 ≤ L := le_trans (le_trans hM0S hSQ4) (by linarith [hLnn])
  have hLM1 : M1 ≤ L := le_trans (le_trans hM1S hSQ4) (by linarith [hLnn])
  have hLM2 : M2 ≤ L := le_trans (le_trans hM2S hSQ4) (by linarith [hLnn])
  have hpi200 : 2 * Real.pi ≤ 200 := by linarith [hpi4]
  have hpi200' : 4 * Real.pi ≤ 200 := by linarith [hpi4, hpi0]
  have hpi200'' : 4 * Real.pi ^ 2 ≤ 200 := by nlinarith [hpi4, hpi0]
  have hfac1 : ∀ (c a b : ℝ), 0 ≤ c → c ≤ 200 → 0 ≤ a → a ≤ Sq → 0 ≤ b → b ≤ (K2 + 1) ^ 2 →
      c * a * b ≤ L / 4 := by
    intro c a b hc0 hc ha0 ha hb0 hb
    calc c * a * b = a * b * c := by ring
      _ ≤ a * b * 200 := mul_le_mul_of_nonneg_left hc (by positivity)
      _ ≤ L / 4 := hQ a b ha0 ha hb0 hb
  have hc1L : M0 + M1 + 2 * Real.pi * K2 * M0 ≤ L := by
    have h0 : M0 ≤ L / 4 := le_trans hM0S hSQ4
    have h1 : M1 ≤ L / 4 := le_trans hM1S hSQ4
    have h2 : 2 * Real.pi * K2 * M0 ≤ L / 4 := by
      have h3 : 2 * Real.pi * K2 * M0 = (2 * Real.pi) * M0 * K2 := by ring
      rw [h3]
      exact hfac1 (2 * Real.pi) M0 K2 (by positivity) hpi200 hM0 hM0S hK2nn hK2sq
    linarith
  have hc2L : M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0) ≤ L := by
    have h1 : M2 ≤ L / 4 := le_trans hM2S hSQ4
    have h2 : 4 * Real.pi * (K2 * M1) ≤ L / 4 := by
      have h3 : 4 * Real.pi * (K2 * M1) = (4 * Real.pi) * M1 * K2 := by ring
      rw [h3]
      exact hfac1 (4 * Real.pi) M1 K2 (by positivity) hpi200' hM1 hM1S hK2nn hK2sq
    have h3 : 4 * Real.pi ^ 2 * (K2 ^ 2 * M0) ≤ L / 4 := by
      have h4 : 4 * Real.pi ^ 2 * (K2 ^ 2 * M0) = (4 * Real.pi ^ 2) * M0 * (K2 ^ 2) := by ring
      rw [h4]
      exact hfac1 (4 * Real.pi ^ 2) M0 (K2 ^ 2) (by positivity) hpi200'' hM0 hM0S
        (pow_nonneg hK2nn 2) hK2sq2
    linarith
  have hP1_1 : (1 : ℝ) ≤ P1 := by rw [hP1]; linarith
  have hA2_1 : (1 : ℝ) ≤ A2 := by
    rw [hA2]
    have h : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * d) := one_le_pow₀ (by norm_num)
    linarith
  have hCS_1 : (1 : ℝ) ≤ CS := by rw [hCS]; linarith
  have hK2le : K2 + 1 ≤ P1 * A2 * T := by
    rw [hK2, hP1, hA2, hT]
    have hp1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * d) := one_le_pow₀ (by norm_num)
    have hp2 : (1 : ℝ) ≤ (2 : ℝ) ^ (d * k₂) := one_le_pow₀ (by norm_num)
    have hpn : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * d) := by positivity
    have hpn2 : (0 : ℝ) ≤ (2 : ℝ) ^ (d * k₂) := by positivity
    nlinarith [hcPnn, hp1, hp2, hpn, hpn2]
  have hLfinal : 16 * L * CS ≤ Cst * T ^ 2 := by
    have hK2sq' : (K2 + 1) ^ 2 ≤ (P1 * A2 * T) ^ 2 := pow_le_pow_left₀ (by linarith) hK2le 2
    have h1 : Sq * (K2 + 1) ^ 2 * 4 * 10 ^ 6 ≤ Sq * (P1 * A2 * T) ^ 2 * 4 * 10 ^ 6 := by
      have h1a : Sq * (K2 + 1) ^ 2 ≤ Sq * (P1 * A2 * T) ^ 2 :=
        mul_le_mul_of_nonneg_left hK2sq' hSqnn
      calc Sq * (K2 + 1) ^ 2 * 4 * 10 ^ 6 = (Sq * (K2 + 1) ^ 2) * (4 * 10 ^ 6) := by ring
        _ ≤ (Sq * (P1 * A2 * T) ^ 2) * (4 * 10 ^ 6) :=
            mul_le_mul_of_nonneg_right h1a (by norm_num)
        _ = Sq * (P1 * A2 * T) ^ 2 * 4 * 10 ^ 6 := by ring
    have h2 : 16 * (Sq * (K2 + 1) ^ 2 * 4 * 10 ^ 6) * CS
        ≤ 16 * (Sq * (P1 * A2 * T) ^ 2 * 4 * 10 ^ 6) * CS :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 16))
        (by linarith [hCS_1])
    have hb1 : (1 : ℝ) ≤ P1 ^ 2 * A2 ^ 2 * CS ^ 3 := by
      have hp : (1 : ℝ) ≤ P1 ^ 2 := one_le_pow₀ hP1_1
      have ha : (1 : ℝ) ≤ A2 ^ 2 := one_le_pow₀ hA2_1
      have hc : (1 : ℝ) ≤ CS ^ 3 := one_le_pow₀ hCS_1
      have h2 : (1 : ℝ) * 1 ≤ P1 ^ 2 * A2 ^ 2 :=
        mul_le_mul hp ha (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ P1 ^ 2)
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ P1 ^ 2 * A2 ^ 2 * CS ^ 3 :=
            mul_le_mul h2 hc (by norm_num : (0 : ℝ) ≤ 1)
              (by positivity : (0 : ℝ) ≤ P1 ^ 2 * A2 ^ 2)
    have hb2 : 64 * 10 ^ 6 ≤ (10 : ℝ) ^ 16 * (P1 ^ 2 * A2 ^ 2 * CS ^ 3) := by
      have h10 : (64 : ℝ) * 10 ^ 6 ≤ (10 : ℝ) ^ 16 := by norm_num
      calc 64 * 10 ^ 6 ≤ (10 : ℝ) ^ 16 := h10
        _ ≤ (10 : ℝ) ^ 16 * (P1 ^ 2 * A2 ^ 2 * CS ^ 3) :=
            le_mul_of_one_le_right (by norm_num) hb1
    have hb3 : 16 * (Sq * (P1 * A2 * T) ^ 2 * 4 * 10 ^ 6) * CS
        ≤ (10 : ℝ) ^ 16 * (Sq * (P1 * A2 * T) ^ 2 * CS) * (P1 ^ 2 * A2 ^ 2 * CS ^ 3) := by
      have hQ : (0 : ℝ) ≤ Sq * (P1 * A2 * T) ^ 2 * CS := by positivity
      calc 16 * (Sq * (P1 * A2 * T) ^ 2 * 4 * 10 ^ 6) * CS
          = (64 * 10 ^ 6) * (Sq * (P1 * A2 * T) ^ 2 * CS) := by ring
        _ ≤ ((10 : ℝ) ^ 16 * (P1 ^ 2 * A2 ^ 2 * CS ^ 3)) * (Sq * (P1 * A2 * T) ^ 2 * CS) :=
            mul_le_mul_of_nonneg_right hb2 hQ
        _ = (10 : ℝ) ^ 16 * (Sq * (P1 * A2 * T) ^ 2 * CS) * (P1 ^ 2 * A2 ^ 2 * CS ^ 3) := by ring
    calc 16 * L * CS = 16 * (Sq * (K2 + 1) ^ 2 * 4 * 10 ^ 6) * CS := by rw [hL]
      _ ≤ 16 * (Sq * (P1 * A2 * T) ^ 2 * 4 * 10 ^ 6) * CS := h2
      _ ≤ (10 : ℝ) ^ 16 * (Sq * (P1 * A2 * T) ^ 2 * CS) * (P1 ^ 2 * A2 ^ 2 * CS ^ 3) := hb3
      _ = Cst * T ^ 2 := by rw [hCst]; ring

  have hsumw : ∀ ξ : ℝ, ∑ i ∈ Finset.range K,
      (sig i * |ξ| + sig (i + 1) * |ξ|) * (if sig (i + 1) * |ξ| ≤ 1 then (1 : ℝ) else 0)
        ≤ 2 * Csum := by
    intro ξ
    set w : ℕ → ℝ := fun m => sig m * |ξ| with hw
    have hw_def : ∀ m : ℕ, w m = sig m * |ξ| := fun m => by rw [hw]
    set χ : ℕ → ℝ := fun m => if w m ≤ 1 then 1 else 0 with hχ
    have hχ_def : ∀ m : ℕ, χ m = if w m ≤ 1 then 1 else 0 := fun m => by rw [hχ]
    show ∑ i ∈ Finset.range K, (w i + w (i + 1)) * χ (i + 1) ≤ 2 * Csum
    have hwnn : ∀ m : ℕ, 0 ≤ w m := by
      intro m; rw [hw_def m]; exact mul_nonneg (le_of_lt (hsigpos m)) (abs_nonneg ξ)
    have hwmono : ∀ m : ℕ, w m ≤ w (m + 1) := by
      intro m; rw [hw_def m, hw_def (m + 1)]
      exact mul_le_mul_of_nonneg_right (hsigmono m) (abs_nonneg ξ)
    have hχ01 : ∀ m : ℕ, χ m = 0 ∨ χ m = 1 := by
      intro m
      by_cases h : w m ≤ 1
      · right; rw [hχ_def m]; exact if_pos h
      · left; rw [hχ_def m]; exact if_neg h
    have hχnn : ∀ m : ℕ, 0 ≤ χ m := by
      intro m; rw [hχ_def m]; split <;> norm_num
    have hχle : ∀ m : ℕ, χ m ≤ 1 := by
      intro m; rw [hχ_def m]; split <;> norm_num
    have hχ1w : ∀ m : ℕ, χ m = 1 → w m ≤ 1 := by
      intro m h
      by_contra hc
      rw [hχ_def m, if_neg hc] at h
      exact zero_ne_one h
    have hχ0w : ∀ m : ℕ, χ m = 0 → 1 < w m := by
      intro m h
      by_contra hc
      push_neg at hc
      rw [hχ_def m, if_pos hc] at h
      exact one_ne_zero h
    have hχmono : ∀ m : ℕ, χ (m + 1) ≤ χ m := by
      intro m
      by_cases h : w (m + 1) ≤ 1
      · have h2 : χ (m + 1) = 1 := by rw [hχ_def (m + 1)]; exact if_pos h
        rw [h2]
        have h3 : χ m = 1 := by
          rw [hχ_def m]; exact if_pos (le_trans (hwmono m) h)
        rw [h3]
      · have h2 : χ (m + 1) = 0 := by rw [hχ_def (m + 1)]; exact if_neg h
        rw [h2]; exact hχnn m
    have h1 : ∑ i ∈ Finset.range K, (w i + w (i + 1)) * χ (i + 1)
        ≤ ∑ i ∈ Finset.range K, (w i * χ i + w (i + 1) * χ (i + 1)) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      calc (w i + w (i + 1)) * χ (i + 1)
          = w i * χ (i + 1) + w (i + 1) * χ (i + 1) := by ring
        _ ≤ w i * χ i + w (i + 1) * χ (i + 1) := by
            refine add_le_add ?_ le_rfl
            exact mul_le_mul_of_nonneg_left (hχmono i) (hwnn i)
    have h2 : ∑ i ∈ Finset.range K, (w i * χ i + w (i + 1) * χ (i + 1))
        = ∑ i ∈ Finset.range K, w i * χ i + ∑ i ∈ Finset.range K, w (i + 1) * χ (i + 1) :=
      Finset.sum_add_distrib
    have h4 : ∑ i ∈ Finset.range K, w (i + 1) * χ (i + 1)
        ≤ ∑ j ∈ Finset.range (K + 1), w j * χ j := by
      have h5 : ∑ j ∈ Finset.range (K + 1), w j * χ j
          = ∑ j ∈ Finset.range K, w (j + 1) * χ (j + 1) + w 0 * χ 0 := by
        rw [Finset.sum_range_succ']
      rw [h5]
      have h6 : 0 ≤ w 0 * χ 0 := mul_nonneg (hwnn 0) (hχnn 0)
      linarith
    have h7 : ∑ j ∈ Finset.range (K + 1), w j * χ j ≤ Csum := by
      have h8 : ∀ j : ℕ, w j * χ j
          = (if (2 : ℝ) ^ (-((d * k₂ : ℕ) : ℤ)) * |ξ| * gScale d (Nat.floor (a j)) 0 ≤ 1
              then (2 : ℝ) ^ (-((d * k₂ : ℕ) : ℤ)) * |ξ| * gScale d (Nat.floor (a j)) 0
              else 0) := by
        intro j
        have hwq : w j
            = (2 : ℝ) ^ (-((d * k₂ : ℕ) : ℤ)) * |ξ| * gScale d (Nat.floor (a j)) 0 := by
          rw [hw_def j]
          simp only [hsig]
          rw [hScaleFac (Nat.floor (a j)) k₂]
          ring
        rw [hwq, hχ_def j]
        simp only [hwq]
        by_cases h : (2 : ℝ) ^ (-((d * k₂ : ℕ) : ℤ)) * |ξ| * gScale d (Nat.floor (a j)) 0 ≤ 1
        · simp [h]
        · simp [h]
      rw [Finset.sum_congr rfl (fun j _ => h8 j)]
      exact hSum a ha ha1 ((2 : ℝ) ^ (-((d * k₂ : ℕ) : ℤ)) * |ξ|) (K + 1)
    have h9 : ∑ i ∈ Finset.range K, w i * χ i ≤ ∑ j ∈ Finset.range (K + 1), w j * χ j := by
      have h10 : ∑ j ∈ Finset.range (K + 1), w j * χ j
          = ∑ j ∈ Finset.range K, w j * χ j + w K * χ K := by
        rw [Finset.sum_range_succ]
      rw [h10]
      have h11 : 0 ≤ w K * χ K := mul_nonneg (hwnn K) (hχnn K)
      linarith
    calc ∑ i ∈ Finset.range K, (w i + w (i + 1)) * χ (i + 1)
        ≤ ∑ i ∈ Finset.range K, (w i * χ i + w (i + 1) * χ (i + 1)) := h1
      _ = ∑ i ∈ Finset.range K, w i * χ i + ∑ i ∈ Finset.range K, w (i + 1) * χ (i + 1) := h2
      _ ≤ ∑ j ∈ Finset.range (K + 1), w j * χ j + ∑ j ∈ Finset.range (K + 1), w j * χ j :=
          add_le_add h9 h4
      _ ≤ Csum + Csum := add_le_add h7 h7
      _ = 2 * Csum := by ring
  have hlam2 : ∀ (m : ℕ) (ξ : ℝ), |ξ| * |lam m| ≤ K2 * (sig m * |ξ|) := by
    intro m ξ
    have h1 := hlam_bound3 m
    calc |ξ| * |lam m| ≤ |ξ| * (cP * (2 : ℝ) ^ (2 * d) * (2 : ℝ) ^ (d * k₂) * sig m) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg ξ)
      _ = K2 * (sig m * |ξ|) := by rw [hK2]; ring
  have hlam3 : ∀ (m : ℕ) (ξ : ℝ),
      |ξ| * |lam (m + 1) - lam m| ≤ K2 * (sig m * |ξ| + sig (m + 1) * |ξ|) := by
    intro m ξ
    have h1 : |lam (m + 1) - lam m| ≤ |lam (m + 1)| + |lam m| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (lam (m + 1)), le_abs_self (lam m)]
      · linarith [le_abs_self (lam (m + 1)), neg_le_abs (lam m)]
    have h2 := hlam_bound3 (m + 1)
    have h3 := hlam_bound3 m
    calc |ξ| * |lam (m + 1) - lam m| ≤ |ξ| * (|lam (m + 1)| + |lam m|) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg ξ)
      _ ≤ |ξ| * (cP * (2 : ℝ) ^ (2 * d) * (2 : ℝ) ^ (d * k₂) * sig (m + 1)
            + cP * (2 : ℝ) ^ (2 * d) * (2 : ℝ) ^ (d * k₂) * sig m) :=
          mul_le_mul_of_nonneg_left (add_le_add h2 h3) (abs_nonneg ξ)
      _ = K2 * (sig m * |ξ| + sig (m + 1) * |ξ|) := by rw [hK2]; ring
  have hpt : ∀ (m : ℕ) (x : ℝ), varphitildeNt P d (Nat.floor (a m)) k₂ t x
      = gProfile d k₂ (sig m * x) * ee (lam m * x) := by
    intro m x
    rw [varphitildeNt_eq_profile]
  have hsym : (fun ξ : ℝ => ∑ m ∈ Finset.range (K + 1),
        c m * varphitildeNt P d (Nat.floor (a m)) k₂ t ξ)
      = fun x : ℝ => ∑ m ∈ Finset.range (K + 1),
          c m * (gProfile d k₂ (sig m * x) * ee (lam m * x)) := by
    funext ξ
    exact Finset.sum_congr rfl (fun m _ => by rw [hpt m ξ])
  have hLfinal' : 16 * L * (Csum + 1) ≤ Cst * T ^ 2 := by
    simpa only [hCS] using hLfinal
  have hwin := rSG_window (g := gProfile d k₂) (sig := sig) (lam := lam) (K2 := K2) (K := K)
    (c := c) (Csum := Csum) (L := L) hM0 hM1 hM2 (fun u => hbd0 k₂ u) (fun u => hbd1 k₂ u)
    (fun u => hbd2 k₂ u) (fun u => hv0 k₂ u) (fun u => hv1 k₂ u) (fun u => hv2 k₂ u)
    (fun u => hdv0 k₂ u) (fun u => hdv1 k₂ u) hglip hsigpos hsigmono hK2nn hcrange
    hlam2 hlam3 hCsum hsumw hLnn hc1L hc2L Real.pi_pos.le
  rw [hsym]
  exact ⟨mul_nonneg hCstnn (sq_nonneg T), fun ξ => (hwin ξ).1.trans hLfinal',
    fun ξ => (hwin ξ).2.1.trans hLfinal', fun ξ => (hwin ξ).2.2.trans hLfinal'⟩

/-! ## The target theorem -/

theorem randSymbG_mikhlin (P : Polynomial ℤ) (d : ℕ) (hd : P.natDegree ≤ d) (Λ : NNReal)
    (hΛ : 1 < Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (a : ℕ → NNReal)
        (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (K : ℕ) (c : ℕ → ℂ) (hc : ∀ u v : ℕ, ‖∑ m ∈ Finset.Icc u v, c m‖ ≤ 4),
        MikhlinBound (fun ξ : ℝ => ∑ m ∈ Finset.range (K + 1),
            c m * varphitildeNt P d (Nat.floor (a m)) k₂ t ξ)
          (C * (1 + (2 : ℝ) ^ (d * k₂)) ^ 2) := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    exact rSG_d0 P hd Λ hΛ
  · obtain ⟨M0, M1, M2, hM0, hM1, hM2, hprof⟩ := gProfile_deriv_bounds d
    obtain ⟨hSpos, hSmono, hSfac, hSpow⟩ := gScale_arith d
    obtain ⟨Csum, hCsum, hSum⟩ := gScale_lacunary_sum d hdpos Λ hΛ
    obtain ⟨C, hC, hfin⟩ := mikhlin_aux P d hdpos hd Λ hΛ M0 M1 M2 hM0 hM1 hM2
      (fun k₂ u => (hprof k₂).2.1 u) (fun k₂ u => (hprof k₂).2.2.1 u)
      (fun k₂ u => (hprof k₂).2.2.2.1 u) (fun k₂ u => (hprof k₂).2.2.2.2.1 u)
      (fun k₂ u => (hprof k₂).2.2.2.2.2.1 u) (fun k₂ u => (hprof k₂).2.2.2.2.2.2.1 u)
      (fun k₂ u => (hprof k₂).2.2.2.2.2.2.2.1 u) (fun k₂ u => (hprof k₂).2.2.2.2.2.2.2.2 u)
      hSpos hSmono hSfac hSpow Csum hCsum hSum
    exact ⟨C, hC, hfin⟩

end

end Work.KMTAreas.A7
