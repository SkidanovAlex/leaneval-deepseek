import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sieve_remainder_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_hdens_cubefree_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_gdens_cubefree_prod_le_final
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold
import Submission.Commons.Analysis.Integral.integral_sqrt_one_sub_pow_four_ge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Hypothesis (R) for `X² + Y⁴`

This file proves the companion-paper hypothesis `(R)` for the Friedlander–Iwaniec
sequence, inlining the relevant workspace development (`Submission/S3g.lean`,
`Submission/ASP_R.lean`) because a commons module may import only Mathlib and other
commons modules.  All the ingredients used are already in the commons:

* `Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sieve_remainder_le`
  (the inlined §3 development of the main paper), which supplies the definitions
  `Ad`, `gdens`, `Aseq`, the asymptotic formula (3.18) `Aseq_asymptotic`, Lemma 3.4
  `Md_cubefree_asymptotic_uniform`, and the sieve remainder bound
  `X2Y4_sieve_remainder_le` (i.e. the paper's (3.3));
* the polylogarithmic summatory bounds for the local-density factors,
  `sum_hdens_cubefree_le` and `sum_gdens_cubefree_prod_le_final`.
-/

namespace Submission.X2Y4R

open Finset

/-- The condition selecting the cubefree moduli `d = d₁ d₂² ≤ D` with `4 ∤ d`. -/
def cubeCond (D d₁ d₂ : ℕ) : Prop :=
  Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧
    ¬ 4 ∣ d₁ * d₂ ^ 2 ∧ d₁ * d₂ ^ 2 ≤ D

instance (D d₁ d₂ : ℕ) : Decidable (cubeCond D d₁ d₂) := by
  unfold cubeCond; infer_instance

/-- `∑^{♭}_{d ≤ D} G` summed over the cubefree moduli `d = d₁ · d₂ ^ 2 ≤ D` with
`d₁`, `d₂` squarefree and coprime and `4 ∤ d`; the summand is `G d₁ d₂`. -/
noncomputable def cubeSum (D : ℕ) (G : ℕ → ℕ → ℝ) : ℝ :=
  ∑ d₁ ∈ Finset.Icc 1 D, ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt D),
    if cubeCond D d₁ d₂ then G d₁ d₂ else 0

lemma cubeSum_le (D : ℕ) {G G' : ℕ → ℕ → ℝ}
    (h : ∀ a b, (if cubeCond D a b then G a b else 0)
      ≤ (if cubeCond D a b then G' a b else 0)) :
    cubeSum D G ≤ cubeSum D G' := by
  unfold cubeSum
  exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => h a b

lemma cubeSum_add (D : ℕ) (G G' : ℕ → ℕ → ℝ) :
    cubeSum D (fun a b => G a b + G' a b) = cubeSum D G + cubeSum D G' := by
  unfold cubeSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hc : cubeCond D a b <;> simp [hc]

lemma cubeSum_const_mul (D : ℕ) (c : ℝ) (G : ℕ → ℕ → ℝ) :
    cubeSum D (fun a b => c * G a b) = c * cubeSum D G := by
  unfold cubeSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hc : cubeCond D a b <;> simp [hc]

/-- `Submission.hdens` is literally the inlined commons function `hdensF`
(Lemma 3.4's error factor `h(d₁ d₂²)`). -/
lemma hdens_eq_hdensF (a b : ℕ) :
    hdens a b = Commons.NumberTheory.FriedlanderIwaniec.hdensF a b := rfl

/-- The polylogarithmic summatory bound for the error factor `h`: this is the
hypothesis `hH` of `prop35_of_inputs`, discharged by the commons lemma
`sum_hdens_cubefree_le`. -/
theorem cubeSum_hdens_le :
    ∃ C A : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y →
      cubeSum y (fun d₁ d₂ => (hdens d₁ d₂ : ℝ)) ≤ C * (Real.log y) ^ A := by
  obtain ⟨C, A, hC, h⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.sum_hdens_cubefree_le
  refine ⟨C, A, hC, fun y hy => ?_⟩
  have h1 := h y hy
  have h2 : cubeSum y (fun d₁ d₂ => (hdens d₁ d₂ : ℝ))
      = ((∑ d₁ ∈ Finset.Icc 1 y, ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y),
            if Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧ ¬ 4 ∣ d₁ * d₂ ^ 2
              ∧ d₁ * d₂ ^ 2 ≤ y
            then Commons.NumberTheory.FriedlanderIwaniec.hdensF d₁ d₂ else 0 : ℚ) : ℝ) := by
    rw [cubeSum]
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hc : cubeCond y a b
    · have hc' : Squarefree a ∧ Squarefree b ∧ Nat.Coprime a b ∧ ¬ 4 ∣ a * b ^ 2
          ∧ a * b ^ 2 ≤ y := hc
      rw [if_pos hc, if_pos hc']
      exact congrArg (fun q : ℚ => (q : ℝ)) (hdens_eq_hdensF a b)
    · have hc' : ¬(Squarefree a ∧ Squarefree b ∧ Nat.Coprime a b ∧ ¬ 4 ∣ a * b ^ 2
          ∧ a * b ^ 2 ≤ y) := hc
      simp only [if_neg hc, if_neg hc', Rat.cast_zero]
  rw [h2]
  exact h1

/-- **Proposition 3.5 of Friedlander–Iwaniec, assembled from Lemma 3.1.**

Hypotheses:
* `h33` is the paper's (3.3) in the form needed, restricted to cubefree moduli;
* `hA` is formula (3.18) and `hM` is Lemma 3.4 (3.15);
* `hH` and `hG` are the polylogarithmic summatory bounds for `h` and `g`;

Conclusion: `∑^{♭}_{d ≤ D} |A_d(t) − g(d) A(t)| ≪ D^{1/4} t^{9/16} + √t (log t)^A`. -/
theorem prop35_of_inputs
    {κ A : ℝ} (hApos : 0 ≤ A)
    (h33 : ∃ C : ℝ, 0 < C ∧ ∀ D t : ℕ, 1 ≤ D → 2 ≤ t → D ≤ ⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ →
      cubeSum D (fun d₁ d₂ => |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (Md (d₁ * d₂ ^ 2) t : ℝ)|)
        ≤ C * (D : ℝ) ^ (1 / 4 : ℝ) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100))
    (hA : ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, 2 ≤ t →
      |(Aseq t : ℝ) - 4 * κ * (t : ℝ) ^ (3 / 4 : ℝ)| ≤ C * Real.sqrt t)
    (hM : ∃ C : ℝ, 0 < C ∧ ∀ d₁ d₂ t : ℕ, Squarefree d₁ → Squarefree d₂ →
      Nat.Coprime d₁ d₂ → ¬ 4 ∣ d₁ * d₂ ^ 2 → 2 ≤ t →
      |(Md (d₁ * d₂ ^ 2) t : ℝ) - 4 * (gdens (d₁ * d₂ ^ 2) : ℝ) * κ
          * (t : ℝ) ^ (3 / 4 : ℝ)|
        ≤ C * (hdens d₁ d₂ : ℝ) * Real.sqrt t)
    (hH : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y →
      cubeSum y (fun d₁ d₂ => (hdens d₁ d₂ : ℝ)) ≤ C * (Real.log y) ^ A)
    (hG : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y →
      cubeSum y (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|) ≤ C * (Real.log y) ^ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ D t : ℕ, 2 ≤ D → 2 ≤ t → D ≤ ⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ →
      cubeSum D (fun d₁ d₂ =>
          |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (gdens (d₁ * d₂ ^ 2) : ℝ) * (Aseq t : ℝ)|)
        ≤ C * ((D : ℝ) ^ (1 / 4 : ℝ) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
            + Real.sqrt t * (Real.log ((D : ℝ) + t + 2)) ^ A) := by
  obtain ⟨c33, hc33pos, h33'⟩ := h33
  obtain ⟨cA, hcApos, hA'⟩ := hA
  obtain ⟨cM, hcMpos, hM'⟩ := hM
  obtain ⟨cH, hcHpos, hH'⟩ := hH
  obtain ⟨cG, hcGpos, hG'⟩ := hG
  refine ⟨max c33 (cM * cH + cA * cG) + 1, by positivity, ?_⟩
  intro D t hD ht hDx
  have ht1 : 1 ≤ t := by omega
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by exact_mod_cast ht1)
  have hlogA : 0 ≤ (Real.log t) ^ A := Real.rpow_nonneg hlog A
  have hspos : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  -- Step 1: pointwise comparison of the summands
  have hpt : ∀ a b : ℕ,
      (if cubeCond D a b then
        |(Ad (a * b ^ 2) t : ℝ) - (gdens (a * b ^ 2) : ℝ) * (Aseq t : ℝ)| else 0)
      ≤ (if cubeCond D a b then
          (|(Ad (a * b ^ 2) t : ℝ) - (Md (a * b ^ 2) t : ℝ)|
            + (cM * Real.sqrt t) * (hdens a b : ℝ)
            + (cA * Real.sqrt t) * |(gdens (a * b ^ 2) : ℝ)|) else 0) := by
    intro a b
    by_cases hc : cubeCond D a b
    · rw [if_pos hc, if_pos hc]
      obtain ⟨ha, hb, hab, h4, -⟩ := hc
      have hm := hM' a b t ha hb hab h4 ht
      have hAab := hA' t ht
      have e1 : |(Md (a * b ^ 2) t : ℝ)
            - 4 * (gdens (a * b ^ 2) : ℝ) * κ * (t : ℝ) ^ (3 / 4 : ℝ)|
          ≤ (cM * Real.sqrt t) * (hdens a b : ℝ) := by
        rw [show cM * (hdens a b : ℝ) * Real.sqrt t
            = (cM * Real.sqrt t) * (hdens a b : ℝ) from by ring] at hm
        exact hm
      have e2 : |4 * (gdens (a * b ^ 2) : ℝ) * κ * (t : ℝ) ^ (3 / 4 : ℝ)
            - (gdens (a * b ^ 2) : ℝ) * (Aseq t : ℝ)|
          ≤ (cA * Real.sqrt t) * |(gdens (a * b ^ 2) : ℝ)| := by
        rw [show (4 * (gdens (a * b ^ 2) : ℝ) * κ * (t : ℝ) ^ (3 / 4 : ℝ)
              - (gdens (a * b ^ 2) : ℝ) * (Aseq t : ℝ))
              = (gdens (a * b ^ 2) : ℝ)
                * (4 * κ * (t : ℝ) ^ (3 / 4 : ℝ) - (Aseq t : ℝ)) from by ring, abs_mul]
        have h4' : |4 * κ * (t : ℝ) ^ (3 / 4 : ℝ) - (Aseq t : ℝ)| ≤ cA * Real.sqrt t := by
          rw [abs_sub_comm]; exact hAab
        calc |(gdens (a * b ^ 2) : ℝ)| * |4 * κ * (t : ℝ) ^ (3 / 4 : ℝ) - (Aseq t : ℝ)|
            ≤ |(gdens (a * b ^ 2) : ℝ)| * (cA * Real.sqrt t) :=
              mul_le_mul_of_nonneg_left h4' (abs_nonneg _)
          _ = (cA * Real.sqrt t) * |(gdens (a * b ^ 2) : ℝ)| := by ring
      have htri := abs_sub_le (Ad (a * b ^ 2) t : ℝ) (Md (a * b ^ 2) t : ℝ)
        ((gdens (a * b ^ 2) : ℝ) * (Aseq t : ℝ))
      have hsplit := abs_sub_le (Md (a * b ^ 2) t : ℝ)
        (4 * (gdens (a * b ^ 2) : ℝ) * κ * (t : ℝ) ^ (3 / 4 : ℝ))
        ((gdens (a * b ^ 2) : ℝ) * (Aseq t : ℝ))
      linarith
    · simp [if_neg hc]
  -- Step 2: sum the pointwise bound
  have hsum : cubeSum D (fun d₁ d₂ =>
        |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (gdens (d₁ * d₂ ^ 2) : ℝ) * (Aseq t : ℝ)|)
      ≤ cubeSum D (fun d₁ d₂ =>
          |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (Md (d₁ * d₂ ^ 2) t : ℝ)|)
        + (cM * Real.sqrt t) * cubeSum D (fun d₁ d₂ => (hdens d₁ d₂ : ℝ))
        + (cA * Real.sqrt t) * cubeSum D (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|) := by
    have h1 := cubeSum_le D (G := fun d₁ d₂ =>
        |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (gdens (d₁ * d₂ ^ 2) : ℝ) * (Aseq t : ℝ)|)
      (G' := fun d₁ d₂ =>
        |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (Md (d₁ * d₂ ^ 2) t : ℝ)|
          + (cM * Real.sqrt t) * (hdens d₁ d₂ : ℝ)
          + (cA * Real.sqrt t) * |(gdens (d₁ * d₂ ^ 2) : ℝ)|)
      (fun a b => hpt a b)
    rw [cubeSum_add, cubeSum_add, cubeSum_const_mul, cubeSum_const_mul] at h1
    exact h1
  -- Step 3: apply the hypotheses
  have hA1 : cubeSum D (fun d₁ d₂ =>
        |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (Md (d₁ * d₂ ^ 2) t : ℝ)|)
      ≤ c33 * ((D : ℝ) ^ (1 / 4 : ℝ) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)) := by
    have h := h33' D t (by omega) ht hDx
    rw [show c33 * (D : ℝ) ^ (1 / 4 : ℝ) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
        = c33 * ((D : ℝ) ^ (1 / 4 : ℝ) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)) from by ring] at h
    exact h
  have hA2 : cubeSum D (fun d₁ d₂ => (hdens d₁ d₂ : ℝ)) ≤ cH * (Real.log D) ^ A := hH' D (by omega)
  have hA3 : cubeSum D (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|) ≤ cG * (Real.log D) ^ A :=
    hG' D (by omega)
  have hZ0 : 0 ≤ Real.log ((D : ℝ) + t + 2) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ D + t + 2))
  have hZ : 0 ≤ (Real.log ((D : ℝ) + t + 2)) ^ A := Real.rpow_nonneg hZ0 A
  have hlogD : (Real.log D) ^ A ≤ (Real.log ((D : ℝ) + t + 2)) ^ A :=
    Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ D)))
      (Real.log_le_log (by exact_mod_cast (by omega : 0 < D))
        (by nlinarith)) hApos
  have hlogt : (Real.log t) ^ A ≤ (Real.log ((D : ℝ) + t + 2)) ^ A :=
    Real.rpow_le_rpow hlog
      (Real.log_le_log (by exact_mod_cast (by omega : 0 < t)) (by nlinarith)) hApos
  have hX : 0 ≤ (D : ℝ) ^ (1 / 4 : ℝ) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) := by positivity
  have hY : 0 ≤ Real.sqrt t * (Real.log ((D : ℝ) + t + 2)) ^ A :=
    mul_nonneg (Real.sqrt_nonneg t) hZ
  have e2 : (cM * Real.sqrt t) * cubeSum D (fun d₁ d₂ => (hdens d₁ d₂ : ℝ))
      ≤ (cM * cH) * (Real.sqrt t * (Real.log ((D : ℝ) + t + 2)) ^ A) := by
    calc (cM * Real.sqrt t) * cubeSum D (fun d₁ d₂ => (hdens d₁ d₂ : ℝ))
        ≤ (cM * Real.sqrt t) * (cH * (Real.log D) ^ A) :=
          mul_le_mul_of_nonneg_left hA2 (by positivity)
      _ ≤ (cM * Real.sqrt t) * (cH * (Real.log ((D : ℝ) + t + 2)) ^ A) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogD (le_of_lt hcHpos))
            (by positivity)
      _ = (cM * cH) * (Real.sqrt t * (Real.log ((D : ℝ) + t + 2)) ^ A) := by ring
  have e3 : (cA * Real.sqrt t) * cubeSum D (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|)
      ≤ (cA * cG) * (Real.sqrt t * (Real.log ((D : ℝ) + t + 2)) ^ A) := by
    calc (cA * Real.sqrt t) * cubeSum D (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|)
        ≤ (cA * Real.sqrt t) * (cG * (Real.log D) ^ A) :=
          mul_le_mul_of_nonneg_left hA3 (by positivity)
      _ ≤ (cA * Real.sqrt t) * (cG * (Real.log ((D : ℝ) + t + 2)) ^ A) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogD (le_of_lt hcGpos))
            (by positivity)
      _ = (cA * cG) * (Real.sqrt t * (Real.log ((D : ℝ) + t + 2)) ^ A) := by ring
  have hstep : cubeSum D (fun d₁ d₂ =>
        |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (gdens (d₁ * d₂ ^ 2) : ℝ) * (Aseq t : ℝ)|)
      ≤ c33 * ((D : ℝ) ^ (1 / 4 : ℝ) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100))
        + (cM * cH + cA * cG) * (Real.sqrt t * (Real.log ((D : ℝ) + t + 2)) ^ A) := by
    calc cubeSum D (fun d₁ d₂ =>
          |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (gdens (d₁ * d₂ ^ 2) : ℝ) * (Aseq t : ℝ)|)
        ≤ cubeSum D (fun d₁ d₂ =>
            |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (Md (d₁ * d₂ ^ 2) t : ℝ)|)
          + (cM * Real.sqrt t) * cubeSum D (fun d₁ d₂ => (hdens d₁ d₂ : ℝ))
          + (cA * Real.sqrt t) * cubeSum D (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|) := hsum
      _ ≤ c33 * ((D : ℝ) ^ (1 / 4 : ℝ) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100))
          + ((cM * cH) * (Real.sqrt t * (Real.log ((D : ℝ) + t + 2)) ^ A)
            + (cA * cG) * (Real.sqrt t * (Real.log ((D : ℝ) + t + 2)) ^ A)) := by
          linarith [hA1, e2, e3]
      _ = c33 * ((D : ℝ) ^ (1 / 4 : ℝ) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100))
          + (cM * cH + cA * cG) * (Real.sqrt t * (Real.log ((D : ℝ) + t + 2)) ^ A) := by ring
  refine le_trans hstep ?_
  have h1 : c33 ≤ max c33 (cM * cH + cA * cG) + 1 := by
    have a := le_max_left c33 (cM * cH + cA * cG); linarith
  have h2 : cM * cH + cA * cG ≤ max c33 (cM * cH + cA * cG) + 1 := by
    have a := le_max_right c33 (cM * cH + cA * cG); linarith
  have hexp : (max c33 (cM * cH + cA * cG) + 1)
        * ((D : ℝ) ^ (1 / 4 : ℝ) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
          + Real.sqrt t * (Real.log ((D : ℝ) + t + 2)) ^ A)
      = (max c33 (cM * cH + cA * cG) + 1) * ((D : ℝ) ^ (1 / 4 : ℝ) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100))
        + (max c33 (cM * cH + cA * cG) + 1)
          * (Real.sqrt t * (Real.log ((D : ℝ) + t + 2)) ^ A) := by ring
  rw [hexp]
  nlinarith [mul_le_mul_of_nonneg_right h1 hX, mul_le_mul_of_nonneg_right h2 hY]

open Finset

lemma gdens_nonneg (d : ℕ) : 0 ≤ gdens d := by
  rw [gdens]; positivity

lemma gdens_cubefree_eq_prod_real {d₁ d₂ : ℕ} (hs₁ : Squarefree d₁) (hs₂ : Squarefree d₂)
    (hcop : Nat.Coprime d₁ d₂) (h4 : ¬ 4 ∣ d₁ * d₂ ^ 2) :
    (gdens (d₁ * d₂ ^ 2) : ℝ)
      = (∏ p ∈ d₁.primeFactors,
            (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + 1) / (p : ℝ) ^ 2)
        * (∏ p ∈ d₂.primeFactors,
            (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + (p : ℝ)) / (p : ℝ) ^ 3) := by
  rw [gdens_cubefree_eq_prod hs₁ hs₂ hcop h4]
  simp only [chi4]
  push_cast
  ring

theorem cubeSum_gdens_le :
    ∃ C A : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y →
      cubeSum y (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|) ≤ C * (Real.log y) ^ A := by
  obtain ⟨C, A, hC, h⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.sum_gdens_cubefree_prod_le_final
  refine ⟨C, A, hC, fun y hy => ?_⟩
  have h2 : cubeSum y (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|)
      = (∑ d₁ ∈ Finset.Icc 1 y, ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y),
          if Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧ ¬ 4 ∣ d₁ * d₂ ^ 2
            ∧ d₁ * d₂ ^ 2 ≤ y then
            (∏ p ∈ d₁.primeFactors,
                (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + 1) / (p : ℝ) ^ 2)
            * (∏ p ∈ d₂.primeFactors,
                (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + (p : ℝ))
                  / (p : ℝ) ^ 3)
          else 0) := by
    rw [cubeSum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hc : cubeCond y a b
    · have hc' : Squarefree a ∧ Squarefree b ∧ Nat.Coprime a b ∧ ¬ 4 ∣ a * b ^ 2
          ∧ a * b ^ 2 ≤ y := hc
      rw [if_pos hc, if_pos hc', abs_of_nonneg (Rat.cast_nonneg.mpr (gdens_nonneg _))]
      exact gdens_cubefree_eq_prod_real hc'.1 hc'.2.1 hc'.2.2.1 hc'.2.2.2.1
    · have hc' : ¬(Squarefree a ∧ Squarefree b ∧ Nat.Coprime a b ∧ ¬ 4 ∣ a * b ^ 2
          ∧ a * b ^ 2 ≤ y) := hc
      simp only [if_neg hc, if_neg hc']
  rw [h2]
  exact h y hy

/-- `(log y)^B ≤ (log 2)^(B-A) (log y)^A` for `B ≤ A`, `y ≥ 2`. -/
lemma rpow_log_le_const_mul {B A : ℝ} (hBA : B ≤ A) {y : ℕ} (hy : 2 ≤ y) :
    (Real.log y) ^ B ≤ (Real.log 2) ^ (B - A) * (Real.log y) ^ A := by
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hy1 : (1:ℝ) < y := by exact_mod_cast (by omega : 1 < y)
  have hy2 : (0:ℝ) < Real.log y := Real.log_pos hy1
  have hle : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) (by exact_mod_cast hy)
  have hneg : B - A ≤ 0 := by linarith
  have h1 : (Real.log y) ^ (B - A) ≤ (Real.log 2) ^ (B - A) :=
    Real.rpow_le_rpow_of_nonpos h2 hle hneg
  calc (Real.log y) ^ B = (Real.log y) ^ (B - A) * (Real.log y) ^ A := by
        rw [← Real.rpow_add hy2]
        congr 1
        ring
    _ ≤ (Real.log 2) ^ (B - A) * (Real.log y) ^ A :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hy2.le A)

/-- A polylogarithmic bound can always be written with a nonnegative exponent. -/
lemma exists_nonneg_exponent_of_polylog {F : ℕ → ℝ}
    (h : ∃ C A : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y → F y ≤ C * (Real.log y) ^ A) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ y : ℕ, 2 ≤ y → F y ≤ C * (Real.log y) ^ A := by
  obtain ⟨C, A, hC, h⟩ := h
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max C (C * (Real.log 2) ^ A), max A 0,
    lt_of_lt_of_le hC (le_max_left _ _), le_max_right _ _, fun y hy => ?_⟩
  have h2le : (2:ℝ) ≤ y := by exact_mod_cast hy
  have hlog2le : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) h2le
  have hlogpos : (0:ℝ) < Real.log y := Real.log_pos (by linarith)
  by_cases hA : A ≤ 0
  · rw [max_eq_right hA, Real.rpow_zero]
    have hlog2lt1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      linarith
    have hge1 : (1:ℝ) ≤ (Real.log 2) ^ A := Real.one_le_rpow_of_pos_of_le_one_of_nonpos h2 hlog2lt1 hA
    have hstep : (Real.log y) ^ A ≤ (Real.log 2) ^ A :=
      Real.rpow_le_rpow_of_nonpos h2 hlog2le hA
    have hCA : C * (Real.log 2) ^ A ≤ max C (C * (Real.log 2) ^ A) := le_max_right _ _
    nlinarith [hC.le, Real.rpow_pos_of_pos h2 A, hstep, hge1, h y hy]
  · rw [max_eq_left (not_le.mp hA).le]
    have hC' : C ≤ max C (C * (Real.log 2) ^ A) := le_max_left _ _
    exact le_trans (h y hy)
      (mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hlogpos.le A))

/-- The nonnegative-exponent form of `cubeSum_hdens_le`. -/
lemma cubeSum_hdens_le_nonneg :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ y : ℕ, 2 ≤ y →
      cubeSum y (fun d₁ d₂ => (hdens d₁ d₂ : ℝ)) ≤ C * (Real.log y) ^ A :=
  exists_nonneg_exponent_of_polylog cubeSum_hdens_le

lemma cubeSum_gdens_le_nonneg :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ y : ℕ, 2 ≤ y →
      cubeSum y (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|) ≤ C * (Real.log y) ^ A :=
  exists_nonneg_exponent_of_polylog cubeSum_gdens_le

/-- **Proposition 3.5** (Friedlander–Iwaniec §3) with everything but (3.3) discharged. -/
theorem prop35_of_33
    (h33 : ∃ C : ℝ, 0 < C ∧ ∀ D t : ℕ, 1 ≤ D → 2 ≤ t → D ≤ ⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ →
      cubeSum D (fun d₁ d₂ => |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (Md (d₁ * d₂ ^ 2) t : ℝ)|)
        ≤ C * (D : ℝ) ^ (1 / 4 : ℝ) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ D t : ℕ, 2 ≤ D → 2 ≤ t → D ≤ ⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ →
      cubeSum D (fun d₁ d₂ =>
          |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (gdens (d₁ * d₂ ^ 2) : ℝ) * (Aseq t : ℝ)|)
        ≤ C * ((D : ℝ) ^ (1 / 4 : ℝ) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
            + Real.sqrt t * (Real.log ((D : ℝ) + t + 2)) ^ A) := by
  obtain ⟨Ch, Ah, hCh, hAh, hHh⟩ := cubeSum_hdens_le_nonneg
  obtain ⟨Cg, Ag, hCg, hAg, hGg⟩ := cubeSum_gdens_le_nonneg
  obtain ⟨CM, hCM, hMu⟩ := Md_cubefree_asymptotic_uniform
  obtain ⟨CA, hCA, hAu⟩ := Aseq_asymptotic
  set A : ℝ := max Ah Ag with hAdef
  have hA0 : 0 ≤ A := le_trans hAh (le_max_left _ _)
  -- adjusted constants
  have hH : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y →
      cubeSum y (fun d₁ d₂ => (hdens d₁ d₂ : ℝ)) ≤ C * (Real.log y) ^ A := by
    refine ⟨Ch + Ch * (Real.log 2) ^ (Ah - A), by positivity, fun y hy => ?_⟩
    have h1 := hHh y hy
    have h2 := rpow_log_le_const_mul (A := A) (B := Ah) (le_max_left _ _) hy
    have h3 : (0:ℝ) ≤ (Real.log 2) ^ (Ah - A) := Real.rpow_nonneg (Real.log_nonneg (by norm_num)) _
    have h4 : Ch * (Real.log y) ^ Ah ≤ Ch * ((Real.log 2) ^ (Ah - A) * (Real.log y) ^ A) :=
      mul_le_mul_of_nonneg_left h2 hCh.le
    have h5 : Ch * ((Real.log 2) ^ (Ah - A) * (Real.log y) ^ A) ≤
        (Ch + Ch * (Real.log 2) ^ (Ah - A)) * (Real.log y) ^ A := by
      nlinarith [Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ y) : (1:ℝ) ≤ (y:ℝ))) A]
    linarith
  have hG : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y →
      cubeSum y (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|) ≤ C * (Real.log y) ^ A := by
    refine ⟨Cg + Cg * (Real.log 2) ^ (Ag - A), by positivity, fun y hy => ?_⟩
    have h1 := hGg y hy
    have h2 := rpow_log_le_const_mul (A := A) (B := Ag) (le_max_right _ _) hy
    have h3 : (0:ℝ) ≤ (Real.log 2) ^ (Ag - A) := Real.rpow_nonneg (Real.log_nonneg (by norm_num)) _
    have h4 : Cg * (Real.log y) ^ Ag ≤ Cg * ((Real.log 2) ^ (Ag - A) * (Real.log y) ^ A) :=
      mul_le_mul_of_nonneg_left h2 hCg.le
    have h5 : Cg * ((Real.log 2) ^ (Ag - A) * (Real.log y) ^ A) ≤
        (Cg + Cg * (Real.log 2) ^ (Ag - A)) * (Real.log y) ^ A := by
      nlinarith [Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ y) : (1:ℝ) ≤ (y:ℝ))) A]
    linarith
  obtain ⟨C, hC, h⟩ := prop35_of_inputs hA0 h33
    ⟨CA, hCA, fun t ht => hAu t (by omega)⟩
    ⟨CM, hCM, fun d₁ d₂ t hs₁ hs₂ hcop h4 ht => hMu d₁ d₂ hs₁ hs₂ hcop h4 t (by omega)⟩
    hH hG
  exact ⟨C, A, hC, hA0, h⟩


/-! ## Discharging `h33` from the commons theorem `(3.3)` -/

open Finset in
/-- `A_d(x)` is the lattice-point count with the congruence condition. -/
theorem Ad_eq_ncard (d x : ℕ) :
    Ad d x
      = ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ (d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4}).ncard := by
  rw [Ad]
  simp only [an]
  exact (ncard_eq_Ad_sum d x).symm

/-- `(log (2D+2))^6 ≤ K · D^{1/4}` for `D ≥ 1`. -/
lemma log_six_le_const_mul (D : ℕ) (hD : 1 ≤ D) :
    (Real.log (2 * (D : ℝ) + 2)) ^ 6 ≤ 27 ^ 6 * (D : ℝ) ^ ((1 : ℝ) / 4) := by
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by linarith
  have h4D : (0 : ℝ) < 4 * (D : ℝ) := by linarith
  have hle : 2 * (D : ℝ) + 2 ≤ 4 * (D : ℝ) := by linarith
  have hlog4 : Real.log (4 * (D : ℝ)) ≤ 3 + Real.log (D : ℝ) := by
    rw [Real.log_mul (by norm_num) hDpos.ne']
    have : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
      linarith
    linarith
  have hlogD : Real.log (D : ℝ) ≤ 24 * (D : ℝ) ^ ((1 : ℝ) / 24) := by
    have h := Real.log_le_rpow_div (x := (D : ℝ)) (ε := (1 : ℝ) / 24) (le_of_lt hDpos) (by norm_num)
    have hr : ((1 : ℝ) / 24) ≠ 0 := by norm_num
    calc Real.log (D : ℝ) ≤ (D : ℝ) ^ ((1:ℝ)/24) / ((1:ℝ)/24) := h
      _ = 24 * (D : ℝ) ^ ((1 : ℝ) / 24) := by field_simp
  have hpow1 : (1 : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 24) := Real.one_le_rpow hD1 (by norm_num)
  have hlog : Real.log (2 * (D : ℝ) + 2) ≤ 27 * (D : ℝ) ^ ((1 : ℝ) / 24) := by
    calc Real.log (2 * (D : ℝ) + 2) ≤ Real.log (4 * (D : ℝ)) := by
          apply Real.log_le_log (by linarith) hle
      _ ≤ 3 + Real.log (D : ℝ) := hlog4
      _ ≤ 3 + 24 * (D : ℝ) ^ ((1 : ℝ) / 24) := by linarith
      _ ≤ 27 * (D : ℝ) ^ ((1 : ℝ) / 24) := by nlinarith
  have hnn : (0 : ℝ) ≤ Real.log (2 * (D : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hp24 : (0 : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 24) := Real.rpow_nonneg (le_of_lt hDpos) _
  calc (Real.log (2 * (D : ℝ) + 2)) ^ 6
      ≤ (27 * (D : ℝ) ^ ((1 : ℝ) / 24)) ^ 6 := by
        exact pow_le_pow_left₀ hnn hlog 6
    _ = 27 ^ 6 * ((D : ℝ) ^ ((1 : ℝ) / 24)) ^ 6 := by ring
    _ = 27 ^ 6 * (D : ℝ) ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_natCast ((D : ℝ) ^ ((1 : ℝ) / 24)) 6, ← Real.rpow_mul (le_of_lt hDpos)]
        norm_num

/-- `∑_{d ≤ D} |A_d(x) − M_d(x)| ≪ D^{1/4} x^{9/16+1/100}` (`x` for the point
`t` of the paper), i.e. the paper's (3.3) in the form needed. -/
theorem Ad_sub_Md_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (x D : ℕ), 1 ≤ x → 1 ≤ D → D ≤ ⌊(x : ℝ) ^ ((3 : ℝ) / 4)⌋₊ →
      (∑ d ∈ Finset.Icc 1 D, |(Ad d x : ℝ) - (Md d x : ℝ)|)
        ≤ C * (D : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) := by
  obtain ⟨C1, hC1, h1⟩ := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sieve_remainder_le
  obtain ⟨C2, hC2, h2⟩ := Md_sub_main_term_sum_le
  refine ⟨(C1 + C2 * 27 ^ 6) * 2, by positivity, ?_⟩
  intro x D hx hD hDx
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hx0 : (0 : ℝ) < (x : ℝ) := by linarith
  have hD0 : (0 : ℝ) < (D : ℝ) := by linarith
  -- first term
  have hA : (∑ d ∈ Finset.Icc 1 D,
      |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
        - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
            ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
              2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
      ≤ C1 * (D : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((9 : ℝ) / 16) * (x : ℝ) ^ ((1 : ℝ) / 100) :=
    h1 x D hx hD hDx
  -- rewrite the first summand as `Ad d x`
  have hAre : ∀ d : ℕ, (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
      = (Ad d x : ℝ) := by
    intro d; rw [Ad_eq_ncard d x]
  simp only [hAre] at hA
  have hB : (∑ d ∈ Finset.Icc 1 D,
      |(Md d x : ℝ)
        - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
            ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
              2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
      ≤ C2 * (x : ℝ) ^ ((1 : ℝ) / 4) * (Real.log (2 * (D : ℝ) + 2)) ^ 6 := h2 x D hx hD
  -- triangle inequality, termwise
  have hsplit : (∑ d ∈ Finset.Icc 1 D, |(Ad d x : ℝ) - (Md d x : ℝ)|)
      ≤ (∑ d ∈ Finset.Icc 1 D,
          |(Ad d x : ℝ)
            - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                  2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
        + (∑ d ∈ Finset.Icc 1 D,
          |(Md d x : ℝ)
            - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                  2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun d _ => ?_
    set B : ℝ := (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                  2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ)) with hBdef
    have h1' : |(Ad d x : ℝ) - B| ≤ |(Ad d x : ℝ) - B| := le_refl _
    have := abs_sub_le (Ad d x : ℝ) B (Md d x : ℝ)
    rw [abs_sub_comm (Md d x : ℝ) B]
    linarith [abs_sub_le (Ad d x : ℝ) B (Md d x : ℝ)]
  -- the second term is bounded by `C2 * K * D^{1/4} * x^{9/16+1/100}`
  have hB2 : (∑ d ∈ Finset.Icc 1 D,
        |(Md d x : ℝ)
          - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
              ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
      ≤ C2 * 27 ^ 6 * (D : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) := by
    refine le_trans hB ?_
    have hlog := log_six_le_const_mul D hD
    have hx14 : (x : ℝ) ^ ((1 : ℝ) / 4) ≤ (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hD14 : (0 : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (le_of_lt hD0) _
    have hxv : (0 : ℝ) ≤ (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) := Real.rpow_nonneg (le_of_lt hx0) _
    have hlognn : (0 : ℝ) ≤ (Real.log (2 * (D : ℝ) + 2)) ^ 6 := by positivity
    calc C2 * (x : ℝ) ^ ((1 : ℝ) / 4) * (Real.log (2 * (D : ℝ) + 2)) ^ 6
        ≤ C2 * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) * (Real.log (2 * (D : ℝ) + 2)) ^ 6 := by
          have := mul_le_mul_of_nonneg_right hx14 hlognn
          nlinarith [le_of_lt hC2]
      _ ≤ C2 * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) * (27 ^ 6 * (D : ℝ) ^ ((1 : ℝ) / 4)) := by
          have h1' : C2 * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) * (Real.log (2 * (D : ℝ) + 2)) ^ 6
              ≤ C2 * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) * (27 ^ 6 * (D : ℝ) ^ ((1 : ℝ) / 4)) := by
            apply mul_le_mul_of_nonneg_left hlog
            exact mul_nonneg (le_of_lt hC2) hxv
          exact h1'
      _ = C2 * 27 ^ 6 * (D : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) := by ring
  have hA2 : (∑ d ∈ Finset.Icc 1 D,
        |(Ad d x : ℝ)
          - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
              ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
      ≤ C1 * (D : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) := by
    have hxx : (x : ℝ) ^ ((9 : ℝ) / 16) * (x : ℝ) ^ ((1 : ℝ) / 100)
        = (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) :=
      (Real.rpow_add hx0 ((9 : ℝ) / 16) ((1 : ℝ) / 100)).symm
    refine le_trans hA (le_of_eq ?_)
    calc C1 * (D : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((9 : ℝ) / 16) * (x : ℝ) ^ ((1 : ℝ) / 100)
        = C1 * (D : ℝ) ^ ((1 : ℝ) / 4)
            * ((x : ℝ) ^ ((9 : ℝ) / 16) * (x : ℝ) ^ ((1 : ℝ) / 100)) := by ring
      _ = C1 * (D : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) := by rw [hxx]
  calc (∑ d ∈ Finset.Icc 1 D, |(Ad d x : ℝ) - (Md d x : ℝ)|)
      ≤ _ + _ := hsplit
    _ ≤ C1 * (D : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
        + C2 * 27 ^ 6 * (D : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) :=
          add_le_add hA2 hB2
    _ = (C1 + C2 * 27 ^ 6) * (D : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) := by ring
    _ ≤ (C1 + C2 * 27 ^ 6) * 2 * (D : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) := by
        have hpos : (0:ℝ) ≤ (D : ℝ) ^ ((1:ℝ)/4) * (x : ℝ) ^ ((9 : ℝ)/16 + 1/100) := by positivity
        have hc : (0:ℝ) ≤ C1 + C2 * 27^6 := by positivity
        nlinarith [hpos, hc]

/-- The decomposition `d = d₁ d₂²` with `d₁, d₂` squarefree and coprime is unique. -/
private lemma mul_sq_inj_cube {a b c e : ℕ} (hs₁ : Squarefree a) (hs₂ : Squarefree b)
    (hc : Nat.Coprime a b) (ht₁ : Squarefree c) (ht₂ : Squarefree e) (htc : Nat.Coprime c e)
    (h : a * b ^ 2 = c * e ^ 2) : a = c ∧ b = e := by
  have ha0 : a ≠ 0 := hs₁.ne_zero
  have hb0 : b ≠ 0 := hs₂.ne_zero
  have hc0 : c ≠ 0 := ht₁.ne_zero
  have he0 : e ≠ 0 := ht₂.ne_zero
  have hbv : ∀ u v w t : ℕ, u ≤ 1 → v ≤ 1 → w ≤ 1 → t ≤ 1 → u * v = 0 → w * t = 0 →
      u + 2 * v = w + 2 * t → u = w ∧ v = t := by
    intro u v w t hu hv hw ht huv hwt heq
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · rcases Nat.eq_zero_or_pos v with h0' | h0'
      · have ht0 : t = 0 := by omega
        exact ⟨by omega, by omega⟩
      · have hv1 : v = 1 := by omega
        have ht1 : t = 1 := by omega
        exact ⟨by omega, by omega⟩
    · have hu1 : u = 1 := by omega
      have hv0 : v = 0 := by
        by_contra hv0
        have : 0 < u * v := Nat.mul_pos h0 (Nat.pos_of_ne_zero hv0)
        omega
      have ht0 : t = 0 := by
        by_contra ht0
        have : 0 < w * t := Nat.mul_pos (by omega) (Nat.pos_of_ne_zero ht0)
        omega
      exact ⟨by omega, by omega⟩
  have key : ∀ p : ℕ,
      a.factorization p = c.factorization p ∧ b.factorization p = e.factorization p := by
    intro p
    have hsum : a.factorization p + 2 * b.factorization p
        = c.factorization p + 2 * e.factorization p := by
      have h1 := congrArg (fun n : ℕ => n.factorization p) h
      rw [Nat.factorization_mul ha0 (pow_ne_zero 2 hb0),
          Nat.factorization_mul hc0 (pow_ne_zero 2 he0),
          Nat.factorization_pow, Nat.factorization_pow] at h1
      simpa [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] using h1
    have hcop : ∀ x y : ℕ, Nat.Coprime x y → x.factorization p * y.factorization p = 0 := by
      intro x y hxy
      by_contra hcon
      push Not at hcon
      have hfx : x.factorization p ≠ 0 := (mul_ne_zero_iff.mp hcon).1
      have hfy : y.factorization p ≠ 0 := (mul_ne_zero_iff.mp hcon).2
      have hpx : p ∣ x := by
        by_contra hpx
        exact hfx (Nat.factorization_eq_zero_of_not_dvd hpx)
      have hpy : p ∣ y := by
        by_contra hpy
        exact hfy (Nat.factorization_eq_zero_of_not_dvd hpy)
      have hp : p.Prime := by
        by_contra hp
        exact hfx (Nat.factorization_eq_zero_of_not_prime x hp)
      have hg : p ∣ Nat.gcd x y := Nat.dvd_gcd hpx hpy
      rw [hxy] at hg
      have hple : p ≤ 1 := Nat.le_of_dvd (by norm_num) hg
      have := hp.two_le
      omega
    exact hbv _ _ _ _ (hs₁.natFactorization_le_one p) (hs₂.natFactorization_le_one p)
      (ht₁.natFactorization_le_one p) (ht₂.natFactorization_le_one p)
      (hcop a b hc) (hcop c e htc) hsum
  exact ⟨Nat.factorization_inj ha0 hc0 (Finsupp.ext (fun p => (key p).1)),
         Nat.factorization_inj hb0 he0 (Finsupp.ext (fun p => (key p).2))⟩

/-- `cubeSum` is a sub-sum of the plain sum over `d ≤ D` (the cube-free decomposition
`d = d₁ d₂²` is unique). -/
lemma cubeSum_le_sum_abs (D t : ℕ) :
    cubeSum D (fun d₁ d₂ => |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (Md (d₁ * d₂ ^ 2) t : ℝ)|)
      ≤ ∑ d ∈ Finset.Icc 1 D, |(Ad d t : ℝ) - (Md d t : ℝ)| := by
  classical
  set F : ℕ → ℝ := fun d => |(Ad d t : ℝ) - (Md d t : ℝ)| with hF
  set S : Finset (ℕ × ℕ) :=
    ((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 (Nat.sqrt D))).filter (fun p => cubeCond D p.1 p.2) with hS
  have hinj : ∀ p ∈ S, ∀ q ∈ S, p.1 * p.2 ^ 2 = q.1 * q.2 ^ 2 → p = q := by
    intro p hp q hq heq
    have hp' : cubeCond D p.1 p.2 := (Finset.mem_filter.mp hp).2
    have hq' : cubeCond D q.1 q.2 := (Finset.mem_filter.mp hq).2
    obtain ⟨hs₁, hs₂, hcop, -, -⟩ := hp'
    obtain ⟨ht₁, ht₂, htcop, -, -⟩ := hq'
    obtain ⟨h1, h2⟩ := mul_sq_inj_cube hs₁ hs₂ hcop ht₁ ht₂ htcop heq
    exact Prod.ext h1 h2
  have h1 : cubeSum D (fun d₁ d₂ => F (d₁ * d₂ ^ 2)) = ∑ p ∈ S, F (p.1 * p.2 ^ 2) := by
    rw [cubeSum, hS, Finset.sum_filter, Finset.sum_product]
  have h2 : (∑ p ∈ S, F (p.1 * p.2 ^ 2))
      = ∑ d ∈ S.image (fun p : ℕ × ℕ => p.1 * p.2 ^ 2), F d :=
    (Finset.sum_image hinj).symm
  have h3 : S.image (fun p : ℕ × ℕ => p.1 * p.2 ^ 2) ⊆ Finset.Icc 1 D := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨p, hp, rfl⟩
    obtain ⟨-, -, -, -, hle⟩ := (Finset.mem_filter.mp hp).2
    have hmem := Finset.mem_product.mp (Finset.mem_of_mem_filter p hp)
    have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hmem.1).1
    have hp2 : 1 ≤ p.2 := (Finset.mem_Icc.mp hmem.2).1
    rw [Finset.mem_Icc]
    refine ⟨?_, hle⟩
    calc (1 : ℕ) = 1 * 1 ^ 2 := by ring
      _ ≤ p.1 * p.2 ^ 2 := Nat.mul_le_mul hp1 (Nat.pow_le_pow_left hp2 2)
  have h4 : ∀ x ∈ Finset.Icc 1 D, x ∉ S.image (fun p : ℕ × ℕ => p.1 * p.2 ^ 2) →
      (0 : ℝ) ≤ F x := fun x _ _ => abs_nonneg _
  calc cubeSum D (fun d₁ d₂ => F (d₁ * d₂ ^ 2))
      = ∑ p ∈ S, F (p.1 * p.2 ^ 2) := h1
    _ = ∑ d ∈ S.image (fun p : ℕ × ℕ => p.1 * p.2 ^ 2), F d := h2
    _ ≤ ∑ d ∈ Finset.Icc 1 D, F d := Finset.sum_le_sum_of_subset_of_nonneg h3 h4

/-- **Hypothesis `(3.3)` of `prop35_of_33`**, discharged from the commons theorem
`X2Y4_sieve_remainder_le` (with the harmless `x^{1/100}` slack). -/
theorem h33_of_commons :
    ∃ C : ℝ, 0 < C ∧ ∀ D t : ℕ, 1 ≤ D → 2 ≤ t → D ≤ ⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ →
      cubeSum D (fun d₁ d₂ => |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (Md (d₁ * d₂ ^ 2) t : ℝ)|)
        ≤ C * (D : ℝ) ^ (1 / 4 : ℝ) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) := by
  obtain ⟨C, hC, h⟩ := Ad_sub_Md_sum_le
  refine ⟨C, hC, fun D t hD ht hDt => ?_⟩
  refine le_trans (cubeSum_le_sum_abs D t) ?_
  refine le_trans (h t D (by omega) hD hDt) (le_of_eq ?_)
  ring

/-- **Proposition 3.5 of Friedlander–Iwaniec** for `D ≤ t^{3/4}` (the range used in the
paper, where `D = t^{3/4−5ε}`), now *unconditional*: everything is discharged from the
commons. -/
theorem prop35_unconditional :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ D t : ℕ, 2 ≤ D → 2 ≤ t → D ≤ ⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ →
        cubeSum D (fun d₁ d₂ =>
            |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (gdens (d₁ * d₂ ^ 2) : ℝ) * (Aseq t : ℝ)|)
          ≤ C * ((D : ℝ) ^ (1 / 4 : ℝ) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
              + Real.sqrt t * (Real.log ((D : ℝ) + t + 2)) ^ A) :=
  prop35_of_33 h33_of_commons

end Submission.X2Y4R

namespace Submission.X2Y4R

open Finset Filter

/-- The modulus cut-off used for `(R)`: `D(x) = ⌊x^{11/16}⌋`.  This lies between
`x^{2/3}` and `x^{3/4}` (indeed `2/3 < 11/16 < 3/4`), as required by the companion
paper's `(R1)`. -/
noncomputable def Rcut (x : ℕ) : ℕ := ⌊(x : ℝ) ^ ((11 : ℝ) / 16)⌋₊

/-- The left hand side of `(R)`: `∑_{d ≤ D} μ²(d) |A_d(t) − g(d)A(t)|`. -/
noncomputable def Rsum (x t : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 (Rcut x)).filter (fun d => Squarefree d),
    |(Ad d t : ℝ) - (gdens d : ℝ) * (Aseq t : ℝ)|

/-! ## Auxiliary estimates for `A` -/

lemma Aseq_mono : Monotone Aseq := by
  intro m n hmn
  unfold Aseq
  have hsub : Finset.range (m + 1) ⊆ Finset.range (n + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => Nat.zero_le _

/-- `A(t) ≤ C t^{3/4}`. -/
lemma Aseq_le_const_mul_rpow :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, 1 ≤ t → (Aseq t : ℝ) ≤ C * (t : ℝ) ^ ((3 : ℝ) / 4) := by
  obtain ⟨C, hC, h⟩ := Aseq_asymptotic
  have hκpos : 0 < ∫ u in (0)..1, Real.sqrt (1 - u ^ 4) :=
    lt_of_lt_of_le (by norm_num) Commons.Analysis.Integral.integral_sqrt_one_sub_pow_four_ge
  refine ⟨4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) + C, by positivity, fun t ht => ?_⟩
  have h1 := (abs_le.mp (h t ht)).2
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := by positivity
  have h2 : Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow]
    calc (t : ℝ) ^ ((1 : ℝ) / 2) ≤ (t : ℝ) ^ ((3 : ℝ) / 4) :=
          Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
      _ = (t : ℝ) ^ ((3 : ℝ) / 4) := rfl
  nlinarith [h1, h2, Real.rpow_nonneg ht0 ((3:ℝ)/4)]

/-- `A(x) ≫ x^{3/4}` for large `x`. -/
lemma exists_const_mul_rpow_le_Aseq :
    ∃ c : ℝ, 0 < c ∧ ∃ X : ℕ, ∀ x : ℕ, X ≤ x → c * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ (Aseq x : ℝ) := by
  obtain ⟨C, hC, h⟩ := Aseq_asymptotic
  set κ : ℝ := ∫ u in (0)..1, Real.sqrt (1 - u ^ 4) with hκdef
  have hκ : (87215 : ℝ) / 100000 ≤ κ := Commons.Analysis.Integral.integral_sqrt_one_sub_pow_four_ge
  have hκpos : 0 < κ := lt_of_lt_of_le (by norm_num) hκ
  set T : ℝ := C / (2 * ((87215 : ℝ) / 100000)) with hTdef
  have hTpos : 0 < T := by rw [hTdef]; positivity
  refine ⟨2 * (87215 / 100000), by norm_num, ⌈T ^ 4⌉₊ + 1, fun x hx => ?_⟩
  have hxT : T ^ 4 ≤ (x : ℝ) := by
    have h2 : T ^ 4 ≤ ((⌈T ^ 4⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h3 : ((⌈T ^ 4⌉₊ : ℕ) : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast (by omega : ⌈T ^ 4⌉₊ ≤ x)
    linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    have hx1' : 1 ≤ x := by omega
    exact_mod_cast hx1'
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le zero_lt_one hx1
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hxpos
  have hrpow : T ≤ (x : ℝ) ^ ((1 : ℝ) / 4) := by
    have h1 : (T ^ 4) ^ ((1 : ℝ) / 4) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) hxT (by norm_num)
    rwa [← Real.rpow_natCast T 4, ← Real.rpow_mul (le_of_lt hTpos), show ((4 : ℕ) : ℝ) * (1/4) = 1 by norm_num,
      Real.rpow_one] at h1
  have hCsq : C ≤ 2 * ((87215 : ℝ) / 100000) * (x : ℝ) ^ ((1 : ℝ) / 4) := by
    have := mul_le_mul_of_nonneg_left hrpow (by norm_num : (0:ℝ) ≤ 2 * ((87215:ℝ)/100000))
    rw [hTdef] at this
    field_simp at this
    linarith
  have hsplit : (x : ℝ) ^ ((3 : ℝ) / 4) = (x : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add hxpos]
    norm_num
  have hCsqrt : C * Real.sqrt (x : ℝ) ≤ 2 * ((87215 : ℝ) / 100000) * (x : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow]
    calc C * (x : ℝ) ^ ((1 : ℝ) / 2)
        ≤ (2 * ((87215 : ℝ) / 100000) * (x : ℝ) ^ ((1 : ℝ) / 4)) * (x : ℝ) ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hCsq (Real.rpow_nonneg hx0 _)
      _ = 2 * ((87215 : ℝ) / 100000) * ((x : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((1 : ℝ) / 2)) := by ring
      _ = 2 * ((87215 : ℝ) / 100000) * (x : ℝ) ^ ((3 : ℝ) / 4) := by rw [← hsplit]
  have h1 := (abs_le.mp (h x (by omega))).1
  have hκ' : 2 * ((87215 : ℝ) / 100000) ≤ 4 * κ - 2 * ((87215 : ℝ) / 100000) := by linarith
  have hmain : 2 * ((87215 : ℝ) / 100000) * (x : ℝ) ^ ((3 : ℝ) / 4)
      ≤ (4 * κ - 2 * ((87215 : ℝ) / 100000)) * (x : ℝ) ^ ((3 : ℝ) / 4) :=
    mul_le_mul_of_nonneg_right hκ' (Real.rpow_nonneg hx0 _)
  have h1' : 4 * κ * (x : ℝ) ^ ((3 : ℝ) / 4) - C * Real.sqrt (x : ℝ) ≤ (Aseq x : ℝ) := by
    linarith [h1]
  refine le_trans ?_ h1'
  calc 2 * ((87215 : ℝ) / 100000) * (x : ℝ) ^ ((3 : ℝ) / 4)
      ≤ (4 * κ - 2 * ((87215 : ℝ) / 100000)) * (x : ℝ) ^ ((3 : ℝ) / 4) := hmain
    _ = 4 * κ * (x : ℝ) ^ ((3 : ℝ) / 4) - 2 * ((87215 : ℝ) / 100000) * (x : ℝ) ^ ((3 : ℝ) / 4) := by ring
    _ ≤ 4 * κ * (x : ℝ) ^ ((3 : ℝ) / 4) - C * Real.sqrt (x : ℝ) := by linarith [hCsqrt]


/-! ## Elementary bounds entering the two cases -/

/-- `an 0 = 1`: the only lattice point with `a² + c⁴ = 0` is the origin. -/
lemma an_zero : an 0 = 1 := by
  unfold an
  rw [Set.ncard_eq_one]
  refine ⟨(0, 0), ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    rw [Nat.cast_zero] at hx
    have h1 : (0 : ℤ) ≤ x.1 ^ 2 := sq_nonneg x.1
    have h2 : (0 : ℤ) ≤ x.2 ^ 4 := by positivity
    have hx1 : x.1 ^ 2 = 0 := by linarith
    have hx2 : x.2 ^ 4 = 0 := by linarith
    exact Prod.ext (sq_eq_zero_iff.mp hx1) ((pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp hx2)
  · rintro rfl
    norm_num

/-- A sum over the squarefree `d ≤ D` of a nonnegative summand is at most the
`cubeSum` over the cubefree moduli `d = d₁ d₂² ≤ D` (the pairs `(d, 1)`). -/
lemma sqfree_sum_le_cubeSum (D : ℕ) (hD : 1 ≤ D) (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d) :
    (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Squarefree d), F d)
      ≤ cubeSum D (fun d₁ d₂ => F (d₁ * d₂ ^ 2)) := by
  have hL : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Squarefree d), F d)
      = ∑ d ∈ Finset.Icc 1 D, if Squarefree d then F d else 0 := by
    rw [Finset.sum_filter]
  rw [hL, cubeSum]
  refine Finset.sum_le_sum fun d₁ hd₁ => ?_
  have h1mem : 1 ∈ Finset.Icc 1 (Nat.sqrt D) := by
    rw [Finset.mem_Icc]
    exact ⟨le_rfl, Nat.le_sqrt'.mpr (by simpa using hD)⟩
  by_cases hs : Squarefree d₁
  · have hnot4 : ¬ 4 ∣ d₁ * 1 ^ 2 := by
      intro h
      have h4 : (2 : ℕ) * 2 ∣ d₁ := by simpa using h
      exact absurd (hs 2 h4) (by norm_num)
    have hcond : cubeCond D d₁ 1 :=
      ⟨hs, squarefree_one, Nat.coprime_one_right d₁, hnot4,
        by simpa using (Finset.mem_Icc.mp hd₁).2⟩
    rw [if_pos hs]
    have hterm : (if cubeCond D d₁ 1 then F (d₁ * 1 ^ 2) else 0) = F d₁ := by
      rw [if_pos hcond]; simp
    rw [← hterm]
    refine Finset.single_le_sum (f := fun d₂ => if cubeCond D d₁ d₂ then F (d₁ * d₂ ^ 2) else 0)
      (fun d₂ _ => ?_) h1mem
    by_cases h : cubeCond D d₁ d₂
    · rw [if_pos h]; exact hF _
    · rw [if_neg h]
  · rw [if_neg hs]
    exact Finset.sum_nonneg fun d₂ _ => by
      by_cases h : cubeCond D d₁ d₂
      · rw [if_pos h]; exact hF _
      · rw [if_neg h]

/-- `∑_{d ∈ Icc 1 D} A_d(t) ≤ D + C t^{1/100} A(t)`: the lattice points `a² + c⁴ ≤ t`
weighted by the number of their divisors `d ≤ D`. -/
lemma sum_Ad_le :
    ∃ C : ℝ, 0 < C ∧ ∀ D t : ℕ,
      (∑ d ∈ Finset.Icc 1 D, (Ad d t : ℝ))
        ≤ (D : ℝ) + C * (t : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ) := by
  obtain ⟨C, hC, hb⟩ := Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (1 / 100 : ℝ)
    (by norm_num)
  refine ⟨C, hC, fun D t => ?_⟩
  have hswap : (∑ d ∈ Finset.Icc 1 D, (Ad d t : ℝ))
      = ∑ n ∈ Finset.range (t + 1),
          (an n : ℝ) * (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ) := by
    have h1 : (∑ d ∈ Finset.Icc 1 D, (Ad d t : ℝ))
        = ∑ d ∈ Finset.Icc 1 D, ∑ n ∈ Finset.range (t + 1),
            (if d ∣ n then (an n : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun d _ => ?_
      unfold Ad
      rw [Finset.sum_filter]
      simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hswap]
  have hsplit : ∀ n ∈ Finset.range (t + 1),
      (an n : ℝ) * (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ)
        ≤ (an n : ℝ) * (if n = 0 then (D : ℝ) else C * (t : ℝ) ^ ((1 : ℝ) / 100)) := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have hcard : ((Finset.Icc 1 D).filter (fun d => d ∣ 0)).card = D := by
        rw [Finset.filter_true_of_mem (fun d _ => dvd_zero d), Nat.card_Icc]
        simp
      rw [if_pos rfl, hcard]
    · have hsub : (Finset.Icc 1 D).filter (fun d => d ∣ n) ⊆ Nat.divisors n := by
        intro d hd
        rw [Finset.mem_filter] at hd
        exact Nat.mem_divisors.mpr ⟨hd.2, by omega⟩
      have hcard : (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ)
          ≤ ((Nat.divisors n).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have htau : ((Nat.divisors n).card : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 100) := hb n
      have hnt : (n : ℝ) ≤ (t : ℝ) := by
        have := Finset.mem_range.mp hn
        exact_mod_cast (by omega : n ≤ t)
      have hlt : (n : ℝ) ^ ((1 : ℝ) / 100) ≤ (t : ℝ) ^ ((1 : ℝ) / 100) :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) hnt (by norm_num)
      have hfin : (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ)
          ≤ C * (t : ℝ) ^ ((1 : ℝ) / 100) :=
        le_trans hcard (le_trans htau (mul_le_mul_of_nonneg_left hlt hC.le))
      rw [if_neg (by omega : n ≠ 0)]
      exact mul_le_mul_of_nonneg_left hfin (by positivity)
  have hshift : (∑ n ∈ Finset.range t, (an (n + 1) : ℝ)) ≤ (Aseq t : ℝ) := by
    rw [Aseq, Nat.cast_sum]
    conv_rhs => rw [Finset.sum_range_succ']
    have hnn : (0 : ℝ) ≤ (an 0 : ℝ) := by positivity
    linarith
  calc ∑ n ∈ Finset.range (t + 1),
        (an n : ℝ) * (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ)
      ≤ ∑ n ∈ Finset.range (t + 1),
          (an n : ℝ) * (if n = 0 then (D : ℝ) else C * (t : ℝ) ^ ((1 : ℝ) / 100)) :=
        Finset.sum_le_sum hsplit
    _ = (an 0 : ℝ) * (D : ℝ) + ∑ n ∈ Finset.range t,
          (an (n + 1) : ℝ) * (C * (t : ℝ) ^ ((1 : ℝ) / 100)) := by
        rw [Finset.sum_range_succ']
        have h0 : (an 0 : ℝ) * (if 0 = 0 then (D : ℝ) else C * (t : ℝ) ^ ((1 : ℝ) / 100))
            = (an 0 : ℝ) * (D : ℝ) := by rw [if_pos rfl]
        rw [h0, add_comm]
        refine congrArg (fun z => (an 0 : ℝ) * (D : ℝ) + z) ?_
        exact Finset.sum_congr rfl fun n _ => by rw [if_neg (by omega : ¬ n + 1 = 0)]
    _ = (an 0 : ℝ) * (D : ℝ) + C * (t : ℝ) ^ ((1 : ℝ) / 100) *
          (∑ n ∈ Finset.range t, (an (n + 1) : ℝ)) := by
        rw [Finset.mul_sum]
        exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun n _ => by ring)
    _ ≤ (D : ℝ) + C * (t : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ) := by
        rw [an_zero]
        push_cast
        have h1 : (0 : ℝ) ≤ C * (t : ℝ) ^ ((1 : ℝ) / 100) := by positivity
        nlinarith [hshift, h1]

/-- `∑_{d ≤ D, d squarefree} g(d) ≪ (log D)^A`: the local-density summatory bound,
through the cubefree `cubeSum` bound of §3. -/
lemma sum_gdens_sqfree_le :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ D : ℕ, 2 ≤ D →
      (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Squarefree d), (gdens d : ℝ))
        ≤ C * (Real.log D) ^ A := by
  obtain ⟨C, A, hC, h⟩ := cubeSum_gdens_le
  have hCpos : 0 < C * max 1 ((Real.log 2) ^ (A - max A 0)) :=
    mul_pos hC (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  refine ⟨C * max 1 ((Real.log 2) ^ (A - max A 0)), max A 0, hCpos, le_max_right _ _, fun D hD => ?_⟩
  have hA' : A ≤ max A 0 := le_max_left _ _
  have hgn : ∀ d : ℕ, 0 ≤ (gdens d : ℝ) := fun d => Rat.cast_nonneg.mpr (gdens_nonneg d)
  have hsq : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Squarefree d), (gdens d : ℝ))
      ≤ cubeSum D (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|) := by
    have h1 := sqfree_sum_le_cubeSum D (by omega) (fun d => |(gdens d : ℝ)|) (fun d => abs_nonneg _)
    rwa [Finset.sum_congr rfl (fun d _ => abs_of_nonneg (hgn d))] at h1
  have hbound := rpow_log_le_const_mul (B := A) (A := max A 0) hA' hD
  have hlogD0 : 0 ≤ (Real.log D) ^ (max A 0) :=
    Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ D))) _
  have hmul : (Real.log 2) ^ (A - max A 0) * (Real.log D) ^ (max A 0)
      ≤ max 1 ((Real.log 2) ^ (A - max A 0)) * (Real.log D) ^ (max A 0) :=
    mul_le_mul_of_nonneg_right (le_max_right 1 _) hlogD0
  calc (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Squarefree d), (gdens d : ℝ))
      ≤ cubeSum D (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|) := hsq
    _ ≤ C * (Real.log D) ^ A := h D hD
    _ ≤ C * ((Real.log 2) ^ (A - max A 0) * (Real.log D) ^ (max A 0)) :=
        mul_le_mul_of_nonneg_left hbound hC.le
    _ ≤ C * (max 1 ((Real.log 2) ^ (A - max A 0)) * (Real.log D) ^ (max A 0)) :=
        mul_le_mul_of_nonneg_left hmul hC.le
    _ = C * max 1 ((Real.log 2) ^ (A - max A 0)) * (Real.log D) ^ (max A 0) := by ring

lemma poly_tail_aux {K α β cA x : ℝ} (hx : 0 < x) (hu : 0 < Real.log x) (hcA : 0 < cA)
    (h : (K / cA) * (Real.log x) ^ (β + 22) ≤ x ^ ((3:ℝ)/4 - α)) :
    K * x ^ α * (Real.log x) ^ β ≤ cA * x ^ ((3:ℝ)/4) * (Real.log x) ^ (-(22:ℝ)) := by
  have hu0 : 0 ≤ Real.log x := le_of_lt hu
  have hx0 : 0 ≤ x := le_of_lt hx
  -- step A
  have hA : (K / cA) * (Real.log x) ^ (β + 22) * x ^ (α - (3:ℝ)/4) ≤ 1 := by
    have hp : x ^ ((3:ℝ)/4 - α) * x ^ (α - (3:ℝ)/4) = 1 := by
      rw [← Real.rpow_add hx, show (3:ℝ)/4 - α + (α - 3/4) = 0 by ring, Real.rpow_zero]
    rw [← hp]
    exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hx0 _)
  -- step B : drop the division by cA
  have hB : K * (Real.log x) ^ (β + 22) * x ^ (α - (3:ℝ)/4) ≤ cA := by
    have heq : (K / cA) * (Real.log x) ^ (β + 22) * x ^ (α - (3:ℝ)/4)
        = (K * (Real.log x) ^ (β + 22) * x ^ (α - (3:ℝ)/4)) / cA := by ring
    rw [heq] at hA
    have := (div_le_iff₀ hcA).mp hA
    simpa using this
  -- step C : multiply by x^(3/4-α)
  have hC : K * (Real.log x) ^ (β + 22) ≤ cA * x ^ ((3:ℝ)/4 - α) := by
    have hp : x ^ (α - (3:ℝ)/4) * x ^ ((3:ℝ)/4 - α) = 1 := by
      rw [← Real.rpow_add hx, show α - 3/4 + ((3:ℝ)/4 - α) = 0 by ring, Real.rpow_zero]
    have h2 : K * (Real.log x) ^ (β + 22) * x ^ (α - (3:ℝ)/4) * x ^ ((3:ℝ)/4 - α) ≤ cA * x ^ ((3:ℝ)/4 - α) :=
      mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hx0 _)
    rwa [mul_assoc, hp, mul_one] at h2
  -- step D : multiply by x^α
  have hD : K * (Real.log x) ^ (β + 22) * x ^ α ≤ cA * x ^ ((3:ℝ)/4) := by
    have hp : x ^ ((3:ℝ)/4 - α) * x ^ α = x ^ ((3:ℝ)/4) := by
      rw [← Real.rpow_add hx, show (3:ℝ)/4 - α + α = (3:ℝ)/4 by ring]
    have h2 := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hx0 α)
    calc K * (Real.log x) ^ (β + 22) * x ^ α
        = (K * (Real.log x) ^ (β + 22)) * x ^ α := by ring
      _ ≤ (cA * x ^ ((3:ℝ)/4 - α)) * x ^ α := h2
      _ = cA * (x ^ ((3:ℝ)/4 - α) * x ^ α) := by ring
      _ = cA * x ^ ((3:ℝ)/4) := by rw [hp]
  -- step E : divide by u^22
  have hE : K * x ^ α * (Real.log x) ^ (β + 22) * (Real.log x) ^ (-(22:ℝ))
      ≤ cA * x ^ ((3:ℝ)/4) * (Real.log x) ^ (-(22:ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith [hD, mul_comm (K * (Real.log x) ^ (β + 22)) (x ^ α)]
      : K * x ^ α * (Real.log x) ^ (β + 22) ≤ cA * x ^ ((3:ℝ)/4))
      (Real.rpow_nonneg hu0 _)
  have hsplit : (Real.log x) ^ (β + 22) * (Real.log x) ^ (-(22:ℝ)) = (Real.log x) ^ β := by
    rw [← Real.rpow_add hu, show β + 22 + (-(22:ℝ)) = β by ring]
  calc K * x ^ α * (Real.log x) ^ β
      = K * x ^ α * ((Real.log x) ^ (β + 22) * (Real.log x) ^ (-(22:ℝ))) := by rw [hsplit]
    _ = K * x ^ α * (Real.log x) ^ (β + 22) * (Real.log x) ^ (-(22:ℝ)) := by ring
    _ ≤ cA * x ^ ((3:ℝ)/4) * (Real.log x) ^ (-(22:ℝ)) := hE

lemma poly_tail_le (K α β cA : ℝ) (hK : 0 < K) (hα : α < 3/4) (hcA : 0 < cA) :
    ∃ X : ℕ, 5 ≤ X ∧ ∀ x : ℕ, X ≤ x →
      K * (x : ℝ) ^ α * (Real.log x) ^ β
        ≤ cA * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-(22 : ℝ)) := by
  obtain ⟨X₁, -, hX₁⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold (K := K / cA) (by positivity)
      (n := ⌈β + 22⌉₊) (r := (3:ℝ)/4 - α) (by linarith)
  refine ⟨max 5 ⌈X₁⌉₊ + 1, by omega, fun x hx => ?_⟩
  have hx5 : 5 ≤ x := by omega
  have hxX : X₁ ≤ (x : ℝ) := by
    have h1 : ((max 5 ⌈X₁⌉₊ + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    push_cast at h1
    have h2 : ((⌈X₁⌉₊ : ℕ) : ℝ) ≤ ((max 5 ⌈X₁⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast le_max_right 5 ⌈X₁⌉₊
    push_cast at h2
    have h3 : X₁ ≤ ((⌈X₁⌉₊ : ℕ) : ℝ) := Nat.le_ceil X₁
    linarith
  have hxR : (5 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx5
  have hxpos : (0 : ℝ) < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    have hexp : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_d9, hxR]
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  have hmain := hX₁ (x : ℝ) hxX
  refine poly_tail_aux hxpos hlogpos hcA ?_
  refine le_trans ?_ hmain
  have hβ : (Real.log x) ^ (β + 22) ≤ (Real.log x) ^ (⌈β + 22⌉₊ : ℕ) := by
    simpa [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hlog1 (Nat.le_ceil (β + 22))
  simpa using mul_le_mul_of_nonneg_left hβ (by positivity : (0:ℝ) ≤ K / cA)

/-- `⌊x^{11/16}⌋ ≥ 2` for `x ≥ 5`. -/
lemma two_le_Rcut {x : ℕ} (hx : 5 ≤ x) : 2 ≤ Rcut x := by
  unfold Rcut
  refine Nat.le_floor ?_
  have hx5 : (5 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have h4 : (2 : ℝ) ^ 2 ≤ (x : ℝ) := by nlinarith
  have hs : (2 : ℝ) ≤ Real.sqrt (x : ℝ) := by
    calc (2 : ℝ) = Real.sqrt ((2 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (x : ℝ) := Real.sqrt_le_sqrt h4
  have hsplit : (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  rw [Real.sqrt_eq_rpow] at hs
  linarith

/-- `A_d(t) ≤ A(t)`. -/
lemma Ad_le_Aseq (d t : ℕ) : Ad d t ≤ Aseq t := by
  unfold Ad Aseq
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => Nat.zero_le _)

/-- `Rcut x ≤ x^{11/16}`. -/
lemma Rcut_le_rpow (x : ℕ) : (Rcut x : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) :=
  Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg x) _)

/-- `Rcut x ≤ x`. -/
lemma Rcut_le_self (x : ℕ) : Rcut x ≤ x := by
  rcases Nat.eq_zero_or_pos x with h0 | hp
  · subst h0
    unfold Rcut
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num : ((11 : ℝ) / 16) ≠ 0)]
    simp
  · have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hp
    have hle : (x : ℝ) ^ ((11 : ℝ) / 16) ≤ (x : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : ((11 : ℝ) / 16) ≤ 1)
      rwa [Real.rpow_one] at h
    calc Rcut x = ⌊(x : ℝ) ^ ((11 : ℝ) / 16)⌋₊ := rfl
      _ ≤ ⌊(x : ℝ)⌋₊ := Nat.floor_mono hle
      _ = x := Nat.floor_natCast x

/-- **(R) of the companion paper for the Friedlander–Iwaniec sequence.**
With the cut-off `D = ⌊x^{11/16}⌋` (which satisfies `x^{2/3} < D(x) < x`) one has
`∑_{d ≤ D} μ²(d) |A_d(t) − g(d)A(t)| ≤ A(x) (log x)^{-22}` for every `t ≤ x`. -/
theorem Rsum_le_inv_log_pow :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
      Rsum x t ≤ (Aseq x : ℝ) * (Real.log x) ^ (-(22 : ℝ)) := by
  obtain ⟨cA, hcA, XA, hAlow⟩ := exists_const_mul_rpow_le_Aseq
  obtain ⟨CA, hCA, hAup⟩ := Aseq_le_const_mul_rpow
  obtain ⟨CAd, hCAd, hAd⟩ := sum_Ad_le
  obtain ⟨Cg, Ag, hCg, hAg, hGg⟩ := sum_gdens_sqfree_le
  obtain ⟨C35, A35, hC35, hA35, h35⟩ := prop35_unconditional
  obtain ⟨Y1, hY1x, hY1⟩ :=
    poly_tail_le C35 ((47 : ℝ) / 64 + 1 / 100) 0 (cA / 2) hC35 (by norm_num) (by positivity)
  obtain ⟨Y2, hY2x, hY2⟩ :=
    poly_tail_le (C35 * 2 ^ A35) (1 / 2) A35 (cA / 2) (by positivity) (by norm_num) (by positivity)
  obtain ⟨Y3, hY3x, hY3⟩ :=
    poly_tail_le 1 ((11 : ℝ) / 16) 0 (cA / 3) (by norm_num) (by norm_num) (by positivity)
  obtain ⟨Y4, hY4x, hY4⟩ :=
    poly_tail_le (CAd * CA) ((11 : ℝ) / 16 + 1 / 100) 0 (cA / 3) (by positivity) (by norm_num) (by positivity)
  obtain ⟨Y5, hY5x, hY5⟩ :=
    poly_tail_le (Cg * CA) ((11 : ℝ) / 16) Ag (cA / 3) (by positivity) (by norm_num) (by positivity)
  refine ⟨max (max (max (max Y1 Y2) Y3) Y4) (max Y5 (max XA 5)) + 1, fun x hx t ht2 htx => ?_⟩
  have hxY1 : Y1 ≤ x := by omega
  have hxY2 : Y2 ≤ x := by omega
  have hxY3 : Y3 ≤ x := by omega
  have hxY4 : Y4 ≤ x := by omega
  have hxY5 : Y5 ≤ x := by omega
  have hxXA : XA ≤ x := by omega
  have hx5 : 5 ≤ x := by omega
  have hxR : (5 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx5
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hxpos
  have hlog1 : 1 ≤ Real.log x := by
    have hexp : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  have hlog0 : 0 ≤ Real.log x := le_of_lt hlogpos
  have hAx : cA * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ (Aseq x : ℝ) := hAlow x hxXA
  have ht1 : 1 ≤ t := by omega
  have htle : (t : ℝ) ≤ (x : ℝ) := by exact_mod_cast htx
  have hlogz : (0 : ℝ) ≤ (Real.log x) ^ (-(22 : ℝ)) := Real.rpow_nonneg hlog0 _
  by_cases hcase : Rcut x ≤ ⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊
  · -- ## Case A : `D ≤ t^{3/4}`, so Proposition 3.5 applies directly
    have hD2 : 2 ≤ Rcut x := two_le_Rcut hx5
    have h35' := h35 (Rcut x) t hD2 ht2 hcase
    have hR1 : Rsum x t ≤ cubeSum (Rcut x)
        (fun d₁ d₂ => |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (gdens (d₁ * d₂ ^ 2) : ℝ) * (Aseq t : ℝ)|) :=
      sqfree_sum_le_cubeSum (Rcut x) (by omega)
        (fun d => |(Ad d t : ℝ) - (gdens d : ℝ) * (Aseq t : ℝ)|) (fun d => abs_nonneg _)
    have hDpow : (Rcut x : ℝ) ^ ((1 : ℝ) / 4) ≤ (x : ℝ) ^ ((11 : ℝ) / 64) := by
      have h1 := Real.rpow_le_rpow (Nat.cast_nonneg (Rcut x)) (Rcut_le_rpow x)
        (by norm_num : (0 : ℝ) ≤ 1 / 4)
      have h2 : ((x : ℝ) ^ ((11 : ℝ) / 16)) ^ ((1 : ℝ) / 4) = (x : ℝ) ^ ((11 : ℝ) / 64) := by
        rw [← Real.rpow_mul hx0]; norm_num
      rwa [h2] at h1
    have htpow : (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) ≤ (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) :=
      Real.rpow_le_rpow (Nat.cast_nonneg t) htle (by norm_num)
    have hterm1 : (Rcut x : ℝ) ^ ((1 : ℝ) / 4) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
        ≤ (x : ℝ) ^ ((47 : ℝ) / 64 + 1 / 100) := by
      have h3 : (11 : ℝ) / 64 + ((9 : ℝ) / 16 + 1 / 100) = (47 : ℝ) / 64 + 1 / 100 := by norm_num
      refine le_trans (mul_le_mul hDpow htpow (Real.rpow_nonneg (Nat.cast_nonneg t) _)
        (Real.rpow_nonneg hx0 _)) ?_
      rw [← h3, ← Real.rpow_add hxpos]
    have hlogar0 : 0 ≤ Real.log ((Rcut x : ℝ) + (t : ℝ) + 2) := by
      refine Real.log_nonneg ?_
      have h1 : (0 : ℝ) ≤ (Rcut x : ℝ) := by positivity
      have h2 : (0 : ℝ) ≤ (t : ℝ) := by positivity
      linarith
    have hlogbound : Real.log ((Rcut x : ℝ) + (t : ℝ) + 2) ≤ 2 * Real.log x := by
      have h1 : (Rcut x : ℝ) + (t : ℝ) + 2 ≤ 3 * (x : ℝ) := by
        have h2 : (Rcut x : ℝ) ≤ (x : ℝ) := by exact_mod_cast (Rcut_le_self x)
        linarith [h2, htle, hxR]
      have h2 : Real.log (3 * (x : ℝ)) = Real.log 3 + Real.log x :=
        Real.log_mul (by norm_num) (ne_of_gt hxpos)
      have h3 : Real.log 3 ≤ Real.log x := by
        have h4 : (3 : ℝ) ≤ (x : ℝ) := by
          have : (3 : ℕ) ≤ x := by omega
          exact_mod_cast this
        exact Real.log_le_log (by norm_num) h4
      have h4 : (0 : ℝ) < (Rcut x : ℝ) + (t : ℝ) + 2 := by
        have h5 : (0 : ℝ) ≤ (Rcut x : ℝ) := by positivity
        have h6 : (0 : ℝ) ≤ (t : ℝ) := by positivity
        linarith
      calc Real.log ((Rcut x : ℝ) + (t : ℝ) + 2) ≤ Real.log (3 * (x : ℝ)) :=
            Real.log_le_log h4 h1
        _ = Real.log 3 + Real.log x := h2
        _ ≤ 2 * Real.log x := by linarith
    have hterm2 : Real.sqrt (t : ℝ) * (Real.log ((Rcut x : ℝ) + (t : ℝ) + 2)) ^ A35
        ≤ 2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35) := by
      have hs : Real.sqrt (t : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow (Nat.cast_nonneg t) htle (by norm_num)
      have hl : (Real.log ((Rcut x : ℝ) + (t : ℝ) + 2)) ^ A35 ≤ (2 * Real.log x) ^ A35 :=
        Real.rpow_le_rpow hlogar0 hlogbound hA35
      have hl2 : (2 * Real.log x) ^ A35 = 2 ^ A35 * (Real.log x) ^ A35 :=
        Real.mul_rpow (by norm_num) hlog0
      have h2nn : (0 : ℝ) ≤ 2 ^ A35 * (Real.log x) ^ A35 :=
        mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hlog0 _)
      calc Real.sqrt (t : ℝ) * (Real.log ((Rcut x : ℝ) + (t : ℝ) + 2)) ^ A35
          ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (2 ^ A35 * (Real.log x) ^ A35) :=
            mul_le_mul hs (hl2 ▸ hl) (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hx0 _)
        _ = 2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35) := by ring
    have hY1' : C35 * (x : ℝ) ^ ((47 : ℝ) / 64 + 1 / 100)
        ≤ cA / 2 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-(22 : ℝ)) := by
      have h := hY1 x hxY1
      simpa only [Real.rpow_zero, mul_one] using h
    have hY2'' : C35 * (2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35))
        ≤ cA / 2 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-(22 : ℝ)) := by
      have h := hY2 x hxY2
      calc C35 * (2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35))
          = C35 * 2 ^ A35 * (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35 := by ring
        _ ≤ cA / 2 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-(22 : ℝ)) := h
    calc Rsum x t
        ≤ cubeSum (Rcut x)
            (fun d₁ d₂ => |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (gdens (d₁ * d₂ ^ 2) : ℝ) * (Aseq t : ℝ)|) := hR1
      _ ≤ C35 * ((Rcut x : ℝ) ^ ((1 : ℝ) / 4) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
            + Real.sqrt (t : ℝ) * (Real.log ((Rcut x : ℝ) + (t : ℝ) + 2)) ^ A35) := h35'
      _ ≤ C35 * ((x : ℝ) ^ ((47 : ℝ) / 64 + 1 / 100)
            + 2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35)) :=
          mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) hC35.le
      _ = C35 * (x : ℝ) ^ ((47 : ℝ) / 64 + 1 / 100)
            + C35 * (2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35)) := by ring
      _ ≤ cA / 2 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-(22 : ℝ))
            + cA / 2 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-(22 : ℝ)) :=
          add_le_add hY1' hY2''
      _ = cA * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-(22 : ℝ)) := by ring
      _ ≤ (Aseq x : ℝ) * (Real.log x) ^ (-(22 : ℝ)) := mul_le_mul_of_nonneg_right hAx hlogz
  · -- ## Case B : `D > t^{3/4}`, elementary bounds suffice
    have hD2 : 2 ≤ Rcut x := two_le_Rcut hx5
    have hlt : ⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ < Rcut x := Nat.lt_of_not_le hcase
    have ht34 : (t : ℝ) ^ ((3 : ℝ) / 4) < (x : ℝ) ^ ((11 : ℝ) / 16) := by
      have h1 : (t : ℝ) ^ ((3 : ℝ) / 4) < ((⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have h2 : ((⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ : ℕ) : ℝ) + 1 ≤ (Rcut x : ℝ) := by
        exact_mod_cast hlt
      exact lt_of_lt_of_le (lt_of_lt_of_le h1 h2) (Rcut_le_rpow x)
    have hAt : (Aseq t : ℝ) ≤ CA * (x : ℝ) ^ ((11 : ℝ) / 16) := by
      calc (Aseq t : ℝ) ≤ CA * (t : ℝ) ^ ((3 : ℝ) / 4) := hAup t ht1
        _ ≤ CA * (x : ℝ) ^ ((11 : ℝ) / 16) :=
            mul_le_mul_of_nonneg_left (le_of_lt ht34) hCA.le
    have hgn : ∀ d : ℕ, 0 ≤ (gdens d : ℝ) := fun d => Rat.cast_nonneg.mpr (gdens_nonneg d)
    have hR1 : Rsum x t ≤ (∑ d ∈ Finset.Icc 1 (Rcut x), (Ad d t : ℝ))
        + (Aseq t : ℝ) * (∑ d ∈ (Finset.Icc 1 (Rcut x)).filter (fun d => Squarefree d), (gdens d : ℝ)) := by
      have h1 : Rsum x t ≤ ∑ d ∈ (Finset.Icc 1 (Rcut x)).filter (fun d => Squarefree d),
          ((Ad d t : ℝ) + (Aseq t : ℝ) * (gdens d : ℝ)) := by
        unfold Rsum
        refine Finset.sum_le_sum fun d _ => ?_
        have hx0' : (0 : ℝ) ≤ (Ad d t : ℝ) := by positivity
        have hy0 : (0 : ℝ) ≤ (Aseq t : ℝ) * (gdens d : ℝ) := by
          have := hgn d; positivity
        have := abs_sub_le_iff.mp (le_refl (|(Ad d t : ℝ) - (Aseq t : ℝ) * (gdens d : ℝ)|))
        simp only [abs_sub_le_iff]
        constructor <;> linarith [abs_nonneg ((Ad d t : ℝ) - (Aseq t : ℝ) * (gdens d : ℝ))]
      refine le_trans h1 ?_
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      refine add_le_add ?_ le_rfl
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => by positivity
    have hpiece1 : (∑ d ∈ Finset.Icc 1 (Rcut x), (Ad d t : ℝ))
        ≤ (x : ℝ) ^ ((11 : ℝ) / 16) + CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ) := by
      have h1 := hAd (Rcut x) t
      have h3 : (t : ℝ) ^ ((1 : ℝ) / 100) ≤ (x : ℝ) ^ ((1 : ℝ) / 100) :=
        Real.rpow_le_rpow (Nat.cast_nonneg t) htle (by norm_num)
      have h4 : CAd * (t : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ)
          ≤ CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ) := by
        have h5 : (0 : ℝ) ≤ (Aseq t : ℝ) := by positivity
        have h6 : CAd * (t : ℝ) ^ ((1 : ℝ) / 100) ≤ CAd * (x : ℝ) ^ ((1 : ℝ) / 100) :=
          mul_le_mul_of_nonneg_left h3 hCAd.le
        exact mul_le_mul_of_nonneg_right h6 h5
      have h7 : (Rcut x : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) := Rcut_le_rpow x
      linarith
    have hpiece2 : (Aseq t : ℝ) * (∑ d ∈ (Finset.Icc 1 (Rcut x)).filter (fun d => Squarefree d), (gdens d : ℝ))
        ≤ CA * (x : ℝ) ^ ((11 : ℝ) / 16) * (Cg * (Real.log x) ^ Ag) := by
      have h1 := hGg (Rcut x) hD2
      have hR1' : (1 : ℕ) ≤ Rcut x := by omega
      have hlogx1 : (1 : ℝ) ≤ (Rcut x : ℝ) := by exact_mod_cast hR1'
      have hlogR0 : 0 ≤ Real.log (Rcut x) := Real.log_nonneg hlogx1
      have hlogR : Real.log (Rcut x) ≤ Real.log x := by
        have h3 : (0 : ℝ) < (Rcut x : ℝ) := by linarith
        have h4 : (Rcut x : ℝ) ≤ (x : ℝ) := by
          exact_mod_cast (Rcut_le_self x)
        exact Real.log_le_log h3 h4
      have hAg' : (Real.log (Rcut x)) ^ Ag ≤ (Real.log x) ^ Ag :=
        Real.rpow_le_rpow hlogR0 hlogR hAg
      have h2 : (∑ d ∈ (Finset.Icc 1 (Rcut x)).filter (fun d => Squarefree d), (gdens d : ℝ))
          ≤ Cg * (Real.log x) ^ Ag :=
        le_trans h1 (mul_le_mul_of_nonneg_left hAg' hCg.le)
      have h4 : (0 : ℝ) ≤ Cg * (Real.log x) ^ Ag :=
        mul_nonneg hCg.le (Real.rpow_nonneg hlog0 _)
      exact mul_le_mul hAt h2 (Finset.sum_nonneg fun d _ => hgn d) (by positivity)
    have hY3' : (x : ℝ) ^ ((11 : ℝ) / 16)
        ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-(22 : ℝ)) := by
      have h := hY3 x hxY3
      simpa only [Real.rpow_zero, mul_one, one_mul] using h
    have hY4' : CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ)
        ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-(22 : ℝ)) := by
      have h := hY4 x hxY4
      simp only [Real.rpow_zero, mul_one] at h
      have h5 : CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ)
          ≤ CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (CA * (x : ℝ) ^ ((11 : ℝ) / 16)) :=
        mul_le_mul_of_nonneg_left hAt (by positivity)
      refine le_trans h5 ?_
      calc CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (CA * (x : ℝ) ^ ((11 : ℝ) / 16))
          = CAd * CA * ((x : ℝ) ^ ((1 : ℝ) / 100) * (x : ℝ) ^ ((11 : ℝ) / 16)) := by ring
        _ = CAd * CA * (x : ℝ) ^ ((11 : ℝ) / 16 + 1 / 100) := by
              rw [← Real.rpow_add hxpos]; norm_num
        _ ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-(22 : ℝ)) := h
    have hY5' : CA * (x : ℝ) ^ ((11 : ℝ) / 16) * (Cg * (Real.log x) ^ Ag)
        ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-(22 : ℝ)) := by
      have h := hY5 x hxY5
      calc CA * (x : ℝ) ^ ((11 : ℝ) / 16) * (Cg * (Real.log x) ^ Ag)
          = Cg * CA * (x : ℝ) ^ ((11 : ℝ) / 16) * (Real.log x) ^ Ag := by ring
        _ ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-(22 : ℝ)) := h
    calc Rsum x t
        ≤ (∑ d ∈ Finset.Icc 1 (Rcut x), (Ad d t : ℝ))
          + (Aseq t : ℝ) * (∑ d ∈ (Finset.Icc 1 (Rcut x)).filter (fun d => Squarefree d), (gdens d : ℝ)) := hR1
      _ ≤ ((x : ℝ) ^ ((11 : ℝ) / 16) + CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ))
          + CA * (x : ℝ) ^ ((11 : ℝ) / 16) * (Cg * (Real.log x) ^ Ag) := add_le_add hpiece1 hpiece2
      _ = (x : ℝ) ^ ((11 : ℝ) / 16) + CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ)
          + CA * (x : ℝ) ^ ((11 : ℝ) / 16) * (Cg * (Real.log x) ^ Ag) := by ring
      _ ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-(22 : ℝ))
          + cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-(22 : ℝ))
          + cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-(22 : ℝ)) :=
          add_le_add (add_le_add hY3' hY4') hY5'
      _ = cA * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-(22 : ℝ)) := by ring
      _ ≤ (Aseq x : ℝ) * (Real.log x) ^ (-(22 : ℝ)) := mul_le_mul_of_nonneg_right hAx hlogz

end Submission.X2Y4R

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- **Hypothesis (R) of the companion paper "Asymptotic sieve for primes"**
(Friedlander–Iwaniec, Ann. of Math. 148 (1998) 1041–1065) for the sequence
`a_n = #{(a,c) ∈ ℤ² : a² + c⁴ = n}` of the Friedlander–Iwaniec polynomial `X² + Y⁴`.

With `A(x) = ∑_{n ≤ x} a_n`, `A_d(x) = ∑_{n ≤ x, d ∣ n} a_n` and `g(d) = N(d)/d²`,
`N(d) = #{x ∈ (ℤ/d)² : x₁² + x₂⁴ ≡ 0}`, and modulus cut-off `D(x) = ⌊x^{11/16}⌋`
(satisfying the companion's `(R1)`: `x^{2/3} < D(x) < x^{3/4} ≤ x`),

  `∑_{d ≤ D} μ²(d) |A_d(t) − g(d) A(t)| ≤ A(x) (log x)^{-22}`   for all `t ≤ x`.

(The proof uses Proposition 3.5 / Lemma 3.1 `(3.3)` of the main paper for
`t ≥ x^{11/12}`, and the crude bound `|A_d(t) − g(d)A(t)| ≤ A_d(t) + g(d)A(t)`
with `A(t) ≪ t^{3/4} < x^{11/16}` for smaller `t`.  A complete proof of exactly this
statement is in the workspace file `Submission/ASP_R.lean`, theorem
`Submission.X2Y4_R_hypothesis`.) -/
theorem X2Y4_R_hypothesis :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
      (∑ d ∈ (Finset.Icc 1 ⌊(x : ℝ) ^ ((11 : ℝ) / 16)⌋₊).filter (fun d => Squarefree d),
        |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
        ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-(22 : ℝ)) := by
  simpa only [Submission.X2Y4R.Rsum, Submission.X2Y4R.Rcut] using Submission.X2Y4R.Rsum_le_inv_log_pow

end Commons.NumberTheory.FriedlanderIwaniec
