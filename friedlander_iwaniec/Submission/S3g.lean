import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sieve_remainder_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_hdens_cubefree_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_gdens_cubefree_prod_le_final

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# §3 endgame of Friedlander–Iwaniec: Proposition 3.5 from Lemma 3.1

This file assembles Proposition 3.5 of

  J. Friedlander, H. Iwaniec, *The polynomial X² + Y⁴ captures its primes*,
  Ann. of Math. **148** (1998), 945–1040,

from the paper's Lemma 3.1 `(3.3)` together with the polylogarithmic bounds for
the local-density factors `h(d)` and `g(d)`.

The statement of Proposition 3.5 is `∑^{♭}_{d ≤ D} |r_d(t)| ≪ D^{1/4} x^{9/16+ε}`,
where the superscript `♭` restricts to cubefree `d` and `r_d(t) = A_d(t) − g(d)A(t)`.
The only non-elementary input beyond (3.3) is the decomposition

  `|M_d(t) − g(d) A(t)| ≤ |M_d(t) − 4 g(d) κ t^{3/4}| + |g(d)| · |4 κ t^{3/4} − A(t)|`

together with the asymptotic formulae (3.15) (`Md_cubefree_asymptotic`) and
(3.18) (`Aseq_asymptotic`), both already formalised, and the polylogarithmic
summatory bounds for `h` and `g`.

All numerical inputs are hypotheses here, so the file records the exact
reduction.  They are supplied by `Submission.Md_cubefree_asymptotic` (Lemma 3.4),
`Submission.Aseq_asymptotic` (formula (3.18)),
`Commons.NumberTheory.FriedlanderIwaniec.sum_hdens_cubefree_le` (for `h`), and
the analogous bound for `g` (which follows from `sum_hdens_le` since `g(d) ≤ h(d)`).
-/

namespace Submission

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

end Submission
