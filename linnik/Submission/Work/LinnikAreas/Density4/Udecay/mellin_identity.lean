import Mathlib
import Submission.Work.LinnikAreas.Density4.selberg_U_aux
import Submission.Work.LinnikAreas.Density4.Udecay.mellin_muRecip_integrable
import Submission.Work.LinnikAreas.Density4.Udecay.mellin_abel_tsum

namespace Work.LinnikAreas.Density4.Udecay

open scoped BigOperators
open MeasureTheory
open Finset

noncomputable section

/-!
# The Mellin transform identity for `A(t) = Σ_{n ≤ t} μ(n)/n`

With `muRecip t = muRecipSum ⌊t⌋₊ = Σ_{n ≤ ⌊t⌋} μ(n)/n` (a step function) we prove

`∫_1^∞ A(t) t^{-1-s} dt = (1/s) Σ_n μ(n)/n^{1+s}`  `(s > 0)`.

The argument is a two-sided Abel summation.  On the integral side we split `[1,∞)` into the
unit intervals `[k+1, k+2)`, on each of which `A(t) = muRecipSum (k+1)` is constant, so that

`∫_1^∞ A(t) t^{-1-s} dt = Σ_k muRecipSum (k+1) · ((k+1)^{-s} - (k+2)^{-s})/s`.

On the series side Abel's summation transforms the partial sums `muRecipSum` back into the
original coefficients `μ(n)/n`, giving `Σ_n μ(n)/n^{1+s}`.
-/

/-- `∫_a^b t^{-1-s} dt = (a^{-s} - b^{-s})/s` over the half-open interval `[a,b)` (`0 < a ≤ b`). -/
lemma mellin_rpow_Ico_integral {a b s : ℝ} (hs : 0 < s) (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in Set.Ico a b, t ^ (-(1 + s) : ℝ) = (a ^ (-s) - b ^ (-s)) / s := by
  have hr : (-(1 + s) : ℝ) ≠ -1 := by intro h; linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    simp only [Set.mem_Icc, not_and]
    intro h; linarith
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  rw [integral_rpow (Or.inr ⟨hr, h0⟩)]
  rw [show (-(1 + s) : ℝ) + 1 = -s by ring]
  field_simp
  ring

/-- On `[n, n+1)` the step function `muRecip` is the partial sum `muRecipSum n`. -/
lemma muRecip_eq_muRecipSum_floor (n : ℕ) {t : ℝ} (ht : t ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1)) :
    Work.LinnikAreas.Density4.muRecip t = Commons.NumberTheory.Moebius.muRecipSum n := by
  rw [Work.LinnikAreas.Density4.muRecip]
  have ht' : (n : ℝ) ≤ t ∧ t < (n : ℝ) + 1 := ht
  have h0 : (0 : ℝ) ≤ t := le_trans (Nat.cast_nonneg n) ht'.1
  rw [show ⌊t⌋₊ = n from (Nat.floor_eq_iff h0).mpr ht']

/-- `[1,∞)` is the union of the half-open unit intervals `[k+1, k+2)`, `k : ℕ`. -/
lemma mellin_iUnion_Ico_eq_Ici :
    (⋃ k : ℕ, (Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2) : Set ℝ)) = Set.Ici (1 : ℝ) := by
  ext t
  rw [show (t ∈ (⋃ k : ℕ, (Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2) : Set ℝ)))
        ↔ (∃ k : ℕ, t ∈ Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2)) from Set.mem_iUnion]
  constructor
  · rintro ⟨k, hk1, _⟩
    show (1 : ℝ) ≤ t
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  · intro ht
    have ht' : (1 : ℝ) ≤ t := ht
    have hfl1 : 1 ≤ ⌊t⌋₊ := by
      have := Nat.floor_mono ht'; simpa using this
    refine ⟨⌊t⌋₊ - 1, ?_, ?_⟩
    · have hk : ((⌊t⌋₊ - 1 : ℕ) : ℝ) + 1 = (⌊t⌋₊ : ℝ) := by
        push_cast [Nat.cast_sub hfl1]; ring
      rw [hk]; exact Nat.floor_le (by linarith : (0 : ℝ) ≤ t)
    · have hk : ((⌊t⌋₊ - 1 : ℕ) : ℝ) + 2 = (⌊t⌋₊ : ℝ) + 1 := by
        push_cast [Nat.cast_sub hfl1]; ring
      rw [hk]; exact Nat.lt_floor_add_one t

/-- The unit intervals `[k+1, k+2)` are pairwise disjoint. -/
lemma mellin_pairwise_disjoint_Ico :
    Pairwise (Function.onFun Disjoint fun k : ℕ => (Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2) : Set ℝ)) := by
  intro i j hij
  change Disjoint (Set.Ico ((i : ℝ) + 1) ((i : ℝ) + 2)) (Set.Ico ((j : ℝ) + 1) ((j : ℝ) + 2))
  rw [Set.disjoint_left]
  intro x hx1 hx2
  rw [Set.mem_Ico] at hx1 hx2
  obtain ⟨h1a, h1b⟩ := hx1
  obtain ⟨h2a, h2b⟩ := hx2
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : ((i : ℝ) + 2) ≤ ((j : ℝ) + 1) := by
      have hc' : (i + 2 : ℕ) ≤ (j + 1 : ℕ) := by omega
      exact_mod_cast hc'
    linarith
  · have hc : ((j : ℝ) + 2) ≤ ((i : ℝ) + 1) := by
      have hc' : (j + 2 : ℕ) ≤ (i + 1 : ℕ) := by omega
      exact_mod_cast hc'
    linarith

/-- Split an integral over `[1,∞)` into the sum of the integrals over the unit intervals. -/
lemma mellin_integral_eq_tsum (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ici (1 : ℝ))) :
    ∫ t in Set.Ici (1 : ℝ), f t = ∑' k : ℕ, ∫ t in Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2), f t := by
  rw [← mellin_iUnion_Ico_eq_Ici]
  exact MeasureTheory.integral_iUnion (fun k => measurableSet_Ico) mellin_pairwise_disjoint_Ico
    (by rwa [mellin_iUnion_Ico_eq_Ici])

/-- Value of the integrand on one unit interval. -/
lemma mellin_Ico_integral (s : ℝ) (hs : 0 < s) (k : ℕ) :
    ∫ t in Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2),
        Work.LinnikAreas.Density4.muRecip t / t ^ (1 + s : ℝ)
      = Commons.NumberTheory.Moebius.muRecipSum (k + 1)
          * ((((k : ℝ) + 1) ^ (-s) - ((k : ℝ) + 2) ^ (-s)) / s) := by
  have hcongr : Set.EqOn
      (fun t => Work.LinnikAreas.Density4.muRecip t / t ^ (1 + s : ℝ))
      (fun t => Commons.NumberTheory.Moebius.muRecipSum (k + 1) * t ^ (-(1 + s)))
      (Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2)) := by
    intro t ht
    change Work.LinnikAreas.Density4.muRecip t / t ^ (1 + s : ℝ)
      = Commons.NumberTheory.Moebius.muRecipSum (k + 1) * t ^ (-(1 + s))
    have ht' : ((k : ℝ) + 1) ≤ t ∧ t < ((k : ℝ) + 2) := ht
    have hk1 : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    have htnn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have ht1 : (1 : ℝ) ≤ t := by rw [hk1] at ht'; linarith [ht'.1]
    have hpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    have hmem : t ∈ Set.Ico ((k + 1 : ℕ) : ℝ) (((k + 1 : ℕ) : ℝ) + 1) := by
      rw [Set.mem_Ico] at ht ⊢
      refine ⟨by rw [← hk1]; exact ht.1, ?_⟩
      push_cast
      rw [hk1] at ht
      linarith [ht.2]
    rw [muRecip_eq_muRecipSum_floor (k + 1) hmem,
        div_eq_mul_inv, Real.rpow_neg (le_of_lt hpos) (1 + s)]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ico hcongr,
      MeasureTheory.integral_const_mul,
      mellin_rpow_Ico_integral hs (by positivity) (by linarith)]

/-- Reindex the interval sum: shifting by one only adds the vanishing `m = 0` term. -/
lemma mellin_tsum_reindex (s : ℝ) (hs : 0 < s) :
    (∑' k : ℕ, Commons.NumberTheory.Moebius.muRecipSum (k + 1)
        * (((k : ℝ) + 1) ^ (-s) - ((k : ℝ) + 2) ^ (-s)))
      = ∑' m : ℕ, Commons.NumberTheory.Moebius.muRecipSum m
        * ((m : ℝ) ^ (-s) - ((m : ℝ) + 1) ^ (-s)) := by
  obtain ⟨hsum, _⟩ := mellin_abel_tsum hs
  rw [hsum.tsum_eq_zero_add]
  have h0 : Commons.NumberTheory.Moebius.muRecipSum (0 : ℕ) = 0 := by
    simp [Commons.NumberTheory.Moebius.muRecipSum]
  simp only [Nat.cast_zero, h0, zero_mul, zero_add]
  refine tsum_congr (fun k => ?_)
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show ((k : ℝ) + 1) + 1 = (k : ℝ) + 2 by ring]

/-- **Mellin transform identity** for the reciprocal Möbius partial sums. -/
theorem mellin_identity (s : ℝ) (hs : 0 < s) :
    ∫ t in Set.Ioi 1, Work.LinnikAreas.Density4.muRecip t / t ^ (1 + s : ℝ)
      = (1 / s) * (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ (1 + s : ℝ)) := by
  have hInt : IntegrableOn
      (fun t : ℝ => Work.LinnikAreas.Density4.muRecip t / t ^ (1 + s : ℝ)) (Set.Ici 1) :=
    mellin_muRecip_integrable hs
  rw [← MeasureTheory.integral_Ici_eq_integral_Ioi
      (f := fun t : ℝ => Work.LinnikAreas.Density4.muRecip t / t ^ (1 + s : ℝ))]
  rw [mellin_integral_eq_tsum _ hInt]
  have hterm : ∀ k : ℕ, ∫ t in Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2),
        Work.LinnikAreas.Density4.muRecip t / t ^ (1 + s : ℝ)
      = (1 / s) * (Commons.NumberTheory.Moebius.muRecipSum (k + 1)
          * (((k : ℝ) + 1) ^ (-s) - ((k : ℝ) + 2) ^ (-s))) := by
    intro k
    rw [mellin_Ico_integral s hs k]
    ring
  rw [tsum_congr hterm, tsum_mul_left]
  congr 1
  rw [mellin_tsum_reindex s hs, (mellin_abel_tsum hs).2]

end

end Work.LinnikAreas.Density4.Udecay
