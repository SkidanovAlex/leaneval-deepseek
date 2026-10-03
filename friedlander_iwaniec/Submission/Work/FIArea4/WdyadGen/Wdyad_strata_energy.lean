import Mathlib
import Submission.Work.FIArea4.WdyadGenDefs
import Submission.Work.FIArea4.prop_11_1_defs
import Submission.Work.FIArea4.WdyadGen.TZbox_stratum
import Submission.Work.FIArea4.WdyadGen.TZbox_one_bound
import Submission.Work.FIArea4.Wdyad_units
import Submission.Work.FIArea4.WdyadGen.Wdyad_strata_defs
import Submission.Work.FIArea4.WdyadGen.braceV_toolbox
import Submission.Work.FIArea4.WdyadGen.TZone_energy_le
import Submission.Work.FIArea4.WdyadGen.stratEn_sum_le_WE
import Submission.Work.FIArea4.WdyadGen.gLift_stratum_le

/-!
# The strata energy bound `Wdyad_strata_energy`

Assuming the unit-class dual variance bound (`hunit`, i.e. Friedlander--Iwaniec (11.24), with
bracket `WTb`), the total energy of the `gcd = e` strata of a coefficient matrix `γ` is bounded by
the target bracket `braceV` times the energy `WE D γ` of `γ`.

The two ingredients are

* the stratum identity `TZbox_stratum`, which writes the stratum of `γ` for `gcd(a,d) = e` as a
  *unit-supported* problem at the reduced parameters `(D/e, R, S/e)` (`gLift_stratum_le`);
* the assumption `hunit`, applied to each reduced problem; the modulus window `(D/e, 2D/e]` and the
  `s`-window `(S/e, 2S/e]` are "almost dyadic" -- each is either `(q,2q]` or `(q,2q+1]` -- and both
  the dyadic box and the single extra modulus `2q+1` are controlled here (`WboxI_almost_dyadic`).

Adding the (disjoint) strata energies (`stratEn_sum_le_WE`) finishes the proof.
-/

namespace Work.FIArea4.WdyadGen

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## Elementary real-analysis and integer-division lemmas -/

/-- `‖x+y‖² ≤ 2‖x‖² + 2‖y‖²`. -/
lemma normSq_add_le_two (x y : ℂ) :
    Complex.normSq (x + y) ≤ 2 * Complex.normSq x + 2 * Complex.normSq y := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  calc ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
    _ ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- **Scaling the `s`-window by at most `2`.**  If `S ≤ S' ≤ 2S` and `S ≥ 1` then the bracket at
`S'` is at most `2^(2+ε)` times the bracket at `S`. -/
lemma braceV_le_two_mul_S_of (D R S S' : ℕ) (ε : ℝ) (hε : 0 < ε) (hS : 1 ≤ S)
    (h2 : S' ≤ 2 * S) :
    Work.FIArea4.braceV D R S' ε ≤ (2:ℝ)^(2+ε) * Work.FIArea4.braceV D R S ε := by
  have hS2 : ((S':ℕ):ℝ) ≤ 2 * (S:ℝ) := by
    have h : ((S':ℕ):ℝ) ≤ ((2*S:ℕ):ℝ) := by exact_mod_cast h2
    push_cast at h; linarith
  have hSnn : (0:ℝ) ≤ (S:ℝ) := by positivity
  have hRnn : (0:ℝ) ≤ (R:ℝ) := by positivity
  have hDnn : (0:ℝ) ≤ (D:ℝ) := by positivity
  have hc2 : (2:ℝ) ≤ (2:ℝ)^(2+ε) := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by linarith : (1:ℝ) ≤ 2+ε)
    rw [Real.rpow_one] at hh; exact hh
  have h2e0 : (0:ℝ) ≤ (2:ℝ)^ε := Real.rpow_nonneg (by norm_num) _
  have hQnn : (0:ℝ) ≤ ((R:ℝ)*(S:ℝ))^ε := Real.rpow_nonneg (by positivity) _
  have hQ'nn : (0:ℝ) ≤ ((R:ℝ)*(S':ℝ))^ε := Real.rpow_nonneg (by positivity) _
  have hRS' : ((R:ℝ) * (S':ℝ)) ≤ 2 * ((R:ℝ) * (S:ℝ)) := by nlinarith
  have hQle : ((R:ℝ) * (S':ℝ))^ε ≤ (2:ℝ)^ε * (((R:ℝ) * (S:ℝ))^ε) := by
    have h1 : ((R:ℝ) * (S':ℝ)) ^ ε ≤ (2 * ((R:ℝ) * (S:ℝ))) ^ ε :=
      Real.rpow_le_rpow (by positivity) hRS' hε.le
    rwa [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity)] at h1
  have hsqrtle : Real.sqrt ((R:ℝ) * (S':ℝ)) ≤ Real.sqrt 2 * Real.sqrt ((R:ℝ) * (S:ℝ)) := by
    calc Real.sqrt ((R:ℝ) * (S':ℝ)) ≤ Real.sqrt (2 * ((R:ℝ) * (S:ℝ))) := Real.sqrt_le_sqrt hRS'
      _ = Real.sqrt 2 * Real.sqrt ((R:ℝ)*(S:ℝ)) := Real.sqrt_mul (by norm_num) _
  have hp34 : ((S':ℕ):ℝ) ^ ((3:ℝ)/4) ≤ (2:ℝ)^((3:ℝ)/4) * (S:ℝ) ^ ((3:ℝ)/4) := by
    have h1 : ((S':ℕ):ℝ) ^ ((3:ℝ)/4) ≤ (2 * (S:ℝ)) ^ ((3:ℝ)/4) :=
      Real.rpow_le_rpow (by positivity) hS2 (by norm_num)
    rwa [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hSnn] at h1
  have hr2 : Real.sqrt 2 * (2:ℝ)^ε ≤ (2:ℝ)^(2+ε) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith : (1:ℝ)/2 + ε ≤ 2+ε)
  have hr3 : (2:ℝ)^((3:ℝ)/4) * (2:ℝ)^ε ≤ (2:ℝ)^(2+ε) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith : (3:ℝ)/4 + ε ≤ 2+ε)
  have hr1 : (2:ℝ) * (2:ℝ)^ε ≤ (2:ℝ)^(2+ε) := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by linarith : (1:ℝ)+ε ≤ 2+ε)
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one] at hh
    simpa using hh
  have keyA : (D:ℝ)^(-(1:ℝ)/2) * (R:ℝ) * (S':ℝ)
      ≤ (2:ℝ)^(2+ε) * ((D:ℝ)^(-(1:ℝ)/2) * (R:ℝ) * (S:ℝ)) := by
    have h0 : (0:ℝ) ≤ (D:ℝ)^(-(1:ℝ)/2) * (R:ℝ) := by positivity
    have h1 : (D:ℝ)^(-(1:ℝ)/2) * (R:ℝ) * (S':ℝ) ≤ (D:ℝ)^(-(1:ℝ)/2) * (R:ℝ) * (2 * (S:ℝ)) :=
      mul_le_mul_of_nonneg_left hS2 h0
    have h2 : (D:ℝ)^(-(1:ℝ)/2) * (R:ℝ) * (2 * (S:ℝ)) = 2 * ((D:ℝ)^(-(1:ℝ)/2) * (R:ℝ) * (S:ℝ)) := by ring
    have h3 : (2:ℝ) * ((D:ℝ)^(-(1:ℝ)/2) * (R:ℝ) * (S:ℝ))
        ≤ (2:ℝ)^(2+ε) * ((D:ℝ)^(-(1:ℝ)/2) * (R:ℝ) * (S:ℝ)) :=
      mul_le_mul_of_nonneg_right hc2 (by positivity)
    linarith [h1, h2.le, h3]
  have keyB : (D:ℝ) * Real.sqrt ((R:ℝ) * (S':ℝ)) * ((R:ℝ) * (S':ℝ))^ε ≤
      (2:ℝ)^(2+ε) * ((D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)) * ((R:ℝ)*(S:ℝ))^ε) := by
    have hb : (D:ℝ) * Real.sqrt ((R:ℝ)*(S':ℝ)) ≤ Real.sqrt 2 * ((D:ℝ)*Real.sqrt ((R:ℝ)*(S:ℝ))) := by
      have h := mul_le_mul_of_nonneg_left hsqrtle hDnn
      linarith [h]
    have h1 : (D:ℝ) * Real.sqrt ((R:ℝ)*(S':ℝ)) * ((R:ℝ)*(S':ℝ))^ε ≤
        (Real.sqrt 2 * ((D:ℝ)*Real.sqrt ((R:ℝ)*(S:ℝ)))) * ((2:ℝ)^ε * (((R:ℝ)*(S:ℝ))^ε)) :=
      mul_le_mul hb hQle hQ'nn (by positivity)
    have h2 : (Real.sqrt 2 * ((D:ℝ)*Real.sqrt ((R:ℝ)*(S:ℝ)))) * ((2:ℝ)^ε * (((R:ℝ)*(S:ℝ))^ε))
        = (Real.sqrt 2 * (2:ℝ)^ε) * ((D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)) * ((R:ℝ)*(S:ℝ))^ε) := by ring
    have h3 : (Real.sqrt 2 * (2:ℝ)^ε) * ((D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)) * ((R:ℝ)*(S:ℝ))^ε)
        ≤ (2:ℝ)^(2+ε) * ((D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)) * ((R:ℝ)*(S:ℝ))^ε) :=
      mul_le_mul_of_nonneg_right hr2 (by positivity)
    linarith [h1, h2.le, h3]
  have keyC : (R:ℝ) * ((S':ℕ):ℝ)^((3:ℝ)/4) * ((R:ℝ)*(S':ℝ))^ε ≤
      (2:ℝ)^(2+ε) * ((R:ℝ) * (S:ℝ)^((3:ℝ)/4) * ((R:ℝ)*(S:ℝ))^ε) := by
    have hc : (R:ℝ) * ((S':ℕ):ℝ)^((3:ℝ)/4) ≤ (2:ℝ)^((3:ℝ)/4) * ((R:ℝ) * (S:ℝ)^((3:ℝ)/4)) := by
      have h := mul_le_mul_of_nonneg_left hp34 hRnn
      linarith [h]
    have h1 : (R:ℝ) * ((S':ℕ):ℝ)^((3:ℝ)/4) * ((R:ℝ)*(S':ℝ))^ε ≤
        ((2:ℝ)^((3:ℝ)/4) * ((R:ℝ)*(S:ℝ)^((3:ℝ)/4))) * ((2:ℝ)^ε * (((R:ℝ)*(S:ℝ))^ε)) :=
      mul_le_mul hc hQle hQ'nn (by positivity)
    have h2 : ((2:ℝ)^((3:ℝ)/4) * ((R:ℝ)*(S:ℝ)^((3:ℝ)/4))) * ((2:ℝ)^ε * (((R:ℝ)*(S:ℝ))^ε))
        = ((2:ℝ)^((3:ℝ)/4) * (2:ℝ)^ε) * ((R:ℝ) * (S:ℝ)^((3:ℝ)/4) * ((R:ℝ)*(S:ℝ))^ε) := by ring
    have h3 : ((2:ℝ)^((3:ℝ)/4) * (2:ℝ)^ε) * ((R:ℝ) * (S:ℝ)^((3:ℝ)/4) * ((R:ℝ)*(S:ℝ))^ε)
        ≤ (2:ℝ)^(2+ε) * ((R:ℝ) * (S:ℝ)^((3:ℝ)/4) * ((R:ℝ)*(S:ℝ))^ε) :=
      mul_le_mul_of_nonneg_right hr3 (by positivity)
    linarith [h1, h2.le, h3]
  have keyE : ((S':ℕ):ℝ) * (R:ℝ)^((3:ℝ)/4) * ((R:ℝ)*(S':ℝ))^ε ≤
      (2:ℝ)^(2+ε) * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) * ((R:ℝ)*(S:ℝ))^ε) := by
    have h3 : (0:ℝ) ≤ (R:ℝ)^((3:ℝ)/4) := Real.rpow_nonneg (by positivity) _
    have he : ((S':ℕ):ℝ) * (R:ℝ)^((3:ℝ)/4) ≤ (2:ℝ) * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4)) := by
      nlinarith [hS2, h3]
    have h1 : ((S':ℕ):ℝ) * (R:ℝ)^((3:ℝ)/4) * ((R:ℝ)*(S':ℝ))^ε ≤
        ((2:ℝ) * ((S:ℝ)*(R:ℝ)^((3:ℝ)/4))) * ((2:ℝ)^ε * (((R:ℝ)*(S:ℝ))^ε)) :=
      mul_le_mul he hQle hQ'nn (by positivity)
    have h2 : ((2:ℝ) * ((S:ℝ)*(R:ℝ)^((3:ℝ)/4))) * ((2:ℝ)^ε * (((R:ℝ)*(S:ℝ))^ε))
        = ((2:ℝ) * (2:ℝ)^ε) * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) * ((R:ℝ)*(S:ℝ))^ε) := by ring
    have h3 : ((2:ℝ) * (2:ℝ)^ε) * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) * ((R:ℝ)*(S:ℝ))^ε)
        ≤ (2:ℝ)^(2+ε) * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) * ((R:ℝ)*(S:ℝ))^ε) :=
      mul_le_mul_of_nonneg_right hr1 (by positivity)
    linarith [h1, h2.le, h3]
  have hsplit : Work.FIArea4.braceV D R S' ε
      = (D:ℝ)^(-(1:ℝ)/2) * (R:ℝ) * (S':ℝ)
        + ((D:ℝ) * Real.sqrt ((R:ℝ)*(S':ℝ)) + (R:ℝ) * ((S':ℕ):ℝ)^((3:ℝ)/4)
            + ((S':ℕ):ℝ) * (R:ℝ)^((3:ℝ)/4)) * ((R:ℝ)*(S':ℝ))^ε := rfl
  have hsplit2 : Work.FIArea4.braceV D R S ε
      = (D:ℝ)^(-(1:ℝ)/2) * (R:ℝ) * (S:ℝ)
        + ((D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)) + (R:ℝ) * (S:ℝ)^((3:ℝ)/4)
            + (S:ℝ) * (R:ℝ)^((3:ℝ)/4)) * ((R:ℝ)*(S:ℝ))^ε := rfl
  rw [hsplit, hsplit2]
  nlinarith [keyA, keyB, keyC, keyE, h2e0, hQnn, hQ'nn, hc2]

/-- The modulus window `(2D/e]` of a stratum is either `(2⌊D/e⌋]` or `(2⌊D/e⌋+1]`. -/
lemma two_mul_div_eq (D e : ℕ) (he : 0 < e) :
    2 * D / e = 2 * (D / e) ∨ 2 * D / e = 2 * (D / e) + 1 := by
  have hD : D = e * (D / e) + D % e := (Nat.div_add_mod D e).symm
  have key : 2 * D / e = 2 * (D % e) / e + 2 * (D / e) := by
    conv_lhs => rw [hD]
    rw [show 2 * (e * (D / e) + D % e) = 2 * (D % e) + e * (2 * (D / e)) by ring]
    exact Nat.add_mul_div_left _ _ he
  have hlt : 2 * (D % e) / e ≤ 1 := by
    have h : 2 * (D % e) / e < 2 := by
      rw [Nat.div_lt_iff_lt_mul he]
      have := Nat.mod_lt D he
      omega
    omega
  rcases Nat.eq_zero_or_pos (2 * (D % e) / e) with h0 | hpos
  · left; rw [key, h0]; ring
  · right; rw [key]; omega

lemma TZbox_succ_eq_TZone (n : ℕ) (β : ℕ → ℕ → ℂ) (r s : ℕ) :
    Work.FIArea4.TZbox n (n+1) β r s = TZone (n+1) β r s := by
  unfold Work.FIArea4.TZbox TZone
  rw [Finset.sum_Ioc_succ_top (le_refl n)]
  simp

/-- `‖Mentry d a r s‖ ≤ 1`. -/
lemma normSq_Mentry_le_one (d a r s : ℕ) : Complex.normSq (Work.FIArea4.Mentry d a r s) ≤ 1 := by
  unfold Work.FIArea4.Mentry
  split
  · rw [Complex.normSq_intCast]
    rcases jacobiSym.trichotomy (r : ℤ) (Work.FIPlan.oddPart d) with h | h | h <;> rw [h] <;> norm_num
  · rw [Complex.normSq_zero]; norm_num

/-- The sum over a union of two finsets is at most the sum of the two sums (nonnegative summand). -/
lemma sum_union_le' (A B : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ A ∪ B, f x ≤ ∑ x ∈ A, f x + ∑ x ∈ B, f x := by
  have h1 : (A ∪ B : Finset ℕ) = A ∪ (B \ A) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  rw [h1, Finset.sum_union Finset.disjoint_sdiff]
  have h2 : ∑ x ∈ B \ A, f x ≤ ∑ x ∈ B, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i _ _ => hf i)
  linarith

lemma rpow_neg_half_mul' (D : ℕ) (x : ℝ) :
    (D:ℝ)^(-(1:ℝ)/2) * x = x / Real.sqrt (D:ℝ) := by
  rw [Real.sqrt_eq_rpow, show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring,
    Real.rpow_neg (by positivity), inv_mul_eq_div]

lemma WboxI_almost_dyadic (ε : ℝ) (hε : 0 < ε) (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hunit : ∀ (D₀ R S : ℕ) (β : ℕ → ℕ → ℂ), 1 ≤ D₀ → 1 ≤ R → 1 ≤ S →
      (∀ a d, β a d ≠ 0 → Nat.Coprime a d) →
      Work.FIArea4.Wdyad D₀ R S β ≤ C₁ * Work.FIArea4.WTb D₀ R S ε * Work.FIArea4.WE D₀ β) :
    ∃ K : ℝ, 0 < K ∧ ∀ (D₀ D₁ S₀ S₁ R : ℕ) (β : ℕ → ℕ → ℂ),
      1 ≤ D₀ → 1 ≤ R → 1 ≤ S₀ →
      (D₁ = 2 * D₀ ∨ D₁ = 2 * D₀ + 1) → (S₁ = 2 * S₀ ∨ S₁ = 2 * S₀ + 1) →
      (∀ a d, β a d ≠ 0 → Nat.Coprime a d) →
      WboxI R S₀ S₁ D₀ D₁ β ≤ K * Work.FIArea4.braceV D₀ R S₀ ε
        * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d) := by
  refine ⟨8 * C₁ + 8 * C₁ * (2:ℝ)^(2+ε) + 10, by positivity, ?_⟩
  intro D₀ D₁ S₀ S₁ R β hD₀ hR hS₀ hDcase hScase hβ
  have hε0 : (0:ℝ) ≤ ε := hε.le
  have hRnn : (0:ℝ) ≤ (R:ℝ) := by positivity
  have hD0pos : 0 < D₀ := hD₀
  have hD1low : 2 * D₀ ≤ D₁ := by rcases hDcase with h | h <;> omega
  have hD₀lt : D₀ < D₁ := by omega
  have hEnn : (0:ℝ) ≤ ∑ d ∈ Finset.Ioc D₀ D₁, rowE β d :=
    Finset.sum_nonneg (fun d _ => rowE_nonneg _ _)
  have hrowD1 : rowE β D₁ ≤ ∑ d ∈ Finset.Ioc D₀ D₁, rowE β d :=
    Finset.single_le_sum (f := fun d => rowE β d) (fun d _ => rowE_nonneg β d)
      (Finset.mem_Ioc.mpr ⟨hD₀lt, le_rfl⟩)
  have hBrnn : 0 ≤ Work.FIArea4.braceV D₀ R S₀ ε := braceV_nonneg D₀ R S₀ ε
  have hBEnn : (0:ℝ) ≤ Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d) :=
    mul_nonneg hBrnn hEnn
  have hsd : Real.sqrt (D₀:ℝ) ≤ (D₁:ℝ) := by
    have h1 : Real.sqrt (D₀:ℝ) ≤ (D₀:ℝ) := by
      have h := Real.sqrt_le_sqrt (show (D₀:ℝ) ≤ (D₀:ℝ)*(D₀:ℝ) by
        have h1 : (1:ℝ) ≤ (D₀:ℝ) := by exact_mod_cast hD₀
        nlinarith)
      rwa [Real.sqrt_mul_self (by positivity)] at h
    have h2 : (D₀:ℝ) ≤ (D₁:ℝ) := by exact_mod_cast (le_trans (by omega : D₀ ≤ 2*D₀) hD1low)
    linarith
  have hsqpos : (0:ℝ) < Real.sqrt (D₀:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hD0pos)
  -- hunit for a dyadic s-window
  have hhunit : ∀ T : ℕ, 1 ≤ T → WboxI R T (2*T) D₀ (2*D₀) β
      ≤ C₁ * Work.FIArea4.WTb D₀ R T ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d) := by
    intro T hT
    have hWE : Work.FIArea4.WE D₀ β ≤ ∑ d ∈ Finset.Ioc D₀ D₁, rowE β d := by
      rw [WE_eq_sum_rowE]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        simp only [Finset.mem_Ioc] at hd ⊢
        exact ⟨hd.1, le_trans hd.2 hD1low⟩
      · intro d _ _; exact rowE_nonneg _ _
    have h := hunit D₀ R T β hD₀ hR hT hβ
    rw [Wdyad_eq_WboxI] at h
    have hnn : (0:ℝ) ≤ C₁ * Work.FIArea4.WTb D₀ R T ε := by
      rw [Work.FIArea4.WTb]; positivity
    calc WboxI R T (2*T) D₀ (2*D₀) β
        ≤ C₁ * Work.FIArea4.WTb D₀ R T ε * Work.FIArea4.WE D₀ β := h
      _ ≤ C₁ * Work.FIArea4.WTb D₀ R T ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d) :=
          mul_le_mul_of_nonneg_left hWE hnn
  -- the single extra modulus
  have htop : ∀ T : ℕ, (∑ r ∈ Finset.Ioc R (2*R), ∑ s ∈ Finset.Ioc T (2*T),
        Complex.normSq (Work.FIArea4.TZbox (2*D₀) D₁ β r s))
      ≤ (R:ℝ) * (((T:ℝ) / (D₁:ℝ)) + 1) * rowE β D₁ := by
    intro T
    rcases hDcase with hD1eq | hD1eq
    · rw [hD1eq]
      have hz : ∀ r s, Work.FIArea4.TZbox (2*D₀) (2*D₀) β r s = 0 := by
        intro r s; unfold Work.FIArea4.TZbox; simp
      have h0 : (∑ r ∈ Finset.Ioc R (2*R), ∑ s ∈ Finset.Ioc T (2*T),
          Complex.normSq (Work.FIArea4.TZbox (2*D₀) (2*D₀) β r s)) = 0 := by
        simp [hz]
      rw [h0]
      have h1 : (0:ℝ) ≤ (R:ℝ) := by positivity
      have h2 : (0:ℝ) ≤ ((T:ℝ) / ((2*D₀:ℕ):ℝ)) + 1 := by positivity
      have h3 : (0:ℝ) ≤ rowE β (2*D₀) := rowE_nonneg β _
      exact mul_nonneg (mul_nonneg h1 h2) h3
    · rw [hD1eq]
      have hkey : ∀ r s, Work.FIArea4.TZbox (2*D₀) (2*D₀+1) β r s = TZone (2*D₀+1) β r s :=
        fun r s => TZbox_succ_eq_TZone (2*D₀) β r s
      simp only [hkey]
      refine (TZone_energy_le (2*D₀+1) (by omega) β R T (2*T)).trans (le_of_eq ?_)
      have h2 : ((2*T - T : ℕ) : ℝ) = (T:ℝ) := by
        rw [show 2 * T - T = T from by omega]
      rw [h2]
  -- each dyadic s-box
  have hbox : ∀ T : ℕ, 1 ≤ T → WboxI R T (2*T) D₀ D₁ β
      ≤ 2 * (C₁ * Work.FIArea4.WTb D₀ R T ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))
        + 2 * ((R:ℝ) * (((T:ℝ)/(D₁:ℝ)) + 1) * rowE β D₁) := by
    intro T hT
    have hpoint : ∀ r s, Complex.normSq (Work.FIArea4.TZbox D₀ D₁ β r s)
        ≤ 2 * Complex.normSq (Work.FIArea4.TZbox D₀ (2*D₀) β r s)
          + 2 * Complex.normSq (Work.FIArea4.TZbox (2*D₀) D₁ β r s) := by
      intro r s
      rw [TZbox_add D₀ (2*D₀) D₁ β (by omega) hD1low r s]
      exact normSq_add_le_two _ _
    have hstep1 : WboxI R T (2*T) D₀ D₁ β ≤ 2 * WboxI R T (2*T) D₀ (2*D₀) β
        + 2 * (∑ r ∈ Finset.Ioc R (2*R), ∑ s ∈ Finset.Ioc T (2*T),
            Complex.normSq (Work.FIArea4.TZbox (2*D₀) D₁ β r s)) := by
      unfold WboxI
      calc (∑ r ∈ Finset.Ioc R (2*R), ∑ s ∈ Finset.Ioc T (2*T),
              Complex.normSq (Work.FIArea4.TZbox D₀ D₁ β r s))
          ≤ ∑ r ∈ Finset.Ioc R (2*R), ∑ s ∈ Finset.Ioc T (2*T),
              (2 * Complex.normSq (Work.FIArea4.TZbox D₀ (2*D₀) β r s)
                + 2 * Complex.normSq (Work.FIArea4.TZbox (2*D₀) D₁ β r s)) :=
            Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun s _ => hpoint r s))
        _ = 2 * (∑ r ∈ Finset.Ioc R (2*R), ∑ s ∈ Finset.Ioc T (2*T),
              Complex.normSq (Work.FIArea4.TZbox D₀ (2*D₀) β r s))
            + 2 * (∑ r ∈ Finset.Ioc R (2*R), ∑ s ∈ Finset.Ioc T (2*T),
              Complex.normSq (Work.FIArea4.TZbox (2*D₀) D₁ β r s)) := by
            simp only [Finset.sum_add_distrib, Finset.mul_sum]
    calc WboxI R T (2*T) D₀ D₁ β
        ≤ 2 * WboxI R T (2*T) D₀ (2*D₀) β
          + 2 * (∑ r ∈ Finset.Ioc R (2*R), ∑ s ∈ Finset.Ioc T (2*T),
              Complex.normSq (Work.FIArea4.TZbox (2*D₀) D₁ β r s)) := hstep1
      _ ≤ 2 * (C₁ * Work.FIArea4.WTb D₀ R T ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))
          + 2 * ((R:ℝ) * (((T:ℝ)/(D₁:ℝ)) + 1) * rowE β D₁) := by
          linarith [hhunit T hT, htop T]
  -- the s-window cover
  have hcover : WboxI R S₀ S₁ D₀ D₁ β
      ≤ WboxI R S₀ (2*S₀) D₀ D₁ β + WboxI R (S₀+1) (2*(S₀+1)) D₀ D₁ β := by
    unfold WboxI
    have hper : ∀ r ∈ Finset.Ioc R (2*R),
        (∑ s ∈ Finset.Ioc S₀ S₁, Complex.normSq (Work.FIArea4.TZbox D₀ D₁ β r s))
        ≤ (∑ s ∈ Finset.Ioc S₀ (2*S₀), Complex.normSq (Work.FIArea4.TZbox D₀ D₁ β r s))
          + ∑ s ∈ Finset.Ioc (S₀+1) (2*(S₀+1)), Complex.normSq (Work.FIArea4.TZbox D₀ D₁ β r s) := by
      intro r _
      have hsub : Finset.Ioc S₀ S₁ ⊆ Finset.Ioc S₀ (2*S₀) ∪ Finset.Ioc (S₀+1) (2*(S₀+1)) := by
        intro s hs
        simp only [Finset.mem_Ioc, Finset.mem_union] at hs ⊢
        rcases hScase with h | h <;> omega
      calc (∑ s ∈ Finset.Ioc S₀ S₁, Complex.normSq (Work.FIArea4.TZbox D₀ D₁ β r s))
          ≤ ∑ s ∈ Finset.Ioc S₀ (2*S₀) ∪ Finset.Ioc (S₀+1) (2*(S₀+1)),
              Complex.normSq (Work.FIArea4.TZbox D₀ D₁ β r s) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Complex.normSq_nonneg _)
        _ ≤ (∑ s ∈ Finset.Ioc S₀ (2*S₀), Complex.normSq (Work.FIArea4.TZbox D₀ D₁ β r s))
              + ∑ s ∈ Finset.Ioc (S₀+1) (2*(S₀+1)), Complex.normSq (Work.FIArea4.TZbox D₀ D₁ β r s) :=
            sum_union_le' _ _ _ (fun i => Complex.normSq_nonneg _)
    calc (∑ r ∈ Finset.Ioc R (2*R), ∑ s ∈ Finset.Ioc S₀ S₁, Complex.normSq (Work.FIArea4.TZbox D₀ D₁ β r s))
        ≤ ∑ r ∈ Finset.Ioc R (2*R),
            ((∑ s ∈ Finset.Ioc S₀ (2*S₀), Complex.normSq (Work.FIArea4.TZbox D₀ D₁ β r s))
              + ∑ s ∈ Finset.Ioc (S₀+1) (2*(S₀+1)), Complex.normSq (Work.FIArea4.TZbox D₀ D₁ β r s)) :=
          Finset.sum_le_sum hper
      _ = (∑ r ∈ Finset.Ioc R (2*R), ∑ s ∈ Finset.Ioc S₀ (2*S₀), Complex.normSq (Work.FIArea4.TZbox D₀ D₁ β r s))
            + ∑ r ∈ Finset.Ioc R (2*R), ∑ s ∈ Finset.Ioc (S₀+1) (2*(S₀+1)), Complex.normSq (Work.FIArea4.TZbox D₀ D₁ β r s) :=
          Finset.sum_add_distrib
  have hb1 := hbox S₀ hS₀
  have hb2 := hbox (S₀+1) (by omega)
  have hw1 : Work.FIArea4.WTb D₀ R S₀ ε ≤ 2 * Work.FIArea4.braceV D₀ R S₀ ε :=
    WTb_le_two_braceV D₀ R S₀ ε hR hS₀
  have hsc : Work.FIArea4.braceV D₀ R (S₀+1) ε ≤ (2:ℝ)^(2+ε) * Work.FIArea4.braceV D₀ R S₀ ε :=
    braceV_le_two_mul_S_of D₀ R S₀ (S₀+1) ε hε hS₀ (by omega)
  have hw2 : Work.FIArea4.WTb D₀ R (S₀+1) ε ≤ 2 * ((2:ℝ)^(2+ε) * Work.FIArea4.braceV D₀ R S₀ ε) := by
    have h1 := WTb_le_two_braceV D₀ R (S₀+1) ε hR (by omega)
    have h2 := mul_le_mul_of_nonneg_left hsc (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have hFs : (R:ℝ) * ((S₀:ℝ) / Real.sqrt (D₀:ℝ)) ≤ Work.FIArea4.braceV D₀ R S₀ ε := by
    have h3 : (R:ℝ) * ((S₀:ℝ) / Real.sqrt (D₀:ℝ)) = (D₀:ℝ)^(-(1:ℝ)/2) * (R:ℝ) * (S₀:ℝ) := by
      rw [rpow_neg_half_mul']; ring
    rw [h3]
    unfold Work.FIArea4.braceV
    have hB : (0:ℝ) ≤ ((D₀:ℝ) * Real.sqrt ((R:ℝ)*(S₀:ℝ)) + (R:ℝ) * (S₀:ℝ)^((3:ℝ)/4)
        + (S₀:ℝ) * (R:ℝ)^((3:ℝ)/4)) * ((R:ℝ)*(S₀:ℝ))^ε := by positivity
    linarith
  have hR1 : (R:ℝ) * (((S₀:ℝ)/(D₁:ℝ)) + 1) ≤ 2 * Work.FIArea4.braceV D₀ R S₀ ε := by
    have hAD : (S₀:ℝ) / (D₁:ℝ) ≤ (S₀:ℝ) / Real.sqrt (D₀:ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hsqpos hsd
    have h3 : (R:ℝ) * ((S₀:ℝ)/(D₁:ℝ)) ≤ (R:ℝ) * ((S₀:ℝ)/Real.sqrt (D₀:ℝ)) :=
      mul_le_mul_of_nonneg_left hAD hRnn
    have h4 : (R:ℝ) ≤ Work.FIArea4.braceV D₀ R S₀ ε := R_le_braceV D₀ R S₀ ε hε0 hR hS₀
    have h2 : (R:ℝ) * (((S₀:ℝ)/(D₁:ℝ)) + 1) = (R:ℝ) * ((S₀:ℝ)/(D₁:ℝ)) + (R:ℝ) := by ring
    linarith [h2.le, h2.ge, h3, hFs, h4]
  have hR2 : (R:ℝ) * ((((S₀+1:ℕ):ℝ)/(D₁:ℝ)) + 1) ≤ 3 * Work.FIArea4.braceV D₀ R S₀ ε := by
    have hS1 : (1:ℝ) ≤ (S₀:ℝ) := by exact_mod_cast hS₀
    have hS0p1 : ((S₀+1:ℕ):ℝ) ≤ 2 * (S₀:ℝ) := by push_cast; linarith
    have hAD : ((S₀+1:ℕ):ℝ) / (D₁:ℝ) ≤ 2 * ((S₀:ℝ) / Real.sqrt (D₀:ℝ)) := by
      calc ((S₀+1:ℕ):ℝ) / (D₁:ℝ) ≤ (2 * (S₀:ℝ)) / (D₁:ℝ) :=
            div_le_div_of_nonneg_right hS0p1 (by positivity)
        _ ≤ (2 * (S₀:ℝ)) / Real.sqrt (D₀:ℝ) :=
            div_le_div_of_nonneg_left (by positivity) hsqpos hsd
        _ = 2 * ((S₀:ℝ) / Real.sqrt (D₀:ℝ)) := by ring
    have h3 : (R:ℝ) * (((S₀+1:ℕ):ℝ)/(D₁:ℝ)) ≤ 2 * ((R:ℝ) * ((S₀:ℝ)/Real.sqrt (D₀:ℝ))) := by
      have := mul_le_mul_of_nonneg_left hAD hRnn
      linarith [this]
    have h4 : (R:ℝ) ≤ Work.FIArea4.braceV D₀ R S₀ ε := R_le_braceV D₀ R S₀ ε hε0 hR hS₀
    have h2 : (R:ℝ) * ((((S₀+1:ℕ):ℝ)/(D₁:ℝ)) + 1)
        = (R:ℝ) * (((S₀+1:ℕ):ℝ)/(D₁:ℝ)) + (R:ℝ) := by ring
    linarith [h2.le, h2.ge, h3, hFs, h4]
  have hE1 : C₁ * Work.FIArea4.WTb D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)
      ≤ 2 * C₁ * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)) := by
    have h := mul_le_mul_of_nonneg_left hw1 hC₁.le
    have h2 := mul_le_mul_of_nonneg_right h hEnn
    nlinarith [h2]
  have hc0 : (0:ℝ) ≤ (2:ℝ)^(2+ε) := by positivity
  have hE2 : C₁ * Work.FIArea4.WTb D₀ R (S₀+1) ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)
      ≤ 2 * C₁ * ((2:ℝ)^(2+ε) * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))) := by
    have h := mul_le_mul_of_nonneg_left hw2 hC₁.le
    have h2 := mul_le_mul_of_nonneg_right h hEnn
    nlinarith [h2]
  have hF1 : (R:ℝ) * ((S₀:ℝ)/(D₁:ℝ) + 1) * rowE β D₁
      ≤ 2 * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)) := by
    have h := mul_le_mul hR1 hrowD1 (rowE_nonneg β D₁) (by positivity)
    nlinarith [h]
  have hF2 : (R:ℝ) * (((S₀+1:ℕ):ℝ)/(D₁:ℝ) + 1) * rowE β D₁
      ≤ 3 * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)) := by
    have h := mul_le_mul hR2 hrowD1 (rowE_nonneg β D₁) (by positivity)
    nlinarith [h]
  have g1 : 2 * (C₁ * Work.FIArea4.WTb D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))
      ≤ 2 * (2 * C₁ * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))) :=
    by linarith [hE1]
  have g2 : 2 * ((R:ℝ) * (((S₀:ℝ)/(D₁:ℝ)) + 1) * rowE β D₁)
      ≤ 2 * (2 * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))) :=
    by linarith [hF1]
  have g3 : 2 * (C₁ * Work.FIArea4.WTb D₀ R (S₀+1) ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))
      ≤ 2 * (2 * C₁ * ((2:ℝ)^(2+ε) * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)))) :=
    by linarith [hE2]
  have g4 : 2 * ((R:ℝ) * ((((S₀+1:ℕ):ℝ)/(D₁:ℝ)) + 1) * rowE β D₁)
      ≤ 2 * (3 * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))) :=
    by linarith [hF2]
  have g5 : 2 * (2 * C₁ * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)))
        + 2 * (2 * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)))
        + 2 * (2 * C₁ * ((2:ℝ)^(2+ε) * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))))
        + 2 * (3 * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)))
      ≤ (4 * C₁ + 4 * C₁ * (2:ℝ)^(2+ε) + 10)
        * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)) := by
    have h1 : 2 * (2 * C₁ * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)))
        = 4 * C₁ * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)) := by ring
    have h2 : 2 * (2 * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)))
        = 4 * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)) := by ring
    have h3 : 2 * (2 * C₁ * ((2:ℝ)^(2+ε) * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))))
        = 4 * C₁ * (2:ℝ)^(2+ε) * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)) := by ring
    have h4 : 2 * (3 * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)))
        = 6 * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)) := by ring
    have h5 : 4 * C₁ * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))
        + 4 * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))
        + 4 * C₁ * (2:ℝ)^(2+ε) * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))
        + 6 * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))
        = (4 * C₁ + 4 * C₁ * (2:ℝ)^(2+ε) + 10)
          * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)) := by ring
    linarith [h1, h2, h3, h4, h5]
  have g6 : (4 * C₁ + 4 * C₁ * (2:ℝ)^(2+ε) + 10)
        * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))
      ≤ (8 * C₁ + 8 * C₁ * (2:ℝ)^(2+ε) + 10) * Work.FIArea4.braceV D₀ R S₀ ε
          * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d) := by
    have h1 : (4 * C₁ + 4 * C₁ * (2:ℝ)^(2+ε) + 10) ≤ (8 * C₁ + 8 * C₁ * (2:ℝ)^(2+ε) + 10) := by
      nlinarith [hC₁.le, hc0]
    have h2 := mul_le_mul_of_nonneg_right h1 hBEnn
    have h3 : (8 * C₁ + 8 * C₁ * (2:ℝ)^(2+ε) + 10)
        * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))
        = (8 * C₁ + 8 * C₁ * (2:ℝ)^(2+ε) + 10) * Work.FIArea4.braceV D₀ R S₀ ε
          * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d) := by ring
    linarith [h2, h3.le, h3.ge]
  calc WboxI R S₀ S₁ D₀ D₁ β
      ≤ WboxI R S₀ (2*S₀) D₀ D₁ β + WboxI R (S₀+1) (2*(S₀+1)) D₀ D₁ β := hcover
    _ ≤ (2 * (C₁ * Work.FIArea4.WTb D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))
          + 2 * ((R:ℝ) * (((S₀:ℝ)/(D₁:ℝ)) + 1) * rowE β D₁))
        + (2 * (C₁ * Work.FIArea4.WTb D₀ R (S₀+1) ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d))
          + 2 * ((R:ℝ) * ((((S₀+1:ℕ):ℝ)/(D₁:ℝ)) + 1) * rowE β D₁)) := by
        have := add_le_add hb1 hb2
        linarith [this]
    _ ≤ (4 * C₁ + 4 * C₁ * (2:ℝ)^(2+ε) + 10)
          * (Work.FIArea4.braceV D₀ R S₀ ε * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d)) := by
        linarith [g1, g2, g3, g4, g5]
    _ ≤ (8 * C₁ + 8 * C₁ * (2:ℝ)^(2+ε) + 10) * Work.FIArea4.braceV D₀ R S₀ ε
          * (∑ d ∈ Finset.Ioc D₀ D₁, rowE β d) := g6


/-- The single extra modulus `D₁ ∈ {2D₀, 2D₀+1}` at the single `s`-value `s = 1`. -/
lemma TZtop_one_le (D₀ D₁ R : ℕ) (β : ℕ → ℕ → ℂ) (hD₀ : 1 ≤ D₀)
    (hDcase : D₁ = 2 * D₀ ∨ D₁ = 2 * D₀ + 1) :
    (∑ r ∈ Finset.Ioc R (2*R), Complex.normSq (Work.FIArea4.TZbox (2*D₀) D₁ β r 1))
      ≤ (R:ℝ) * (((1:ℝ)/(D₁:ℝ)) + 1) * rowE β D₁ := by
  rcases hDcase with hD1eq | hD1eq
  · rw [hD1eq]
    have hz : ∀ r, Work.FIArea4.TZbox (2*D₀) (2*D₀) β r 1 = 0 := by
      intro r; unfold Work.FIArea4.TZbox; simp
    have h0 : (∑ r ∈ Finset.Ioc R (2*R), Complex.normSq (Work.FIArea4.TZbox (2*D₀) (2*D₀) β r 1)) = 0 := by
      simp [hz]
    rw [h0]
    have h1 : (0:ℝ) ≤ (R:ℝ) := by positivity
    have h2 : (0:ℝ) ≤ ((1:ℝ) / ((2*D₀:ℕ):ℝ)) + 1 := by positivity
    have h3 : (0:ℝ) ≤ rowE β (2*D₀) := rowE_nonneg β _
    exact mul_nonneg (mul_nonneg h1 h2) h3
  · rw [hD1eq]
    have h1 : (∑ r ∈ Finset.Ioc R (2*R), Complex.normSq (Work.FIArea4.TZbox (2*D₀) (2*D₀+1) β r 1))
        = ∑ r ∈ Finset.Ioc R (2*R), ∑ s ∈ Finset.Ioc 0 1,
            Complex.normSq (TZone (2*D₀+1) β r s) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_Ioc_succ_top (le_refl 0), Finset.Ioc_self, Finset.sum_empty, zero_add]
      rw [TZbox_succ_eq_TZone (2*D₀) β r 1]
    rw [h1]
    refine (TZone_energy_le (2*D₀+1) (by omega) β R 0 1).trans (le_of_eq ?_)
    have h2 : ((1 - 0 : ℕ) : ℝ) = (1:ℝ) := by norm_num
    rw [h2]

/-- The `e`-th stratum box form is bounded by `braceV` times the stratum energy. -/
theorem gamE_stratum_box_le (ε : ℝ) (hε : 0 < ε) (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hunit : ∀ (D₀ R S : ℕ) (β : ℕ → ℕ → ℂ), 1 ≤ D₀ → 1 ≤ R → 1 ≤ S →
      (∀ a d, β a d ≠ 0 → Nat.Coprime a d) →
      Work.FIArea4.Wdyad D₀ R S β ≤ C₁ * Work.FIArea4.WTb D₀ R S ε * Work.FIArea4.WE D₀ β) :
    ∃ K : ℝ, 0 < K ∧ ∀ (D R S e : ℕ) (γ : ℕ → ℕ → ℂ),
      1 ≤ D → 1 ≤ R → 1 ≤ S → S < R → 1 ≤ e →
      WboxI R (S / e) (2 * S / e) (D / e) (2 * D / e) (Work.FIArea4.gamE γ e)
        ≤ K * Work.FIArea4.braceV D R S ε * stratEn D e γ := by
  obtain ⟨Kb, hKb, hb⟩ := WboxI_almost_dyadic ε hε C₁ hC₁ hunit
  refine ⟨Kb * (1 + Real.sqrt 2) + 8, by positivity, ?_⟩
  intro D R S e γ hD hR hS hSR he
  have hepos : 0 < e := by omega
  have hε0 : (0:ℝ) ≤ ε := hε.le
  have hBnn : 0 ≤ Work.FIArea4.braceV D R S ε := braceV_nonneg D R S ε
  have hSEnn : 0 ≤ stratEn D e γ := stratEn_nonneg D e γ
  have hKpos : (0:ℝ) < Kb * (1 + Real.sqrt 2) + 8 := by
    have : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith
  have hK8 : (8:ℝ) ≤ Kb * (1 + Real.sqrt 2) + 8 := by
    have h2 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith
  have hgamE_unit : ∀ a d, Work.FIArea4.gamE γ e a d ≠ 0 → Nat.Coprime a d := by
    intro a d h
    by_contra hc
    simp only [Work.FIArea4.gamE] at h
    rw [if_neg hc] at h
    exact h rfl
  have hDcase : 2 * D / e = 2 * (D / e) ∨ 2 * D / e = 2 * (D / e) + 1 := two_mul_div_eq D e hepos
  have hScase : 2 * S / e = 2 * (S / e) ∨ 2 * S / e = 2 * (S / e) + 1 := two_mul_div_eq S e hepos
  have hD2 : 2 * (D/e) ≤ 2 * D / e := by rcases hDcase with h | h <;> omega
  have hS2 : 2 * (S/e) ≤ 2 * S / e := by rcases hScase with h | h <;> omega
  have hstratm : stratEn D e γ = ∑ d ∈ Finset.Ioc (D/e) (2*D/e), rowE (Work.FIArea4.gamE γ e) d := rfl
  have hKK := hKpos
  rcases Nat.eq_zero_or_pos (D / e) with hDe0 | hDepos
  · -- **Case C**: `e > D`, so `D₁ ∈ {0,1}`
    have hlt : D < e := by
      by_contra h
      have : 1 ≤ D / e := Nat.div_pos (by omega) hepos
      omega
    have hD1 : 2 * D / e = 0 ∨ 2 * D / e = 1 := by rcases hDcase with h | h <;> omega
    rcases hD1 with hD1z | hD1o
    · -- `D₁ = 0`: the modulus window is empty
      have hz : WboxI R (S/e) (2*S/e) 0 0 (Work.FIArea4.gamE γ e) = 0 := by
        unfold WboxI
        have h0 : ∀ r s, Complex.normSq (Work.FIArea4.TZbox 0 0 (Work.FIArea4.gamE γ e) r s) = 0 := by
          intro r s; unfold Work.FIArea4.TZbox; simp
        simp [h0]
      have hgoal : WboxI R (S/e) (2*S/e) (D/e) (2*D/e) (Work.FIArea4.gamE γ e) = 0 := by
        rw [hDe0, hD1z]; exact hz
      rw [hgoal]
      have : (0:ℝ) ≤ (Kb * (1 + Real.sqrt 2) + 8) * Work.FIArea4.braceV D R S ε * stratEn D e γ :=
        mul_nonneg (mul_nonneg hKpos.le hBnn) hSEnn
      linarith
    · -- `D₁ = 1`: the class sum is a single term
      have hstrat' : stratEn D e γ = Complex.normSq (Work.FIArea4.gamE γ e 0 1) := by
        rw [hstratm, hDe0, hD1o]
        rw [Finset.sum_Ioc_succ_top (le_refl 0), Finset.Ioc_self, Finset.sum_empty, zero_add]
        simp [rowE]
      have hpt : ∀ r s, Complex.normSq (Work.FIArea4.TZbox 0 1 (Work.FIArea4.gamE γ e) r s)
          ≤ Complex.normSq (Work.FIArea4.gamE γ e 0 1) := by
        intro r s
        rw [TZbox_succ_eq_TZone 0]
        have h1 : TZone 1 (Work.FIArea4.gamE γ e) r s
            = Work.FIArea4.gamE γ e 0 1 * Work.FIArea4.Mentry 1 0 r s := by
          unfold TZone
          rw [Finset.sum_range_one]
        rw [h1, Complex.normSq_mul]
        have h2 := normSq_Mentry_le_one 1 0 r s
        have h3 : (0:ℝ) ≤ Complex.normSq (Work.FIArea4.gamE γ e 0 1) := Complex.normSq_nonneg _
        nlinarith [h2, h3]
      have hcard : 2 * S / e - S / e ≤ S / e + 1 := by rcases hScase with h | h <;> omega
      have hmain : WboxI R (S/e) (2*S/e) 0 1 (Work.FIArea4.gamE γ e)
          ≤ (R:ℝ) * (((S/e : ℕ):ℝ) + 1) * Complex.normSq (Work.FIArea4.gamE γ e 0 1) := by
        unfold WboxI
        calc (∑ r ∈ Finset.Ioc R (2*R), ∑ s ∈ Finset.Ioc (S/e) (2*S/e),
                Complex.normSq (Work.FIArea4.TZbox 0 1 (Work.FIArea4.gamE γ e) r s))
            ≤ ∑ r ∈ Finset.Ioc R (2*R), ∑ s ∈ Finset.Ioc (S/e) (2*S/e),
                Complex.normSq (Work.FIArea4.gamE γ e 0 1) :=
              Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun s _ => hpt r s))
          _ = (R:ℝ) * (((2*S/e - S/e : ℕ)):ℝ) * Complex.normSq (Work.FIArea4.gamE γ e 0 1) := by
              rw [Finset.sum_const, Finset.sum_const, Nat.card_Ioc, Nat.card_Ioc]
              rw [show 2*R - R = R from by omega]
              ring
          _ ≤ (R:ℝ) * (((S/e : ℕ):ℝ) + 1) * Complex.normSq (Work.FIArea4.gamE γ e 0 1) := by
              have h1 : (((2*S/e - S/e : ℕ)):ℝ) ≤ (((S/e : ℕ)):ℝ) + 1 := by
                exact_mod_cast hcard
              have h5 : (0:ℝ) ≤ (R:ℝ) := by positivity
              have h6 : (0:ℝ) ≤ Complex.normSq (Work.FIArea4.gamE γ e 0 1) := Complex.normSq_nonneg _
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h5) h6
      have hRm2 := R_mul_le_braceV D R S e (S/e) ε hε0 hD hR hS hlt (Nat.div_mul_le_self S e)
      have hgoal : WboxI R (S/e) (2*S/e) (D/e) (2*D/e) (Work.FIArea4.gamE γ e)
          ≤ (Kb * (1 + Real.sqrt 2) + 8) * Work.FIArea4.braceV D R S ε * stratEn D e γ := by
        rw [hDe0, hD1o]
        rw [hstrat']
        have h1 : (R:ℝ) * (((S/e : ℕ):ℝ) + 1) ≤ 2 * Work.FIArea4.braceV D R S ε := hRm2
        have h2 : (0:ℝ) ≤ Complex.normSq (Work.FIArea4.gamE γ e 0 1) := Complex.normSq_nonneg _
        have h3 := mul_le_mul_of_nonneg_right h1 h2
        have h4 : (2 * Work.FIArea4.braceV D R S ε) * Complex.normSq (Work.FIArea4.gamE γ e 0 1)
            ≤ (Kb * (1 + Real.sqrt 2) + 8) * Work.FIArea4.braceV D R S ε
                * Complex.normSq (Work.FIArea4.gamE γ e 0 1) := by
          apply mul_le_mul_of_nonneg_right _ h2
          nlinarith [hBnn, hK8]
        linarith [hmain, h3, h4]
      exact hgoal
  · rcases Nat.eq_zero_or_pos (S / e) with hSe0 | hSepos
    · -- **Case B**: `D/e ≥ 1`, `S/e = 0`, so `S₁ ∈ {0,1}`
      have hS1 : 2 * S / e = 0 ∨ 2 * S / e = 1 := by rcases hScase with h | h <;> omega
      rcases hS1 with hS1z | hS1o
      · have hgoal : WboxI R (S/e) (2*S/e) (D/e) (2*D/e) (Work.FIArea4.gamE γ e) = 0 := by
          rw [hSe0, hS1z]
          unfold WboxI
          simp
        rw [hgoal]
        have : (0:ℝ) ≤ (Kb * (1 + Real.sqrt 2) + 8) * Work.FIArea4.braceV D R S ε * stratEn D e γ :=
          mul_nonneg (mul_nonneg hKpos.le hBnn) hSEnn
        linarith
      · have hkey : WboxI R (S/e) (2*S/e) (D/e) (2*D/e) (Work.FIArea4.gamE γ e)
            = ∑ r ∈ Finset.Ioc R (2*R), Complex.normSq (Work.FIArea4.TZbox (D/e) (2*D/e) (Work.FIArea4.gamE γ e) r 1) := by
          rw [hSe0, hS1o]
          unfold WboxI
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_Ioc_succ_top (le_refl 0)]
          simp
        have hpoint : ∀ r, Complex.normSq (Work.FIArea4.TZbox (D/e) (2*D/e) (Work.FIArea4.gamE γ e) r 1)
            ≤ 2 * Complex.normSq (Work.FIArea4.TZbox (D/e) (2*(D/e)) (Work.FIArea4.gamE γ e) r 1)
              + 2 * Complex.normSq (Work.FIArea4.TZbox (2*(D/e)) (2*D/e) (Work.FIArea4.gamE γ e) r 1) := by
          intro r
          rw [TZbox_add (D/e) (2*(D/e)) (2*D/e) (Work.FIArea4.gamE γ e) (by omega) hD2 r 1]
          exact normSq_add_le_two _ _
        have hone := TZbox_one_bound hDepos R (Work.FIArea4.gamE γ e)
        have hWEle : Work.FIArea4.WE (D/e) (Work.FIArea4.gamE γ e) ≤ stratEn D e γ := by
          rw [hstratm, WE_eq_sum_rowE]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro d hd
            simp only [Finset.mem_Ioc] at hd ⊢
            exact ⟨hd.1, le_trans hd.2 hD2⟩
          · intro d _ _; exact rowE_nonneg (Work.FIArea4.gamE γ e) d
        have hrowle : rowE (Work.FIArea4.gamE γ e) (2*D/e) ≤ stratEn D e γ := by
          rw [hstratm]
          refine Finset.single_le_sum (f := fun d => rowE (Work.FIArea4.gamE γ e) d)
            (fun d _ => rowE_nonneg (Work.FIArea4.gamE γ e) d) (Finset.mem_Ioc.mpr ⟨?_, le_rfl⟩)
          omega
        have htopB := TZtop_one_le (D/e) (2*D/e) R (Work.FIArea4.gamE γ e) hDepos hDcase
        have hmain : (∑ r ∈ Finset.Ioc R (2*R), Complex.normSq (Work.FIArea4.TZbox (D/e) (2*D/e) (Work.FIArea4.gamE γ e) r 1))
            ≤ (2 * ((R:ℝ) + ((D/e : ℕ):ℝ)) + 2 * ((R:ℝ) * (((1:ℝ)/((2*D/e : ℕ):ℝ)) + 1))) * stratEn D e γ := by
          have hs1 : (∑ r ∈ Finset.Ioc R (2*R), Complex.normSq (Work.FIArea4.TZbox (D/e) (2*D/e) (Work.FIArea4.gamE γ e) r 1))
              ≤ 2 * (∑ r ∈ Finset.Ioc R (2*R), Complex.normSq (Work.FIArea4.TZbox (D/e) (2*(D/e)) (Work.FIArea4.gamE γ e) r 1))
                + 2 * (∑ r ∈ Finset.Ioc R (2*R), Complex.normSq (Work.FIArea4.TZbox (2*(D/e)) (2*D/e) (Work.FIArea4.gamE γ e) r 1)) := by
            calc (∑ r ∈ Finset.Ioc R (2*R), Complex.normSq (Work.FIArea4.TZbox (D/e) (2*D/e) (Work.FIArea4.gamE γ e) r 1))
                ≤ ∑ r ∈ Finset.Ioc R (2*R), (2 * Complex.normSq (Work.FIArea4.TZbox (D/e) (2*(D/e)) (Work.FIArea4.gamE γ e) r 1)
                    + 2 * Complex.normSq (Work.FIArea4.TZbox (2*(D/e)) (2*D/e) (Work.FIArea4.gamE γ e) r 1)) :=
                  Finset.sum_le_sum (fun r _ => hpoint r)
              _ = _ := by
                  simp only [Finset.sum_add_distrib, Finset.mul_sum]
          have hs2 : (∑ r ∈ Finset.Ioc R (2*R), Complex.normSq (Work.FIArea4.TZbox (D/e) (2*(D/e)) (Work.FIArea4.gamE γ e) r 1))
              ≤ ((R:ℝ) + ((D/e : ℕ):ℝ)) * stratEn D e γ := by
            have := hone
            rw [hstratm]
            refine this.trans ?_
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro d hd
              simp only [Finset.mem_Ioc] at hd ⊢
              exact ⟨hd.1, le_trans hd.2 hD2⟩
            · intro d _ _; exact rowE_nonneg (Work.FIArea4.gamE γ e) d
          have hs4 : (∑ r ∈ Finset.Ioc R (2*R), Complex.normSq (Work.FIArea4.TZbox (2*(D/e)) (2*D/e) (Work.FIArea4.gamE γ e) r 1))
              ≤ (R:ℝ) * (((1:ℝ)/((2*D/e : ℕ):ℝ)) + 1) * stratEn D e γ := by
            have := htopB
            refine this.trans ?_
            exact mul_le_mul_of_nonneg_left hrowle (by positivity)
          have h6 : (0:ℝ) ≤ ((R:ℝ) + ((D/e : ℕ):ℝ)) := by positivity
          have h7 : (0:ℝ) ≤ (R:ℝ) * (((1:ℝ)/((2*D/e : ℕ):ℝ)) + 1) := by positivity
          nlinarith [hs1, hs2, hs4, h6, h7]
        have hArith : (2 * ((R:ℝ) + ((D/e : ℕ):ℝ)) + 2 * ((R:ℝ) * (((1:ℝ)/((2*D/e : ℕ):ℝ)) + 1)))
            ≤ 8 * Work.FIArea4.braceV D R S ε := by
          have hRle := R_le_braceV D R S ε hε0 hR hS
          have hDle := D_le_braceV D R S ε hε0 hD hR hS
          have hDele : ((D/e : ℕ):ℝ) ≤ Work.FIArea4.braceV D R S ε := by
            have h1 : ((D/e : ℕ):ℝ) ≤ (D:ℝ) := by exact_mod_cast (Nat.div_le_self D e)
            linarith [hDle, h1]
          have hx1 : (1:ℝ) ≤ ((2*D/e : ℕ):ℝ) := by
            have h2 : 1 ≤ 2*D/e := by rcases hDcase with h | h <;> omega
            exact_mod_cast h2
          have hdiv1 : (1:ℝ) / ((2*D/e : ℕ):ℝ) ≤ 1 := by
            rw [div_le_one (by linarith : (0:ℝ) < ((2*D/e : ℕ):ℝ))]
            exact hx1
          have h1div : (R:ℝ) * (((1:ℝ)/((2*D/e : ℕ):ℝ)) + 1) ≤ 2 * (R:ℝ) := by
            have h1 : (R:ℝ) * (((1:ℝ)/((2*D/e : ℕ):ℝ)) + 1)
                = (R:ℝ) * ((1:ℝ)/((2*D/e : ℕ):ℝ)) + (R:ℝ) := by ring
            have h2 : (R:ℝ) * ((1:ℝ)/((2*D/e : ℕ):ℝ)) ≤ (R:ℝ) :=
              mul_le_of_le_one_right (by positivity) hdiv1
            linarith [h1.le, h1.ge, h2]
          linarith [hRle, hDele, h1div]
        have hgoal : WboxI R (S/e) (2*S/e) (D/e) (2*D/e) (Work.FIArea4.gamE γ e)
            ≤ (Kb * (1 + Real.sqrt 2) + 8) * Work.FIArea4.braceV D R S ε * stratEn D e γ := by
          rw [hkey]
          have h1 : (2 * ((R:ℝ) + ((D/e : ℕ):ℝ)) + 2 * ((R:ℝ) * (((1:ℝ)/((2*D/e : ℕ):ℝ)) + 1))) * stratEn D e γ
              ≤ (8 * Work.FIArea4.braceV D R S ε) * stratEn D e γ :=
            mul_le_mul_of_nonneg_right hArith hSEnn
          have h2 : (8 * Work.FIArea4.braceV D R S ε) * stratEn D e γ
              ≤ (Kb * (1 + Real.sqrt 2) + 8) * Work.FIArea4.braceV D R S ε * stratEn D e γ := by
            have h3 : (8 * Work.FIArea4.braceV D R S ε)
                ≤ (Kb * (1 + Real.sqrt 2) + 8) * Work.FIArea4.braceV D R S ε := by
              nlinarith [hK8, hBnn]
            exact mul_le_mul_of_nonneg_right h3 hSEnn
          linarith [hmain, h1, h2]
        exact hgoal
    · -- **Case A**: both windows are almost dyadic
      have hstep := hb (D/e) (2*D/e) (S/e) (2*S/e) R (Work.FIArea4.gamE γ e) hDepos hR hSepos
        (by rcases hDcase with h | h
            · exact Or.inl h
            · exact Or.inr h)
        (by rcases hScase with h | h
            · exact Or.inl h
            · exact Or.inr h) hgamE_unit
      have hstrat2 : (∑ d ∈ Finset.Ioc (D/e) (2*D/e), rowE (Work.FIArea4.gamE γ e) d)
          = stratEn D e γ := rfl
      rw [hstrat2] at hstep
      have hdiv := braceV_div_le D R S e ε hε0 hD hR hS he
      have h3 : Kb * Work.FIArea4.braceV (D/e) R (S/e) ε * stratEn D e γ
          ≤ Kb * ((1 + Real.sqrt 2) * Work.FIArea4.braceV D R S ε) * stratEn D e γ := by
        apply mul_le_mul_of_nonneg_right _ hSEnn
        exact mul_le_mul_of_nonneg_left hdiv hKb.le
      have h4 : Kb * ((1 + Real.sqrt 2) * Work.FIArea4.braceV D R S ε) * stratEn D e γ
          ≤ (Kb * (1 + Real.sqrt 2) + 8) * Work.FIArea4.braceV D R S ε * stratEn D e γ := by
        have h5 : Kb * ((1 + Real.sqrt 2) * Work.FIArea4.braceV D R S ε)
            ≤ (Kb * (1 + Real.sqrt 2) + 8) * Work.FIArea4.braceV D R S ε := by
          nlinarith [hBnn, hKpos]
        exact mul_le_mul_of_nonneg_right h5 hSEnn
      linarith [hstep, h3, h4]

/-- **The strata energy bound.**  Assuming the unit-class dual variance bound `hunit`
(Friedlander--Iwaniec (11.24), bracket `WTb`), the total energy of the `gcd = e` strata of a
coefficient matrix `γ` is bounded by the target bracket `braceV` times the energy `WE D γ`. -/
theorem Wdyad_strata_energy (ε : ℝ) (hε : 0 < ε) (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hunit : ∀ (D₀ R S : ℕ) (β : ℕ → ℕ → ℂ), 1 ≤ D₀ → 1 ≤ R → 1 ≤ S →
      (∀ a d, β a d ≠ 0 → Nat.Coprime a d) →
      Work.FIArea4.Wdyad D₀ R S β ≤ C₁ * Work.FIArea4.WTb D₀ R S ε * Work.FIArea4.WE D₀ β) :
    ∃ K : ℝ, 0 < K ∧ ∀ (D R S : ℕ) (γ : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S → S < R →
      (∑ e ∈ Finset.Ioc 0 (2 * D), ∑ r ∈ Finset.Ioc R (2 * R), ∑ s ∈ Finset.Ioc S (2 * S),
          Complex.normSq (Work.FIArea4.TZbox D (2 * D) (Work.FIArea4.gLift γ e) r s))
        ≤ K * Work.FIArea4.braceV D R S ε *
            (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
  obtain ⟨K₁, hK₁, hstat⟩ := gamE_stratum_box_le ε hε C₁ hC₁ hunit
  refine ⟨K₁, hK₁, ?_⟩
  intro D R S γ hD hR hS hSR
  have hstep1 : (∑ e ∈ Finset.Ioc 0 (2*D), ∑ r ∈ Finset.Ioc R (2*R), ∑ s ∈ Finset.Ioc S (2*S),
        Complex.normSq (Work.FIArea4.TZbox D (2*D) (Work.FIArea4.gLift γ e) r s))
      = ∑ e ∈ Finset.Ioc 0 (2*D), WboxI R S (2*S) D (2*D) (Work.FIArea4.gLift γ e) := rfl
  rw [hstep1]
  calc ∑ e ∈ Finset.Ioc 0 (2*D), WboxI R S (2*S) D (2*D) (Work.FIArea4.gLift γ e)
      ≤ ∑ e ∈ Finset.Ioc 0 (2*D),
          WboxI R (S/e) (2*S/e) (D/e) (2*D/e) (Work.FIArea4.gamE γ e) := by
        apply Finset.sum_le_sum
        intro e he
        exact gLift_stratum_le D R S e γ (by have := (Finset.mem_Ioc.mp he).1; omega)
    _ ≤ ∑ e ∈ Finset.Ioc 0 (2*D), K₁ * Work.FIArea4.braceV D R S ε * stratEn D e γ := by
        apply Finset.sum_le_sum
        intro e he
        exact hstat D R S e γ hD hR hS hSR (by have := (Finset.mem_Ioc.mp he).1; omega)
    _ = K₁ * Work.FIArea4.braceV D R S ε * ∑ e ∈ Finset.Ioc 0 (2*D), stratEn D e γ := by
        rw [Finset.mul_sum]
    _ ≤ K₁ * Work.FIArea4.braceV D R S ε * Work.FIArea4.WE D γ := by
        have h1 : (0:ℝ) ≤ K₁ * Work.FIArea4.braceV D R S ε :=
          mul_nonneg hK₁.le (braceV_nonneg D R S ε)
        exact mul_le_mul_of_nonneg_left (stratEn_sum_le_WE D γ) h1
    _ = K₁ * Work.FIArea4.braceV D R S ε *
          (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := rfl
end

end Work.FIArea4.WdyadGen
