import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MDBasic.nonneg_basic
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.EE_lower_all
import Submission.Work.HP.MDEstimates.Sigma2_caseF_44
import Submission.Work.HP.MDEstimates.Sigma2_44_I_hi
import Submission.Work.HP.MDEstimates.Sigma2_44_I_lo

set_option autoImplicit false
noncomputable section

open MvPolynomial Finset MeasureTheory
open scoped BigOperators

namespace Work.HP.MDEstimates
open Work.HP

lemma ballVol_pos_R (R : ℕ) (hR : 1 ≤ R) : 0 < ballVol R := by
  haveI : Nonempty (Fin R) := ⟨⟨0, by omega⟩⟩
  have hg : 0 < Real.sqrt Real.pi ^ R / Real.Gamma ((R : ℝ) / 2 + 1) := by
    have h1 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have h2 : 0 < Real.Gamma ((R : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    positivity
  have h := EuclideanSpace.volume_closedBall (Fin R) (0 : EuclideanSpace ℝ (Fin R)) 1
  simp only [Fintype.card_fin] at h
  have h2 : ballVol R = Real.sqrt Real.pi ^ R / Real.Gamma ((R : ℝ) / 2 + 1) := by
    unfold ballVol
    rw [h, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1), one_pow,
      ENNReal.toReal_ofReal (le_of_lt hg)]
    ring
  rw [h2]; exact hg

lemma zeta_tail_pos_R (m : ℕ) (hm : 1 < m) : 0 < ∑' k : ℕ, (1:ℝ) / ((k:ℝ)+1)^m := by
  have hsum : Summable (fun k : ℕ => (1:ℝ) / ((k:ℝ)+1)^m) := by
    have hf : Summable (fun j : ℕ => (1:ℝ) / (j:ℝ)^m) := Real.summable_one_div_nat_pow.mpr hm
    have := (summable_nat_add_iff (f := fun j : ℕ => (1:ℝ)/(j:ℝ)^m) 1).mpr hf
    simpa [Nat.cast_add, Nat.cast_one] using this
  exact Summable.tsum_pos hsum (fun i => by positivity) 0 (by norm_num)

lemma iotaDN_44_pos : 0 < iotaDN 4 4 := by
  have h6 : 6 ≤ NN 4 4 := Work.HP.six_le_NN 4 4 (by norm_num) (by norm_num)
  have hN : 1 ≤ NN 4 4 - 2 := by omega
  have hm : 1 < NN 4 4 - 2 := by omega
  unfold iotaDN
  have h1 := ballVol_pos_R (NN 4 4 - 2) hN
  have h2 := zeta_tail_pos_R (NN 4 4 - 2) hm
  exact div_pos h1 (mul_pos (by norm_num) h2)

def SFset (A B : ℝ) : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
  {p | p ∈ Omega 4 4 B ∧ ¬ (muXY 4 p.1 p.2 ≤ A) ∧
      dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) ^ 2
        ≤ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) * (eNorm p.1 * eNorm p.2)}

def SHset (A B : ℝ) : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
  {p | p ∈ Omega 4 4 B ∧ ¬ (muXY 4 p.1 p.2 ≤ A) ∧
      ¬ (dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) ^ 2
          ≤ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) * (eNorm p.1 * eNorm p.2)) ∧
      A ^ ((1 : ℝ) / 20) < dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ))}

def SLset (A B : ℝ) : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
  {p | p ∈ Omega 4 4 B ∧ ¬ (muXY 4 p.1 p.2 ≤ A) ∧
      ¬ (dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) ^ 2
          ≤ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) * (eNorm p.1 * eNorm p.2)) ∧
      dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ A ^ ((1 : ℝ) / 20)}

def Sset (A B : ℝ) : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
  {p | p ∈ Omega 4 4 B ∧ ¬ (muXY 4 p.1 p.2 ≤ A)}

lemma Sset_eq (A B : ℝ) : Sset A B = SFset A B ∪ (SHset A B ∪ SLset A B) := by
  ext p
  simp only [Sset, SFset, SHset, SLset, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hc : dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) ^ 2
        ≤ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) * (eNorm p.1 * eNorm p.2)
    · exact Or.inl ⟨h1, h2, hc⟩
    · by_cases hd : A ^ ((1 : ℝ) / 20) < dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ))
      · exact Or.inr (Or.inl ⟨h1, h2, hc, hd⟩)
      · exact Or.inr (Or.inr ⟨h1, h2, hc, not_lt.mp hd⟩)
  · rintro (⟨h1, h2, _⟩ | ⟨h1, h2, _, _⟩ | ⟨h1, h2, _, _⟩) <;> exact ⟨h1, h2⟩

lemma Sset_finite (A B : ℝ) : (Sset A B).Finite :=
  (MDBasic.finite_sets 4 4 A B (fun _ => True)).2.2.subset (fun p hp => hp.1)

lemma SFset_finite (A B : ℝ) : (SFset A B).Finite :=
  (Sset_finite A B).subset (fun p hp => ⟨hp.1, hp.2.1⟩)

lemma SHset_finite (A B : ℝ) : (SHset A B).Finite :=
  (Sset_finite A B).subset (fun p hp => ⟨hp.1, hp.2.1⟩)

lemma SLset_finite (A B : ℝ) : (SLset A B).Finite :=
  (Sset_finite A B).subset (fun p hp => ⟨hp.1, hp.2.1⟩)

lemma Sset_disj (A B : ℝ) : Disjoint (SFset A B) (SHset A B ∪ SLset A B) := by
  rw [Set.disjoint_left]
  rintro p ⟨_, _, hc⟩ (⟨_, _, hc', _⟩ | ⟨_, _, hc', _⟩) <;> exact hc' hc

lemma SH_SL_disj (A B : ℝ) : Disjoint (SHset A B) (SLset A B) := by
  rw [Set.disjoint_left]
  rintro p ⟨_, _, _, hd⟩ ⟨_, _, _, hd'⟩
  exact absurd (lt_of_le_of_lt hd' hd) (lt_irrefl _)

lemma Sigma2_eq_quarter_finsum (A B : ℝ) :
    Sigma2 4 4 A B = (1/4) * ∑ᶠ p ∈ Sset A B, pairS0 4 4 A p := by
  rfl

/-- Assembly: given the three regime estimates and the lower bound for `E_{4,4}`, the `(4,4)`
large-`μ` second moment obeys the `A^{-1/32}` bound. -/
lemma Sigma2_44_of_estimates (K₄ c : ℝ) (hc : 0 < c)
    (hEE : ∀ B : ℝ, K₄ ≤ B → c * B ^ 2 ≤ EE 4 4 B)
    (hF : ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      (∑ᶠ p ∈ SFset A B, pairS0 4 4 A p) ≤ K * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/3) * B ^ 2)
    (hH : ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      (∑ᶠ p ∈ SHset A B, pairS0 4 4 A p) ≤ K * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * B ^ 2)
    (hL : ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      (∑ᶠ p ∈ SLset A B, pairS0 4 4 A p) ≤ K * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * B ^ 2) :
    ∃ K B₀ : ℝ, ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      Sigma2 4 4 A B ≤ K * mainTerm 4 4 A B / A ^ ((1 : ℝ) / 32) := by
  obtain ⟨K₁, B₁, hK₁, hFb⟩ := hF
  obtain ⟨K₂, B₂, hK₂, hHb⟩ := hH
  obtain ⟨K₃, B₃, hK₃, hLb⟩ := hL
  refine ⟨(K₁ + K₂ + K₃) / (8 * iotaDN 4 4 * c) + 1,
      max (max (max B₁ B₂) (max B₃ K₄)) 3 + 1, ?_⟩
  intro A B hB hAB hAB2
  have hBm : max (max (max B₁ B₂) (max B₃ K₄)) 3 ≤ B :=
    le_trans (le_add_of_nonneg_right zero_le_one) hB
  have hBp : max (max B₁ B₂) (max B₃ K₄) ≤ B := le_trans (le_max_left _ 3) hBm
  have hBB₁ : B₁ ≤ B :=
    le_trans (le_trans (le_trans (le_max_left B₁ B₂)
      (le_max_left (max B₁ B₂) (max B₃ K₄))) hBp) (le_refl B)
  have hBB₂ : B₂ ≤ B :=
    le_trans (le_trans (le_trans (le_max_right B₁ B₂)
      (le_max_left (max B₁ B₂) (max B₃ K₄))) hBp) (le_refl B)
  have hBB₃ : B₃ ≤ B :=
    le_trans (le_trans (le_trans (le_max_left B₃ K₄)
      (le_max_right (max B₁ B₂) (max B₃ K₄))) hBp) (le_refl B)
  have hBBc : K₄ ≤ B :=
    le_trans (le_trans (le_trans (le_max_right B₃ K₄)
      (le_max_right (max B₁ B₂) (max B₃ K₄))) hBp) (le_refl B)
  have hB3 : (3:ℝ) ≤ B := le_trans (le_max_right _ 3) hBm
  have hBpos : 0 < B := by linarith
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hApos : 0 < A := lt_of_lt_of_le (div_pos hBpos hlogB) hAB
  have hA1 : 1 ≤ A := by
    have h1 : 1 ≤ B / Real.log B := by
      rw [le_div_iff₀ hlogB]
      nlinarith [Real.log_le_self hBpos.le]
    exact le_trans h1 hAB
  have hB1 : (1:ℝ) ≤ B := by linarith
  have hsplit : (∑ᶠ p ∈ Sset A B, pairS0 4 4 A p)
      = (∑ᶠ p ∈ SFset A B, pairS0 4 4 A p)
        + ((∑ᶠ p ∈ SHset A B, pairS0 4 4 A p) + (∑ᶠ p ∈ SLset A B, pairS0 4 4 A p)) := by
    rw [Sset_eq, finsum_mem_union (Sset_disj A B) (SFset_finite A B)
        ((SHset_finite A B).union (SLset_finite A B)),
      finsum_mem_union (SH_SL_disj A B) (SHset_finite A B) (SLset_finite A B)]
  have hbF := hFb A B hBB₁ hAB hAB2
  have hbH := hHb A B hBB₂ hAB hAB2
  have hbL := hLb A B hBB₃ hAB hAB2
  have hEE' := hEE B hBBc
  -- `A^{D-1/3} ≤ A^{D-1/32}` with `D = NN 4 4 - 2`
  have hpow_le : A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/3) ≤ A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) := by
    refine Real.rpow_le_rpow_of_exponent_le hA1 ?_
    linarith
  have hsum_le : (∑ᶠ p ∈ Sset A B, pairS0 4 4 A p)
      ≤ (K₁ + K₂ + K₃) * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * B ^ 2 := by
    rw [hsplit]
    have h1 : K₁ * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/3) * B ^ 2
        ≤ K₁ * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * B ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow_le (le_of_lt hK₁)) (sq_nonneg B)
    have h2 : K₂ * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * B ^ 2
        + K₃ * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * B ^ 2
        = (K₂ + K₃) * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * B ^ 2 := by ring
    linarith [hbF, hbH, hbL, h1, h2]
  -- the `E`-lower bound
  have hB2le : B ^ 2 ≤ EE 4 4 B / c := by
    rw [le_div_iff₀ hc]; linarith
  have hstep2 : (1/4) * ((K₁ + K₂ + K₃) * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * B ^ 2)
      ≤ (1/4) * ((K₁ + K₂ + K₃) * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * (EE 4 4 B / c)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact mul_le_mul_of_nonneg_left hB2le (mul_nonneg (by linarith) (Real.rpow_nonneg hApos.le _))
  have hstep3 : (1/4) * ((K₁ + K₂ + K₃) * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * (EE 4 4 B / c))
      = ((K₁ + K₂ + K₃) / (8 * iotaDN 4 4 * c)) *
          (2 * iotaDN 4 4 * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * EE 4 4 B) := by
    have hι := iotaDN_44_pos
    have hιne : iotaDN 4 4 ≠ 0 := ne_of_gt hι
    have hcne : c ≠ 0 := ne_of_gt hc
    field_simp
    ring
  have hmain : mainTerm 4 4 A B / A ^ ((1:ℝ)/32)
      = 2 * iotaDN 4 4 * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * EE 4 4 B := by
    have hnat : A ^ (NN 4 4 - 2) = A ^ ((NN 4 4 : ℝ) - 2) := by
      rw [← Real.rpow_natCast A (NN 4 4 - 2)]
      congr 1
      rw [Nat.cast_sub]
      · push_cast; ring
      · have h : 6 ≤ NN 4 4 := Work.HP.six_le_NN 4 4 (by norm_num) (by norm_num); omega
    have hAeq : A ^ (NN 4 4 - 2)
        = A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * A ^ ((1:ℝ)/32) := by
      have h₂ : ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) + (1:ℝ)/32 = (NN 4 4 : ℝ) - 2 := by ring
      calc A ^ (NN 4 4 - 2) = A ^ ((NN 4 4 : ℝ) - 2) := hnat
        _ = A ^ (((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) + (1:ℝ)/32) := by rw [h₂]
        _ = A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * A ^ ((1:ℝ)/32) :=
              Real.rpow_add hApos _ _
    rw [mainTerm, hAeq]
    have hA32 : A ^ ((1:ℝ)/32) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hApos _)
    field_simp
  have htarget : (0:ℝ) ≤ 2 * iotaDN 4 4 * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * EE 4 4 B := by
    have hEEnn : (0:ℝ) ≤ EE 4 4 B := le_trans (by positivity : (0:ℝ) ≤ c * B ^ 2) hEE'
    have hι := iotaDN_44_pos
    positivity
  rw [Sigma2_eq_quarter_finsum, mul_div_assoc, hmain]
  have hstep1 : (1/4) * (∑ᶠ p ∈ Sset A B, pairS0 4 4 A p)
      ≤ (1/4) * ((K₁ + K₂ + K₃) * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * B ^ 2) :=
    mul_le_mul_of_nonneg_left hsum_le (by norm_num)
  calc (1/4) * (∑ᶠ p ∈ Sset A B, pairS0 4 4 A p)
      ≤ (1/4) * ((K₁ + K₂ + K₃) * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * B ^ 2) := hstep1
    _ ≤ (1/4) * ((K₁ + K₂ + K₃) * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * (EE 4 4 B / c)) := hstep2
    _ = ((K₁ + K₂ + K₃) / (8 * iotaDN 4 4 * c)) *
          (2 * iotaDN 4 4 * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * EE 4 4 B) := hstep3
    _ ≤ ((K₁ + K₂ + K₃) / (8 * iotaDN 4 4 * c) + 1) *
          (2 * iotaDN 4 4 * A ^ ((NN 4 4 : ℝ) - 2 - (1:ℝ)/32) * EE 4 4 B) := by
        have hK : (0:ℝ) ≤ (K₁ + K₂ + K₃) / (8 * iotaDN 4 4 * c) := by
          have hι := iotaDN_44_pos
          positivity
        nlinarith [htarget, hK]

theorem Sigma2_44 :
    ∃ K B₀ : ℝ, ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      Sigma2 4 4 A B ≤ K * mainTerm 4 4 A B / A ^ ((1 : ℝ) / 32) := by
  obtain ⟨c, Bc, hc, hEEb⟩ := Work.HP.EE_lower_all 4 4 (by norm_num) (by norm_num) (by norm_num)
  exact Sigma2_44_of_estimates Bc c hc hEEb Sigma2_caseF_44 Sigma2_44_I_hi Sigma2_44_I_lo

end Work.HP.MDEstimates
