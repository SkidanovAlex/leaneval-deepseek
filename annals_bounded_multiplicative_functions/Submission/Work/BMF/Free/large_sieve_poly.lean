/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Large sieve for polynomial phases (MRTTZ, Prop. 3.3 / MRT Fourier, Lemma 2.2)

`Work.BMF.large_sieve_poly` is proved here, with the two inputs
`Work.BMF.weyl_structure` (structured inverse Weyl inequality at a base point, derived from the
inverse Weyl theorem `Work.BMF.weyl_inverse`) and `Work.BMF.large_sieve_moment` (the
Cauchy--Schwarz second moment reduction) imported from their own files.
-/
import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.Free.weyl_structure
import Submission.Work.BMF.large_sieve_moment

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

namespace Work.BMF.FreeLS

open Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions

/-! ## Elementary interval counting lemmas -/

lemma card_natIcc_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ((natIcc a b).card : ℝ) ≤ b - a + 1 := by
  have hb : 0 ≤ b := ha.trans hab
  rw [natIcc, Nat.card_Icc]
  have key : ⌊b⌋₊ ≤ ⌈a⌉₊ + ⌊b - a⌋₊ := by
    rcases le_or_gt ⌊b⌋₊ ⌈a⌉₊ with h | h
    · exact le_trans h (Nat.le_add_right _ _)
    · have hle : ⌈a⌉₊ ≤ ⌊b⌋₊ := le_of_lt h
      have hsub : (((⌊b⌋₊ - ⌈a⌉₊ : ℕ)) : ℝ) ≤ b - a := by
        rw [Nat.cast_sub hle]
        have h1 : ((⌊b⌋₊ : ℝ)) ≤ b := Nat.floor_le hb
        have h2 : a ≤ ((⌈a⌉₊ : ℝ)) := Nat.le_ceil a
        linarith
      have hsub2 : ⌊b⌋₊ - ⌈a⌉₊ ≤ ⌊b - a⌋₊ := Nat.le_floor hsub
      omega
  have h1 : (⌊b⌋₊ + 1 - ⌈a⌉₊ : ℕ) ≤ ⌊b - a⌋₊ + 1 := by omega
  calc (((⌊b⌋₊ + 1 - ⌈a⌉₊ : ℕ)) : ℝ) ≤ (((⌊b - a⌋₊ + 1 : ℕ)) : ℝ) := by exact_mod_cast h1
    _ = (⌊b - a⌋₊ : ℝ) + 1 := by push_cast; ring
    _ ≤ (b - a) + 1 := by linarith [Nat.floor_le (show (0:ℝ) ≤ b - a by linarith)]

lemma natIcc_inter (a b c d : ℝ) :
    natIcc a b ∩ natIcc c d = Finset.Icc (max ⌈a⌉₊ ⌈c⌉₊) (min ⌊b⌋₊ ⌊d⌋₊) := by
  ext n
  simp only [natIcc, Finset.mem_inter, Finset.mem_Icc, max_le_iff, le_min_iff]
  tauto

lemma natIcc_subset {a₁ a₂ b₁ b₂ : ℝ} (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
    natIcc a₁ b₁ ⊆ natIcc a₂ b₂ := by
  intro n hn
  simp only [natIcc, Finset.mem_Icc] at hn ⊢
  exact ⟨le_trans (Nat.ceil_mono ha) hn.1, le_trans hn.2 (Nat.floor_mono hb)⟩

/-- Expansion of a polynomial of degree `≤ k` in powers of `X - n₀`, with the Taylor
coefficients at `n₀`. -/
lemma eq_sum_C_taylor_coeff (k : ℕ) {R : ℝ[X]} (hR : R ∈ degreeLE ℝ (k : WithBot ℕ))
    (n₀ : ℕ) :
    R = ∑ l ∈ Finset.range (k + 1),
        Polynomial.C ((Polynomial.taylor (n₀ : ℝ) R).coeff l) *
          (Polynomial.X - Polynomial.C (n₀ : ℝ)) ^ l := by
  have hnd : R.natDegree ≤ k := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [Polynomial.mem_degreeLE, Polynomial.degree_le_iff_coeff_zero] at hR
    exact hR N (WithBot.coe_lt_coe.mpr hN)
  have hnd' : (Polynomial.taylor (n₀ : ℝ) R).natDegree ≤ k := by
    rw [Polynomial.natDegree_taylor]; exact hnd
  have hA : Polynomial.taylor (n₀ : ℝ) R
      = ∑ l ∈ Finset.range (k + 1),
          Polynomial.C ((Polynomial.taylor (n₀ : ℝ) R).coeff l) * Polynomial.X ^ l := by
    nth_rewrite 1 [Polynomial.as_sum_range_C_mul_X_pow (Polynomial.taylor (n₀ : ℝ) R)]
    refine Finset.sum_subset (Finset.range_mono ?_) ?_
    · exact Nat.succ_le_succ hnd'
    · intro x hx hx'
      simp only [Finset.mem_range] at hx hx'
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.C_0, zero_mul]
  have h1 : Polynomial.taylor (-(n₀ : ℝ)) (Polynomial.taylor (n₀ : ℝ) R) = R := by
    rw [Polynomial.taylor_taylor]; simp
  conv_lhs => rw [← h1, hA]
  rw [map_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Polynomial.C_mul', map_smul, Polynomial.taylor_X_pow, Polynomial.smul_eq_C_mul]
  congr 1
  rw [Polynomial.C_neg, sub_eq_add_neg]

lemma range_succ_eq_insert_Icc (k : ℕ) : Finset.range (k+1) = insert 0 (Finset.Icc 1 k) := by
  ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega

lemma abs_sub_div_le {a Q m C : ℝ} (hQ : 1 ≤ Q) (hC : 0 ≤ C) (h : |Q * a - m| ≤ C) :
    |a - m / Q| ≤ C := by
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have key : a - m / Q = (Q * a - m) / Q := by field_simp
  rw [key, abs_div, abs_of_pos hQpos]
  have h1 : |Q * a - m| / Q ≤ C / Q := by gcongr
  have h2 : C / Q ≤ C := by rw [div_le_iff₀ hQpos]; nlinarith
  linarith

lemma C_mul_X_sub_C_pow_mem (k l : ℕ) (hl : l ≤ k) (c a : ℝ) :
    Polynomial.C c * (Polynomial.X - Polynomial.C a) ^ l ∈ degreeLE ℝ (k : WithBot ℕ) := by
  rw [Polynomial.mem_degreeLE, Polynomial.degree_le_iff_coeff_zero]
  intro m hm
  have hmk : k < m := WithBot.coe_lt_coe.mp hm
  rw [Polynomial.coeff_C_mul]
  have hlt : ((Polynomial.X - Polynomial.C a) ^ l).natDegree < m := by
    calc ((Polynomial.X - Polynomial.C a) ^ l).natDegree
        ≤ l * (Polynomial.X - Polynomial.C a).natDegree := Polynomial.natDegree_pow_le
      _ = l := by rw [Polynomial.natDegree_X_sub_C, mul_one]
      _ < m := lt_of_le_of_lt hl hmk
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]

lemma exists_bounded_integral_of_coeffs (k : ℕ) (q : ℕ) (C_W δ₃ H : ℝ) (n₀ : ℕ) (M₁ M₂ : ℝ)
    (m₁ m₂ : ℕ → ℤ) {x L B : ℝ} {R₁ R₂ : ℝ[X]}
    (hq : 1 ≤ q) (hCW : 0 ≤ C_W) (hδ₃ : 0 < δ₃) (hH : 0 < H) (hB : 0 ≤ B)
    (hdeg₁ : R₁ ∈ degreeLE ℝ (k : WithBot ℕ)) (hdeg₂ : R₂ ∈ degreeLE ℝ (k : WithBot ℕ))
    (hM₁ : δ₃ * H ≤ M₁) (hM₂ : δ₃ * H ≤ M₂)
    (ha₁ : ∀ l ∈ Finset.range (k + 1),
      |(q : ℝ) * (Polynomial.taylor (n₀ : ℝ) R₁).coeff l - (m₁ l : ℝ)| ≤ C_W / M₁ ^ l)
    (ha₂ : ∀ l ∈ Finset.range (k + 1),
      |(q : ℝ) * (Polynomial.taylor (n₀ : ℝ) R₂).coeff l - (m₂ l : ℝ)| ≤ C_W / M₂ ^ l)
    (hmod : ∀ l ∈ Finset.Icc 1 k, (m₁ l) ≡ (m₂ l) [ZMOD (q : ℤ)])
    (hBt : ∀ t ∈ Set.Icc x (x + L), |t - (n₀ : ℝ)| ≤ B) :
    ∃ ε γ : ℝ[X], ε ∈ degreeLE ℝ (k : WithBot ℕ) ∧ γ ∈ degreeLE ℝ (k : WithBot ℕ) ∧
        R₁ - R₂ = ε + γ ∧
        (∀ t ∈ Set.Icc x (x + L),
          |ε.eval t| ≤ 1/2 + ∑ l ∈ Finset.Icc 1 k, 2 * C_W * (B / (δ₃ * H)) ^ l) ∧
        IntegralOn 1 γ := by
  have hδH : 0 < δ₃ * H := mul_pos hδ₃ hH
  have hdvd : ∀ l ∈ Finset.Icc 1 k, ∃ c : ℤ, m₁ l - m₂ l = (q : ℤ) * c := by
    intro l hl
    have h := hmod l hl
    rw [Int.modEq_iff_dvd] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨-c, by rw [← neg_sub (m₂ l) (m₁ l), hc]; ring⟩
  let γc : ℕ → ℤ := fun l => if h : l ∈ Finset.Icc 1 k then Classical.choose (hdvd l h) else 0
  have hγc : ∀ l (hl : l ∈ Finset.Icc 1 k), m₁ l - m₂ l = (q : ℤ) * γc l := by
    intro l hl
    simp only [γc, dif_pos hl]
    exact Classical.choose_spec (hdvd l hl)
  set α₁ : ℕ → ℝ := fun l => (Polynomial.taylor (n₀ : ℝ) R₁).coeff l with hα₁
  set α₂ : ℕ → ℝ := fun l => (Polynomial.taylor (n₀ : ℝ) R₂).coeff l with hα₂
  set γ₀ : ℤ := ⌊α₁ 0 - α₂ 0 + 1/2⌋ with hγ₀
  have hγ₀b : |α₁ 0 - α₂ 0 - (γ₀ : ℝ)| ≤ 1/2 := by
    have h2 : ((γ₀ : ℤ) : ℝ) ≤ α₁ 0 - α₂ 0 + 1/2 := by
      rw [hγ₀]; exact Int.floor_le _
    have h3 : α₁ 0 - α₂ 0 + 1/2 < ((γ₀ : ℤ) : ℝ) + 1 := by
      rw [hγ₀]; exact Int.lt_floor_add_one _
    rw [abs_le]; constructor <;> linarith
  let γf : ℕ → ℤ := fun l => if h : l = 0 then γ₀ else γc l
  have hγf0 : γf 0 = γ₀ := by simp only [γf, dif_pos rfl]
  have hγfl : ∀ l (hl : l ∈ Finset.Icc 1 k), γf l = γc l := by
    intro l hl
    have hl0 : l ≠ 0 := by rintro rfl; exact absurd (Finset.mem_Icc.mp hl).1 (by norm_num)
    simp only [γf, dif_neg hl0]
  let εf : ℕ → ℝ := fun l => α₁ l - α₂ l - (γf l : ℝ)
  have hε0 : |εf 0| ≤ 1/2 := by
    have h0 : εf 0 = α₁ 0 - α₂ 0 - (γ₀ : ℝ) := by
      simp only [εf, hγf0]
    rw [h0]; exact hγ₀b
  have hQ1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hQpos : (0:ℝ) < (q:ℝ) := lt_of_lt_of_le zero_lt_one hQ1
  have hεl : ∀ l ∈ Finset.Icc 1 k, |εf l| ≤ 2 * C_W / (δ₃ * H) ^ l := by
    intro l hl
    obtain ⟨hl1, hlk⟩ := Finset.mem_Icc.mp hl
    have hl0 : l ≠ 0 := by omega
    have hlrange : l ∈ Finset.range (k + 1) := by rw [Finset.mem_range]; omega
    have hrel := hγc l hl
    have hrel' : ((m₁ l : ℝ) - (m₂ l : ℝ)) = (q:ℝ) * (γc l : ℝ) := by
      have hcast := congrArg (fun z : ℤ => (z : ℝ)) hrel
      push_cast at hcast
      simpa using hcast
    have hqε : (q:ℝ) * εf l
        = ((q:ℝ) * α₁ l - (m₁ l : ℝ)) - ((q:ℝ) * α₂ l - (m₂ l : ℝ)) := by
      have hγfl' := hγfl l hl
      simp only [εf, dif_neg hl0, hγfl']
      push_cast
      nlinarith [hrel']
    have h1 := ha₁ l hlrange
    have h2 := ha₂ l hlrange
    have hM1pos : 0 < M₁ := lt_of_lt_of_le hδH hM₁
    have hM2pos : 0 < M₂ := lt_of_lt_of_le hδH hM₂
    have hpow1 : 0 < M₁ ^ l := pow_pos hM1pos l
    have hpow2 : 0 < M₂ ^ l := pow_pos hM2pos l
    have hDnn : 0 ≤ C_W / M₁^l + C_W / M₂^l :=
      add_nonneg (div_nonneg hCW hpow1.le) (div_nonneg hCW hpow2.le)
    have hkey : (q:ℝ) * |εf l| = |((q:ℝ) * α₁ l - (m₁ l : ℝ)) - ((q:ℝ) * α₂ l - (m₂ l : ℝ))| := by
      rw [← hqε, abs_mul, abs_of_pos hQpos]
    have hstep : (q:ℝ) * |εf l| ≤ C_W / M₁^l + C_W / M₂^l := by
      rw [hkey]
      calc |((q:ℝ) * α₁ l - (m₁ l : ℝ)) - ((q:ℝ) * α₂ l - (m₂ l : ℝ))|
          ≤ |(q:ℝ) * α₁ l - (m₁ l : ℝ)| + |(q:ℝ) * α₂ l - (m₂ l : ℝ)| := abs_sub _ _
        _ ≤ C_W / M₁^l + C_W / M₂^l := add_le_add h1 h2
    have hquot : |εf l| ≤ C_W / M₁^l + C_W / M₂^l := by
      have hqd : |εf l| ≤ (C_W / M₁^l + C_W / M₂^l) / (q:ℝ) := by
        rw [le_div_iff₀ hQpos, mul_comm]
        exact hstep
      calc |εf l| ≤ (C_W / M₁^l + C_W / M₂^l) / (q:ℝ) := hqd
        _ ≤ C_W / M₁^l + C_W / M₂^l := by
              rw [div_le_iff₀ hQpos]; nlinarith [hQ1, hDnn]
    refine le_trans hquot ?_
    have hle1 : C_W / M₁^l ≤ C_W / (δ₃*H)^l :=
      div_le_div_of_nonneg_left hCW (pow_pos hδH l) (pow_le_pow_left₀ hδH.le hM₁ l)
    have hle2 : C_W / M₂^l ≤ C_W / (δ₃*H)^l :=
      div_le_div_of_nonneg_left hCW (pow_pos hδH l) (pow_le_pow_left₀ hδH.le hM₂ l)
    have htwo : C_W / (δ₃*H)^l + C_W / (δ₃*H)^l = 2 * C_W / (δ₃*H)^l := by ring_nf
    linarith [hle1, hle2, htwo]
  set Q : ℕ → ℝ[X] := fun l => (Polynomial.X - Polynomial.C (n₀ : ℝ)) ^ l with hQ
  set εP : ℝ[X] := ∑ l ∈ Finset.range (k+1), Polynomial.C (εf l) * Q l with hεP
  set γP : ℝ[X] := ∑ l ∈ Finset.range (k+1), Polynomial.C ((γf l : ℝ)) * Q l with hγP
  have hmemεP : εP ∈ degreeLE ℝ (k : WithBot ℕ) := by
    rw [hεP]
    refine Submodule.sum_mem _ fun l hl => ?_
    rw [Finset.mem_range] at hl
    exact C_mul_X_sub_C_pow_mem k l (by omega) _ _
  have hmemγP : γP ∈ degreeLE ℝ (k : WithBot ℕ) := by
    rw [hγP]
    refine Submodule.sum_mem _ fun l hl => ?_
    rw [Finset.mem_range] at hl
    exact C_mul_X_sub_C_pow_mem k l (by omega) _ _
  have hcoef : ∀ l, α₁ l - α₂ l = εf l + (γf l : ℝ) := by
    intro l; simp only [εf]; ring
  have heq : R₁ - R₂ = εP + γP := by
    rw [eq_sum_C_taylor_coeff k hdeg₁ n₀, eq_sum_C_taylor_coeff k hdeg₂ n₀, hεP, hγP]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [← sub_mul, ← Polynomial.C_sub, ← add_mul, ← Polynomial.C_add, hcoef l]
  have hεeval : ∀ t : ℝ, εP.eval t = ∑ l ∈ Finset.range (k+1), εf l * (t - (n₀ : ℝ))^l := by
    intro t
    simp only [hεP, hQ, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X]
  have hεbound : ∀ t ∈ Set.Icc x (x + L),
      |εP.eval t| ≤ 1/2 + ∑ l ∈ Finset.Icc 1 k, 2 * C_W * (B / (δ₃ * H)) ^ l := by
    intro t ht
    have htB : |t - (n₀:ℝ)| ≤ B := hBt t ht
    have htB' : 0 ≤ |t - (n₀:ℝ)| := abs_nonneg _
    have h1 : |∑ l ∈ Finset.range (k+1), εf l * (t - (n₀:ℝ))^l|
        ≤ ∑ l ∈ Finset.range (k+1), |εf l| * |t - (n₀:ℝ)|^l := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun l hl => ?_)
      rw [abs_mul, abs_pow]
    have h2 : ∑ l ∈ Finset.range (k+1), |εf l| * |t - (n₀:ℝ)|^l
        = |εf 0| * |t - (n₀:ℝ)|^0 + ∑ l ∈ Finset.Icc 1 k, |εf l| * |t - (n₀:ℝ)|^l := by
      rw [range_succ_eq_insert_Icc, Finset.sum_insert (by simp [Finset.mem_Icc])]
    have h3 : ∑ l ∈ Finset.Icc 1 k, |εf l| * |t - (n₀:ℝ)|^l
        ≤ ∑ l ∈ Finset.Icc 1 k, 2 * C_W * (B / (δ₃ * H)) ^ l := by
      refine Finset.sum_le_sum fun l hl => ?_
      have hb : |εf l| ≤ 2 * C_W / (δ₃*H)^l := hεl l hl
      have hb' : |εf l| ≤ 2 * C_W * (1/(δ₃*H)^l) := by
        rw [div_eq_mul_one_div] at hb; exact hb
      calc |εf l| * |t - (n₀:ℝ)|^l
          ≤ (2 * C_W / (δ₃*H)^l) * B^l := by
            refine mul_le_mul hb (pow_le_pow_left₀ htB' htB l) (pow_nonneg htB' l) ?_
            have hpos : 0 < (δ₃*H)^l := pow_pos hδH l
            positivity
        _ = 2 * C_W * (B / (δ₃ * H)) ^ l := by
            rw [div_pow, mul_div_assoc']
            ring
    rw [hεeval t]
    calc |∑ l ∈ Finset.range (k+1), εf l * (t - (n₀:ℝ))^l|
        ≤ ∑ l ∈ Finset.range (k+1), |εf l| * |t - (n₀:ℝ)|^l := h1
      _ = |εf 0| * |t - (n₀:ℝ)|^0 + ∑ l ∈ Finset.Icc 1 k, |εf l| * |t - (n₀:ℝ)|^l := h2
      _ ≤ 1/2 + ∑ l ∈ Finset.Icc 1 k, 2 * C_W * (B / (δ₃ * H)) ^ l := by
            rw [pow_zero, mul_one]
            exact add_le_add hε0 h3
  have hγint : IntegralOn 1 γP := by
    intro n
    refine ⟨∑ l ∈ Finset.range (k+1), γf l * ((n - (n₀:ℤ))^l), ?_⟩
    have hev : γP.eval (1 * (n:ℝ))
        = ∑ l ∈ Finset.range (k+1), (γf l : ℝ) * ((n:ℝ) - (n₀:ℝ))^l := by
      simp only [hγP, hQ, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, one_mul]
    rw [hev]
    push_cast
    refine Finset.sum_congr rfl fun l hl => ?_
    push_cast
    ring
  exact ⟨εP, γP, hmemεP, hmemγP, heq, hεbound, hγint⟩

lemma ceil_add_le (a b : ℝ) : ⌈a + b⌉₊ ≤ ⌈a⌉₊ + ⌈b⌉₊ := by
  rw [Nat.ceil_le]
  push_cast
  exact add_le_add (Nat.le_ceil a) (Nat.le_ceil b)

theorem norm_eC (t : ℝ) : ‖eC t‖ = 1 := by
  rw [eC, Complex.norm_exp]
  simp [Complex.mul_re]

theorem large_sieve_polyF (k : ℕ) (η' C₀ : ℝ) (hη' : 0 < η') (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, C₀ ≤ C ∧ ∃ K : ℕ, ∀ (N : ℕ) (f : ℕ → ℂ) (x₀ H : ℝ) (xs Ls : Fin N → ℝ)
      (Ps : Fin N → ℝ[X]),
      (∀ n, ‖f n‖ ≤ 1) → 1 ≤ H →
      (∀ i, 1 ≤ xs i) →
      (∀ i, Ls i ≤ C₀ * H ∧ H ≤ C₀ * Ls i ∧ |xs i - x₀| ≤ C₀ * H) →
      (∀ i, Ps i ∈ degreeLE ℝ (k : WithBot ℕ)) →
      (∀ i, η' * Ls i ≤ ‖corr f (Ps i) (xs i) (Ls i)‖) →
      K ≤ N → ∃ i j : Fin N, i ≠ j ∧ PolyRel k C 1 (xs i) (Ls i) (Ps i) (xs j) (Ls j) (Ps j) := by
  obtain ⟨δm, hδm, hmom⟩ := large_sieve_moment k η' C₀ hη' hC₀
  have hC0pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  set δ₃ : ℝ := δm / 2 with hδ₃
  have hδ₃pos : 0 < δ₃ := by rw [hδ₃]; linarith
  set δ₂ : ℝ := δm / (2 * (C₀ + 1)) with hδ₂
  have hδ₂pos : 0 < δ₂ := by rw [hδ₂]; positivity
  set Asc : ℝ := (2 * C₀ + 1) / δ₃ + 1 with hAsc
  have hAscnn : 0 ≤ Asc := by rw [hAsc]; positivity
  set δW : ℝ := δm / (4 * C₀) with hδW
  have hδWpos : 0 < δW := by rw [hδW]; positivity
  obtain ⟨Q, C_W, hCW, hweyl⟩ := Work.BMF.FreeWS.weyl_structure k Asc δW hAscnn hδWpos
  set Lfac : ℕ := Nat.factorial (Q + 1) with hLfac
  have hLfacpos : 0 < Lfac := by rw [hLfac]; exact Nat.factorial_pos _
  haveI hLfacNeZero : NeZero Lfac := ⟨Nat.pos_iff_ne_zero.mp hLfacpos⟩
  set Tn : ℕ := (Q + 1) * Lfac ^ k with hTn
  set Cval : ℝ := max C₀ (max (2 * C₀ ^ 2) (1/2 + ∑ l ∈ Finset.Icc 1 k, 2 * C_W * (4 * C₀ / δ₃) ^ l)) with hCval
  set Kval : ℕ := ⌈(Tn : ℝ) / δ₂⌉₊ + 2 with hKval
  refine ⟨Cval, ?_, Kval, ?_⟩
  · rw [hCval]; exact le_max_left _ _
  intro N f x₀ H xs Ls Ps hf hH hxs hgeo hdeg hcorr hKN
  have hK2 : 2 ≤ Kval := by rw [hKval]; omega
  have hN1 : 1 ≤ N := by omega
  have hNbig : (Tn : ℝ) < δ₂ * (N : ℝ) := by
    have h1 : (Tn : ℝ) / δ₂ ≤ ((⌈(Tn : ℝ) / δ₂⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(Tn : ℝ) / δ₂⌉₊ : ℕ) : ℝ) + 2 ≤ (N : ℝ) := by
      have h3 : ⌈(Tn : ℝ) / δ₂⌉₊ + 2 ≤ N := by rw [← hKval]; exact hKN
      exact_mod_cast h3
    have h4 : (Tn : ℝ) / δ₂ + 2 ≤ (N : ℝ) := by linarith
    have h5 : (Tn : ℝ) ≤ δ₂ * ((N : ℝ) - 2) := by
      rw [div_le_iff₀ hδ₂pos] at h1
      nlinarith [h1, h4]
    nlinarith [h5, hδ₂pos]
  obtain ⟨i₀, hi₀⟩ := hmom N f x₀ H xs Ls Ps hf hH hN1 hxs hgeo hdeg hcorr
  set S : Fin N → Fin N → ℂ := fun i j => ∑ n ∈ (natIcc (xs i) (xs i + Ls i)) ∩ (natIcc (xs j) (xs j + Ls j)),
      eC ((Ps i).eval (n : ℝ) - (Ps j).eval (n : ℝ)) with hS
  have hi₀x : 1 ≤ xs i₀ := hxs i₀
  have hi₀L : Ls i₀ ≤ C₀ * H := (hgeo i₀).1
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hcard_i : ((natIcc (xs i₀) (xs i₀ + Ls i₀)).card : ℝ) ≤ C₀ * H + 1 := by
    have hLnn : 0 ≤ Ls i₀ := by nlinarith [(hgeo i₀).2.1, hH]
    calc ((natIcc (xs i₀) (xs i₀ + Ls i₀)).card : ℝ) ≤ (xs i₀ + Ls i₀) - xs i₀ + 1 :=
          card_natIcc_le (by linarith [hi₀x]) (by linarith)
      _ = Ls i₀ + 1 := by ring
      _ ≤ C₀ * H + 1 := by linarith [hi₀L]
  have hSle : ∀ j, ‖S i₀ j‖ ≤ C₀ * H + 1 := by
    intro j
    have h1 : ‖S i₀ j‖ ≤ ((natIcc (xs i₀) (xs i₀ + Ls i₀) ∩ natIcc (xs j) (xs j + Ls j)).card : ℝ) := by
      rw [hS]
      calc ‖∑ n ∈ (natIcc (xs i₀) (xs i₀ + Ls i₀)) ∩ (natIcc (xs j) (xs j + Ls j)),
              eC ((Ps i₀).eval (n : ℝ) - (Ps j).eval (n : ℝ))‖
          ≤ ∑ n ∈ (natIcc (xs i₀) (xs i₀ + Ls i₀)) ∩ (natIcc (xs j) (xs j + Ls j)),
              ‖eC ((Ps i₀).eval (n : ℝ) - (Ps j).eval (n : ℝ))‖ := norm_sum_le _ _
        _ = _ := by simp [norm_eC]
    calc ‖S i₀ j‖ ≤ ((natIcc (xs i₀) (xs i₀ + Ls i₀) ∩ natIcc (xs j) (xs j + Ls j)).card : ℝ) := h1
      _ ≤ ((natIcc (xs i₀) (xs i₀ + Ls i₀)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card (Finset.inter_subset_left)
      _ ≤ C₀ * H + 1 := hcard_i
  set G : Finset (Fin N) := Finset.univ.filter (fun j => δ₃ * H ≤ ‖S i₀ j‖) with hG
  have hGmem : ∀ j, (j ∈ G ↔ δ₃ * H ≤ ‖S i₀ j‖) := by
    intro j; rw [hG]; simp
  have hGcard : δ₂ * (N : ℝ) ≤ (G.card : ℝ) := by
    have hsum : ∑ j : Fin N, ‖S i₀ j‖ = ∑ j ∈ G, ‖S i₀ j‖ + ∑ j ∈ Gᶜ, ‖S i₀ j‖ := by
      rw [← Finset.sum_add_sum_compl G (fun j => ‖S i₀ j‖)]
    have hb1 : ∑ j ∈ G, ‖S i₀ j‖ ≤ (G.card : ℝ) * (C₀ * H + 1) := by
      calc ∑ j ∈ G, ‖S i₀ j‖ ≤ ∑ _j ∈ G, (C₀ * H + 1) := Finset.sum_le_sum (fun j _ => hSle j)
        _ = (G.card : ℝ) * (C₀ * H + 1) := by
              rw [Finset.sum_const, nsmul_eq_mul]
    have hb2 : ∑ j ∈ Gᶜ, ‖S i₀ j‖ ≤ ((Gᶜ.card : ℕ) : ℝ) * (δ₃ * H) := by
      calc ∑ j ∈ Gᶜ, ‖S i₀ j‖ ≤ ∑ _j ∈ Gᶜ, (δ₃ * H) := Finset.sum_le_sum (fun j hj => by
            rw [Finset.mem_compl, hGmem] at hj
            push_neg at hj
            linarith)
        _ = ((Gᶜ.card : ℕ) : ℝ) * (δ₃ * H) := by
              rw [Finset.sum_const, nsmul_eq_mul]
    have hcompl : Gᶜ.card = N - G.card := by
      rw [Finset.card_compl]
      simp
    have hmain : δm * (N : ℝ) * H ≤ (G.card : ℝ) * (C₀ * H + 1) + ((N - G.card : ℕ) : ℝ) * (δ₃ * H) := by
      calc δm * (N : ℝ) * H ≤ ∑ j : Fin N, ‖S i₀ j‖ := hi₀
        _ = ∑ j ∈ G, ‖S i₀ j‖ + ∑ j ∈ Gᶜ, ‖S i₀ j‖ := hsum
        _ ≤ (G.card : ℝ) * (C₀ * H + 1) + ((Gᶜ.card : ℕ) : ℝ) * (δ₃ * H) := add_le_add hb1 hb2
        _ = (G.card : ℝ) * (C₀ * H + 1) + ((N - G.card : ℕ) : ℝ) * (δ₃ * H) := by rw [hcompl]
    have hGc_le : ((N - G.card : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.sub_le N G.card
    have hb : (δm / 2) * (N : ℝ) * H ≤ (G.card : ℝ) * (C₀ * H + 1) := by
      have h2 : δm * (N : ℝ) * H - ((N - G.card : ℕ) : ℝ) * (δ₃ * H) ≤ (G.card : ℝ) * (C₀ * H + 1) := by
        linarith [hmain]
      rw [hδ₃] at h2
      have hle : ((N - G.card : ℕ) : ℝ) * (δm / 2) * H ≤ (N : ℝ) * (δm / 2) * H := by
        apply mul_le_mul_of_nonneg_right _ hHpos.le
        exact mul_le_mul_of_nonneg_right hGc_le (by positivity)
      linarith [h2, hle]
    have hba : (δm / 2) * (N : ℝ) * H ≤ (G.card : ℝ) * (C₀ + 1) * H := by
      calc (δm / 2) * (N : ℝ) * H ≤ (G.card : ℝ) * (C₀ * H + 1) := hb
        _ ≤ (G.card : ℝ) * ((C₀ + 1) * H) := by
              apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
              nlinarith [hH]
        _ = (G.card : ℝ) * (C₀ + 1) * H := by ring
    have hbb : (δm / 2) * (N : ℝ) ≤ (G.card : ℝ) * (C₀ + 1) := by
      nlinarith [hba, hHpos]
    have hbb' : δm * (N : ℝ) ≤ (G.card : ℝ) * (2 * (C₀ + 1)) := by
      have e1 : δm * (N : ℝ) = 2 * ((δm / 2) * (N : ℝ)) := by ring
      have e2 : (G.card : ℝ) * (2 * (C₀ + 1)) = 2 * ((G.card : ℝ) * (C₀ + 1)) := by ring
      linarith [hbb, e1, e2]
    rw [hδ₂]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 2 * (C₀ + 1))]
    exact hbb'
  -- geometric data
  set Ev : Fin N → ℕ := fun j => max ⌈xs i₀⌉₊ ⌈xs j⌉₊ with hEv
  set Fv : Fin N → ℕ := fun j => min ⌊xs i₀ + Ls i₀⌋₊ ⌊xs j + Ls j⌋₊ with hFv
  set Mj : Fin N → ℕ := fun j => Fv j + 1 - Ev j with hMj
  have hnI : ∀ j, natIcc (xs i₀) (xs i₀ + Ls i₀) ∩ natIcc (xs j) (xs j + Ls j)
      = Finset.Icc (Ev j) (Fv j) := by
    intro j; rw [natIcc_inter]
  have hSsum : ∀ j, S i₀ j = ∑ n ∈ Finset.Icc (Ev j) (Fv j),
      eC ((Ps i₀ - Ps j).eval (n : ℝ)) := by
    intro j
    simp only [hS]
    rw [hnI j]
    exact Finset.sum_congr rfl (fun n _ => by rw [Polynomial.eval_sub])
  have hMj_card : ∀ j, (Mj j : ℝ) ≤ ((natIcc (xs i₀) (xs i₀ + Ls i₀)).card : ℝ) := by
    intro j
    have h2 : Mj j = (Finset.Icc (Ev j) (Fv j)).card := by rw [hMj, Nat.card_Icc]
    rw [h2, ← hnI j]
    exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  have hS_le_Mj : ∀ j, ‖S i₀ j‖ ≤ (Mj j : ℝ) := by
    intro j
    rw [hSsum j]
    calc ‖∑ n ∈ Finset.Icc (Ev j) (Fv j), eC ((Ps i₀ - Ps j).eval (n : ℝ))‖
        ≤ ∑ n ∈ Finset.Icc (Ev j) (Fv j), ‖eC ((Ps i₀ - Ps j).eval (n : ℝ))‖ := norm_sum_le _ _
      _ = ((Finset.Icc (Ev j) (Fv j)).card : ℝ) := by simp [norm_eC]
      _ = (Mj j : ℝ) := by rw [hMj, Nat.card_Icc]
  have hweylG : ∀ j : {j // j ∈ G}, ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ Q ∧
      ∀ l ∈ Finset.range (k + 1), ∃ m : ℤ,
        |(q : ℝ) * (Polynomial.taylor (⌈xs i₀⌉₊ : ℝ) (Ps i₀ - Ps j.val)).coeff l - m| ≤
          C_W / (Mj j.val : ℝ) ^ l := by
    intro j
    have hjgood : δ₃ * H ≤ ‖S i₀ j.val‖ := (hGmem j.val).mp j.property
    have hMj_ge : δ₃ * H ≤ (Mj j.val : ℝ) := le_trans hjgood (hS_le_Mj j.val)
    have hMjpos : 0 < (Mj j.val : ℝ) := lt_of_lt_of_le (mul_pos hδ₃pos hHpos) hMj_ge
    have hMj1 : 1 ≤ Mj j.val := by
      rcases Nat.eq_zero_or_pos (Mj j.val) with h | h
      · rw [h] at hMjpos; norm_num at hMjpos
      · exact h
    have hEvFv : Ev j.val ≤ Fv j.val := by
      have h1 : Mj j.val = Fv j.val + 1 - Ev j.val := by simp only [hMj]
      omega
    have hIcc : Finset.Icc (Ev j.val) (Ev j.val + Mj j.val - 1) = Finset.Icc (Ev j.val) (Fv j.val) := by
      have h1 : Mj j.val = Fv j.val + 1 - Ev j.val := by simp only [hMj]
      congr 1
      omega
    have hdegsub : (Ps i₀ - Ps j.val) ∈ degreeLE ℝ (k : WithBot ℕ) := by
      rw [Polynomial.mem_degreeLE]
      have h1 : (Ps i₀).degree ≤ (k : WithBot ℕ) := Polynomial.mem_degreeLE.mp (hdeg i₀)
      have h2 : (Ps j.val).degree ≤ (k : WithBot ℕ) := Polynomial.mem_degreeLE.mp (hdeg j.val)
      calc (Ps i₀ - Ps j.val).degree ≤ max (Ps i₀).degree (Ps j.val).degree := Polynomial.degree_sub_le _ _
        _ ≤ (k : WithBot ℕ) := max_le h1 h2
    have hn₀le : ⌈xs i₀⌉₊ ≤ Ev j.val := le_max_left _ _
    have hD : ((Ev j.val - ⌈xs i₀⌉₊ : ℕ) : ℝ) ≤ Asc * (Mj j.val : ℝ) := by
      have hceil : ⌈xs j.val⌉₊ ≤ ⌈xs i₀⌉₊ + ⌈2 * C₀ * H⌉₊ := by
        have hx : xs j.val ≤ xs i₀ + 2 * C₀ * H := by
          have h1 := (hgeo j.val).2.2
          have h2 := (hgeo i₀).2.2
          rw [abs_le] at h1 h2
          linarith [h1.1, h1.2, h2.1, h2.2]
        calc ⌈xs j.val⌉₊ ≤ ⌈xs i₀ + 2 * C₀ * H⌉₊ := Nat.ceil_mono hx
          _ ≤ ⌈xs i₀⌉₊ + ⌈2 * C₀ * H⌉₊ := ceil_add_le _ _
      have hEvle : Ev j.val ≤ ⌈xs i₀⌉₊ + ⌈2 * C₀ * H⌉₊ := by
        rw [hEv]
        exact max_le (by omega) hceil
      have hD2 : Ev j.val - ⌈xs i₀⌉₊ ≤ ⌈2 * C₀ * H⌉₊ := by omega
      have hceilbound : ((⌈2 * C₀ * H⌉₊ : ℕ) : ℝ) ≤ 2 * C₀ * H + 1 := by
        have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2 * C₀ * H by positivity)
        linarith
      have hAsc_ge : (2 * C₀ + 1) / δ₃ ≤ Asc := by rw [hAsc]; linarith
      have h1 : ((2 * C₀ + 1) / δ₃) * (δ₃ * H) ≤ Asc * (Mj j.val : ℝ) := by
        apply mul_le_mul hAsc_ge hMj_ge (le_of_lt (mul_pos hδ₃pos hHpos))
        rw [hAsc]; positivity
      have h2 : (2 * C₀ + 1) * H ≤ ((2 * C₀ + 1) / δ₃) * (δ₃ * H) := by
        have h3 : ((2 * C₀ + 1) / δ₃) * (δ₃ * H) = (2 * C₀ + 1) * H := by
          rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hδ₃pos)]
        exact le_of_eq h3.symm
      calc ((Ev j.val - ⌈xs i₀⌉₊ : ℕ) : ℝ) ≤ ((⌈2 * C₀ * H⌉₊ : ℕ) : ℝ) := by exact_mod_cast hD2
        _ ≤ 2 * C₀ * H + 1 := hceilbound
        _ ≤ (2 * C₀ + 1) * H := by nlinarith [hH]
        _ ≤ ((2 * C₀ + 1) / δ₃) * (δ₃ * H) := h2
        _ ≤ Asc * (Mj j.val : ℝ) := h1
    have hbdist : |((⌈xs i₀⌉₊ : ℕ) : ℝ) - ((Ev j.val : ℕ) : ℝ)| ≤ Asc * (Mj j.val : ℝ) := by
      have hcast : -(((⌈xs i₀⌉₊ : ℕ) : ℝ) - ((Ev j.val : ℕ) : ℝ))
          = ((Ev j.val - ⌈xs i₀⌉₊ : ℕ) : ℝ) := by
        rw [Nat.cast_sub hn₀le]; ring
      rw [abs_of_nonpos (by
            have : ((⌈xs i₀⌉₊ : ℕ) : ℝ) ≤ ((Ev j.val : ℕ) : ℝ) := by exact_mod_cast hn₀le
            linarith), hcast]
      exact hD
    have hSW : δW * (Mj j.val : ℝ) ≤ ‖S i₀ j.val‖ := by
      have h1 : (Mj j.val : ℝ) ≤ 2 * C₀ * H := by
        have hA := hMj_card j.val
        have hB := hcard_i
        have hC1 : 1 ≤ C₀ * H := by nlinarith [hC₀, hH]
        linarith
      have h2 : δW * (Mj j.val : ℝ) ≤ δW * (2 * C₀ * H) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hδWpos)
      have h3 : δW * (2 * C₀ * H) = δ₃ * H := by
        rw [hδW, hδ₃]
        have hC0ne : (4 * C₀ : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      linarith [h2, h3, hjgood]
    have hSw : δW * (Mj j.val : ℝ) ≤
        ‖∑ m ∈ Finset.Icc (Ev j.val) (Ev j.val + Mj j.val - 1), eC ((Ps i₀ - Ps j.val).eval (m : ℝ))‖ := by
      rw [hIcc, ← hSsum j.val]
      exact hSW
    exact hweyl (Ps i₀ - Ps j.val) (Ev j.val) (⌈xs i₀⌉₊) (Mj j.val) hdegsub hMj1 hbdist hSw
  let qf : {j // j ∈ G} → ℕ := fun j => Classical.choose (hweylG j)
  have hqspec : ∀ j : {j // j ∈ G}, 1 ≤ qf j ∧ (qf j : ℝ) ≤ Q ∧
      ∀ l ∈ Finset.range (k + 1), ∃ m : ℤ,
        |(qf j : ℝ) * (Polynomial.taylor (⌈xs i₀⌉₊ : ℝ) (Ps i₀ - Ps j.val)).coeff l - m| ≤
          C_W / (Mj j.val : ℝ) ^ l := fun j => Classical.choose_spec (hweylG j)
  let mf : {j // j ∈ G} → ℕ → ℤ := fun j l =>
    if h : l ∈ Finset.range (k + 1) then Classical.choose ((hqspec j).2.2 l h) else 0
  have hmfspec : ∀ (j : {j // j ∈ G}) (l : ℕ) (hl : l ∈ Finset.range (k + 1)),
      |(qf j : ℝ) * (Polynomial.taylor (⌈xs i₀⌉₊ : ℝ) (Ps i₀ - Ps j.val)).coeff l - (mf j l : ℝ)| ≤
        C_W / (Mj j.val : ℝ) ^ l := by
    intro j l hl
    simp only [mf, dif_pos hl]
    exact Classical.choose_spec ((hqspec j).2.2 l hl)
  let typ : {j // j ∈ G} → Fin (Q + 1) × (Fin k → ZMod Lfac) := fun j =>
    (⟨qf j, by
        have h := (hqspec j).2.1
        have h' : qf j ≤ Q := by exact_mod_cast h
        omega⟩,
     fun l : Fin k => ((mf j (l.val + 1) : ℤ) : ZMod Lfac))
  have hcard_types : Fintype.card (Fin (Q + 1) × (Fin k → ZMod Lfac)) = Tn := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, ZMod.card, hTn]
  have hGcard_nat : Tn < G.card := by
    have h1 : (Tn : ℝ) < (G.card : ℝ) := lt_of_lt_of_le hNbig hGcard
    exact_mod_cast h1
  obtain ⟨j₁, j₂, hne, htyp⟩ := Fintype.exists_ne_map_eq_of_card_lt typ (by
    have hcardG : Fintype.card ↥G = G.card := by simp
    rw [hcard_types, hcardG]
    exact hGcard_nat)
  have hqeq : qf j₁ = qf j₂ := by
    have h := congrArg (fun p : Fin (Q + 1) × (Fin k → ZMod Lfac) => (p.1 : ℕ)) htyp
    simpa using h
  have hmod : ∀ l ∈ Finset.Icc 1 k, (mf j₁ l) ≡ (mf j₂ l) [ZMOD (qf j₁ : ℤ)] := by
    intro l hl
    obtain ⟨hl1, hlk⟩ := Finset.mem_Icc.mp hl
    have hkey := congrArg (fun p : Fin (Q + 1) × (Fin k → ZMod Lfac) => p.2 ⟨l - 1, by omega⟩) htyp
    simp only [typ] at hkey
    have hidx : ((⟨l - 1, by omega⟩ : Fin k).val + 1) = l := by simp; omega
    rw [hidx] at hkey
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hkey
    have hqQ : qf j₁ ≤ Q := by have := (hqspec j₁).2.1; exact_mod_cast this
    have hqpos : 0 < qf j₁ := (hqspec j₁).1
    have hdiv : qf j₁ ∣ Lfac := by
      rw [hLfac]
      exact Nat.dvd_factorial hqpos (by omega)
    rw [Int.modEq_iff_dvd]
    exact dvd_trans (by exact_mod_cast hdiv) hkey
  have hBt : ∀ t ∈ Set.Icc (xs j₁.val) (xs j₁.val + Ls j₁.val),
      |t - (⌈xs i₀⌉₊ : ℝ)| ≤ 4 * C₀ * H := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have hg₁ := hgeo j₁.val
    have hg₀ := hgeo i₀
    have h1 : xs j₁.val ≤ x₀ + C₀ * H := by
      have := hg₁.2.2; rw [abs_le] at this; linarith [this.2]
    have h2 : x₀ - C₀ * H ≤ xs j₁.val := by
      have := hg₁.2.2; rw [abs_le] at this; linarith [this.1]
    have h3 : Ls j₁.val ≤ C₀ * H := hg₁.1
    have h4 : x₀ - C₀ * H ≤ xs i₀ := by
      have := hg₀.2.2; rw [abs_le] at this; linarith [this.1]
    have h5 : xs i₀ ≤ x₀ + C₀ * H := by
      have := hg₀.2.2; rw [abs_le] at this; linarith [this.2]
    have h6 : (⌈xs i₀⌉₊ : ℝ) ≤ x₀ + C₀ * H + 1 := by
      have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ xs i₀ by linarith [hxs i₀])
      linarith
    have h7 : x₀ - C₀ * H ≤ (⌈xs i₀⌉₊ : ℝ) := le_trans h4 (Nat.le_ceil (xs i₀))
    have hC0H : 1 ≤ C₀ * H := by nlinarith [hC₀, hH]
    rw [abs_le]
    constructor <;> linarith
  have hdeg₁ : (Ps i₀ - Ps j₁.val) ∈ degreeLE ℝ (k : WithBot ℕ) := by
    rw [Polynomial.mem_degreeLE]
    have h1 : (Ps i₀).degree ≤ (k : WithBot ℕ) := Polynomial.mem_degreeLE.mp (hdeg i₀)
    have h2 : (Ps j₁.val).degree ≤ (k : WithBot ℕ) := Polynomial.mem_degreeLE.mp (hdeg j₁.val)
    calc (Ps i₀ - Ps j₁.val).degree ≤ max (Ps i₀).degree (Ps j₁.val).degree := Polynomial.degree_sub_le _ _
      _ ≤ (k : WithBot ℕ) := max_le h1 h2
  have hdeg₂ : (Ps i₀ - Ps j₂.val) ∈ degreeLE ℝ (k : WithBot ℕ) := by
    rw [Polynomial.mem_degreeLE]
    have h1 : (Ps i₀).degree ≤ (k : WithBot ℕ) := Polynomial.mem_degreeLE.mp (hdeg i₀)
    have h2 : (Ps j₂.val).degree ≤ (k : WithBot ℕ) := Polynomial.mem_degreeLE.mp (hdeg j₂.val)
    calc (Ps i₀ - Ps j₂.val).degree ≤ max (Ps i₀).degree (Ps j₂.val).degree := Polynomial.degree_sub_le _ _
      _ ≤ (k : WithBot ℕ) := max_le h1 h2
  have hM₁ : δ₃ * H ≤ (Mj j₁.val : ℝ) :=
    le_trans ((hGmem j₁.val).mp j₁.property) (hS_le_Mj j₁.val)
  have hM₂ : δ₃ * H ≤ (Mj j₂.val : ℝ) :=
    le_trans ((hGmem j₂.val).mp j₂.property) (hS_le_Mj j₂.val)
  have ha₁ : ∀ l ∈ Finset.range (k + 1),
      |(qf j₁ : ℝ) * (Polynomial.taylor (⌈xs i₀⌉₊ : ℝ) (Ps i₀ - Ps j₁.val)).coeff l - (mf j₁ l : ℝ)| ≤
        C_W / (Mj j₁.val : ℝ) ^ l := fun l hl => hmfspec j₁ l hl
  have ha₂ : ∀ l ∈ Finset.range (k + 1),
      |(qf j₁ : ℝ) * (Polynomial.taylor (⌈xs i₀⌉₊ : ℝ) (Ps i₀ - Ps j₂.val)).coeff l - (mf j₂ l : ℝ)| ≤
        C_W / (Mj j₂.val : ℝ) ^ l := by
    intro l hl
    have h := hmfspec j₂ l hl
    rw [← hqeq] at h
    exact h
  obtain ⟨εp, γp, hεdeg, hγdeg, heqR, hεbd, hγint⟩ :=
    exists_bounded_integral_of_coeffs (k := k) (q := qf j₁) (C_W := C_W) (δ₃ := δ₃) (H := H)
      (n₀ := ⌈xs i₀⌉₊) (M₁ := (Mj j₁.val : ℝ)) (M₂ := (Mj j₂.val : ℝ))
      (m₁ := mf j₁) (m₂ := mf j₂) (x := xs j₁.val) (L := Ls j₁.val) (B := 4 * C₀ * H)
      (R₁ := Ps i₀ - Ps j₁.val) (R₂ := Ps i₀ - Ps j₂.val)
      (hqspec j₁).1 (le_of_lt hCW) hδ₃pos hHpos (by positivity)
      hdeg₁ hdeg₂ hM₁ hM₂ ha₁ ha₂ hmod hBt
  refine ⟨j₁.val, j₂.val, fun h => hne (Subtype.ext h), ?_, ?_, ?_, -εp, -γp,
    neg_mem hεdeg, neg_mem hγdeg, ?_, ?_, ?_⟩
  · have h1 : Ls j₁.val ≤ C₀ * H := (hgeo j₁.val).1
    have h2 : H ≤ C₀ * Ls j₂.val := (hgeo j₂.val).2.1
    have h3 : 0 ≤ Ls j₂.val := by nlinarith [h2, hH, hC0pos]
    have hC2 : C₀ ^ 2 ≤ Cval := by
      rw [hCval]
      have : C₀ ^ 2 ≤ 2 * C₀ ^ 2 := by nlinarith [sq_nonneg C₀]
      exact le_trans this (le_trans (le_max_left _ _) (le_max_right _ _))
    calc Ls j₁.val ≤ C₀ * H := h1
      _ ≤ C₀ * (C₀ * Ls j₂.val) := by nlinarith [h2, hC0pos]
      _ = C₀ ^ 2 * Ls j₂.val := by ring
      _ ≤ Cval * Ls j₂.val := mul_le_mul_of_nonneg_right hC2 h3
  · have h1 : Ls j₂.val ≤ C₀ * H := (hgeo j₂.val).1
    have h2 : H ≤ C₀ * Ls j₁.val := (hgeo j₁.val).2.1
    have h3 : 0 ≤ Ls j₁.val := by nlinarith [h2, hH, hC0pos]
    have hC2 : C₀ ^ 2 ≤ Cval := by
      rw [hCval]
      have : C₀ ^ 2 ≤ 2 * C₀ ^ 2 := by nlinarith [sq_nonneg C₀]
      exact le_trans this (le_trans (le_max_left _ _) (le_max_right _ _))
    calc Ls j₂.val ≤ C₀ * H := h1
      _ ≤ C₀ * (C₀ * Ls j₁.val) := by nlinarith [h2, hC0pos]
      _ = C₀ ^ 2 * Ls j₁.val := by ring
      _ ≤ Cval * Ls j₁.val := mul_le_mul_of_nonneg_right hC2 h3
  · have h1 : |xs j₁.val - x₀| ≤ C₀ * H := (hgeo j₁.val).2.2
    have h2 : |xs j₂.val - x₀| ≤ C₀ * H := (hgeo j₂.val).2.2
    have h3 : |xs j₁.val - xs j₂.val| ≤ 2 * C₀ * H := by
      have h := abs_sub_le (xs j₁.val) x₀ (xs j₂.val)
      rw [abs_sub_comm x₀ (xs j₂.val)] at h
      linarith
    have h4 : H ≤ C₀ * Ls j₁.val := (hgeo j₁.val).2.1
    have h5 : 0 ≤ Ls j₁.val := by nlinarith [h4, hH, hC0pos]
    have hC4 : 2 * C₀ ^ 2 ≤ Cval := by
      rw [hCval]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    calc |xs j₁.val - xs j₂.val| ≤ 2 * C₀ * H := h3
      _ ≤ 2 * C₀ * (C₀ * Ls j₁.val) := by nlinarith [h4, hC0pos]
      _ = 2 * C₀ ^ 2 * Ls j₁.val := by ring
      _ ≤ Cval * Ls j₁.val := mul_le_mul_of_nonneg_right hC4 h5
  · have hR : (Ps i₀ - Ps j₁.val) - (Ps i₀ - Ps j₂.val) = εp + γp := heqR
    have hR' : Ps j₂.val - Ps j₁.val = εp + γp := by rw [← hR]; ring
    linear_combination -hR'
  · intro t ht
    have hbd := hεbd t ht
    have hsum : (∑ l ∈ Finset.Icc 1 k, 2 * C_W * (4 * C₀ * H / (δ₃ * H)) ^ l)
        = ∑ l ∈ Finset.Icc 1 k, 2 * C_W * (4 * C₀ / δ₃) ^ l := by
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [show 4 * C₀ * H / (δ₃ * H) = 4 * C₀ / δ₃ by field_simp]
    have hCle : 1/2 + ∑ l ∈ Finset.Icc 1 k, 2 * C_W * (4 * C₀ / δ₃) ^ l ≤ Cval := by
      rw [hCval]
      exact le_trans (le_max_right (2 * C₀ ^ 2) _) (le_max_right C₀ _)
    rw [Polynomial.eval_neg, abs_neg]
    rw [hsum] at hbd
    exact le_trans hbd hCle
  · intro n
    obtain ⟨m, hm⟩ := hγint n
    refine ⟨-m, ?_⟩
    rw [Polynomial.eval_neg, hm]
    push_cast
    ring

end Work.BMF.FreeLS
