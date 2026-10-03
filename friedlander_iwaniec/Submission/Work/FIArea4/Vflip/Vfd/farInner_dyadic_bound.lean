import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.farGadgets
import Submission.Work.FIArea4.Vflip.Vfd.FarSepDefs
import Submission.Work.FIArea4.Vflip.Vfd.farExpSum_eq_pairSumCo
import Submission.Work.FIArea4.Vflip.Vfd.pairSum_large_sieve_coprime
import Submission.Work.FIArea4.Vflip.Vfd.coprimeSetup
import Submission.Work.FIArea4.PairSumCommon
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.Evar_le_trivial
import Submission.Work.FIArea4.Vflip.Vfd.pairSum_large_sieve
import Submission.Work.FIArea4.Vflip.Vfd.VfdDefs
import Submission.Work.FIArea4.Vflip.Vfd.FarExpSum_le_crude
import Submission.Work.FIArea4.Vflip.Vfd.FarExpSum_le_crude_unif
import Submission.Work.FIArea4.Vflip.Vfd.farInner_eq_zero_of_range
import Submission.Work.FIArea4.Vflip.Vfd.pairSumCo_ls_twisted

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

set_option linter.unusedVariables false

noncomputable section

/-- A product of five complex numbers, four of them of modulus at most one, is bounded by the
modulus of the first. -/
private lemma norm_five_le_one {a b c d e : ℂ} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (he : ‖e‖ ≤ 1) : ‖a * b * c * d * e‖ ≤ ‖a‖ := by
  have hbc : ‖b‖ * ‖c‖ ≤ 1 := mul_le_one₀ hb (norm_nonneg _) hc
  have hbcd : ‖b‖ * ‖c‖ * ‖d‖ ≤ 1 := mul_le_one₀ hbc (by positivity) hd
  have hbcde : ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ ≤ 1 := mul_le_one₀ hbcd (by positivity) he
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  rw [show ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ = ‖a‖ * (‖b‖ * ‖c‖ * ‖d‖ * ‖e‖) by ring]
  calc ‖a‖ * (‖b‖ * ‖c‖ * ‖d‖ * ‖e‖) ≤ ‖a‖ * 1 :=
        mul_le_mul_of_nonneg_left hbcde (norm_nonneg _)
    _ = ‖a‖ := mul_one _

/-- All the factors of `farU` beyond `α (cρ) s` have modulus at most one. -/
lemma norm_farU_le (m c : ℕ) (α : ℕ → ℕ → ℂ) (u t : ℝ) (ρ s : ℕ) :
    ‖farU m c α u t ρ s‖ ≤ ‖α (c * ρ) s‖ := by
  rw [farU]
  refine norm_five_le_one ?_ ?_ ?_ ?_
  · exact norm_jacobiSym_cast_le_one (s:ℤ) ρ
  · exact norm_jacobiSym_cast_le_one (ρ:ℤ) (Work.FIPlan.oddPart m)
  · simpa using le_of_eq (norm_exp_two_pi_I_mul (u * ((s:ℝ) / (((c*ρ:ℕ):ℝ)))))
  · exact norm_cpow_I_mul_le_one (Nat.cast_nonneg ρ) t

/-- All the factors of `farV` beyond `α (cρ) s` have modulus at most one. -/
lemma norm_farV_le (m c : ℕ) (α : ℕ → ℕ → ℂ) (u t : ℝ) (ρ s : ℕ) :
    ‖farV m c α u t ρ s‖ ≤ ‖α (c * ρ) s‖ := by
  rw [farV]
  refine norm_five_le_one ?_ ?_ ?_ ?_
  · exact norm_jacobiSym_cast_le_one (s:ℤ) ρ
  · exact norm_jacobiSym_cast_le_one (ρ:ℤ) (Work.FIPlan.oddPart m)
  · simpa using le_of_eq (norm_exp_two_pi_I_mul (u * ((s:ℝ) / (((c*ρ:ℕ):ℝ)))))
  · simpa using norm_cpow_I_mul_le_one (Nat.cast_nonneg ρ) (-t)

/-- Pointwise domination of `farU` by the reduced array `redA c α`. -/
lemma normSq_farU_le_redA (m c : ℕ) (α : ℕ → ℕ → ℂ) (u t : ℝ) (ρ s : ℕ) :
    Complex.normSq (farU m c α u t ρ s) ≤ Complex.normSq (redA c α ρ s) := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, redA_apply]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_farU_le m c α u t ρ s) 2

/-- Pointwise domination of `farV` by the reduced array `redA c α`. -/
lemma normSq_farV_le_redA (m c : ℕ) (α : ℕ → ℕ → ℂ) (u t : ℝ) (ρ s : ℕ) :
    Complex.normSq (farV m c α u t ρ s) ≤ Complex.normSq (redA c α ρ s) := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, redA_apply]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_farV_le m c α u t ρ s) 2

/-- Monotonicity of `p14L2` in the coefficient array. -/
lemma p14L2_le_of_normSq_le {R S : ℕ} {β γ : ℕ → ℕ → ℂ}
    (h : ∀ r s, Complex.normSq (β r s) ≤ Complex.normSq (γ r s)) :
    Work.FIArea4.p14L2 R S β ≤ Work.FIArea4.p14L2 R S γ := by
  simp only [Work.FIArea4.p14L2]
  exact Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun s _ => h r s))

/-- `farU` carries no more energy than the reduced array `redA c α`. -/
lemma p14L2_farU_le (m c R S : ℕ) (α : ℕ → ℕ → ℂ) (u t : ℝ) :
    Work.FIArea4.p14L2 (cR c R) S (farU m c α u t) ≤
      Work.FIArea4.p14L2 (cR c R) S (redA c α) :=
  p14L2_le_of_normSq_le (fun r s => normSq_farU_le_redA m c α u t r s)

/-- `farV` carries no more energy than the reduced array `redA c α`. -/
lemma p14L2_farV_le (m c R S : ℕ) (α : ℕ → ℕ → ℂ) (u t : ℝ) :
    Work.FIArea4.p14L2 (cR c R) S (farV m c α u t) ≤
      Work.FIArea4.p14L2 (cR c R) S (redA c α) :=
  p14L2_le_of_normSq_le (fun r s => normSq_farV_le_redA m c α u t r s)

/-- The array `farU` is supported on odd `r` when `α` is. -/
lemma farU_odd {m c : ℕ} {α : ℕ → ℕ → ℂ} {u t : ℝ}
    (hcop : ∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) :
    ∀ ρ s, farU m c α u t ρ s ≠ 0 → Odd ρ := by
  intro ρ s h
  have hα : α (c * ρ) s ≠ 0 := fun h0 => h (by rw [farU]; simp [h0])
  have hodd : Odd (c * ρ) := by
    have h2 : 2 ∣ 2 * s := ⟨s, rfl⟩
    exact Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right h2 (hcop (c*ρ) s hα))
  exact (Nat.odd_mul.mp hodd).2

/-- The array `farV` is supported on odd `r` when `α` is. -/
lemma farV_odd {m c : ℕ} {α : ℕ → ℕ → ℂ} {u t : ℝ}
    (hcop : ∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) :
    ∀ ρ s, farV m c α u t ρ s ≠ 0 → Odd ρ := by
  intro ρ s h
  have hα : α (c * ρ) s ≠ 0 := fun h0 => h (by rw [farV]; simp [h0])
  have hodd : Odd (c * ρ) := by
    have h2 : 2 ∣ 2 * s := ⟨s, rfl⟩
    exact Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right h2 (hcop (c*ρ) s hα))
  exact (Nat.odd_mul.mp hodd).2

/-! ## 2. The reduced box parameters `Rred` and `cR`, and the crude bracket -/

/-- The reduced parameter `⌊2R/c⌋` of the crude bound is at most twice the reduced box parameter
`⌈R/c⌉`. -/
lemma Rred_le_two_cR {c R : ℕ} (hc : 1 ≤ c) : Rred c R ≤ 2 * cR c R := by
  simp only [Rred, cR]
  rw [Nat.div_le_iff_le_mul_add_pred (by omega : 0 < c)]
  have h1 : R ≤ c * ((R + c - 1) / c) := le_mul_cR hc
  have h2 : 2 * R ≤ c * (2 * ((R + c - 1) / c)) := by nlinarith [h1]
  exact le_trans h2 (le_add_of_nonneg_right (Nat.zero_le _))

/-- Two `p14L2`-energies of an array supported in `r ≤ M` over boxes of `r`-radius `R₁`, `R₂`
agree, provided `M` fits in both. -/
lemma p14L2_eq_of_support_le {R1 R2 S M : ℕ} {β : ℕ → ℕ → ℂ}
    (h1 : M ≤ 2 * R1) (h2 : M ≤ 2 * R2)
    (hsupp : ∀ r s, β r s ≠ 0 → 1 ≤ r ∧ r ≤ M) :
    Work.FIArea4.p14L2 R1 S β = Work.FIArea4.p14L2 R2 S β := by
  have hsub1 : Finset.Icc 1 M ⊆ Finset.Icc 1 (2 * R1) := by
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  have hsub2 : Finset.Icc 1 M ⊆ Finset.Icc 1 (2 * R2) := by
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  have hzero : ∀ {R : ℕ}, M ≤ 2 * R → ∀ r ∈ Finset.Icc 1 (2 * R), r ∉ Finset.Icc 1 M →
      (∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (β r s)) = 0 := by
    intro R hR r hr hrM
    refine Finset.sum_eq_zero (fun s _ => ?_)
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hMr : M < r := by
      by_contra h
      exact hrM (Finset.mem_Icc.mpr ⟨hr1, by omega⟩)
    have hb : β r s = 0 := by
      by_contra h
      exact absurd (hsupp r s h).2 (by omega)
    rw [hb, Complex.normSq_zero]
  have e1 : (∑ r ∈ Finset.Icc 1 (2 * R1), ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (β r s))
      = ∑ r ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (β r s) :=
    (Finset.sum_subset hsub1 (hzero h1)).symm
  have e2 : (∑ r ∈ Finset.Icc 1 (2 * R2), ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (β r s))
      = ∑ r ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (β r s) :=
    (Finset.sum_subset hsub2 (hzero h2)).symm
  simp only [Work.FIArea4.p14L2]
  rw [e1, e2]

/-- The energy of `redA c α` over the crude box `Rred c R` equals its energy over the reduced box
`cR c R` of the flip. -/
lemma p14L2_Rred_eq_cR {c R S : ℕ} {α : ℕ → ℕ → ℂ} (hc : 1 ≤ c)
    (hbox : ∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) :
    Work.FIArea4.p14L2 (Rred c R) S (redA c α) = Work.FIArea4.p14L2 (cR c R) S (redA c α) := by
  refine p14L2_eq_of_support_le (M := Rred c R) (R1 := Rred c R) (R2 := cR c R) ?_ ?_ ?_
  · omega
  · exact Rred_le_two_cR hc
  · intro r s h
    rw [redA_apply] at h
    obtain ⟨hr1, hr2, -, -⟩ := hbox (c * r) s h
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos r with h0 | h0
      · rw [h0, mul_zero] at hr1; omega
      · exact h0
    · rw [Rred, Nat.le_div_iff_mul_le (by omega : 0 < c)]
      simpa [Nat.mul_comm] using hr2

/-- The unit twist `(c/n)^{it}` of the flipped modulus has modulus at most one. -/
lemma norm_cpow_twist_le_one {c n : ℕ} (hc : 1 ≤ c) (t : ℝ) :
    ‖((c : ℂ) / (n : ℂ)) ^ (Complex.I * (t : ℂ))‖ ≤ 1 := by
  have h := Complex.norm_cpow_le ((c : ℂ) / (n : ℂ)) (Complex.I * (t : ℂ))
  have hre : (Complex.I * (t : ℂ)).re = 0 := by simp [Complex.mul_re]
  rw [hre, Real.rpow_zero] at h
  have harg : (((c : ℂ) / (n : ℂ)).arg) = 0 := by
    rcases eq_or_ne (n : ℂ) 0 with hn | hn
    · rw [hn, div_zero, Complex.arg_zero]
    · have hn0 : (0:ℝ) < (n:ℝ) := by
        have hn' : n ≠ 0 := by rintro rfl; exact hn (by simp)
        exact_mod_cast Nat.pos_of_ne_zero hn'
      have h1 : ((c : ℂ) / (n : ℂ)) = ((((c:ℝ)/(n:ℝ)) : ℝ) : ℂ) := by
        push_cast; ring
      rw [h1, Complex.arg_ofReal_of_nonneg (by positivity)]
  rw [harg, zero_mul, Real.exp_zero] at h
  simpa using h

/-- `1/m ≤ m^{-1/2}` for `m ≥ 1`. -/
lemma one_div_le_rpow_neg_half (m : ℕ) (hm : 1 ≤ m) :
    (1:ℝ) / m ≤ (m:ℝ) ^ (-(1:ℝ)/2) := by
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hsplit : (-(1:ℝ)/2) = -((1:ℝ)/2) := by norm_num
  rw [hsplit, Real.rpow_neg (Nat.cast_nonneg m), ← one_div]
  refine one_div_le_one_div_of_le (by positivity) ?_
  calc (m:ℝ) ^ ((1:ℝ)/2) ≤ (m:ℝ) ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
    _ = (m:ℝ) := Real.rpow_one _

/-- The crude counting factor `4·Rred·S/m + 2·min(Rred,S)` of `FarExpSum_le_crude_unif` is
dominated by a constant multiple of the large-sieve bracket with the reduced box parameter
`⌈R/c⌉`. -/
lemma crude_factor_le_T11 {m c R S : ℕ} (hm : 1 ≤ m) (hc : 1 ≤ c) (hR : 1 ≤ R) (hS : 1 ≤ S)
    {ε : ℝ} (hε : 0 ≤ ε) :
    4 * (Rred c R : ℝ) * S / m + 2 * min (Rred c R : ℝ) S
      ≤ 10 * Work.FIArea4.p14T11 m (cR c R) S ε := by
  have hcR : 1 ≤ cR c R := cR_pos hc hR
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hSnn : (0:ℝ) ≤ (S:ℝ) := by positivity
  have hcR1 : (1:ℝ) ≤ (cR c R : ℝ) := by exact_mod_cast hcR
  have hRred : (Rred c R : ℝ) ≤ 2 * (cR c R : ℝ) := by
    have h := Rred_le_two_cR (c := c) (R := R) hc
    exact_mod_cast h
  have h4 : 4 * (Rred c R : ℝ) * S ≤ 8 * (cR c R : ℝ) * S := by nlinarith [hRred, hSnn]
  have hstep1 : 4 * (Rred c R : ℝ) * S / m ≤ 8 * (cR c R : ℝ) * S / m := by
    rw [div_le_div_iff_of_pos_right hmpos]; exact h4
  have hstep2 : 8 * (cR c R : ℝ) * S / m
      ≤ 8 * (m:ℝ)^(-(1:ℝ)/2) * (cR c R : ℝ) * S := by
    have hinv := one_div_le_rpow_neg_half m hm
    rw [div_eq_mul_one_div]
    rw [show (8 : ℝ) * (m:ℝ)^(-(1:ℝ)/2) * (cR c R : ℝ) * S
        = (8 * (cR c R : ℝ) * S) * ((m:ℝ)^(-(1:ℝ)/2)) by ring]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  have hterm1 : 4 * (Rred c R : ℝ) * S / m ≤ 8 * pT1 m (cR c R) S := by
    refine le_trans hstep1 ?_
    rw [show (8 : ℝ) * pT1 m (cR c R) S
        = 8 * (m:ℝ)^(-(1:ℝ)/2) * (cR c R : ℝ) * S by
      unfold pT1; ring]
    exact hstep2
  have hA : (1:ℝ) ≤ (cR c R : ℝ) ^ ((3:ℝ)/4) * (((cR c R : ℝ) * S) ^ ε) := by
    have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
    have h1 : (1:ℝ) ≤ (cR c R : ℝ) ^ ((3:ℝ)/4) := Real.one_le_rpow hcR1 (by norm_num)
    have h2 : (1:ℝ) ≤ ((cR c R : ℝ) * S) ^ ε :=
      Real.one_le_rpow (by nlinarith [hcR1, hS1]) hε
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ _ := mul_le_mul h1 h2 (by norm_num) (Real.rpow_nonneg (by positivity) _)
  have hterm2 : 2 * min (Rred c R : ℝ) S ≤ 2 * pT4 m (cR c R) S ε := by
    have h3 : (S:ℝ) ≤ (S:ℝ) * ((cR c R : ℝ) ^ ((3:ℝ)/4) * (((cR c R : ℝ) * S) ^ ε)) :=
      le_mul_of_one_le_right hSnn hA
    have h5 : 2 * min (Rred c R : ℝ) S ≤ 2 * (S:ℝ) := by
      have := min_le_right (Rred c R : ℝ) (S:ℝ); linarith
    calc 2 * min (Rred c R : ℝ) S ≤ 2 * (S:ℝ) := h5
      _ ≤ 2 * ((S:ℝ) * ((cR c R : ℝ) ^ ((3:ℝ)/4) * (((cR c R : ℝ) * S) ^ ε))) := by
          linarith
      _ = 2 * pT4 m (cR c R) S ε := by unfold pT4; ring
  have hT := p14T11_eq_sum m (cR c R) S ε
  have hp1 := pT1_nonneg m (cR c R) S
  have hp2 := pT2_nonneg m (cR c R) S ε
  have hp3 := pT3_nonneg m (cR c R) S ε
  have hp4 := pT4_nonneg m (cR c R) S ε
  rw [hT]
  linarith [hterm1, hterm2, hp1, hp2, hp3, hp4]

/-! ## 3. The exponential sums of a piece -/

/-- **The exponential sum of a dyadic `(m,c,Q)`-piece.**  Given the twisted coprime large sieve
(whose conclusion is passed as the hypothesis `hls`), the exponential sum of the piece is bounded by
`(log(2⌈R/c⌉) + 1)·p14T11 (mQ) (⌈R/c⌉) S ε'·p14L2 (⌈R/c⌉) S (redA c α)`. -/
theorem farExpSum_dyadic_le_of_ls (Cls : ℝ) (hCls : 0 < Cls) (ε' : ℝ)
    (hls : ∀ (m Q R S : ℕ) (β γ : ℕ → ℕ → ℂ) (A : ℕ → ℂ),
        1 ≤ m → 1 ≤ Q → 1 ≤ R → 1 ≤ S →
        (∀ r s, β r s ≠ 0 → Odd r) → (∀ r s, γ r s ≠ 0 → Odd r) →
        (∀ q, ‖A q‖ ≤ 1) →
        ‖∑ q ∈ Finset.Ioc Q (2 * Q), A q * pairSumCo R S (m * q) β γ‖
          ≤ Cls * Work.FIArea4.p14T11 (m * Q) R S ε' * (Real.log (2 * (R : ℝ)) + 1)
              * (Work.FIArea4.p14L2 R S β) ^ ((1 : ℝ) / 2)
              * (Work.FIArea4.p14L2 R S γ) ^ ((1 : ℝ) / 2)) :
    ∀ (D R S m c Q : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (u t : ℝ),
      1 ≤ D → 1 ≤ R → 1 ≤ S → 1 ≤ m → 1 ≤ c → m ∣ c → 1 ≤ Q →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
      ‖farExpSum D R S a b α m c Q (2 * Q) u t‖
        ≤ Cls * (Real.log (2 * (cR c R : ℝ)) + 1) * Work.FIArea4.p14T11 (m * Q) (cR c R) S ε'
            * Work.FIArea4.p14L2 (cR c R) S (redA c α) := by
  intro D R S m c Q a b α u t hD hR hS hm hc hmc hQ hcop hbox
  have hD0 : 0 < D := by omega
  have hcR : 1 ≤ cR c R := cR_pos hc hR
  have hLS := hls m Q (cR c R) S (farU m c α u t) (farV m c α u t)
      (fun q => ((c : ℂ) / ((q * D : ℕ) : ℂ)) ^ (Complex.I * (t : ℂ)))
      hm hQ hcR hS (farU_odd hcop) (farV_odd hcop) (fun q => norm_cpow_twist_le_one hc t)
  have hrew := farExpSum_eq_pairSumCo (D := D) (R := R) (S := S) (m := m) (c := c)
    (Q1 := Q) (Q2 := 2 * Q) (a := a) (b := b) (α := α) hD0 hR hS hc hmc hcop hbox u t
  have hL2U := p14L2_farU_le m c R S α u t
  have hL2V := p14L2_farV_le m c R S α u t
  have hL2nn : 0 ≤ Work.FIArea4.p14L2 (cR c R) S (redA c α) := p14L2_nonneg _ _ _
  have hsqrt : (Work.FIArea4.p14L2 (cR c R) S (farU m c α u t)) ^ ((1 : ℝ) / 2)
        * (Work.FIArea4.p14L2 (cR c R) S (farV m c α u t)) ^ ((1 : ℝ) / 2)
      ≤ Work.FIArea4.p14L2 (cR c R) S (redA c α) := by
    have h1 : (Work.FIArea4.p14L2 (cR c R) S (farU m c α u t)) ^ ((1 : ℝ) / 2)
        ≤ (Work.FIArea4.p14L2 (cR c R) S (redA c α)) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (p14L2_nonneg _ _ _) hL2U (by norm_num)
    have h2 : (Work.FIArea4.p14L2 (cR c R) S (farV m c α u t)) ^ ((1 : ℝ) / 2)
        ≤ (Work.FIArea4.p14L2 (cR c R) S (redA c α)) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (p14L2_nonneg _ _ _) hL2V (by norm_num)
    have h3 := mul_le_mul h1 h2 (Real.rpow_nonneg (p14L2_nonneg _ _ _) _)
      (Real.rpow_nonneg hL2nn _)
    have h4 : (Work.FIArea4.p14L2 (cR c R) S (redA c α)) ^ ((1 : ℝ) / 2)
        * (Work.FIArea4.p14L2 (cR c R) S (redA c α)) ^ ((1 : ℝ) / 2)
        = Work.FIArea4.p14L2 (cR c R) S (redA c α) := by
      rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt hL2nn]
    rw [h4] at h3
    exact h3
  rw [hrew]
  have hμ : ‖(((ArithmeticFunction.moebius m : ℤ)) : ℂ)‖ ≤ 1 := norm_moebius_cast_le_one m
  have hlogcR : (0:ℝ) < Real.log (2 * (cR c R : ℝ)) + 1 := by
    have h2 : (1:ℝ) ≤ 2 * (cR c R : ℝ) := by
      have h := cR_pos hc hR
      exact_mod_cast (by omega : 1 ≤ 2 * cR c R)
    have := Real.log_nonneg h2
    linarith
  calc ‖↑(ArithmeticFunction.moebius m) * (∑ q ∈ Finset.Ioc Q (2 * Q),
          ((c : ℂ) / ((q * D : ℕ) : ℂ)) ^ (Complex.I * (t : ℂ)) *
            pairSumCo (cR c R) S (m * q) (farU m c α u t) (farV m c α u t))‖
      = ‖(((ArithmeticFunction.moebius m : ℤ)) : ℂ)‖ * ‖(∑ q ∈ Finset.Ioc Q (2 * Q),
          ((c : ℂ) / ((q * D : ℕ) : ℂ)) ^ (Complex.I * (t : ℂ)) *
            pairSumCo (cR c R) S (m * q) (farU m c α u t) (farV m c α u t))‖ := norm_mul _ _
    _ ≤ 1 * ‖(∑ q ∈ Finset.Ioc Q (2 * Q),
          ((c : ℂ) / ((q * D : ℕ) : ℂ)) ^ (Complex.I * (t : ℂ)) *
            pairSumCo (cR c R) S (m * q) (farU m c α u t) (farV m c α u t))‖ :=
        mul_le_mul_of_nonneg_right hμ (norm_nonneg _)
    _ = ‖(∑ q ∈ Finset.Ioc Q (2 * Q),
          ((c : ℂ) / ((q * D : ℕ) : ℂ)) ^ (Complex.I * (t : ℂ)) *
            pairSumCo (cR c R) S (m * q) (farU m c α u t) (farV m c α u t))‖ := one_mul _
    _ ≤ Cls * Work.FIArea4.p14T11 (m * Q) (cR c R) S ε' * (Real.log (2 * (cR c R : ℝ)) + 1)
          * (Work.FIArea4.p14L2 (cR c R) S (farU m c α u t)) ^ ((1 : ℝ) / 2)
          * (Work.FIArea4.p14L2 (cR c R) S (farV m c α u t)) ^ ((1 : ℝ) / 2) := hLS
    _ = (Cls * Work.FIArea4.p14T11 (m * Q) (cR c R) S ε' * (Real.log (2 * (cR c R : ℝ)) + 1))
          * ((Work.FIArea4.p14L2 (cR c R) S (farU m c α u t)) ^ ((1 : ℝ) / 2)
              * (Work.FIArea4.p14L2 (cR c R) S (farV m c α u t)) ^ ((1 : ℝ) / 2)) := by ring
    _ ≤ (Cls * Work.FIArea4.p14T11 (m * Q) (cR c R) S ε' * (Real.log (2 * (cR c R : ℝ)) + 1))
          * Work.FIArea4.p14L2 (cR c R) S (redA c α) :=
        mul_le_mul_of_nonneg_left hsqrt
          (by have h1 := p14T11_nonneg (m * Q) (cR c R) S ε'
              exact mul_nonneg (mul_nonneg hCls.le h1) hlogcR.le)
    _ = Cls * (Real.log (2 * (cR c R : ℝ)) + 1) * Work.FIArea4.p14T11 (m * Q) (cR c R) S ε'
          * Work.FIArea4.p14L2 (cR c R) S (redA c α) := by ring

/-- **The exponential sum of the piece with flipped modulus `q' = 1`.**  The crude counting bound
`FarExpSum_le_crude_unif` gives the estimate with the reduced box `⌊2R/c⌋`, which is converted into
the reduced box `⌈R/c⌉` of the flip. -/
theorem farExpSum_one_le_of_crude (Ccr : ℝ) (hCcr : 0 < Ccr) (ε' : ℝ) (hε' : 0 ≤ ε')
    (hcr : ∀ (D R S : ℕ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      ∀ (a b : ℝ) (α : ℕ → ℕ → ℂ) (m c : ℕ) (u t : ℝ),
        1 ≤ c → 1 ≤ m →
        (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
        (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
        ‖farExpSum D R S a b α m c 0 1 u t‖
          ≤ Ccr * (4 * (Rred c R : ℝ) * S / m + 2 * min (Rred c R : ℝ) S)
              * Work.FIArea4.p14L2 (Rred c R) S (redA c α)) :
    ∀ (D R S m c : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (u t : ℝ),
      1 ≤ D → 1 ≤ R → 1 ≤ S → 1 ≤ m → 1 ≤ c →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
      ‖farExpSum D R S a b α m c 0 1 u t‖
        ≤ Ccr * 10 * (Real.log (2 * (cR c R : ℝ)) + 1)
            * Work.FIArea4.p14T11 m (cR c R) S ε'
            * Work.FIArea4.p14L2 (cR c R) S (redA c α) := by
  intro D R S m c a b α u t hD hR hS hm hc hcop hbox
  have h1 := hcr D R S hD hR hS a b α m c u t hc hm hcop hbox
  have hfac := crude_factor_le_T11 hm hc hR hS hε'
  have hL2eq := p14L2_Rred_eq_cR hc hbox
  rw [hL2eq] at h1
  have hT11nn : 0 ≤ Work.FIArea4.p14T11 m (cR c R) S ε' := p14T11_nonneg _ _ _ _
  have hL2nn : 0 ≤ Work.FIArea4.p14L2 (cR c R) S (redA c α) := p14L2_nonneg _ _ _
  have hlog1 : (1:ℝ) ≤ Real.log (2 * (cR c R : ℝ)) + 1 := by
    have h2 : (1:ℝ) ≤ 2 * (cR c R : ℝ) := by
      have h := cR_pos hc hR
      exact_mod_cast (by omega : 1 ≤ 2 * cR c R)
    have := Real.log_nonneg h2
    linarith
  have hstep : Ccr * (4 * (Rred c R : ℝ) * S / m + 2 * min (Rred c R : ℝ) S)
        * Work.FIArea4.p14L2 (cR c R) S (redA c α)
      ≤ Ccr * 10 * (Real.log (2 * (cR c R : ℝ)) + 1)
        * Work.FIArea4.p14T11 m (cR c R) S ε'
        * Work.FIArea4.p14L2 (cR c R) S (redA c α) := by
    have hfac' : Ccr * (4 * (Rred c R : ℝ) * S / m + 2 * min (Rred c R : ℝ) S)
        ≤ Ccr * (10 * Work.FIArea4.p14T11 m (cR c R) S ε') :=
      mul_le_mul_of_nonneg_left hfac hCcr.le
    have hlogm : Ccr * (10 * Work.FIArea4.p14T11 m (cR c R) S ε')
        ≤ Ccr * 10 * (Real.log (2 * (cR c R : ℝ)) + 1)
          * Work.FIArea4.p14T11 m (cR c R) S ε' := by
      have h2a : (10:ℝ) ≤ 10 * (Real.log (2 * (cR c R : ℝ)) + 1) := by
        have := mul_le_mul_of_nonneg_left hlog1 (by norm_num : (0:ℝ) ≤ 10)
        simpa using this
      have h2b : (10:ℝ) * Work.FIArea4.p14T11 m (cR c R) S ε'
          ≤ (10 * (Real.log (2 * (cR c R : ℝ)) + 1)) * Work.FIArea4.p14T11 m (cR c R) S ε' :=
        mul_le_mul_of_nonneg_right h2a hT11nn
      have h2c : Ccr * (10 * Work.FIArea4.p14T11 m (cR c R) S ε')
          ≤ Ccr * ((10 * (Real.log (2 * (cR c R : ℝ)) + 1))
              * Work.FIArea4.p14T11 m (cR c R) S ε') :=
        mul_le_mul_of_nonneg_left h2b hCcr.le
      calc Ccr * (10 * Work.FIArea4.p14T11 m (cR c R) S ε')
          ≤ Ccr * ((10 * (Real.log (2 * (cR c R : ℝ)) + 1))
              * Work.FIArea4.p14T11 m (cR c R) S ε') := h2c
        _ = Ccr * 10 * (Real.log (2 * (cR c R : ℝ)) + 1)
            * Work.FIArea4.p14T11 m (cR c R) S ε' := by ring
    calc Ccr * (4 * (Rred c R : ℝ) * S / m + 2 * min (Rred c R : ℝ) S)
          * Work.FIArea4.p14L2 (cR c R) S (redA c α)
        ≤ Ccr * (10 * Work.FIArea4.p14T11 m (cR c R) S ε')
          * Work.FIArea4.p14L2 (cR c R) S (redA c α) :=
          mul_le_mul_of_nonneg_right hfac' hL2nn
      _ ≤ Ccr * 10 * (Real.log (2 * (cR c R : ℝ)) + 1)
          * Work.FIArea4.p14T11 m (cR c R) S ε'
          * Work.FIArea4.p14L2 (cR c R) S (redA c α) := by
          refine le_trans (mul_le_mul_of_nonneg_right hlogm hL2nn) ?_
          exact le_of_eq (by ring)
  exact le_trans h1 hstep

/-! ## 4. The dyadic bound for one far piece -/

/-- **The dyadic bound for one `(m,c,Q)`-piece of the far sum**, given the twisted coprime large
sieve as an explicit input.  This is the body of `farInner_dyadic_bound`, isolated so that the
large-sieve input (proved in `pairSumCo_ls_twisted`) appears as a hypothesis. -/
theorem farInner_dyadic_bound_of_ls (h11 : Work.FIArea4.p14Prop111All) (ε : ℝ) (hε : 0 < ε)
    (hls : ∀ (ε' : ℝ), 0 < ε' → ∃ Cls : ℝ, 0 < Cls ∧
      ∀ (m Q R S : ℕ) (β γ : ℕ → ℕ → ℂ) (A : ℕ → ℂ),
        1 ≤ m → 1 ≤ Q → 1 ≤ R → 1 ≤ S →
        (∀ r s, β r s ≠ 0 → Odd r) → (∀ r s, γ r s ≠ 0 → Odd r) →
        (∀ q, ‖A q‖ ≤ 1) →
        ‖∑ q ∈ Finset.Ioc Q (2 * Q), A q * pairSumCo R S (m * q) β γ‖
          ≤ Cls * Work.FIArea4.p14T11 (m * Q) R S ε' * (Real.log (2 * (R : ℝ)) + 1)
              * (Work.FIArea4.p14L2 R S β) ^ ((1 : ℝ) / 2)
              * (Work.FIArea4.p14L2 R S γ) ^ ((1 : ℝ) / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S m c Q : ℕ) (a b H : ℝ) (α : ℕ → ℕ → ℂ),
      1 ≤ D → 1 ≤ R → 1 ≤ S → 1 ≤ m → 1 ≤ c → m ∣ c →
      D ≤ R * S → R * S < D * D →
      H = ((R:ℝ)*(S:ℝ)/(D:ℝ))^((1:ℝ)/3) →
      a = 2*(S:ℝ)/(H*(R:ℝ)) → b = 2*(S:ℝ)/(R:ℝ) →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
      ((1 ≤ Q → ‖farInner D R S a b α m c Q (2 * Q)‖
            ≤ C * (Real.log (2 + b / a) + 1) ^ 2 * (Real.log (2 * (cR c R : ℝ)) + 1)
                * Work.FIArea4.p14T11 (m * Q) (cR c R) S (ε / 4)
                * Work.FIArea4.p14L2 (cR c R) S (redA c α))
        ∧ (‖farInner D R S a b α m c 0 1‖
            ≤ C * (Real.log (2 + b / a) + 1) ^ 2 * (Real.log (2 * (cR c R : ℝ)) + 1)
                * Work.FIArea4.p14T11 m (cR c R) S (ε / 4)
                * Work.FIArea4.p14L2 (cR c R) S (redA c α))) := by
  obtain ⟨Csep, hCsep, hsep⟩ := farInner_bound_sep
  obtain ⟨Cls, hCls, hls'⟩ := hls (ε / 4) (by linarith)
  obtain ⟨Ccr, hCcr, hcr⟩ := FarExpSum_le_crude_unif
  have hCh1 : (0:ℝ) < Ccr * 10 := by positivity
  have hone := farExpSum_one_le_of_crude Ccr hCcr (ε / 4) (by linarith) hcr
  refine ⟨Csep * (Cls + Ccr * 10 + 1), by positivity, ?_⟩
  intro D R S m c Q a b H α hD hR hS hm hc hmc hDle hDsq hH ha hb hcop hbox
  have hD0 : 0 < D := by omega
  have hR0 : 0 < R := by omega
  have hD1 : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD0
  have hR1 : (0:ℝ) < (R:ℝ) := by exact_mod_cast hR0
  have hHpos : 0 < H := by
    rw [hH]; exact Real.rpow_pos_of_pos (by positivity) _
  have hH1 : 1 ≤ H := by
    rw [hH]
    refine Real.one_le_rpow ?_ (by norm_num)
    rw [le_div_iff₀ hD1]
    have h : (D:ℝ) ≤ (R:ℝ)*(S:ℝ) := by exact_mod_cast hDle
    linarith
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hHa : a = b / H := by rw [ha, hb]; field_simp
  have hab : a ≤ b := by
    rw [hHa, div_eq_mul_one_div]
    calc b * (1 / H) ≤ b * 1 := mul_le_mul_of_nonneg_left (by
            have h := one_div_le_one_div_of_le zero_lt_one hH1
            simpa using h) hb0
      _ = b := mul_one _
  have hapos : 0 < a := by
    rw [ha]; exact div_pos (by positivity) (mul_pos hHpos hR1)
  have hlogA : (1:ℝ) ≤ (Real.log (2 + b / a) + 1) ^ 2 := by
    have h2 : (1:ℝ) ≤ 2 + b / a := by
      have := div_nonneg hb0 hapos.le
      linarith
    have h3 : (1:ℝ) ≤ Real.log (2 + b / a) + 1 := by
      have := Real.log_nonneg h2
      linarith
    nlinarith [h3]
  have hlogcR : (1:ℝ) ≤ Real.log (2 * (cR c R : ℝ)) + 1 := by
    have h2 : (1:ℝ) ≤ 2 * (cR c R : ℝ) := by
      have h := cR_pos hc hR
      exact_mod_cast (by omega : 1 ≤ 2 * cR c R)
    have := Real.log_nonneg h2
    linarith
  have hL2nn : 0 ≤ Work.FIArea4.p14L2 (cR c R) S (redA c α) := p14L2_nonneg _ _ _
  have hCnn : (0:ℝ) ≤ Csep * (Real.log (2 + b / a) + 1) ^ 2 :=
    mul_nonneg hCsep.le (by positivity)
  constructor
  · intro hQ
    have hM : ∀ u t : ℝ, ‖farExpSum D R S a b α m c Q (2 * Q) u t‖
        ≤ Cls * (Real.log (2 * (cR c R : ℝ)) + 1)
            * Work.FIArea4.p14T11 (m * Q) (cR c R) S (ε / 4)
            * Work.FIArea4.p14L2 (cR c R) S (redA c α) := fun u t =>
      farExpSum_dyadic_le_of_ls Cls hCls (ε / 4) hls' D R S m c Q a b α u t
        hD hR hS hm hc hmc hQ hcop hbox
    have hstep : ‖farInner D R S a b α m c Q (2 * Q)‖
        ≤ Csep * (Real.log (2 + b / a) + 1) ^ 2
          * (Cls * (Real.log (2 * (cR c R : ℝ)) + 1)
              * Work.FIArea4.p14T11 (m * Q) (cR c R) S (ε / 4)
              * Work.FIArea4.p14L2 (cR c R) S (redA c α)) := hsep hapos hab hD0 hM
    have hkey : Cls * (Real.log (2 * (cR c R : ℝ)) + 1)
          * Work.FIArea4.p14T11 (m * Q) (cR c R) S (ε / 4)
          * Work.FIArea4.p14L2 (cR c R) S (redA c α)
        ≤ (Cls + Ccr * 10 + 1) * (Real.log (2 * (cR c R : ℝ)) + 1)
          * Work.FIArea4.p14T11 (m * Q) (cR c R) S (ε / 4)
          * Work.FIArea4.p14L2 (cR c R) S (redA c α) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith [hCcr.le]) (by linarith [hlogcR]))
          (p14T11_nonneg _ _ _ _))
        hL2nn
    refine le_trans hstep ?_
    calc Csep * (Real.log (2 + b / a) + 1) ^ 2 * (Cls * (Real.log (2 * (cR c R : ℝ)) + 1)
            * Work.FIArea4.p14T11 (m * Q) (cR c R) S (ε / 4)
            * Work.FIArea4.p14L2 (cR c R) S (redA c α))
        = (Csep * (Real.log (2 + b / a) + 1) ^ 2) * (Cls * (Real.log (2 * (cR c R : ℝ)) + 1)
            * Work.FIArea4.p14T11 (m * Q) (cR c R) S (ε / 4)
            * Work.FIArea4.p14L2 (cR c R) S (redA c α)) := by ring
      _ ≤ (Csep * (Real.log (2 + b / a) + 1) ^ 2) * ((Cls + Ccr * 10 + 1)
            * (Real.log (2 * (cR c R : ℝ)) + 1)
            * Work.FIArea4.p14T11 (m * Q) (cR c R) S (ε / 4)
            * Work.FIArea4.p14L2 (cR c R) S (redA c α)) :=
          mul_le_mul_of_nonneg_left hkey hCnn
      _ = Csep * (Cls + Ccr * 10 + 1) * (Real.log (2 + b / a) + 1) ^ 2
            * (Real.log (2 * (cR c R : ℝ)) + 1)
            * Work.FIArea4.p14T11 (m * Q) (cR c R) S (ε / 4)
            * Work.FIArea4.p14L2 (cR c R) S (redA c α) := by ring
  · have hM : ∀ u t : ℝ, ‖farExpSum D R S a b α m c 0 1 u t‖
        ≤ (Ccr * 10) * (Real.log (2 * (cR c R : ℝ)) + 1)
            * Work.FIArea4.p14T11 m (cR c R) S (ε / 4)
            * Work.FIArea4.p14L2 (cR c R) S (redA c α) := fun u t =>
      hone D R S m c a b α u t hD hR hS hm hc hcop hbox
    have hstep : ‖farInner D R S a b α m c 0 1‖
        ≤ Csep * (Real.log (2 + b / a) + 1) ^ 2
          * ((Ccr * 10) * (Real.log (2 * (cR c R : ℝ)) + 1)
              * Work.FIArea4.p14T11 m (cR c R) S (ε / 4)
              * Work.FIArea4.p14L2 (cR c R) S (redA c α)) := hsep hapos hab hD0 hM
    have hkey : (Ccr * 10) * (Real.log (2 * (cR c R : ℝ)) + 1)
          * Work.FIArea4.p14T11 m (cR c R) S (ε / 4)
          * Work.FIArea4.p14L2 (cR c R) S (redA c α)
        ≤ (Cls + Ccr * 10 + 1) * (Real.log (2 * (cR c R : ℝ)) + 1)
          * Work.FIArea4.p14T11 m (cR c R) S (ε / 4)
          * Work.FIArea4.p14L2 (cR c R) S (redA c α) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith [hCh1, hCls]) (by linarith [hlogcR]))
          (p14T11_nonneg _ _ _ _))
        hL2nn
    refine le_trans hstep ?_
    calc Csep * (Real.log (2 + b / a) + 1) ^ 2 * ((Ccr * 10) * (Real.log (2 * (cR c R : ℝ)) + 1)
            * Work.FIArea4.p14T11 m (cR c R) S (ε / 4)
            * Work.FIArea4.p14L2 (cR c R) S (redA c α))
        = (Csep * (Real.log (2 + b / a) + 1) ^ 2) * ((Ccr * 10) * (Real.log (2 * (cR c R : ℝ)) + 1)
            * Work.FIArea4.p14T11 m (cR c R) S (ε / 4)
            * Work.FIArea4.p14L2 (cR c R) S (redA c α)) := by ring
      _ ≤ (Csep * (Real.log (2 + b / a) + 1) ^ 2) * ((Cls + Ccr * 10 + 1)
            * (Real.log (2 * (cR c R : ℝ)) + 1)
            * Work.FIArea4.p14T11 m (cR c R) S (ε / 4)
            * Work.FIArea4.p14L2 (cR c R) S (redA c α)) :=
          mul_le_mul_of_nonneg_left hkey hCnn
      _ = Csep * (Cls + Ccr * 10 + 1) * (Real.log (2 + b / a) + 1) ^ 2
            * (Real.log (2 * (cR c R : ℝ)) + 1)
            * Work.FIArea4.p14T11 m (cR c R) S (ε / 4)
            * Work.FIArea4.p14L2 (cR c R) S (redA c α) := by ring

/-- **The dyadic bound for one `(m,c,Q)`-piece of the far sum** (FI §12).  For a vector `α`
supported in the dyadic box `(R,2R] × (S,2S]` with `(r,2s) = 1`, in the range `D ≤ RS < D²`, with
the separation parameters `H = (RS/D)^{1/3}`, `a = 2S/(HR)`, `b = 2S/R`, each `(m,c,Q)`-piece of the
far sum is bounded by `(log(2 + b/a) + 1)²(log(2⌈R/c⌉) + 1)` times the large-sieve bracket
`p14T11 (mQ) (⌈R/c⌉) S (ε/4)` and the energy `p14L2 (⌈R/c⌉) S (redA c α)`; the piece with flipped
modulus `q' = 1` obeys the same bound with `p14T11 m (⌈R/c⌉) S (ε/4)`. -/
theorem farInner_dyadic_bound (h11 : Work.FIArea4.p14Prop111All) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S m c Q : ℕ) (a b H : ℝ) (α : ℕ → ℕ → ℂ),
      1 ≤ D → 1 ≤ R → 1 ≤ S → 1 ≤ m → 1 ≤ c → m ∣ c →
      D ≤ R * S → R * S < D * D →
      H = ((R:ℝ)*(S:ℝ)/(D:ℝ))^((1:ℝ)/3) →
      a = 2*(S:ℝ)/(H*(R:ℝ)) → b = 2*(S:ℝ)/(R:ℝ) →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
      ((1 ≤ Q → ‖farInner D R S a b α m c Q (2 * Q)‖
            ≤ C * (Real.log (2 + b / a) + 1) ^ 2 * (Real.log (2 * (cR c R : ℝ)) + 1)
                * Work.FIArea4.p14T11 (m * Q) (cR c R) S (ε / 4)
                * Work.FIArea4.p14L2 (cR c R) S (redA c α))
        ∧ (‖farInner D R S a b α m c 0 1‖
            ≤ C * (Real.log (2 + b / a) + 1) ^ 2 * (Real.log (2 * (cR c R : ℝ)) + 1)
                * Work.FIArea4.p14T11 m (cR c R) S (ε / 4)
                * Work.FIArea4.p14L2 (cR c R) S (redA c α))) :=
  farInner_dyadic_bound_of_ls h11 ε hε (pairSumCo_ls_twisted h11)

end

end Work.FIArea4.Vflip.Vfd
