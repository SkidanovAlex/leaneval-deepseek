import Mathlib
import Submission.Work.Peluse.ExpA.Defs
import Submission.Work.Peluse.Holds.ExpPET.Jensen
import Submission.Work.Peluse.Holds.ExpPET.existsPairExpansion

set_option maxHeartbeats 1000000
open scoped BigOperators

namespace Work.Peluse.ExpA

/-- The norm of a complex number multiplied by the inverse of a positive natural number. -/
private lemma norm_inv_natCast_mul (M : ℕ) (hM : 1 ≤ M) (z : ℂ) :
    ‖(((M : ℂ))⁻¹) * z‖ = ((M : ℝ))⁻¹ * ‖z‖ := by
  rw [norm_mul]
  congr 1
  rw [norm_inv, Complex.norm_natCast]

theorem avgExtraction {s M₁ M₂ : ℕ} (hs : 1 ≤ s) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (c : ℤ)
    (b : Fin s → ℤ) (S : Finset ℤ) (f : ℤ → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hfin : Work.Peluse.FinSuppZ f)
    (hbox : δ ^ (2 ^ s) ≤ ((M₂ : ℝ))⁻¹ * ∑ a ∈ Finset.Icc 1 M₂,
        Work.Peluse.boxNormPow s (fun i : Fin s => Work.Peluse.arithIcc (c * (a : ℤ) + b i) M₁)
          S f) :
    δ ^ (2 ^ s) * (S.card : ℝ) ≤ (((M₁ : ℝ) ^ s) ^ 2)⁻¹ *
      ∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
        ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
          ‖((M₂ : ℂ))⁻¹ * (∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
            Work.Peluse.Holds.ExpPET.expCube (fun i : Fin s => c * (a : ℤ) + b i)
              (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x)‖ := by
  classical
  -- (0) the box sum is a nonnegative real
  have hreal : ∀ a ∈ Finset.Icc 1 M₂,
      Work.Peluse.boxSumPow s (fun i : Fin s => Work.Peluse.arithIcc (c * (a : ℤ) + b i) M₁) S f
        = ((Work.Peluse.boxNormPow s
            (fun i : Fin s => Work.Peluse.arithIcc (c * (a : ℤ) + b i) M₁) S f : ℝ) : ℂ) :=
    fun a _ => Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow hs hfin
  have hreal' : ∀ a ∈ Finset.Icc 1 M₂,
      Work.Peluse.boxNormPow s
          (fun i : Fin s => Work.Peluse.arithIcc (c * (a : ℤ) + b i) M₁) S f
        = (Work.Peluse.boxSumPow s
            (fun i : Fin s => Work.Peluse.arithIcc (c * (a : ℤ) + b i) M₁) S f).re := by
    intro a ha
    rw [hreal a ha, Complex.ofReal_re]
  have hnorm : (∑ a ∈ Finset.Icc 1 M₂,
        Work.Peluse.boxNormPow s
          (fun i : Fin s => Work.Peluse.arithIcc (c * (a : ℤ) + b i) M₁) S f)
      = (∑ a ∈ Finset.Icc 1 M₂,
          Work.Peluse.boxSumPow s
            (fun i : Fin s => Work.Peluse.arithIcc (c * (a : ℤ) + b i) M₁) S f).re := by
    rw [Finset.sum_congr rfl hreal']
    simp only [← Complex.coe_reAddGroupHom]
    exact (map_sum Complex.reAddGroupHom
      (fun a : ℕ => Work.Peluse.boxSumPow s
        (fun i : Fin s => Work.Peluse.arithIcc (c * (a : ℤ) + b i) M₁) S f)
      (Finset.Icc 1 M₂)).symm
  -- (1) the expansion of the box sum at the arithmetic-progression direction sets
  have hexp : ∀ a : ℕ,
      Work.Peluse.boxSumPow s
          (fun i : Fin s => Work.Peluse.arithIcc (c * (a : ℤ) + b i) M₁) S f
        = ((S.card : ℂ))⁻¹ * ((∏ i : Fin s, (((M₁ : ℂ))⁻¹)) ^ 2
            * (∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
                ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
                  ∑' x : ℤ, Work.Peluse.Holds.ExpPET.expCube
                    (fun i : Fin s => c * (a : ℤ) + b i)
                    (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x)) :=
    fun a => Work.Peluse.Holds.ExpPET.boxSumPow_arithIcc_eq hM₁
      (fun i : Fin s => c * (a : ℤ) + b i) S f
  -- (2) Fubini
  have hsum : (∑ a ∈ Finset.Icc 1 M₂,
        Work.Peluse.boxSumPow s
          (fun i : Fin s => Work.Peluse.arithIcc (c * (a : ℤ) + b i) M₁) S f)
      = ((S.card : ℂ))⁻¹ * ((∏ i : Fin s, (((M₁ : ℂ))⁻¹)) ^ 2
          * (∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
              ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
                ∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
                  Work.Peluse.Holds.ExpPET.expCube
                    (fun i : Fin s => c * (a : ℤ) + b i)
                    (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x)) := by
    rw [Finset.sum_congr rfl (fun a _ => hexp a), ← Finset.mul_sum]
    congr 1
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm (s := Finset.Icc 1 M₂)
      (t := (Finset.univ : Finset ((i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁})))]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact Finset.sum_comm (s := Finset.Icc 1 M₂)
      (t := (Finset.univ : Finset ((i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁})))
  -- the label sum, as a single complex number
  set T : ℂ := (∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
      ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
        ∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
          Work.Peluse.Holds.ExpPET.expCube (fun i : Fin s => c * (a : ℤ) + b i)
            (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x) with hT
  -- (3) the constants are real
  have hre1 : ((S.card : ℂ))⁻¹ = ((((S.card : ℝ))⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast]
    exact (Complex.ofReal_inv (S.card : ℝ)).symm
  have hK : (∏ i : Fin s, (((M₁ : ℂ))⁻¹)) ^ 2 = ((((((M₁ : ℝ))⁻¹) ^ s) ^ 2 : ℝ) : ℂ) := by
    have h1 : (∏ i : Fin s, (((M₁ : ℂ))⁻¹)) = (((((M₁ : ℝ))⁻¹) ^ s : ℝ) : ℂ) := by
      rw [Finset.prod_const, Finset.card_fin]
      rw [show (M₁ : ℂ) = (((M₁ : ℝ)) : ℂ) from (Complex.ofReal_natCast M₁).symm,
        ← Complex.ofReal_inv, ← Complex.ofReal_pow]
    rw [h1, ← Complex.ofReal_pow]
  have hreT : (∑ a ∈ Finset.Icc 1 M₂,
        Work.Peluse.boxSumPow s
          (fun i : Fin s => Work.Peluse.arithIcc (c * (a : ℤ) + b i) M₁) S f).re
      = ((S.card : ℝ))⁻¹ * (((((M₁ : ℝ))⁻¹) ^ s) ^ 2) * T.re := by
    rw [hsum, hre1, hK]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  -- (4) positivity of the ingredients
  have hM1r : (0 : ℝ) < (M₁ : ℝ) := by exact_mod_cast hM₁
  have hM2r : (0 : ℝ) < (M₂ : ℝ) := by exact_mod_cast hM₂
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by
    rcases Nat.eq_zero_or_pos S.card with h | h
    · exfalso
      have h0 : ((S.card : ℂ))⁻¹ = 0 := by rw [h]; simp
      have h6 : (∑ a ∈ Finset.Icc 1 M₂,
          Work.Peluse.boxSumPow s
            (fun i : Fin s => Work.Peluse.arithIcc (c * (a : ℤ) + b i) M₁) S f) = 0 := by
        rw [hsum, h0, zero_mul]
      rw [hnorm, h6, Complex.zero_re, mul_zero] at hbox
      have hpos : 0 < δ ^ (2 ^ s) := pow_pos hδ _
      linarith
    · exact_mod_cast h
  have hp : (0 : ℝ) < ((((M₁ : ℝ))⁻¹) ^ s) ^ 2 := by positivity
  -- (5) the lower bound for the real part of the label sum
  have hTlow : δ ^ (2 ^ s) * ((M₂ : ℝ) * (S.card : ℝ) * (((((M₁ : ℝ))⁻¹) ^ s) ^ 2)⁻¹)
      ≤ T.re := by
    have h1 := hbox
    rw [hnorm, hreT] at h1
    have h3 := mul_le_mul_of_nonneg_right h1
      (by positivity : (0 : ℝ) ≤ (M₂ : ℝ) * (S.card : ℝ) * (((((M₁ : ℝ))⁻¹) ^ s) ^ 2)⁻¹)
    have hM2ne : (M₂ : ℝ) ≠ 0 := ne_of_gt hM2r
    have hSne : (S.card : ℝ) ≠ 0 := ne_of_gt hSpos
    have hpne : ((((M₁ : ℝ))⁻¹) ^ s) ^ 2 ≠ 0 := ne_of_gt hp
    have h4 : ((M₂ : ℝ))⁻¹ * (((S.card : ℝ))⁻¹ * (((((M₁ : ℝ))⁻¹) ^ s) ^ 2) * T.re)
          * ((M₂ : ℝ) * (S.card : ℝ) * (((((M₁ : ℝ))⁻¹) ^ s) ^ 2)⁻¹) = T.re := by
      field_simp
    rw [h4] at h3
    exact h3
  -- (6) the norm of the label sum dominates its real part
  have hnormT : T.re ≤ ∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
        ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
          ‖∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
            Work.Peluse.Holds.ExpPET.expCube (fun i : Fin s => c * (a : ℤ) + b i)
              (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x‖ := by
    refine le_trans (Complex.re_le_norm T) ?_
    rw [hT]
    calc ‖∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
            ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
              ∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
                Work.Peluse.Holds.ExpPET.expCube (fun i : Fin s => c * (a : ℤ) + b i)
                  (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x‖
        ≤ ∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
            ‖∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
              ∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
                Work.Peluse.Holds.ExpPET.expCube (fun i : Fin s => c * (a : ℤ) + b i)
                  (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
            ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
              ‖∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
                  Work.Peluse.Holds.ExpPET.expCube (fun i : Fin s => c * (a : ℤ) + b i)
                    (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x‖ :=
          Finset.sum_le_sum fun k _ => norm_sum_le _ _
  have hmain : δ ^ (2 ^ s) * ((M₂ : ℝ) * (S.card : ℝ) * (((((M₁ : ℝ))⁻¹) ^ s) ^ 2)⁻¹)
      ≤ ∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
          ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
            ‖∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
                Work.Peluse.Holds.ExpPET.expCube (fun i : Fin s => c * (a : ℤ) + b i)
                  (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x‖ :=
    le_trans hTlow hnormT
  -- (7) assembly: normalising the inner sums by `M₂⁻¹` and the outer sum by `(M₁^s)⁻²`
  have hinnerfac : ∀ (k k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁}),
      ‖((M₂ : ℂ))⁻¹ * (∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
            Work.Peluse.Holds.ExpPET.expCube (fun i : Fin s => c * (a : ℤ) + b i)
              (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x)‖
        = ((M₂ : ℝ))⁻¹ * ‖(∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
            Work.Peluse.Holds.ExpPET.expCube (fun i : Fin s => c * (a : ℤ) + b i)
              (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x)‖ :=
    fun k k' => norm_inv_natCast_mul M₂ hM₂ _
  have hsumfac : (∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
        ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
          ‖((M₂ : ℂ))⁻¹ * (∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
            Work.Peluse.Holds.ExpPET.expCube (fun i : Fin s => c * (a : ℤ) + b i)
              (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x)‖)
      = ((M₂ : ℝ))⁻¹ * ∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
          ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
            ‖∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
              Work.Peluse.Holds.ExpPET.expCube (fun i : Fin s => c * (a : ℤ) + b i)
                (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k' _ => hinnerfac k k'
  have hfin_eq : (((M₁ : ℝ) ^ s) ^ 2)⁻¹ = ((((M₁ : ℝ))⁻¹) ^ s) ^ 2 := by
    rw [← Work.Peluse.Holds.ExpPET.inv_labelNorm s M₁, inv_inv]
  rw [hfin_eq, hsumfac]
  have h2 : ((((M₁ : ℝ))⁻¹) ^ s) ^ 2
        * ((M₂ : ℝ)⁻¹ * (δ ^ (2 ^ s)
            * ((M₂ : ℝ) * (S.card : ℝ) * (((((M₁ : ℝ))⁻¹) ^ s) ^ 2)⁻¹)))
      = δ ^ (2 ^ s) * (S.card : ℝ) := by
    have hM2ne : (M₂ : ℝ) ≠ 0 := ne_of_gt hM2r
    have hpne : ((((M₁ : ℝ))⁻¹) ^ s) ^ 2 ≠ 0 := ne_of_gt hp
    field_simp
  have h3 := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hmain (by positivity : (0 : ℝ) ≤ ((M₂ : ℝ))⁻¹))
    (by positivity : (0 : ℝ) ≤ ((((M₁ : ℝ))⁻¹) ^ s) ^ 2)
  rw [h2] at h3
  exact h3

end Work.Peluse.ExpA
