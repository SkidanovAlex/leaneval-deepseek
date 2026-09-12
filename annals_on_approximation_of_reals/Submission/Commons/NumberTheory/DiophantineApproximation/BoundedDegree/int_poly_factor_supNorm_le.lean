import Mathlib.Analysis.Polynomial.MahlerMeasure

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

open Polynomial

private lemma supNorm_map_eq {A B : Type*} [NormedRing A] [NormedRing B] (p : Polynomial A)
    (f : A →+* B) (h_norm : ∀ a, ‖f a‖ = ‖a‖) : (p.map f).supNorm = p.supNorm := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := (p.map f).exists_eq_supNorm
    rw [hi]
    calc
      ‖(p.map f).coeff i‖ = ‖f (p.coeff i)‖ := by rw [Polynomial.coeff_map]
      _ = ‖p.coeff i‖ := h_norm (p.coeff i)
      _ ≤ p.supNorm := p.le_supNorm i
  · obtain ⟨i, hi⟩ := p.exists_eq_supNorm
    rw [hi]
    calc
      ‖p.coeff i‖ = ‖f (p.coeff i)‖ := (h_norm (p.coeff i)).symm
      _ = ‖(p.map f).coeff i‖ := by rw [Polynomial.coeff_map]
      _ ≤ (p.map f).supNorm := (p.map f).le_supNorm i

private lemma norm_int_real (z : ℤ) : ‖(z : ℝ)‖ = ‖z‖ := by
  rw [Real.norm_eq_abs, Int.norm_eq_abs, ← Int.cast_abs]

private lemma norm_int_complex (z : ℤ) : ‖(z : ℂ)‖ = ‖z‖ := by
  exact Complex.isometry_intCast.norm_map_of_map_zero (by simp) z

/-- For an integer polynomial the sup norm is the same whether we view the coefficients
in `ℝ` or in `ℂ`. -/
private lemma int_supNorm_real_eq_complex (S : Polynomial ℤ) :
    (S.map (Int.castRingHom ℝ)).supNorm = (S.map (Int.castRingHom ℂ)).supNorm := by
  calc
    (S.map (Int.castRingHom ℝ)).supNorm = S.supNorm :=
      supNorm_map_eq S (Int.castRingHom ℝ) norm_int_real
    _ = (S.map (Int.castRingHom ℂ)).supNorm :=
      (supNorm_map_eq S (Int.castRingHom ℂ) norm_int_complex).symm

/-- The sup-norm (maximal absolute coefficient) of an integer polynomial which divides
another integer polynomial `Q` is controlled by the sup-norm of `Q`, with a constant
depending only on a common bound `n` for the degrees. This is Mahler's factor bound:
`height P ≤ 2^n √(n+1) height Q`. -/
theorem int_poly_factor_supNorm_le (n : ℕ) {P Q : Polynomial ℤ} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hdegP : P.natDegree ≤ n) (hdegQ : Q.natDegree ≤ n) (hdiv : P ∣ Q) :
    (P.map (Int.castRingHom ℝ)).supNorm ≤
      (2 : ℝ) ^ n * Real.sqrt (n + 1) * (Q.map (Int.castRingHom ℝ)).supNorm := by
  rcases hdiv with ⟨R, hR⟩
  have hRne : R ≠ 0 := by
    intro hR0
    apply hQ
    rw [hR, hR0, mul_zero]
  let PC : Polynomial ℂ := P.map (Int.castRingHom ℂ)
  let QC : Polynomial ℂ := Q.map (Int.castRingHom ℂ)
  let RC : Polynomial ℂ := R.map (Int.castRingHom ℂ)
  have hPC : PC ≠ 0 := by
    dsimp [PC]
    exact (Polynomial.map_eq_zero_iff (f := Int.castRingHom ℂ) Int.cast_injective).not.mpr hP
  have hQC : QC ≠ 0 := by
    dsimp [QC]
    exact (Polynomial.map_eq_zero_iff (f := Int.castRingHom ℂ) Int.cast_injective).not.mpr hQ
  have hRC : RC ≠ 0 := by
    dsimp [RC]
    exact (Polynomial.map_eq_zero_iff (f := Int.castRingHom ℂ) Int.cast_injective).not.mpr hRne
  have hmul : QC = PC * RC := by
    dsimp [QC, PC, RC]
    rw [hR, Polynomial.map_mul]
  have hdegPC : PC.natDegree ≤ n := by
    dsimp [PC]
    rw [Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℂ) Int.cast_injective]
    exact hdegP
  have hdegQC : QC.natDegree ≤ n := by
    dsimp [QC]
    rw [Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℂ) Int.cast_injective]
    exact hdegQ
  -- the leading coefficient of `R` is a nonzero integer, so its Mahler measure is ≥ 1
  have hlc_map : RC.leadingCoeff = ((R.leadingCoeff : ℤ) : ℂ) := by
    dsimp [RC]
    exact Polynomial.leadingCoeff_map_of_injective (f := Int.castRingHom ℂ) Int.cast_injective R
  have hlc_ne : R.leadingCoeff ≠ 0 := (Polynomial.leadingCoeff_eq_zero.not.mpr hRne)
  have hlcR : (1 : ℝ) ≤ ‖RC.leadingCoeff‖ := by
    rw [hlc_map]
    have hRnorm : (1 : ℝ) ≤ ‖(((R.leadingCoeff : ℤ) : ℂ))‖ := by
      rw [norm_int_complex R.leadingCoeff]
      -- ‖z‖ for z : ℤ is ≥ 1 for a nonzero integer
      rw [Int.norm_eq_abs]
      have hle : (1 : ℤ) ≤ |R.leadingCoeff| := Int.one_le_abs hlc_ne
      exact_mod_cast hle
    exact hRnorm
  have hM1 : (1 : ℝ) ≤ RC.mahlerMeasure :=
    one_le_mahlerMeasure_of_one_le_norm_leadingCoeff hlcR
  -- Mahler measure of `P` is at most that of `Q = P·R`
  have hM : PC.mahlerMeasure ≤ QC.mahlerMeasure := by
    rw [hmul, mahlerMeasure_mul]
    exact le_mul_of_one_le_right PC.mahlerMeasure_nonneg hM1
  -- the bound supNorm P ≤ 2^deg P * M(P)
  have hbinom : PC.supNorm ≤ (2 : ℝ) ^ PC.natDegree * PC.mahlerMeasure := by
    calc
      PC.supNorm ≤ (PC.natDegree.choose (PC.natDegree / 2) : ℝ) * PC.mahlerMeasure :=
        PC.supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure
      _ ≤ (2 : ℝ) ^ PC.natDegree * PC.mahlerMeasure := by
        have hb : (PC.natDegree.choose (PC.natDegree / 2) : ℝ) ≤ (2 : ℝ) ^ PC.natDegree := by
          exact_mod_cast Nat.choose_le_two_pow PC.natDegree (PC.natDegree / 2)
        exact mul_le_mul_of_nonneg_right hb PC.mahlerMeasure_nonneg
  -- √(deg Q + 1) ≤ √(n + 1)
  have hsqrt : Real.sqrt ((QC.natDegree : ℝ) + 1) ≤ Real.sqrt ((n : ℝ) + 1) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.succ_le_succ hdegQC)
  have hnonnegQsup : (0 : ℝ) ≤ QC.supNorm := QC.supNorm_nonneg
  calc
    (P.map (Int.castRingHom ℝ)).supNorm
        = PC.supNorm := by simpa [PC] using int_supNorm_real_eq_complex P
    _ ≤ (2 : ℝ) ^ PC.natDegree * PC.mahlerMeasure := hbinom
    _ ≤ (2 : ℝ) ^ PC.natDegree * QC.mahlerMeasure := by
        exact mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ (2 : ℝ) ^ PC.natDegree)
    _ ≤ (2 : ℝ) ^ PC.natDegree * (Real.sqrt ((QC.natDegree : ℝ) + 1) * QC.supNorm) := by
        have hMQC : QC.mahlerMeasure ≤ Real.sqrt ((QC.natDegree : ℝ) + 1) * QC.supNorm :=
          QC.mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm
        exact mul_le_mul_of_nonneg_left hMQC (by positivity : 0 ≤ (2 : ℝ) ^ PC.natDegree)
    _ ≤ (2 : ℝ) ^ PC.natDegree * (Real.sqrt ((n : ℝ) + 1) * QC.supNorm) := by
        have hs : (Real.sqrt ((QC.natDegree : ℝ) + 1) : ℝ) * QC.supNorm ≤
            Real.sqrt ((n : ℝ) + 1) * QC.supNorm :=
          mul_le_mul_of_nonneg_right hsqrt hnonnegQsup
        exact mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (2 : ℝ) ^ PC.natDegree)
    _ ≤ (2 : ℝ) ^ n * (Real.sqrt ((n : ℝ) + 1) * QC.supNorm) := by
        have hpow : (2 : ℝ) ^ PC.natDegree ≤ (2 : ℝ) ^ n := by
          exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) hdegPC
        have hsq : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) * QC.supNorm := by
          positivity
        exact mul_le_mul_of_nonneg_right hpow hsq
    _ = (2 : ℝ) ^ n * Real.sqrt (n + 1) * QC.supNorm := by ring
    _ = (2 : ℝ) ^ n * Real.sqrt (n + 1) * (Q.map (Int.castRingHom ℝ)).supNorm := by
        rw [← int_supNorm_real_eq_complex Q]

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree
