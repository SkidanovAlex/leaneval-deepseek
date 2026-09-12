import Mathlib
import Submission.Szemeredi.Removal.GencountMain

/-!
# Smallness of the counting-lemma constants

This file bounds the constants `ThetaC` and `XC` of the generalized counting lemma by
explicit quantities, and shows (for the concrete growth function `F n = 2^n`) that they can be
made small by taking the complexity bound `Md` large.
-/

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Szemeredi.Removal

/-! ## The pure `ρ`-recursion -/

/-- The pure recursion bounding `XC`: `Xbd 0 m = 1`,
`Xbd (D+1) m = Xbd D m + m * (2 * Xbd D (2m) + 1)`. -/
noncomputable def Xbd : ℕ → ℕ → ℝ
  | 0, _ => 1
  | (D + 1), m => Xbd D m + (m : ℝ) * (2 * Xbd D (2 * m) + 1)

@[simp] theorem Xbd_zero (m : ℕ) : Xbd 0 m = 1 := rfl

theorem Xbd_succ (D m : ℕ) :
    Xbd (D + 1) m = Xbd D m + (m : ℝ) * (2 * Xbd D (2 * m) + 1) := rfl

theorem Xbd_one_le (D : ℕ) : ∀ m, 1 ≤ Xbd D m := by
  induction D with
  | zero => intro m; simp
  | succ D ih =>
    intro m
    rw [Xbd_succ]
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have h1 : (0 : ℝ) ≤ Xbd D (2 * m) := le_trans (by norm_num) (ih (2 * m))
    have h2 : (1 : ℝ) ≤ Xbd D m := ih m
    nlinarith

theorem Xbd_nonneg (D m : ℕ) : 0 ≤ Xbd D m := le_trans (by norm_num) (Xbd_one_le D m)

theorem Xbd_mono_m : ∀ D : ℕ, Monotone (Xbd D) := by
  intro D
  induction D with
  | zero => intro a b _; simp
  | succ D ih =>
    intro m m' hmm'
    rw [Xbd_succ, Xbd_succ]
    have h1 : Xbd D m ≤ Xbd D m' := ih hmm'
    have h2 : Xbd D (2 * m) ≤ Xbd D (2 * m') := ih (by omega)
    have h3 : (0 : ℝ) ≤ Xbd D (2 * m') := Xbd_nonneg D (2 * m')
    have h4 : (m : ℝ) ≤ (m' : ℝ) := by exact_mod_cast hmm'
    nlinarith

theorem Xbd_mono_D {D D' : ℕ} (h : D ≤ D') (m : ℕ) : Xbd D m ≤ Xbd D' m := by
  induction h with
  | refl => exact le_rfl
  | step hle ih =>
    rename_i D1
    rw [Xbd_succ]
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have h1 : (0 : ℝ) ≤ 2 * Xbd D1 (2 * m) + 1 := by
      have := Xbd_nonneg D1 (2 * m); linarith
    nlinarith

theorem Xbd_mono {D D' m m' : ℕ} (hD : D ≤ D') (hm : m ≤ m') : Xbd D m ≤ Xbd D' m' :=
  le_trans (Xbd_mono_m D hm) (Xbd_mono_D hD m')

/-- `XC` is bounded by the pure recursion `Xbd`. -/
theorem XC_le_Xbd {F M : ℕ → ℕ} (hF : ∀ n, 1 ≤ F n) :
    ∀ D m : ℕ, XC F M D m ≤ Xbd D m := by
  intro D
  induction D with
  | zero => intro m; simp
  | succ D ih =>
    intro m
    rw [XC_succ, Xbd_succ]
    have hsum : ∑ j ∈ Finset.range m,
        (CBc F M (D + 1) (j + 1) (XC F M D) + 1)
        ≤ (m : ℝ) * (2 * Xbd D (2 * m) + 1) := by
      have hterm : ∀ j ∈ Finset.range m,
          CBc F M (D + 1) (j + 1) (XC F M D) + 1 ≤ 2 * Xbd D (2 * m) + 1 := by
        intro j hj
        have hj1 : j + 1 ≤ 2 * m := by have := Finset.mem_range.mp hj; omega
        have hj2 : 2 * (j + 1) ≤ 2 * m := by
          have := Finset.mem_range.mp hj; omega
        have hX1 : XC F M D (j + 1) ≤ Xbd D (2 * m) :=
          le_trans (ih (j + 1)) (Xbd_mono_m D hj1)
        have hX2 : XC F M D (2 * (j + 1)) ≤ Xbd D (2 * m) :=
          le_trans (ih (2 * (j + 1))) (Xbd_mono_m D hj2)
        have hprod : Real.sqrt (XC F M D (j + 1) * XC F M D (2 * (j + 1)))
            ≤ Xbd D (2 * m) := by
          refine Real.sqrt_le_iff.mpr ⟨le_trans (by norm_num) (Xbd_one_le D (2 * m)), ?_⟩
          rw [sq]
          exact mul_le_mul hX1 hX2 (XC_nonneg _ _) (le_trans (by norm_num) (Xbd_one_le D (2 * m)))
        have hP : PsiC F M (D + 1) ≤ 1 := by
          rw [PsiC]
          refine inv_le_one_of_one_le₀ ?_
          have : (1 : ℝ) ≤ (F (M (D + 1)) : ℝ) := by
            have := hF (M (D + 1)); exact_mod_cast this
          calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
            _ ≤ Real.sqrt (F (M (D + 1)) : ℝ) := Real.sqrt_le_sqrt this
        unfold CBc
        have h2 : 2 * PsiC F M (D + 1) * Real.sqrt (XC F M D (j + 1) * XC F M D (2 * (j + 1)))
            ≤ 2 * Xbd D (2 * m) := by
          have h2' : 2 * PsiC F M (D + 1) * Real.sqrt (XC F M D (j + 1) * XC F M D (2 * (j + 1)))
              ≤ 2 * 1 * Xbd D (2 * m) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hP (by norm_num)) hprod
              (Real.sqrt_nonneg _) (by norm_num)
          linarith
        linarith
      calc ∑ j ∈ Finset.range m, (CBc F M (D + 1) (j + 1) (XC F M D) + 1)
          ≤ ∑ _j ∈ Finset.range m, (2 * Xbd D (2 * m) + 1) := Finset.sum_le_sum hterm
        _ = (m : ℝ) * (2 * Xbd D (2 * m) + 1) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    linarith [ih m, hsum]

/-- The main smallness bound for `ThetaC`. -/
theorem ThetaC_bound {F M : ℕ → ℕ} {d K : ℕ} {a b : ℝ}
    (hF : ∀ n, 1 ≤ F n)
    (hLam1 : ∀ D ≤ d, 1 ≤ LamC F M D)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : ∀ D ≤ d, ∀ j ≤ 2 ^ d * K, PsiC F M D * (LamC F M D) ^ j ≤ a)
    (hb : ∀ j ≤ 2 ^ d * K, Real.sqrt (rhoC F M) * (LupC F M) ^ j ≤ b)
    (hd : 1 ≤ d)
    (hη1 : (d : ℝ) * ((2 ^ d * K : ℕ) : ℝ)
        * (8 * a + 8 * Real.sqrt (Xbd d (2 * (2 ^ d * K))) * b) ≤ 1) :
    ∀ D ≤ d, ∀ m ≤ 2 ^ (d - D) * K,
      ThetaC F M D m ≤ (D : ℝ) * ((2 ^ d * K : ℕ) : ℝ)
        * (8 * a + 8 * Real.sqrt (Xbd d (2 * (2 ^ d * K))) * b) := by
  have hLup1 : 1 ≤ LupC F M := le_trans (by norm_num) (LupC_ge_two hF)
  set Xb : ℝ := Real.sqrt (Xbd d (2 * (2 ^ d * K))) with hXb
  have hXb0 : 0 ≤ Xb := by rw [hXb]; exact Real.sqrt_nonneg _
  set δ : ℝ := 8 * a + 8 * Xb * b with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; nlinarith
  set Kg : ℝ := ((2 ^ d * K : ℕ) : ℝ) with hKg
  have hKg0 : 0 ≤ Kg := by rw [hKg]; exact Nat.cast_nonneg _
  have hmonoD : ∀ D D' : ℕ, D ≤ D' → (D : ℝ) * Kg * δ ≤ (D' : ℝ) * Kg * δ := by
    intro D D' h
    have h1 : (D : ℝ) ≤ (D' : ℝ) := by exact_mod_cast h
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hKg0) hδ0
  clear_value Kg δ Xb
  intro D
  induction D with
  | zero =>
    intro hD m hm
    rw [ThetaC_zero]
    simp
  | succ D ih =>
    intro hD m hm
    have hDd : D ≤ d := by omega
    have hD1d : D + 1 ≤ d := hD
    have hmD : m ≤ 2 ^ (d - D) * K := by
      have h1 : d - (D + 1) ≤ d - D := by omega
      exact le_trans hm (Nat.mul_le_mul_right K (pow_le_pow_right₀ (by norm_num) h1))
    rw [ThetaC_succ]
    have ihD : ThetaC F M D m ≤ (D : ℝ) * Kg * δ := ih hDd m hmD
    have hKB : ∀ j, j ≤ 2 ^ (d - D) * K → j ≤ 2 ^ d * K := by
      intro j hj
      exact le_trans hj (Nat.mul_le_mul_right K (pow_le_pow_right₀ (by norm_num) (by omega)))
    have hterm : ∀ j ∈ Finset.range m,
        etaBC F M (D + 1) (j + 1) (ThetaC F M D) (XC F M D) ≤ δ := by
      intro j hj
      have hjlt : j < m := Finset.mem_range.mp hj
      have hj1m : j + 1 ≤ m := by omega
      have hb1 : j + 1 ≤ 2 ^ (d - D) * K := le_trans hj1m hmD
      have hb2 : 2 * (j + 1) ≤ 2 ^ (d - D) * K := by
        have h2 : 2 * (j + 1) ≤ 2 * m := by omega
        have h4 : 2 * (2 ^ (d - (D + 1)) * K) = 2 ^ (d - D) * K := by
          have he : d - (D + 1) + 1 = d - D := by omega
          rw [← mul_assoc, ← pow_succ', he]
        calc 2 * (j + 1) ≤ 2 * m := h2
          _ ≤ 2 * (2 ^ (d - (D + 1)) * K) := Nat.mul_le_mul_left 2 hm
          _ = 2 ^ (d - D) * K := h4
      have hTh1 : ThetaC F M D (j + 1) ≤ (D : ℝ) * Kg * δ := ih hDd (j + 1) hb1
      have hTh2 : ThetaC F M D (2 * (j + 1)) ≤ (D : ℝ) * Kg * δ :=
        ih hDd (2 * (j + 1)) hb2
      have hTh1' : ThetaC F M D (j + 1) ≤ 1 := le_trans hTh1 (le_trans (hmonoD D d hDd) hη1)
      have hTh2' : ThetaC F M D (2 * (j + 1)) ≤ 1 := le_trans hTh2 (le_trans (hmonoD D d hDd) hη1)
      have hXb1 : XC F M D (j + 1) ≤ Xbd d (2 * (2 ^ d * K)) :=
        le_trans (XC_le_Xbd hF D (j + 1))
          (Xbd_mono (D := D) (D' := d) (m := j + 1) (m' := 2 * (2 ^ d * K)) (by omega)
            (by have := hKB (j + 1) hb1; omega))
      have hXb2 : XC F M D (2 * (j + 1)) ≤ Xbd d (2 * (2 ^ d * K)) :=
        le_trans (XC_le_Xbd hF D (2 * (j + 1)))
          (Xbd_mono (D := D) (D' := d) (m := 2 * (j + 1)) (m' := 2 * (2 ^ d * K)) (by omega)
            (by have := hKB (2 * (j + 1)) hb2; omega))
      have hsq1 : Real.sqrt (1 + ThetaC F M D (j + 1)) ≤ 2 := by
        rw [Real.sqrt_le_iff]
        exact ⟨by norm_num, by nlinarith [hTh1']⟩
      have hsq2 : Real.sqrt (1 + ThetaC F M D (2 * (j + 1))) ≤ 2 := by
        rw [Real.sqrt_le_iff]
        exact ⟨by norm_num, by nlinarith [hTh2']⟩
      have hsX1 : Real.sqrt (XC F M D (j + 1)) ≤ Xb := by rw [hXb]; exact Real.sqrt_le_sqrt hXb1
      have hsX2 : Real.sqrt (XC F M D (2 * (j + 1))) ≤ Xb := by rw [hXb]; exact Real.sqrt_le_sqrt hXb2
      have hPsi1 : PsiC F M (D + 1) ≤ 1 := by
        rw [PsiC]
        refine inv_le_one_of_one_le₀ ?_
        have : (1 : ℝ) ≤ (F (M (D + 1)) : ℝ) := by
          have := hF (M (D + 1)); exact_mod_cast this
        calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
          _ ≤ Real.sqrt (F (M (D + 1)) : ℝ) := Real.sqrt_le_sqrt this
      have hPsi0 : 0 ≤ PsiC F M (D + 1) := PsiC_nonneg (F := F) (M := M) (D + 1)
      have hΨΛ : PsiC F M (D + 1) * (LamC F M (D + 1)) ^ (j + 1) ≤ a :=
        ha (D + 1) hD1d (j + 1) (hKB (j + 1) hb1)
      have hρb : Real.sqrt (rhoC F M) * (LupC F M) ^ (j + 1) ≤ b :=
        hb (j + 1) (hKB (j + 1) hb1)
      have hrho0 : 0 ≤ Real.sqrt (rhoC F M) := Real.sqrt_nonneg _
      have hLupj0 : (0 : ℝ) ≤ (LupC F M) ^ (j + 1) :=
        pow_nonneg (le_trans zero_le_one hLup1) _
      have hXb0' : 0 ≤ Real.sqrt (Xbd d (2 * (2 ^ d * K))) := Real.sqrt_nonneg _
      unfold etaBC
      have hPpos : 0 < PsiC F M (D + 1) := PsiC_pos (F := F) (M := M) hF (D + 1)
      have hA : Real.sqrt (1 + ThetaC F M D (j + 1))
            * Real.sqrt (1 + ThetaC F M D (2 * (j + 1))) * (LamC F M (D + 1)) ^ (j + 1)
          ≤ 4 * (a / PsiC F M (D + 1)) := by
        have h5 : (LamC F M (D + 1)) ^ (j + 1) ≤ a / PsiC F M (D + 1) := by
          rw [le_div_iff₀ hPpos]
          rw [mul_comm]
          exact hΨΛ
        have h6 : Real.sqrt (1 + ThetaC F M D (j + 1))
              * Real.sqrt (1 + ThetaC F M D (2 * (j + 1))) ≤ 4 := by
          have := mul_le_mul hsq1 hsq2 (Real.sqrt_nonneg _) (by norm_num)
          linarith
        have h7 : (0 : ℝ) ≤ a / PsiC F M (D + 1) := div_nonneg ha0 (le_of_lt hPpos)
        exact mul_le_mul h6 h5 (pow_nonneg (le_trans zero_le_one (hLam1 (D + 1) hD1d)) _) (by norm_num)
      have hB : Real.sqrt (rhoC F M)
            * (Real.sqrt (1 + ThetaC F M D (j + 1)) * Real.sqrt (XC F M D (2 * (j + 1)))
              + Real.sqrt (1 + ThetaC F M D (2 * (j + 1))) * Real.sqrt (XC F M D (j + 1)))
            * (LupC F M) ^ (j + 1)
          ≤ Xb * b * 4 := by
        have hinner : Real.sqrt (1 + ThetaC F M D (j + 1)) * Real.sqrt (XC F M D (2 * (j + 1)))
              + Real.sqrt (1 + ThetaC F M D (2 * (j + 1))) * Real.sqrt (XC F M D (j + 1))
            ≤ 4 * Xb := by
          have h1 : Real.sqrt (1 + ThetaC F M D (j + 1)) * Real.sqrt (XC F M D (2 * (j + 1)))
              ≤ 2 * Xb := mul_le_mul hsq1 hsX2 (Real.sqrt_nonneg _) (by norm_num)
          have h2 : Real.sqrt (1 + ThetaC F M D (2 * (j + 1))) * Real.sqrt (XC F M D (j + 1))
              ≤ 2 * Xb := mul_le_mul hsq2 hsX1 (Real.sqrt_nonneg _) (by norm_num)
          linarith
        calc Real.sqrt (rhoC F M)
              * (Real.sqrt (1 + ThetaC F M D (j + 1)) * Real.sqrt (XC F M D (2 * (j + 1)))
                + Real.sqrt (1 + ThetaC F M D (2 * (j + 1))) * Real.sqrt (XC F M D (j + 1)))
              * (LupC F M) ^ (j + 1)
            = (Real.sqrt (rhoC F M) * (LupC F M) ^ (j + 1))
              * (Real.sqrt (1 + ThetaC F M D (j + 1)) * Real.sqrt (XC F M D (2 * (j + 1)))
                + Real.sqrt (1 + ThetaC F M D (2 * (j + 1))) * Real.sqrt (XC F M D (j + 1))) := by
                ring
          _ ≤ b * (4 * Xb) := mul_le_mul hρb hinner (by positivity) hb0
          _ = Xb * b * 4 := by ring
      have htot : 2 * PsiC F M (D + 1)
            * (Real.sqrt (1 + ThetaC F M D (j + 1))
                * Real.sqrt (1 + ThetaC F M D (2 * (j + 1))) * (LamC F M (D + 1)) ^ (j + 1)
              + Real.sqrt (rhoC F M)
                * (Real.sqrt (1 + ThetaC F M D (j + 1)) * Real.sqrt (XC F M D (2 * (j + 1)))
                  + Real.sqrt (1 + ThetaC F M D (2 * (j + 1))) * Real.sqrt (XC F M D (j + 1)))
                * (LupC F M) ^ (j + 1))
          ≤ 8 * a + 8 * Xb * b := by
        have step1 : 2 * PsiC F M (D + 1)
              * (Real.sqrt (1 + ThetaC F M D (j + 1))
                  * Real.sqrt (1 + ThetaC F M D (2 * (j + 1))) * (LamC F M (D + 1)) ^ (j + 1))
            ≤ 8 * a := by
          have hA' : Real.sqrt (1 + ThetaC F M D (j + 1))
                * Real.sqrt (1 + ThetaC F M D (2 * (j + 1))) * (LamC F M (D + 1)) ^ (j + 1)
              ≤ 4 * (a / PsiC F M (D + 1)) := hA
          have hmul : PsiC F M (D + 1)
              * (Real.sqrt (1 + ThetaC F M D (j + 1))
                * Real.sqrt (1 + ThetaC F M D (2 * (j + 1))) * (LamC F M (D + 1)) ^ (j + 1))
              ≤ PsiC F M (D + 1) * (4 * (a / PsiC F M (D + 1))) :=
            mul_le_mul_of_nonneg_left hA' (le_of_lt hPpos)
          have hsimp : PsiC F M (D + 1) * (4 * (a / PsiC F M (D + 1))) = 4 * a := by
            field_simp
          rw [hsimp] at hmul
          linarith
        have step2 : 2 * PsiC F M (D + 1)
              * (Real.sqrt (rhoC F M)
                * (Real.sqrt (1 + ThetaC F M D (j + 1)) * Real.sqrt (XC F M D (2 * (j + 1)))
                  + Real.sqrt (1 + ThetaC F M D (2 * (j + 1))) * Real.sqrt (XC F M D (j + 1)))
                * (LupC F M) ^ (j + 1))
            ≤ 8 * Xb * b := by
          have hP1 : PsiC F M (D + 1) ≤ 1 := hPsi1
          have h2 : PsiC F M (D + 1) * (Real.sqrt (rhoC F M)
                * (Real.sqrt (1 + ThetaC F M D (j + 1)) * Real.sqrt (XC F M D (2 * (j + 1)))
                  + Real.sqrt (1 + ThetaC F M D (2 * (j + 1))) * Real.sqrt (XC F M D (j + 1)))
                * (LupC F M) ^ (j + 1)) ≤ 1 * (Xb * b * 4) :=
            mul_le_mul hP1 hB (by positivity) (by norm_num)
          linarith
        linarith
      rw [hδ]
      exact htot
    have hsum : ∑ j ∈ Finset.range m,
        etaBC F M (D + 1) (j + 1) (ThetaC F M D) (XC F M D) ≤ (m : ℝ) * δ := by
      calc ∑ j ∈ Finset.range m, etaBC F M (D + 1) (j + 1) (ThetaC F M D) (XC F M D)
          ≤ ∑ _j ∈ Finset.range m, δ := Finset.sum_le_sum hterm
        _ = (m : ℝ) * δ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hmKg : (m : ℝ) ≤ Kg := by
      rw [hKg]
      have h1 : m ≤ 2 ^ d * K := le_trans hmD (Nat.mul_le_mul_right K (pow_le_pow_right₀ (by norm_num) (by omega)))
      exact_mod_cast h1
    have hstep : ThetaC F M D m + (m : ℝ) * δ ≤ (D : ℝ) * Kg * δ + Kg * δ := by
      nlinarith [ihD, hmKg, hδ0]
    calc ThetaC F M D m + ∑ j ∈ Finset.range m, etaBC F M (D + 1) (j + 1) (ThetaC F M D) (XC F M D)
        ≤ ThetaC F M D m + (m : ℝ) * δ := by linarith
      _ ≤ (D : ℝ) * Kg * δ + Kg * δ := hstep
      _ = ((D + 1 : ℕ) : ℝ) * Kg * δ := by push_cast; ring

end Szemeredi.Removal