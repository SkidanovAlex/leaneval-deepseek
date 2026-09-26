import Mathlib
import Submission.Work.Asymptotics.CarryDefs
import Submission.Work.Asymptotics.FrobPeel

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

set_option maxHeartbeats 2000000

/-! ## Elementary facts about `Frob`, `frobSq` and the two generators `S`, `T` -/

private lemma Frob_neg' (γ : SL(2,ℤ)) : Frob (-γ) = Frob γ := by
  unfold Frob
  have h : ∀ i j : Fin 2, ((-γ : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = -(γ i j) :=
    fun i j => rfl
  rw [h 0 0, h 0 1, h 1 0, h 1 1]
  congr 1
  simp only [Int.cast_neg]
  ring

private lemma natAbs_sq_cast' (z : ℤ) : ((z.natAbs : ℝ)) ^ 2 = ((z : ℝ)) ^ 2 := by
  rw [Nat.cast_natAbs]
  push_cast
  rw [sq_abs]

private lemma Frob_T_zpow (k : ℤ) : Frob (ModularGroup.T ^ k) = Real.sqrt ((k : ℝ) ^ 2 + 2) := by
  rw [Frob_eq_sqrt_frobSq, coe_frobSq, ModularGroup.coe_T_zpow]
  congr 1
  simp only [sqsum, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  push_cast
  ring

private lemma Frob_ST_zpow (k : ℤ) :
    Frob (ModularGroup.S * ModularGroup.T ^ k) = Real.sqrt ((k : ℝ) ^ 2 + 2) := by
  rw [Frob_eq_sqrt_frobSq, coe_frobSq, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S,
    ModularGroup.coe_T_zpow]
  congr 1
  simp only [sqsum, Fin.sum_univ_two, Matrix.mul_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  push_cast
  ring

private lemma sqrt_add_two_le (k : ℤ) : Real.sqrt ((k : ℝ) ^ 2 + 2) ≤ |(k : ℝ)| + 2 := by
  have h2 : (0:ℝ) ≤ |(k:ℝ)| := abs_nonneg _
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [sq_abs (k:ℝ), h2]

/-- `1 + Frob w` for a block `w` is at most `3 (1 + |k|)`. -/
private lemma one_add_Frob_T_le (k : ℤ) :
    1 + Frob (ModularGroup.T ^ k) ≤ 3 * (1 + |(k : ℝ)|) := by
  rw [Frob_T_zpow]
  have h1 := sqrt_add_two_le k
  have h0 : (0:ℝ) ≤ |(k : ℝ)| := abs_nonneg _
  linarith

private lemma one_add_Frob_ST_le (k : ℤ) :
    1 + Frob (ModularGroup.S * ModularGroup.T ^ k) ≤ 3 * (1 + |(k : ℝ)|) := by
  rw [Frob_ST_zpow]
  have h1 := sqrt_add_two_le k
  have h0 : (0:ℝ) ≤ |(k : ℝ)| := abs_nonneg _
  linarith

private lemma frobSq_one : frobSq (1 : SL(2,ℤ)) = 2 := by decide

private lemma frobSq_S : frobSq (ModularGroup.S) = 2 := by decide

private lemma frobSq_neg_one : frobSq (-1 : SL(2,ℤ)) = 2 := by
  rw [frobSq_neg, frobSq_one]

private lemma frobSq_neg_S : frobSq (-ModularGroup.S) = 2 := by
  rw [frobSq_neg, frobSq_S]

private lemma frobSq_of_isBase {δ : SL(2,ℤ)}
    (h : δ = 1 ∨ δ = -1 ∨ δ = ModularGroup.S ∨ δ = -ModularGroup.S) : frobSq δ = 2 := by
  rcases h with h | h | h | h <;> rw [h]
  · exact frobSq_one
  · exact frobSq_neg_one
  · exact frobSq_S
  · exact frobSq_neg_S

/-- The squared norms of the two rows of `γ`. -/
private def row1sq (γ : SL(2,ℤ)) : ℕ := (γ 0 0).natAbs ^ 2 + (γ 0 1).natAbs ^ 2
private def row2sq (γ : SL(2,ℤ)) : ℕ := (γ 1 0).natAbs ^ 2 + (γ 1 1).natAbs ^ 2

private lemma frobSq_eq_rows (γ : SL(2,ℤ)) : frobSq γ = row1sq γ + row2sq γ := by
  simp only [frobSq, row1sq, row2sq]
  ring

private lemma row1sq_cast (γ : SL(2,ℤ)) :
    ((row1sq γ : ℕ) : ℝ) = ((γ 0 0 : ℤ) : ℝ) ^ 2 + ((γ 0 1 : ℤ) : ℝ) ^ 2 := by
  simp only [row1sq, Nat.cast_add, Nat.cast_pow]
  rw [natAbs_sq_cast', natAbs_sq_cast']

private lemma row2sq_cast (γ : SL(2,ℤ)) :
    ((row2sq γ : ℕ) : ℝ) = ((γ 1 0 : ℤ) : ℝ) ^ 2 + ((γ 1 1 : ℤ) : ℝ) ^ 2 := by
  simp only [row2sq, Nat.cast_add, Nat.cast_pow]
  rw [natAbs_sq_cast', natAbs_sq_cast']

private lemma one_le_row1sq (γ : SL(2,ℤ)) : 1 ≤ row1sq γ := by
  by_contra h
  push_neg at h
  have h0 : row1sq γ = 0 := by omega
  simp only [row1sq, Nat.add_eq_zero_iff, pow_eq_zero_iff (n := 2) (by norm_num),
    Int.natAbs_eq_zero] at h0
  obtain ⟨h1, h2⟩ := h0
  have hd := γ.2
  rw [Matrix.det_fin_two, h1, h2] at hd
  norm_num at hd

private lemma one_le_row2sq (γ : SL(2,ℤ)) : 1 ≤ row2sq γ := by
  by_contra h
  push_neg at h
  have h0 : row2sq γ = 0 := by omega
  simp only [row2sq, Nat.add_eq_zero_iff, pow_eq_zero_iff (n := 2) (by norm_num),
    Int.natAbs_eq_zero] at h0
  obtain ⟨h1, h2⟩ := h0
  have hd := γ.2
  rw [Matrix.det_fin_two, h1, h2] at hd
  norm_num at hd

/-- The nearest integer to `x`. -/
private def roundHalf (x : ℝ) : ℤ := ⌊x + 1/2⌋

private lemma abs_roundHalf_sub (x : ℝ) : |(roundHalf x : ℝ) - x| ≤ 1/2 := by
  have h1 : (roundHalf x : ℝ) ≤ x + 1/2 := Int.floor_le _
  have h2 : x + 1/2 < (roundHalf x : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  constructor <;> linarith

/-! ## The Euclidean step -/

private lemma step_T (γ : SL(2,ℤ)) (hle : row2sq γ ≤ row1sq γ) (h2 : 2 < frobSq γ) :
    ∃ k : ℤ, 4 * frobSq ((ModularGroup.T ^ k)⁻¹ * γ) ≤ 3 * frobSq γ ∧
      (1 + Frob (ModularGroup.T ^ k)) * Real.sqrt (frobSq ((ModularGroup.T ^ k)⁻¹ * γ))
        ≤ 9 * Real.sqrt (frobSq γ) := by
  have hF3 : (3:ℝ) ≤ ((frobSq γ : ℕ) : ℝ) := by
    have : (3:ℕ) ≤ frobSq γ := by omega
    exact_mod_cast this
  set e1 : ℝ := ((γ 0 0 : ℤ) : ℝ) with he1
  set e2 : ℝ := ((γ 0 1 : ℤ) : ℝ) with he2
  set e3 : ℝ := ((γ 1 0 : ℤ) : ℝ) with he3
  set e4 : ℝ := ((γ 1 1 : ℤ) : ℝ) with he4
  have hdet : e1 * e4 - e2 * e3 = 1 := by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    rw [he1, he2, he3, he4]
    exact_mod_cast h
  set n1 : ℝ := e1^2 + e2^2 with hn1
  set n2 : ℝ := e3^2 + e4^2 with hn2
  set pp : ℝ := e1*e3 + e2*e4 with hpp
  have hn2pos : 0 < n2 := by
    rw [hn2]
    by_contra hcon
    push_neg at hcon
    have h3 : e3 = 0 := by nlinarith [sq_nonneg e3, sq_nonneg e4]
    have h4 : e4 = 0 := by nlinarith [sq_nonneg e3, sq_nonneg e4]
    rw [h3, h4] at hdet
    norm_num at hdet
  have hlag : pp^2 + 1 = n1 * n2 := by
    have h1 : (1:ℝ) = (e1*e4 - e2*e3)^2 := by rw [hdet]; norm_num
    rw [h1, hpp, hn1, hn2]
    ring
  have hn1cast : ((row1sq γ : ℕ) : ℝ) = n1 := by rw [row1sq_cast, ← he1, ← he2, hn1]
  have hn2cast : ((row2sq γ : ℕ) : ℝ) = n2 := by rw [row2sq_cast, ← he3, ← he4, hn2]
  have hF : ((frobSq γ : ℕ) : ℝ) = n1 + n2 := by
    rw [frobSq_eq_rows]; push_cast; rw [hn1cast, hn2cast]
  have hle' : n2 ≤ n1 := by
    rw [← hn1cast, ← hn2cast]; exact_mod_cast hle
  have hm : (2:ℝ) ≤ n2 ∨ n2 = 1 := by
    by_cases hh : 2 ≤ row2sq γ
    · left; rw [← hn2cast]; exact_mod_cast hh
    · right
      have : row2sq γ = 1 := by have := one_le_row2sq γ; omega
      rw [← hn2cast, this]; norm_num
  set k : ℤ := roundHalf (pp / n2) with hkdef
  have hmat : ((((ModularGroup.T ^ k)⁻¹ * γ : SL(2,ℤ))) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![γ 0 0 - k * γ 1 0, γ 0 1 - k * γ 1 1; γ 1 0, γ 1 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ← _root_.zpow_neg, ModularGroup.coe_T_zpow]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hF' : ((frobSq ((ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ)
      = (e1 - (k:ℝ)*e3)^2 + (e2 - (k:ℝ)*e4)^2 + e3^2 + e4^2 := by
    rw [coe_frobSq, hmat]
    simp only [sqsum, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
    simp only [Int.cast_sub, Int.cast_mul]
    rw [← he1, ← he2, ← he3, ← he4]
    ring
  have hF'eq : ((frobSq ((ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ)
      = (e1 - (k:ℝ)*e3)^2 + (e2 - (k:ℝ)*e4)^2 + n2 := by
    rw [hF', hn2]; ring
  have hquad : (e1 - (k:ℝ)*e3)^2 + (e2 - (k:ℝ)*e4)^2 ≤ 1/n2 + n2/4 := by
    have hkey1 : (e1 - (k:ℝ)*e3)^2 + (e2 - (k:ℝ)*e4)^2
        = n1 - 2*(k:ℝ)*pp + (k:ℝ)^2 * n2 := by rw [hn1, hpp]; ring
    have hkey2 : n1 - 2*(k:ℝ)*pp + (k:ℝ)^2 * n2
        = 1/n2 + n2 * ((k:ℝ) - pp/n2)^2 := by
      have hn1eq : n1 = (pp^2 + 1)/n2 := by
        rw [eq_div_iff (ne_of_gt hn2pos)]; linarith [hlag]
      rw [hn1eq]; field_simp; ring
    rw [hkey1, hkey2]
    have h1 : ((k:ℝ) - pp/n2)^2 ≤ 1/4 := by
      have h3 : |(k:ℝ) - pp/n2| ≤ 1/2 := by rw [hkdef]; exact abs_roundHalf_sub _
      have h5 : ((k:ℝ) - pp/n2)^2 = |(k:ℝ) - pp/n2|^2 := (sq_abs _).symm
      rw [h5]
      calc |(k:ℝ) - pp/n2|^2 ≤ (1/2:ℝ)^2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
        _ = 1/4 := by norm_num
    have h6 := mul_le_mul_of_nonneg_left h1 hn2pos.le
    linarith [h6]
  have hkey : 4 / n2 + 2 * n2 ≤ 3 * n1 := by
    rcases hm with hge | heq
    · have h4 : 4 / n2 ≤ n2 := by rw [div_le_iff₀ hn2pos]; nlinarith
      linarith
    · rw [heq]
      have h3 : (2:ℝ) ≤ n1 := by have := hF; rw [heq] at this; linarith
      linarith
  have hk_abs : |(k:ℝ)| ≤ Real.sqrt (n1/n2) + 1/2 := by
    have hPle : |pp| ≤ Real.sqrt (n1*n2) := by
      rw [← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_le_sqrt
      nlinarith [hlag]
    have hsplit : |(k:ℝ)| ≤ |(k:ℝ) - pp/n2| + |pp/n2| := by
      have h := abs_add_le ((k:ℝ) - pp/n2) (pp/n2)
      have heq2 : ((k:ℝ) - pp/n2) + pp/n2 = (k:ℝ) := by ring
      rwa [heq2] at h
    have h2' : |pp/n2| ≤ Real.sqrt (n1/n2) := by
      rw [abs_div, abs_of_pos hn2pos, div_le_iff₀ hn2pos]
      have h3 : Real.sqrt (n1*n2) = Real.sqrt (n1/n2) * n2 := by
        rw [show n1*n2 = (n1/n2) * n2^2 by field_simp]
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hn2pos.le]
      linarith [hPle, h3]
    have h4 : |(k:ℝ) - pp/n2| ≤ 1/2 := by rw [hkdef]; exact abs_roundHalf_sub _
    linarith
  refine ⟨k, ?_, ?_⟩
  · -- the geometric decrease
    have hq4 := mul_le_mul_of_nonneg_left hquad (by norm_num : (0:ℝ) ≤ 4)
    have hq5 : 4 * (1/n2 + n2/4) = 4/n2 + n2 := by ring
    have hreal : 4 * ((frobSq ((ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ)
        ≤ 3 * ((frobSq γ : ℕ) : ℝ) := by
      rw [hF'eq, hF]
      nlinarith [hq4, hq5, hkey]
    have hcast : ((4 * frobSq ((ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ)
        ≤ ((3 * frobSq γ : ℕ) : ℝ) := by
      push_cast
      exact hreal
    exact_mod_cast hcast
  · -- the multiplicative bound
    have hb2 : (1:ℝ) + |(k:ℝ)| ≤ 3/2 + Real.sqrt ((n1+n2)/n2) := by
      have h3 : Real.sqrt (n1/n2) ≤ Real.sqrt ((n1+n2)/n2) := Real.sqrt_le_sqrt (by
        rw [div_le_div_iff_of_pos_right hn2pos]; linarith)
      linarith [hk_abs, h3]
    have hsq : Real.sqrt (2*n2) * Real.sqrt ((n1+n2)/n2) = Real.sqrt (2*(n1+n2)) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    have hmain : Real.sqrt (((frobSq ((ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ)) * (1 + |(k:ℝ)|)
        ≤ 3 * Real.sqrt (n1 + n2) := by
      rcases hm with hge | heq
      · have hbase : Real.sqrt (((frobSq ((ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ))
            ≤ Real.sqrt (2 * n2) := by
          apply Real.sqrt_le_sqrt
          rw [hF'eq]
          have h5 : 1/n2 ≤ n2/4 := by
            rw [div_le_iff₀ hn2pos]
            rw [show (n2/4) * n2 = n2 * n2 / 4 by ring]
            rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
            nlinarith
          linarith [hquad]
        calc Real.sqrt (((frobSq ((ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ)) * (1 + |(k:ℝ)|)
            ≤ Real.sqrt (2*n2) * (3/2 + Real.sqrt ((n1+n2)/n2)) :=
              mul_le_mul hbase hb2 (by positivity) (by positivity)
          _ = (3/2) * Real.sqrt (2*n2) + Real.sqrt (2*n2) * Real.sqrt ((n1+n2)/n2) := by ring
          _ = (3/2) * Real.sqrt (2*n2) + Real.sqrt (2*(n1+n2)) := by rw [hsq]
          _ ≤ (3/2) * Real.sqrt (n1+n2) + Real.sqrt 2 * Real.sqrt (n1+n2) := by
              have ha : (3/2) * Real.sqrt (2*n2) ≤ (3/2) * Real.sqrt (n1+n2) :=
                mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by norm_num)
              have hb : Real.sqrt (2*(n1+n2)) = Real.sqrt 2 * Real.sqrt (n1+n2) := by
                rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
              linarith [ha, hb.le]
          _ = (3/2 + Real.sqrt 2) * Real.sqrt (n1+n2) := by ring
          _ ≤ 3 * Real.sqrt (n1+n2) := by
              apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
              have h3 : Real.sqrt 2 ≤ 3/2 := by
                nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
              linarith
      · have hquad' := hquad
        rw [heq] at hquad'
        have hbase : Real.sqrt (((frobSq ((ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ)) ≤ 3/2 := by
          rw [Real.sqrt_le_iff]
          refine ⟨by norm_num, ?_⟩
          rw [hF'eq]
          rw [heq]
          linarith [hquad']
        have hb2' : (1:ℝ) + |(k:ℝ)| ≤ 3/2 + Real.sqrt (n1+n2) := by
          have h3 : Real.sqrt (n1/n2) ≤ Real.sqrt (n1+n2) := by
            rw [heq, div_one]
            exact Real.sqrt_le_sqrt (by linarith)
          linarith [hk_abs, h3]
        have h4 : (3/2:ℝ) ≤ Real.sqrt (n1+n2) := by
          rw [Real.le_sqrt (by norm_num) (by positivity)]
          have := hF; rw [heq] at this; linarith
        calc Real.sqrt (((frobSq ((ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ)) * (1 + |(k:ℝ)|)
            ≤ (3/2) * (3/2 + Real.sqrt (n1+n2)) :=
              mul_le_mul hbase hb2' (by positivity) (by norm_num)
          _ = 9/4 + (3/2) * Real.sqrt (n1+n2) := by ring
          _ ≤ 3 * Real.sqrt (n1+n2) := by linarith
    have hstep : (1 + Frob (ModularGroup.T ^ k)) ≤ 3 * (1 + |(k:ℝ)|) := one_add_Frob_T_le k
    have hspos : (0:ℝ) ≤ Real.sqrt (((frobSq ((ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ)) :=
      Real.sqrt_nonneg _
    have h1 : (1 + Frob (ModularGroup.T ^ k))
          * Real.sqrt (((frobSq ((ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ))
        ≤ 9 * Real.sqrt (n1 + n2) := by
      calc (1 + Frob (ModularGroup.T ^ k))
            * Real.sqrt (((frobSq ((ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ))
          ≤ (3 * (1 + |(k:ℝ)|))
            * Real.sqrt (((frobSq ((ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right hstep hspos
        _ = 3 * (Real.sqrt (((frobSq ((ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ)) * (1 + |(k:ℝ)|)) := by
            ring
        _ ≤ 3 * (3 * Real.sqrt (n1 + n2)) :=
            mul_le_mul_of_nonneg_left hmain (by norm_num)
        _ = 9 * Real.sqrt (n1 + n2) := by ring
    rw [hF]
    exact h1

private lemma step_ST (γ : SL(2,ℤ)) (hle : row1sq γ ≤ row2sq γ) (h2 : 2 < frobSq γ) :
    ∃ k : ℤ, 4 * frobSq ((ModularGroup.S * ModularGroup.T ^ k)⁻¹ * γ) ≤ 3 * frobSq γ ∧
      (1 + Frob (ModularGroup.S * ModularGroup.T ^ k))
          * Real.sqrt (frobSq ((ModularGroup.S * ModularGroup.T ^ k)⁻¹ * γ))
        ≤ 9 * Real.sqrt (frobSq γ) := by
  have hF3 : (3:ℝ) ≤ ((frobSq γ : ℕ) : ℝ) := by
    have : (3:ℕ) ≤ frobSq γ := by omega
    exact_mod_cast this
  set e1 : ℝ := ((γ 0 0 : ℤ) : ℝ) with he1
  set e2 : ℝ := ((γ 0 1 : ℤ) : ℝ) with he2
  set e3 : ℝ := ((γ 1 0 : ℤ) : ℝ) with he3
  set e4 : ℝ := ((γ 1 1 : ℤ) : ℝ) with he4
  have hdet : e1 * e4 - e2 * e3 = 1 := by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    rw [he1, he2, he3, he4]
    exact_mod_cast h
  set n1 : ℝ := e1^2 + e2^2 with hn1
  set n2 : ℝ := e3^2 + e4^2 with hn2
  set pp : ℝ := e1*e3 + e2*e4 with hpp
  have hn1pos : 0 < n1 := by
    rw [hn1]
    by_contra hcon
    push_neg at hcon
    have h3 : e1 = 0 := by nlinarith [sq_nonneg e1, sq_nonneg e2]
    have h4 : e2 = 0 := by nlinarith [sq_nonneg e1, sq_nonneg e2]
    rw [h3, h4] at hdet
    norm_num at hdet
  have hlag : pp^2 + 1 = n1 * n2 := by
    have h1 : (1:ℝ) = (e1*e4 - e2*e3)^2 := by rw [hdet]; norm_num
    rw [h1, hpp, hn1, hn2]
    ring
  have hn1cast : ((row1sq γ : ℕ) : ℝ) = n1 := by rw [row1sq_cast, ← he1, ← he2, hn1]
  have hn2cast : ((row2sq γ : ℕ) : ℝ) = n2 := by rw [row2sq_cast, ← he3, ← he4, hn2]
  have hF : ((frobSq γ : ℕ) : ℝ) = n1 + n2 := by
    rw [frobSq_eq_rows]; push_cast; rw [hn1cast, hn2cast]
  have hle' : n1 ≤ n2 := by
    rw [← hn1cast, ← hn2cast]; exact_mod_cast hle
  have hm : (2:ℝ) ≤ n1 ∨ n1 = 1 := by
    by_cases hh : 2 ≤ row1sq γ
    · left; rw [← hn1cast]; exact_mod_cast hh
    · right
      have : row1sq γ = 1 := by have := one_le_row1sq γ; omega
      rw [← hn1cast, this]; norm_num
  set k : ℤ := roundHalf (-(pp / n1)) with hkdef
  have hmat : ((((ModularGroup.S * ModularGroup.T ^ k)⁻¹ * γ : SL(2,ℤ))) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![k * γ 0 0 + γ 1 0, k * γ 0 1 + γ 1 1; -γ 0 0, -γ 0 1] := by
    have hST : ((ModularGroup.S * ModularGroup.T ^ k : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = !![0, -1; 1, k] := by
      rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T_zpow]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, hST,
      Matrix.adjugate_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hF' : ((frobSq ((ModularGroup.S * ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ)
      = ((k:ℝ)*e1 + e3) ^ 2 + ((k:ℝ)*e2 + e4)^2 + e1^2 + e2^2 := by
    rw [coe_frobSq, hmat]
    simp only [sqsum, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
    push_cast
    rw [← he1, ← he2, ← he3, ← he4]
    ring
  have hF'eq : ((frobSq ((ModularGroup.S * ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ)
      = ((k:ℝ)*e1 + e3)^2 + ((k:ℝ)*e2 + e4)^2 + n1 := by
    rw [hF', hn1]; ring
  have hquad : ((k:ℝ)*e1 + e3)^2 + ((k:ℝ)*e2 + e4)^2 ≤ 1/n1 + n1/4 := by
    have hkey1 : ((k:ℝ)*e1 + e3)^2 + ((k:ℝ)*e2 + e4)^2
        = n2 + 2*(k:ℝ)*pp + (k:ℝ)^2 * n1 := by rw [hn2, hpp]; ring
    have hkey2 : n2 + 2*(k:ℝ)*pp + (k:ℝ)^2 * n1
        = 1/n1 + n1 * ((k:ℝ) + pp/n1)^2 := by
      have hn2eq : n2 = (pp^2 + 1)/n1 := by
        rw [eq_div_iff (ne_of_gt hn1pos)]; linarith [hlag]
      rw [hn2eq]; field_simp; ring
    rw [hkey1, hkey2]
    have h1 : ((k:ℝ) + pp/n1)^2 ≤ 1/4 := by
      have h3 : |(k:ℝ) + pp/n1| ≤ 1/2 := by
        rw [hkdef]; simpa using abs_roundHalf_sub (-(pp/n1))
      have h5 : ((k:ℝ) + pp/n1)^2 = |(k:ℝ) + pp/n1|^2 := (sq_abs _).symm
      rw [h5]
      calc |(k:ℝ) + pp/n1|^2 ≤ (1/2:ℝ)^2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
        _ = 1/4 := by norm_num
    have h6 := mul_le_mul_of_nonneg_left h1 hn1pos.le
    linarith [h6]
  have hkey : 4 / n1 + 2 * n1 ≤ 3 * n2 := by
    rcases hm with hge | heq
    · have h4 : 4 / n1 ≤ n1 := by rw [div_le_iff₀ hn1pos]; nlinarith
      linarith
    · rw [heq]
      have h3 : (2:ℝ) ≤ n2 := by have := hF; rw [heq] at this; linarith
      linarith
  have hk_abs : |(k:ℝ)| ≤ Real.sqrt (n2/n1) + 1/2 := by
    have hPle : |pp| ≤ Real.sqrt (n1*n2) := by
      rw [← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_le_sqrt
      nlinarith [hlag]
    have hsplit : |(k:ℝ)| ≤ |(k:ℝ) + pp/n1| + |pp/n1| := by
      have h := abs_add_le ((k:ℝ) + pp/n1) (-(pp/n1))
      have heq2 : ((k:ℝ) + pp/n1) + (-(pp/n1)) = (k:ℝ) := by ring
      have h2 : |-(pp/n1)| = |pp/n1| := abs_neg _
      rwa [heq2, h2] at h
    have h2' : |pp/n1| ≤ Real.sqrt (n2/n1) := by
      rw [abs_div, abs_of_pos hn1pos, div_le_iff₀ hn1pos]
      have h3 : Real.sqrt (n1*n2) = Real.sqrt (n2/n1) * n1 := by
        rw [show n1*n2 = (n2/n1) * n1^2 by field_simp]
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hn1pos.le]
      linarith [hPle, h3]
    have h4 : |(k:ℝ) + pp/n1| ≤ 1/2 := by
      rw [hkdef]; simpa using abs_roundHalf_sub (-(pp/n1))
    linarith
  refine ⟨k, ?_, ?_⟩
  · have hq4 := mul_le_mul_of_nonneg_left hquad (by norm_num : (0:ℝ) ≤ 4)
    have hq5 : 4 * (1/n1 + n1/4) = 4/n1 + n1 := by ring
    have hreal : 4 * ((frobSq ((ModularGroup.S * ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ)
        ≤ 3 * ((frobSq γ : ℕ) : ℝ) := by
      rw [hF'eq, hF]
      nlinarith [hq4, hq5, hkey]
    have hcast : ((4 * frobSq ((ModularGroup.S * ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ)
        ≤ ((3 * frobSq γ : ℕ) : ℝ) := by
      push_cast
      exact hreal
    exact_mod_cast hcast
  · have hb2 : (1:ℝ) + |(k:ℝ)| ≤ 3/2 + Real.sqrt ((n1+n2)/n1) := by
      have h3 : Real.sqrt (n2/n1) ≤ Real.sqrt ((n1+n2)/n1) := Real.sqrt_le_sqrt (by
        rw [div_le_div_iff_of_pos_right hn1pos]; linarith)
      linarith [hk_abs, h3]
    have hsq : Real.sqrt (2*n1) * Real.sqrt ((n1+n2)/n1) = Real.sqrt (2*(n1+n2)) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    have hmain : Real.sqrt (((frobSq ((ModularGroup.S * ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ))
          * (1 + |(k:ℝ)|)
        ≤ 3 * Real.sqrt (n1 + n2) := by
      rcases hm with hge | heq
      · have hbase : Real.sqrt (((frobSq ((ModularGroup.S * ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ))
            ≤ Real.sqrt (2 * n1) := by
          apply Real.sqrt_le_sqrt
          rw [hF'eq]
          have h5 : 1/n1 ≤ n1/4 := by
            rw [div_le_iff₀ hn1pos]
            rw [show (n1/4) * n1 = n1 * n1 / 4 by ring]
            rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
            nlinarith
          linarith [hquad]
        calc Real.sqrt (((frobSq ((ModularGroup.S * ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ))
              * (1 + |(k:ℝ)|)
            ≤ Real.sqrt (2*n1) * (3/2 + Real.sqrt ((n1+n2)/n1)) :=
              mul_le_mul hbase hb2 (by positivity) (by positivity)
          _ = (3/2) * Real.sqrt (2*n1) + Real.sqrt (2*n1) * Real.sqrt ((n1+n2)/n1) := by ring
          _ = (3/2) * Real.sqrt (2*n1) + Real.sqrt (2*(n1+n2)) := by rw [hsq]
          _ ≤ (3/2) * Real.sqrt (n1+n2) + Real.sqrt 2 * Real.sqrt (n1+n2) := by
              have ha : (3/2) * Real.sqrt (2*n1) ≤ (3/2) * Real.sqrt (n1+n2) :=
                mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by norm_num)
              have hb : Real.sqrt (2*(n1+n2)) = Real.sqrt 2 * Real.sqrt (n1+n2) := by
                rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
              linarith [ha, hb.le]
          _ = (3/2 + Real.sqrt 2) * Real.sqrt (n1+n2) := by ring
          _ ≤ 3 * Real.sqrt (n1+n2) := by
              apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
              have h3 : Real.sqrt 2 ≤ 3/2 := by
                nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
              linarith
      · have hquad' := hquad
        rw [heq] at hquad'
        have hbase : Real.sqrt (((frobSq ((ModularGroup.S * ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ))
            ≤ 3/2 := by
          rw [Real.sqrt_le_iff]
          refine ⟨by norm_num, ?_⟩
          rw [hF'eq]
          rw [heq]
          linarith [hquad']
        have hb2' : (1:ℝ) + |(k:ℝ)| ≤ 3/2 + Real.sqrt (n1+n2) := by
          have h3 : Real.sqrt (n2/n1) ≤ Real.sqrt (n1+n2) := by
            rw [heq, div_one]
            exact Real.sqrt_le_sqrt (by linarith)
          linarith [hk_abs, h3]
        have h4 : (3/2:ℝ) ≤ Real.sqrt (n1+n2) := by
          rw [Real.le_sqrt (by norm_num) (by positivity)]
          have := hF; rw [heq] at this; linarith
        calc Real.sqrt (((frobSq ((ModularGroup.S * ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ))
              * (1 + |(k:ℝ)|)
            ≤ (3/2) * (3/2 + Real.sqrt (n1+n2)) :=
              mul_le_mul hbase hb2' (by positivity) (by norm_num)
          _ = 9/4 + (3/2) * Real.sqrt (n1+n2) := by ring
          _ ≤ 3 * Real.sqrt (n1+n2) := by linarith
    have hstep : (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ≤ 3 * (1 + |(k:ℝ)|) :=
      one_add_Frob_ST_le k
    have hspos : (0:ℝ) ≤ Real.sqrt (((frobSq ((ModularGroup.S * ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ)) :=
      Real.sqrt_nonneg _
    have h1 : (1 + Frob (ModularGroup.S * ModularGroup.T ^ k))
          * Real.sqrt (((frobSq ((ModularGroup.S * ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ))
        ≤ 9 * Real.sqrt (n1 + n2) := by
      calc (1 + Frob (ModularGroup.S * ModularGroup.T ^ k))
            * Real.sqrt (((frobSq ((ModularGroup.S * ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ))
          ≤ (3 * (1 + |(k:ℝ)|))
            * Real.sqrt (((frobSq ((ModularGroup.S * ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right hstep hspos
        _ = 3 * (Real.sqrt (((frobSq ((ModularGroup.S * ModularGroup.T ^ k)⁻¹ * γ) : ℕ) : ℝ))
              * (1 + |(k:ℝ)|)) := by ring
        _ ≤ 3 * (3 * Real.sqrt (n1 + n2)) := mul_le_mul_of_nonneg_left hmain (by norm_num)
        _ = 9 * Real.sqrt (n1 + n2) := by ring
    rw [hF]
    exact h1


private lemma frobSq_cast_pos (γ : SL(2,ℤ)) : (0:ℝ) < ((frobSq γ : ℕ) : ℝ) := by
  exact_mod_cast frobSq_pos γ

private lemma step (γ : SL(2,ℤ)) (h2 : 2 < frobSq γ) :
    ∃ w : SL(2,ℤ), (∃ k : ℤ, w = ModularGroup.T ^ k ∨ w = ModularGroup.S * ModularGroup.T ^ k) ∧
      4 * frobSq (w⁻¹ * γ) ≤ 3 * frobSq γ ∧
      (1 + Frob w) * Real.sqrt (frobSq (w⁻¹ * γ)) ≤ 9 * Real.sqrt (frobSq γ) := by
  rcases le_total (row2sq γ) (row1sq γ) with h | h
  · obtain ⟨k, h1, h2'⟩ := step_T γ h h2
    exact ⟨ModularGroup.T ^ k, ⟨k, Or.inl rfl⟩, h1, h2'⟩
  · obtain ⟨k, h1, h2'⟩ := step_ST γ h h2
    exact ⟨ModularGroup.S * ModularGroup.T ^ k, ⟨k, Or.inr rfl⟩, h1, h2'⟩

/-! ## The induction -/

private theorem main_induction : ∀ f : ℕ, ∀ γ : SL(2,ℤ), frobSq γ ≤ f →
    ∃ (L : List SL(2,ℤ)) (δ : SL(2,ℤ)),
      (∀ x ∈ L, ∃ k : ℤ, x = ModularGroup.T ^ k ∨ x = ModularGroup.S * ModularGroup.T ^ k) ∧
      (δ = 1 ∨ δ = -1 ∨ δ = ModularGroup.S ∨ δ = -ModularGroup.S) ∧
      L.prod * δ = γ ∧
      (L.length : ℝ) * Real.log (4/3) ≤ Real.log (((frobSq γ : ℕ) : ℝ)) ∧
      (L.map (fun x => 1 + Frob x)).prod
        ≤ 9 ^ L.length * Real.sqrt ((((frobSq γ : ℕ) : ℝ)) / (((frobSq δ : ℕ) : ℝ))) := by
  intro f
  induction f with
  | zero =>
    intro γ hγ
    exact absurd hγ (not_le.mpr (frobSq_pos γ))
  | succ f ih =>
    intro γ hγ
    by_cases h2 : frobSq γ ≤ 2
    · refine ⟨[], γ, by simp, (frobSq_peel γ).2 h2, by simp, ?_, ?_⟩
      · simp only [List.length_nil, Nat.cast_zero, zero_mul]
        exact Real.log_nonneg (by
          have h := frobSq_pos γ
          exact_mod_cast (show (1:ℕ) ≤ frobSq γ by omega))
      · simp only [List.map_nil, List.prod_nil, List.length_nil, pow_zero, one_mul, Nat.cast_zero,
          zero_mul, div_self (ne_of_gt (frobSq_cast_pos γ)), Real.sqrt_one, le_refl]
    · push_neg at h2
      obtain ⟨w, hw, hdec, hmult⟩ := step γ h2
      have hlt : frobSq (w⁻¹ * γ) < frobSq γ := by
        have hp := frobSq_pos (w⁻¹ * γ)
        omega
      have hle : frobSq (w⁻¹ * γ) ≤ f := by omega
      obtain ⟨L, δ, hbl, hδ, hprod, hn, hpr⟩ := ih (w⁻¹ * γ) hle
      have hF'pos := frobSq_cast_pos (w⁻¹ * γ)
      have hFpos := frobSq_cast_pos γ
      have hδpos := frobSq_cast_pos δ
      refine ⟨w :: L, δ, ?_, hδ, ?_, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hw
        · exact hbl x hx
      · rw [List.prod_cons, mul_assoc, hprod]
        group
      · -- the length bound
        rw [List.length_cons]
        push_cast
        have hratio : (4/3:ℝ) ≤ (((frobSq γ : ℕ) : ℝ)) / (((frobSq (w⁻¹ * γ) : ℕ) : ℝ)) := by
          rw [le_div_iff₀ hF'pos]
          have hh : (4:ℝ) * (((frobSq (w⁻¹ * γ) : ℕ) : ℝ)) ≤ 3 * (((frobSq γ : ℕ) : ℝ)) := by
            exact_mod_cast hdec
          linarith
        have hlog : Real.log (4/3)
            ≤ Real.log ((((frobSq γ : ℕ) : ℝ)) / (((frobSq (w⁻¹ * γ) : ℕ) : ℝ))) :=
          Real.log_le_log (by norm_num) hratio
        have hsplit : Real.log (((frobSq γ : ℕ) : ℝ))
            = Real.log (((frobSq (w⁻¹ * γ) : ℕ) : ℝ))
              + Real.log ((((frobSq γ : ℕ) : ℝ)) / (((frobSq (w⁻¹ * γ) : ℕ) : ℝ))) := by
          rw [← Real.log_mul (ne_of_gt hF'pos) (by positivity)]
          congr 1
          field_simp
        linarith
      · -- the product bound
        rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
        rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ (((frobSq γ : ℕ) : ℝ)))]
        have hpr' : (L.map fun x => 1 + Frob x).prod
            ≤ 9 ^ L.length * (Real.sqrt (((frobSq (w⁻¹ * γ) : ℕ) : ℝ))
                / Real.sqrt (((frobSq δ : ℕ) : ℝ))) := by
          rw [← Real.sqrt_div (by positivity : (0:ℝ) ≤ (((frobSq (w⁻¹ * γ) : ℕ) : ℝ)))]
          exact hpr
        have hmul' : (1 + Frob w) * (Real.sqrt (((frobSq (w⁻¹ * γ) : ℕ) : ℝ))
              / Real.sqrt (((frobSq δ : ℕ) : ℝ)))
            ≤ 9 * (Real.sqrt (((frobSq γ : ℕ) : ℝ)) / Real.sqrt (((frobSq δ : ℕ) : ℝ))) := by
          rw [← mul_div_assoc, ← mul_div_assoc]
          exact div_le_div_of_nonneg_right hmult (Real.sqrt_nonneg _)
        calc (1 + Frob w) * (L.map fun x => 1 + Frob x).prod
            ≤ (1 + Frob w) * (9 ^ L.length * (Real.sqrt (((frobSq (w⁻¹ * γ) : ℕ) : ℝ))
                / Real.sqrt (((frobSq δ : ℕ) : ℝ)))) :=
              mul_le_mul_of_nonneg_left hpr' (by have := Frob_nonneg w; linarith)
          _ = 9 ^ L.length * ((1 + Frob w) * (Real.sqrt (((frobSq (w⁻¹ * γ) : ℕ) : ℝ))
                / Real.sqrt (((frobSq δ : ℕ) : ℝ)))) := by ring
          _ ≤ 9 ^ L.length * (9 * (Real.sqrt (((frobSq γ : ℕ) : ℝ))
                / Real.sqrt (((frobSq δ : ℕ) : ℝ)))) :=
              mul_le_mul_of_nonneg_left hmul' (by positivity)
          _ = 9 ^ (L.length + 1) * (Real.sqrt (((frobSq γ : ℕ) : ℝ))
                / Real.sqrt (((frobSq δ : ℕ) : ℝ))) := by rw [pow_succ]; ring

/-! ## Conversions of the logarithmic bound -/

private lemma log_four_thirds : (1/4:ℝ) ≤ Real.log (4/3) := by
  have h1 : Real.log (3/4) ≤ (3/4:ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h2 : Real.log (3/4) = -Real.log (4/3) := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num)]
    ring
  linarith

private lemma nine_pow_le (n : ℕ) (m : ℝ) (hm : 1 ≤ m)
    (h : (n:ℝ) * Real.log (4/3) ≤ Real.log m) : (9:ℝ)^n ≤ m^16 := by
  have h43pos : 0 < Real.log (4/3) := Real.log_pos (by norm_num)
  have hmpos : 0 < m := by linarith
  have hLnn : 0 ≤ Real.log m := Real.log_nonneg hm
  have hr : Real.log 9 / Real.log (4/3) ≤ 16 := by
    rw [div_le_iff₀ h43pos]
    have h1 : Real.log 9 ≤ Real.log ((4/3:ℝ)^16) := Real.log_le_log (by norm_num) (by norm_num)
    rwa [Real.log_pow] at h1
  have h9 : (9:ℝ)^n = Real.exp ((n:ℝ) * Real.log 9) := by
    rw [← Real.rpow_natCast (9:ℝ) n, Real.rpow_def_of_pos (by norm_num)]; ring
  have hm16 : m ^ 16 = Real.exp (16 * Real.log m) := by
    rw [← Real.rpow_natCast m 16, Real.rpow_def_of_pos hmpos]; ring
  rw [h9, hm16]
  apply Real.exp_le_exp.mpr
  have h2 : (n:ℝ) * Real.log 9
      = ((n:ℝ) * Real.log (4/3)) * (Real.log 9 / Real.log (4/3)) := by
    field_simp
  rw [h2]
  calc ((n:ℝ) * Real.log (4/3)) * (Real.log 9 / Real.log (4/3))
      ≤ (Real.log m) * (Real.log 9 / Real.log (4/3)) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ ≤ (Real.log m) * 16 := mul_le_mul_of_nonneg_left hr hLnn
    _ = 16 * Real.log m := by ring

/-! ## The theorem -/

theorem block_factorization :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∃ (n : ℕ) (w : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℤ)
        (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ),
      (δ = 1 ∨ δ = -1 ∨ δ = ModularGroup.S ∨ δ = -ModularGroup.S) ∧
      (∀ i : Fin n, ∃ k : ℤ, w i = ModularGroup.T ^ k ∨
        w i = ModularGroup.S * ModularGroup.T ^ k) ∧
      (List.ofFn w).prod * δ = γ ∧
      (n : ℝ) ≤ C * (1 + Real.log (1 + Work.Asymptotics.Frob γ)) ∧
      (∏ i, (1 + Work.Asymptotics.Frob (w i))) ≤ C * (1 + Work.Asymptotics.Frob γ) ^ N := by
  refine ⟨8, 33, by norm_num, by norm_num, fun γ => ?_⟩
  obtain ⟨L, δ, hbl, hδ, hprod, hn, hpr⟩ := main_induction (frobSq γ) γ le_rfl
  have h1eq : (((frobSq γ : ℕ) : ℝ)) = Frob γ ^ 2 := by
    rw [Frob_eq_sqrt_frobSq, Real.sq_sqrt (by positivity)]
  have hF1 : (1:ℝ) ≤ Frob γ := one_le_Frob γ
  refine ⟨L.length, L.get, δ, hδ, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hbl (L.get i) (List.get_mem L i)
  · rw [List.ofFn_get]
    exact hprod
  · have hlog43 := log_four_thirds
    have hlog2 : Real.log (((frobSq γ : ℕ) : ℝ)) = 2 * Real.log (Frob γ) := by
      rw [h1eq, Real.log_pow]; push_cast; ring
    have hnn : (0:ℝ) ≤ (L.length : ℝ) := Nat.cast_nonneg _
    have hmul : (L.length : ℝ) * (1/4) ≤ 2 * Real.log (Frob γ) := by
      nlinarith [hn, hlog43, hlog2, hnn]
    have hlogF : 0 ≤ Real.log (Frob γ) := Real.log_nonneg hF1
    have hlogmono : Real.log (Frob γ) ≤ Real.log (1 + Frob γ) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlogpos : 0 ≤ Real.log (1 + Frob γ) := Real.log_nonneg (by linarith)
    linarith
  · have hδ2 : frobSq δ = 2 := frobSq_of_isBase hδ
    have hmap : (List.ofFn fun i : Fin L.length => 1 + Frob (L.get i))
        = L.map (fun x => 1 + Frob x) := by
      have h2 : List.ofFn (Function.comp (fun x => 1 + Frob x) L.get)
          = L.map (fun x => 1 + Frob x) := by
        rw [← List.map_ofFn, List.ofFn_get]
      exact h2
    rw [← List.prod_ofFn, hmap]
    have hL1 : (1:ℝ) ≤ (((frobSq γ : ℕ) : ℝ)) := by rw [h1eq]; nlinarith [hF1]
    have h9 : (9:ℝ) ^ L.length ≤ ((((frobSq γ : ℕ) : ℝ))) ^ 16 :=
      nine_pow_le L.length _ hL1 hn
    have hsqrt : Real.sqrt ((((frobSq γ : ℕ) : ℝ)) / (((frobSq δ : ℕ) : ℝ))) ≤ Frob γ := by
      rw [hδ2]
      have h2 : (((frobSq γ : ℕ) : ℝ)) / (2:ℝ) ≤ Frob γ ^ 2 := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]; nlinarith [hF1]
      calc Real.sqrt ((((frobSq γ : ℕ) : ℝ)) / (2:ℝ)) ≤ Real.sqrt (Frob γ ^ 2) :=
            Real.sqrt_le_sqrt h2
        _ = Frob γ := Real.sqrt_sq (by linarith)
    have h4 : 9 ^ L.length * Real.sqrt ((((frobSq γ : ℕ) : ℝ)) / (((frobSq δ : ℕ) : ℝ)))
        ≤ (((frobSq γ : ℕ) : ℝ)) ^ 16 * Frob γ :=
      mul_le_mul h9 hsqrt (Real.sqrt_nonneg _) (pow_nonneg (by positivity) 16)
    have h5 : (((frobSq γ : ℕ) : ℝ)) ^ 16 * Frob γ = Frob γ ^ 33 := by rw [h1eq]; ring
    have hA : (L.map fun x => 1 + Frob x).prod ≤ Frob γ ^ 33 :=
      le_trans hpr (le_trans h4 h5.le)
    have hB : Frob γ ^ 33 ≤ 8 * (1 + Frob γ) ^ (33:ℕ) :=
      le_trans (pow_le_pow_left₀ (by linarith) (by linarith) 33)
        (le_mul_of_one_le_left (pow_nonneg (by linarith : (0:ℝ) ≤ 1 + Frob γ) 33) (by norm_num))
    have hC : (L.map fun x => 1 + Frob x).prod ≤ 8 * (1 + Frob γ) ^ (33:ℕ) := le_trans hA hB
    rw [show (33:ℝ) = ((33:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    exact hC

end Work.Asymptotics
