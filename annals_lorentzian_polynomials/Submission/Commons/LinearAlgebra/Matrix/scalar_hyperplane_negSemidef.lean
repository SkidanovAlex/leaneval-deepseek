import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Field.Basic

set_option linter.unnecessarySimpa false

namespace Commons.LinearAlgebra.Matrix

open scoped BigOperators

set_option autoImplicit false

/-- Weighted version of the scalar weights `lam` cut at the distinguished index `p`:
zero at `p`, and `-lam i` elsewhere (nonnegative when `lam i ≤ 0`). -/
private def wLam {n : ℕ} (lam : Fin n → ℝ) (p i : Fin n) : ℝ :=
  if i = p then 0 else -lam i

private lemma wLam_self {n : ℕ} (lam : Fin n → ℝ) (p : Fin n) : wLam lam p p = 0 := by
  simp [wLam]

private lemma wLam_of_ne {n : ℕ} (lam : Fin n → ℝ) (p : Fin n) {i : Fin n} (hi : i ≠ p) :
    wLam lam p i = -lam i := by
  simp [wLam, hi]

/-- Cauchy--Schwarz for the semi-inner product `(x, y) ↦ ∑ i, w i * x i * y i` with
nonnegative weights `w`. -/
private lemma weighted_cs {n : ℕ} (w a b : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i : Fin n, w i * (a i * b i)) ^ 2 ≤
      (∑ i : Fin n, w i * (a i * a i)) * (∑ i : Fin n, w i * (b i * b i)) := by
  classical
  have hsqrt : ∀ i : Fin n, Real.sqrt (w i) * Real.sqrt (w i) = w i := by
    intro i
    rw [← sq]
    exact Real.sq_sqrt (hw i)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun i => Real.sqrt (w i) * a i) (fun i => Real.sqrt (w i) * b i)
  have hcs' : (∑ i : Fin n, (Real.sqrt (w i) * a i) * (Real.sqrt (w i) * b i)) ^ 2 ≤
      (∑ i : Fin n, (Real.sqrt (w i) * a i) ^ 2) * (∑ i : Fin n, (Real.sqrt (w i) * b i) ^ 2) := by
    simpa using hcs
  have hL : (∑ i : Fin n, (Real.sqrt (w i) * a i) * (Real.sqrt (w i) * b i)) =
      ∑ i : Fin n, w i * (a i * b i) := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (Real.sqrt (w i) * a i) * (Real.sqrt (w i) * b i)
          = (Real.sqrt (w i) * Real.sqrt (w i)) * (a i * b i) := by ring
      _ = w i * (a i * b i) := by rw [hsqrt i]
  have hR : (∑ i : Fin n, (Real.sqrt (w i) * a i) ^ 2) * (∑ i : Fin n, (Real.sqrt (w i) * b i) ^ 2) =
      (∑ i : Fin n, w i * (a i * a i)) * (∑ i : Fin n, w i * (b i * b i)) := by
    have h1 : (∑ i : Fin n, (Real.sqrt (w i) * a i) ^ 2) = ∑ i : Fin n, w i * (a i * a i) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (Real.sqrt (w i) * a i) ^ 2 = (Real.sqrt (w i) * Real.sqrt (w i)) * (a i * a i) := by ring
        _ = w i * (a i * a i) := by rw [hsqrt i]
    have h2 : (∑ i : Fin n, (Real.sqrt (w i) * b i) ^ 2) = ∑ i : Fin n, w i * (b i * b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (Real.sqrt (w i) * b i) ^ 2 = (Real.sqrt (w i) * Real.sqrt (w i)) * (b i * b i) := by ring
        _ = w i * (b i * b i) := by rw [hsqrt i]
    rw [h1, h2]
  rwa [hL, hR] at hcs'

/-- Decompose `∑ lam i * a i * b i` into the term at `p` and the negative of the
weighted sum with weights `wLam lam p`. -/
private lemma lam_sum_decompose {n : ℕ} (lam a b : Fin n → ℝ) (p : Fin n) :
    (∑ i : Fin n, lam i * (a i * b i)) =
      lam p * (a p * b p) - ∑ i : Fin n, wLam lam p i * (a i * b i) := by
  classical
  have hsplit : (∑ i : Fin n, lam i * (a i * b i))
      = lam p * (a p * b p) + ∑ i ∈ (Finset.univ : Finset (Fin n)).erase p, lam i * (a i * b i) := by
    calc
      (∑ i : Fin n, lam i * (a i * b i))
          = ∑ i ∈ (Finset.univ : Finset (Fin n)).erase p, lam i * (a i * b i)
              + lam p * (a p * b p) := by
            simpa using (Finset.sum_erase_add (Finset.univ : Finset (Fin n))
              (fun i : Fin n => lam i * (a i * b i)) (Finset.mem_univ p)).symm
      _ = lam p * (a p * b p) + ∑ i ∈ (Finset.univ : Finset (Fin n)).erase p, lam i * (a i * b i) := by
            rw [add_comm]
  have herase : (∑ i ∈ (Finset.univ : Finset (Fin n)).erase p, lam i * (a i * b i))
      = - ∑ i : Fin n, wLam lam p i * (a i * b i) := by
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin n)).erase p, lam i * (a i * b i))
          = ∑ i ∈ (Finset.univ : Finset (Fin n)).erase p, -(wLam lam p i * (a i * b i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hne : i ≠ p := (Finset.mem_erase.mp hi).1
            rw [wLam_of_ne lam p hne]
            ring
      _ = - ∑ i ∈ (Finset.univ : Finset (Fin n)).erase p, wLam lam p i * (a i * b i) := by
            rw [Finset.sum_neg_distrib]
      _ = - ∑ i : Fin n, wLam lam p i * (a i * b i) := by
            congr 1
            rw [Finset.sum_erase_eq_sub (Finset.mem_univ p)]
            simp [wLam]
  calc
    (∑ i : Fin n, lam i * (a i * b i))
        = lam p * (a p * b p) + ∑ i ∈ (Finset.univ : Finset (Fin n)).erase p, lam i * (a i * b i) := hsplit
    _ = lam p * (a p * b p) + (- ∑ i : Fin n, wLam lam p i * (a i * b i)) := by rw [herase]
    _ = lam p * (a p * b p) - ∑ i : Fin n, wLam lam p i * (a i * b i) := by ring

theorem scalar_hyperplane_negSemidef {n : ℕ} (lam b a : Fin n → ℝ) (p : Fin n)
    (hlam_p : 0 < lam p)
    (hlam_rest : ∀ i : Fin n, i ≠ p → lam i ≤ 0)
    (hb : 0 < ∑ i : Fin n, lam i * (b i * b i))
    (hab : (∑ i : Fin n, lam i * (a i * b i)) = 0) :
    (∑ i : Fin n, lam i * (a i * a i)) ≤ 0 ∧
      ((∑ i : Fin n, lam i * (a i * a i)) = 0 → ∀ i : Fin n, lam i ≠ 0 → a i = 0) := by
  classical
  -- Nonnegative weights attached to the coordinates different from `p`.
  have hw_nonneg : ∀ i : Fin n, 0 ≤ wLam lam p i := by
    intro i
    by_cases hi : i = p
    · rw [hi, wLam_self]
    · rw [wLam_of_ne lam p hi]
      exact neg_nonneg.mpr (hlam_rest i hi)
  -- Split each quadratic/bilinear sum at the distinguished coordinate `p`.
  have hQa : (∑ i : Fin n, lam i * (a i * a i)) =
      lam p * (a p * a p) - ∑ i : Fin n, wLam lam p i * (a i * a i) := by
    simpa using lam_sum_decompose lam a a p
  have hQb : (∑ i : Fin n, lam i * (b i * b i)) =
      lam p * (b p * b p) - ∑ i : Fin n, wLam lam p i * (b i * b i) := by
    simpa using lam_sum_decompose lam b b p
  have hCross : (∑ i : Fin n, lam i * (a i * b i)) =
      lam p * (a p * b p) - ∑ i : Fin n, wLam lam p i * (a i * b i) := by
    simpa using lam_sum_decompose lam a b p
  -- Orthogonality `hab` rewritten with the split weights: `W = lam p * a p * b p`.
  have hW_eq : (∑ i : Fin n, wLam lam p i * (a i * b i)) = lam p * (a p * b p) := by
    linarith [hab, hCross]
  -- `V < lam p * (b p * b p)` and positivity of the `p`-th contribution of `b`.
  have hbV : 0 < lam p * (b p * b p) - ∑ i : Fin n, wLam lam p i * (b i * b i) := by
    linarith [hb, hQb]
  have hV_nonneg : 0 ≤ ∑ i : Fin n, wLam lam p i * (b i * b i) := by
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (hw_nonneg i) (mul_self_nonneg (b i)))
  have hTpos : 0 < lam p * (b p * b p) := by linarith
  have hU_nonneg : 0 ≤ ∑ i : Fin n, wLam lam p i * (a i * a i) := by
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (hw_nonneg i) (mul_self_nonneg (a i)))
  -- Cauchy--Schwarz for the weighted space part.
  have hcs : (∑ i : Fin n, wLam lam p i * (a i * b i)) ^ 2 ≤
      (∑ i : Fin n, wLam lam p i * (a i * a i)) * (∑ i : Fin n, wLam lam p i * (b i * b i)) := by
    exact weighted_cs (wLam lam p) a b hw_nonneg
  -- Core chain: `(lam p * b p^2) * quad_a ≤ - (weighted part) * quad_b`.
  have hchain : (lam p * (b p * b p)) * (∑ i : Fin n, lam i * (a i * a i)) ≤
      -(∑ i : Fin n, wLam lam p i * (a i * a i)) * (∑ i : Fin n, lam i * (b i * b i)) := by
    calc
      (lam p * (b p * b p)) * (∑ i : Fin n, lam i * (a i * a i))
          = (lam p * (b p * b p)) *
              (lam p * (a p * a p) - ∑ i : Fin n, wLam lam p i * (a i * a i)) := by
            rw [hQa]
      _ = (lam p * (a p * b p)) ^ 2
            - (lam p * (b p * b p)) * (∑ i : Fin n, wLam lam p i * (a i * a i)) := by
            ring
      _ = (∑ i : Fin n, wLam lam p i * (a i * b i)) ^ 2
            - (lam p * (b p * b p)) * (∑ i : Fin n, wLam lam p i * (a i * a i)) := by
            rw [← hW_eq]
      _ ≤ (∑ i : Fin n, wLam lam p i * (a i * a i)) * (∑ i : Fin n, wLam lam p i * (b i * b i))
            - (lam p * (b p * b p)) * (∑ i : Fin n, wLam lam p i * (a i * a i)) := by
            linarith
      _ = -(∑ i : Fin n, wLam lam p i * (a i * a i)) *
            (lam p * (b p * b p) - ∑ i : Fin n, wLam lam p i * (b i * b i)) := by
            ring
      _ = -(∑ i : Fin n, wLam lam p i * (a i * a i)) * (∑ i : Fin n, lam i * (b i * b i)) := by
            rw [← hQb]
  have hneg : -(∑ i : Fin n, wLam lam p i * (a i * a i)) * (∑ i : Fin n, lam i * (b i * b i)) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hU_nonneg) (le_of_lt hb)
  -- First conjunct: the quadratic form in `a` is nonpositive.
  have hQa_le0 : (∑ i : Fin n, lam i * (a i * a i)) ≤ 0 := by
    by_contra h
    have hpos : 0 < (∑ i : Fin n, lam i * (a i * a i)) := lt_of_not_ge h
    have hp : 0 < (lam p * (b p * b p)) * (∑ i : Fin n, lam i * (a i * a i)) := mul_pos hTpos hpos
    have hle : (lam p * (b p * b p)) * (∑ i : Fin n, lam i * (a i * a i)) ≤ 0 :=
      le_trans hchain hneg
    linarith
  constructor
  · exact hQa_le0
  · intro hQa0 i hlami
    -- From vanishing of the quadratic form we first get that the weighted space part
    -- `U = ∑ wLam lam p i * a i ^ 2` vanishes.
    have hU0 : (∑ i : Fin n, wLam lam p i * (a i * a i)) = 0 := by
      have hz : (lam p * (b p * b p)) * (∑ i : Fin n, lam i * (a i * a i)) = 0 := by
        simp [hQa0]
      have hge : 0 ≤ -(∑ i : Fin n, wLam lam p i * (a i * a i)) * (∑ i : Fin n, lam i * (b i * b i)) := by
        linarith
      have hm : -(∑ i : Fin n, wLam lam p i * (a i * a i)) * (∑ i : Fin n, lam i * (b i * b i)) = 0 :=
        le_antisymm hneg hge
      have hnegmul : (-(∑ i : Fin n, wLam lam p i * (a i * a i))) *
          (∑ i : Fin n, lam i * (b i * b i)) =
          -((∑ i : Fin n, wLam lam p i * (a i * a i)) * (∑ i : Fin n, lam i * (b i * b i))) := by
        ring
      have hm' : (∑ i : Fin n, wLam lam p i * (a i * a i)) * (∑ i : Fin n, lam i * (b i * b i)) = 0 := by
        exact neg_eq_zero.mp (by simpa [hnegmul] using hm)
      exact (mul_eq_zero.mp hm').resolve_right (ne_of_gt hb)
    -- Every weighted square vanishes.
    have hterm_zero : ∀ i : Fin n, wLam lam p i * (a i * a i) = 0 := by
      intro j
      have hiff := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun k : Fin n => wLam lam p k * (a k * a k))
        (by intro k hk; exact mul_nonneg (hw_nonneg k) (mul_self_nonneg (a k)))).1 hU0
      exact hiff j (Finset.mem_univ j)
    by_cases hip : i = p
    · rw [hip]
      have hTp : lam p * (a p * a p) = 0 := by
        linarith [hQa, hU0, hQa0]
      have hap2 : a p * a p = 0 := (mul_eq_zero.mp hTp).resolve_left (ne_of_gt hlam_p)
      exact mul_self_eq_zero.mp hap2
    · have hw_ne : wLam lam p i ≠ 0 := by
        rw [wLam_of_ne lam p hip]
        exact neg_ne_zero.mpr hlami
      have hsq : a i * a i = 0 := (mul_eq_zero.mp (hterm_zero i)).resolve_left hw_ne
      exact mul_self_eq_zero.mp hsq

end Commons.LinearAlgebra.Matrix