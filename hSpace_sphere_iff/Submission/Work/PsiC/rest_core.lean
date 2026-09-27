import Mathlib

namespace Work.PsiC

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- Generic core identity.  If `e`, `f` are orthogonal idempotents and `t` is an involution
conjugating `e` to `f`, then the elements `e (1/2)(1+t) e`, `(e+f)(1/2)(1+t)` (and `e+f`) are
idempotent and the relevant sandwich identities hold.  This is the algebraic content of the
computation in Adams--Atiyah. -/
theorem rest_gen {R : Type} [Ring R] [Algebra ℂ R] (e f t : R)
    (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0)
    (ht2 : t * t = 1) (hte : t * e * t = f) :
    (e * (algebraMap ℂ R (1 / 2) * (1 + t))) * ((1 + t) * e) = e ∧
    ((1 + t) * e) * (e * (algebraMap ℂ R (1 / 2) * (1 + t))) =
      (e + f) * (algebraMap ℂ R (1 / 2) * (1 + t)) ∧
    ((e + f) * (algebraMap ℂ R (1 / 2) * (1 + t))) *
      ((e + f) * (algebraMap ℂ R (1 / 2) * (1 + t))) =
      (e + f) * (algebraMap ℂ R (1 / 2) * (1 + t)) ∧
    (e + f) * (e + f) = e + f := by
  -- derived commutation between `t` and the idempotents
  have h1 : t * e = f * t := by
    have h := congrArg (fun x => x * t) hte
    simp only [mul_assoc, ht2, mul_one] at h
    exact h
  have h3 : e * t = t * f := by
    have h := congrArg (fun x => t * x) hte
    simp only [← mul_assoc, ht2, one_mul] at h
    exact h
  have h5 : t * f * t = e := by rw [← h3, mul_assoc, ht2, mul_one]
  -- context-free rewriting rules for products of the three generators
  have w_tt : ∀ X : R, t * (t * X) = X := fun X => by rw [← mul_assoc, ht2, one_mul]
  have w_ee : ∀ X : R, e * (e * X) = e * X := fun X => by rw [← mul_assoc, he]
  have w_ff : ∀ X : R, f * (f * X) = f * X := fun X => by rw [← mul_assoc, hf]
  have w_ef : ∀ X : R, e * (f * X) = 0 := fun X => by rw [← mul_assoc, hef, zero_mul]
  have w_fe : ∀ X : R, f * (e * X) = 0 := fun X => by rw [← mul_assoc, hfe, zero_mul]
  have w_te : ∀ X : R, t * (e * X) = f * (t * X) := fun X => by rw [← mul_assoc, h1, mul_assoc]
  have w_tf : ∀ X : R, t * (f * X) = e * (t * X) := fun X => by rw [← mul_assoc, ← h3, mul_assoc]
  -- the ring identities (no scalars)
  have K1 : (e * (1 + t)) * ((1 + t) * e) = e + e := by
    simp only [mul_add, add_mul, one_mul, mul_one, mul_assoc, h1, h3.symm, h5, he, hf, hef, hfe, ht2,
      w_tt, w_ee, w_ff, w_ef, w_fe, w_te, w_tf, zero_mul, mul_zero, add_zero, zero_add,
      add_comm, add_left_comm, add_assoc]
  have K2 : ((1 + t) * e) * (e * (1 + t)) = (e + f) * (1 + t) := by
    simp only [mul_add, add_mul, one_mul, mul_one, mul_assoc, h1, h3.symm, h5, he, hf, hef, hfe, ht2,
      w_tt, w_ee, w_ff, w_ef, w_fe, w_te, w_tf, zero_mul, mul_zero, add_zero, zero_add,
      add_comm, add_left_comm, add_assoc]
  have K3 : ((e + f) * (1 + t)) * ((e + f) * (1 + t)) = (e + f) * (1 + t) + (e + f) * (1 + t) := by
    simp only [mul_add, add_mul, one_mul, mul_one, mul_assoc, h1, h3.symm, h5, he, hf, hef, hfe, ht2,
      w_tt, w_ee, w_ff, w_ef, w_fe, w_te, w_tf, zero_mul, mul_zero, add_zero, zero_add,
      add_comm, add_left_comm, add_assoc]
  have K4 : (e + f) * (e + f) = e + f := by
    simp only [mul_add, add_mul, one_mul, mul_one, mul_assoc, h1, h3.symm, h5, he, hf, hef, hfe, ht2,
      w_tt, w_ee, w_ff, w_ef, w_fe, w_te, w_tf, zero_mul, mul_zero, add_zero, zero_add,
      add_comm, add_left_comm, add_assoc]
  -- rewrite the scalar into `•` form
  have hPt : algebraMap ℂ R (1 / 2) * (1 + t) = (1 / 2 : ℂ) • (1 + t) :=
    (Algebra.smul_def (1 / 2 : ℂ) (1 + t)).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [hPt, mul_smul_comm, smul_mul_assoc]
    rw [K1, ← two_smul ℂ e, smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul]
  · simp only [hPt, mul_smul_comm]
    rw [K2]
  · simp only [hPt, mul_smul_comm, smul_mul_assoc, smul_smul]
    rw [K3, ← two_smul ℂ ((e + f) * (1 + t)), smul_smul,
      show (1 / 2 : ℂ) * (1 / 2) * 2 = (1 / 2 : ℂ) by norm_num]
  · exact K4

theorem rest_core {R : Type} [Ring R] [Algebra ℂ R] (Am Bm s : R)
    (hAid : Am * Am = Am) (hBid : Bm * Bm = Bm) (hAB : Am * Bm = 0) (hBA : Bm * Am = 0)
    (hs2 : s * s = 1) (hsA : s * Am * s = Bm) :
    (Am * (algebraMap ℂ R (1 / 2) * (1 + s))) * ((1 + s) * Am) = Am ∧
    ((1 + s) * Am) * (Am * (algebraMap ℂ R (1 / 2) * (1 + s))) =
      (Am + Bm) * (algebraMap ℂ R (1 / 2) * (1 + s)) ∧
    (Bm * (algebraMap ℂ R (1 / 2) * (1 - s))) * ((1 - s) * Bm) = Bm ∧
    ((1 - s) * Bm) * (Bm * (algebraMap ℂ R (1 / 2) * (1 - s))) =
      (Am + Bm) * (algebraMap ℂ R (1 / 2) * (1 - s)) ∧
    ((Am + Bm) * (algebraMap ℂ R (1 / 2) * (1 + s))) *
      ((Am + Bm) * (algebraMap ℂ R (1 / 2) * (1 + s))) =
      (Am + Bm) * (algebraMap ℂ R (1 / 2) * (1 + s)) ∧
    ((Am + Bm) * (algebraMap ℂ R (1 / 2) * (1 - s))) *
      ((Am + Bm) * (algebraMap ℂ R (1 / 2) * (1 - s))) =
      (Am + Bm) * (algebraMap ℂ R (1 / 2) * (1 - s)) ∧
    (Am + Bm) * (Am + Bm) = Am + Bm := by
  have h3' : s * Bm = Am * s := by
    rw [← hsA, ← mul_assoc, ← mul_assoc, hs2, one_mul]
  have h5s : s * Bm * s = Am := by rw [h3', mul_assoc, hs2, mul_one]
  have hneg2 : (-s) * (-s) = 1 := by rw [neg_mul_neg, hs2]
  have hnegA : (-s) * Bm * (-s) = Am := by
    rw [neg_mul, mul_neg, neg_mul, neg_neg, h5s]
  obtain ⟨g1, g2, g5, g7⟩ := rest_gen Am Bm s hAid hBid hAB hBA hs2 hsA
  obtain ⟨g3, g4, g6, _⟩ := rest_gen Bm Am (-s) hBid hAid hBA hAB hneg2 hnegA
  exact ⟨g1, g2, by simpa [sub_eq_add_neg] using g3,
    by simpa [sub_eq_add_neg, add_comm] using g4, g5,
    by simpa [sub_eq_add_neg, add_comm] using g6, g7⟩

end Work.PsiC
