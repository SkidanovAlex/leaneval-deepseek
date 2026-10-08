/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The number of elements of `SL(2,F)` of trace `t` and order a prime `r`

For a finite field `F` (so that `Nat.card F = |F|`) and a `t : F` with `Rootless F t`
(i.e. `quad F t = X² - tX + 1` has no root in `F`, equivalently `t ≠ ±2` and `t² - 4`
is a nonsquare), the trace-`t` class of `SL(2,F)` has exactly `|F|(|F| - 1)` elements, and
an element of it has order a prime `r` exactly when `quad F t ∣ X ^ r - 1`; both are
independent of the element.  Consequently

`Nat.card {x : SL(2,F) // trace x = t ∧ orderOf x = r}
   = |F|(|F| - 1) * indicator (quad F t ∣ X ^ r - 1)`.

The two ingredients are proved here as private lemmas (`card_traceClass`, the explicit
bijection `x ↦ (x₀₀, x₀₁)` onto `F × Fˣ`; and `orderOf_eq_prime_iff_quad_dvd`, via the
`F`-algebra `F[X]/(quad F t) ≅ F[x] ⊆ M₂(F)`, which is a field because `quad F t` is
irreducible, together with Cayley–Hamilton).
-/
import Mathlib
import Submission.Work.L2F.Props.Count.Defs
import Submission.Work.L2F.Props.Count.Basic

open scoped MatrixGroups
open Matrix Polynomial

namespace Work.L2F.Props.Count

variable {F : Type*} [Field F]

/-- `X² - tX + 1` is irreducible as soon as it has no root in `F`. -/
private lemma quad_irreducible {t : F} (ht : Work.L2F.Count.Rootless F t) :
    Irreducible (Work.L2F.Count.quad F t) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [show Work.L2F.Count.quad F t =
        Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C (-t) * Polynomial.X + Polynomial.C 1 by
      simp only [Work.L2F.Count.quad, Polynomial.C_neg, Polynomial.C_1]; ring]
    rw [Polynomial.natDegree_quadratic (by norm_num)]
    norm_num
  · intro a ha
    exact ht a ((Work.L2F.Count.quad_isRoot_iff t a).mp ha)

/-- Cayley–Hamilton: `x` annihilates its characteristic polynomial `quad F (trace x)`. -/
private lemma aeval_quad_eq_zero (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    Polynomial.aeval (x : Matrix (Fin 2) (Fin 2) F)
      (Work.L2F.Count.quad F ((x : Matrix (Fin 2) (Fin 2) F).trace)) = 0 := by
  rw [← Work.L2F.Count.charpoly_sl x]
  exact Matrix.aeval_self_charpoly _

/-- For `x ∈ SL(2,F)` of rootless trace, a polynomial vanishes at `x` exactly when it is a
multiple of `quad F (trace x)` (the minimal polynomial of `x`). -/
private lemma aeval_eq_zero_iff_quad_dvd (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (ht : Work.L2F.Count.Rootless F ((x : Matrix (Fin 2) (Fin 2) F).trace)) (p : F[X]) :
    Polynomial.aeval (x : Matrix (Fin 2) (Fin 2) F) p = 0 ↔
      Work.L2F.Count.quad F ((x : Matrix (Fin 2) (Fin 2) F).trace) ∣ p :=
  (quad_irreducible ht).dvd_iff_aeval_eq_zero (aeval_quad_eq_zero x)

private lemma aeval_X_pow_sub_one (x : Matrix.SpecialLinearGroup (Fin 2) F) (r : ℕ) :
    Polynomial.aeval (x : Matrix (Fin 2) (Fin 2) F) ((Polynomial.X : F[X]) ^ r - 1) =
      (x : Matrix (Fin 2) (Fin 2) F) ^ r - 1 := by
  rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_one]

/-- An element of `SL(2,F)` whose trace is rootless has order a prime `r` exactly when
`quad F t ∣ X ^ r - 1`; in particular this does not depend on the element. -/
private lemma orderOf_eq_prime_iff_quad_dvd {t : F} (ht : Work.L2F.Count.Rootless F t) (r : ℕ)
    (hr : r.Prime) (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : (x : Matrix (Fin 2) (Fin 2) F).trace = t) :
    orderOf x = r ↔ Work.L2F.Count.quad F t ∣ (Polynomial.X ^ r - 1) := by
  have ht' : Work.L2F.Count.Rootless F ((x : Matrix (Fin 2) (Fin 2) F).trace) := by
    rw [hx]; exact ht
  have hne : x ≠ 1 := by
    intro h
    have h2 : (x : Matrix (Fin 2) (Fin 2) F).trace = 2 := by
      rw [h]
      rw [show ((1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 from rfl,
        Matrix.trace_one]
      simp
    rw [h2] at hx
    exact Work.L2F.Count.rootless_ne_two ht hx.symm
  have key : ∀ p : F[X], Polynomial.aeval (x : Matrix (Fin 2) (Fin 2) F) p = 0 ↔
      Work.L2F.Count.quad F t ∣ p := by
    intro p
    have h := aeval_eq_zero_iff_quad_dvd x ht' p
    rw [hx] at h
    exact h
  constructor
  · intro h
    have hpow : x ^ r = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, h]
    have hm : (x : Matrix (Fin 2) (Fin 2) F) ^ r = 1 := by
      rw [← show ((x ^ r : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (x : Matrix (Fin 2) (Fin 2) F) ^ r from rfl, hpow]
      rfl
    rw [← (key ((Polynomial.X : F[X]) ^ r - 1))]
    rw [aeval_X_pow_sub_one, hm]
    simp
  · intro h
    have hm : (x : Matrix (Fin 2) (Fin 2) F) ^ r = 1 := by
      have h0 := (key ((Polynomial.X : F[X]) ^ r - 1)).mpr h
      rw [aeval_X_pow_sub_one] at h0
      exact sub_eq_zero.mp h0
    have hpow : x ^ r = 1 := by
      apply Subtype.ext
      exact hm
    have hdvd : orderOf x ∣ r := orderOf_dvd_iff_pow_eq_one.mpr hpow
    rcases hr.eq_one_or_self_of_dvd (orderOf x) hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h1

/-- If `x ∈ SL(2,F)` has rootless trace then its `(0,1)`-entry is nonzero (otherwise the
determinant condition exhibits a root of `quad F t`). -/
private lemma entry01_ne_zero {t : F} (ht : Work.L2F.Count.Rootless F t)
    (x : Matrix.SpecialLinearGroup (Fin 2) F) (hx : (x : Matrix (Fin 2) (Fin 2) F).trace = t) :
    (x : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 := by
  intro h
  have hdet : (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (x : Matrix (Fin 2) (Fin 2) F) 1 1
      - (x : Matrix (Fin 2) (Fin 2) F) 0 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact x.2
  have htr : (x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1 = t := by
    rw [← Matrix.trace_fin_two]; exact hx
  rw [h, zero_mul, sub_zero] at hdet
  refine ht ((x : Matrix (Fin 2) (Fin 2) F) 0 0) ?_
  linear_combination -hdet + ((x : Matrix (Fin 2) (Fin 2) F) 0 0) * htr

/-- The trace-`t` class of `SL(2,F)`, for rootless `t`, is in bijection with `F × Fˣ` via
`x ↦ (x₀₀, x₀₁)`; the inverse sends `(a,b)` to `!![a, b; (a(t-a)-1)/b, t-a]`. -/
private noncomputable def traceClassEquiv (t : F) (ht : Work.L2F.Count.Rootless F t) :
    {x : Matrix.SpecialLinearGroup (Fin 2) F // (x : Matrix (Fin 2) (Fin 2) F).trace = t} ≃
      F × Fˣ where
  toFun x := ((x.1 : Matrix (Fin 2) (Fin 2) F) 0 0,
      Units.mk0 ((x.1 : Matrix (Fin 2) (Fin 2) F) 0 1) (entry01_ne_zero ht x.1 x.2))
  invFun p := ⟨⟨!![p.1, (p.2 : F); (p.1 * (t - p.1) - 1) / (p.2 : F), t - p.1], by
      rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Fin.isValue]
      field_simp
      ring⟩, by
      rw [Matrix.trace_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Fin.isValue]
      ring⟩
  left_inv x := by
    have hdet : (x.1 : Matrix (Fin 2) (Fin 2) F) 0 0 * (x.1 : Matrix (Fin 2) (Fin 2) F) 1 1
        - (x.1 : Matrix (Fin 2) (Fin 2) F) 0 1 * (x.1 : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
      rw [← Matrix.det_fin_two]; exact x.1.2
    have htr : (x.1 : Matrix (Fin 2) (Fin 2) F) 0 0 + (x.1 : Matrix (Fin 2) (Fin 2) F) 1 1 = t := by
      rw [← Matrix.trace_fin_two]; exact x.2
    have h01 : (x.1 : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 := entry01_ne_zero ht x.1 x.2
    apply Subtype.ext
    apply Subtype.ext
    rw [Matrix.eta_fin_two (x.1 : Matrix (Fin 2) (Fin 2) F)]
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ']
    · simp only [Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ', Units.val_mk0]
    · simp only [Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ', Units.val_mk0]
      rw [div_eq_iff h01]
      linear_combination -((x.1 : Matrix (Fin 2) (Fin 2) F) 0 0) * htr + hdet
    · simp only [Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ']
      linear_combination -htr
  right_inv p := by
    apply Prod.ext
    · simp
    · apply Units.ext
      simp

/-- The trace-`t` class of `SL(2,F)` has `|F| (|F| - 1)` elements when `t` is rootless. -/
private lemma card_traceClass [Fintype F] {t : F} (ht : Work.L2F.Count.Rootless F t) :
    Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
        (x : Matrix (Fin 2) (Fin 2) F).trace = t} = Nat.card F * (Nat.card F - 1) := by
  rw [Nat.card_congr (traceClassEquiv t ht), Nat.card_prod, Nat.card_units]

/-- The number of elements of `SL(2,F)` of trace rootless `t` and order a prime `r`. -/
theorem TraceClassCard (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) {t : F}
    (ht : Work.L2F.Count.Rootless F t) (r : ℕ) (hr : r.Prime) :
    Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
        (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧ orderOf x = r}
      = (Nat.card F * (Nat.card F - 1))
        * Work.L2F.Count.indicator (Work.L2F.Count.quad F t ∣ (Polynomial.X ^ r - 1)) := by
  classical
  by_cases hP : Work.L2F.Count.quad F t ∣ (Polynomial.X ^ r - 1)
  · rw [Work.L2F.Count.indicator_eq_one hP, mul_one]
    have heq : Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
        (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧ orderOf x = r}
        = Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
            (x : Matrix (Fin 2) (Fin 2) F).trace = t} :=
      Nat.card_congr (Equiv.subtypeEquivRight
        (p := fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
          (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧ orderOf x = r)
        (q := fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
          (x : Matrix (Fin 2) (Fin 2) F).trace = t)
        (fun x => ⟨fun h => h.1,
          fun h => ⟨h, (orderOf_eq_prime_iff_quad_dvd ht r hr x h).mpr hP⟩⟩))
    rw [heq]
    exact card_traceClass ht
  · rw [Work.L2F.Count.indicator_eq_zero hP, mul_zero, Nat.card_eq_zero]
    exact Or.inl ⟨fun x =>
      hP ((orderOf_eq_prime_iff_quad_dvd ht r hr x.1 x.2.1).mp x.2.2)⟩

end Work.L2F.Props.Count
