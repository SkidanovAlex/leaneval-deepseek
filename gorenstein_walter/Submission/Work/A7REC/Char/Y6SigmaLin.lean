/-
Area `A7REC`, leaf `Char/Y6SigmaLin.lean`: the linear algebra of the value of the degree-`6`
irreducible character at `σ`.

The statement `Work.A7REC.A7Y6SigmaLinProp` (see `Char/Y6Defs.lean`) is the following elementary
linear-algebra fact over `ℂ`: for a `6`-dimensional complex vector space `V` and endomorphisms
`A B C` with

* `A ^ 3 = 1`, `B ^ 2 = 1`, `B * A * B = A * A`,
* `C ^ 2 = 1`, `A * C = C * A`,
* `trace (B * A) = 2`, `trace C = 2`, `trace (C * A) = -1`,

one has `trace A = 3`.

The proof is entirely trace-theoretic.  Let `ω` be a primitive cube root of unity.  Since
`A ^ 3 = 1`, the three *eigenprojections* of `A`

`e₁ = (1 + A + A²)/3`,  `e₂ = (1 + ω²A + ωA²)/3`,  `e₃ = (1 + ωA + ω²A²)/3`

satisfy `e₁ + e₂ + e₃ = 1`, `A = e₁ + ωe₂ + ω²e₃`, are idempotent, and satisfy `e₂e₃ = 0`.
Writing `a = tr e₁`, `b = tr e₂`, `c = tr e₃` (all nonnegative integers, with `a + b + c = 6`),
the conjugation relation `BAB = A²` gives `B e₂ B = e₃`, whence `b = c`; the trace hypothesis
`tr(BA) = 2` shows `a ≠ 0` while `tr(Ce₂)` and `tr(Ce₃)` are integers which, together with
`tr C = 2` and `tr(CA) = -1`, force `tr(Ce₂) = 1`, so `b` is odd.  With `a + 2b = 6` and `a ≠ 0`
this gives `b = 1`, `a = 4`, hence `tr A = 4 - 1 = 3`.
-/
import Mathlib
import Submission.Work.A7REC.Char.Y6Defs

namespace Work.A7REC.Char

open Polynomial

/-! ## The primitive cube root of unity -/

/-- A concrete primitive cube root of unity, `-1/2 + (√3/2) i`. -/
noncomputable def gwOm : ℂ := Complex.mk (-1/2) (Real.sqrt 3 / 2)

lemma gwOm_sq : gwOm ^ 2 = Complex.mk (-1/2) (-(Real.sqrt 3 / 2)) := by
  rw [pow_two]
  apply Complex.ext <;> simp [gwOm, Complex.mul_re, Complex.mul_im]
  · ring_nf; rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring
  · ring

lemma gwOm_quad : gwOm ^ 2 + gwOm + 1 = 0 := by
  rw [gwOm_sq]
  apply Complex.ext <;> simp [gwOm, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im] <;> ring

lemma gwOm_add_sq : gwOm + gwOm ^ 2 = -1 := by linear_combination gwOm_quad

lemma gwOm_sq_eq_neg : gwOm ^ 2 = -1 - gwOm := by linear_combination gwOm_quad

lemma gwOm_im_ne_zero : gwOm.im ≠ 0 := by
  simp [gwOm, ne_of_gt (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 3))]

/-- `ω` is not a rational number: `ω * k = l` with `k, l` integers forces `k = 0`. -/
lemma gwOm_mul_int (k l : ℤ) (h : gwOm * (k : ℂ) = (l : ℂ)) : k = 0 := by
  have h2 := congrArg Complex.im h
  rw [Complex.mul_im] at h2
  simp at h2
  rcases h2 with h' | h'
  · exact absurd h' gwOm_im_ne_zero
  · exact h'

/-! ## The three eigenprojections of `A`, as polynomials in `A` -/

noncomputable abbrev gW : Polynomial ℂ := Polynomial.C gwOm
noncomputable abbrev gu1 : Polynomial ℂ := 1 + X + X ^ 2
noncomputable abbrev gu2 : Polynomial ℂ := 1 + gW ^ 2 * X + gW * X ^ 2
noncomputable abbrev gu3 : Polynomial ℂ := 1 + gW * X + gW ^ 2 * X ^ 2

/-- `e₁ * e₁ = e₁`, scaled by `9`. -/
lemma pid1 : gu1 * gu1 - 3 * gu1 = (X ^ 3 - 1) * (X + 2) := by ring

/-- `e₂ * e₂ = e₂`, scaled by `9`. -/
lemma pid2 : gu2 * gu2 - 3 * gu2
    = (X ^ 3 - 1) * (2 + gW ^ 2 * X) + (gW - 1) * (gW * X ^ 2 + 2 * X ^ 3) * (gW ^ 2 + gW + 1) := by
  ring

/-- `e₃ * e₃ = e₃`, scaled by `9`. -/
lemma pid3 : gu3 * gu3 - 3 * gu3
    = (X ^ 3 - 1) * (2 + gW * X) + (gW - 1) * (2 * X ^ 3 + gW * X ^ 4) * (gW ^ 2 + gW + 1) := by
  ring

/-- `e₂ * e₃ = 0`, scaled by `9`. -/
lemma pid23 : gu2 * gu3 = (X ^ 3 - 1) * (X - 1)
    + (gW ^ 2 + gW + 1) * (X + gW * X ^ 2 + (gW ^ 2 - gW + 1) * X ^ 3 + (gW - 1) * X ^ 4) := by
  ring

/-- `3 * A = e₁ + ω e₂ + ω² e₃`. -/
lemma pidA : gu1 + gW * gu2 + gW ^ 2 * gu3
    = 3 * X + (gW ^ 2 + gW + 1) * (1 + 2 * (gW - 1) * X + (1 + gW ^ 2 - gW) * X ^ 2) := by
  ring

/-- `3 = e₁ + e₂ + e₃`. -/
lemma pidS : gu1 + gu2 + gu3 = 3 + (gW ^ 2 + gW + 1) * (X + X ^ 2) := by ring

/-- Multiplication of a scalar multiple by a scalar multiple. -/
lemma gwSMS {V : Type} [AddCommGroup V] [Module ℂ V] (c d : ℂ) (x y : Module.End ℂ V) :
    (c • x) * (d • y) = (c * d) • (x * y) := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

section GW

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The `ℂ`-algebra homomorphism `ℂ[X] → End V`, `X ↦ A`. -/
noncomputable def gwE (A : Module.End ℂ V) : Polynomial ℂ →ₐ[ℂ] Module.End ℂ V := Polynomial.aeval A

/-- The eigenprojection of `A` onto its `1`-eigenspace. -/
noncomputable def gwE1 (A : Module.End ℂ V) : Module.End ℂ V := (3 : ℂ)⁻¹ • gwE A gu1

/-- The eigenprojection of `A` onto its `ω`-eigenspace. -/
noncomputable def gwE2 (A : Module.End ℂ V) : Module.End ℂ V := (3 : ℂ)⁻¹ • gwE A gu2

/-- The eigenprojection of `A` onto its `ω²`-eigenspace. -/
noncomputable def gwE3 (A : Module.End ℂ V) : Module.End ℂ V := (3 : ℂ)⁻¹ • gwE A gu3

lemma gwE_X (A : Module.End ℂ V) : gwE A X = A := Polynomial.aeval_X A

lemma gwE_C (A : Module.End ℂ V) (r : ℂ) :
    gwE A (Polynomial.C r) = algebraMap ℂ (Module.End ℂ V) r := Polynomial.aeval_C A r

lemma gwE_X2 (A : Module.End ℂ V) : gwE A (X ^ 2) = A ^ 2 := by rw [map_pow, gwE_X]

lemma gwE_X3 (A : Module.End ℂ V) (hA : A ^ 3 = 1) : gwE A (X ^ 3 - 1) = 0 := by
  rw [map_sub, map_pow, gwE_X, map_one, hA, sub_self]

lemma gwE_gW (A : Module.End ℂ V) : gwE A gW = gwOm • (1 : Module.End ℂ V) := by
  rw [gW] at *; rw [gwE_C, Algebra.algebraMap_eq_smul_one]

lemma gwE_gWs (A : Module.End ℂ V) : gwE A (gW ^ 2) = gwOm ^ 2 • (1 : Module.End ℂ V) := by
  rw [map_pow, gwE_gW, pow_two, gwSMS, one_mul, sq]

lemma gwE_W (A : Module.End ℂ V) : gwE A (gW ^ 2 + gW + 1) = 0 := by
  have h1 : gW ^ 2 + gW + 1 = Polynomial.C (gwOm ^ 2 + gwOm + 1) := by
    rw [gW]; simp only [map_add, map_pow, map_one]
  rw [h1, gwE_C, Algebra.algebraMap_eq_smul_one, gwOm_quad, zero_smul]

lemma gwE_3 (A : Module.End ℂ V) : gwE A (3 : Polynomial ℂ) = (3 : ℂ) • (1 : Module.End ℂ V) := by
  rw [show (3 : Polynomial ℂ) = Polynomial.C (3 : ℂ) from (Polynomial.C_ofNat 3).symm,
      gwE_C, Algebra.algebraMap_eq_smul_one]

lemma gwE_kill (A : Module.End ℂ V) : ∀ p q : Polynomial ℂ, gwE A p = 0 → gwE A (p * q) = 0 := by
  intro p q hp; rw [map_mul, hp, zero_mul]

lemma gwE_kill' (A : Module.End ℂ V) : ∀ p q : Polynomial ℂ, gwE A q = 0 → gwE A (p * q) = 0 := by
  intro p q hq; rw [map_mul, hq, mul_zero]

lemma gwE_gu1 (A : Module.End ℂ V) : gwE A gu1 = 1 + A + A ^ 2 := by
  simp only [gu1, map_add, map_one, gwE_X, gwE_X2]

lemma gwE_gu2 (A : Module.End ℂ V) : gwE A gu2 = 1 + gwOm ^ 2 • A + gwOm • A ^ 2 := by
  simp only [gu2, map_add, map_one, map_mul, gwE_gWs, gwE_gW, gwE_X, gwE_X2]
  rw [Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, one_mul, one_mul]

lemma gwE_gu3 (A : Module.End ℂ V) : gwE A gu3 = 1 + gwOm • A + gwOm ^ 2 • A ^ 2 := by
  simp only [gu3, map_add, map_one, map_mul, gwE_gWs, gwE_gW, gwE_X, gwE_X2]
  rw [Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, one_mul, one_mul]

end GW

/-! ## Auxiliary lemmas -/

/-- Anything commuting with `A` commutes with every polynomial in `A`. -/
lemma gwCommuteAeval {V : Type} [AddCommGroup V] [Module ℂ V] (A Cc : Module.End ℂ V)
    (hc : Cc * A = A * Cc) (p : Polynomial ℂ) :
    Cc * Polynomial.aeval A p = Polynomial.aeval A p * Cc := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, mul_add, add_mul, hp, hq]
  | monomial n a =>
      rw [Polynomial.aeval_monomial]
      have hpow : Cc * A ^ n = A ^ n * Cc := by
        induction n with
        | zero => simp
        | succ k ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hc, ← mul_assoc]
      rw [← mul_assoc, ← Algebra.commutes a Cc, mul_assoc, hpow, ← mul_assoc]

/-- If `C` is an involution commuting with an idempotent `e`, then `tr (C * e)` has the form
`2 m - dim (range e)` for some natural number `m`; in particular it is an integer congruent to
`- dim (range e)` modulo `2`. -/
lemma gwTraceInvIdem {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Cc e : Module.End ℂ V) (hC : Cc * Cc = 1) (he : e * e = e) (hc : Cc * e = e * Cc) :
    ∃ m : ℕ, LinearMap.trace ℂ V (Cc * e)
      = 2 * (m : ℂ) - (Module.finrank ℂ (LinearMap.range e) : ℂ) := by
  have h1e : (1 + Cc) * e = e * (1 + Cc) := by rw [add_mul, one_mul, mul_add, mul_one, hc]
  set Re : Module.End ℂ V := (2 : ℂ)⁻¹ • (1 + Cc) with hRe
  have hRe2 : Re * Re = Re := by
    rw [hRe, gwSMS]
    have hsq : (1 + Cc) * (1 + Cc) = (2 : ℂ) • (1 + Cc) := by
      rw [Algebra.smul_def, show (algebraMap ℂ (Module.End ℂ V)) 2 = 2 from map_ofNat _ 2]
      rw [two_mul, mul_add, mul_one, add_mul, one_mul, hC]; abel
    rw [hsq, smul_smul]; norm_num
  have hRe_comm : Re * e = e * Re := by
    rw [hRe]; rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← h1e]
  have hRee : (Re * e) * (Re * e) = Re * e := by
    rw [show (Re * e) * (Re * e) = Re * (e * Re) * e by noncomm_ring, ← hRe_comm, ← mul_assoc,
      hRe2, mul_assoc, he]
  have htrRee : LinearMap.trace ℂ V (Re * e)
      = (Module.finrank ℂ (LinearMap.range (Re * e)) : ℂ) :=
    (LinearMap.IsIdempotentElem.isProj_range (Re * e) hRee).trace
  have htr_e : LinearMap.trace ℂ V e = (Module.finrank ℂ (LinearMap.range e) : ℂ) :=
    (LinearMap.IsIdempotentElem.isProj_range e he).trace
  have hCc : Cc = (2 : ℂ) • Re - 1 := by
    rw [hRe, smul_smul, show (2 : ℂ) * (2 : ℂ)⁻¹ = 1 by norm_num, one_smul]; abel
  have hCe_eq : Cc * e = (2 : ℂ) • (Re * e) - e := by
    rw [hCc, sub_mul, Algebra.smul_mul_assoc, one_mul]
  have htr : LinearMap.trace ℂ V (Cc * e)
      = 2 * LinearMap.trace ℂ V (Re * e) - LinearMap.trace ℂ V e := by
    rw [hCe_eq]; simp only [map_sub, map_smul, smul_eq_mul]
  exact ⟨Module.finrank ℂ (LinearMap.range (Re * e)), by rw [htr, htrRee, htr_e]⟩

/-! ## The main statement -/

theorem Y6SigmaLin : Work.A7REC.A7Y6SigmaLinProp := by
  intro V _ _ _ hdim A B Cc hA hB hBA hC hAC htrBA htrC htrCA
  have hEX3 := gwE_X3 A hA
  have hEW := gwE_W A
  have hE3 := gwE_3 A
  have hp23 : gwE A (gu2 * gu3) = 0 := by
    rw [pid23, map_add, gwE_kill A (X ^ 3 - 1) (X - 1) hEX3,
        gwE_kill A (gW ^ 2 + gW + 1)
          (X + gW * X ^ 2 + (gW ^ 2 - gW + 1) * X ^ 3 + (gW - 1) * X ^ 4) hEW, add_zero]
  have he2e3 : gwE2 A * gwE3 A = 0 := by rw [gwE2, gwE3, gwSMS, ← map_mul, hp23, smul_zero]
  have he3e2 : gwE3 A * gwE2 A = 0 := by
    rw [gwE3, gwE2, gwSMS, ← map_mul, show gwE A (gu3 * gu2) = 0 by rw [mul_comm, hp23], smul_zero]
  have he1e1 : gwE1 A * gwE1 A = gwE1 A := by
    have hp : gwE A (gu1 * gu1 - 3 * gu1) = 0 := by rw [pid1, map_mul, hEX3, zero_mul]
    rw [map_sub, map_mul, map_mul, hE3] at hp
    rw [Algebra.smul_mul_assoc, one_mul, sub_eq_zero] at hp
    rw [gwE1, gwSMS, hp, smul_smul]; norm_num
  have he2e2 : gwE2 A * gwE2 A = gwE2 A := by
    have hp : gwE A (gu2 * gu2 - 3 * gu2) = 0 := by
      rw [pid2, map_add, gwE_kill A (X ^ 3 - 1) (2 + gW ^ 2 * X) hEX3,
          gwE_kill' A ((gW - 1) * (gW * X ^ 2 + 2 * X ^ 3)) (gW ^ 2 + gW + 1) hEW, add_zero]
    rw [map_sub, map_mul, map_mul, hE3] at hp
    rw [Algebra.smul_mul_assoc, one_mul, sub_eq_zero] at hp
    rw [gwE2, gwSMS, hp, smul_smul]; norm_num
  have he3e3 : gwE3 A * gwE3 A = gwE3 A := by
    have hp : gwE A (gu3 * gu3 - 3 * gu3) = 0 := by
      rw [pid3, map_add, gwE_kill A (X ^ 3 - 1) (2 + gW * X) hEX3,
          gwE_kill' A ((gW - 1) * (2 * X ^ 3 + gW * X ^ 4)) (gW ^ 2 + gW + 1) hEW, add_zero]
    rw [map_sub, map_mul, map_mul, hE3] at hp
    rw [Algebra.smul_mul_assoc, one_mul, sub_eq_zero] at hp
    rw [gwE3, gwSMS, hp, smul_smul]; norm_num
  have hAE : gwE A gu1 + gwOm • gwE A gu2 + gwOm ^ 2 • gwE A gu3 = (3 : ℂ) • A := by
    have hp : gwE A (gu1 + gW * gu2 + gW ^ 2 * gu3) = (3 : ℂ) • A := by
      rw [pidA, map_add,
          gwE_kill A (gW ^ 2 + gW + 1) (1 + 2 * (gW - 1) * X + (1 + gW ^ 2 - gW) * X ^ 2) hEW,
          add_zero, map_mul, hE3, gwE_X, Algebra.smul_mul_assoc, one_mul]
    rw [map_add, map_add, map_mul, map_mul, gwE_gW, gwE_gWs] at hp
    rw [Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, one_mul, one_mul] at hp
    exact hp
  have heA : gwE1 A + gwOm • gwE2 A + gwOm ^ 2 • gwE3 A = A := by
    rw [gwE1, gwE2, gwE3]
    rw [show gwOm • ((3 : ℂ)⁻¹ • gwE A gu2) = (3 : ℂ)⁻¹ • (gwOm • gwE A gu2) by
          rw [smul_smul, smul_smul, mul_comm],
        show gwOm ^ 2 • ((3 : ℂ)⁻¹ • gwE A gu3) = (3 : ℂ)⁻¹ • (gwOm ^ 2 • gwE A gu3) by
          rw [smul_smul, smul_smul, mul_comm]]
    rw [← smul_add, ← smul_add, hAE, smul_smul, show (3 : ℂ)⁻¹ * 3 = 1 by norm_num, one_smul]
  have hesum : gwE1 A + gwE2 A + gwE3 A = 1 := by
    have hp : gwE A (gu1 + gu2 + gu3) = (3 : ℂ) • (1 : Module.End ℂ V) := by
      rw [pidS, map_add, gwE_kill A (gW ^ 2 + gW + 1) (X + X ^ 2) hEW, add_zero, hE3]
    rw [map_add, map_add] at hp
    rw [gwE1, gwE2, gwE3, ← smul_add, ← smul_add, hp, smul_smul,
        show (3 : ℂ)⁻¹ * 3 = 1 by norm_num, one_smul]
  have hBsq : B * B = 1 := by rw [← sq, hB]
  have hB1 : B * A = A ^ 2 * B := by
    calc B * A = B * A * (B * B) := by rw [hBsq, mul_one]
      _ = (B * A * B) * B := by noncomm_ring
      _ = (A * A) * B := by rw [hBA]
      _ = A ^ 2 * B := by rw [sq]
  have hA4 : A ^ 4 = A := by rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hA, one_mul]
  have hB2 : B * A ^ 2 = A ^ 4 * B := by
    calc B * A ^ 2 = (B * A) * A := by rw [sq, mul_assoc]
      _ = (A ^ 2 * B) * A := by rw [hB1]
      _ = A ^ 2 * (B * A) := by noncomm_ring
      _ = A ^ 2 * (A ^ 2 * B) := by rw [hB1]
      _ = A ^ 4 * B := by rw [← mul_assoc, ← pow_add]
  have hA2sq : B * A ^ 2 * B = A ^ 4 := by rw [hB2, mul_assoc, hBsq, mul_one]
  have hBgu1 : B * gwE A gu1 * B = gwE A gu1 := by
    rw [gwE_gu1 A]
    calc B * (1 + A + A ^ 2) * B = B * B + B * A * B + B * A ^ 2 * B := by noncomm_ring
      _ = 1 + A ^ 2 + A ^ 4 := by rw [hBsq, hBA, ← sq, hA2sq]
      _ = 1 + A + A ^ 2 := by rw [hA4]; abel
  have hBgu2 : B * gwE A gu2 * B = gwE A gu3 := by
    rw [gwE_gu2 A, gwE_gu3 A]
    have key : B * (1 + gwOm ^ 2 • A + gwOm • A ^ 2) * B
        = B * B + gwOm ^ 2 • (B * A * B) + gwOm • (B * A ^ 2 * B) := by
      rw [mul_add, mul_add, add_mul, add_mul]
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_one]
    rw [key, hBsq, hBA, ← sq, hA2sq, hA4]
    abel
  have hBe1 : B * gwE1 A * B = gwE1 A := by
    rw [gwE1, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hBgu1]
  have hBe2 : B * gwE2 A * B = gwE3 A := by
    rw [gwE2, gwE3, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hBgu2]
  set na : ℕ := Module.finrank ℂ (LinearMap.range (gwE1 A)) with hna
  set nb : ℕ := Module.finrank ℂ (LinearMap.range (gwE2 A)) with hnb
  set nc : ℕ := Module.finrank ℂ (LinearMap.range (gwE3 A)) with hnc
  have ht1 : LinearMap.trace ℂ V (gwE1 A) = (na : ℂ) := by
    rw [hna]; exact (LinearMap.IsIdempotentElem.isProj_range (gwE1 A) he1e1).trace
  have ht2 : LinearMap.trace ℂ V (gwE2 A) = (nb : ℂ) := by
    rw [hnb]; exact (LinearMap.IsIdempotentElem.isProj_range (gwE2 A) he2e2).trace
  have ht3 : LinearMap.trace ℂ V (gwE3 A) = (nc : ℂ) := by
    rw [hnc]; exact (LinearMap.IsIdempotentElem.isProj_range (gwE3 A) he3e3).trace
  have hsum3 : na + nb + nc = 6 := by
    have h : (na : ℂ) + (nb : ℂ) + (nc : ℂ) = 6 := by
      rw [← ht1, ← ht2, ← ht3, ← map_add, ← map_add, hesum, LinearMap.trace_one, hdim]; norm_num
    exact_mod_cast h
  have hnb_nc : nb = nc := by
    have h : LinearMap.trace ℂ V (gwE3 A) = LinearMap.trace ℂ V (gwE2 A) := by
      rw [← hBe2, LinearMap.trace_mul_comm, ← mul_assoc, hBsq, one_mul]
    rw [ht3, ht2] at h
    exact_mod_cast h.symm
  have hBe2' : B * gwE2 A = gwE3 A * B := by
    calc B * gwE2 A = B * gwE2 A * (B * B) := by rw [hBsq, mul_one]
      _ = (B * gwE2 A * B) * B := by noncomm_ring
      _ = gwE3 A * B := by rw [hBe2]
  have htrBe2 : LinearMap.trace ℂ V (B * gwE2 A) = 0 := by
    have hnil : IsNilpotent (B * gwE2 A) := ⟨2, by
      rw [sq, show (B * gwE2 A) * (B * gwE2 A) = (B * gwE2 A * B) * gwE2 A by noncomm_ring,
        hBe2, he3e2]⟩
    exact (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  have hBe3' : B * gwE3 A = gwE2 A * B := by
    rw [← hBe2, show B * (B * gwE2 A * B) = (B * B) * gwE2 A * B by noncomm_ring, hBsq, one_mul]
  have htrBe3 : LinearMap.trace ℂ V (B * gwE3 A) = 0 := by
    rw [hBe3', LinearMap.trace_mul_comm, htrBe2]
  have htrBe1 : LinearMap.trace ℂ V (B * gwE1 A) = 2 := by
    have hBAeq : LinearMap.trace ℂ V (B * A) = LinearMap.trace ℂ V (B * gwE1 A) := by
      have h1 : B * A = B * gwE1 A + gwOm • (B * gwE2 A) + gwOm ^ 2 • (B * gwE3 A) := by
        conv_lhs => rw [heA.symm]
        rw [mul_add, mul_add]; simp only [Algebra.mul_smul_comm]
      rw [h1]; simp only [map_add, map_smul, smul_eq_mul, htrBe2, htrBe3, mul_zero, add_zero]
    rw [← hBAeq]; exact htrBA
  have he1ne0 : gwE1 A ≠ 0 := by
    intro h
    rw [h, mul_zero] at htrBe1
    simp at htrBe1
  have hna_ge : 1 ≤ na := by
    by_contra h
    have h0 : na = 0 := by omega
    have h1 : LinearMap.trace ℂ V (gwE1 A) = 0 := by rw [ht1, h0]; simp
    exact he1ne0 ((LinearMap.IsIdempotentElem.trace_eq_zero_iff he1e1).mp h1)
  have hcA : Cc * A = A * Cc := hAC.symm
  have hec2 : Cc * gwE2 A = gwE2 A * Cc := by
    rw [gwE2, gwE, Algebra.mul_smul_comm, gwCommuteAeval A Cc hcA gu2, Algebra.smul_mul_assoc]
  have hec3 : Cc * gwE3 A = gwE3 A * Cc := by
    rw [gwE3, gwE, Algebra.mul_smul_comm, gwCommuteAeval A Cc hcA gu3, Algebra.smul_mul_assoc]
  obtain ⟨m2, hm2⟩ := gwTraceInvIdem Cc (gwE2 A) hC he2e2 hec2
  obtain ⟨m3, hm3⟩ := gwTraceInvIdem Cc (gwE3 A) hC he3e3 hec3
  rw [← hnb] at hm2
  rw [← hnc] at hm3
  have heq1 : LinearMap.trace ℂ V (Cc * gwE1 A) + (2 * (m2 : ℂ) - (nb : ℂ))
      + (2 * (m3 : ℂ) - (nc : ℂ)) = 2 := by
    have h1 : Cc * gwE1 A + Cc * gwE2 A + Cc * gwE3 A = Cc := by
      rw [← mul_add, ← mul_add, hesum, mul_one]
    have h := congrArg (LinearMap.trace ℂ V) h1
    rw [map_add, map_add, hm2, hm3, htrC] at h
    exact h
  have heq2 : LinearMap.trace ℂ V (Cc * gwE1 A) + gwOm * (2 * (m2 : ℂ) - (nb : ℂ))
      + gwOm ^ 2 * (2 * (m3 : ℂ) - (nc : ℂ)) = -1 := by
    have h1 : Cc * gwE1 A + gwOm • (Cc * gwE2 A) + gwOm ^ 2 • (Cc * gwE3 A) = Cc * A := by
      conv_rhs => rw [heA.symm]
      rw [mul_add, mul_add]; simp only [Algebra.mul_smul_comm]
    have h := congrArg (LinearMap.trace ℂ V) h1
    simp only [map_add, map_smul, smul_eq_mul, hm2, hm3, htrCA] at h
    exact h
  set k2 : ℤ := 2 * (m2 : ℤ) - (nb : ℤ) with hk2def
  set k3 : ℤ := 2 * (m3 : ℤ) - (nc : ℤ) with hk3def
  have hK2 : 2 * (m2 : ℂ) - (nb : ℂ) = (k2 : ℂ) := by rw [hk2def]; push_cast; ring
  have hK3 : 2 * (m3 : ℂ) - (nc : ℂ) = (k3 : ℂ) := by rw [hk3def]; push_cast; ring
  rw [hK2, hK3] at heq1 heq2
  have hsub : (gwOm - 1) * (k2 : ℂ) + (gwOm ^ 2 - 1) * (k3 : ℂ) = -3 := by
    linear_combination heq2 - heq1
  have hz23 : k2 = k3 := by
    have hw : gwOm * ((k2 - k3 : ℤ) : ℂ) = ((k2 + 2 * k3 - 3 : ℤ) : ℂ) := by
      have hp := hsub
      rw [gwOm_sq_eq_neg] at hp
      push_cast
      linear_combination hp
    have := gwOm_mul_int (k2 - k3) (k2 + 2 * k3 - 3) hw
    omega
  have hk2_eq : k2 = 1 := by
    have h1 : (gwOm + gwOm ^ 2 - 2) * (k2 : ℂ) = -3 := by
      rw [← hz23] at hsub
      linear_combination hsub
    have h2 : (gwOm + gwOm ^ 2 - 2) = (-3 : ℂ) := by rw [gwOm_add_sq]; norm_num
    rw [h2] at h1
    have h3 : (k2 : ℂ) = 1 := by linear_combination (-1 / 3 : ℂ) * h1
    exact_mod_cast h3
  have hv : LinearMap.trace ℂ V (Cc * gwE2 A) = 1 := by rw [hm2, hK2, hk2_eq]; norm_num
  have hnb_odd : nb + 1 = 2 * m2 := by
    have h : (nb : ℂ) + 1 = 2 * (m2 : ℂ) := by rw [← hv, hm2]; ring
    exact_mod_cast h
  have hfin : na = 4 ∧ nb = 1 := by omega
  have htrA : LinearMap.trace ℂ V A = (na : ℂ) + gwOm * (nb : ℂ) + gwOm ^ 2 * (nb : ℂ) := by
    rw [heA.symm]
    simp only [map_add, map_smul, ht1, ht2, ht3, hnb_nc.symm, smul_eq_mul]
  rw [htrA, hfin.1, hfin.2]
  linear_combination gwOm_add_sq

end Work.A7REC.Char
