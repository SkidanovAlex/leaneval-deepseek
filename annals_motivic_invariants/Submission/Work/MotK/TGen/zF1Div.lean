import Mathlib
import Submission.Work.MotK.TGen.RadSatDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

/-- The algebra equivalence `finSuccEquiv` turns `rename zEmb` (adjoining the `X 1`, `X 2` variables)
into the constant-coefficient inclusion.

NOTE (2026-10-05): this lemma must stay **public**: `Submission/Work/MotK/TGen/zA_cancel_zg.lean`
(the `zA`-regularity route `ZRingIsDomainAll`) imports this module and uses it to rewrite
`finSuccEquiv (zg)`. -/
theorem finSuccEquiv_rename_zEmb {K : Type} [Field K] (p : MvPolynomial (Fin 2) K) :
    MvPolynomial.finSuccEquiv K 2 (MvPolynomial.rename zEmb p) = Polynomial.C p := by
  have hz : zEmb = Fin.succ := by funext i; fin_cases i <;> rfl
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [MvPolynomial.rename_C, MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
      rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      have h1 : MvPolynomial.rename zEmb (p * MvPolynomial.X i)
          = MvPolynomial.rename zEmb p * MvPolynomial.X (zEmb i) := by
        rw [map_mul, MvPolynomial.rename_X]
      rw [h1]
      simp only [map_mul]
      rw [hp]
      have hXi : MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X (zEmb i))
          = Polynomial.C (MvPolynomial.X i) := by
        rw [hz]; exact MvPolynomial.finSuccEquiv_X_succ
      rw [hXi, ← Polynomial.C_mul]

theorem zF1Div (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    ∀ f : MvPolynomial (Fin 3) K, ∃ f₀ f₁ : MvPolynomial (Fin 2) K, ∃ q : MvPolynomial (Fin 3) K,
      f = MvPolynomial.rename Work.MotK.TGen.zEmb f₀
            + MvPolynomial.rename Work.MotK.TGen.zEmb f₁ * MvPolynomial.X 0
            + q * Work.MotK.TGen.zF1 K a b h := by
  intro f
  -- `zF1` is quadratic in `X 0` with leading coefficient `a^2 b^4 h`, a unit.
  have hc : a^2*b^4*h ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb)) hh
  -- the coefficient polynomials, as elements of `K[X1,X2]`
  set A2 : MvPolynomial (Fin 2) K := MvPolynomial.C (a^2*b^4*h) with hA2
  set B2 : MvPolynomial (Fin 2) K := MvPolynomial.C (-(a^6*h)) * (MvPolynomial.X 1)^3 with hB2
  set G2 : MvPolynomial (Fin 2) K :=
    MvPolynomial.C (a^4*b^2*h) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1)^2
      + MvPolynomial.C (a*b^5*h) * (MvPolynomial.X 0)^3 - MvPolynomial.C (a^5*b + b^6) * MvPolynomial.X 1
    with hG2
  set cinv : MvPolynomial (Fin 2) K := MvPolynomial.C ((a^2*b^4*h)⁻¹) with hcinv
  -- view everything as a polynomial in `X 0` over `K[X1,X2]`
  set F : Polynomial (MvPolynomial (Fin 2) K) := MvPolynomial.finSuccEquiv K 2 f with hF
  set g : Polynomial (MvPolynomial (Fin 2) K) := MvPolynomial.finSuccEquiv K 2 (zF1 K a b h) with hg
  have hzAl : zAl K a b h = MvPolynomial.rename zEmb A2 := by
    rw [hA2, zAl]; simp only [MvPolynomial.rename_C]
  have hzBet : zBet K a b h = MvPolynomial.rename zEmb B2 := by
    rw [hB2, zBet]
    simp only [map_mul, map_pow, MvPolynomial.rename_X, MvPolynomial.rename_C]
    rw [show zEmb 1 = 2 from rfl]
  have hzGam : zGam K a b h = MvPolynomial.rename zEmb G2 := by
    rw [hG2, zGam]
    simp only [map_add, map_mul, map_pow, map_sub, MvPolynomial.rename_X, MvPolynomial.rename_C]
    rw [show zEmb 0 = 1 from rfl, show zEmb 1 = 2 from rfl]
  -- the image of `zF1` under `finSuccEquiv`
  have hg_eq : g = Polynomial.C A2 * Polynomial.X^2 + Polynomial.C B2 * Polynomial.X + Polynomial.C G2 := by
    rw [hg, zF1, hzAl, hzBet, hzGam]
    simp only [map_add, map_mul, map_pow, finSuccEquiv_rename_zEmb, MvPolynomial.finSuccEquiv_X_zero]
  have hA2cinv : A2 * cinv = 1 := by
    rw [hA2, hcinv, ← MvPolynomial.C_mul, mul_inv_cancel₀ hc, MvPolynomial.C_1]
  have h1 : A2 * (cinv * B2) = B2 := by rw [← mul_assoc, hA2cinv, one_mul]
  have h2 : A2 * (cinv * G2) = G2 := by rw [← mul_assoc, hA2cinv, one_mul]
  -- a monic polynomial of degree two, a unit multiple of `g`
  set m : Polynomial (MvPolynomial (Fin 2) K) :=
    Polynomial.X^2 + (Polynomial.C (cinv * B2) * Polynomial.X + Polynomial.C (cinv * G2)) with hm
  have hCm : Polynomial.C A2 * m = g := by
    rw [hm, hg_eq, mul_add, mul_add, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul, h1, h2]
    first | refl_ring1 | ring
  have hdegp : (Polynomial.C (cinv * B2) * Polynomial.X + Polynomial.C (cinv * G2)).degree
      < (2 : WithBot ℕ) := by
    have h1' : (Polynomial.C (cinv * B2) * Polynomial.X).degree ≤ 1 := Polynomial.degree_C_mul_X_le _
    have h0 : (Polynomial.C (cinv * G2)).degree ≤ 0 := Polynomial.degree_C_le
    calc (Polynomial.C (cinv * B2) * Polynomial.X + Polynomial.C (cinv * G2)).degree
        ≤ max (Polynomial.C (cinv * B2) * Polynomial.X).degree
            (Polynomial.C (cinv * G2)).degree := Polynomial.degree_add_le _ _
      _ ≤ max 1 0 := max_le_max h1' h0
      _ = 1 := by norm_num
      _ < 2 := by norm_num
  have hm_monic : m.Monic := by rw [hm]; exact Polynomial.monic_X_pow_add hdegp
  have hdegm : m.degree = (2 : WithBot ℕ) := by
    rw [hm, Polynomial.degree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow])]
    exact Polynomial.degree_X_pow 2
  -- divide `F` by `m`
  set R : Polynomial (MvPolynomial (Fin 2) K) := F %ₘ m with hR
  set Q : Polynomial (MvPolynomial (Fin 2) K) := F /ₘ m with hQ
  have hFR : F = R + m * Q := by rw [hR, hQ]; exact (Polynomial.modByMonic_add_div F m).symm
  have hRdeg : R.degree < (2 : WithBot ℕ) := by
    rw [hR, ← hdegm]; exact Polynomial.degree_modByMonic_lt F hm_monic
  have hRcoeff : ∀ k, 2 ≤ k → R.coeff k = 0 := (Polynomial.degree_lt_iff_coeff_zero R 2).mp hRdeg
  set r0 : MvPolynomial (Fin 2) K := R.coeff 0 with hr0
  set r1 : MvPolynomial (Fin 2) K := R.coeff 1 with hr1
  have hRdecomp0 : R = Polynomial.C (R.coeff 0) + Polynomial.C (R.coeff 1) * Polynomial.X := by
    ext n
    rcases n with _ | _ | n
    · simp
    · simp
    · have hcoeff : R.coeff (n+2) = 0 := hRcoeff (n+2) (by omega)
      simp [hcoeff]
  have hRdecomp : R = Polynomial.C r0 + Polynomial.C r1 * Polynomial.X := by
    rw [← hr0, ← hr1] at hRdecomp0
    exact hRdecomp0
  have hm_eq : m = Polynomial.C cinv * g := by
    have h3 : Polynomial.C cinv * Polynomial.C A2 = 1 := by
      rw [← Polynomial.C_mul, show cinv * A2 = 1 from by rw [mul_comm, hA2cinv], Polynomial.C_1]
    calc m = (Polynomial.C cinv * Polynomial.C A2) * m := by rw [h3, one_mul]
      _ = Polynomial.C cinv * (Polynomial.C A2 * m) := by rw [mul_assoc]
      _ = Polynomial.C cinv * g := by rw [hCm]
  have hFm : F = R + Q * Polynomial.C cinv * g := by
    rw [hFR, hm_eq]
    first | refl_ring1 | ring
  have hFinal : F = Polynomial.C r0 + Polynomial.C r1 * Polynomial.X + (Q * Polynomial.C cinv) * g := by
    rw [hFm, hRdecomp]
  -- assemble
  refine ⟨r0, r1, (MvPolynomial.finSuccEquiv K 2).symm (Q * Polynomial.C cinv), ?_⟩
  apply (MvPolynomial.finSuccEquiv K 2).injective
  rw [← hF]
  simp only [map_add, map_mul, ← hg, finSuccEquiv_rename_zEmb, MvPolynomial.finSuccEquiv_X_zero,
    AlgEquiv.apply_symm_apply]
  exact hFinal

end Work.MotK.TGen
