import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.Heart.Param
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.Unramified.Heart

open Polynomial

universe u

/-- The `j`-th coefficient of `v + s·t ∈ A[s][X]`: the constant `v.coeff j` plus `s · (t.coeff j)`. -/
theorem paramPoly_coeff {A : Type*} [CommRing A] (v t : Polynomial A) (j : ℕ) :
    (paramPoly v t).coeff j
      = Polynomial.C (v.coeff j) + Polynomial.X * Polynomial.C (t.coeff j) := by
  rw [paramPoly, Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_C_mul,
    Polynomial.coeff_map]

/-- **The `s`-linear coefficients of the `s`-parametrised norm operator vanish modulo `P`.**

Let `A` be a commutative domain and `P ∈ A` such that `A ⧸ (P)` is a domain, and let `q ≥ 2` be a
power of the residue characteristic (`IsFrobeniusPower P q`).  For the `s`-parametrised norm operator

`paramNormOp P q v t = Res_X(f(X) - Y, v(X) + s·t(X)) ∈ (A[s])[Y]`,   `f = LTpoly P q = P·X + X^q`,

the **linear term in `s`** of every `Y`-coefficient is divisible by `P`:

`[s] (paramNormOp P q v t).coeff j ∈ (P)`.

Proof.  Base change to the residue ring `B = A ⧸ (P)` along `φ : A →+* B` and use `map_paramNormOp`:
the image of `paramNormOp P q v t` is `Res_X(X^q - Y, v̄(X) + s·t̄(X))` in `(B[s])[Y]`.  The
Frobenius resultant formula (`resultant_X_pow_sub_C_X'`, applied over `B[s]`) turns this into
`∑_j C((v̄ + s·t̄).coeff j ^ q) Y^j`; by `add_pow_char_pow` and `q = p^k` the `j`-th coefficient is
`v̄_j ^ q + s^q·(t̄_j)^q`, whose linear `s`-coefficient vanishes because `q ≥ 2`.  Hence the
`s`-coefficient lies in the kernel of `φ`, i.e. in `(P)`. -/
theorem paramNormOp_sCoeff {A : Type u} [CommRing A] [IsDomain A] (P : A)
    [IsDomain (A ⧸ Ideal.span ({P} : Set A))] (q : ℕ) (hq : 2 ≤ q)
    (hpow : NK.LocalReciprocityLubinTate.IsFrobeniusPower P q) (v t : Polynomial A) :
    ∀ j, ((NK.LocalReciprocityLubinTate.Unramified.Heart.paramNormOp P q v t).coeff j).coeff 1
      ∈ Ideal.span ({P} : Set A) := by
  intro j
  set I := Ideal.span ({P} : Set A) with hI
  haveI : IsDomain (A ⧸ I) := by rw [hI]; infer_instance
  set φ : A →+* (A ⧸ I) := Ideal.Quotient.mk I with hφ
  obtain ⟨p, hp, hchar, k, hqk⟩ := hpow
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (A ⧸ I) p := hchar
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hφ, ← Polynomial.coeff_map]
  set hh : Polynomial (Polynomial (A ⧸ I)) :=
    Polynomial.map (Polynomial.mapRingHom φ) (paramPoly v t) with hhh
  -- the first argument of the resultant reduces to `X ^ q - C Y`
  have hA1 : (Polynomial.map Polynomial.C (Polynomial.map (Polynomial.mapRingHom φ)
        (Polynomial.map Polynomial.C (NK.LocalReciprocityLubinTate.LTpoly P q)))
      - Polynomial.C (Polynomial.X : Polynomial (Polynomial (A ⧸ I))))
      = Polynomial.X ^ q - Polynomial.C (Polynomial.X : Polynomial (Polynomial (A ⧸ I))) := by
    congr 1
    have h1 : ((NK.LocalReciprocityLubinTate.LTpoly P q).map Polynomial.C).map
          (Polynomial.mapRingHom φ)
        = ((NK.LocalReciprocityLubinTate.LTpoly P q).map φ).map Polynomial.C := by
      rw [Polynomial.map_map, Polynomial.map_map]
      congr 1
      ext a
      simp [RingHom.comp_apply]
    rw [show Polynomial.map Polynomial.C (Polynomial.map (Polynomial.mapRingHom φ)
          (Polynomial.map Polynomial.C (NK.LocalReciprocityLubinTate.LTpoly P q)))
        = (((NK.LocalReciprocityLubinTate.LTpoly P q).map Polynomial.C).map
            (Polynomial.mapRingHom φ)).map Polynomial.C from rfl,
      h1, NK.LocalReciprocityLubinTate.Unramified.LTpoly_map_quotient]
    simp only [Polynomial.map_pow, Polynomial.map_X]
  -- the Frobenius resultant formula over the residue ring
  have hres := NK.LocalReciprocityLubinTate.Unramified.resultant_X_pow_sub_C_X'
    (A := Polynomial (A ⧸ I)) (p := p) (q := q) (k := k) hqk hh
    (n := (paramPoly v t).natDegree) Polynomial.natDegree_map_le
  have hG' : Polynomial.map (Polynomial.mapRingHom φ)
        (NK.LocalReciprocityLubinTate.Unramified.Heart.paramNormOp P q v t)
      = ∑ i ∈ hh.support, Polynomial.C (hh.coeff i ^ q) * Polynomial.X ^ i := by
    rw [map_paramNormOp, hA1]
    exact hres
  have e1 : Polynomial.map φ
        ((NK.LocalReciprocityLubinTate.Unramified.Heart.paramNormOp P q v t).coeff j)
      = (Polynomial.map (Polynomial.mapRingHom φ)
          (NK.LocalReciprocityLubinTate.Unramified.Heart.paramNormOp P q v t)).coeff j := by
    rw [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
  rw [e1, hG', coeff_sum_C_pow_mul_X_pow hh (by omega) j]
  -- the `j`-th coefficient of `hh` is `C (v̄_j) + s · C (t̄_j)`
  have hh_coeff : hh.coeff j
      = Polynomial.C (φ (v.coeff j)) + Polynomial.X * Polynomial.C (φ (t.coeff j)) := by
    rw [hhh, Polynomial.coeff_map, Polynomial.coe_mapRingHom, paramPoly_coeff]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
  rw [hh_coeff, coeff_one_pow_C_add_X_mul hqk hq]

end NK.LocalReciprocityLubinTate.Unramified.Heart
