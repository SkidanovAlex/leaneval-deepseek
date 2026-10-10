import Mathlib
import Submission.Work.MotK.TwCensus.ZTwist
import Submission.Work.MotK.TwCensus.GoodDiscNe
import Submission.Work.MotV.Defs
import Submission.Work.MotK.TGen.ZElim2Defs
import Submission.Work.MotK.TGen.ZElim2Case14
import Submission.Work.MotK.TGen.ZElim2Case23
import Submission.Work.MotK.TGen.ZElim2Struct
import Submission.Work.MotK.TGen.ZElim2Reduce

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ZElim2Irreducible`

`Irreducible (ZElim2 D.a D.b h)` for a `Good` Klein datum `D` and `h ≠ 0`.

The proof is the one described in the header of `ZElim2Defs`:

* `ZElim2Reduce`: after the diagonal substitution `(X0,X1) ↦ (w²X0, wX1)`, `w^5 = h`, in the
  algebraic closure, `ZElim2 a b h` becomes `a^8 · g0p (b/a)`; hence irreducibility of
  `g0p (b/a)` over `K̄` implies irreducibility of `ZElim2 a b h` over `K`.
* `ZElim2Struct`: a factorization of `g0p r` over a field `L` of characteristic `≠ 5` is either of
  the `(2,3)` shape `Q23 * C23` or of the `(1,4)` shape `(rX - ηY + τ) * q` with `η^5 = 1`.
* `ZElim2Case23`, `ZElim2Case14`: neither shape can occur when `1 - 11r^5 - r^10 ≠ 0`, which holds
  for `r = b/a` because `GoodDiscNe` gives `a^10 - 11a^5b^5 - b^10 ≠ 0`.
-/

set_option autoImplicit false

namespace Work.MotK.TGen

open MvPolynomial

/-- Elements of the algebraic closure are algebraic, hence `K` is a tower: the natural map
`K → AlgebraicClosure K` is injective, so `5 ≠ 0` transfers. -/
private theorem five_ne_zero_closure (K : Type) [Field K] (hk : ringChar K ≠ 5) :
    (5 : AlgebraicClosure K) ≠ 0 := by
  intro h
  have h5K : (5 : K) = 0 := by
    have key : (algebraMap K (AlgebraicClosure K)) (5 : K) = 0 := by
      change (algebraMap K (AlgebraicClosure K)) ((5 : ℕ) : K) = 0
      rw [map_natCast]
      exact h
    exact (FaithfulSMul.algebraMap_eq_zero_iff K (AlgebraicClosure K)).mp key
  have hdvd : ringChar K ∣ 5 := (ringChar.spec (R := K) 5).1 h5K
  rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h1 | h5
  · exact CharP.ringChar_ne_one h1
  · exact hk h5

/-- The main theorem. -/
theorem ZElim2Irreducible (K : Type) [Field K] [Infinite K] (hk : ringChar K ≠ 5)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) :
    Irreducible (Work.MotK.TwCensus.ZElim2 D.a D.b h) := by
  have ha : D.a ≠ 0 := fun h0 => hD.ab_ne (by rw [h0, zero_mul])
  have hb : D.b ≠ 0 := fun h0 => hD.ab_ne (by rw [h0, mul_zero])
  -- work over the algebraic closure
  set L := AlgebraicClosure K with hL
  set r : L := algebraMap K L (D.b / D.a) with hr
  refine ZElim2Reduce K hk D.a D.b h ha hb hh ?_
  
  have h5 : (5 : L) ≠ 0 := five_ne_zero_closure K hk
  have hrne : r ≠ 0 := by
    rw [hr]
    refine (map_ne_zero_iff _ (algebraMap K L).injective).mpr ?_
    exact div_ne_zero hb ha
  have hdiscK : D.a ^ 10 - 11 * D.a ^ 5 * D.b ^ 5 - D.b ^ 10 ≠ 0 :=
    Work.MotK.TwCensus.GoodDiscNe K hk D hD
  -- transfer the discriminant to the closure at r = b/a
  have hdiscL : (algebraMap K L D.a) ^ 10
      - 11 * (algebraMap K L D.a) ^ 5 * (algebraMap K L D.b) ^ 5
      - (algebraMap K L D.b) ^ 10 ≠ 0 := by
    intro h0
    apply hdiscK
    have h1 : (algebraMap K L) (D.a ^ 10 - 11 * D.a ^ 5 * D.b ^ 5 - D.b ^ 10) = 0 := by
      simpa only [map_sub, map_mul, map_pow, map_ofNat] using h0
    exact (map_eq_zero_iff _ (algebraMap K L).injective).mp h1
  have hrpow : r = (algebraMap K L D.b) / (algebraMap K L D.a) := by
    rw [hr, map_div₀]
  have hdisc : 1 - 11 * r ^ 5 - r ^ 10 ≠ 0 := by
    intro h0
    apply hdiscL
    have haL : (algebraMap K L D.a) ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr ha
    have hpow : (algebraMap K L D.a) ^ 10 * (1 - 11 * r ^ 5 - r ^ 10)
        = (algebraMap K L D.a) ^ 10 - 11 * (algebraMap K L D.a) ^ 5
            * (algebraMap K L D.b) ^ 5 - (algebraMap K L D.b) ^ 10 := by
      have hra : r * algebraMap K L D.a = algebraMap K L D.b := by
        rw [hrpow, div_mul_cancel₀ _ haL]
      calc (algebraMap K L D.a) ^ 10 * (1 - 11 * r ^ 5 - r ^ 10)
          = (algebraMap K L D.a) ^ 10 - 11 * (algebraMap K L D.a) ^ 5
              * (r * algebraMap K L D.a) ^ 5 - (r * algebraMap K L D.a) ^ 10 := by ring
        _ = (algebraMap K L D.a) ^ 10 - 11 * (algebraMap K L D.a) ^ 5
              * (algebraMap K L D.b) ^ 5 - (algebraMap K L D.b) ^ 10 := by rw [hra]
    rw [h0, mul_zero] at hpow
    exact hpow.symm
  by_contra hred
  rcases ZElim2Struct L h5 r hrne hred with
    ⟨u1, u0, v2, v1, v0, hprod⟩ | ⟨η, τ, hη, q, hprod⟩
  · exact ZElim2Case23 L h5 r u1 u0 v2 v1 v0 hrne hdisc hprod
  · exact ZElim2Case14 L h5 r η τ hrne hη hdisc q hprod

end Work.MotK.TGen
