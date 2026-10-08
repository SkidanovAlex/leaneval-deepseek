/-
# The conjugation and the norm of the quadratic extension `L = K[α]`

App. VIII Prop. 3 identifies `K × K`, with the squaring form `q(a,b) = a² + εab + b²` of
`B(n,1,ε)`, with the quadratic field `L = K[α]`, `α² = εα + 1`; under this identification `q`
becomes the norm `x ↦ x · x^{|K|}` of `L/K`.  This file proves the two inputs:

* `qalpha_pow_natCard : α ^ |K| = α + ε` — i.e. the `|K|`-power map is the nontrivial element of
  `Gal(L/K)` (the conjugation), expressed through `α ↦ α + ε`;
* `normRepr : (a + bα) · (a + bα)^{|K|} = a² + εab + b²`.
-/
import Mathlib
import Submission.Work.Hering.AppVIII.QuadExt

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial Module

namespace Work.Hering.AppVIII

variable (K : Type*) [Field K] [CharP K 2] [Finite K]

/-- `L` is nontrivial (used to state its characteristic). -/
theorem quadExt_nontrivial (ε : K) : Nontrivial (QuadExt K ε) := by
  refine AdjoinRoot.nontrivial (quadPoly K ε) ?_
  rw [Polynomial.degree_eq_natDegree (quadPoly_ne_zero K ε), quadPoly_natDegree]
  norm_num

/-- `L` has characteristic two (proved without using that `L` is a field). -/
theorem quadExt_charP (ε : K) : CharP (QuadExt K ε) 2 := by
  haveI := quadExt_nontrivial K ε
  refine CharTwo.of_one_ne_zero_of_two_eq_zero (R := QuadExt K ε) one_ne_zero ?_
  show (2 : QuadExt K ε) = 0
  rw [show (2 : QuadExt K ε) = 2 * 1 from (mul_one 2).symm, two_mul]
  exact quadExt_add_self K ε 1

instance instCharPQuadExt (ε : K) : CharP (QuadExt K ε) 2 := quadExt_charP K ε

instance instModuleFiniteQuadExt (ε : K) : Module.Finite K (QuadExt K ε) :=
  @Finite.of_basis K (QuadExt K ε) (Fin (AdjoinRoot.powerBasis (quadPoly_ne_zero K ε)).dim)
    _ _ _ _ (AdjoinRoot.powerBasis (quadPoly_ne_zero K ε)).basis

instance instFiniteQuadExt (ε : K) [Fact (Irreducible (quadPoly K ε))] : Finite (QuadExt K ε) :=
  Module.finite_of_finite K

/-- The `K`-dimension of the quadratic extension is `2`. -/
theorem quadExt_finrank (ε : K) [Fact (Irreducible (quadPoly K ε))] :
    Module.finrank K (QuadExt K ε) = 2 := by
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis (quadPoly_ne_zero K ε)),
    AdjoinRoot.powerBasis_dim (quadPoly_ne_zero K ε), quadPoly_natDegree]

/-- **The conjugation of `L/K` is the `|K|`-th power map**, i.e. `α ^ |K| = α + ε`. -/
theorem qalpha_pow_natCard {ε : K} [Fact (Irreducible (quadPoly K ε))] (h : Anisotropic K ε) :
    qalpha K ε ^ Nat.card K = qalpha K ε + algebraMap K (QuadExt K ε) ε := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Algebra.IsAlgebraic K (QuadExt K ε) := Algebra.IsAlgebraic.of_finite K _
  set σ : QuadExt K ε ≃ₐ[K] QuadExt K ε :=
    FiniteField.frobeniusAlgEquivOfAlgebraic K (QuadExt K ε) with hσ
  have hσcoe : ∀ x : QuadExt K ε, σ x = x ^ Fintype.card K := fun x =>
    congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic K (QuadExt K ε)) x
  have hσne : σ ≠ 1 := by
    intro h1
    have hord := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic K (QuadExt K ε)
    rw [← hσ, h1, orderOf_one, quadExt_finrank K ε] at hord
    exact absurd hord (by norm_num)
  set X := qalpha K ε with hX
  set E := algebraMap K (QuadExt K ε) ε with hE
  have hroot : σ X * σ X = E * σ X + 1 := by
    have h1 := congrArg (fun x => σ x) (qalpha_sq K ε)
    simp only [map_mul, map_add, map_one, AlgEquiv.commutes] at h1
    simpa only [← hX, ← hE] using h1
  have hXs : X * X = E * X + 1 := by rw [hX, hE]; exact qalpha_sq K ε
  have h2 : (2 : QuadExt K ε) = 0 := CharP.cast_eq_zero _ 2
  have h4 : (4 : QuadExt K ε) = 0 := by
    rw [show (4 : QuadExt K ε) = 2 * 2 by norm_num, h2, zero_mul]
  have hfac : (σ X + X) * (σ X + (X + E)) = 0 := by
    have hexp : (σ X + X) * (σ X + (X + E))
        = (σ X * σ X + E * σ X + 1) + (X * X + E * X + 1) := by
      ring_nf
      simp only [h2, h4, mul_zero, add_zero, zero_add]
    rw [hexp, hroot, hXs]
    ring_nf
    simp only [h2, h4, mul_zero, add_zero, zero_add]
  have hcases : σ X = X ∨ σ X = X + E := by
    rcases mul_eq_zero.mp hfac with h1 | h1
    · left
      exact add_right_cancel (h1.trans (CharTwo.add_self_eq_zero X).symm)
    · right
      exact add_right_cancel (h1.trans (CharTwo.add_self_eq_zero (X + E)).symm)
  have hσeqone : σ X = X → σ = 1 := by
    intro hα
    have h2 : σ.toAlgHom = (1 : QuadExt K ε →ₐ[K] QuadExt K ε) := by
      refine AdjoinRoot.algHom_ext (f := quadPoly K ε) (h := ?_)
      show σ X = (1 : QuadExt K ε →ₐ[K] QuadExt K ε) X
      rw [AlgHom.one_apply]
      exact hα
    refine AlgEquiv.ext fun x => ?_
    exact DFunLike.congr_fun h2 x
  rcases hcases with hcase | hcase
  · exact absurd (hσeqone hcase) hσne
  · calc qalpha K ε ^ Nat.card K = X ^ Nat.card K := by rw [hX]
      _ = X ^ Fintype.card K := by rw [Nat.card_eq_fintype_card]
      _ = σ X := (hσcoe X).symm
      _ = X + E := hcase
      _ = qalpha K ε + algebraMap K (QuadExt K ε) ε := by rw [hX, hE]

/-- The norm computation: `(a + bα) · (a + bα)^{|K|} = a² + εab + b²`. -/
theorem normRepr {ε : K} [Fact (Irreducible (quadPoly K ε))] (h : Anisotropic K ε) (a b : K) :
    (algebraMap K (QuadExt K ε) a + algebraMap K (QuadExt K ε) b * qalpha K ε)
        * (algebraMap K (QuadExt K ε) a + algebraMap K (QuadExt K ε) b * qalpha K ε) ^ (Nat.card K)
      = algebraMap K (QuadExt K ε) (a * a + ε * (a * b) + b * b) := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hn' : Fintype.card K = 2 ^ (n : ℕ) := hn
  have hcard : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn']
  set X := qalpha K ε with hX
  set A := algebraMap K (QuadExt K ε) a with hA
  set B := algebraMap K (QuadExt K ε) b with hB
  set E := algebraMap K (QuadExt K ε) ε with hE
  have ha : a ^ 2 ^ (n : ℕ) = a := by rw [← hn']; exact FiniteField.pow_card a
  have hb : b ^ 2 ^ (n : ℕ) = b := by rw [← hn']; exact FiniteField.pow_card b
  have hx : X ^ 2 ^ (n : ℕ) = X + E := by
    rw [hX, hE, ← hcard]
    exact qalpha_pow_natCard K h
  have hpow : (A + B * X) ^ (Nat.card K) = A + B * (X + E) := by
    rw [hcard, add_pow_char_pow (p := 2) (n := (n : ℕ)), mul_pow]
    rw [← map_pow (algebraMap K (QuadExt K ε)) a, ← map_pow (algebraMap K (QuadExt K ε)) b]
    rw [hA, hB, ha, hb, hx]
  have h2 : (2 : QuadExt K ε) = 0 := CharP.cast_eq_zero _ 2
  have h4 : (4 : QuadExt K ε) = 0 := by
    rw [show (4 : QuadExt K ε) = 2 * 2 by norm_num, h2, zero_mul]
  have hαα : X * (X + E) = 1 := by
    rw [hX, hE, mul_add, qalpha_sq K ε, mul_comm (algebraMap K (QuadExt K ε) ε) (qalpha K ε)]
    ring_nf
    simp only [h2, h4, mul_zero, add_zero, zero_add]
  rw [hpow]
  have h1 : A * (B * (X + E)) = algebraMap K (QuadExt K ε) (a * b) * (X + E) := by
    calc A * (B * (X + E)) = (A * B) * (X + E) := by ring
      _ = algebraMap K (QuadExt K ε) (a * b) * (X + E) := by
            rw [hA, hB, ← map_mul (algebraMap K (QuadExt K ε)) a b]
  have h2' : (B * X) * A = algebraMap K (QuadExt K ε) (a * b) * X := by
    calc (B * X) * A = (B * A) * X := by ring
      _ = algebraMap K (QuadExt K ε) (b * a) * X := by
            rw [hB, hA, ← map_mul (algebraMap K (QuadExt K ε)) b a]
      _ = algebraMap K (QuadExt K ε) (a * b) * X := by rw [mul_comm b a]
  have h3 : (B * X) * (B * (X + E)) = algebraMap K (QuadExt K ε) (b * b) := by
    calc (B * X) * (B * (X + E)) = (B * B) * (X * (X + E)) := by ring
      _ = (B * B) * 1 := by rw [hαα]
      _ = algebraMap K (QuadExt K ε) (b * b) := by
            rw [mul_one, hB, ← map_mul (algebraMap K (QuadExt K ε)) b b]
  have hXEX : X + E + X = E := by
    rw [show X + E + X = (X + X) + E by abel, CharTwo.add_self_eq_zero, zero_add]
  have hstep : algebraMap K (QuadExt K ε) (a * b) * (X + E)
      + algebraMap K (QuadExt K ε) (a * b) * X
      = E * (A * B) := by
    calc algebraMap K (QuadExt K ε) (a * b) * (X + E)
          + algebraMap K (QuadExt K ε) (a * b) * X
        = algebraMap K (QuadExt K ε) (a * b) * (X + E + X) := by ring
      _ = algebraMap K (QuadExt K ε) (a * b) * E := by rw [hXEX]
      _ = E * (A * B) := by
            rw [hE, hA, hB, ← map_mul (algebraMap K (QuadExt K ε)) a b]
            ring
  calc (A + B * X) * (A + B * (X + E))
      = A * A + (A * (B * (X + E)) + (B * X) * A) + (B * X) * (B * (X + E)) := by ring
    _ = A * A + (algebraMap K (QuadExt K ε) (a * b) * (X + E)
          + algebraMap K (QuadExt K ε) (a * b) * X)
          + algebraMap K (QuadExt K ε) (b * b) := by rw [h1, h2', h3]
    _ = A * A + E * (A * B) + algebraMap K (QuadExt K ε) (b * b) := by rw [hstep]
    _ = algebraMap K (QuadExt K ε) (a * a + ε * (a * b) + b * b) := by
        rw [hA, hB, hE, ← map_mul (algebraMap K (QuadExt K ε)) a a,
          ← map_mul (algebraMap K (QuadExt K ε)) a b,
          ← map_mul (algebraMap K (QuadExt K ε)) ε (a * b),
          ← map_add (algebraMap K (QuadExt K ε)), ← map_add (algebraMap K (QuadExt K ε))]

end Work.Hering.AppVIII
