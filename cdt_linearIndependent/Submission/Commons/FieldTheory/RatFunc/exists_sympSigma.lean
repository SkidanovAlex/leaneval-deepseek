import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.RingTheory.RatFunc.iterate_deriv_algebraMap

namespace Commons.FieldTheory.RatFunc

open Polynomial

noncomputable section

local notation "Xr" => (RatFunc.X : RatFunc ℚ)

/-- The two `ℚ`-algebra structures on `ℚ(X)` (the one induced by the polynomial algebra structure
and the canonical one coming from the fact that `ℚ(X)` is a field of characteristic zero) agree,
because both have the same `algebraMap`. -/
private lemma instAlgebraOfPolynomial_eq_toRatAlgebra :
    (RatFunc.instAlgebraOfPolynomial ℚ ℚ) = DivisionRing.toRatAlgebra := by
  apply Algebra.algebra_ext
  intro r
  exact RingHom.congr_fun (RingHom.ext_rat _ _) r

/-- The Möbius involution `x ↦ x/(x−1)` of the projective line, as a `ℚ`-algebra automorphism of
`ℚ(X)` of order two.  (Concretely: lift the `ℚ`-algebra map `ℚ[X] → ℚ(X)`, `X ↦ X/(X−1)` along
`RatFunc.liftAlgHom`; it is injective, and since it is an involution it is bijective.) -/
theorem exists_sympSigma :
    ∃ σ : RatFunc ℚ ≃ₐ[ℚ] RatFunc ℚ,
      (∀ f : RatFunc ℚ, σ (σ f) = f) ∧
      σ (algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X)
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X
          / (algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X - 1) := by
  let t : RatFunc ℚ := Xr / (Xr - 1)
  -- Denominator facts
  have hX1 : Xr - 1 ≠ 0 := by
    have h : (Xr - 1 : RatFunc ℚ) = algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.X - 1) := by
      simp
    rw [h]
    exact RatFunc.algebraMap_ne_zero (by simpa using Polynomial.X_sub_C_ne_zero (1 : ℚ))
  have ht_ne_zero : t ≠ 0 := by
    rw [show t = Xr / (Xr - 1) from rfl]
    exact div_ne_zero RatFunc.X_ne_zero hX1
  -- `t` has numerator `X` and denominator `X - 1`, hence is not a constant
  have h_eq : t.num * (Polynomial.X - 1) = Polynomial.X * t.denom := by
    have ht : t = algebraMap ℚ[X] (RatFunc ℚ) Polynomial.X
        / algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.X - 1) := by
      simp [t]
    have hnd : algebraMap ℚ[X] (RatFunc ℚ) t.num / algebraMap ℚ[X] (RatFunc ℚ) t.denom
        = algebraMap ℚ[X] (RatFunc ℚ) Polynomial.X
          / algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.X - 1) := by
      rw [RatFunc.num_div_denom t, ht]
    have h' := mul_eq_mul_of_div_eq_div (algebraMap ℚ[X] (RatFunc ℚ) t.num)
      (algebraMap ℚ[X] (RatFunc ℚ) Polynomial.X)
      (RatFunc.algebraMap_ne_zero t.denom_ne_zero)
      (RatFunc.algebraMap_ne_zero (by simpa using Polynomial.X_sub_C_ne_zero (1 : ℚ))) hnd
    rw [← map_mul, ← map_mul] at h'
    exact RatFunc.algebraMap_injective ℚ h'
  have ht_ne_C : ¬ ∃ c, t = RatFunc.C c := by
    rintro ⟨c, hc⟩
    have hnum : t.num = Polynomial.C c := by rw [hc, RatFunc.num_C]
    have h0 : (t.num * (Polynomial.X - 1)).eval (0 : ℚ)
        = (Polynomial.X * t.denom).eval (0 : ℚ) := by
      rw [h_eq]
    rw [hnum] at h0
    simp at h0
    have hnum0 : t.num = 0 := by rw [hnum, h0]; simp
    have : t = 0 := by
      rw [← RatFunc.num_div_denom t, hnum0, map_zero, zero_div]
    exact ht_ne_zero this
  -- `t` is transcendental, so `aeval t` is injective
  have htr : Transcendental ℚ t := by
    have htrA : @Transcendental ℚ (RatFunc ℚ) _ _ (RatFunc.instAlgebraOfPolynomial ℚ ℚ) t :=
      RatFunc.transcendental_of_ne_C t ht_ne_C
    rwa [instAlgebraOfPolynomial_eq_toRatAlgebra] at htrA
  have hinj : Function.Injective (Polynomial.aeval t : ℚ[X] →ₐ[ℚ] RatFunc ℚ) :=
    transcendental_iff_injective.mp htr
  have hφ : nonZeroDivisors ℚ[X] ≤ (nonZeroDivisors (RatFunc ℚ)).comap (Polynomial.aeval t).toRingHom := by
    intro p hp
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    intro hzero
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hp) (hinj (by simpa using hzero))
  -- the ring endomorphism `X ↦ X/(X-1)`
  let σR : RatFunc ℚ →+* RatFunc ℚ := RatFunc.liftRingHom (Polynomial.aeval t).toRingHom hφ
  have hC : ∀ r : ℚ, algebraMap ℚ (RatFunc ℚ) r = RatFunc.C r :=
    fun r => RingHom.congr_fun (RingHom.ext_rat (algebraMap ℚ (RatFunc ℚ)) RatFunc.C) r
  have hσ_algR : ∀ p : ℚ[X], σR (algebraMap ℚ[X] (RatFunc ℚ) p) = (Polynomial.aeval t) p := by
    intro p
    change RatFunc.liftRingHom (Polynomial.aeval t).toRingHom hφ
      (algebraMap ℚ[X] (RatFunc ℚ) p) = (Polynomial.aeval t) p
    rw [RatFunc.liftRingHom_algebraMap]
    rfl
  -- upgrade to a `ℚ`-algebra homomorphism
  let σA : RatFunc ℚ →ₐ[ℚ] RatFunc ℚ :=
    { toRingHom := σR
      commutes' := by
        intro r
        rw [hC r]
        rw [show RatFunc.C r = algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.C r) from rfl]
        change σR (algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.C r))
            = algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.C r)
        rw [hσ_algR (Polynomial.C r), Polynomial.aeval_C, RatFunc.algebraMap_C]
        exact hC r }
  have hσ_alg : ∀ p : ℚ[X], σA (algebraMap ℚ[X] (RatFunc ℚ) p) = (Polynomial.aeval t) p :=
    fun p => hσ_algR p
  have hσx : σA Xr = t := by
    have := hσ_alg Polynomial.X
    simpa [t] using this
  -- field computation: `t/(t-1) = X`
  have ht1 : t - 1 = 1 / (Xr - 1) := by
    rw [show t = Xr / (Xr - 1) from rfl, div_sub_one hX1,
      show Xr - (Xr - 1) = 1 by ring]
  have ht_div : t / (t - 1) = Xr := by
    have htx : t * (Xr - 1) = Xr := by
      rw [show t = Xr / (Xr - 1) from rfl, div_mul_cancel₀ Xr hX1]
    have h1 : t / (t - 1) = t * (Xr - 1) := by
      rw [ht1, one_div, div_inv_eq_mul]
    rw [h1, htx]
  have hσt : σA t = Xr := by
    have h : σA (Xr / (Xr - 1)) = t / (t - 1) := by
      simp only [map_div₀, map_sub, map_one, hσx]
    rw [show t = Xr / (Xr - 1) from rfl, h, ht_div]
  have haevalX : ∀ p : ℚ[X], (Polynomial.aeval Xr) p = algebraMap ℚ[X] (RatFunc ℚ) p := by
    intro p
    have h := RatFunc.aeval_X_left_eq_algebraMap (K := ℚ) p
    rw [instAlgebraOfPolynomial_eq_toRatAlgebra] at h
    exact h
  -- `σA ∘ aeval t = aeval X`
  have hcomp : ∀ p : ℚ[X], σA ((Polynomial.aeval t) p) = (Polynomial.aeval Xr) p := by
    intro p
    have h2 : (Polynomial.aeval (σA t) : ℚ[X] →ₐ[ℚ] RatFunc ℚ) = Polynomial.aeval Xr := by
      rw [hσt]
    have h3 : (Polynomial.aeval (σA t)) p = σA ((Polynomial.aeval t) p) := by
      simpa using AlgHom.congr_fun (Polynomial.aeval_algHom σA t) p
    rw [← h3, h2]
  have hσσ : ∀ f : RatFunc ℚ, σA (σA f) = f := by
    intro f
    have h1 : σA f = (Polynomial.aeval t) f.num / (Polynomial.aeval t) f.denom := by
      calc σA f
          = σA (algebraMap ℚ[X] (RatFunc ℚ) f.num / algebraMap ℚ[X] (RatFunc ℚ) f.denom) := by
            rw [RatFunc.num_div_denom f]
        _ = σA (algebraMap ℚ[X] (RatFunc ℚ) f.num) / σA (algebraMap ℚ[X] (RatFunc ℚ) f.denom) := by
            rw [map_div₀]
        _ = (Polynomial.aeval t) f.num / (Polynomial.aeval t) f.denom := by
            rw [hσ_alg f.num, hσ_alg f.denom]
    calc σA (σA f)
        = σA ((Polynomial.aeval t) f.num / (Polynomial.aeval t) f.denom) := by rw [h1]
      _ = σA ((Polynomial.aeval t) f.num) / σA ((Polynomial.aeval t) f.denom) := by rw [map_div₀]
      _ = (Polynomial.aeval Xr) f.num / (Polynomial.aeval Xr) f.denom := by
            rw [hcomp f.num, hcomp f.denom]
      _ = algebraMap ℚ[X] (RatFunc ℚ) f.num / algebraMap ℚ[X] (RatFunc ℚ) f.denom := by
            rw [haevalX f.num, haevalX f.denom]
      _ = f := RatFunc.num_div_denom f
  have hbij : Function.Bijective σA :=
    ⟨fun a b h => by rw [← hσσ a, h, hσσ b], fun b => ⟨σA b, hσσ b⟩⟩
  refine ⟨AlgEquiv.ofBijective σA hbij, ?_, ?_⟩
  · intro f
    rw [AlgEquiv.ofBijective_apply]
    exact hσσ f
  · rw [AlgEquiv.ofBijective_apply]
    exact hσx

end

end Commons.FieldTheory.RatFunc