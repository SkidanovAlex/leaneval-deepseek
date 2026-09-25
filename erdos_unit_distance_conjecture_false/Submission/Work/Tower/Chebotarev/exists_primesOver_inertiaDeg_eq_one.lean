import Mathlib
import Submission.Work.Tower.Chebotarev.Defs

namespace Work.Tower.Chebotarev

open NumberField Polynomial
open scoped Classical nonZeroDivisors NumberField

/-- Kummer–Dedekind: if the prime `q` does not divide the exponent of `θ : 𝓞 K` (equivalently `q`
is coprime to the conductor of `ℤ[θ]`) and `minpoly ℤ θ` has a root `a` modulo `q`, then some prime
of `𝓞 K` above `q` has residue field `𝔽_q` (inertia degree one). -/
theorem exists_primesOver_inertiaDeg_eq_one {K : Type} [Field K] [NumberField K] (θ : 𝓞 K)
    (q : ℕ) [Fact (Nat.Prime q)] (hp : ¬ q ∣ RingOfIntegers.exponent θ) (a : ℤ)
    (ha : (q : ℤ) ∣ (minpoly ℤ θ).eval a) :
    ∃ P : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K), P.1.inertiaDeg ℤ = 1 := by
  -- The reduction of `minpoly ℤ θ` modulo `q` is nonzero, because `minpoly ℤ θ` is monic.
  have hne : (minpoly ℤ θ).map (Int.castRingHom (ZMod q)) ≠ 0 :=
    Polynomial.map_monic_ne_zero (minpoly.monic θ.isIntegral)
  -- The root `a` modulo `q` of `minpoly ℤ θ` gives a root of its reduction modulo `q`.
  have hroot : Polynomial.IsRoot ((minpoly ℤ θ).map (Int.castRingHom (ZMod q)))
      ((Int.castRingHom (ZMod q)) a) := by
    show ((minpoly ℤ θ).map (Int.castRingHom (ZMod q))).eval
      ((Int.castRingHom (ZMod q)) a) = 0
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, Int.coe_castRingHom]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ha
  -- Hence `X - a` is a monic irreducible factor of `minpoly ℤ θ` modulo `q`.
  have hQ : X - C ((Int.castRingHom (ZMod q)) a) ∈ RingOfIntegers.monicFactorsMod θ q :=
    Multiset.mem_toFinset.mpr <|
      (Polynomial.mem_normalizedFactors_iff hne).mpr
        ⟨Polynomial.irreducible_X_sub_C _, Polynomial.monic_X_sub_C _,
          Polynomial.dvd_iff_isRoot.mpr hroot⟩
  -- Kummer–Dedekind: this factor corresponds to a prime of `𝓞 K` above `q`,
  -- whose inertia degree is the degree of the factor, namely `1`.
  refine ⟨(NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm
    ⟨X - C ((Int.castRingHom (ZMod q)) a), hQ⟩, ?_⟩
  exact (NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ).trans
    (Polynomial.natDegree_X_sub_C _)

end Work.Tower.Chebotarev
