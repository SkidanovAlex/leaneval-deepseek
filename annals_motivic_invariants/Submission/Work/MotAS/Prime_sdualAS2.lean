import Mathlib
import Submission.Work.MotAS.SdualAS2Explicit
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.LinkCertASBase
import Submission.Work.MotAS.TwistField
import Submission.Work.MotV5.CensusAux.fAS_notMem_pe
import Submission.Work.ClassBCD.RatFunc.irreducible_X_pow_sub_X_sub_C
import Submission.Work.MotAS.sdualAS2_finSuccEquiv_deg_lc
import Submission.Work.MotAS.sdualAS2_finSuccEquiv_map
import Submission.Work.MotAS.irreducible_sdualAS2_quintic
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.Prime_sdualAS2`

The target ruling quintic `sdualAS2 a b g = kleinSecDualAS a b g (tchart)` of the AS
(characteristic 5) Crauder–Katz chart is a prime element of `K[x₀,x₁,x₂]`, `K = RatFunc 𝕜`.

## The argument

Write `p = sdualAS2 a b g` and `P = finSuccEquiv K 2 p ∈ R[X]`, `R = K[x₁,x₂]`
(`R[X] = K[x₀,x₁,x₂]`, `X = x₀`).  The explicit shape (`SdualAS2Explicit.sdualAS2_explicit`)
shows

* `P.natDegree = 5` and `P.leadingCoeff = C (g * (a^10 - a^5 b^5 - b^10))`, a **unit** of `R`
  (as soon as `g * (a^10-a^5b^5-b^10) ≠ 0`);
* the `R →+* K`-map `ψ` evaluating `x₁, x₂` at `0` sends
  `P ↦ (a^10-a^5b^5-b^10) * (C g * X^5 - X^4 + 1)`.

If `P = F * H` is a non-trivial factorisation then `lc F * lc H = lc P` is a unit, so
`lc F = C c` with `c ≠ 0`; hence `natDegree (map ψ F) = natDegree F`, and `ψ` (which cannot
kill the product) turns the factorisation into one of `ψ P`.  Therefore irreducibility of
`ψ P` — i.e. of the quintic `C g * X^5 - X^4 + 1`, whose reversal `X^5 - X + C g` is
irreducible by the Artin–Schreier criterion since `g ∉ ℘(K)` — forces `P`, hence `p`, to be
irreducible.  In a UFD irreducible elements are prime.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Work.MotAS

open MvPolynomial

/-- Irreducibility transfers along a ring equivalence. -/
theorem irreducible_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) {x : A} :
    Irreducible x ↔ Irreducible (e x) := by
  have h1 : ∀ y : A, IsUnit (e y) ↔ IsUnit y := fun y =>
    ⟨fun h => by
      have h' : IsUnit (e.symm (e y)) := h.map e.symm
      rwa [RingEquiv.symm_apply_apply] at h',
     fun h => h.map e⟩
  constructor
  · intro hx
    refine ⟨fun hu => hx.not_isUnit ((h1 x).mp hu), ?_⟩
    intro y z hyz
    have h : x = e.symm y * e.symm z := by
      apply e.injective
      rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hyz]
    rcases hx.isUnit_or_isUnit h with hu | hu
    · exact Or.inl (by simpa using (h1 (e.symm y)).mpr hu)
    · exact Or.inr (by simpa using (h1 (e.symm z)).mpr hu)
  · intro hx
    refine ⟨fun hu => hx.not_isUnit ((h1 x).mpr hu), ?_⟩
    intro y z hyz
    have h : e x = e y * e z := by rw [hyz, map_mul]
    rcases hx.isUnit_or_isUnit h with hu | hu
    · exact Or.inl ((h1 y).mp hu)
    · exact Or.inr ((h1 z).mp hu)

/-- **The assembly.**  Given the explicit-shape inputs for `p = sdualAS2 a b g`, prime-ness of `p`
follows from irreducibility of the chart quintic `C g * X^5 - X^4 + 1`. -/
theorem prime_sdualAS2_of {K : Type*} [Field K] (a b g : K)
    (h : g * (a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10) ≠ 0)
    (hirr : Irreducible ((Polynomial.C g : Polynomial K) * Polynomial.X ^ 5
      - Polynomial.X ^ 4 + 1))
    (hdeg : (MvPolynomial.finSuccEquiv K 2 (sdualAS2 a b g)).natDegree = 5)
    (hlc : (MvPolynomial.finSuccEquiv K 2 (sdualAS2 a b g)).leadingCoeff
      = MvPolynomial.C (g * (a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10)))
    (hmap : Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K))
        (MvPolynomial.finSuccEquiv K 2 (sdualAS2 a b g))
      = Polynomial.C (a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10)
        * (Polynomial.C g * Polynomial.X ^ 5 - Polynomial.X ^ 4 + 1)) :
    Prime (sdualAS2 a b g) := by
  have hcc : a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10 ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
  have hg : g ≠ 0 := fun h0 => h (by rw [h0, zero_mul])
  -- the image of `P` under `ψ` is irreducible
  have hCunit : IsUnit (Polynomial.C (a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10) : Polynomial K) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcc)
  have hmapirr : Irreducible (Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K))
      (MvPolynomial.finSuccEquiv K 2 (sdualAS2 a b g))) := by
    rw [hmap, mul_comm]
    exact (irreducible_mul_isUnit hCunit).mpr hirr
  -- `P` itself
  have hPne : MvPolynomial.finSuccEquiv K 2 (sdualAS2 a b g) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    exact absurd hdeg (by norm_num)
  have hPnotunit : ¬ IsUnit (MvPolynomial.finSuccEquiv K 2 (sdualAS2 a b g)) := fun hu => by
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [hdeg] at h0
    exact absurd h0 (by norm_num)
  have hPirr : Irreducible (MvPolynomial.finSuccEquiv K 2 (sdualAS2 a b g)) := by
    refine ⟨hPnotunit, ?_⟩
    intro F H hFH
    by_contra hcon
    push_neg at hcon
    obtain ⟨hFnu, hHnu⟩ := hcon
    have hF0 : F ≠ 0 := fun h0 => hPne (by rw [hFH, h0, zero_mul])
    have hH0 : H ≠ 0 := fun h0 => hPne (by rw [hFH, h0, mul_zero])
    have hdegFH : F.natDegree + H.natDegree = 5 := by
      have h1 := Polynomial.natDegree_mul hF0 hH0
      rw [← hFH, hdeg] at h1
      exact h1.symm
    -- the leading coefficients are units of `R`
    have hlcFH : F.leadingCoeff * H.leadingCoeff
        = MvPolynomial.C (g * (a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10)) := by
      rw [← Polynomial.leadingCoeff_mul, ← hFH, hlc]
    have hP5 : (MvPolynomial.finSuccEquiv K 2 (sdualAS2 a b g)).coeff 5
        = MvPolynomial.C (g * (a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10)) := by
      have h1 := hlc
      rw [Polynomial.leadingCoeff, hdeg] at h1
      exact h1
    have hunitF : IsUnit F.leadingCoeff := by
      have h1 : IsUnit (F.leadingCoeff * H.leadingCoeff) := by
        rw [hlcFH]
        exact (isUnit_iff_ne_zero.mpr (mul_ne_zero hg hcc)).map MvPolynomial.C
      exact (IsUnit.mul_iff.mp h1).1
    have hunitH : IsUnit H.leadingCoeff := by
      have h1 : IsUnit (F.leadingCoeff * H.leadingCoeff) := by
        rw [hlcFH]
        exact (isUnit_iff_ne_zero.mpr (mul_ne_zero hg hcc)).map MvPolynomial.C
      exact (IsUnit.mul_iff.mp h1).2
    -- so the images of the factors keep their degrees
    obtain ⟨c, hcu, hFc⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp hunitF
    obtain ⟨d, hdu, hHd⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp hunitH
    have hc0 : c ≠ 0 := isUnit_iff_ne_zero.mp hcu
    have hd0 : d ≠ 0 := isUnit_iff_ne_zero.mp hdu
    have hψF : (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K)) F.leadingCoeff ≠ 0 := by
      rw [hFc, MvPolynomial.eval₂Hom_C]
      exact hc0
    have hψH : (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K)) H.leadingCoeff ≠ 0 := by
      rw [hHd, MvPolynomial.eval₂Hom_C]
      exact hd0
    have hmapFdeg : (Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K))
        F).natDegree = F.natDegree :=
      Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hψF
    have hmapHdeg : (Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K))
        H).natDegree = H.natDegree :=
      Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hψH
    -- both factors of `P` have positive `X`-degree
    have hFdeg1 : 1 ≤ F.natDegree := by
      by_contra hlt
      have hFn : F.natDegree = 0 := by omega
      refine hFnu ?_
      have hFc : F = Polynomial.C (F.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hFn
      have hdvd : F.coeff 0 ∣ MvPolynomial.C (g * (a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10)) := by
        refine ⟨H.coeff 5, ?_⟩
        have h1 : (MvPolynomial.finSuccEquiv K 2 (sdualAS2 a b g)).coeff 5
            = F.coeff 0 * H.coeff 5 := by
          conv_lhs => rw [hFH, hFc]
          exact Polynomial.coeff_C_mul H
        rw [← h1, hP5]
      have hunit : IsUnit (F.coeff 0) := by
        obtain ⟨k, hk⟩ := hdvd
        have hU : IsUnit (F.coeff 0 * k) := by
          rw [← hk]
          exact (isUnit_iff_ne_zero.mpr (mul_ne_zero hg hcc)).map MvPolynomial.C
        exact (IsUnit.mul_iff.mp hU).1
      rw [hFc]
      exact Polynomial.isUnit_C.mpr hunit
    have hHdeg1 : 1 ≤ H.natDegree := by
      by_contra hlt
      have hHn : H.natDegree = 0 := by omega
      refine hHnu ?_
      have hHc : H = Polynomial.C (H.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hHn
      have hdvd : H.coeff 0 ∣ MvPolynomial.C (g * (a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10)) := by
        refine ⟨F.coeff 5, ?_⟩
        have h1 : (MvPolynomial.finSuccEquiv K 2 (sdualAS2 a b g)).coeff 5
            = H.coeff 0 * F.coeff 5 := by
          conv_lhs => rw [hFH, hHc, mul_comm]
          exact Polynomial.coeff_C_mul F
        rw [← h1, hP5]
      have hunit : IsUnit (H.coeff 0) := by
        obtain ⟨k, hk⟩ := hdvd
        have hU : IsUnit (H.coeff 0 * k) := by
          rw [← hk]
          exact (isUnit_iff_ne_zero.mpr (mul_ne_zero hg hcc)).map MvPolynomial.C
        exact (IsUnit.mul_iff.mp hU).1
      rw [hHc]
      exact Polynomial.isUnit_C.mpr hunit
    -- one of the two factors has `X`-degree at most two
    have hkey : ∀ (G G' : Polynomial (MvPolynomial (Fin 2) K)), G * G'
        = MvPolynomial.finSuccEquiv K 2 (sdualAS2 a b g) → 1 ≤ G.natDegree →
        (Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K)) G).natDegree
            = G.natDegree →
        (Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K)) G').natDegree
            = G'.natDegree →
        G.natDegree ≤ 2 →
        False := by
      intro G G' hGG hG1 hGdeg hG'deg hG2
      have hG0 : G ≠ 0 := fun h0 => hPne (by rw [← hGG, h0, zero_mul])
      have hG'0 : G' ≠ 0 := fun h0 => hPne (by rw [← hGG, h0, mul_zero])
      have hG'3 : 3 ≤ G'.natDegree := by
        have h1 := Polynomial.natDegree_mul hG0 hG'0
        rw [hGG, hdeg] at h1
        omega
      have hfac : Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K))
          (MvPolynomial.finSuccEquiv K 2 (sdualAS2 a b g))
          = Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K)) G
            * Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K)) G' := by
        rw [← hGG, Polynomial.map_mul]
      have hGu : ¬ IsUnit (Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K)) G) :=
        fun hu => by have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
      have hG'u : ¬ IsUnit (Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K)) G') :=
        fun hu => by have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
      rcases hmapirr.isUnit_or_isUnit hfac with hu | hu
      · exact hGu hu
      · exact hG'u hu
    by_cases hF2 : F.natDegree ≤ 2
    · exact hkey F H (by rw [hFH]) hFdeg1 hmapFdeg hmapHdeg hF2
    · have hH2 : H.natDegree ≤ 2 := by omega
      exact hkey H F (by rw [hFH, mul_comm]) hHdeg1 hmapHdeg hmapFdeg hH2
  have hpirr : Irreducible (sdualAS2 a b g) :=
    (irreducible_of_ringEquiv (MvPolynomial.finSuccEquiv K 2).toRingEquiv
      (x := sdualAS2 a b g)).mpr hPirr
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hpirr

/-- **The target ruling quintic of the AS chart is a prime element.** -/
theorem Prime_sdualAS2 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    Prime (Work.MotAS.sdualAS2 (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜)) := by
  have hd : (Work.MotAS.aK D) ^ 2 - (Work.MotAS.aK D) * (Work.MotAS.bK D)
      - (Work.MotAS.bK D) ^ 2 ≠ 0 := aK_sq_sub_ne D hD
  have hfAS : Work.MotV.fAS 𝕜 ≠ 0 := by
    intro h
    refine Work.MotV5.CensusAux.fAS_notMem_pe 𝕜 ⟨0, ?_⟩
    rw [show (RatFunc.X ^ 3 + RatFunc.X : RatFunc 𝕜) = 0 from h]
    first | refl_ring1 | ring
  have hfrob : (Work.MotAS.aK D) ^ 10 - (Work.MotAS.aK D) ^ 5 * (Work.MotAS.bK D) ^ 5
      - (Work.MotAS.bK D) ^ 10
      = ((Work.MotAS.aK D) ^ 2 - (Work.MotAS.aK D) * (Work.MotAS.bK D)
          - (Work.MotAS.bK D) ^ 2) ^ 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hA := sub_pow_char_pow ((Work.MotAS.aK D) ^ 2 - (Work.MotAS.aK D) * (Work.MotAS.bK D))
      ((Work.MotAS.bK D) ^ 2) 1
    have hB := sub_pow_char_pow ((Work.MotAS.aK D) ^ 2)
      ((Work.MotAS.aK D) * (Work.MotAS.bK D)) 1
    simp only [pow_one] at hA hB
    rw [hA, hB]
    first | refl_ring1 | ring
  have hcc : (Work.MotAS.aK D) ^ 10 - (Work.MotAS.aK D) ^ 5 * (Work.MotAS.bK D) ^ 5
      - (Work.MotAS.bK D) ^ 10 ≠ 0 := by
    rw [hfrob]
    exact pow_ne_zero 5 hd
  have h : Work.MotV.fAS 𝕜 * ((Work.MotAS.aK D) ^ 10 - (Work.MotAS.aK D) ^ 5
      * (Work.MotAS.bK D) ^ 5 - (Work.MotAS.bK D) ^ 10) ≠ 0 := mul_ne_zero hfAS hcc
  have hdl := sdualAS2_finSuccEquiv_deg_lc (Work.MotAS.aK D) (Work.MotAS.bK D)
    (Work.MotV.fAS 𝕜) h
  exact prime_sdualAS2_of (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜) h
    (irreducible_sdualAS2_quintic 𝕜) hdl.1 hdl.2
    (sdualAS2_finSuccEquiv_map (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜))

end Work.MotAS
