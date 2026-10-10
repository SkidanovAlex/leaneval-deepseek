import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotC5N3.ASZResVecDefs
import Submission.Work.MotC5N3.ASZPhiRes
import Submission.Work.MotC5N3.ASZResVecAdjoin
import Submission.Work.MotC5N3.ASZPhiMemGen
import Submission.Work.MotC5N3.ASZChartPresentationGen
import Submission.Work.MotC5N3.trdeg_twistFieldAS
import Submission.Work.MotAS.ASPhiKerHeight
import Submission.Work.MotV5.Contrib.le_two_height_radical_ZIAS
import Submission.Work.MotAS.asChartIdeal_fracIso_of_certificates

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.ASZPhiKerRoot` — the kernel of the residual-coordinate map

The K6 leaf `Work.MotC5N3.ASZTwistDivPlaneGeom_three` states that the function field of the AS
residual curve is the function field of the chart `y₀ = 1` of the class-`3 * g` AS-twisted Klein
curve.  Via `Work.MotC5N3.ASZChartPresentationGen` this is the statement

`FractionRing (K[X₀,X₁,X₂] ⧸ √ZIAS) ≃ₐ[K] ↥(twistFieldAS D (3 * g))`,

i.e. the residual-coordinate map

`aszPhi D g : K[X₀,X₁,X₂] →ₐ[K] ↥(twistFieldAS D (3 * g))`, `X i ↦ Z_{i+1}/Z₀`,

has kernel exactly `√ZIAS`.  This file reduces that to the single input `IsPrime (√ZIAS)`.

## Content

* `zias_le_ker_aszPhi` — the **easy half** `ZIAS ≤ ker (aszPhi D g)`: the residual cubics vanish
  on the class-`3 * g` twisted Klein curve.  The computation is carried out in the ambient
  function field `OmA K D` (where `Work.MotC5N3.ASZPhiMemGen` and
  `Work.MotC5N3.aszPhi_kleinPAS_zero` live) and transported back along the injective inclusion
  `↥(twistFieldAS D (3*g)) → OmA K D`; the key points are the chart identity
  `(1, Z₁/Z₀, Z₂/Z₀, Z₃/Z₀, 0) = Z₀⁻¹ • (Z₀,…,Z₄)` and the homogeneity
  `kleinRAS (c • v) = c³ • kleinRAS v`.
* `aszPhi_hgen` — the image of `aszPhi` generates the twist field (from the proved
  `Work.MotC5N3.ASZResVecAdjoin`).
* `ker_aszPhi_eq_radical` — the **hard half**, in the form in which it is needed: given that
  `√ZIAS` is prime, `ker (aszPhi D g) = √ZIAS`.  The argument is the height count of
  `Work.MotAS.ker_asPhi_eq_radical_of_height_le`: `√Z ≤ ker Φ` and both are prime, so a strict
  inclusion would force `ht (√Z) + 1 ≤ ht (ker Φ) ≤ 2`, contradicting
  `2 ≤ ht (√Z)` (`Work.MotV5.Contrib.le_two_height_radical_ZIAS`); the bound `ht (ker Φ) ≤ 2` is
  the abstract `Work.MotAS.height_ker_le_two_of_transcendental`, applied to the transcendental
  element of the twist field (`Work.MotC5N3.transcendental_twistFieldAS_general`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace Work.MotC5N3

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜]
variable {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]

/-! ## §1 The residual-coordinate map in the ambient function field -/

/-- The residual-coordinate map `aszPhi D g`, composed with the inclusion of the twist field into
the ambient function field `OmA K D`.  Working in `OmA K D` lets every identity be checked where
the AS data (`aszZ_eq_phiAS`, `aszPhi_kleinPAS_zero`) actually lives. -/
noncomputable def aszPhiOmA (D : Work.MotV.KleinData 𝕜) (g : K) :
    MvPolynomial (Fin 3) K →ₐ[K] OmA K D :=
  (IntermediateField.val (twistFieldAS D (3 * g))).comp (aszPhi D g)

theorem aszPhiOmA_apply (D : Work.MotV.KleinData 𝕜) (g : K)
    (x : MvPolynomial (Fin 3) K) :
    aszPhiOmA D g x = ((aszPhi D g x : ↥(twistFieldAS D (3 * g))) : OmA K D) := rfl

/-- The residual-coordinate map and its `OmA`-valued companion have the same kernel. -/
theorem ker_aszPhiOmA (D : Work.MotV.KleinData 𝕜) (g : K) :
    RingHom.ker (aszPhiOmA D g) = RingHom.ker (aszPhi D g) := by
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, aszPhiOmA_apply]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- `C` is `algebraMap` for `MvPolynomial`, so an algebra map commutes with it. -/
theorem aszPhiOmA_C (D : Work.MotV.KleinData 𝕜) (g : K) (x : K) :
    aszPhiOmA D g (MvPolynomial.C x) = algebraMap K (OmA K D) x := by
  rw [MvPolynomial.C_eq_algebraMap]
  exact (aszPhiOmA D g).commutes x

/-! ## §2 The easy half: `ZIAS ≤ ker (aszPhi D g)` -/

/-- **The chart identity.**  The chart vector `(1, X₀, X₁, X₂, 0)` of the AS target hyperplane,
read in the twist field through `aszPhi`, is the residual coordinate vector `(Z₀,…,Z₄)` normalised
by `Z₀`.  The last entry uses `Z₄ = 0` (`aszZ_four`), the first `Z₀ ≠ 0`. -/
theorem aszPhiOmA_chart (D : Work.MotV.KleinData 𝕜) (g : K)
    (hz0 : aszZ D (3 * g) 0 ≠ 0) :
    (fun i : Fin 5 =>
        aszPhiOmA D g (![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0] i))
      = fun i => (aszZ D (3 * g) 0)⁻¹ * aszZ D (3 * g) i := by
  funext i
  fin_cases i
  · show aszPhiOmA D g 1 = (aszZ D (3 * g) 0)⁻¹ * aszZ D (3 * g) 0
    rw [map_one, inv_mul_cancel₀ hz0]
  · show aszPhiOmA D g (MvPolynomial.X 0) = (aszZ D (3 * g) 0)⁻¹ * aszZ D (3 * g) 1
    rw [aszPhiOmA_apply, aszPhi_X]
    show aszX D (3 * g) 0 = (aszZ D (3 * g) 0)⁻¹ * aszZ D (3 * g) 1
    rw [aszX, div_eq_mul_inv, mul_comm]
    exact congrArg (fun t : Fin 5 => (aszZ D (3 * g) 0)⁻¹ * aszZ D (3 * g) t)
      (by decide : (⟨(0 : Fin 3).1 + 1, by omega⟩ : Fin 5) = 1)
  · show aszPhiOmA D g (MvPolynomial.X 1) = (aszZ D (3 * g) 0)⁻¹ * aszZ D (3 * g) 2
    rw [aszPhiOmA_apply, aszPhi_X]
    show aszX D (3 * g) 1 = (aszZ D (3 * g) 0)⁻¹ * aszZ D (3 * g) 2
    rw [aszX, div_eq_mul_inv, mul_comm]
    exact congrArg (fun t : Fin 5 => (aszZ D (3 * g) 0)⁻¹ * aszZ D (3 * g) t)
      (by decide : (⟨(1 : Fin 3).1 + 1, by omega⟩ : Fin 5) = 2)
  · show aszPhiOmA D g (MvPolynomial.X 2) = (aszZ D (3 * g) 0)⁻¹ * aszZ D (3 * g) 3
    rw [aszPhiOmA_apply, aszPhi_X]
    show aszX D (3 * g) 2 = (aszZ D (3 * g) 0)⁻¹ * aszZ D (3 * g) 3
    rw [aszX, div_eq_mul_inv, mul_comm]
    exact congrArg (fun t : Fin 5 => (aszZ D (3 * g) 0)⁻¹ * aszZ D (3 * g) t)
      (by decide : (⟨(2 : Fin 3).1 + 1, by omega⟩ : Fin 5) = 3)
  · show aszPhiOmA D g 0 = (aszZ D (3 * g) 0)⁻¹ * aszZ D (3 * g) 4
    rw [map_zero, aszZ_four D (3 * g), mul_zero]

/-- **The residual cubics vanish on the class-`3 * g` twisted Klein curve.** -/
theorem kleinRAS_aszZ_zero (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (g : K) :
    Work.MotAS.kleinRAS (algebraMap K (OmA K D) (aK K D))
        (algebraMap K (OmA K D) (bK K D)) (algebraMap K (OmA K D) g)
        (fun i => aszZ D (3 * g) i) = 0 := by
  have h5 : (5 : OmA K D) = 0 := five_eq_zero_OmA 𝕜 D
  have hPAS : Work.MotAS.kleinPAS (algebraMap K (OmA K D) (aK K D))
      (algebraMap K (OmA K D) (bK K D)) (3 * algebraMap K (OmA K D) g)
      (fun j => aszV D (3 * g) j) = 0 := by
    rw [show (3 : OmA K D) * algebraMap K (OmA K D) g
        = algebraMap K (OmA K D) (3 * g) by rw [map_mul, map_ofNat]]
    exact aszPhi_kleinPAS_zero D hD.1 g
  have hspan : Ideal.span (Set.range (fun i : Fin 5 =>
      Work.MotAS.kleinPAS (algebraMap K (OmA K D) (aK K D))
        (algebraMap K (OmA K D) (bK K D)) (3 * algebraMap K (OmA K D) g)
        (fun j => aszV D (3 * g) j) i)) = ⊥ := by
    have hfun : (fun i : Fin 5 => Work.MotAS.kleinPAS (algebraMap K (OmA K D) (aK K D))
        (algebraMap K (OmA K D) (bK K D)) (3 * algebraMap K (OmA K D) g)
        (fun j => aszV D (3 * g) j) i) = fun _ => (0 : OmA K D) :=
      funext fun i => congrFun hPAS i
    rw [hfun]
    simp
  have hzero : ∀ k : Fin 5,
      Work.MotAS.kleinRAS (algebraMap K (OmA K D) (aK K D))
        (algebraMap K (OmA K D) (bK K D)) (algebraMap K (OmA K D) g)
        (fun i => ∑ j, Work.MotAS.phiAS (algebraMap K (OmA K D) (aK K D))
          (algebraMap K (OmA K D) (bK K D)) i j * aszV D (3 * g) j) k = 0 := by
    intro k
    have h := ASZPhiMemGen h5 (algebraMap K (OmA K D) (aK K D))
      (algebraMap K (OmA K D) (bK K D)) (algebraMap K (OmA K D) g)
      (fun j => aszV D (3 * g) j) k
    rw [hspan] at h
    simpa using h
  have hfun : (fun i => aszZ D (3 * g) i)
      = fun i => ∑ j, Work.MotAS.phiAS (algebraMap K (OmA K D) (aK K D))
          (algebraMap K (OmA K D) (bK K D)) i j * aszV D (3 * g) j :=
    funext fun i => aszZ_eq_phiAS D (3 * g) i
  rw [hfun]
  exact funext hzero

/-- **The easy half**: the residual ideal lies in the kernel of the residual-coordinate map. -/
theorem zias_le_ker_aszPhiOmA (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : K) :
    Work.MotAS.ZIAS (aK K D) (bK K D) g ≤ RingHom.ker (aszPhiOmA D g) := by
  rw [Work.MotAS.ZIAS, Ideal.span_le]
  rintro x ⟨k, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker]
  have hker := kleinRAS_ringHom (aszPhiOmA D g).toRingHom (MvPolynomial.C (aK K D))
    (MvPolynomial.C (bK K D)) (MvPolynomial.C g)
    ![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0] k
  have hker' : aszPhiOmA D g (Work.MotAS.kleinRAS (MvPolynomial.C (aK K D))
      (MvPolynomial.C (bK K D)) (MvPolynomial.C g)
      ![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0] k)
      = Work.MotAS.kleinRAS (aszPhiOmA D g (MvPolynomial.C (aK K D)))
          (aszPhiOmA D g (MvPolynomial.C (bK K D))) (aszPhiOmA D g (MvPolynomial.C g))
          (fun i => aszPhiOmA D g
            (![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0] i)) k := hker
  rw [Work.MotAS.zcubAS, hker', aszPhiOmA_C D g (aK K D), aszPhiOmA_C D g (bK K D),
    aszPhiOmA_C D g g, aszPhiOmA_chart D g (aszZ_three_mul_zero_ne_zero D hD g)]
  have hsmul := Work.MotAS.kleinRAS_smul (algebraMap K (OmA K D) (aK K D))
    (algebraMap K (OmA K D) (bK K D)) (algebraMap K (OmA K D) g)
    ((aszZ D (3 * g) 0)⁻¹) (fun i => aszZ D (3 * g) i)
  rw [hsmul, kleinRAS_aszZ_zero D hD g]
  simp

/-- **The easy half**, in the twist field. -/
theorem zias_le_ker_aszPhi (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : K) :
    Work.MotAS.ZIAS (aK K D) (bK K D) g ≤ RingHom.ker (aszPhi D g) := by
  rw [← ker_aszPhiOmA D g]
  exact zias_le_ker_aszPhiOmA D hD g

/-! ## §3 The generation statement -/

/-- The range of `aszPhi D g` contains the generating set of `ASZResVecAdjoin`; hence the subfield
it generates is everything. -/
theorem aszPhi_hgen (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    Subfield.closure (Set.range (algebraMap K ↥(twistFieldAS D (3 * g)))
      ∪ Set.range (aszPhi D g)) = ⊤ := by
  set L := ↥(twistFieldAS D (3 * g)) with hL
  have hsub : Subfield.closure (Set.range (algebraMap K L)
      ∪ Set.range (fun i : Fin 3 => aszResVec D g i)) = ⊤ := by
    change (IntermediateField.adjoin K (Set.range (fun i : Fin 3 => aszResVec D g i))).toSubfield
      = ⊤
    rw [(ASZResVecAdjoin K D hD g hg).2]
    exact Subfield.ext (fun x => Iff.rfl)
  have hrange : Set.range (fun i : Fin 3 => aszResVec D g i) ⊆ Set.range (aszPhi D g) := by
    rintro x ⟨i, rfl⟩
    exact ⟨MvPolynomial.X i, aszPhi_X D g i⟩
  rw [eq_top_iff]
  refine le_trans (le_of_eq hsub.symm) ?_
  refine Subfield.closure_le.mpr ?_
  intro x hx
  exact Subfield.subset_closure (hx.elim (fun h => Or.inl h) (fun h => Or.inr (hrange h)))

/-! ## §4 The hard half, from the irreducibility of the residual curve -/

/-- **`ker (aszPhi D g) = √ZIAS`** as soon as `√ZIAS` is prime.

`√Z ≤ ker Φ` because `ker Φ` is prime and contains `Z`; `√Z` has height at least `2`
(`le_two_height_radical_ZIAS`) and `ker Φ` at most `2` (the abstract dimension bound
`height_ker_le_two_of_transcendental`, the twist field having a transcendental element), so a
strict inclusion of primes would give `2 + 1 ≤ 2`. -/
theorem ker_aszPhi_eq_radical (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g)
    (hprime : (Ideal.radical (Work.MotAS.ZIAS (aK K D) (bK K D) g)).IsPrime) :
    RingHom.ker (aszPhi D g) = Ideal.radical (Work.MotAS.ZIAS (aK K D) (bK K D) g) := by
  haveI hker : (RingHom.ker (aszPhi D g)).IsPrime := RingHom.ker_isPrime (aszPhi D g)
  have hZ := zias_le_ker_aszPhi D hD g
  have hle : Ideal.radical (Work.MotAS.ZIAS (aK K D) (bK K D) g) ≤ RingHom.ker (aszPhi D g) :=
    hker.radical_le_iff.mpr hZ
  refine le_antisymm ?_ hle
  haveI : (Ideal.radical (Work.MotAS.ZIAS (aK K D) (bK K D) g)).IsPrime := hprime
  have hker2 : (RingHom.ker (aszPhi D g)).height ≤ 2 := by
    obtain ⟨x, hx⟩ := transcendental_twistFieldAS_general D hD.1 (3 * g)
    exact Work.MotAS.height_ker_le_two_of_transcendental (aszPhi D g) (aszPhi_hgen D hD g hg)
      ⟨x, hx⟩
  have hht : (2 : ℕ∞) ≤ (Ideal.radical (Work.MotAS.ZIAS (aK K D) (bK K D) g)).height :=
    Work.MotV5.Contrib.le_two_height_radical_ZIAS K (aK K D) (bK K D) g
      (aK_sq_sub_ne (K := K) D hD) hg
  by_contra hcon
  have hne : Ideal.radical (Work.MotAS.ZIAS (aK K D) (bK K D) g) ≠ RingHom.ker (aszPhi D g) :=
    fun h => hcon (le_of_eq h.symm)
  have hlt : Ideal.radical (Work.MotAS.ZIAS (aK K D) (bK K D) g) < RingHom.ker (aszPhi D g) :=
    lt_of_le_of_ne hle hne
  have h2 : (Ideal.radical (Work.MotAS.ZIAS (aK K D) (bK K D) g)).height + 1
      ≤ (RingHom.ker (aszPhi D g)).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h3 : (Ideal.radical (Work.MotAS.ZIAS (aK K D) (bK K D) g)).height + 1 ≤ (2 : ℕ∞) :=
    le_trans h2 hker2
  have h4 : (Ideal.radical (Work.MotAS.ZIAS (aK K D) (bK K D) g)).height < (2 : ℕ∞) :=
    (ENat.add_one_le_iff' (ne_of_lt (WithTop.coe_lt_top 2))).mp h3
  exact (not_lt.mpr hht) h4

/-! ## §5 The class-`3 * g` leaf, conditional on the irreducibility of the residual curve -/

/-- **The class-`3 * g` K6 leaf, from the irreducibility of the residual curve.** -/
theorem ASZTwistDivPlaneGeom_three_of_isPrime (K : Type) [Field K] [CharP K 5] {𝕜 : Type}
    [Field 𝕜] [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g)
    (hprime : (Ideal.radical (Work.MotAS.ZIAS (aK K D) (bK K D) g)).IsPrime) :
    Nonempty (FractionRing (MvPolynomial (Fin 3) K ⧸
        Ideal.radical (Work.MotAS.ZIAS (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g)) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin 5) K ⧸
        Work.MotAS.asChartIdeal (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) (3 * g))) := by
  obtain ⟨e⟩ := Work.MotAS.fractionRing_quotient_algEquiv_of_ker
    (Ideal.radical (Work.MotAS.ZIAS (aK K D) (bK K D) g)) (aszPhi D g)
    (ker_aszPhi_eq_radical D hD g hg hprime) (aszPhi_hgen D hD g hg)
  obtain ⟨e₂⟩ := ASZChartPresentationGen K D hD (3 * g)
  exact ⟨e.trans e₂.symm⟩

end Work.MotC5N3
