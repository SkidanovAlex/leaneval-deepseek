import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASZTwistDefs
import Submission.Work.MotAS.ASZChartPresentation
import Submission.Work.MotAS.PhiSDefs
import Submission.Work.MotAS.TwistField
import Submission.Work.MotAS.AK

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASZResidualChartDefs` — the chart map of the residual from the AS twisted Klein curve

The linear projection `phiAS a b` (`Work.MotAS.phiAS`) maps the AS-twisted Klein curve
`C_{3g} = V(kleinPAS a b (3g))` onto the residual curve `V(ZIAS a b g)` of the AS Crauder–Katz
link.  In the chart `y₀ = 1` of `C_{3g}` the projection reads

  `X i ↦ Z (i+1) / Z 0`,   `Z k = Σ j, phiAS a b k j · (y j / y 0)`,

with `y j / y 0 = asTwY D (3g) j / asTwY D (3g) 0` the twisted coordinates.  This file introduces
the elements `Z k ∈ Om D` and the resulting `K`-algebra map `asZResMap`, together with the
homogeneity of `kleinRAS` and the naturality of `phiAS`.

The mathematical statement that `asZResMap` generates the twist field is node
**`Work.MotAS.ASResidualGen`** (the projection is `K`-birational); the polynomial-identity input
that its kernel contains `√(ZIAS a b g)` is the certificate `Work.MotAS.ASPhiChartMem`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace Work.MotAS

open MvPolynomial

section general

variable {R : Type*} [CommRing R]

/-- The `phiAS` entries commute with a ring homomorphism. -/
theorem map_phiAS {S : Type*} [CommRing S] (φ : R →+* S) (a b : R)
    (k j : Fin 5) : φ (Work.MotAS.phiAS a b k j) = Work.MotAS.phiAS (φ a) (φ b) k j := by
  fin_cases k <;> fin_cases j <;> simp [Work.MotAS.phiAS, map_ofNat]

private lemma kR0 (a b g c : R) (z : Fin 5 → R) :
    kleinRAS0 a b g (fun i => c * z i) = c ^ 3 * kleinRAS0 a b g z := by
  simp only [kleinRAS0]; ring
private lemma kR1 (a b g c : R) (z : Fin 5 → R) :
    kleinRAS1 a b g (fun i => c * z i) = c ^ 3 * kleinRAS1 a b g z := by
  simp only [kleinRAS1]; ring
private lemma kR2 (a b g c : R) (z : Fin 5 → R) :
    kleinRAS2 a b g (fun i => c * z i) = c ^ 3 * kleinRAS2 a b g z := by
  simp only [kleinRAS2]; ring
private lemma kR3 (a b g c : R) (z : Fin 5 → R) :
    kleinRAS3 a b g (fun i => c * z i) = c ^ 3 * kleinRAS3 a b g z := by
  simp only [kleinRAS3]; ring
private lemma kR4 (a b g c : R) (z : Fin 5 → R) :
    kleinRAS4 a b g (fun i => c * z i) = c ^ 3 * kleinRAS4 a b g z := by
  simp only [kleinRAS4]; ring

/-- `kleinRAS` is a homogeneous cubic in `z`. -/
theorem kleinRAS_smul_z (a b g c : R) (z : Fin 5 → R) (k : Fin 5) :
    kleinRAS a b g (fun i => c * z i) k = c ^ 3 * kleinRAS a b g z k := by
  fin_cases k
  · simpa [kleinRAS] using kR0 a b g c z
  · simpa [kleinRAS] using kR1 a b g c z
  · simpa [kleinRAS] using kR2 a b g c z
  · simpa [kleinRAS] using kR3 a b g c z
  · simpa [kleinRAS] using kR4 a b g c z

end general

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- `Z k = Σ j, phiAS a b k j · (asTwY D c j / asTwY D c 0)` in the function field `Om D`. -/
noncomputable def asZOm (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (c : RatFunc 𝕜) (k : Fin 5) : Work.MotV.Om D :=
  ∑ j : Fin 5, algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (phiAS (aK D) (bK D) k j)
    * (asTwY D c j / asTwY D c 0)

/-- `asZOm` is `(phiAS · y) k` for the twisted coordinates `y`. -/
theorem asZOm_eq (D : Work.MotV.KleinData 𝕜) (c : RatFunc 𝕜) (k : Fin 5) :
    asZOm 𝕜 D c k = ∑ j : Fin 5, Work.MotAS.phiAS
      (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (aK D))
      (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (bK D)) k j
      * (asTwY D c j / asTwY D c 0) := by
  unfold asZOm
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_phiAS (algebraMap (RatFunc 𝕜) (Work.MotV.Om D)) (aK D) (bK D) k j]

/-- `asZOm` lies in the twist field. -/
theorem asZOm_mem (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (c : RatFunc 𝕜) (k : Fin 5) : asZOm 𝕜 D c k ∈ twistFieldAS D c := by
  unfold asZOm
  refine Subalgebra.sum_mem _ (fun j _ => ?_)
  have h1 : asTwY D c j / asTwY D c 0 ∈ twistFieldAS D c := by
    rw [twistFieldAS]
    exact IntermediateField.subset_adjoin _ _ (Set.mem_range_self j)
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) h1

/-- The `K`-algebra map of the residual chart, `X i ↦ Z (i+1) / Z 0`. -/
noncomputable def asZResMap (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (c : RatFunc 𝕜) (hZ : asZOm 𝕜 D c 0 ≠ 0) :
    MvPolynomial (Fin 3) (RatFunc 𝕜) →ₐ[RatFunc 𝕜] ↥(twistFieldAS D c) :=
  MvPolynomial.aeval
    ![(⟨asZOm 𝕜 D c 1, asZOm_mem D hD c 1⟩ : ↥(twistFieldAS D c))
        / ⟨asZOm 𝕜 D c 0, asZOm_mem D hD c 0⟩,
      (⟨asZOm 𝕜 D c 2, asZOm_mem D hD c 2⟩ : ↥(twistFieldAS D c))
        / ⟨asZOm 𝕜 D c 0, asZOm_mem D hD c 0⟩,
      (⟨asZOm 𝕜 D c 3, asZOm_mem D hD c 3⟩ : ↥(twistFieldAS D c))
        / ⟨asZOm 𝕜 D c 0, asZOm_mem D hD c 0⟩]

theorem asZResMap_X (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (c : RatFunc 𝕜) (hZ : asZOm 𝕜 D c 0 ≠ 0) (i : Fin 3) :
    asZResMap D hD c hZ (MvPolynomial.X i) =
      (⟨asZOm 𝕜 D c ⟨i.1 + 1, by omega⟩, asZOm_mem D hD c _⟩ : ↥(twistFieldAS D c))
        / ⟨asZOm 𝕜 D c 0, asZOm_mem D hD c 0⟩ := by
  fin_cases i <;>
    simp [asZResMap, MvPolynomial.aeval_X]

end Work.MotAS
