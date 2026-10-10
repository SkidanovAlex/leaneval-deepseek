import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.PhiSDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.aszResVec` — the residual coordinates of the AS projection

The K6 leaf `Work.MotC5N3.ASZTwistDivPlaneGeom_three` reduces (see the module docstring of
`Submission/Work/MotC5N3/ASZTwistDivPlaneGeom.lean`) to the statement that the *residual
coordinates* of the AS link, read as functions on the class-`3 * g` twisted Klein curve
`C_{3g} = V(kleinPAS a b (3 * g))`, generate the twist field — together with the (clean) radical
membership of the five cubics.

This file is the **definition layer**: the projective twisted coordinates `v_j = y_j / y_0`
(`aszV`), the residual coordinates `Z_k = Σ_j phiAS k j · v_j` (`aszZ`), the residual chart
coordinates `X_i = Z_{i+1}/Z_0` (`aszX`), their membership in the twist field, the residual chart
vector `aszResVec : Fin 3 → ↥(twistFieldAS D (3 * g))` and the `K`-algebra map
`aszPhi : K[X₀,X₁,X₂] →ₐ[K] ↥(twistFieldAS D (3 * g))`, `X i ↦ X_i`.

Nothing here is hard; the point is that every other module of the leaf can refer to `aszResVec`
and `aszPhi` by name.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Work.MotC5N3

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜]
variable {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]

/-- The projective twisted coordinates `v_j = asTwY D g j / asTwY D g 0`. -/
noncomputable def aszV (D : Work.MotV.KleinData 𝕜) (g : K) (j : Fin 5) : OmA K D :=
  asTwY D g j / asTwY D g 0

/-- The residual coordinates `Z_k = Σ_j phiAS (aK K D) (bK K D) k j · v_j` of the linear
projection `phiAS` applied to the class-`g` twisted Klein point. -/
noncomputable def aszZ (D : Work.MotV.KleinData 𝕜) (g : K) (k : Fin 5) : OmA K D :=
  ∑ j : Fin 5, algebraMap K (OmA K D) (Work.MotAS.phiAS (aK K D) (bK K D) k j) * aszV D g j

/-- The entries of `phiAS` are `K`-rational constants. -/
lemma phiAS_algebraMap (D : Work.MotV.KleinData 𝕜) (k j : Fin 5) :
    Work.MotAS.phiAS (algebraMap K (OmA K D) (aK K D)) (algebraMap K (OmA K D) (bK K D)) k j
      = algebraMap K (OmA K D) (Work.MotAS.phiAS (aK K D) (bK K D) k j) := by
  fin_cases k <;> fin_cases j <;>
    simp only [Work.MotAS.phiAS, map_add, map_mul, map_ofNat, map_zero, map_one]

/-- `aszZ` in the `phiAS`-of-`algebraMap` form, which is the form consumed by
`Work.MotAS.ASZPhiMemGen`. -/
lemma aszZ_eq_phiAS (D : Work.MotV.KleinData 𝕜) (g : K) (k : Fin 5) :
    aszZ D g k = ∑ j : Fin 5, Work.MotAS.phiAS (algebraMap K (OmA K D) (aK K D))
      (algebraMap K (OmA K D) (bK K D)) k j * aszV D g j := by
  rw [aszZ]
  exact Finset.sum_congr rfl fun j _ => by rw [phiAS_algebraMap D k j]

/-- The residual **chart** coordinate `X_i = Z_{i+1} / Z_0` (`i : Fin 3`). -/
noncomputable def aszX (D : Work.MotV.KleinData 𝕜) (g : K) (i : Fin 3) : OmA K D :=
  aszZ D g ⟨i.1 + 1, by omega⟩ / aszZ D g 0

/-- `v_j` lies in the twist field. -/
theorem aszV_mem (D : Work.MotV.KleinData 𝕜) (g : K) (j : Fin 5) :
    aszV D g j ∈ twistFieldAS D g := by
  rw [aszV, twistFieldAS]
  exact IntermediateField.subset_adjoin K _ (Set.mem_range_self j)

/-- `Z_k` lies in the twist field. -/
theorem aszZ_mem (D : Work.MotV.KleinData 𝕜) (g : K) (k : Fin 5) :
    aszZ D g k ∈ twistFieldAS D g := by
  rw [aszZ]
  refine Subalgebra.sum_mem _ (fun j _ => ?_)
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (aszV_mem D g j)

/-- `X_i` lies in the twist field. -/
theorem aszX_mem (D : Work.MotV.KleinData 𝕜) (g : K) (i : Fin 3) :
    aszX D g i ∈ twistFieldAS D g := by
  rw [aszX]
  exact div_mem (aszZ_mem D g _) (aszZ_mem D g 0)

/-- **The residual chart vector** `X_0, X_1, X_2` of the class-`3 * g` twisted Klein curve, as
elements of its twist field. -/
noncomputable def aszResVec (D : Work.MotV.KleinData 𝕜) (g : K) :
    Fin 3 → ↥(twistFieldAS D (3 * g)) :=
  fun i => ⟨aszX D (3 * g) i, aszX_mem D (3 * g) i⟩

/-- **The residual-coordinate map** `X i ↦ Z_{i+1}/Z_0`, from the affine coordinates of the AS
target hyperplane slice to the twist field of the class-`3 * g` twisted Klein curve. -/
noncomputable def aszPhi (D : Work.MotV.KleinData 𝕜) (g : K) :
    MvPolynomial (Fin 3) K →ₐ[K] ↥(twistFieldAS D (3 * g)) :=
  MvPolynomial.aeval (aszResVec D g)

theorem aszPhi_X (D : Work.MotV.KleinData 𝕜) (g : K) (i : Fin 3) :
    aszPhi D g (MvPolynomial.X i) = aszResVec D g i := by
  rw [aszPhi, MvPolynomial.aeval_X]

end Work.MotC5N3
