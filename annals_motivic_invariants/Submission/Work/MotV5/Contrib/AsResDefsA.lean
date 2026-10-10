import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotC5N3.twistFieldAS_eq
import Submission.Work.MotAS.ASResDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotV5.Contrib.AsResDefsA` — the residual chart of the AS projection over a general base

Generic-`K` analogue of `Work.MotAS.ASZResidualChartDefs` / `Work.MotAS.ASResDefs` (which are
stated over `RatFunc 𝕜`):  the residual coordinates

  `asZOmA D g k = Σ j, phiAS (aK K D) (bK K D) k j · (asTwY D g j / asTwY D g 0) ∈ OmA K D`

of the linear projection `phiAS`, together with the constants `A,B,C,D,E,μ,λ` of the six nonzero
entries of `phiAS`, the projective coordinates `asZvA`, the residual chart `asZXA` and the inverse
chart `asZwA1 … asZwA4`.

The content proved here is the linear-form description of the `asZOmA` (the `phiAS` matrix is
strictly upper triangular with the six listed entries), the nonvanishing of the chart coefficients
`A, D, E, μ` under `ASGood`, and the membership of the residual coordinates in the twist field.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace Work.MotV5.Contrib

open Work.MotC5N3
open Work.MotAS (phiAS kleinPAS1 kleinPAS3 kleinPAS kleinPAS1_decomp_fin kleinPAS1_decomp_u
  kleinPAS3_decomp_fin kleinPAS3_decomp_u kleinPAS1_smul kleinPAS3_smul kleinPAS_smul
  three_mul_add_ne_zero add_two_mul_ne_zero four_mul_add_three_mul_ne_zero sum_five_sq
  phiAS_00 phiAS_01 phiAS_02 phiAS_03 phiAS_04 phiAS_10 phiAS_11 phiAS_12 phiAS_13 phiAS_14
  phiAS_20 phiAS_21 phiAS_22 phiAS_23 phiAS_24 phiAS_30 phiAS_31 phiAS_32 phiAS_33 phiAS_34
  phiAS_40 phiAS_41 phiAS_42 phiAS_43 phiAS_44)

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]
variable {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]

/-! ## §1 The residual coordinates `Z k = Σ j, phiAS k j · (y_j / y_0)` -/

/-- `Z k = Σ j, phiAS (aK K D) (bK K D) k j · (asTwY D g j / asTwY D g 0)` in `OmA K D`. -/
noncomputable def asZOmA (D : Work.MotV.KleinData 𝕜) (g : K) (k : Fin 5) : OmA K D :=
  ∑ j : Fin 5, algebraMap K (OmA K D) (phiAS (aK K D) (bK K D) k j) *
    (asTwY D g j / asTwY D g 0)

/-! ## §2 The constants of the residual chart -/

/-- `A = 3a+b = phiAS 0 1`. -/
noncomputable def asZAA (D : Work.MotV.KleinData 𝕜) (g : K) : OmA K D :=
  algebraMap K (OmA K D) (phiAS (aK K D) (bK K D) 0 1)

/-- `B = 3a+4b = phiAS 0 3`. -/
noncomputable def asZBA (D : Work.MotV.KleinData 𝕜) (g : K) : OmA K D :=
  algebraMap K (OmA K D) (phiAS (aK K D) (bK K D) 0 3)

/-- `C = a+3b = phiAS 1 4`. -/
noncomputable def asZCA (D : Work.MotV.KleinData 𝕜) (g : K) : OmA K D :=
  algebraMap K (OmA K D) (phiAS (aK K D) (bK K D) 1 4)

/-- `D = a+2b = phiAS 2 3`. -/
noncomputable def asZDA (D : Work.MotV.KleinData 𝕜) (g : K) : OmA K D :=
  algebraMap K (OmA K D) (phiAS (aK K D) (bK K D) 2 3)

/-- `E = 4a+3b = phiAS 3 4`. -/
noncomputable def asZEA (D : Work.MotV.KleinData 𝕜) (g : K) : OmA K D :=
  algebraMap K (OmA K D) (phiAS (aK K D) (bK K D) 3 4)

/-- The Klein coefficient `a`, pushed to `OmA K D`. -/
noncomputable def asZaA (D : Work.MotV.KleinData 𝕜) (g : K) : OmA K D :=
  algebraMap K (OmA K D) (aK K D)

/-- The Klein coefficient `b`, pushed to `OmA K D`. -/
noncomputable def asZbA (D : Work.MotV.KleinData 𝕜) (g : K) : OmA K D :=
  algebraMap K (OmA K D) (bK K D)

/-- The Artin–Schreier parameter `g`, pushed to `OmA K D`. -/
noncomputable def asZcA (D : Work.MotV.KleinData 𝕜) (g : K) : OmA K D :=
  algebraMap K (OmA K D) g

/-- `μ = 2(a² - ab - b²)`. -/
noncomputable def asZmuA (D : Work.MotV.KleinData 𝕜) (g : K) : OmA K D :=
  algebraMap K (OmA K D) (2 * (aK K D ^ 2 - aK K D * bK K D - bK K D ^ 2))

/-- `λ = μ·B/A + (a² + b²)`. -/
noncomputable def asZlamA (D : Work.MotV.KleinData 𝕜) (g : K) : OmA K D :=
  asZmuA D g * asZBA D g / asZAA D g + (asZaA D g ^ 2 + asZbA D g ^ 2)

/-! ## §3 The projective coordinates, the residual chart and the inverse chart -/

/-- The projective twisted coordinates `v_j = asTwY D g j / asTwY D g 0`. -/
noncomputable def asZvA (D : Work.MotV.KleinData 𝕜) (g : K) (j : Fin 5) : OmA K D :=
  asTwY D g j / asTwY D g 0

/-- The residual chart coordinates `X i = Z (i+1) / Z 0`. -/
noncomputable def asZXA (D : Work.MotV.KleinData 𝕜) (g : K) (i : Fin 3) : OmA K D :=
  asZOmA D g ⟨i.1 + 1, by omega⟩ / asZOmA D g 0

/-- `w₃ = X₁/D`. -/
noncomputable def asZwA3 (D : Work.MotV.KleinData 𝕜) (g : K) : OmA K D :=
  asZXA D g 1 / asZDA D g
/-- `w₄ = X₂/E`. -/
noncomputable def asZwA4 (D : Work.MotV.KleinData 𝕜) (g : K) : OmA K D :=
  asZXA D g 2 / asZEA D g
/-- `w₁ = (1 - B·w₃)/A`. -/
noncomputable def asZwA1 (D : Work.MotV.KleinData 𝕜) (g : K) : OmA K D :=
  (1 - asZBA D g * asZwA3 D g) / asZAA D g
/-- `w₂ = (X₀ - C·w₄)/A`. -/
noncomputable def asZwA2 (D : Work.MotV.KleinData 𝕜) (g : K) : OmA K D :=
  (asZXA D g 0 - asZCA D g * asZwA4 D g) / asZAA D g

/-- The recovered chart vector `w = (0, w₁, w₂, w₃, w₄)`. -/
noncomputable def asZwA (D : Work.MotV.KleinData 𝕜) (g : K) : Fin 5 → OmA K D :=
  ![0, asZwA1 D g, asZwA2 D g, asZwA3 D g, asZwA4 D g]

/-! ## §4 Membership in the twist field -/

theorem asZvA_mem (D : Work.MotV.KleinData 𝕜) (g : K) (j : Fin 5) :
    asZvA D g j ∈ twistFieldAS D g := by
  rw [asZvA]
  exact IntermediateField.subset_adjoin K _ (Set.mem_range_self j)

theorem asZOmA_mem (D : Work.MotV.KleinData 𝕜) (g : K) (k : Fin 5) :
    asZOmA D g k ∈ twistFieldAS D g := by
  unfold asZOmA
  refine Subalgebra.sum_mem _ (fun j _ => ?_)
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (asZvA_mem D g j)

/-! ## §5 The residual coordinates as linear forms in `v` -/

theorem asZOmA_zero_eq (D : Work.MotV.KleinData 𝕜) (g : K) :
    asZOmA D g 0 = asZAA D g * asZvA D g 1 + asZBA D g * asZvA D g 3 := by
  simp only [asZOmA, asZAA, asZBA, asZvA, Fin.sum_univ_five, phiAS_00, phiAS_01, phiAS_02, phiAS_03, phiAS_04, phiAS_10, phiAS_11, phiAS_12, phiAS_13, phiAS_14, phiAS_20, phiAS_21, phiAS_22, phiAS_23, phiAS_24, phiAS_30, phiAS_31, phiAS_32, phiAS_33, phiAS_34, phiAS_40, phiAS_41, phiAS_42, phiAS_43, phiAS_44, map_zero, zero_mul, mul_zero, add_zero, zero_add]

theorem asZOmA_one_eq (D : Work.MotV.KleinData 𝕜) (g : K) :
    asZOmA D g 1 = asZAA D g * asZvA D g 2 + asZCA D g * asZvA D g 4 := by
  simp only [asZOmA, asZAA, asZCA, asZvA, Fin.sum_univ_five, phiAS_00, phiAS_01, phiAS_02, phiAS_03, phiAS_04, phiAS_10, phiAS_11, phiAS_12, phiAS_13, phiAS_14, phiAS_20, phiAS_21, phiAS_22, phiAS_23, phiAS_24, phiAS_30, phiAS_31, phiAS_32, phiAS_33, phiAS_34, phiAS_40, phiAS_41, phiAS_42, phiAS_43, phiAS_44, map_zero, zero_mul, mul_zero, add_zero, zero_add]

theorem asZOmA_two_eq (D : Work.MotV.KleinData 𝕜) (g : K) :
    asZOmA D g 2 = asZDA D g * asZvA D g 3 := by
  simp only [asZOmA, asZDA, asZvA, Fin.sum_univ_five, phiAS_00, phiAS_01, phiAS_02, phiAS_03, phiAS_04, phiAS_10, phiAS_11, phiAS_12, phiAS_13, phiAS_14, phiAS_20, phiAS_21, phiAS_22, phiAS_23, phiAS_24, phiAS_30, phiAS_31, phiAS_32, phiAS_33, phiAS_34, phiAS_40, phiAS_41, phiAS_42, phiAS_43, phiAS_44, map_zero, zero_mul, mul_zero, add_zero, zero_add]

theorem asZOmA_three_eq (D : Work.MotV.KleinData 𝕜) (g : K) :
    asZOmA D g 3 = asZEA D g * asZvA D g 4 := by
  simp only [asZOmA, asZEA, asZvA, Fin.sum_univ_five, phiAS_00, phiAS_01, phiAS_02, phiAS_03, phiAS_04, phiAS_10, phiAS_11, phiAS_12, phiAS_13, phiAS_14, phiAS_20, phiAS_21, phiAS_22, phiAS_23, phiAS_24, phiAS_30, phiAS_31, phiAS_32, phiAS_33, phiAS_34, phiAS_40, phiAS_41, phiAS_42, phiAS_43, phiAS_44, map_zero, zero_mul, mul_zero, add_zero, zero_add]

theorem asZOmA_four_eq (D : Work.MotV.KleinData 𝕜) (g : K) : asZOmA D g 4 = 0 := by
  simp only [asZOmA, Fin.sum_univ_five, phiAS_00, phiAS_01, phiAS_02, phiAS_03, phiAS_04, phiAS_10, phiAS_11, phiAS_12, phiAS_13, phiAS_14, phiAS_20, phiAS_21, phiAS_22, phiAS_23, phiAS_24, phiAS_30, phiAS_31, phiAS_32, phiAS_33, phiAS_34, phiAS_40, phiAS_41, phiAS_42, phiAS_43, phiAS_44, map_zero, zero_mul, mul_zero, add_zero, zero_add]

/-! ## §6 Nonvanishing of the chart coefficients under `ASGood` -/

theorem asZAA_ne_zero (D : Work.MotV.KleinData 𝕜) (g : K)
    (hD : Work.MotV5.KleinData.ASGood D) : asZAA D g ≠ 0 := by
  rw [asZAA, phiAS_01]
  intro h
  have h2 : (3 : K) * aK K D + bK K D = 0 :=
    (algebraMap K (OmA K D)).injective (by rw [h, map_zero])
  exact three_mul_add_ne_zero (aK K D) (bK K D) (aK_sq_sub_ne D hD) h2

theorem asZDA_ne_zero (D : Work.MotV.KleinData 𝕜) (g : K)
    (hD : Work.MotV5.KleinData.ASGood D) : asZDA D g ≠ 0 := by
  rw [asZDA, phiAS_23]
  intro h
  have h2 : aK K D + 2 * bK K D = 0 :=
    (algebraMap K (OmA K D)).injective (by rw [h, map_zero])
  exact add_two_mul_ne_zero (aK K D) (bK K D) (aK_sq_sub_ne D hD) h2

theorem asZEA_ne_zero (D : Work.MotV.KleinData 𝕜) (g : K)
    (hD : Work.MotV5.KleinData.ASGood D) : asZEA D g ≠ 0 := by
  rw [asZEA, phiAS_34]
  intro h
  have h2 : 4 * aK K D + 3 * bK K D = 0 :=
    (algebraMap K (OmA K D)).injective (by rw [h, map_zero])
  exact four_mul_add_three_mul_ne_zero (aK K D) (bK K D) (aK_sq_sub_ne D hD) h2

theorem asZmuA_ne_zero (D : Work.MotV.KleinData 𝕜) (g : K)
    (hD : Work.MotV5.KleinData.ASGood D) : asZmuA D g ≠ 0 := by
  rw [asZmuA]
  intro h
  have h' : (2 : K) * (aK K D ^ 2 - aK K D * bK K D - bK K D ^ 2) = 0 :=
    (algebraMap K (OmA K D)).injective (by rw [h, map_zero])
  have h2 : (2 : K) ≠ 0 := by
    intro hh
    have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
    have h32 : (3 : K) * 2 = 1 := by linear_combination h5
    rw [hh, mul_zero] at h32
    exact one_ne_zero h32.symm
  rcases mul_eq_zero.mp h' with hzero | hd
  · exact absurd hzero h2
  · exact aK_sq_sub_ne D hD hd

end Work.MotV5.Contrib
