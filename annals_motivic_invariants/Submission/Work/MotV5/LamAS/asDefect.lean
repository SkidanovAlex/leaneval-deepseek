import Mathlib
import Submission.Work.MotV5.LamAS.asPsi
import Submission.Work.MotT.coeffAut_conj_trans

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# The Galois defect of the comparison point (C4 of the LAM node)

Let `K = RatFunc 𝕜`, `L = asL2 f₁ f₂` the two-root Artin–Schreier field, `M = asML D f₁ f₂ = L(E)`
the function field of the Klein model base changed to `L`, and `Ω = kleinField D ⊔ LImage D L`.

The two twisted Galois actions of the class of `gᵢ` are
`ψᵢ(γ) = σS'^(χᵢ(γ)) ∘ γ̃` where `γ̃ = asCoeff D f₁ f₂ γ` is the coefficient action, `χᵢ(γ)` the
Artin–Schreier shift of a root `Wᵢ` of `X⁵ - X - gᵢ` and `σS' = τ_T` the fifth-torsion shift.
The comparison `Θ ψ₁ = ψ₂ Θ` with `Θ = τ_Q ∘ [-1]^ε` forces the Galois defect of the point `Q`:

`γ Q - Q = ((-1)^ε · χ₁(γ) - χ₂(γ)) • T`.

The proof is the concrete computation on the two generators `x = genX E` and `y = genY E` of
`M = L(x, y)`: applying the comparison to `x` and `y` and evaluating the coefficient action via the
addition formulae (`Work.MotT.map_transX`, `Work.MotT.map_transY`) produces
`τ_A = τ_B` with `A = Q + (-1)^ε • (χ₁ • T)` and `B = χ₂ • T + γQ`, and `Q ↦ τ_Q` is injective.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace Work.MotV5.LamAS

open WeierstrassCurve WeierstrassCurve.Affine

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-! ## §1 `Point.map` does not depend on the scalar structure -/

private theorem point_map_smul_eq {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    [DecidableEq ↥(asL2 (𝕜 := 𝕜) f₁ f₂)]
    [hEll : (asE2 D f₁ f₂).IsElliptic]
    (R : (asE2 D f₁ f₂).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
        (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
        (γ.restrictScalars 𝕜).toAlgHom R
      = WeierstrassCurve.Affine.Point.map (W' := D.E) (S := RatFunc 𝕜)
        (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
        γ.toAlgHom R := rfl

/-! ## §2 Bridging `Work.MotV` and `Work.MotC2` coordinates -/

private lemma motC2_genX_eq' {L : Type} [Field L] (E : WeierstrassCurve L) :
    Work.MotC2.genX E = Work.MotV.genX E := by
  rw [Work.MotC2.genX, Work.MotV.genX, Work.MotC2.coordX_eq_mk]

private lemma motC2_genY_eq' {L : Type} [Field L] (E : WeierstrassCurve L) :
    Work.MotC2.genY E = Work.MotV.genY E := by
  rw [Work.MotC2.genY, Work.MotV.genY, Work.MotC2.coordY]
  rfl

private lemma motC2_genX_eq {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (f₁ f₂ : RatFunc 𝕜) :
    Work.MotC2.genX (asE2 D f₁ f₂) = Work.MotV.genX (asE2 D f₁ f₂) :=
  motC2_genX_eq' (asE2 D f₁ f₂)

private lemma motC2_genY_eq {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (f₁ f₂ : RatFunc 𝕜) :
    Work.MotC2.genY (asE2 D f₁ f₂) = Work.MotV.genY (asE2 D f₁ f₂) :=
  motC2_genY_eq' (asE2 D f₁ f₂)

private lemma negAlgEquiv_genX_motv {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (f₁ f₂ : RatFunc 𝕜) :
    Work.MotC2.negAlgEquiv (asE2 D f₁ f₂) (Work.MotV.genX (asE2 D f₁ f₂)) =
      Work.MotV.genX (asE2 D f₁ f₂) := by
  rw [← motC2_genX_eq D f₁ f₂, Work.MotC2.negAlgEquiv_genX]

private lemma negAlgEquiv_genY_motv {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (f₁ f₂ : RatFunc 𝕜) :
    Work.MotC2.negAlgEquiv (asE2 D f₁ f₂) (Work.MotV.genY (asE2 D f₁ f₂)) =
      - Work.MotV.genY (asE2 D f₁ f₂) -
        algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) ((asE2 D f₁ f₂).a₁) *
          Work.MotV.genX (asE2 D f₁ f₂) -
        algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) ((asE2 D f₁ f₂).a₃) := by
  rw [← motC2_genY_eq D f₁ f₂, ← motC2_genX_eq D f₁ f₂, Work.MotC2.negAlgEquiv_genY]

/-! ## §3 The coefficient action fixes the base coefficients -/

private lemma gamma_fixes_base {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (c : 𝕜) :
    γ (algebraMap 𝕜 ↥(asL2 (𝕜 := 𝕜) f₁ f₂) c) = algebraMap 𝕜 ↥(asL2 (𝕜 := 𝕜) f₁ f₂) c := by
  rw [IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂), γ.commutes]

private lemma asCoeff_fixes_baseCoeff {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (c : 𝕜) :
    asCoeff D f₁ f₂ γ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂)
        (algebraMap 𝕜 ↥(asL2 (𝕜 := 𝕜) f₁ f₂) c)) =
      algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂)
        (algebraMap 𝕜 ↥(asL2 (𝕜 := 𝕜) f₁ f₂) c) := by
  rw [asCoeff_algebraMap, gamma_fixes_base f₁ f₂ γ c]

private lemma asCoeff_fixes_a1 {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :
    asCoeff D f₁ f₂ γ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂)
        ((D.E.baseChange ↥(asL2 (𝕜 := 𝕜) f₁ f₂)).a₁)) =
      algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂)
        ((D.E.baseChange ↥(asL2 (𝕜 := 𝕜) f₁ f₂)).a₁) := by
  show asCoeff D f₁ f₂ γ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂)
        (algebraMap 𝕜 ↥(asL2 (𝕜 := 𝕜) f₁ f₂) D.E.a₁)) =
      algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂)
        (algebraMap 𝕜 ↥(asL2 (𝕜 := 𝕜) f₁ f₂) D.E.a₁)
  exact asCoeff_fixes_baseCoeff D f₁ f₂ γ D.E.a₁

private lemma asCoeff_fixes_a3 {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :
    asCoeff D f₁ f₂ γ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂)
        ((D.E.baseChange ↥(asL2 (𝕜 := 𝕜) f₁ f₂)).a₃)) =
      algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂)
        ((D.E.baseChange ↥(asL2 (𝕜 := 𝕜) f₁ f₂)).a₃) := by
  show asCoeff D f₁ f₂ γ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂)
        (algebraMap 𝕜 ↥(asL2 (𝕜 := 𝕜) f₁ f₂) D.E.a₃)) =
      algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂)
        (algebraMap 𝕜 ↥(asL2 (𝕜 := 𝕜) f₁ f₂) D.E.a₃)
  exact asCoeff_fixes_baseCoeff D f₁ f₂ γ D.E.a₃

/-! ## §4 The coefficient action commutes with `[-1]` -/

private lemma coeff_neg_comm {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    [DecidableEq ↥(asL2 (𝕜 := 𝕜) f₁ f₂)] (x : asML D f₁ f₂) :
    asCoeff D f₁ f₂ γ (Work.MotC2.negAlgEquiv (asE2 D f₁ f₂) x) =
      Work.MotC2.negAlgEquiv (asE2 D f₁ f₂) (asCoeff D f₁ f₂ γ x) := by
  have key : ((asCoeff D f₁ f₂ γ).restrictScalars 𝕜).toAlgHom.comp
        ((Work.MotC2.negAlgEquiv (asE2 D f₁ f₂)).restrictScalars 𝕜).toAlgHom =
      ((Work.MotC2.negAlgEquiv (asE2 D f₁ f₂)).restrictScalars 𝕜).toAlgHom.comp
        ((asCoeff D f₁ f₂ γ).restrictScalars 𝕜).toAlgHom := by
    refine Work.MotT.ext_of_genX_genY_algebraMap (K := 𝕜)
      (L := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) D.E ?_ ?_ ?_
    · intro l
      show asCoeff D f₁ f₂ γ (Work.MotC2.negAlgEquiv (asE2 D f₁ f₂)
            (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l)) =
        Work.MotC2.negAlgEquiv (asE2 D f₁ f₂)
            (asCoeff D f₁ f₂ γ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l))
      rw [(Work.MotC2.negAlgEquiv (asE2 D f₁ f₂)).commutes l, asCoeff_algebraMap,
        (Work.MotC2.negAlgEquiv (asE2 D f₁ f₂)).commutes (γ l)]
    · show asCoeff D f₁ f₂ γ (Work.MotC2.negAlgEquiv (asE2 D f₁ f₂)
            (Work.MotC2.genX (asE2 D f₁ f₂))) =
        Work.MotC2.negAlgEquiv (asE2 D f₁ f₂)
          (asCoeff D f₁ f₂ γ (Work.MotC2.genX (asE2 D f₁ f₂)))
      rw [Work.MotC2.negAlgEquiv_genX, motC2_genX_eq D f₁ f₂, asCoeff_genX,
        ← motC2_genX_eq D f₁ f₂, Work.MotC2.negAlgEquiv_genX]
    · show asCoeff D f₁ f₂ γ (Work.MotC2.negAlgEquiv (asE2 D f₁ f₂)
            (Work.MotC2.genY (asE2 D f₁ f₂))) =
        Work.MotC2.negAlgEquiv (asE2 D f₁ f₂)
          (asCoeff D f₁ f₂ γ (Work.MotC2.genY (asE2 D f₁ f₂)))
      rw [motC2_genY_eq D f₁ f₂, negAlgEquiv_genY_motv D f₁ f₂]
      rw [map_sub, map_sub, map_mul, map_neg]
      rw [asCoeff_genY, asCoeff_fixes_a1 D f₁ f₂ γ, asCoeff_genX,
        asCoeff_fixes_a3 D f₁ f₂ γ]
      rw [negAlgEquiv_genY_motv D f₁ f₂]
  exact DFunLike.congr_fun key x

/-! ## §5 The coefficient action on the translates of the generic point -/

private lemma coeff_apply_transX {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    [DecidableEq ↥(asL2 (𝕜 := 𝕜) f₁ f₂)] [hEll : (asE2 D f₁ f₂).IsElliptic]
    (R : (asE2 D f₁ f₂).toAffine.Point) :
    asCoeff D f₁ f₂ γ (Work.MotC2.transX (asE2 D f₁ f₂) R) =
      Work.MotC2.transX (asE2 D f₁ f₂)
        (WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
          (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
          (γ.restrictScalars 𝕜).toAlgHom R) :=
  Work.MotT.map_transX (K := 𝕜) (L := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) D.E (γ.restrictScalars 𝕜)
    ((asCoeff D f₁ f₂ γ).restrictScalars 𝕜)
    (fun l => asCoeff_algebraMap D f₁ f₂ γ l)
    (by rw [AlgEquiv.restrictScalars_apply, motC2_genX_eq]; exact asCoeff_genX D f₁ f₂ γ)
    (by rw [AlgEquiv.restrictScalars_apply, motC2_genY_eq]; exact asCoeff_genY D f₁ f₂ γ)
    R

private lemma coeff_apply_transY {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    [DecidableEq ↥(asL2 (𝕜 := 𝕜) f₁ f₂)] [hEll : (asE2 D f₁ f₂).IsElliptic]
    (R : (asE2 D f₁ f₂).toAffine.Point) :
    asCoeff D f₁ f₂ γ (Work.MotC2.transY (asE2 D f₁ f₂) R) =
      Work.MotC2.transY (asE2 D f₁ f₂)
        (WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
          (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
          (γ.restrictScalars 𝕜).toAlgHom R) :=
  Work.MotT.map_transY (K := 𝕜) (L := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) D.E (γ.restrictScalars 𝕜)
    ((asCoeff D f₁ f₂ γ).restrictScalars 𝕜)
    (fun l => asCoeff_algebraMap D f₁ f₂ γ l)
    (by rw [AlgEquiv.restrictScalars_apply, motC2_genX_eq]; exact asCoeff_genX D f₁ f₂ γ)
    (by rw [AlgEquiv.restrictScalars_apply, motC2_genY_eq]; exact asCoeff_genY D f₁ f₂ γ)
    R

private lemma coeff_apply_negY {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    [DecidableEq ↥(asL2 (𝕜 := 𝕜) f₁ f₂)] [hEll : (asE2 D f₁ f₂).IsElliptic]
    (R : (asE2 D f₁ f₂).toAffine.Point) :
    asCoeff D f₁ f₂ γ
      (- Work.MotC2.transY (asE2 D f₁ f₂) R
        - algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) ((asE2 D f₁ f₂).a₁) *
            Work.MotC2.transX (asE2 D f₁ f₂) R
        - algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) ((asE2 D f₁ f₂).a₃)) =
      (- Work.MotC2.transY (asE2 D f₁ f₂)
          (WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
            (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
            (γ.restrictScalars 𝕜).toAlgHom R)
        - algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) ((asE2 D f₁ f₂).a₁) *
            Work.MotC2.transX (asE2 D f₁ f₂)
              (WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
                (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
                (γ.restrictScalars 𝕜).toAlgHom R)
        - algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) ((asE2 D f₁ f₂).a₃)) := by
  rw [map_sub, map_sub, map_mul, map_neg, coeff_apply_transY, coeff_apply_transX,
    asCoeff_fixes_a1 D f₁ f₂ γ, asCoeff_fixes_a3 D f₁ f₂ γ]

/-! ## §6 The action of `Θ = τ_Q * [-1]^ε` on the generators -/

private lemma transAlgEquiv_genX' {L : Type} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (P : E.toAffine.Point) :
    (Work.MotC2.transAlgEquiv E P) (Work.MotC2.genX E) = Work.MotC2.transX E P := by
  rw [Work.MotC2.transAlgEquiv_apply, Work.MotC2.phi_genX]

private lemma transAlgEquiv_genY' {L : Type} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (P : E.toAffine.Point) :
    (Work.MotC2.transAlgEquiv E P) (Work.MotC2.genY E) = Work.MotC2.transY E P := by
  rw [Work.MotC2.transAlgEquiv_apply, Work.MotC2.phi_genY]

private lemma transAlgEquiv_genX_motv {L : Type} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (P : E.toAffine.Point) :
    (Work.MotC2.transAlgEquiv E P) (Work.MotV.genX E) = Work.MotC2.transX E P := by
  rw [← motC2_genX_eq' E, Work.MotC2.transAlgEquiv_apply, Work.MotC2.phi_genX]

private lemma transAlgEquiv_genY_motv {L : Type} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (P : E.toAffine.Point) :
    (Work.MotC2.transAlgEquiv E P) (Work.MotV.genY E) = Work.MotC2.transY E P := by
  rw [← motC2_genY_eq' E, Work.MotC2.transAlgEquiv_apply, Work.MotC2.phi_genY]

private lemma transAlgEquiv_transX {L : Type} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (P S : E.toAffine.Point) :
    (Work.MotC2.transAlgEquiv E P) (Work.MotC2.transX E S) = Work.MotC2.transX E (P + S) := by
  rw [Work.MotC2.transAlgEquiv_apply, Work.MotC2.phi_transX]

private lemma transAlgEquiv_transY {L : Type} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (P S : E.toAffine.Point) :
    (Work.MotC2.transAlgEquiv E P) (Work.MotC2.transY E S) = Work.MotC2.transY E (P + S) := by
  rw [Work.MotC2.transAlgEquiv_apply, Work.MotC2.phi_transY]

private lemma trans_apply_negY {L : Type} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (P R : E.toAffine.Point) :
    (Work.MotC2.transAlgEquiv E P)
      (- Work.MotC2.transY E R - algebraMap L (Work.MotC2.Func E) E.a₁ * Work.MotC2.transX E R
        - algebraMap L (Work.MotC2.Func E) E.a₃) =
      (- Work.MotC2.transY E (P + R)
        - algebraMap L (Work.MotC2.Func E) E.a₁ * Work.MotC2.transX E (P + R)
        - algebraMap L (Work.MotC2.Func E) E.a₃) := by
  rw [map_sub, map_sub, map_mul, map_neg, transAlgEquiv_transY, transAlgEquiv_transX,
    AlgEquiv.commutes, AlgEquiv.commutes]

private lemma transAlgEquiv_pow {L : Type} [Field L] [DecidableEq L]
    (E : WeierstrassCurve L) [E.IsElliptic] (T : E.toAffine.Point) (n : ℕ) :
    (Work.MotC2.transAlgEquiv E T) ^ n = Work.MotC2.transAlgEquiv E (n • T) := by
  induction n with
  | zero => rw [zero_nsmul, Work.MotC2.transAlgEquiv_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, Work.MotC2.transAlgEquiv_add, pow_succ, ih]

private lemma negAlgEquiv_pow_transX {L : Type} [Field L] [DecidableEq L]
    (E : WeierstrassCurve L) [E.IsElliptic] (ε : Fin 2) (S : E.toAffine.Point) :
    (Work.MotC2.negAlgEquiv E ^ (ε : ℕ)) (Work.MotC2.transX E S) =
      Work.MotC2.transX E (((-1 : ℤ) ^ (ε : ℕ)) • S) := by
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by omega
  rcases hε with h | h
  · rw [h]; simp
  · rw [h, pow_one]
    have h2 : ((-1 : ℤ) ^ (1 : ℕ)) = -1 := by norm_num
    rw [h2, neg_one_smul, Work.MotC2.negAlgEquiv_transX]

private lemma neg_pow_mul_trans_eq {L : Type} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (A : E.toAffine.Point) (ε : Fin 2) :
    (Work.MotC2.negAlgEquiv E) ^ (ε : ℕ) *
        Work.MotC2.transAlgEquiv E (((-1 : ℤ) ^ (ε : ℕ)) • A) =
      Work.MotC2.transAlgEquiv E A * (Work.MotC2.negAlgEquiv E) ^ (ε : ℕ) := by
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by omega
  rcases hε with h | h
  · rw [h]; simp
  · rw [h, pow_one, pow_one]
    rw [neg_one_smul]
    have h3 := Work.MotC2.negAlgEquiv_mul_transAlgEquiv E (-A)
    simpa using h3

private lemma theta_transX_apply {L : Type} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (Q : E.toAffine.Point) (ε : Fin 2) (S : E.toAffine.Point) :
    (Work.MotC2.transAlgEquiv E Q * Work.MotC2.negAlgEquiv E ^ (ε : ℕ))
        (Work.MotC2.transX E S) =
      Work.MotC2.transX E (Q + (((-1 : ℤ) ^ (ε : ℕ)) • S)) := by
  rw [AlgEquiv.mul_apply, negAlgEquiv_pow_transX, transAlgEquiv_transX]

private lemma negAlgEquiv_pow_genX_motv {L : Type} [Field L] (E : WeierstrassCurve L)
    (ε : Fin 2) :
    (Work.MotC2.negAlgEquiv E ^ (ε : ℕ)) (Work.MotV.genX E) = Work.MotV.genX E := by
  rw [← motC2_genX_eq' E]
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by omega
  rcases hε with h | h
  · rw [h]; simp
  · rw [h, pow_one, Work.MotC2.negAlgEquiv_genX]

private lemma theta_genX {L : Type} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (Q : E.toAffine.Point) (ε : Fin 2) :
    (Work.MotC2.transAlgEquiv E Q * Work.MotC2.negAlgEquiv E ^ (ε : ℕ))
        (Work.MotV.genX E) = Work.MotC2.transX E Q := by
  rw [AlgEquiv.mul_apply, negAlgEquiv_pow_genX_motv, Work.MotC2.transAlgEquiv_apply,
    ← motC2_genX_eq' E, Work.MotC2.phi_genX]

private lemma theta_genY_one {L : Type} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (Q : E.toAffine.Point) (ε : Fin 2) (hε : (ε : ℕ) = 1) :
    (Work.MotC2.transAlgEquiv E Q * Work.MotC2.negAlgEquiv E ^ (ε : ℕ))
        (Work.MotV.genY E) =
      - Work.MotC2.transY E Q - algebraMap L (Work.MotC2.Func E) E.a₁ * Work.MotC2.transX E Q
        - algebraMap L (Work.MotC2.Func E) E.a₃ := by
  rw [← motC2_genY_eq' E]
  rw [hε, pow_one, AlgEquiv.mul_apply, Work.MotC2.negAlgEquiv_genY]
  rw [show (- Work.MotC2.genY E - algebraMap L (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E
        - algebraMap L (Work.MotC2.Func E) E.a₃) =
      (- Work.MotC2.transY E WeierstrassCurve.Affine.Point.zero
        - algebraMap L (Work.MotC2.Func E) E.a₁ * Work.MotC2.transX E WeierstrassCurve.Affine.Point.zero
        - algebraMap L (Work.MotC2.Func E) E.a₃) from by
    rw [Work.MotC2.transY_zero, Work.MotC2.transX_zero]]
  rw [trans_apply_negY]
  simp only [← WeierstrassCurve.Affine.Point.zero_def, add_zero]

private lemma theta_transY_one {L : Type} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (Q : E.toAffine.Point) (ε : Fin 2) (hε : (ε : ℕ) = 1)
    (S : E.toAffine.Point) :
    (Work.MotC2.transAlgEquiv E Q * Work.MotC2.negAlgEquiv E ^ (ε : ℕ))
        (Work.MotC2.transY E S) =
      - Work.MotC2.transY E (Q + (((-1 : ℤ) ^ (ε : ℕ)) • S))
        - algebraMap L (Work.MotC2.Func E) E.a₁ *
            Work.MotC2.transX E (Q + (((-1 : ℤ) ^ (ε : ℕ)) • S))
        - algebraMap L (Work.MotC2.Func E) E.a₃ := by
  rw [hε, pow_one, AlgEquiv.mul_apply, Work.MotC2.negAlgEquiv_transY]
  have h2 : ((-1 : ℤ) ^ (1 : ℕ)) = -1 := by norm_num
  rw [h2, neg_one_smul, trans_apply_negY]

/-! ## §7 The twisted Galois action applied to the translates -/

private lemma psi_apply_genX {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (f₁ f₂ g : RatFunc 𝕜)
    (σS' : asML D f₁ f₂ ≃ₐ[↥(asL2 (𝕜 := 𝕜) f₁ f₂)] asML D f₁ f₂)
    (W : ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (hW : W ^ 5 - W = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) g)
    [DecidableEq ↥(asL2 (𝕜 := 𝕜) f₁ f₂)] [hEll : (asE2 D f₁ f₂).IsElliptic]
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (T : (asE2 D f₁ f₂).toAffine.Point)
    (hσS' : σS' = Work.MotC2.transAlgEquiv (asE2 D f₁ f₂) T) :
    asPsi D f₁ f₂ g σS' W hW γ (Work.MotV.genX (asE2 D f₁ f₂)) =
      Work.MotC2.transX (asE2 D f₁ f₂) (((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ) • T) := by
  simp only [asPsi, AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply]
  rw [asCoeff_genX, hσS']
  have h : ((Work.MotC2.transAlgEquiv (asE2 D f₁ f₂) T) ^
        ((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ))
        (Work.MotV.genX (asE2 D f₁ f₂)) =
      Work.MotC2.transX (asE2 D f₁ f₂) (((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ) • T) := by
    rw [transAlgEquiv_pow]
    exact transAlgEquiv_genX' (asE2 D f₁ f₂) _
  exact h

private lemma psi_apply_genY {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (f₁ f₂ g : RatFunc 𝕜)
    (σS' : asML D f₁ f₂ ≃ₐ[↥(asL2 (𝕜 := 𝕜) f₁ f₂)] asML D f₁ f₂)
    (W : ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (hW : W ^ 5 - W = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) g)
    [DecidableEq ↥(asL2 (𝕜 := 𝕜) f₁ f₂)] [hEll : (asE2 D f₁ f₂).IsElliptic]
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (T : (asE2 D f₁ f₂).toAffine.Point)
    (hσS' : σS' = Work.MotC2.transAlgEquiv (asE2 D f₁ f₂) T) :
    asPsi D f₁ f₂ g σS' W hW γ (Work.MotV.genY (asE2 D f₁ f₂)) =
      Work.MotC2.transY (asE2 D f₁ f₂) (((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ) • T) := by
  simp only [asPsi, AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply]
  rw [asCoeff_genY, hσS']
  have h : ((Work.MotC2.transAlgEquiv (asE2 D f₁ f₂) T) ^
        ((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ))
        (Work.MotV.genY (asE2 D f₁ f₂)) =
      Work.MotC2.transY (asE2 D f₁ f₂) (((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ) • T) := by
    rw [transAlgEquiv_pow]
    exact transAlgEquiv_genY' (asE2 D f₁ f₂) _
  exact h

private lemma psi_apply_transX {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (f₁ f₂ g : RatFunc 𝕜)
    (σS' : asML D f₁ f₂ ≃ₐ[↥(asL2 (𝕜 := 𝕜) f₁ f₂)] asML D f₁ f₂)
    (W : ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (hW : W ^ 5 - W = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) g)
    [DecidableEq ↥(asL2 (𝕜 := 𝕜) f₁ f₂)] [hEll : (asE2 D f₁ f₂).IsElliptic]
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (T : (asE2 D f₁ f₂).toAffine.Point)
    (hσS' : σS' = Work.MotC2.transAlgEquiv (asE2 D f₁ f₂) T)
    (R : (asE2 D f₁ f₂).toAffine.Point) :
    asPsi D f₁ f₂ g σS' W hW γ (Work.MotC2.transX (asE2 D f₁ f₂) R) =
      Work.MotC2.transX (asE2 D f₁ f₂)
        ((((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ) • T) +
          WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
            (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
            (γ.restrictScalars 𝕜).toAlgHom R) := by
  simp only [asPsi, AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply]
  rw [coeff_apply_transX, hσS']
  have h : ((Work.MotC2.transAlgEquiv (asE2 D f₁ f₂) T) ^
        ((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ))
        (Work.MotC2.transX (asE2 D f₁ f₂)
          (WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
            (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
            (γ.restrictScalars 𝕜).toAlgHom R)) =
      Work.MotC2.transX (asE2 D f₁ f₂)
        ((((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ) • T) +
          WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
            (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
            (γ.restrictScalars 𝕜).toAlgHom R) := by
    rw [transAlgEquiv_pow, transAlgEquiv_transX]
  exact h

private lemma psi_apply_transY {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (f₁ f₂ g : RatFunc 𝕜)
    (σS' : asML D f₁ f₂ ≃ₐ[↥(asL2 (𝕜 := 𝕜) f₁ f₂)] asML D f₁ f₂)
    (W : ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (hW : W ^ 5 - W = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) g)
    [DecidableEq ↥(asL2 (𝕜 := 𝕜) f₁ f₂)] [hEll : (asE2 D f₁ f₂).IsElliptic]
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (T : (asE2 D f₁ f₂).toAffine.Point)
    (hσS' : σS' = Work.MotC2.transAlgEquiv (asE2 D f₁ f₂) T)
    (R : (asE2 D f₁ f₂).toAffine.Point) :
    asPsi D f₁ f₂ g σS' W hW γ (Work.MotC2.transY (asE2 D f₁ f₂) R) =
      Work.MotC2.transY (asE2 D f₁ f₂)
        ((((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ) • T) +
          WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
            (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
            (γ.restrictScalars 𝕜).toAlgHom R) := by
  simp only [asPsi, AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply]
  rw [coeff_apply_transY, hσS']
  have h : ((Work.MotC2.transAlgEquiv (asE2 D f₁ f₂) T) ^
        ((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ))
        (Work.MotC2.transY (asE2 D f₁ f₂)
          (WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
            (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
            (γ.restrictScalars 𝕜).toAlgHom R)) =
      Work.MotC2.transY (asE2 D f₁ f₂)
        ((((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ) • T) +
          WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
            (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
            (γ.restrictScalars 𝕜).toAlgHom R) := by
    rw [transAlgEquiv_pow, transAlgEquiv_transY]
  exact h

private lemma psi_apply_negY {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (f₁ f₂ g : RatFunc 𝕜)
    (σS' : asML D f₁ f₂ ≃ₐ[↥(asL2 (𝕜 := 𝕜) f₁ f₂)] asML D f₁ f₂)
    (W : ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (hW : W ^ 5 - W = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) g)
    [DecidableEq ↥(asL2 (𝕜 := 𝕜) f₁ f₂)] [hEll : (asE2 D f₁ f₂).IsElliptic]
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (T : (asE2 D f₁ f₂).toAffine.Point)
    (hσS' : σS' = Work.MotC2.transAlgEquiv (asE2 D f₁ f₂) T)
    (R : (asE2 D f₁ f₂).toAffine.Point) :
    asPsi D f₁ f₂ g σS' W hW γ
      (- Work.MotC2.transY (asE2 D f₁ f₂) R
        - algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) ((asE2 D f₁ f₂).a₁) *
            Work.MotC2.transX (asE2 D f₁ f₂) R
        - algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) ((asE2 D f₁ f₂).a₃)) =
      (- Work.MotC2.transY (asE2 D f₁ f₂)
          ((((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ) • T) +
            WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
              (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
              (γ.restrictScalars 𝕜).toAlgHom R)
        - algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) ((asE2 D f₁ f₂).a₁) *
            Work.MotC2.transX (asE2 D f₁ f₂)
              ((((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ) • T) +
                WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
                  (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
                  (γ.restrictScalars 𝕜).toAlgHom R)
        - algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) ((asE2 D f₁ f₂).a₃)) := by
  simp only [asPsi, AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply]
  rw [coeff_apply_negY, hσS']
  have h : ((Work.MotC2.transAlgEquiv (asE2 D f₁ f₂) T) ^
        ((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ))
        (- Work.MotC2.transY (asE2 D f₁ f₂)
            (WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
              (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
              (γ.restrictScalars 𝕜).toAlgHom R)
          - algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) ((asE2 D f₁ f₂).a₁) *
              Work.MotC2.transX (asE2 D f₁ f₂)
                (WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
                  (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
                  (γ.restrictScalars 𝕜).toAlgHom R)
          - algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) ((asE2 D f₁ f₂).a₃)) =
      (- Work.MotC2.transY (asE2 D f₁ f₂)
          ((((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ) • T) +
            WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
              (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
              (γ.restrictScalars 𝕜).toAlgHom R)
        - algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) ((asE2 D f₁ f₂).a₁) *
            Work.MotC2.transX (asE2 D f₁ f₂)
              ((((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ) • T) +
                WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
                  (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
                  (γ.restrictScalars 𝕜).toAlgHom R)
        - algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) ((asE2 D f₁ f₂).a₃)) := by
    rw [transAlgEquiv_pow, trans_apply_negY]
  exact h

/-! ## §8 The target -/

/-- The comparison `Θ ψ₁ = ψ₂ Θ` together with `Θ = τ_Q ∘ [-1]^ε` and `σS' = τ_T` gives the Galois defect of the point `Q`: `γ Q - Q = ((-1)^ε · χ₁(γ) - χ₂(γ)) • T`, where `χᵢ(γ)` is the Artin–Schreier shift of the root `Wᵢ`. -/
theorem asDefect (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (f₁ f₂ g₁ g₂ : RatFunc 𝕜)
    (τ₁ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σS' : Work.MotV5.LamAS.asML D f₁ f₂ ≃ₐ[↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)]
      Work.MotV5.LamAS.asML D f₁ f₂)
    (W₁ W₂ : ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂))
    (hW₁ : W₁ ^ 5 - W₁ = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂) g₁)
    (hW₂ : W₂ ^ 5 - W₂ = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂) g₂)
    [DecidableEq ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)]
    [hEll : (Work.MotV5.LamAS.asE2 D f₁ f₂).IsElliptic]
    (ε : Fin 2) (Q T : (Work.MotV5.LamAS.asE2 D f₁ f₂).toAffine.Point)
    (hσS' : σS' = Work.MotC2.transAlgEquiv (Work.MotV5.LamAS.asE2 D f₁ f₂) T)
    (Θ : Work.MotV5.LamAS.asML D f₁ f₂ ≃ₐ[↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)]
      Work.MotV5.LamAS.asML D f₁ f₂)
    (hΘ : Θ = Work.MotC2.transAlgEquiv (Work.MotV5.LamAS.asE2 D f₁ f₂) Q *
      (Work.MotC2.negAlgEquiv (Work.MotV5.LamAS.asE2 D f₁ f₂)) ^ (ε : ℕ))
    (hcomp : ∀ γ : ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜]
        ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂),
      Θ.restrictScalars (RatFunc 𝕜) * (Work.MotV5.LamAS.asPsi D f₁ f₂ g₁ σS' W₁ hW₁ γ) =
        (Work.MotV5.LamAS.asPsi D f₁ f₂ g₂ σS' W₂ hW₂ γ) * Θ.restrictScalars (RatFunc 𝕜))
    (γ : ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜]
      ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)) :
    WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
        (F := ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂))
        (K := ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂))
        (γ.restrictScalars 𝕜).toAlgHom Q - Q =
      ((-1 : ℤ) ^ (ε : ℕ) *
          ((Work.MotV5.LamAS.asShift D f₁ f₂ g₁ W₁ hW₁ γ : Fin 5) : ℤ) -
        ((Work.MotV5.LamAS.asShift D f₁ f₂ g₂ W₂ hW₂ γ : Fin 5) : ℤ)) • T := by
  classical
  -- The point `γ Q`.
  let σQ : (asE2 D f₁ f₂).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
      (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
      (γ.restrictScalars 𝕜).toAlgHom Q
  -- The two shifts.
  let n₁ : ℕ := ((asShift D f₁ f₂ g₁ W₁ hW₁ γ : Fin 5) : ℕ)
  let n₂ : ℕ := ((asShift D f₁ f₂ g₂ W₂ hW₂ γ : Fin 5) : ℕ)
  -- The pointwise form of the comparison.
  have hpt : ∀ z : asML D f₁ f₂, Θ (asPsi D f₁ f₂ g₁ σS' W₁ hW₁ γ z) =
      asPsi D f₁ f₂ g₂ σS' W₂ hW₂ γ (Θ z) := by
    intro z
    have h := DFunLike.congr_fun (hcomp γ) z
    simpa only [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply] using h
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by omega
  -- the `x`-coordinate equation
  have hx : Work.MotC2.transX (asE2 D f₁ f₂) (Q + (((-1 : ℤ) ^ (ε : ℕ)) • (n₁ • T))) =
      Work.MotC2.transX (asE2 D f₁ f₂) ((n₂ • T) + σQ) := by
    have h := hpt (Work.MotV.genX (asE2 D f₁ f₂))
    rw [psi_apply_genX D f₁ f₂ g₁ σS' W₁ hW₁ γ T hσS', hΘ, theta_transX_apply, theta_genX,
      psi_apply_transX D f₁ f₂ g₂ σS' W₂ hW₂ γ T hσS' Q] at h
    exact h
  -- the `y`-coordinate equation
  have hy : Work.MotC2.transY (asE2 D f₁ f₂) (Q + (((-1 : ℤ) ^ (ε : ℕ)) • (n₁ • T))) =
      Work.MotC2.transY (asE2 D f₁ f₂) ((n₂ • T) + σQ) := by
    rcases hε with hε0 | hε1
    · -- `ε = 0`
      have h := hpt (Work.MotV.genY (asE2 D f₁ f₂))
      rw [psi_apply_genY D f₁ f₂ g₁ σS' W₁ hW₁ γ T hσS', hΘ] at h
      rw [hε0, pow_zero, mul_one, transAlgEquiv_transY, transAlgEquiv_genY_motv] at h
      rw [psi_apply_transY D f₁ f₂ g₂ σS' W₂ hW₂ γ T hσS' Q] at h
      have hs : ((-1 : ℤ) ^ (ε : ℕ)) = 1 := by rw [hε0]; norm_num
      rw [hs, one_smul]
      exact h
    · -- `ε = 1`
      have h := hpt (Work.MotV.genY (asE2 D f₁ f₂))
      rw [psi_apply_genY D f₁ f₂ g₁ σS' W₁ hW₁ γ T hσS', hΘ] at h
      rw [theta_transY_one (asE2 D f₁ f₂) Q ε hε1 (n₁ • T),
        theta_genY_one (asE2 D f₁ f₂) Q ε hε1,
        psi_apply_negY D f₁ f₂ g₂ σS' W₂ hW₂ γ T hσS' Q] at h
      have hs : ((-1 : ℤ) ^ (ε : ℕ)) = -1 := by rw [hε1]; norm_num
      have hx' := hx
      rw [hs, neg_one_smul] at hx' h
      have h2 : Work.MotC2.transX (asE2 D f₁ f₂) (Q + -(n₁ • T)) =
          Work.MotC2.transX (asE2 D f₁ f₂) ((n₂ • T) + σQ) := hx'
      have h3 : Work.MotC2.transY (asE2 D f₁ f₂) (Q + -(n₁ • T)) =
          Work.MotC2.transY (asE2 D f₁ f₂) ((n₂ • T) + σQ) := by
        have h4 : -(Work.MotC2.transY (asE2 D f₁ f₂) (Q + -(n₁ • T))) =
            -(Work.MotC2.transY (asE2 D f₁ f₂) ((n₂ • T) + σQ)) := by
          have key := h
          rw [h2] at key
          simp only [sub_eq_add_neg] at key
          exact add_right_cancel (add_right_cancel key)
        exact neg_inj.mp h4
      rw [hs, neg_one_smul]
      exact h3
  -- combine
  have hτ : Work.MotC2.transAlgEquiv (asE2 D f₁ f₂) (Q + (((-1 : ℤ) ^ (ε : ℕ)) • (n₁ • T))) =
      Work.MotC2.transAlgEquiv (asE2 D f₁ f₂) ((n₂ • T) + σQ) := by
    refine Work.MotC2.funcAlgEquiv_ext_genX_genY (asE2 D f₁ f₂) _ _ ?_ ?_
    · rw [transAlgEquiv_genX', transAlgEquiv_genX']; exact hx
    · rw [transAlgEquiv_genY', transAlgEquiv_genY']; exact hy
  have hAB : Q + (((-1 : ℤ) ^ (ε : ℕ)) • (n₁ • T)) = (n₂ • T) + σQ :=
    Work.MotC2.transAlgEquiv_injective (asE2 D f₁ f₂) hτ
  have hfin : σQ - Q = ((((-1 : ℤ) ^ (ε : ℕ)) * (n₁ : ℤ)) - (n₂ : ℤ)) • T := by
    have h1 : σQ - Q = ((-1 : ℤ) ^ (ε : ℕ)) • (n₁ • T) - n₂ • T := by
      have h2 : σQ = Q + ((-1 : ℤ) ^ (ε : ℕ)) • (n₁ • T) - n₂ • T := by
        rw [hAB]; abel
      rw [h2]; abel
    rw [h1, ← natCast_zsmul, ← natCast_zsmul, ← mul_smul, ← sub_smul]
  exact hfin

end Work.MotV5.LamAS
