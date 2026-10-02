import Mathlib
import Submission.Work.Transgression.Pieces
import Submission.Work.Transgression.Rank
import Submission.Work.Transgression.Algebra
import Submission.Work.Agree.kunnethInj
import Submission.Work.Agree.kunnethSpan
import Submission.Work.Cohomology.sphereCohomologyTop

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# Auxiliary lemmas for `Work.Transgression.PsiClass`

This module proves the Künneth injectivity for `S³ × S³` in the quaternionic model
(`KunnethInjS3Prod`), the Hopf formula for the cohomology class of a pointwise product
(`s3MulCm_HMap`) and the resulting action of the power maps on `H³(S³;ℤ)` (`zPow_HMap`),
which together give the class of the clutching map `ψ (u,v) = uᵃ v uᵇ` used in
`Work.Transgression.PsiClass`.
-/

namespace Work.Transgression
namespace PsiAux

open Work.TangentClasses Work.CharacteristicClasses CategoryTheory

noncomputable section

/-- `H³(S³;ℤ)` in the quaternionic model `S³ = Sp(1)`. -/
abbrev CohS : Type := ↥(Work.Thom.Coh ℤ 3 Work.CharacteristicClasses.S3)

/-- `H³(S³ × S³;ℤ)` in the quaternionic model. -/
abbrev CohQQ : Type :=
  ↥(Work.Thom.Coh ℤ 3 (Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3))

/-! ## 1. The four pairings between the factor projections and the factor inclusions -/

lemma prjA_comp_sectA : prjA.comp sectA = ContinuousMap.id _ := by
  apply ContinuousMap.ext; intro v; rfl

lemma prjB_comp_sectB : prjB.comp sectB = ContinuousMap.id _ := by
  apply ContinuousMap.ext; intro v; rfl

lemma prjB_comp_sectA :
    prjB.comp sectA = ContinuousMap.const _ (Work.CharacteristicClasses.s3One) := by
  apply ContinuousMap.ext; intro v; rfl

lemma prjA_comp_sectB :
    prjA.comp sectB = ContinuousMap.const _ (Work.CharacteristicClasses.s3One) := by
  apply ContinuousMap.ext; intro v; rfl

/-- The pullback along `sectA` is a left inverse of the pullback along `prjA`. -/
theorem sectA_comp_prjA :
    (HMap sectA 3).hom.comp (HMap prjA 3).hom = LinearMap.id := by
  rw [← ModuleCat.hom_comp, ← HMap_comp sectA prjA 3, prjA_comp_sectA, HMap_id]
  rfl

/-- The pullback along `sectB` is a left inverse of the pullback along `prjB`. -/
theorem sectB_comp_prjB :
    (HMap sectB 3).hom.comp (HMap prjB 3).hom = LinearMap.id := by
  rw [← ModuleCat.hom_comp, ← HMap_comp sectB prjB 3, prjB_comp_sectB, HMap_id]
  rfl

/-- The first cross pullback vanishes in degree `3`: `sectA^* ∘ prjB^* = 0`. -/
theorem sectA_prjB_zero :
    ((HMap sectA 3).hom).comp ((HMap prjB 3).hom) = 0 := by
  apply LinearMap.ext
  intro x
  have hcomp := HMap_comp sectA prjB 3
  rw [prjB_comp_sectA] at hcomp
  rw [← ModuleCat.hom_comp, ← hcomp]
  exact Work.Agree.HMap_const_eq_zero (Work.CharacteristicClasses.s3One) 2 x

/-- The second cross pullback vanishes in degree `3`: `sectB^* ∘ prjA^* = 0`. -/
theorem sectB_prjA_zero :
    ((HMap sectB 3).hom).comp ((HMap prjA 3).hom) = 0 := by
  apply LinearMap.ext
  intro x
  have hcomp := HMap_comp sectB prjA 3
  rw [prjA_comp_sectB] at hcomp
  rw [← ModuleCat.hom_comp, ← hcomp]
  exact Work.Agree.HMap_const_eq_zero (Work.CharacteristicClasses.s3One) 2 x

/-! ## 2. Künneth injectivity for `S³ × S³` in the quaternionic model -/

/-- **`H³(S³;ℤ) ≅ ℤ`** in the quaternionic model, via the homeomorphism
`Work.CharacteristicClasses.s3Homeo` with the Euclidean sphere. -/
def s3CohIso : CohS ≃ₗ[ℤ] ℤ :=
  ((Work.Cohomology.cohomologyIso_of_homotopyEquiv
      (Work.CharacteristicClasses.s3Homeo.toHomotopyEquiv) 3).some ≪≫
    (Work.Cohomology.sphereCohomologyTop 3 (by norm_num)).some).toLinearEquiv

/-- **Künneth injectivity for `S³ × S³`** in the quaternionic model: a class of `H³(S³ × S³;ℤ)`
killed by both factor restrictions `sectA^*`, `sectB^*` is zero.  This is
`Work.Agree.span_eq_bot` applied to the four pairings. -/
theorem KunnethInjS3Prod (x : CohQQ)
    (h1 : (HMap sectA 3).hom x = 0) (h2 : (HMap sectB 3).hom x = 0) : x = 0 := by
  obtain ⟨eM⟩ := Sph33Rank
  exact Work.Agree.span_eq_bot (A := (HMap prjA 3).hom) (B := (HMap prjB 3).hom)
    (A' := (HMap sectA 3).hom) (B' := (HMap sectB 3).hom)
    sectA_comp_prjA sectA_prjB_zero sectB_prjA_zero sectB_comp_prjB
    (eM.trans (LinearEquiv.finTwoArrow ℤ ℤ)) s3CohIso x h1 h2

/-! ## 3. The Hopf formula: the class of the pointwise product -/

/-- Quaternion multiplication, as a continuous map `μ : S³ × S³ → S³`. -/
def mulMap : C(S3 × S3, S3) := ⟨fun p => s3Mul p.1 p.2, continuous_s3Mul⟩

@[simp] lemma mulMap_apply (p : S3 × S3) : mulMap p = s3Mul p.1 p.2 := rfl

lemma mul_comp_sectA : mulMap.comp sectA = ContinuousMap.id S3 := by
  apply ContinuousMap.ext; intro v
  simp [s3Mul_one]

lemma mul_comp_sectB : mulMap.comp sectB = ContinuousMap.id S3 := by
  apply ContinuousMap.ext; intro v
  simp [s3One_mul]

lemma sectA_comp_mul :
    (HMap sectA 3).hom.comp (HMap mulMap 3).hom = LinearMap.id := by
  rw [← ModuleCat.hom_comp, ← HMap_comp sectA mulMap 3, mul_comp_sectA, HMap_id]
  rfl

lemma sectB_comp_mul :
    (HMap sectB 3).hom.comp (HMap mulMap 3).hom = LinearMap.id := by
  rw [← ModuleCat.hom_comp, ← HMap_comp sectB mulMap 3, mul_comp_sectB, HMap_id]
  rfl

/-- **The class of the multiplication**: `μ^* x = prjA^* x + prjB^* x` in `H³(S³ × S³;ℤ)`. -/
theorem mulClass (x : CohS) :
    (HMap mulMap 3).hom x = (HMap prjA 3).hom x + (HMap prjB 3).hom x := by
  refine sub_eq_zero.mp (KunnethInjS3Prod _ ?_ ?_)
  · have h1 : (HMap sectA 3).hom ((HMap mulMap 3).hom x) = x := by
      rw [← LinearMap.comp_apply, sectA_comp_mul, LinearMap.id_apply]
    have h2 : (HMap sectA 3).hom ((HMap prjA 3).hom x) = x := by
      rw [← LinearMap.comp_apply, sectA_comp_prjA, LinearMap.id_apply]
    have h3 : (HMap sectA 3).hom ((HMap prjB 3).hom x) = 0 := by
      rw [← LinearMap.comp_apply, sectA_prjB_zero, LinearMap.zero_apply]
    rw [map_sub, map_add, h1, h2, h3]
    simp
  · have h1 : (HMap sectB 3).hom ((HMap mulMap 3).hom x) = x := by
      rw [← LinearMap.comp_apply, sectB_comp_mul, LinearMap.id_apply]
    have h2 : (HMap sectB 3).hom ((HMap prjB 3).hom x) = x := by
      rw [← LinearMap.comp_apply, sectB_comp_prjB, LinearMap.id_apply]
    have h3 : (HMap sectB 3).hom ((HMap prjA 3).hom x) = 0 := by
      rw [← LinearMap.comp_apply, sectB_prjA_zero, LinearMap.zero_apply]
    rw [map_sub, map_add, h1, h2, h3]
    simp

lemma prjA_comp_prodMk (f g : C(S3, S3)) : prjA.comp (f.prodMk g) = f := by
  apply ContinuousMap.ext; intro q; rfl

lemma prjB_comp_prodMk (f g : C(S3, S3)) : prjB.comp (f.prodMk g) = g := by
  apply ContinuousMap.ext; intro q; rfl

lemma s3MulCm_eq_comp_prodMk (f g : C(S3, S3)) :
    s3MulCm f g = mulMap.comp (f.prodMk g) := by
  apply ContinuousMap.ext; intro q
  simp [s3MulCm_apply]

/-- **The Hopf formula** for the cohomology class of a pointwise product of two maps `S³ → S³`:
`(f · g)^* x = f^* x + g^* x` in `H³(S³;ℤ)`. -/
theorem s3MulCm_HMap (f g : C(S3, S3)) (x : CohS) :
    (HMap (s3MulCm f g) 3).hom x = (HMap f 3).hom x + (HMap g 3).hom x := by
  rw [s3MulCm_eq_comp_prodMk, HMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply, mulClass]
  have h1 : (HMap (f.prodMk g) 3).hom ((HMap prjA 3).hom x) = (HMap f 3).hom x := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HMap_comp (f.prodMk g) prjA 3,
      prjA_comp_prodMk]
  have h2 : (HMap (f.prodMk g) 3).hom ((HMap prjB 3).hom x) = (HMap g 3).hom x := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HMap_comp (f.prodMk g) prjB 3,
      prjB_comp_prodMk]
  rw [map_add, h1, h2]

/-! ## 4. The action of the power maps on `H³(S³;ℤ)` -/

/-- **`s3ZPowCm (m + n) = s3ZPowCm m · s3ZPowCm n`** (pointwise product). -/
lemma zPow_add_eq_mulCm (m n : ℤ) :
    s3ZPowCm (m + n) = s3MulCm (s3ZPowCm m) (s3ZPowCm n) := by
  apply ContinuousMap.ext; intro q
  apply Subtype.ext
  simp only [s3ZPowCm_coe, s3MulCm_apply, s3Mul_coe]
  exact zpow_add₀ (coe_ne_zero_of_s3 (q := q)) m n

/-- **The power maps act by multiplication**: `(q ↦ qᵐ)^* x = m • x` on `H³(S³;ℤ)`, for every
`x`.  The proof is additivity in `m` (the Hopf formula `s3MulCm_HMap`) applied to a single `x`,
together with `s3ZPowCm 1 = id`. -/
theorem zPow_HMap (m : ℤ) (x : CohS) : (HMap (s3ZPowCm m) 3).hom x = m • x := by
  let F : ℤ →+ CohS :=
    { toFun := fun k => (HMap (s3ZPowCm k) 3).hom x
      map_zero' := by
        show (HMap (s3ZPowCm (0 : ℤ)) 3).hom x = 0
        rw [s3ZPowCm_zero]
        exact Work.Agree.HMap_const_eq_zero (Work.CharacteristicClasses.s3One) 2 x
      map_add' := by
        intro k l
        show (HMap (s3ZPowCm (k + l)) 3).hom x
          = (HMap (s3ZPowCm k) 3).hom x + (HMap (s3ZPowCm l) 3).hom x
        rw [zPow_add_eq_mulCm, s3MulCm_HMap] }
  have hF1 : F 1 = x := by
    show (HMap (s3ZPowCm (1 : ℤ)) 3).hom x = x
    rw [s3ZPowCm_one, HMap_id]
    rfl
  have h := AddMonoidHom.map_zsmul F m (1 : ℤ)
  rw [show m • (1 : ℤ) = m by simp, hF1] at h
  exact h

/-! ## 5. The clutching map `ψ (u,v) = uᵃ v uᵇ` on the two factors -/

lemma psi_sectA_apply (a b : ℤ) (v : S3) :
    psi a b (sectA v) = s3ZPowCm (a + b) v := by
  apply Subtype.ext
  simp only [sectA_apply, psi, ContinuousMap.coe_mk, Function.const_apply,
    s3ZPowCm_coe, Work.CharacteristicClasses.s3One_coe, mul_one]
  exact (zpow_add₀ (coe_ne_zero_of_s3 (q := v)) a b).symm

lemma psi_sectB_apply (a b : ℤ) (v : S3) :
    psi a b (sectB v) = v := by
  apply Subtype.ext
  simp only [sectB_apply, psi, ContinuousMap.coe_mk, Function.const_apply,
    Work.CharacteristicClasses.s3One_coe, one_zpow, one_mul, mul_one]

lemma psi_comp_sectA (a b : ℤ) :
    (psi a b).comp sectA = s3ZPowCm (a + b) := by
  apply ContinuousMap.ext; intro v
  exact psi_sectA_apply a b v

lemma psi_comp_sectB (a b : ℤ) : (psi a b).comp sectB = ContinuousMap.id S3 := by
  apply ContinuousMap.ext; intro v
  exact psi_sectB_apply a b v

lemma sectA_comp_psi (a b : ℤ) :
    (HMap sectA 3).hom.comp (HMap (psi a b) 3).hom = (HMap (s3ZPowCm (a + b)) 3).hom := by
  rw [← ModuleCat.hom_comp, ← HMap_comp sectA (psi a b) 3, psi_comp_sectA]

lemma sectB_comp_psi (a b : ℤ) :
    (HMap sectB 3).hom.comp (HMap (psi a b) 3).hom = LinearMap.id := by
  rw [← ModuleCat.hom_comp, ← HMap_comp sectB (psi a b) 3, psi_comp_sectB, HMap_id]
  rfl

end

end PsiAux

end Work.Transgression
