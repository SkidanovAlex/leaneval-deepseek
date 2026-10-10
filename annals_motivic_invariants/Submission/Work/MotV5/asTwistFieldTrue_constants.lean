import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData
import Submission.Work.MotV5.asAut_Kb
import Submission.Work.MotV5.coeffAut
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.TranslationDefs
import Submission.Work.MotC2.TransAux.NoRoot
import Submission.Work.MotV5.algMemAdjoinWeierstrass
import Submission.Work.MotV5.kleinField_eq_adjoin_genXY
import Submission.Work.MotV5.exists_algebraMap_of_mem_adjoin_asRoot_of_sigma_fixed
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The constants of the corrected Artin–Schreier twist field `asTwistFieldTrue`

`Work.MotV5.asTwistFieldTrue D g τ σS = asTwistFieldFix D τ σS ⊓ asFieldL D g` is the twist
field of the Klein curve by the Artin–Schreier class of `g` in characteristic `5`, realized
inside `L(E) = asFieldL D g` (with `L = K(asRoot g)`, `K = 𝕜(t)`); the intersection with
`asFieldL` removes the spurious algebraic constants `Kb 𝕜 ^ σ` of `asTwistFieldFix`.

The present file proves that its constants in `Kb 𝕜 = AlgebraicClosure (𝕜(t))` are exactly `K`:
if `algebraMap (Kb 𝕜) (Om D) c` lies in `asTwistFieldTrue D g τ σS`, then `c` is rational.

The route is the one of the design note:

* `algebraMap c ∈ asTwistFieldFix D τ σS` gives `σ' (algebraMap c) = algebraMap c` where
  `σ' = asTwistAction D τ σS = σS ∘ τ`; since `σS` is `Kb 𝕜`-linear and `τ` acts on constants by
  `σ`, this is `algebraMap (σ c) = algebraMap c`, i.e. `σ c = c`
  (`sigma_apply_eq_of_mem_fix`), by injectivity of the constant embedding;
* `algebraMap c ∈ asFieldL D g` and `asFieldL = K(x, y) ⊔ K(asRoot g)` — with
  `Work.MotV5.kleinField_eq_adjoin_genXY`, `asFieldL = adjoin K ({x,y} ∪ {asRoot g})` — gives
  `c ∈ L⟮x,y⟯`, `L = K(asRoot g)`;
* `K` is algebraically closed in `L(x,y)` for the Weierstrass relation
  `y² + (a₁x+a₃)y = x³ + a₂x² + a₄x + a₆`: this is `Work.MotV5.algMemAdjoinWeierstrass`,
  whose input "no root of the Weierstrass polynomial in `L(z)(X)`" comes from
  `Work.MotC2.TransAux.NoRoot` (a degree obstruction), so
  `c ∈ IntermediateField.adjoin K {asRoot g}`;
* finally `Work.MotV5.exists_algebraMap_of_mem_adjoin_asRoot_of_sigma_fixed` upgrades
  `c ∈ K(asRoot g)` and `σ c = c` to `c ∈ K` (the Artin–Schreier generator `σ` has order `5`).

The bridges to the `Work.MotC2` chapter are `genX_eq_MotC2`, `genY_eq_MotC2` (the two spellings
of the Weierstrass coordinates agree), `transcendental_genX_*` (from
`Work.MotC2.transcendental_genX`) and `genY_weierstrass` (from `Work.MotC2.genY_sq_relation`).
-/

namespace Work.MotV5

open Work.MotV

variable {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)

/-- `Work.MotV.genX` and `Work.MotC2.genX` are the same element of the function field. -/
private lemma genX_eq_MotC2 :
    Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜))
      = Work.MotC2.genX (D.E.baseChange (Work.MotV.Kb 𝕜)) := by
  rw [Work.MotV.genX, Work.MotC2.genX, Work.MotC2.coordX_eq_mk]

/-- `Work.MotV.genY` and `Work.MotC2.genY` are the same element of the function field. -/
private lemma genY_eq_MotC2 :
    Work.MotV.genY (D.E.baseChange (Work.MotV.Kb 𝕜))
      = Work.MotC2.genY (D.E.baseChange (Work.MotV.Kb 𝕜)) := by
  rw [Work.MotV.genY, Work.MotC2.genY, Work.MotC2.coordY_eq_mk]

/-- The constant embedding `Kb 𝕜 → Om D` is injective. -/
private lemma algebraMap_Kb_Om_injective :
    Function.Injective (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)) :=
  FaithfulSMul.algebraMap_injective (Work.MotV.Kb 𝕜) (Work.MotV.Om D)

/-- `genX` is transcendental over `Kb 𝕜`. -/
private lemma transcendental_genX_Kb :
    Transcendental (Work.MotV.Kb 𝕜) (Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜))) := by
  simpa only [genX_eq_MotC2 D] using
    (Work.MotC2.transcendental_genX (D.E.baseChange (Work.MotV.Kb 𝕜)))

/-- `genX` is transcendental over `RatFunc 𝕜`. -/
private lemma transcendental_genX_ratFunc :
    Transcendental (RatFunc 𝕜) (Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜))) := fun halg =>
  transcendental_genX_Kb D (IsAlgebraic.tower_top (Work.MotV.Kb 𝕜) halg)

/-- The Weierstrass relation in `Om D`, with coefficients pushed to `RatFunc 𝕜`. -/
private lemma genY_weierstrass :
    (Work.MotV.genY (D.E.baseChange (Work.MotV.Kb 𝕜))) ^ 2
      + (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₁)
          * Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜))
        + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₃))
        * (Work.MotV.genY (D.E.baseChange (Work.MotV.Kb 𝕜)))
      = (Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜))) ^ 3
        + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₂)
          * (Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜))) ^ 2
        + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₄)
          * Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜))
        + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₆) := by
  have e1 : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (D.E.baseChange (Work.MotV.Kb 𝕜)).a₁
      = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₁) := by
    rw [show (D.E.baseChange (Work.MotV.Kb 𝕜)).a₁ = algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.E.a₁ from rfl]
    exact (IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) D.E.a₁).trans
      (IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D) D.E.a₁).symm
  have e3 : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (D.E.baseChange (Work.MotV.Kb 𝕜)).a₃
      = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₃) := by
    rw [show (D.E.baseChange (Work.MotV.Kb 𝕜)).a₃ = algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.E.a₃ from rfl]
    exact (IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) D.E.a₃).trans
      (IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D) D.E.a₃).symm
  have e2 : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (D.E.baseChange (Work.MotV.Kb 𝕜)).a₂
      = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₂) := by
    rw [show (D.E.baseChange (Work.MotV.Kb 𝕜)).a₂ = algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.E.a₂ from rfl]
    exact (IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) D.E.a₂).trans
      (IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D) D.E.a₂).symm
  have e4 : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (D.E.baseChange (Work.MotV.Kb 𝕜)).a₄
      = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₄) := by
    rw [show (D.E.baseChange (Work.MotV.Kb 𝕜)).a₄ = algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.E.a₄ from rfl]
    exact (IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) D.E.a₄).trans
      (IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D) D.E.a₄).symm
  have e6 : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (D.E.baseChange (Work.MotV.Kb 𝕜)).a₆
      = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₆) := by
    rw [show (D.E.baseChange (Work.MotV.Kb 𝕜)).a₆ = algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.E.a₆ from rfl]
    exact (IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) D.E.a₆).trans
      (IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D) D.E.a₆).symm
  have h := Work.MotC2.genY_sq_relation (D.E.baseChange (Work.MotV.Kb 𝕜))
  simp only [genX_eq_MotC2 D, genY_eq_MotC2 D, e1, e2, e3, e4, e6] at h ⊢
  linear_combination (norm := first | refl_ring1 | ring1) h

/-- An element of the fixed field of `asTwistAction` lying in the image of `Kb 𝕜` is `σ`-fixed. -/
private lemma sigma_apply_eq_of_mem_fix
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (hτ : ∀ c : Work.MotV.Kb 𝕜, τ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c))
    (c : Work.MotV.Kb 𝕜)
    (hfix : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c ∈
      Work.MotV5.asTwistFieldFix D τ σS) :
    σ c = c := by
  have h1 : Work.MotV5.asTwistAction D τ σS (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c :=
    (IntermediateField.mem_fixedField_iff
      (Subgroup.zpowers (Work.MotV5.asTwistAction D τ σS)) _).mp hfix _
      (Subgroup.mem_zpowers _)
  have h2 : σS (τ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c))
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c := h1
  rw [hτ c, σS.commutes (σ c)] at h2
  exact algebraMap_Kb_Om_injective D h2

theorem asTwistFieldTrue_constants (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : D.Good) (g : RatFunc 𝕜) (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (hτ : ∀ c : Work.MotV.Kb 𝕜, τ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c))
    (hσ : σ (Work.MotV5.asRoot g) = Work.MotV5.asRoot g + 1)
    (c : Work.MotV.Kb 𝕜)
    (hc : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c ∈
      Work.MotV5.asTwistFieldTrue D g τ σS) :
    ∃ d : RatFunc 𝕜, algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) d = c := by
  have hσc : σ c = c :=
    sigma_apply_eq_of_mem_fix D τ σS σ hτ c (by
      rw [Work.MotV5.asTwistFieldTrue] at hc
      exact hc.1)
  let x : Work.MotV.Om D := Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜))
  let y : Work.MotV.Om D := Work.MotV.genY (D.E.baseChange (Work.MotV.Kb 𝕜))
  let z : Work.MotV.Om D := algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c
  let L' : IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
    IntermediateField.adjoin (RatFunc 𝕜)
      {algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)}
  have hzm : z ∈ IntermediateField.adjoin ↥L' ({x, y} : Set (Work.MotV.Om D)) := by
    have h : z ∈ Work.MotV5.asFieldL D g := by
      rw [Work.MotV5.asTwistFieldTrue] at hc
      exact hc.2
    rw [Work.MotV5.asFieldL, Work.MotV5.kleinField_eq_adjoin_genXY 𝕜 D hD] at h
    rw [← IntermediateField.adjoin_union] at h
    rw [Set.union_comm] at h
    rw [← IntermediateField.adjoin_adjoin_left (RatFunc 𝕜)
      ({algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)} :
        Set (Work.MotV.Om D)) ({x, y} : Set (Work.MotV.Om D))] at h
    exact h
  have hz : IsAlgebraic ↥L' z := by
    have h1 : IsAlgebraic (RatFunc 𝕜) z :=
      IsAlgebraic.algebraMap (R := RatFunc 𝕜) (S := Work.MotV.Kb 𝕜) (A := Work.MotV.Om D)
        (Algebra.IsAlgebraic.isAlgebraic (R := RatFunc 𝕜) c)
    exact IsAlgebraic.tower_top ↥L' h1
  have hxt : Transcendental (RatFunc 𝕜) x := transcendental_genX_ratFunc D
  have hLalg : Algebra.IsAlgebraic (RatFunc 𝕜) ↥L' := by
    refine IntermediateField.isAlgebraic_adjoin
      (S := ({algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)} :
        Set (Work.MotV.Om D))) ?_
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact IsIntegral.algebraMap (R := RatFunc 𝕜) (A := Work.MotV.Kb 𝕜) (B := Work.MotV.Om D)
      ⟨asPolyK g, asPolyK_monic g, asPolyK_aeval_root g⟩
  have hW : y ^ 2 + (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₁)
        * x + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₃)) * y
      = x ^ 3 + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₂) * x ^ 2
        + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₄) * x
        + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₆) :=
    genY_weierstrass D
  have hno : ∀ r s : Polynomial ↥(IntermediateField.adjoin ↥L' ({z} : Set (Work.MotV.Om D))),
      s ≠ 0 →
      r ^ 2 + (Polynomial.C (algebraMap (RatFunc 𝕜)
            (↥(IntermediateField.adjoin ↥L' ({z} : Set (Work.MotV.Om D))))
            (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₁))
          * Polynomial.X + Polynomial.C (algebraMap (RatFunc 𝕜) _ (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₃)))
          * r * s
        - (Polynomial.X ^ 3 + Polynomial.C (algebraMap (RatFunc 𝕜) _ (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₂))
              * Polynomial.X ^ 2
            + Polynomial.C (algebraMap (RatFunc 𝕜) _ (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₄)) * Polynomial.X
            + Polynomial.C (algebraMap (RatFunc 𝕜) _ (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₆))) * s ^ 2
        ≠ 0 := by
    intro r s hs
    exact Work.MotC2.TransAux.NoRoot
      (algebraMap (RatFunc 𝕜) ↥(IntermediateField.adjoin ↥L' ({z} : Set (Work.MotV.Om D)))
        (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₁))
      (algebraMap (RatFunc 𝕜) _ (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₃))
      (algebraMap (RatFunc 𝕜) _ (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₂))
      (algebraMap (RatFunc 𝕜) _ (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₄))
      (algebraMap (RatFunc 𝕜) _ (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₆)) r s hs
  obtain ⟨l, hl⟩ := algMemAdjoinWeierstrass (K := RatFunc 𝕜) (L := ↥L') (Ω := Work.MotV.Om D)
    hLalg x y z (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₁) (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₂)
    (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₃) (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₄)
    (algebraMap 𝕜 (RatFunc 𝕜) D.E.a₆) hW hxt hz hzm hno
  have hzL' : z ∈ L' := by
    rw [show z = (l : Work.MotV.Om D) from hl]
    exact l.2
  have hzmap : z ∈ (IntermediateField.adjoin (RatFunc 𝕜) {Work.MotV5.asRoot g}).map
      (IsScalarTower.toAlgHom (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D)) := by
    have h : (IntermediateField.adjoin (RatFunc 𝕜) {Work.MotV5.asRoot g}).map
        (IsScalarTower.toAlgHom (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D)) = L' := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]
      rfl
    rw [h]
    exact hzL'
  rw [IntermediateField.mem_map] at hzmap
  obtain ⟨y', hy'mem, hy'z⟩ := hzmap
  have hy'c : y' = c := algebraMap_Kb_Om_injective D hy'z
  rw [hy'c] at hy'mem
  exact exists_algebraMap_of_mem_adjoin_asRoot_of_sigma_fixed 𝕜 g σ hσ c hy'mem hσc

end Work.MotV5
