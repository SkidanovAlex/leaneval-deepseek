import Mathlib
import Submission.Work.RatHurewicz.SphereThomDefs
import Submission.Work.Serre.bijective_mixedCup_of_two_subset

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.RatHurewicz

open CategoryTheory

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-!
# The degree-`0` two-piece gluing of the mixed cup bijectivity

`Work.Serre.bijective_mixedCup_of_two_subset` glues the *local* bijectivity of the mixed cup map
`x ↦ x ⌣ U₀` over two open pieces `Uc`, `Vc` of `↥(Uc ∪ Vc)` to the piece `Uc ∪ Vc` itself, in all
degrees `m` with `m + n₀ ≤ K`; in degree `0` it needs the vanishing of the relative cohomology of
degree `n₀ - 1` on the three pieces.

The local hypothesis over `Uc` in degree `0` is *exactly* the predicate `CupBij A n₀ U₀ Uc 0`: the
class entering the cup is the pullback of the ambient `U₀` along `↥Uc ↪ X`, whereas
`bijective_mixedCup_of_two_subset` uses the pullback along the composite `↥Uc ↪ ↥(Uc ∪ Vc) → X`.
The two agree by functoriality of `relCohMap` (`Work.Thom.relCohMap_compA_apply`), so the target is
the case `m = 0`, `K = n₀` of the general gluing.

Main result: `Work.RatHurewicz.cupBijZeroUnion`.
-/

/-- **The degree-`0` two-piece gluing of the cup bijectivity.**  If the mixed cup product with `U₀`
is bijective in degree `0` over the open pieces `Uc`, `Vc` and over `Uc ∩ Vc`, and the degree
`n₀ - 1` relative cohomology vanishes on these three pieces, then the mixed cup product with `U₀` is
bijective in degree `0` over `Uc ∪ Vc`. -/
theorem cupBijZeroUnion {X : Type} [TopologicalSpace X] (A : Set X) (Uc Vc : Set X)
    (hUo : IsOpen Uc) (hVo : IsOpen Vc) (n₀ : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A)
    (hvanU : Subsingleton ↥(Work.Thom.RelCoh ℚ (n₀ - 1) ↥Uc {y : ↥Uc | (y : X) ∈ A}))
    (hvanV : Subsingleton ↥(Work.Thom.RelCoh ℚ (n₀ - 1) ↥Vc {y : ↥Vc | (y : X) ∈ A}))
    (hvanUV : Subsingleton ↥(Work.Thom.RelCoh ℚ (n₀ - 1) ↥(Uc ∩ Vc)
      {y : ↥(Uc ∩ Vc) | (y : X) ∈ A}))
    (hU : Work.RatHurewicz.CupBij A n₀ U₀ Uc 0)
    (hV : Work.RatHurewicz.CupBij A n₀ U₀ Vc 0)
    (hUV : Work.RatHurewicz.CupBij A n₀ U₀ (Uc ∩ Vc) 0) :
    Work.RatHurewicz.CupBij A n₀ U₀ (Uc ∪ Vc) 0 := by
  classical
  -- The inclusions of the three pieces into `Uc ∪ Vc`, and the inclusion `↥(Uc ∪ Vc) ↪ X`.
  let inclU : C(↥Uc, ↥(Uc ∪ Vc)) := ⟨fun x => ⟨x.1, Or.inl x.2⟩, by fun_prop⟩
  let inclV : C(↥Vc, ↥(Uc ∪ Vc)) := ⟨fun x => ⟨x.1, Or.inr x.2⟩, by fun_prop⟩
  let inclUV : C(↥(Uc ∩ Vc), ↥(Uc ∪ Vc)) := ⟨fun y => ⟨y.1, Or.inl y.2.1⟩, by fun_prop⟩
  let subUV : C(↥(Uc ∪ Vc), X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hcompU : subUV.comp inclU = (⟨Subtype.val, continuous_subtype_val⟩ : C(↥Uc, X)) := by
    ext x; rfl
  have hcompV : subUV.comp inclV = (⟨Subtype.val, continuous_subtype_val⟩ : C(↥Vc, X)) := by
    ext x; rfl
  have hcompUV : subUV.comp inclUV = (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(Uc ∩ Vc), X)) :=
    by ext x; rfl
  -- The local bijectivity hypotheses, in the form used by
  -- `Work.Serre.bijective_mixedCup_of_two_subset`: there the ambient class lives on `↥(Uc ∪ Vc)`,
  -- so the class entering the cup over a piece is the pullback of `subUV^* U₀`.
  have hlocU : ∀ m : ℕ, m + n₀ ≤ n₀ → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m ↥Uc =>
        (Work.Thom.mixedCupC ℚ {y : ↥Uc | (y : X) ∈ A} m n₀) x
          ((Work.Thom.relCohMap inclU {y : ↥Uc | (y : X) ∈ A}
            {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} (fun _ hy => hy) ℚ n₀).hom
            ((Work.Thom.relCohMap subUV {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A
              (fun _ hy => hy) ℚ n₀).hom U₀))) := by
    intro m hm
    have hm0 : m = 0 := by omega
    subst hm0
    -- `inclU^* (subUV^* U₀) = (subUV ∘ inclU)^* U₀ = (Subtype.val)^* U₀`.
    have hclassU : (Work.Thom.relCohMap inclU {y : ↥Uc | (y : X) ∈ A}
        {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} (fun _ hy => hy) ℚ n₀).hom
        ((Work.Thom.relCohMap subUV {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A
          (fun _ hy => hy) ℚ n₀).hom U₀)
        = (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥Uc, X))
          {y : ↥Uc | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀ :=
      calc (Work.Thom.relCohMap inclU {y : ↥Uc | (y : X) ∈ A}
              {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} (fun _ hy => hy) ℚ n₀).hom
            ((Work.Thom.relCohMap subUV {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A
              (fun _ hy => hy) ℚ n₀).hom U₀)
          = (Work.Thom.relCohMap (subUV.comp inclU) {y : ↥Uc | (y : X) ∈ A} A
              (fun _ hy => hy) ℚ n₀).hom U₀ :=
            Work.Thom.relCohMap_compA_apply {y : ↥Uc | (y : X) ∈ A}
              {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A inclU subUV (fun _ hy => hy)
              (fun _ hy => hy) (fun _ hy => hy) ℚ n₀ U₀
        _ = (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥Uc, X))
              {y : ↥Uc | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀ :=
            congrArg (fun φ => φ.hom U₀) (Work.Thom.relCohMap_congrA
              {y : ↥Uc | (y : X) ∈ A} A hcompU (fun _ hy => hy) (fun _ hy => hy) ℚ n₀)
    rw [hclassU]
    simpa only [CupBij] using hU
  have hlocV : ∀ m : ℕ, m + n₀ ≤ n₀ → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m ↥Vc =>
        (Work.Thom.mixedCupC ℚ {y : ↥Vc | (y : X) ∈ A} m n₀) x
          ((Work.Thom.relCohMap inclV {y : ↥Vc | (y : X) ∈ A}
            {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} (fun _ hy => hy) ℚ n₀).hom
            ((Work.Thom.relCohMap subUV {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A
              (fun _ hy => hy) ℚ n₀).hom U₀))) := by
    intro m hm
    have hm0 : m = 0 := by omega
    subst hm0
    have hclassV : (Work.Thom.relCohMap inclV {y : ↥Vc | (y : X) ∈ A}
        {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} (fun _ hy => hy) ℚ n₀).hom
        ((Work.Thom.relCohMap subUV {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A
          (fun _ hy => hy) ℚ n₀).hom U₀)
        = (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥Vc, X))
          {y : ↥Vc | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀ :=
      calc (Work.Thom.relCohMap inclV {y : ↥Vc | (y : X) ∈ A}
              {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} (fun _ hy => hy) ℚ n₀).hom
            ((Work.Thom.relCohMap subUV {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A
              (fun _ hy => hy) ℚ n₀).hom U₀)
          = (Work.Thom.relCohMap (subUV.comp inclV) {y : ↥Vc | (y : X) ∈ A} A
              (fun _ hy => hy) ℚ n₀).hom U₀ :=
            Work.Thom.relCohMap_compA_apply {y : ↥Vc | (y : X) ∈ A}
              {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A inclV subUV (fun _ hy => hy)
              (fun _ hy => hy) (fun _ hy => hy) ℚ n₀ U₀
        _ = (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥Vc, X))
              {y : ↥Vc | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀ :=
            congrArg (fun φ => φ.hom U₀) (Work.Thom.relCohMap_congrA
              {y : ↥Vc | (y : X) ∈ A} A hcompV (fun _ hy => hy) (fun _ hy => hy) ℚ n₀)
    rw [hclassV]
    simpa only [CupBij] using hV
  have hlocUV : ∀ m : ℕ, m + n₀ ≤ n₀ → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m ↥(Uc ∩ Vc) =>
        (Work.Thom.mixedCupC ℚ {y : ↥(Uc ∩ Vc) | (y : X) ∈ A} m n₀) x
          ((Work.Thom.relCohMap inclUV {y : ↥(Uc ∩ Vc) | (y : X) ∈ A}
            {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} (fun _ hy => hy) ℚ n₀).hom
            ((Work.Thom.relCohMap subUV {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A
              (fun _ hy => hy) ℚ n₀).hom U₀))) := by
    intro m hm
    have hm0 : m = 0 := by omega
    subst hm0
    have hclassUV : (Work.Thom.relCohMap inclUV {y : ↥(Uc ∩ Vc) | (y : X) ∈ A}
        {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} (fun _ hy => hy) ℚ n₀).hom
        ((Work.Thom.relCohMap subUV {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A
          (fun _ hy => hy) ℚ n₀).hom U₀)
        = (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(Uc ∩ Vc), X))
          {y : ↥(Uc ∩ Vc) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀ :=
      calc (Work.Thom.relCohMap inclUV {y : ↥(Uc ∩ Vc) | (y : X) ∈ A}
              {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} (fun _ hy => hy) ℚ n₀).hom
            ((Work.Thom.relCohMap subUV {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A
              (fun _ hy => hy) ℚ n₀).hom U₀)
          = (Work.Thom.relCohMap (subUV.comp inclUV) {y : ↥(Uc ∩ Vc) | (y : X) ∈ A} A
              (fun _ hy => hy) ℚ n₀).hom U₀ :=
            Work.Thom.relCohMap_compA_apply {y : ↥(Uc ∩ Vc) | (y : X) ∈ A}
              {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A inclUV subUV (fun _ hy => hy)
              (fun _ hy => hy) (fun _ hy => hy) ℚ n₀ U₀
        _ = (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(Uc ∩ Vc), X))
              {y : ↥(Uc ∩ Vc) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀ :=
            congrArg (fun φ => φ.hom U₀) (Work.Thom.relCohMap_congrA
              {y : ↥(Uc ∩ Vc) | (y : X) ∈ A} A hcompUV (fun _ hy => hy) (fun _ hy => hy) ℚ n₀)
    rw [hclassUV]
    simpa only [CupBij] using hUV
  -- The general gluing, with `K := n₀`: the only degree asked for is `m = 0`.
  have hmain := Work.Serre.bijective_mixedCup_of_two_subset A Uc Vc hUo hVo n₀ n₀
    ((Work.Thom.relCohMap subUV {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A
      (fun _ hy => hy) ℚ n₀).hom U₀)
    hvanU hvanV hvanUV hlocU hlocV hlocUV
  simpa only [CupBij] using hmain 0 (by omega)

end Work.RatHurewicz
