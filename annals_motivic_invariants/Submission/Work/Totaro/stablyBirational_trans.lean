import Mathlib
import Submission.Work.Totaro.Defs
import Submission.Work.Totaro.partialIso_prod_affine
import Submission.Work.K3Inputs.prodOver_affine_assoc
import Submission.Work.K3Inputs.exists_variety_prodOver_affineSpace
import Submission.Work.Motivic.exists_partialIso_toBirationalMap

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Totaro

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-! ## Pasting of pullbacks -/

/-- **Pasting of pullbacks**: `A ×_X (X ×_Z B) ≅ A ×_Z B` for `A ⟶ X ⟶ Z ⟵ B`. -/
theorem pullback_pasting {C : Type*} [Category C] {A X Z B : C} (f : A ⟶ X)
    (g : X ⟶ Z) (h : B ⟶ Z)
    [HasPullback g h] [HasPullback f (pullback.fst g h)] [HasPullback (f ≫ g) h] :
    Nonempty (pullback f (pullback.fst g h) ≅ pullback (f ≫ g) h) := by
  let w : pullback (f ≫ g) h ⟶ pullback g h :=
    pullback.map (f ≫ g) h g h f (𝟙 B) (𝟙 Z) (by simp) (by simp)
  have hw : w ≫ pullback.fst g h = pullback.fst (f ≫ g) h ≫ f := by
    simp only [w, pullback.map, pullback.lift_fst, Category.comp_id]
  have hw' : w ≫ pullback.snd g h = pullback.snd (f ≫ g) h := by
    simp only [w, pullback.map, pullback.lift_snd, Category.comp_id]
  let φ : pullback f (pullback.fst g h) ⟶ pullback (f ≫ g) h :=
    pullback.lift (pullback.fst f (pullback.fst g h))
      (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h)
      (by
        calc pullback.fst f (pullback.fst g h) ≫ (f ≫ g)
            = (pullback.fst f (pullback.fst g h) ≫ f) ≫ g := (Category.assoc _ _ _).symm
          _ = (pullback.snd f (pullback.fst g h) ≫ pullback.fst g h) ≫ g := by
                rw [pullback.condition]
          _ = pullback.snd f (pullback.fst g h) ≫ (pullback.fst g h ≫ g) := Category.assoc _ _ _
          _ = pullback.snd f (pullback.fst g h) ≫ (pullback.snd g h ≫ h) := by
                rw [pullback.condition]
          _ = (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h) ≫ h :=
                (Category.assoc _ _ _).symm)
  let ψ : pullback (f ≫ g) h ⟶ pullback f (pullback.fst g h) :=
    pullback.lift (pullback.fst (f ≫ g) h) w (by rw [hw])
  have hφf : φ ≫ pullback.fst (f ≫ g) h = pullback.fst f (pullback.fst g h) :=
    pullback.lift_fst _ _ _
  have hφs : φ ≫ pullback.snd (f ≫ g) h
      = pullback.snd f (pullback.fst g h) ≫ pullback.snd g h := pullback.lift_snd _ _ _
  have hψf : ψ ≫ pullback.fst f (pullback.fst g h) = pullback.fst (f ≫ g) h :=
    pullback.lift_fst _ _ _
  have hψs : ψ ≫ pullback.snd f (pullback.fst g h) = w := pullback.lift_snd _ _ _
  refine ⟨⟨φ, ψ, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, hψf, hφf, Category.id_comp]
    · rw [Category.assoc, hψs, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, hw, ← Category.assoc, hφf, pullback.condition]
      · rw [Category.assoc, hw', hφs]
  · apply pullback.hom_ext
    · rw [Category.assoc, hφf, hψf, Category.id_comp]
    · rw [Category.assoc, hφs, ← Category.assoc, hψs, hw', Category.id_comp]


/-! ## The exponent shift, with the `Over`-structures as binders

`Work.Totaro.partialIso_prod_affine` proves the shift for `Variety`s (whose `Variety.over` field is
opaque); for the assembly of the transitivity law below it is convenient to have it with the
`Over`-structure as a binder, so that the `Variety` instance of the exponents can be chosen with the
canonical structure morphism `Work.K3.prodOverOver`.  The proof is the same as the one of
`Work.Totaro.partialIso_prod_affine` (base change along `𝔸ⁿ_ℤ ⟶ Spec ℤ`, the base being the terminal
scheme so that every morphism is a morphism over it, and the identification
`Work.Totaro.prodOver_affineN_iso`). -/

/-- **The exponent shift, for `Over`-structures as binders.**  A partial isomorphism
`i : A ⤏ B` of `𝕜`-schemes induces one between `A × 𝔸ᵏ` and `B × 𝔸ᵏ`. -/
theorem partialIso_prod_affine_of {A B : Scheme.{0}} [A.Over (Spec (.of 𝕜))]
    [B.Over (Spec (.of 𝕜))] (i : A.PartialIso B) (k : ℕ) :
    Nonempty ((Work.K3.prodOver 𝕜 A (Work.Totaro.AffineN 𝕜 k)).PartialIso
      (Work.K3.prodOver 𝕜 B (Work.Totaro.AffineN 𝕜 k))) := by
  letI hAz : A.Over SpecZ := ⟨(A ↘ Spec (.of 𝕜)) ≫ specZMap (𝕜 := 𝕜)⟩
  letI hBz : B.Over SpecZ := ⟨(B ↘ Spec (.of 𝕜)) ≫ specZMap (𝕜 := 𝕜)⟩
  haveI hSurj : Surjective (affineNZMap k) := inferInstance
  haveI hOpen : UniversallyOpen (affineNZMap k) := inferInstance
  haveI hIsOver : i.toPartialMap.IsOver SpecZ := ⟨specZ_hom_ext _ _⟩
  obtain ⟨h, -, -, -⟩ := Work.K3.partialIso_baseChangeAlong (f := affineNZMap k) i hIsOver
  have eA : Work.K3.prodOver 𝕜 A (Work.Totaro.AffineN 𝕜 k) ≅
      Work.K3.baseChangeAlong (affineNZMap k) A := by
    show Work.K3.prodOver 𝕜 A (Work.Totaro.AffineN 𝕜 k) ≅ pullback (affineNZMap k) (A ↘ SpecZ)
    exact prodOver_affineN_iso (𝕜 := 𝕜) A k
  have eB : Work.K3.prodOver 𝕜 B (Work.Totaro.AffineN 𝕜 k) ≅
      Work.K3.baseChangeAlong (affineNZMap k) B := by
    show Work.K3.prodOver 𝕜 B (Work.Totaro.AffineN 𝕜 k) ≅ pullback (affineNZMap k) (B ↘ SpecZ)
    exact prodOver_affineN_iso (𝕜 := 𝕜) B k
  exact ⟨(PartialIso.ofIso eA).trans (h.trans (PartialIso.ofIso eB.symm))⟩

/-! ## Transitivity of stable birationality -/

/-- **Stable birationality is transitive.**  `Work.Totaro.StablyBirational 𝕜 X Y` (the relation of
`Work.CY3.TotaroInput` / `Work.K3.TotaroInput`, i.e. `∃ n m, X × 𝔸ⁿ ∼ Y × 𝔸ᵐ`) is an equivalence
relation; transitivity is the missing law.  The proof needs no product of partial isomorphisms:
from `X × 𝔸ⁿ ∼ Y × 𝔸ᵐ` and `Y × 𝔸ᵐ' ∼ Z × 𝔸ᵐ''` one may shift the exponents *upward* on both sides
by composing with the associativity isomorphisms `(X × 𝔸ⁿ) × 𝔸ᵏ ≅ X × 𝔸^{n+k}`
(`Work.K3Inputs.prodOver_assoc_iso` / `Work.K3Inputs.prodOver_affine_assoc`, and
`Work.K3Inputs.exists_variety_prodOver_affineSpace` for the `Variety` instances the existential
demands), so that the two relations have the same middle exponent `m + m'` and can be composed. -/
theorem stablyBirational_trans {𝕜 : Type} [Field 𝕜] {X Y Z : AlgebraicGeometry.Scheme.{0}}
    [MotivicInvariants.Variety 𝕜 X] [MotivicInvariants.Variety 𝕜 Y]
    [MotivicInvariants.Variety 𝕜 Z]
    (h₁ : Work.Totaro.StablyBirational 𝕜 X Y) (h₂ : Work.Totaro.StablyBirational 𝕜 Y Z) :
    Work.Totaro.StablyBirational 𝕜 X Z := by
  obtain ⟨n, m, hXn, hYm, ⟨φ⟩⟩ := h₁
  obtain ⟨n', m', hYn, hZm, ⟨ψ⟩⟩ := h₂
  -- representatives of the two birational maps by partial isomorphisms
  obtain ⟨i, -⟩ := Work.Motivic.exists_partialIso_toBirationalMap φ
  obtain ⟨j, -⟩ := Work.Motivic.exists_partialIso_toBirationalMap ψ
  -- the two upward shifts of the exponents
  obtain ⟨i'⟩ := @partialIso_prod_affine_of 𝕜 _
    (Work.Totaro.prodOver 𝕜 X (Work.Totaro.AffineN 𝕜 n))
    (Work.Totaro.prodOver 𝕜 Y (Work.Totaro.AffineN 𝕜 m))
    (Work.K3.prodOverOver X (Work.Totaro.AffineN 𝕜 n))
    (Work.K3.prodOverOver Y (Work.Totaro.AffineN 𝕜 m)) i n'
  obtain ⟨j'⟩ := @partialIso_prod_affine_of 𝕜 _
    (Work.Totaro.prodOver 𝕜 Y (Work.Totaro.AffineN 𝕜 n'))
    (Work.Totaro.prodOver 𝕜 Z (Work.Totaro.AffineN 𝕜 m'))
    (Work.K3.prodOverOver Y (Work.Totaro.AffineN 𝕜 n'))
    (Work.K3.prodOverOver Z (Work.Totaro.AffineN 𝕜 m')) j m
  -- the associativity isomorphisms for the exponents
  obtain ⟨eX, -⟩ := Work.K3Inputs.prodOver_affine_assoc 𝕜 X n n'
  obtain ⟨eY₁, -⟩ := Work.K3Inputs.prodOver_affine_assoc 𝕜 Y m n'
  obtain ⟨eY₂, -⟩ := Work.K3Inputs.prodOver_affine_assoc 𝕜 Y n' m
  obtain ⟨eZ, -⟩ := Work.K3Inputs.prodOver_affine_assoc 𝕜 Z m' m
  -- the two middle schemes agree because `m + n' = n' + m`
  have hmid : Work.Totaro.prodOver 𝕜 Y (Work.Totaro.AffineN 𝕜 (m + n')) =
      Work.Totaro.prodOver 𝕜 Y (Work.Totaro.AffineN 𝕜 (n' + m)) := by
    rw [Nat.add_comm m n']
  -- the composite partial isomorphism between the two products
  have hchain : Nonempty
      ((Work.Totaro.prodOver 𝕜 X (Work.Totaro.AffineN 𝕜 (n + n'))).PartialIso
        (Work.Totaro.prodOver 𝕜 Z (Work.Totaro.AffineN 𝕜 (m' + m)))) :=
    ⟨(PartialIso.ofIso eX.symm).trans (i'.trans ((PartialIso.ofIso eY₁).trans
      ((PartialIso.ofIso (eqToIso hmid)).trans ((PartialIso.ofIso eY₂.symm).trans
        (j'.trans (PartialIso.ofIso eZ))))))⟩
  haveI hXa : Variety 𝕜 (Work.Totaro.prodOver 𝕜 X (Work.Totaro.AffineN 𝕜 (n + n'))) :=
    Classical.choice (Work.K3Inputs.exists_variety_prodOver_affineSpace 𝕜 X (n + n'))
  haveI hZb : Variety 𝕜 (Work.Totaro.prodOver 𝕜 Z (Work.Totaro.AffineN 𝕜 (m' + m))) :=
    Classical.choice (Work.K3Inputs.exists_variety_prodOver_affineSpace 𝕜 Z (m' + m))
  exact ⟨n + n', m' + m, hXa, hZb, hchain.map PartialIso.toBirationalMap⟩

end

end Work.Totaro
