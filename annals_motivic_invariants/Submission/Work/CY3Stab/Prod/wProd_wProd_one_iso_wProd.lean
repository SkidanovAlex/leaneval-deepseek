import Mathlib
import Submission.Work.CY3Stab.Defs
import Submission.Work.K3Inputs.Defs
import Submission.Work.K3Inputs.prodOver_affine_assoc
import Submission.Work.K3Inputs.affineN_prodOver_iso
import Submission.Work.K3Inputs.stablyBirat_congr
import Submission.Work.CrauderKatz.functionField_iso

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

set_option linter.style.haveILetI false

noncomputable section

/-- `𝔸ᵏ × (𝔸¹ × X)` and `𝔸^{k+1} × X` are isomorphic over `Spec 𝕜`, i.e.
`WProd (WProd X 1) k ≅ WProd X (k+1)` compatibly with the structure morphisms to `Spec 𝕜`.

Concretely, writing `a = (𝔸ᵏ ↘ Spec 𝕜)`, `b = (𝔸¹ ↘ Spec 𝕜)`, `c = (X ↘ Spec 𝕜)`,
`d = (𝔸^{k+1} ↘ Spec 𝕜)` and `h = pullback.snd b c ≫ c` (the structure morphism of
`𝔸¹ ×_{Spec 𝕜} X` used by the statement's `Over` instance), the two schemes are
`P = pullback a h` and `Q = pullback d c`, and the isomorphism is the explicit map

* `φ : P ⟶ Q`, `φ := pullback.lift (u ≫ e) (pullback.snd a h ≫ pullback.snd b c) ⋯`, where
  `u : P ⟶ pullback a b` collects the two projections of `P` through `a` and `b`, and
  `e : pullback a b ≅ 𝔸^{k+1}` is the affine product `𝔸ᵏ × 𝔸¹ ≅ 𝔸^{k+1}`
  (`Work.K3Inputs.affineN_prodOver_iso`);
* the inverse `ψ` reconstructs `P` out of the two projections of `Q`.

The composite `φ ≫ (Q ↘ Spec 𝕜) = φ ≫ (pullback.snd d c ≫ c) = (pullback.snd a h ≫
pullback.snd b c) ≫ c = (P ↘ Spec 𝕜)` identifies the structure morphisms. -/
theorem wProd_wProd_one_iso_wProd (𝕜 : Type) [Field 𝕜]
    (X : AlgebraicGeometry.Scheme.{0}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (k : ℕ) :
    ∃ E : Work.CY3Stab.WProd (𝕜 := 𝕜) (Work.CY3Stab.WProd (𝕜 := 𝕜) X 1) k ≅
        Work.CY3Stab.WProd (𝕜 := 𝕜) X (k + 1),
      CategoryTheory.CategoryStruct.comp E.hom
        (CategoryTheory.over (Work.CY3Stab.WProd (𝕜 := 𝕜) X (k + 1))
          (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))) =
      CategoryTheory.over (Work.CY3Stab.WProd (𝕜 := 𝕜) (Work.CY3Stab.WProd (𝕜 := 𝕜) X 1) k)
        (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := by
  -- The structure morphisms of the two affine factors and of `X`.
  let a : AffineK (𝕜 := 𝕜) k ⟶ Spec (CommRingCat.of 𝕜) :=
    AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)
  let b : AffineK (𝕜 := 𝕜) 1 ⟶ Spec (CommRingCat.of 𝕜) :=
    AffineK (𝕜 := 𝕜) 1 ↘ Spec (CommRingCat.of 𝕜)
  let c : X ⟶ Spec (CommRingCat.of 𝕜) := X ↘ Spec (CommRingCat.of 𝕜)
  let d : AffineK (𝕜 := 𝕜) (k + 1) ⟶ Spec (CommRingCat.of 𝕜) :=
    AffineK (𝕜 := 𝕜) (k + 1) ↘ Spec (CommRingCat.of 𝕜)
  -- The structure morphism of `𝔸¹ ×_{Spec 𝕜} X` induced by `b` (second projection).
  let h : pullback b c ⟶ Spec (CommRingCat.of 𝕜) := pullback.snd b c ≫ c
  -- The affine product `𝔸ᵏ × 𝔸¹ ≅ 𝔸^{k+1}` over `Spec 𝕜`, in explicit pullback form.
  obtain ⟨ae, hae⟩ := Work.K3Inputs.affineN_prodOver_iso 𝕜 k 1
  let e : pullback a b ⟶ AffineK (𝕜 := 𝕜) (k + 1) := ae.hom
  let ei : AffineK (𝕜 := 𝕜) (k + 1) ⟶ pullback a b := ae.inv
  have he : e ≫ d = pullback.fst a b ≫ a :=
    (Hom.isOver_iff (S := Spec (CommRingCat.of 𝕜))).mp hae
  have hcomp : ei ≫ e = 𝟙 (AffineK (𝕜 := 𝕜) (k + 1)) := ae.inv_hom_id
  have hcomp' : e ≫ ei = 𝟙 (pullback a b) := ae.hom_inv_id
  have hei : ei ≫ (pullback.fst a b ≫ a) = d := by
    calc ei ≫ (pullback.fst a b ≫ a)
        = ei ≫ (e ≫ d) := by rw [he]
      _ = (ei ≫ e) ≫ d := (Category.assoc ..).symm
      _ = d := by rw [hcomp, Category.id_comp]
  have heei : e ≫ (ei ≫ pullback.snd a b) = pullback.snd a b := by
    rw [← Category.assoc, hcomp', Category.id_comp]
  have heei' : e ≫ (ei ≫ pullback.fst a b) = pullback.fst a b := by
    rw [← Category.assoc, hcomp', Category.id_comp]
  -- `u : P ⟶ pullback a b`, the two projections of `P` bundled through `a` and `b`.
  have hu : pullback.fst a h ≫ a = (pullback.snd a h ≫ pullback.fst b c) ≫ b := by
    rw [Category.assoc, pullback.condition (f := b) (g := c)]
    exact pullback.condition (f := a) (g := h)
  let u : pullback a h ⟶ pullback a b :=
    pullback.lift (pullback.fst a h) (pullback.snd a h ≫ pullback.fst b c) hu
  have hu_fst : u ≫ pullback.fst a b = pullback.fst a h := pullback.lift_fst _ _ _
  have hu_snd : u ≫ pullback.snd a b = pullback.snd a h ≫ pullback.fst b c :=
    pullback.lift_snd _ _ _
  -- The forward map `φ : P ⟶ Q`.
  have hφ : (u ≫ e) ≫ d = (pullback.snd a h ≫ pullback.snd b c) ≫ c := by
    calc (u ≫ e) ≫ d
        = u ≫ (e ≫ d) := Category.assoc ..
      _ = u ≫ (pullback.fst a b ≫ a) := by rw [he]
      _ = (u ≫ pullback.fst a b) ≫ a := (Category.assoc ..).symm
      _ = pullback.fst a h ≫ a := by rw [hu_fst]
      _ = pullback.snd a h ≫ h := pullback.condition (f := a) (g := h)
      _ = pullback.snd a h ≫ (pullback.snd b c ≫ c) := rfl
      _ = (pullback.snd a h ≫ pullback.snd b c) ≫ c := (Category.assoc ..).symm
  let φ : pullback a h ⟶ pullback d c :=
    pullback.lift (u ≫ e) (pullback.snd a h ≫ pullback.snd b c) hφ
  have hφ_fst : φ ≫ pullback.fst d c = u ≫ e := pullback.lift_fst _ _ _
  have hφ_snd : φ ≫ pullback.snd d c = pullback.snd a h ≫ pullback.snd b c :=
    pullback.lift_snd _ _ _
  -- The map `w : Q ⟶ pullback b c` through the two projections of `pullback b c`.
  have hwk : ei ≫ (pullback.snd a b ≫ b) = d := by
    rw [← pullback.condition (f := a) (g := b)]
    exact hei
  have hw : pullback.fst d c ≫ (ei ≫ (pullback.snd a b ≫ b)) = pullback.snd d c ≫ c := by
    rw [hwk, pullback.condition]
  let w : pullback d c ⟶ pullback b c :=
    pullback.lift (pullback.fst d c ≫ ei ≫ pullback.snd a b) (pullback.snd d c) hw
  have hw_fst : w ≫ pullback.fst b c = pullback.fst d c ≫ ei ≫ pullback.snd a b :=
    pullback.lift_fst _ _ _
  have hw_snd : w ≫ pullback.snd b c = pullback.snd d c := pullback.lift_snd _ _ _
  -- The inverse `ψ : Q ⟶ P`.
  have hψ : pullback.fst d c ≫ (ei ≫ (pullback.fst a b ≫ a)) = w ≫ h := by
    have h3 : w ≫ h = pullback.snd d c ≫ c := by
      change w ≫ (pullback.snd b c ≫ c) = pullback.snd d c ≫ c
      rw [← Category.assoc, hw_snd]
    rw [h3, hei, pullback.condition]
  let ψ : pullback d c ⟶ pullback a h :=
    pullback.lift (pullback.fst d c ≫ ei ≫ pullback.fst a b) w hψ
  have hψ_fst : ψ ≫ pullback.fst a h = pullback.fst d c ≫ ei ≫ pullback.fst a b :=
    pullback.lift_fst _ _ _
  have hψ_snd : ψ ≫ pullback.snd a h = w := pullback.lift_snd _ _ _
  -- The two auxiliary identities used in the round trips.
  have hφw : φ ≫ w = pullback.snd a h := by
    apply pullback.hom_ext
    · calc (φ ≫ w) ≫ pullback.fst b c
          = φ ≫ (w ≫ pullback.fst b c) := Category.assoc ..
        _ = φ ≫ (pullback.fst d c ≫ (ei ≫ pullback.snd a b)) := by rw [hw_fst]
        _ = (φ ≫ pullback.fst d c) ≫ (ei ≫ pullback.snd a b) := (Category.assoc ..).symm
        _ = (u ≫ e) ≫ (ei ≫ pullback.snd a b) := by rw [hφ_fst]
        _ = u ≫ pullback.snd a b := by rw [Category.assoc, heei]
        _ = pullback.snd a h ≫ pullback.fst b c := hu_snd
    · rw [Category.assoc, hw_snd, hφ_snd]
  have hψu : ψ ≫ u = pullback.fst d c ≫ ei := by
    apply pullback.hom_ext
    · calc (ψ ≫ u) ≫ pullback.fst a b
          = ψ ≫ (u ≫ pullback.fst a b) := Category.assoc ..
        _ = ψ ≫ pullback.fst a h := by rw [hu_fst]
        _ = pullback.fst d c ≫ (ei ≫ pullback.fst a b) := by rw [hψ_fst]
        _ = (pullback.fst d c ≫ ei) ≫ pullback.fst a b := (Category.assoc ..).symm
    · calc (ψ ≫ u) ≫ pullback.snd a b
          = ψ ≫ (u ≫ pullback.snd a b) := Category.assoc ..
        _ = ψ ≫ (pullback.snd a h ≫ pullback.fst b c) := by rw [hu_snd]
        _ = (ψ ≫ pullback.snd a h) ≫ pullback.fst b c := (Category.assoc ..).symm
        _ = w ≫ pullback.fst b c := by rw [hψ_snd]
        _ = pullback.fst d c ≫ (ei ≫ pullback.snd a b) := by rw [hw_fst]
        _ = (pullback.fst d c ≫ ei) ≫ pullback.snd a b := (Category.assoc ..).symm
  -- The two round trips.
  have hφψ : φ ≫ ψ = 𝟙 (pullback a h) := by
    apply pullback.hom_ext
    · calc (φ ≫ ψ) ≫ pullback.fst a h
          = φ ≫ (ψ ≫ pullback.fst a h) := Category.assoc ..
        _ = φ ≫ (pullback.fst d c ≫ (ei ≫ pullback.fst a b)) := by rw [hψ_fst]
        _ = (φ ≫ pullback.fst d c) ≫ (ei ≫ pullback.fst a b) := (Category.assoc ..).symm
        _ = (u ≫ e) ≫ (ei ≫ pullback.fst a b) := by rw [hφ_fst]
        _ = u ≫ pullback.fst a b := by rw [Category.assoc, heei']
        _ = pullback.fst a h := hu_fst
        _ = 𝟙 (pullback a h) ≫ pullback.fst a h := (Category.id_comp _).symm
    · calc (φ ≫ ψ) ≫ pullback.snd a h
          = φ ≫ (ψ ≫ pullback.snd a h) := Category.assoc ..
        _ = φ ≫ w := by rw [hψ_snd]
        _ = pullback.snd a h := hφw
        _ = 𝟙 (pullback a h) ≫ pullback.snd a h := (Category.id_comp _).symm
  have hψφ : ψ ≫ φ = 𝟙 (pullback d c) := by
    apply pullback.hom_ext
    · calc (ψ ≫ φ) ≫ pullback.fst d c
          = ψ ≫ (φ ≫ pullback.fst d c) := Category.assoc ..
        _ = ψ ≫ (u ≫ e) := by rw [hφ_fst]
        _ = (ψ ≫ u) ≫ e := (Category.assoc ..).symm
        _ = (pullback.fst d c ≫ ei) ≫ e := by rw [hψu]
        _ = pullback.fst d c := by rw [Category.assoc, hcomp, Category.comp_id]
        _ = 𝟙 (pullback d c) ≫ pullback.fst d c := (Category.id_comp _).symm
    · calc (ψ ≫ φ) ≫ pullback.snd d c
          = ψ ≫ (φ ≫ pullback.snd d c) := Category.assoc ..
        _ = ψ ≫ (pullback.snd a h ≫ pullback.snd b c) := by rw [hφ_snd]
        _ = (ψ ≫ pullback.snd a h) ≫ pullback.snd b c := (Category.assoc ..).symm
        _ = w ≫ pullback.snd b c := by rw [hψ_snd]
        _ = pullback.snd d c := hw_snd
        _ = 𝟙 (pullback d c) ≫ pullback.snd d c := (Category.id_comp _).symm
  refine ⟨⟨φ, ψ, hφψ, hψφ⟩, ?_⟩
  change φ ≫ (pullback.snd d c ≫ c) = pullback.snd a h ≫ h
  calc φ ≫ (pullback.snd d c ≫ c)
      = (φ ≫ pullback.snd d c) ≫ c := (Category.assoc ..).symm
    _ = (pullback.snd a h ≫ pullback.snd b c) ≫ c := by rw [hφ_snd]
    _ = pullback.snd a h ≫ (pullback.snd b c ≫ c) := Category.assoc ..
    _ = pullback.snd a h ≫ h := rfl

end

end Work.CY3Stab.Prod
