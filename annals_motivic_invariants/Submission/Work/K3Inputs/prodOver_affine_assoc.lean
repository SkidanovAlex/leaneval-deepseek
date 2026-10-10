import Mathlib
import Submission.Work.K3Inputs.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

set_option linter.style.haveILetI false

noncomputable section

/-! ## The associativity of the fibre product

The first two results are purely categorical: they compute the structure morphism of the
canonical isomorphism `(X ×_S A) ×_S B ≅ X ×_S (A ×_S B)`, in the slightly unusual shape in
which `Work.K3.prodOver` presents the fibre products. -/

/-- The canonical isomorphism `(X ×_S A) ×_S B ≅ X ×_S (A ×_S B)` between pullbacks over `S`,
in the shape needed for `Work.K3.prodOver` (where the structure morphism of `X ×_S A` is
`pullback.fst p q ≫ p`).

It is `pullbackAssoc` preceded by the substitution `pullback.condition`. -/
def pullback_prod_assoc_iso (S : Scheme.{0}) {X A B : Scheme.{0}} (p : X ⟶ S) (q : A ⟶ S)
    (r : B ⟶ S) :
    pullback (pullback.fst p q ≫ p) r ≅ pullback p (pullback.fst q r ≫ q) :=
  pullback.congrHom pullback.condition rfl ≪≫ pullbackAssoc p q q r

/-- The structure-morphism computation for `pullback_prod_assoc_iso`. -/
theorem pullback_prod_assoc_iso_comp (S : Scheme.{0}) {X A B : Scheme.{0}} (p : X ⟶ S)
    (q : A ⟶ S) (r : B ⟶ S) :
    (pullback_prod_assoc_iso S p q r).hom ≫ (pullback.fst p (pullback.fst q r ≫ q) ≫ p)
      = pullback.fst (pullback.fst p q ≫ p) r ≫ (pullback.fst p q ≫ p) := by
  have h1 : (pullback.congrHom pullback.condition rfl :
      pullback (pullback.fst p q ≫ p) r ≅ pullback (pullback.snd p q ≫ q) r).hom
      ≫ (pullback.fst (pullback.snd p q ≫ q) r ≫ (pullback.snd p q ≫ q))
      = pullback.fst (pullback.fst p q ≫ p) r ≫ (pullback.fst p q ≫ p) := by
    have h0 : (pullback.congrHom pullback.condition rfl :
        pullback (pullback.fst p q ≫ p) r ≅ pullback (pullback.snd p q ≫ q) r).hom
        ≫ (pullback.fst (pullback.snd p q ≫ q) r) = pullback.fst (pullback.fst p q ≫ p) r := by
      simp only [pullback.congrHom, asIso_hom, pullback.map, pullback.lift_fst, Category.comp_id]
    rw [← Category.assoc, h0, ← pullback.condition]
  have h2 : (pullbackAssoc p q q r).hom ≫ (pullback.fst p (pullback.fst q r ≫ q) ≫ p)
      = pullback.fst (pullback.snd p q ≫ q) r ≫ (pullback.snd p q ≫ q) := by
    rw [← Category.assoc, pullbackAssoc_hom_fst, Category.assoc]
    simp only [pullback.condition]
  simp only [pullback_prod_assoc_iso, Iso.trans_hom]
  rw [Category.assoc, h2, h1]

/-- **Associativity of `Work.K3.prodOver`**, together with the compatibility with the structure
morphisms over `Spec 𝕜`: `(X ×_𝕜 A) ×_𝕜 B ≅ X ×_𝕜 (A ×_𝕜 B)`. -/
theorem prodOver_assoc (𝕜 : Type) [Field 𝕜] (X A B : Scheme.{0}) [X.Over (Spec (.of 𝕜))]
    [A.Over (Spec (.of 𝕜))] [B.Over (Spec (.of 𝕜))] :
    ∃ E : Work.K3.prodOver 𝕜 (Work.K3.prodOver 𝕜 X A) B ≅
        Work.K3.prodOver 𝕜 X (Work.K3.prodOver 𝕜 A B),
      E.hom.IsOver (Spec (.of 𝕜)) := by
  refine ⟨pullback_prod_assoc_iso _ (X ↘ _) (A ↘ _) (B ↘ _), ?_⟩
  rw [Hom.isOver_iff]
  exact pullback_prod_assoc_iso_comp _ _ _ _

/-! ## Transport of the second factor along an isomorphism over the base -/

/-- If `A ≅ B` over `Spec 𝕜`, then `X ×_𝕜 A ≅ X ×_𝕜 B` over `Spec 𝕜`. -/
theorem prodOver_iso_of_right (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))]
    {A B : Scheme.{0}} [A.Over (Spec (.of 𝕜))] [B.Over (Spec (.of 𝕜))] (e : A ≅ B)
    (he : e.hom.IsOver (Spec (.of 𝕜))) :
    ∃ E : Work.K3.prodOver 𝕜 X A ≅ Work.K3.prodOver 𝕜 X B, E.hom.IsOver (Spec (.of 𝕜)) := by
  haveI := he
  have hwφ : pullback.fst (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ (X ↘ Spec (.of 𝕜))
      = (pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ e.hom) ≫ (B ↘ Spec (.of 𝕜)) := by
    rw [Category.assoc, CategoryTheory.comp_over (f := e.hom) (S := Spec (.of 𝕜))]
    exact pullback.condition
  have hwψ : pullback.fst (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜)) ≫ (X ↘ Spec (.of 𝕜))
      = (pullback.snd (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜)) ≫ e.inv) ≫ (A ↘ Spec (.of 𝕜)) := by
    rw [Category.assoc, CategoryTheory.comp_over (f := e.inv) (S := Spec (.of 𝕜))]
    exact pullback.condition
  let φ : pullback (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ⟶
      pullback (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜)) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ e.hom) hwφ
  let ψ : pullback (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜)) ⟶
      pullback (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ e.inv) hwψ
  have hφ : φ ≫ pullback.fst (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜))
      = pullback.fst (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) := pullback.lift_fst _ _ _
  have hφ' : φ ≫ pullback.snd (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜))
      = pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ e.hom := pullback.lift_snd _ _ _
  have hψ : ψ ≫ pullback.fst (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))
      = pullback.fst (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜)) := pullback.lift_fst _ _ _
  have hψ' : ψ ≫ pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))
      = pullback.snd (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜)) ≫ e.inv := pullback.lift_snd _ _ _
  have hφψ : φ ≫ ψ = 𝟙 (pullback (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hψ, hφ, Category.id_comp]
    · calc (φ ≫ ψ) ≫ pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))
          = φ ≫ (ψ ≫ pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))) := Category.assoc ..
        _ = φ ≫ (pullback.snd (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜)) ≫ e.inv) := by rw [hψ']
        _ = (φ ≫ pullback.snd (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜))) ≫ e.inv :=
              (Category.assoc ..).symm
        _ = (pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ e.hom) ≫ e.inv := by rw [hφ']
        _ = pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ (e.hom ≫ e.inv) :=
              Category.assoc ..
        _ = pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ 𝟙 A := by rw [e.hom_inv_id]
        _ = pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) := Category.comp_id ..
        _ = 𝟙 (pullback (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)))
              ≫ pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) := (Category.id_comp ..).symm
  have hψφ : ψ ≫ φ = 𝟙 (pullback (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜))) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφ, hψ, Category.id_comp]
    · calc (ψ ≫ φ) ≫ pullback.snd (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜))
          = ψ ≫ (φ ≫ pullback.snd (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜))) := Category.assoc ..
        _ = ψ ≫ (pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ e.hom) := by rw [hφ']
        _ = (ψ ≫ pullback.snd (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜))) ≫ e.hom :=
              (Category.assoc ..).symm
        _ = (pullback.snd (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜)) ≫ e.inv) ≫ e.hom := by rw [hψ']
        _ = pullback.snd (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜)) ≫ (e.inv ≫ e.hom) :=
              Category.assoc ..
        _ = pullback.snd (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜)) ≫ 𝟙 B := by rw [e.inv_hom_id]
        _ = pullback.snd (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜)) := Category.comp_id ..
        _ = 𝟙 (pullback (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜)))
              ≫ pullback.snd (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜)) := (Category.id_comp ..).symm
  refine ⟨⟨φ, ψ, hφψ, hψφ⟩, ?_⟩
  rw [Hom.isOver_iff]
  show φ ≫ (pullback.fst (X ↘ Spec (.of 𝕜)) (B ↘ Spec (.of 𝕜)) ≫ (X ↘ Spec (.of 𝕜)))
    = pullback.fst (X ↘ Spec (.of 𝕜)) (A ↘ Spec (.of 𝕜)) ≫ (X ↘ Spec (.of 𝕜))
  rw [← Category.assoc, hφ]

/-! ## The affine product `𝔸ⁿ ×_{Spec 𝕜} 𝔸ᵐ ≅ 𝔸ⁿ⁺ᵐ`

The second ingredient: the fibre product of two affine spaces over `Spec 𝕜` is affine
`(n+m)`-space.  The forward morphism is `AffineSpace.homOfVector` applied to the `n + m`
coordinate functions of the product (the first `n` coming from the first projection, the last `m`
from the second, glued along `finSumFinEquiv`), and the inverse is `pullback.lift` of the two
`AffineSpace.reindex` maps `Fin.castAdd m` and `Fin.natAdd n`.  The two round trips are checked on
coordinates (`AffineSpace.hom_ext`) resp. on the two projections (`pullback.hom_ext`). -/

/-- **The affine product.**  `𝔸(Fin n) ×_{Spec 𝕜} 𝔸(Fin m) ≅ 𝔸(Fin (n+m))`, compatibly with the
structure morphisms to `Spec 𝕜`. -/
theorem pullback_affineN_prod_iso (𝕜 : Type) [Field 𝕜] (n m : ℕ) :
    ∃ e : pullback (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
          (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) ≅ 𝔸(Fin (n + m); Spec (.of 𝕜)),
      e.hom ≫ (𝔸(Fin (n + m); Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
        = pullback.fst (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
          (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) ≫ (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := by
  have hre_l : AffineSpace.reindex (Fin.castAdd m) (Spec (.of 𝕜))
        ≫ (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
      = (𝔸(Fin (n + m); Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := AffineSpace.reindex_over _ _
  have hre_r : AffineSpace.reindex (Fin.natAdd n) (Spec (.of 𝕜))
        ≫ (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
      = (𝔸(Fin (n + m); Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := AffineSpace.reindex_over _ _
  let v : Fin (n + m) → Γ(pullback (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
      (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)), ⊤) :=
    fun k => Sum.elim
      (fun i : Fin n => (pullback.fst (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
        (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))).appTop (AffineSpace.coord (Spec (.of 𝕜)) i))
      (fun j : Fin m => (pullback.snd (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
        (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))).appTop (AffineSpace.coord (Spec (.of 𝕜)) j))
      ((finSumFinEquiv (m := n) (n := m)).symm k)
  let q : pullback (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
      (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) ⟶ 𝔸(Fin (n + m); Spec (.of 𝕜)) :=
    AffineSpace.homOfVector (pullback.fst (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
      (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) ≫ (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))) v
  let p : 𝔸(Fin (n + m); Spec (.of 𝕜)) ⟶ pullback (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
      (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) :=
    pullback.lift (AffineSpace.reindex (Fin.castAdd m) (Spec (.of 𝕜)))
      (AffineSpace.reindex (Fin.natAdd n) (Spec (.of 𝕜))) (hre_l.trans hre_r.symm)
  have hq_over : q ≫ (𝔸(Fin (n + m); Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
      = pullback.fst (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
        (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) ≫ (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := by
    dsimp only [q]
    exact AffineSpace.homOfVector_over _ _
  have hq_coord (k : Fin (n + m)) : q.appTop (AffineSpace.coord (Spec (.of 𝕜)) k) = v k := by
    dsimp only [q]
    exact AffineSpace.homOfVector_appTop_coord _ _ _
  have hp_fst : p ≫ pullback.fst (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
      (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
      = AffineSpace.reindex (Fin.castAdd m) (Spec (.of 𝕜)) := by
    dsimp only [p]
    exact pullback.lift_fst _ _ _
  have hp_snd : p ≫ pullback.snd (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
      (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
      = AffineSpace.reindex (Fin.natAdd n) (Spec (.of 𝕜)) := by
    dsimp only [p]
    exact pullback.lift_snd _ _ _
  have hv_left (i : Fin n) : v (Fin.castAdd m i)
      = (pullback.fst (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
          (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))).appTop (AffineSpace.coord (Spec (.of 𝕜)) i) := by
    dsimp only [v]
    rw [finSumFinEquiv_symm_apply_castAdd]
    rfl
  have hv_right (j : Fin m) : v (Fin.natAdd n j)
      = (pullback.snd (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
          (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))).appTop (AffineSpace.coord (Spec (.of 𝕜)) j) := by
    dsimp only [v]
    rw [finSumFinEquiv_symm_apply_natAdd]
    rfl
  have hpv_left (i : Fin n) : p.appTop (v (Fin.castAdd m i))
      = AffineSpace.coord (Spec (.of 𝕜)) (Fin.castAdd m i) := by
    rw [hv_left, ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hp_fst,
      AffineSpace.reindex_appTop_coord]
  have hpv_right (j : Fin m) : p.appTop (v (Fin.natAdd n j))
      = AffineSpace.coord (Spec (.of 𝕜)) (Fin.natAdd n j) := by
    rw [hv_right, ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hp_snd,
      AffineSpace.reindex_appTop_coord]
  have hqf : q ≫ AffineSpace.reindex (Fin.castAdd m) (Spec (.of 𝕜))
      = pullback.fst (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
        (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := by
    apply AffineSpace.hom_ext
    · calc (q ≫ AffineSpace.reindex (Fin.castAdd m) (Spec (.of 𝕜)))
              ≫ (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
          = q ≫ (AffineSpace.reindex (Fin.castAdd m) (Spec (.of 𝕜))
              ≫ (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))) := Category.assoc ..
        _ = q ≫ (𝔸(Fin (n + m); Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := by rw [hre_l]
        _ = pullback.fst (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              ≫ (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := hq_over
    · intro i
      rw [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, AffineSpace.reindex_appTop_coord,
        hq_coord, hv_left]
  have hqs : q ≫ AffineSpace.reindex (Fin.natAdd n) (Spec (.of 𝕜))
      = pullback.snd (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
        (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := by
    apply AffineSpace.hom_ext
    · calc (q ≫ AffineSpace.reindex (Fin.natAdd n) (Spec (.of 𝕜)))
              ≫ (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
          = q ≫ (AffineSpace.reindex (Fin.natAdd n) (Spec (.of 𝕜))
              ≫ (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))) := Category.assoc ..
        _ = q ≫ (𝔸(Fin (n + m); Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := by rw [hre_r]
        _ = pullback.fst (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              ≫ (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := hq_over
        _ = pullback.snd (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              ≫ (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := pullback.condition
    · intro j
      rw [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, AffineSpace.reindex_appTop_coord,
        hq_coord, hv_right]
  have hqp : q ≫ p = 𝟙 (pullback (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
      (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))) := by
    apply pullback.hom_ext
    · calc (q ≫ p) ≫ pullback.fst (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
          = q ≫ (p ≫ pullback.fst (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))) := Category.assoc ..
        _ = q ≫ AffineSpace.reindex (Fin.castAdd m) (Spec (.of 𝕜)) := by rw [hp_fst]
        _ = pullback.fst (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := hqf
        _ = 𝟙 (pullback (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)))
              ≫ pullback.fst (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := (Category.id_comp _).symm
    · calc (q ≫ p) ≫ pullback.snd (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
          = q ≫ (p ≫ pullback.snd (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))) := Category.assoc ..
        _ = q ≫ AffineSpace.reindex (Fin.natAdd n) (Spec (.of 𝕜)) := by rw [hp_snd]
        _ = pullback.snd (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := hqs
        _ = 𝟙 (pullback (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)))
              ≫ pullback.snd (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := (Category.id_comp _).symm
  have hpq : p ≫ q = 𝟙 (𝔸(Fin (n + m); Spec (.of 𝕜))) := by
    apply AffineSpace.hom_ext
    · calc (p ≫ q) ≫ (𝔸(Fin (n + m); Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
          = p ≫ (q ≫ (𝔸(Fin (n + m); Spec (.of 𝕜)) ↘ Spec (.of 𝕜))) := Category.assoc ..
        _ = p ≫ (pullback.fst (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              ≫ (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))) := by rw [hq_over]
        _ = (p ≫ pullback.fst (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
              (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)))
              ≫ (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := (Category.assoc ..).symm
        _ = AffineSpace.reindex (Fin.castAdd m) (Spec (.of 𝕜))
              ≫ (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := by rw [hp_fst]
        _ = (𝔸(Fin (n + m); Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := hre_l
        _ = 𝟙 (𝔸(Fin (n + m); Spec (.of 𝕜)))
              ≫ (𝔸(Fin (n + m); Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) := (Category.id_comp _).symm
    · intro k
      rw [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, hq_coord, Scheme.Hom.id_appTop,
        ConcreteCategory.id_apply]
      obtain ⟨s, rfl⟩ := (finSumFinEquiv (m := n) (n := m)).surjective k
      cases s with
      | inl i => rw [finSumFinEquiv_apply_left, hpv_left]
      | inr j => rw [finSumFinEquiv_apply_right, hpv_right]
  exact ⟨⟨q, p, hqp, hpq⟩, hq_over⟩

/-- **The affine product, in the vocabulary of `Work.K3.prodOver`**: the fibre product of the two
affine spaces is affine `(n+m)`-space, and the isomorphism is over `Spec 𝕜`. -/
theorem affineN_prodOver_iso_aux (𝕜 : Type) [Field 𝕜] (n m : ℕ) :
    ∃ e : Work.K3.prodOver 𝕜 (AffineN 𝕜 n) (AffineN 𝕜 m) ≅ AffineN 𝕜 (n + m),
      e.hom.IsOver (Spec (.of 𝕜)) := by
  obtain ⟨e, he⟩ := pullback_affineN_prod_iso 𝕜 n m
  refine ⟨e, ?_⟩
  rw [Hom.isOver_iff]
  show e.hom ≫ (𝔸(Fin (n + m); Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
      = pullback.fst (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
        (𝔸(Fin m; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) ≫ (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
  exact he

/-- **Associativity of the affine exponents.**  For a `𝕜`-scheme `X` and `n m : ℕ`,
`(X × 𝔸ⁿ) × 𝔸ᵐ ≅ X × 𝔸^{n+m}` over `Spec 𝕜`, where `𝔸ⁿ := 𝔸(Fin n; Spec 𝕜)` is Mathlib's
`AlgebraicGeometry.AffineSpace` and `Work.K3.prodOver 𝕜` is the fibre product over `Spec 𝕜`.

This is the bookkeeping that lets the exponent of `Work.K3.StablyBirational` be handled: it is
proved from `CategoryTheory.Limits.pullbackAssoc` together with the affine product
`𝔸ⁿ ×_{Spec 𝕜} 𝔸ᵐ ≅ 𝔸^{n+m}`.  The isomorphism is required *over* `Spec 𝕜`,
since the resulting `Variety`-transport must be compatible with the structure morphisms. -/
theorem prodOver_affine_assoc (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))]
    (n m : ℕ) :
    ∃ e : Work.K3.prodOver 𝕜 (Work.K3.prodOver 𝕜 X (Work.K3Inputs.AffineN 𝕜 n))
        (Work.K3Inputs.AffineN 𝕜 m) ≅
      Work.K3.prodOver 𝕜 X (Work.K3Inputs.AffineN 𝕜 (n + m)),
      e.hom.IsOver (Spec (.of 𝕜)) := by
  obtain ⟨ea, ha⟩ := affineN_prodOver_iso_aux 𝕜 n m
  obtain ⟨e1, h1⟩ := prodOver_assoc 𝕜 X (AffineN 𝕜 n) (AffineN 𝕜 m)
  obtain ⟨e2, h2⟩ := prodOver_iso_of_right 𝕜 X ea ha
  exact ⟨e1 ≪≫ e2, by
    haveI : (e1.hom).IsOver (Spec (.of 𝕜)) := h1
    haveI : (e2.hom).IsOver (Spec (.of 𝕜)) := h2
    show (e1.hom ≫ e2.hom).IsOver (Spec (.of 𝕜))
    exact inferInstance⟩

end

end Work.K3Inputs
