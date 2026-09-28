import Mathlib
import Submission.Work.SSS.vertRestrEZDefs
import Submission.Work.KunnethEZ.ez23_eq_ezGen

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

noncomputable section

set_option autoImplicit false

/-! ## Auxiliary lemmas for the vertex-insertion Eilenberg–Zilber identity

For a `t`-chain `z` of `Y` and a vertex `ν` of `Δ[1]`, the Eilenberg–Zilber shuffle chain
`ezChain t 0 Y Δ[1] z (genC Δ[1] ν)` is the push-forward of `z` along the vertex insertion
`g = lift (𝟙 Y) (SSet.const ν) : Y ⟶ Y ⊗ Δ[1]`, `y ↦ (y, ν)`.

The only combinatorial input is that the unique `(t,0)`-shuffle has `aHom = 𝟙` and
`bHom = const` (so that the `Δ[1]`-coordinate of the shuffle chain is `Δ[1].map (const …).op ν`,
which is exactly the `Δ[1]`-component of `g`).
-/

/-- The `aHom` of the unique `(t,0)`-shuffle is the identity. -/
lemma ezZeroLast_aHom_zSh0_eq_id (t : ℕ) :
    (Work.Cohomology.Crux33.aHom (Work.KunnethEZ.zSh0 t).1 (Work.KunnethEZ.zSh0 t).2
      : ⦋t+0⦌ ⟶ ⦋t⦌) = 𝟙 ⦋t⦌ := by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  apply Fin.ext
  rw [Work.KunnethEZ.aHom_zSh0_val t k]
  simp [SimplexCategory.concreteCategoryHom_id]

/-- The `bHom` of the unique `(t,0)`-shuffle is the constant map. -/
lemma ezZeroLast_bHom_zSh0_eq_const (t : ℕ) :
    (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh0 t).1 (Work.KunnethEZ.zSh0 t).2
      : ⦋t+0⦌ ⟶ ⦋0⦌) = SimplexCategory.const ⦋t⦌ ⦋0⦌ 0 := by
  rw [SimplexCategory.eq_const_to_zero
    (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh0 t).1 (Work.KunnethEZ.zSh0 t).2)]
  rfl

/-- The action of `aHom (zSh0 t)` on a simplex is the identity. -/
lemma ezZeroLast_map_aHom (Y : SSet.{0}) (t : ℕ) (σ : Y _⦋t⦌) :
    Y.map (Work.Cohomology.Crux33.aHom (Work.KunnethEZ.zSh0 t).1 (Work.KunnethEZ.zSh0 t).2).op σ
      = σ := by
  rw [ezZeroLast_aHom_zSh0_eq_id t]
  simp

/-- The action of `bHom (zSh0 t)` on a simplex is the action of the constant map. -/
lemma ezZeroLast_map_bHom (Y : SSet.{0}) (t : ℕ) (ν : Y _⦋0⦌) :
    Y.map (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh0 t).1 (Work.KunnethEZ.zSh0 t).2).op ν
      = Y.map (SimplexCategory.const ⦋t⦌ ⦋0⦌ 0).op ν := by
  rw [ezZeroLast_bHom_zSh0_eq_const t]
  try rfl

/-- **The element formula for the vertex insertion `y ↦ (y, ν)`.** -/
lemma ezZeroLast_lift_id_const_app (Y : SSet.{0}) (t : ℕ)
    (ν : Work.SSS.stdS1 _⦋0⦌) (σ : Y _⦋t⦌) :
    (CartesianMonoidalCategory.lift (CategoryTheory.CategoryStruct.id Y) (SSet.const ν)).app
        (Opposite.op (SimplexCategory.mk t)) σ
      = (σ, Work.SSS.stdS1.map (SimplexCategory.const ⦋t⦌ ⦋0⦌ 0).op ν) := by
  refine Prod.ext ?_ ?_
  · change (CategoryStruct.comp (CartesianMonoidalCategory.lift (CategoryStruct.id Y) (SSet.const ν))
      (CartesianMonoidalCategory.fst Y stdS1)).app (Opposite.op (SimplexCategory.mk t)) σ
      = (CategoryStruct.id Y).app (Opposite.op (SimplexCategory.mk t)) σ
    rw [CartesianMonoidalCategory.lift_fst]
  · change (CategoryStruct.comp (CartesianMonoidalCategory.lift (CategoryStruct.id Y) (SSet.const ν))
      (CartesianMonoidalCategory.snd Y stdS1)).app (Opposite.op (SimplexCategory.mk t)) σ
      = (SSet.const ν).app (Opposite.op (SimplexCategory.mk t)) σ
    rw [CartesianMonoidalCategory.lift_snd]

/-- **The chain map induced by a simplicial map on a generator.** -/
lemma ezZeroLast_sCCMap_genC {X Y : SSet.{0}} (g : X ⟶ Y) {n : ℕ} (x : X _⦋n⦌) :
    (Work.SSS.sCCMap g).f n (Work.KunnethEZ.genC X x)
      = Work.KunnethEZ.genC Y (g.app (Opposite.op (SimplexCategory.mk n)) x) := by
  have h := SSet.ι_chainComplexMap_f X Y g (ModuleCat.of ℤ ℤ) (n := n) x
  have h2 := congrArg (fun (φ : ModuleCat.of ℤ ℤ ⟶ (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n) =>
    φ.hom (1 : ℤ)) h
  simpa only [Work.KunnethEZ.genC, ModuleCat.hom_comp, LinearMap.comp_apply,
    Work.SSS.sCCMap] using h2

/-- **Linearity of the induced chain map on a finite `ℤ`-linear combination.** -/
lemma ezZeroLast_sCCMap_f_sum {X Y : SSet.{0}} (g : X ⟶ Y) (n : ℕ) {ι : Type*}
    (s : Finset ι) (a : ι → ℤ) (w : ι → (X.chainComplex Work.KunnethEZ.ezR).X n) :
    (Work.SSS.sCCMap g).f n (∑ i ∈ s, a i • w i)
      = ∑ i ∈ s, a i • (Work.SSS.sCCMap g).f n (w i) := by
  have h1 : ((Work.SSS.sCCMap g).f n).hom (∑ i ∈ s, a i • w i)
      = ∑ i ∈ s, a i • ((Work.SSS.sCCMap g).f n).hom (w i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => map_zsmul _ _ _)
  simpa using h1

/-- **The Eilenberg–Zilber chain of a generator and a vertex is the vertex insertion.** -/
lemma ezZeroLast_ezChain_gen_vertex (Y : SSet.{0}) (t : ℕ)
    (ν : Work.SSS.stdS1 _⦋0⦌) (σ : Y _⦋t⦌) :
    Work.KunnethEZ.ezChain t 0 Y Work.SSS.stdS1 (Work.KunnethEZ.genC Y σ)
        (Work.KunnethEZ.genC Work.SSS.stdS1 ν)
      = Work.KunnethEZ.genC (Y ⊗ Work.SSS.stdS1)
          ((CartesianMonoidalCategory.lift (CategoryTheory.CategoryStruct.id Y)
            (SSet.const ν)).app (Opposite.op (SimplexCategory.mk t)) σ) := by
  rw [Work.KunnethEZ.ezChain_gen t 0 Y Work.SSS.stdS1 σ ν,
    Work.KunnethEZ.ezGen_zero_single_right t Y Work.SSS.stdS1 σ ν]
  have hpair :
      (Y.map (Work.Cohomology.Crux33.aHom (Work.KunnethEZ.zSh0 t).1
            (Work.KunnethEZ.zSh0 t).2).op σ,
        Work.SSS.stdS1.map (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh0 t).1
            (Work.KunnethEZ.zSh0 t).2).op ν)
        = (CartesianMonoidalCategory.lift (CategoryTheory.CategoryStruct.id Y)
            (SSet.const ν)).app (Opposite.op (SimplexCategory.mk t)) σ := by
    rw [ezZeroLast_map_aHom Y t σ, ezZeroLast_map_bHom Work.SSS.stdS1 t ν,
      ezZeroLast_lift_id_const_app Y t ν σ]
  exact congrArg (Work.KunnethEZ.genC (Y ⊗ Work.SSS.stdS1)) hpair

/-- **The Eilenberg–Zilber chain of a `t`-chain and a vertex is the push-forward along the vertex
insertion `y ↦ (y, ν)`.** -/
lemma ezZeroLast_ezChain_eq_sCCMap_lift (Y : SSet.{0}) (t : ℕ)
    (ν : Work.SSS.stdS1 _⦋0⦌)
    (z : (Y.chainComplex Work.KunnethEZ.ezR).X t) :
    Work.KunnethEZ.ezChain t 0 Y Work.SSS.stdS1 z (Work.KunnethEZ.genC Work.SSS.stdS1 ν)
      = (Work.SSS.sCCMap (CategoryTheory.CartesianMonoidalCategory.lift
          (CategoryTheory.CategoryStruct.id Y) (SSet.const ν))).f t z := by
  have hL : Work.KunnethEZ.ezChain t 0 Y Work.SSS.stdS1 z (Work.KunnethEZ.genC Work.SSS.stdS1 ν)
      = ∑ σ ∈ (Work.Cohomology.Crux33.coords Y t z).support,
          (Work.Cohomology.Crux33.coords Y t z) σ •
            Work.KunnethEZ.genC (Y ⊗ Work.SSS.stdS1)
              ((CartesianMonoidalCategory.lift (CategoryTheory.CategoryStruct.id Y)
                (SSet.const ν)).app (Opposite.op (SimplexCategory.mk t)) σ) := by
    conv_lhs => rw [Work.KunnethEZ.chain_eq_sum_gen Y t z]
    rw [Work.KunnethEZ.ezChain_sum_left]
    exact Finset.sum_congr rfl (fun σ _ => by rw [ezZeroLast_ezChain_gen_vertex Y t ν σ])
  have hR : (Work.SSS.sCCMap (CategoryTheory.CartesianMonoidalCategory.lift
        (CategoryTheory.CategoryStruct.id Y) (SSet.const ν))).f t z
      = ∑ σ ∈ (Work.Cohomology.Crux33.coords Y t z).support,
          (Work.Cohomology.Crux33.coords Y t z) σ •
            Work.KunnethEZ.genC (Y ⊗ Work.SSS.stdS1)
              ((CartesianMonoidalCategory.lift (CategoryTheory.CategoryStruct.id Y)
                (SSet.const ν)).app (Opposite.op (SimplexCategory.mk t)) σ) := by
    conv_lhs => rw [Work.KunnethEZ.chain_eq_sum_gen Y t z]
    rw [ezZeroLast_sCCMap_f_sum]
    exact Finset.sum_congr rfl (fun σ _ => by rw [ezZeroLast_sCCMap_genC])
  rw [hL, hR]

/-- **Composition of chain maps applied to an element.** -/
lemma ezZeroLast_sCCMap_comp_apply {X Y Z : SSet.{0}} (g : X ⟶ Y) (k : Y ⟶ Z) {n : ℕ}
    (x : (Work.SSS.sCC X).X n) :
    (Work.SSS.sCCMap k).f n ((Work.SSS.sCCMap g).f n x) = (Work.SSS.sCCMap (g ≫ k)).f n x := by
  have h : Work.SSS.sCCMap (g ≫ k) = Work.SSS.sCCMap g ≫ Work.SSS.sCCMap k :=
    CategoryTheory.Functor.map_comp _ _ _
  rw [h, HomologicalComplex.comp_f, ModuleCat.comp_apply]

/-- **The Eilenberg–Zilber chain of a `t`-chain and a vertex of `Δ[1]`, pushed forward.**

For a simplicial map `φ : Y ⊗ Δ[1] ⟶ Z`, a `t`-chain `z` of `Y` and a vertex `ν` of `Δ[1]`,
the image of the Eilenberg–Zilber chain `ezChain t 0 Y Δ[1] z (genC Δ[1] ν)` under `sCCMap φ`
is the image of `z` under the chain map induced by the vertex insertion `Y ⟶ Y ⊗ Δ[1]`,
`y ↦ (y, ν)`, followed by `φ`.

Proof route (all ingredients exist in the workspace):
* `Work.KunnethEZ.chain_eq_sum_gen` writes `z = Σ_σ c_σ • genC Y σ`;
* `Work.KunnethEZ.ezChain_gen`, `Work.KunnethEZ.ezGen_zero_single_right` and
  `Work.KunnethEZ.ezChain_sum_left` give
  `ezChain t 0 Y Δ[1] z (genC Δ[1] ν) = Σ_σ c_σ • genP σ (Δ[1].map (const ⦋t⦌ ⦋0⦌ 0).op ν)`
  (using `Work.KunnethEZ.aHom_zSh0_val` and `SimplexCategory.Hom.ext` to see that
  `aHom (Work.KunnethEZ.zSh0 t) = 𝟙`, and `Work.KunnethEZ.bHom_zSh0_val` together with
  `SimplexCategory.eq_const_to_zero` for `bHom`);
* `Work.KunnethEZ.genP` is `genC (Y ⊗ Δ[1])` of the pair, so `Work.KunnethEZ.ezChain_gen` /
  `SSet.ι_chainComplexMap_f` evaluates the push-forward, and
  `SSet.const_app`/`CategoryTheory.CartesianMonoidalCategory.lift_fst`/`lift_snd`
  identify `(CategoryTheory.CartesianMonoidalCategory.lift (𝟙 Y) (SSet.const ν)).app _ σ` with
  `(σ, Δ[1].map (const ⦋t⦌ ⦋0⦌ 0).op ν)`;
* `Work.KunnethEZ.chain_eq_sum_gen` again reassembles `z`. -/
theorem sCCMap_ezChain_zero_last {Y Z : SSet.{0}}
    (φ : CategoryTheory.MonoidalCategory.tensorObj Y Work.SSS.stdS1 ⟶ Z)
    (t : ℕ) (ν : (Work.SSS.stdS1).obj (Opposite.op (SimplexCategory.mk 0)))
    (z : (Y.chainComplex Work.KunnethEZ.ezR).X t) :
    (Work.SSS.sCCMap φ).f t
        (Work.KunnethEZ.ezChain t 0 Y Work.SSS.stdS1 z
          (Work.KunnethEZ.genC Work.SSS.stdS1 ν))
      = (Work.SSS.sCCMap (CategoryTheory.CategoryStruct.comp
          (CategoryTheory.CartesianMonoidalCategory.lift (CategoryTheory.CategoryStruct.id Y)
            (SSet.const ν)) φ)).f t z := by
  rw [ezZeroLast_ezChain_eq_sCCMap_lift]
  exact ezZeroLast_sCCMap_comp_apply _ _ _

end

end Work.SSS
