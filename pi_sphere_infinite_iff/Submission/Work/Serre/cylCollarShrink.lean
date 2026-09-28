import Mathlib
import Submission.Work.Serre.relCohPreimageDefs
import Submission.Work.Serre.cylCollarHomeo
import Submission.Work.Serre.relCohomologyUnivVanishing
import Submission.Work.Thom.relCohMap_homotopic

/-!
# The shrink of the collar of a mapping cylinder

For a continuous map `q : C(X,Γ)` with collar coordinate `λ = cylLam q`, the collar
`cylCollar q = {λ < 1}` is the product `X × [0,1)` (`Work.Serre.cylCollarHomeo`), and on the
product the *shrink* `(x,t) ↦ (x,(1-s)t)` (`Work.Serre.collarShrinkProd`, with its homotopy
`collarShrinkProdHomotopy`) pushes the half open interval down to `X × {0}`.

Pulling this back along the collar homeomorphism gives the shrink `cylShrink q s` of the collar and
the homotopy `cylShrinkHomotopy q` from the identity of the collar to its retraction onto the bottom
copy `cylBot q = range (cylIncl q)`.  Because the shrink is the identity on `cylBot q`, the
retraction is a retraction of pairs and the homotopy homotopy of pairs, which is what makes the
relative cohomology of the collar pair `(cylCollar q, cylBot q)` vanish
(`Work.Serre.relCoh_cylCollar_vanishing` and `Work.Serre.relCoh_cylPre_inter_vanishing`), and hence
what makes the identification `Work.Serre.relCoh_pair_preimage_iso` work.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

variable {Γ : Type} [TopologicalSpace Γ] {X : Type} [TopologicalSpace X]

/-- The collar homeomorphism of `Work.Serre.cylCollarHomeo`, as a chosen homeomorphism. -/
noncomputable def cylCollarEquiv (q : C(X, Γ)) : X × CollT ≃ₜ ↥(cylCollar q) :=
  (cylCollarHomeo q).choose

/-- The defining property of the collar homeomorphism: the image of `(x,t)` is `⟦inl (x,t)⟧`. -/
theorem cylCollarEquiv_apply_coe (q : C(X, Γ)) (z : X × CollT) :
    ((cylCollarEquiv q z : ↥(cylCollar q)) : cyl q) = cylMk q (Sum.inl (z.1, z.2.1)) :=
  (cylCollarHomeo q).choose_spec z.1 z.2.1 z.2.2

/-! ## The shrink of the collar -/

/-- **The shrink of the collar**: the map of the collar corresponding to `(x,t) ↦ (x,(1-s)t)`
under the collar homeomorphism. -/
def cylShrink (q : C(X, Γ)) (s : unitInterval) : C(↥(cylCollar q), ↥(cylCollar q)) where
  toFun y := (cylCollarEquiv q) (collarShrinkProd s ((cylCollarEquiv q).symm y))
  continuous_toFun := (cylCollarEquiv q).continuous_toFun.comp
    ((collarShrinkProd s).continuous.comp (cylCollarEquiv q).symm.continuous_toFun)

theorem cylShrink_apply (q : C(X, Γ)) (s : unitInterval) (y : ↥(cylCollar q)) :
    cylShrink q s y = (cylCollarEquiv q) (collarShrinkProd s ((cylCollarEquiv q).symm y)) := rfl

/-- The shrink does not move the retraction: it stays in the same fibre of `cylRetract q`. -/
theorem cylRetract_cylShrink (q : C(X, Γ)) (s : unitInterval) (y : ↥(cylCollar q)) :
    cylRetract q (cylShrink q s y) = cylRetract q (y : cyl q) := by
  conv_rhs => rw [← Homeomorph.apply_symm_apply (cylCollarEquiv q) y]
  rw [cylShrink_apply, cylCollarEquiv_apply_coe, cylCollarEquiv_apply_coe]
  simp

/-- The shrink at time `1` lands in the bottom copy. -/
theorem cylShrink_one_mem_cylBot (q : C(X, Γ)) (y : ↥(cylCollar q)) :
    ((cylShrink q 1 y : ↥(cylCollar q)) : cyl q) ∈ cylBot q := by
  refine ⟨((cylCollarEquiv q).symm y).1, ?_⟩
  rw [cylShrink_apply]
  have h : (cylCollarEquiv q (collarShrinkProd 1 ((cylCollarEquiv q).symm y)) : cyl q)
      = cylMk q (Sum.inl (((cylCollarEquiv q).symm y).1,
          (collarShrinkProd 1 ((cylCollarEquiv q).symm y)).2.1)) :=
    cylCollarEquiv_apply_coe q _
  rw [h, collarShrinkProd_snd_apply, unitIntervalMulSub_one_left]
  rfl

/-- The shrink fixes the points of the bottom copy. -/
theorem cylShrink_fixes_bot (q : C(X, Γ)) (s : unitInterval) {y : ↥(cylCollar q)}
    (hy : (y : cyl q) ∈ cylBot q) : cylShrink q s y = y := by
  obtain ⟨x, hx⟩ := hy
  -- the coordinate of `y`
  set z := (cylCollarEquiv q).symm y with hz
  have hyz : (y : cyl q) = cylMk q (Sum.inl (z.1, z.2.1)) := by
    conv_lhs => rw [← Homeomorph.apply_symm_apply (cylCollarEquiv q) y]
    exact cylCollarEquiv_apply_coe q z
  have hx' : cylMk q (Sum.inl (z.1, z.2.1)) = cylMk q (Sum.inl (x, 0)) := by
    rw [← hyz, ← hx]
    rfl
  obtain ⟨h1, h2⟩ := cylCollar_injective q z.2.2 hx'
  have hz0 : (z.2.1 : unitInterval) = 0 := h2
  have hfix : collarShrinkProd s z = z := by
    refine Prod.ext rfl ?_
    refine Subtype.ext ?_
    rw [collarShrinkProd_snd_apply]
    apply Subtype.ext
    rw [coe_unitIntervalMulSub, hz0]
    norm_num
  rw [cylShrink_apply, hfix]
  exact Homeomorph.apply_symm_apply _ y

/-- The bottom copy, included in the collar. -/
def cylBotIncl (q : C(X, Γ)) : C(↥(cylBot q), ↥(cylCollar q)) where
  toFun b := ⟨b.1, cylBot_subset_cylCollar q b.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val (fun b => cylBot_subset_cylCollar q b.2)

/-- The shrink at time `1`, as a map into the bottom copy. -/
def cylShrinkToBot (q : C(X, Γ)) : C(↥(cylCollar q), ↥(cylBot q)) where
  toFun y := ⟨(cylShrink q 1 y : ↥(cylCollar q)), cylShrink_one_mem_cylBot q y⟩
  continuous_toFun := Continuous.subtype_mk
    (f := fun y : ↥(cylCollar q) => ((cylShrink q 1 y : ↥(cylCollar q)) : cyl q))
    (continuous_subtype_val.comp (cylShrink q 1).continuous) (cylShrink_one_mem_cylBot q)

/-- The retraction of the collar onto the bottom copy, as a map of the collar: it is
`cylBotIncl q ∘ cylShrinkToBot q`, i.e. definitionally the shrink at time `1` read in the collar. -/
def cylShrinkRetract (q : C(X, Γ)) : C(↥(cylCollar q), ↥(cylCollar q)) :=
  (cylBotIncl q).comp (cylShrinkToBot q)

theorem cylShrinkRetract_apply (q : C(X, Γ)) (y : ↥(cylCollar q)) :
    cylShrinkRetract q y = cylShrink q 1 y := by
  refine Subtype.ext ?_
  rfl

/-- **The shrink homotopy of the collar**: a homotopy from the identity of the collar to the
retraction `cylShrinkRetract q` onto the bottom copy. -/
def cylShrinkHomotopy (q : C(X, Γ)) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(cylCollar q)) (cylShrinkRetract q) where
  toContinuousMap := ((cylCollarEquiv q) : C(X × CollT, ↥(cylCollar q))).comp
    (collarShrinkProdPair.comp
      (ContinuousMap.prodMap (ContinuousMap.id unitInterval) (cylCollarEquiv q).symm))
  map_zero_left := fun y => by
    show (cylCollarEquiv q) (collarShrinkProdPair ((0 : unitInterval), (cylCollarEquiv q).symm y)) = y
    have h1 : collarShrinkProdPair ((0 : unitInterval), (cylCollarEquiv q).symm y)
        = collarShrinkProd (0 : unitInterval) ((cylCollarEquiv q).symm y) := rfl
    rw [h1]
    have h2 : collarShrinkProd (0 : unitInterval) ((cylCollarEquiv q).symm y)
        = (cylCollarEquiv q).symm y := by
      refine Prod.ext (collarShrinkProd_apply 0 _) ?_
      refine Subtype.ext ?_
      rw [collarShrinkProd_snd_apply, unitIntervalMulSub_zero_left]
    rw [h2]
    exact Homeomorph.apply_symm_apply _ y
  map_one_left := fun y => by
    show (cylCollarEquiv q) (collarShrinkProdPair ((1 : unitInterval), (cylCollarEquiv q).symm y))
      = cylShrinkRetract q y
    have h1 : collarShrinkProdPair ((1 : unitInterval), (cylCollarEquiv q).symm y)
        = collarShrinkProd (1 : unitInterval) ((cylCollarEquiv q).symm y) := rfl
    rw [h1, cylShrinkRetract_apply, cylShrink_apply]

theorem cylShrinkHomotopy_apply (q : C(X, Γ)) (s : unitInterval) (y : ↥(cylCollar q)) :
    cylShrinkHomotopy q (s, y) = cylShrink q s y := by
  show (cylCollarEquiv q) (collarShrinkProdPair (s, (cylCollarEquiv q).symm y)) = cylShrink q s y
  rw [show collarShrinkProdPair (s, (cylCollarEquiv q).symm y)
      = collarShrinkProd s ((cylCollarEquiv q).symm y) from rfl]
  rw [cylShrink_apply]

/-- The shrink homotopy is a homotopy of pairs: it preserves the bottom copy. -/
theorem cylShrinkHomotopy_mapsTo (q : C(X, Γ)) (s : unitInterval) {y : ↥(cylCollar q)}
    (hy : (y : cyl q) ∈ cylBot q) :
    ((cylShrinkHomotopy q (s, y) : ↥(cylCollar q)) : cyl q) ∈ cylBot q := by
  rw [cylShrinkHomotopy_apply, cylShrink_fixes_bot q s hy]
  exact hy


/-! ## The vanishing of the relative cohomology of the collar pair -/

/-- A morphism out of a subsingleton module is zero. -/
theorem hom_eq_zero_of_subsingleton_src {R : Type} [Ring R] {M N : ModuleCat R}
    [Subsingleton M] (f : M ⟶ N) : f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [Subsingleton.elim x 0]
  simp

/-- An endomorphism equal to zero has a subsingleton domain. -/
theorem subsingleton_of_id_eq_zero_general {R : Type} [Ring R] {M : ModuleCat R} (h : 𝟙 M = 0) :
    Subsingleton M := by
  refine ⟨fun a b => ?_⟩
  have ha : (𝟙 M : M ⟶ M).hom a = a := rfl
  have hb : (𝟙 M : M ⟶ M).hom b = b := rfl
  rw [h] at ha hb
  rw [ModuleCat.hom_zero, LinearMap.zero_apply] at ha hb
  rw [← ha, ← hb]

/-- **The relative cohomology of the collar pair `(cylCollar q, cylBot q)` vanishes.**  The shrink
homotopy `cylShrinkHomotopy q` retracts the collar onto the bottom copy through maps of pairs, so
the identity of `H^k(cylCollar q, cylBot q)` factors through
`H^k(cylBot q, cylBot q) = 0`. -/
theorem relCoh_cylCollar_vanishing (q : C(X, Γ)) (k : ℕ) :
    Subsingleton (Work.Thom.RelCoh ℚ k ↥(cylCollar q)
      {y : ↥(cylCollar q) | (y : cyl q) ∈ cylBot q}) := by
  set A : Set ↥(cylCollar q) := {y | (y : cyl q) ∈ cylBot q} with hA
  have hid : ∀ y ∈ A, (ContinuousMap.id ↥(cylCollar q)) y ∈ A := fun y hy => hy
  have hr : ∀ y ∈ A, cylShrinkRetract q y ∈ A := fun y hy => by
    show ((cylShrinkRetract q y : ↥(cylCollar q)) : cyl q) ∈ cylBot q
    rw [cylShrinkRetract_apply]
    exact cylShrink_one_mem_cylBot q y
  have hH : ∀ (s : unitInterval) (y : ↥(cylCollar q)),
      y ∈ A → cylShrinkHomotopy q (s, y) ∈ A :=
    fun s y hy => cylShrinkHomotopy_mapsTo q s hy
  have h1 : Work.Thom.relCohMap (ContinuousMap.id ↥(cylCollar q)) A A hid ℚ k
      = Work.Thom.relCohMap (cylShrinkRetract q) A A hr ℚ k :=
    Work.Thom.relCohMap_homotopic A A hid hr (cylShrinkHomotopy q) hH ℚ k
  rw [Work.Thom.relCohMap_idA A ℚ k] at h1
  have hincl : ∀ b ∈ (Set.univ : Set ↥(cylBot q)), cylBotIncl q b ∈ A := fun b _ => b.2
  have hr' : ∀ y ∈ A, cylShrinkToBot q y ∈ (Set.univ : Set ↥(cylBot q)) := fun y hy => trivial
  have hgf : ∀ y ∈ A, cylBotIncl q (cylShrinkToBot q y) ∈ A := fun y hy => hincl _ (hr' y hy)
  haveI hbot : Subsingleton (Work.Thom.RelCoh ℚ k ↥(cylBot q) Set.univ) :=
    relCohomologyUnivVanishing ℚ (TopCat.of ↥(cylBot q)) k
  have hz : Work.Thom.relCohMap (cylShrinkToBot q) A Set.univ hr' ℚ k = 0 :=
    hom_eq_zero_of_subsingleton_src _
  have hzero : (𝟙 (Work.Thom.RelCoh ℚ k ↥(cylCollar q) A)) = 0 := by
    rw [h1]
    rw [show Work.Thom.relCohMap (cylShrinkRetract q) A A hr ℚ k
        = Work.Thom.relCohMap ((cylBotIncl q).comp (cylShrinkToBot q)) A A hgf ℚ k from rfl]
    rw [← Work.Thom.relCohMap_compA A Set.univ A (cylShrinkToBot q) (cylBotIncl q)
      hr' hincl hgf ℚ k, hz, comp_zero]
  exact subsingleton_of_id_eq_zero_general hzero

end

end Work.Serre
