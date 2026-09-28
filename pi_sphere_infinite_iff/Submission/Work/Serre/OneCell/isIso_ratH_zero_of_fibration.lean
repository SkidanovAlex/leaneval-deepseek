import Mathlib
import Submission.Work.Serre.OneCell.Prelim
import Submission.Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration
import Submission.Work.Serre.Assembly.pullbackSnd_piMapN_zero_bijective

/-!
# Degree `0` of the restriction of a Serre fibration to a set with connected fibres

If `q : E → Z` is a Serre fibration and every fibre of `q` over a point of `W ⊆ Z` is path
connected, then the restriction `q⁻¹W → W` induces an isomorphism on `H₀(-;ℚ)`:
`Work.Serre.OneCell.isIso_ratH_zero_of_fibration`.

`H₀(X;ℚ)` is the free `ℚ`-module on the set of path components of `X` (Mathlib's
`TopCat.singularHomology₀Iso`, made functorial by `Work.Serre.h0Iso_natural`), so the statement is
exactly: every path component of `W` has exactly one path component of `q⁻¹W` above it.

* Injectivity on `π₀`: if two points of `q⁻¹W` have joined images in `W`, lift a path joining the
  images along the Serre fibration `q` with prescribed starting point; the lifted path stays in
  `q⁻¹W`, and its endpoint lies in the same fibre as the second point, so it can be joined to it by
  path connectedness of the fibre.
* Surjectivity on `π₀`: the fibres over `W` are nonempty.

The passage from the `π₀`-bijection to the isomorphism on `H₀(-;ℚ)` is
`Work.Serre.hZeroOfPiZero_aux` without the `[Nonempty _]` hypothesis
(`isIso_ratHomologyMap_zero_of_bijective_pi0`), which is needed here because `q⁻¹W` may be empty.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.Serre.OneCell

open Work.Serre

noncomputable section

/-- **A `π₀`-bijection induces an isomorphism on `H₀(-;ℚ)`.**  This is
`Work.Serre.hZeroOfPiZero_aux` without the `[Nonempty X]` hypothesis: the coproduct model
`H₀(X;ℚ) ≅ ∐_{π₀(X)} ℚ` and its naturality hold for the empty space too (where both sides vanish),
and the proof of `hZeroOfPiZero_aux` never uses the base point. -/
theorem isIso_ratHomologyMap_zero_of_bijective_pi0 {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (hbij : Function.Bijective (h0Pi0Map f)) :
    IsIso (ratHomologyMap f 0) := by
  change IsIso (HomologicalComplex.homologyMap
    (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) h0Coeff) 0)
  have hcf : IsIso (TypeCat.ofHom (h0Pi0Map f)) := by
    rw [show TypeCat.ofHom (h0Pi0Map f) =
      (Equiv.toIso (Equiv.ofBijective (h0Pi0Map f) hbij)).hom from rfl]
    exact Iso.isIso_hom _
  have hmk : IsIso ((sigmaConst.obj h0Coeff).map (TypeCat.ofHom (h0Pi0Map f))) :=
    Functor.map_isIso (sigmaConst.obj h0Coeff) (TypeCat.ofHom (h0Pi0Map f))
  have hg := h0Iso_natural f
  have hcomp : HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) h0Coeff) 0 =
      (h0Iso (TopCat.of X)).hom ≫ ((sigmaConst.obj h0Coeff).map (TypeCat.ofHom (h0Pi0Map f))) ≫
        (h0Iso (TopCat.of Y)).inv := by
    rw [← hg]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hcomp]
  let e : ZerothHomotopy (TopCat.of X) ≅ ZerothHomotopy (TopCat.of Y) :=
    Equiv.toIso (Equiv.ofBijective (h0Pi0Map f) hbij)
  have hmap : (sigmaConst.obj h0Coeff).map (TypeCat.ofHom (h0Pi0Map f)) =
      (sigmaConst.obj h0Coeff).map e.hom := rfl
  rw [hmap]
  exact Iso.isIso_hom ((h0Iso (TopCat.of X)) ≪≫ (sigmaConst.obj h0Coeff).mapIso e ≪≫
    (h0Iso (TopCat.of Y)).symm)

/-- **The restriction of a Serre fibration with path connected fibres over `W` is an isomorphism
on `H₀(-;ℚ)`.** -/
theorem isIso_ratH_zero_of_fibration {E Z : Type} [TopologicalSpace E] [TopologicalSpace Z]
    (q : C(E, Z)) (hq : Work.StemsB.IsSerreFibration q) (W : Set Z)
    (hfib : ∀ z : Z, z ∈ W → PathConnectedSpace (Work.StemsB.fibre q z)) :
    CategoryTheory.IsIso (Work.Serre.ratHomologyMap (Work.Serre.OneCell.restrictTo q W) 0) := by
  classical
  -- surjectivity on `π₀`: every point of `W` is the image of a point of `q⁻¹W`
  have hsurj : ∀ y : ↥W, ∃ x : ↥(q ⁻¹' W), Joined ((restrictTo q W) x) y := by
    intro y
    haveI hpc : PathConnectedSpace (Work.StemsB.fibre q (y : Z)) := hfib (y : Z) y.2
    obtain ⟨e₀⟩ := (inferInstance : Nonempty (Work.StemsB.fibre q (y : Z)))
    refine ⟨⟨e₀.1, ?_⟩, ?_⟩
    · change q (e₀.1) ∈ W
      rw [e₀.2]
      exact y.2
    · have h : (restrictTo q W ⟨e₀.1, by change q (e₀.1) ∈ W; rw [e₀.2]; exact y.2⟩ : ↥W) = y :=
        Subtype.ext e₀.2
      rw [h]
  -- injectivity on `π₀`: lift a path joining the images along `q`, then use the fibre
  have hinj : ∀ x x' : ↥(q ⁻¹' W),
      Joined ((restrictTo q W) x) ((restrictTo q W) x') → Joined x x' := by
    intro x x' hj
    obtain ⟨γ⟩ := hj
    -- the path of the base, and its lift along the fibration with prescribed starting point
    let γW : Path (q x.1) (q x'.1) := γ.map continuous_subtype_val
    let H : C(↑unitInterval × ↑unitInterval, Z) :=
      ⟨fun p => γW p.1, γW.continuous.comp continuous_fst⟩
    let f : C(↑unitInterval, E) := ContinuousMap.const _ x.1
    have hf : ∀ s : ↑unitInterval, H (0, s) = q (f s) := fun s => by
      show γW 0 = q x.1
      exact γW.source
    obtain ⟨G, hG, hG0⟩ := exists_liftPathHomotopy q hq H f hf
    -- the lift lies over the path, hence in `q⁻¹W`
    have hGval : ∀ t : ↑unitInterval, q (G (t, 0)) = ((γ t : ↥W) : Z) := by
      intro t
      have h1 : q (G (t, 0)) = H (t, 0) := by
        have := congrFun (congrArg DFunLike.coe hG) (t, 0)
        simpa [ContinuousMap.comp_apply] using this
      rw [h1]
      rfl
    have hf0 : f 0 = x.1 := rfl
    have hmem₁ : ∀ t : ↑unitInterval, G (t, 0) ∈ q ⁻¹' W := fun t => by
      change q (G (t, 0)) ∈ W
      rw [hGval t]
      exact (γ t).2
    have hcont₁ : Continuous fun t : ↑unitInterval => (⟨G (t, 0), hmem₁ t⟩ : ↥(q ⁻¹' W)) :=
      Continuous.subtype_mk (G.continuous.comp (continuous_id.prodMk continuous_const)) hmem₁
    let c₁ : C(↑unitInterval, ↥(q ⁻¹' W)) := ⟨fun t => ⟨G (t, 0), hmem₁ t⟩, hcont₁⟩
    have hc₁ : c₁ 0 = x := Subtype.ext (by show G (0, 0) = x.1; rw [hG0 0, hf0])
    -- the endpoint `x₁` of the lift lies in the fibre of `q` over the image of `x'`
    let x₁ : ↥(q ⁻¹' W) := c₁ 1
    have hx₁ : q x₁.1 = q x'.1 := by
      have h1 : q (G (1, 0)) = ((γ 1 : ↥W) : Z) := hGval 1
      rw [show x₁.1 = G (1, 0) from rfl, h1, γ.target]
      exact restrictTo_apply q W x'
    let P₁ : Path x x₁ := Path.mk c₁ hc₁ rfl
    -- `x₁` and `x'` lie in the same fibre, which is path connected
    haveI hpc : PathConnectedSpace (Work.StemsB.fibre q (q x'.1)) := hfib (q x'.1) x'.2
    let F₁ : Work.StemsB.fibre q (q x'.1) := ⟨x₁.1, hx₁⟩
    let F₂ : Work.StemsB.fibre q (q x'.1) := ⟨x'.1, rfl⟩
    obtain ⟨β⟩ := PathConnectedSpace.joined F₁ F₂
    have hmem₂ : ∀ t : ↑unitInterval, (β t).1 ∈ q ⁻¹' W := fun t => by
      change q ((β t).1) ∈ W
      rw [(β t).2]
      exact x'.2
    have hcont₂ : Continuous fun t : ↑unitInterval => (⟨(β t).1, hmem₂ t⟩ : ↥(q ⁻¹' W)) :=
      Continuous.subtype_mk (continuous_subtype_val.comp β.continuous) hmem₂
    have P₂ : Path x₁ x' :=
      Path.mk ⟨fun t : ↑unitInterval => ⟨(β t).1, hmem₂ t⟩, hcont₂⟩
        (Subtype.ext (by show (β 0).1 = x₁.1; rw [β.source]))
        (Subtype.ext (by show (β 1).1 = x'.1; rw [β.target]))
    exact ⟨P₁.trans P₂⟩
  have hbij : Function.Bijective (h0Pi0Map (restrictTo q W)) :=
    ⟨Assembly.injective_h0Pi0Map_of_joined _ hinj,
      Assembly.surjective_h0Pi0Map_of_joined _ hsurj⟩
  exact isIso_ratHomologyMap_zero_of_bijective_pi0 (restrictTo q W) hbij

end

end Work.Serre.OneCell
