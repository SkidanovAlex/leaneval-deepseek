import Mathlib
import Submission.Work.CY3Stab.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Prod.specTensorTo_bot_mem_closure`

The geometric input of the stabilisation step: for a point `q` of the cylinder
`P = 𝔸ⁿ ×_{Spec 𝕜} X` lying over `x = T.y`, the point `q` lies in the closure of the "cylinder
generic point" `T.SpecTensorTo ⊥` of the `Triplet` fibre over `(genericPoint 𝔸ⁿ, x)`.

## Mathematical content

Let `S = Spec 𝕜`, `Y = 𝔸(n; S)`, `f = Y ↘ S`, `g_X = X ↘ S` and `P = Y ×_S X`.  The point
`p := T.SpecTensorTo ⊥` has `fst p = T.x = genericPoint Y` and `snd p = T.y = x`, and the
`Spec`-fibre of `T.SpecTensorTo` is exactly the fibre of `(fst, snd)` over `(T.x, T.y)`.

The proof is by exhibiting a *single* irreducible scheme mapping into `P` whose image contains
both `p` and `q`, namely the scheme-theoretic fibre of `snd : P ⟶ X` over `x`:

* `F := (pullback.snd f g_X).fiber x = P ×_X Spec κ(x) = 𝔸ⁿ ×_{Spec 𝕜} Spec κ(x)`, which is
  *integral* (it is the fibre of the base change of the geometrically integral morphism
  `𝔸ⁿ ⟶ Spec 𝕜`, Mathlib's `IsIntegral (f.fiber s)` instance) and hence irreducible;
* its image in `P` under `ι := (pullback.snd f g_X).fiberι x` is exactly
  `snd ⁻¹' {x}` (`Scheme.Hom.range_fiberι`), so that `q ∈ range ι` (because `snd q = x`)
  and `range ι ⊆ closure {ι η}` for `η = genericPoint F` (irreducibility);
* `ι η` lies in the `Spec`-fibre of `T.SpecTensorTo`, i.e. in `closure {p}`: its `snd` is `x`
  (`Scheme.fromSpecResidueField_apply`) and its `fst` is `genericPoint Y = T.x` (the projection
  `pullback.fst f κ(x)` is surjective, so it maps the generic point to the generic point);

so `closure {ι η} ⊆ closure {p}` and `q ∈ closure {ι η} ⊆ closure {p}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

/-! ## 1. Two topological lemmas -/

/-- **The image of an irreducible space is contained in the closure of the image of its generic
point.** -/
theorem range_subset_closure_genericPoint {Z P : Type*} [TopologicalSpace Z] [TopologicalSpace P]
    [IrreducibleSpace Z] [QuasiSober Z] {j : Z → P} (hc : Continuous j) :
    Set.range j ⊆ closure ({j (genericPoint Z)} : Set P) := by
  calc Set.range j = j '' (Set.univ : Set Z) := by rw [Set.image_univ]
    _ = j '' closure ({genericPoint Z} : Set Z) := by rw [genericPoint_closure]
    _ ⊆ closure (j '' ({genericPoint Z} : Set Z)) := image_closure_subset_closure_image hc
    _ = closure ({j (genericPoint Z)} : Set P) := by rw [Set.image_singleton]

/-- **A surjective continuous map sends the generic point to the generic point.** -/
theorem map_genericPoint_eq_of_surjective {Z P : Type*} [TopologicalSpace Z] [TopologicalSpace P]
    [IrreducibleSpace Z] [IrreducibleSpace P] [QuasiSober Z] [QuasiSober P]
    [T0Space Z] [T0Space P] {j : Z → P} (hf : Function.Surjective j) (hc : Continuous j) :
    j (genericPoint Z) = genericPoint P := by
  have hsub : Set.range j ⊆ closure ({j (genericPoint Z)} : Set P) := by
    calc Set.range j = j '' (Set.univ : Set Z) := by rw [Set.image_univ]
      _ = j '' closure ({genericPoint Z} : Set Z) := by rw [genericPoint_closure]
      _ ⊆ closure (j '' ({genericPoint Z} : Set Z)) := image_closure_subset_closure_image hc
      _ = closure ({j (genericPoint Z)} : Set P) := by rw [Set.image_singleton]
  have hgen : IsGenericPoint (j (genericPoint Z)) Set.univ := by
    rw [isGenericPoint_def]
    apply le_antisymm le_top
    rw [show (⊤ : Set P) = Set.range j from (Set.range_eq_univ.mpr hf).symm]
    exact hsub
  exact hgen.eq (genericPoint_spec P)

/-! ## 2. The main statement -/

theorem specTensorTo_bot_mem_closure {𝕜 : Type} [Field 𝕜] {n : Type}
    (X : AlgebraicGeometry.Scheme.{0})
    [X.Over (Spec (CommRingCat.of 𝕜))] (x : X)
    (T : Pullback.Triplet (𝔸(n; Spec (CommRingCat.of 𝕜)) ↘ Spec (CommRingCat.of 𝕜))
      (X ↘ Spec (CommRingCat.of 𝕜)))
    (hTx : T.x = genericPoint (𝔸(n; Spec (CommRingCat.of 𝕜))))
    (hTy : T.y = x) [IsDomain T.tensor]
    (q : ↥(Limits.pullback (𝔸(n; Spec (CommRingCat.of 𝕜)) ↘ Spec (CommRingCat.of 𝕜))
      (X ↘ Spec (CommRingCat.of 𝕜))))
    (hq : Limits.pullback.snd (𝔸(n; Spec (CommRingCat.of 𝕜)) ↘ Spec (CommRingCat.of 𝕜))
      (X ↘ Spec (CommRingCat.of 𝕜)) q = x) :
    q ∈ closure {T.SpecTensorTo (⊥ : PrimeSpectrum T.tensor)} := by
  let S := Spec (CommRingCat.of 𝕜)
  let Y := 𝔸(n; S)
  let f : Y ⟶ S := Y ↘ S
  let gX : X ⟶ S := X ↘ S
  let P : Scheme := pullback f gX
  -- the scheme-theoretic fibre of `snd : P ⟶ X` over `x`
  let F : Scheme := pullback f (X.fromSpecResidueField x ≫ gX)
  let ι : F ⟶ P :=
    pullback.map f (X.fromSpecResidueField x ≫ gX) f gX (𝟙 Y) (X.fromSpecResidueField x) (𝟙 S)
      (by simp) (by simp)
  have hmapfst : ι ≫ pullback.fst f gX = pullback.fst f (X.fromSpecResidueField x ≫ gX) := by
    simp only [ι, pullback.map, pullback.lift_fst, Category.comp_id]
  have hmapsnd : ι ≫ pullback.snd f gX =
      pullback.snd f (X.fromSpecResidueField x ≫ gX) ≫ X.fromSpecResidueField x := by
    simp only [ι, pullback.map, pullback.lift_snd, Category.comp_id]
  have hsurj : Surjective (X.fromSpecResidueField x ≫ gX : Spec (X.residueField x) ⟶ S) := by
    rw [surjective_iff]
    intro y
    exact ⟨IsLocalRing.closedPoint ↥(X.residueField x), Subsingleton.elim _ _⟩
  haveI : Surjective (pullback.fst f (X.fromSpecResidueField x ≫ gX)) := inferInstance
  haveI hIntF : IsIntegral F := inferInstance
  haveI : IrreducibleSpace F := inferInstance
  have hrange : Set.range ι = ⇑(pullback.snd f gX) ⁻¹' {x} := by
    rw [Pullback.range_map]
    simp [Scheme.range_fromSpecResidueField]
  have hgen_pt : (⊥ : PrimeSpectrum ↥T.tensor) = genericPoint (Spec T.tensor) :=
    (genericPoint_eq_bot_of_affine T.tensor).symm
  suffices hmain : q ∈ closure
      ({T.SpecTensorTo (genericPoint (Spec T.tensor))} : Set P) by
    convert hmain using 1
    rw [show T.SpecTensorTo (⊥ : PrimeSpectrum ↥T.tensor)
        = T.SpecTensorTo (genericPoint (Spec T.tensor)) from congrArg T.SpecTensorTo hgen_pt]
  have hq_mem : q ∈ Set.range ι := by
    rw [hrange, Set.mem_preimage, Set.mem_singleton_iff]
    exact hq
  have hrangeι : Set.range ι ⊆ closure ({ι (genericPoint F)} : Set P) :=
    range_subset_closure_genericPoint ι.continuous
  have hη_fst : pullback.fst f gX (ι (genericPoint F)) = T.x := by
    rw [← Scheme.Hom.comp_apply, hmapfst, hTx]
    exact map_genericPoint_eq_of_surjective
      (j := ⇑(pullback.fst f (X.fromSpecResidueField x ≫ gX)))
      ((surjective_iff _).mp inferInstance)
      (pullback.fst f (X.fromSpecResidueField x ≫ gX)).continuous
  have hη_snd : pullback.snd f gX (ι (genericPoint F)) = T.y := by
    rw [← Scheme.Hom.comp_apply, hmapsnd, Scheme.Hom.comp_apply,
      Scheme.fromSpecResidueField_apply, hTy]
  -- the `Spec`-fibre of `T.SpecTensorTo` is the fibre of `(fst, snd)` over `(T.x, T.y)`
  have h_range_SpecTensorTo : Set.range T.SpecTensorTo =
      {z : P | pullback.fst f gX z = T.x ∧ pullback.snd f gX z = T.y} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨Pullback.Triplet.fst_SpecTensorTo_apply (T := T) w,
        Pullback.Triplet.snd_SpecTensorTo_apply (T := T) w⟩
    · rintro ⟨h1, h2⟩
      have hof : Pullback.Triplet.ofPoint z = T := Pullback.Triplet.ext h1 h2
      rw [← hof]
      exact ⟨Pullback.SpecOfPoint z, Pullback.SpecTensorTo_SpecOfPoint z⟩
  have hιη_range : ι (genericPoint F) ∈ Set.range T.SpecTensorTo := by
    rw [h_range_SpecTensorTo]
    exact ⟨hη_fst, hη_snd⟩
  have hιη_closure : ι (genericPoint F) ∈ closure
      ({T.SpecTensorTo (genericPoint (Spec T.tensor))} : Set P) :=
    (range_subset_closure_genericPoint (P := P) T.SpecTensorTo.continuous) hιη_range
  have hclosure : closure ({ι (genericPoint F)} : Set P) ⊆ closure
      ({T.SpecTensorTo (genericPoint (Spec T.tensor))} : Set P) :=
    closure_minimal (Set.singleton_subset_iff.mpr hιη_closure) isClosed_closure
  exact hclosure (hrangeι hq_mem)

end

end Work.CY3Stab.Prod
