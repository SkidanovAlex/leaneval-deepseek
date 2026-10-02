import Mathlib
import Submission.Work.Bordism.Basic
import Submission.Work.Bordism.cohomology_coprod_iso
import Submission.Work.Bordism.interForm_coprod
import Submission.Work.Bordism.chainC_coprod_iso
import Submission.Work.Bordism.toSSet_coprod_iso
import Submission.Work.Bordism.chainC_coprod_split
import Submission.Work.SignatureBordism.Bordism
import Submission.Work.Bordism.Middle
import Submission.Work.SignatureBordism.signature_prod

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Additivity of the signature under disjoint unions

For closed oriented `2k`-manifolds `M`, `N` in the model of
`Submission/Work/Bordism/Basic.lean`, the signature of the disjoint union is the sum of the
signatures:

`σ(M ⊔ N) = σ(M) + σ(N)`

(`Work.Bordism.sigma_disj`).

## The proof

The intersection *pairing* of `M ⊔ N` is evaluated against the fundamental class
`(inl)_*[M] + (inr)_*[N]`, so `Work.Bordism.interForm_coprod` identifies it with the orthogonal sum
of the two intersection pairings of the pieces, with classes pulled back along the coproduct
inclusions (`Work.Bordism.interForm_coprod_eq`, rationalised as
`Work.Bordism.ratInterForm_coprod_disj`).

The rationalised middle cohomology of the disjoint union splits as the *product* of the two middle
cohomologies, with components the two pullbacks: the map

`y ↦ (inl* y, inr* y) : Hᵏ(M ⊔ N;ℚ) ⟶ Hᵏ(M;ℚ) × Hᵏ(N;ℚ)`

is a bijection (`Work.Bordism.pullbackRat_coprod_bijective_aux`).  This is the compatibility of the
cohomological Künneth splitting `Work.Bordism.cohomology_coprod_iso` with the pullbacks `inl*`,
`inr*`, and it is what makes the middle form of `M ⊔ N` the composite of the middle form of
`ḴM ⊥ N` with a **linear equivalence**: the coproduct inclusions of the singular chains of the two
pieces split it off as a biproduct (`Work.Bordism.chainC_coprod_split`), the dual cochain
complexes inherit the splitting (`Work.Bordism.dualComplexMap`), and on rationalised cohomology the
resulting maps are a section and a retraction of the two pullbacks.

The result then follows from `Work.SignatureBordism.signature_comp_linearEquiv` (Sylvester's law of
inertia: isometric forms have the same signature) and `Work.SignatureBordism.signature_prod`
(additivity of the signature over orthogonal direct sums).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology
open scoped Simplicial

namespace Work.Bordism

open Work.Cohomology Work.SignatureBordism

noncomputable section

/-! ## The intersection form of a disjoint union -/

/-- **The base change to `ℚ` of a bilinear form commutes with `compl₁₂`**: reindexing an integral
bilinear form along two linear maps and then rationalising is the same as rationalising first and
then reindexing along the base changes. -/
theorem baseChangeBilin_compl₁₂ {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (B : N →ₗ[ℤ] N →ₗ[ℤ] ℤ) (φ ψ : M →ₗ[ℤ] N) :
    baseChangeBilin (B.compl₁₂ φ ψ)
      = (baseChangeBilin B).compl₁₂ (φ.baseChange ℚ) (ψ.baseChange ℚ) := by
  apply tensor_bilin_ext
  intro a b x y
  simp only [baseChangeBilin_tmul, LinearMap.compl₁₂_apply, LinearMap.baseChange_tmul]

/-- **`Work.Bordism.interForm_coprod`, as an identity of bilinear forms**: the intersection
*pairing* of a disjoint union is the sum of the intersection pairings of the two pieces, pulled
back along the coproduct inclusions. -/
theorem interForm_coprod_eq {k : ℕ} (M N : ClosedOriented (k + k)) :
    interForm ℤ (TopCat.toSSet.obj (M.X ⨿ N.X)) k k (ClosedOriented.disj M N).c
      = (interForm ℤ (TopCat.toSSet.obj M.X) k k M.c).compl₁₂
          (singularCohomologyMap ℤ M.X (M.X ⨿ N.X) CategoryTheory.Limits.coprod.inl k).hom
          (singularCohomologyMap ℤ M.X (M.X ⨿ N.X) CategoryTheory.Limits.coprod.inl k).hom
        + (interForm ℤ (TopCat.toSSet.obj N.X) k k N.c).compl₁₂
          (singularCohomologyMap ℤ N.X (M.X ⨿ N.X) CategoryTheory.Limits.coprod.inr k).hom
          (singularCohomologyMap ℤ N.X (M.X ⨿ N.X) CategoryTheory.Limits.coprod.inr k).hom := by
  apply LinearMap.ext
  intro y
  apply LinearMap.ext
  intro z
  exact interForm_coprod M N y z

/-- **The rationalised intersection pairing of a disjoint union is the orthogonal sum of the
rationalised intersection pairings of the pieces.** -/
theorem ratInterForm_coprod_disj {k : ℕ} (M N : ClosedOriented (k + k)) :
    ratInterForm k (TopCat.toSSet.obj (M.X ⨿ N.X)) (ClosedOriented.disj M N).c =
      (ratInterForm k (TopCat.toSSet.obj M.X) M.c).compl₁₂
          (pullbackRat k (CategoryTheory.Limits.coprod.inl))
          (pullbackRat k (CategoryTheory.Limits.coprod.inl))
        + (ratInterForm k (TopCat.toSSet.obj N.X) N.c).compl₁₂
          (pullbackRat k (CategoryTheory.Limits.coprod.inr))
          (pullbackRat k (CategoryTheory.Limits.coprod.inr)) := by
  unfold ratInterForm pullbackRat
  rw [← baseChangeBilin_compl₁₂, ← baseChangeBilin_compl₁₂, ← baseChangeBilin_add,
    ← interForm_coprod_eq]

/-! ## The splitting of the cohomology of a disjoint union -/

/-- The dual of the zero chain map is the zero cochain map. -/
theorem dualComplexMap_zero {C D : ChainComplex (ModuleCat ℤ) ℕ} :
    dualComplexMap ℤ C D 0 = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [dualComplexMap_f]
  apply ModuleCat.hom_ext
  ext φ x
  rw [dualComplexMapComp_apply, HomologicalComplex.zero_f_apply]
  simp

/-- **The rationalised cohomology of a disjoint union splits off its two summands.**

The pullbacks along the two coproduct inclusions exhibit `Hᵏ(X ⊔ Y;ℚ)` as the product
`Hᵏ(X;ℚ) × Hᵏ(Y;ℚ)`:

`y ↦ (inl* y, inr* y)`

is a bijection.  This is the sharpening of `Work.Bordism.cohomology_coprod_iso` needed for
additivity of the signature: the Künneth splitting of the cohomology of a disjoint union *is* given
by the two pullbacks.

The splitting is inherited from the chain level: the coproduct inclusions of the singular chains
split `C_*(X ⊔ Y)` off its two summands (`Work.Bordism.chainC_coprod_split`, giving `p`, `q` with
`f ≫ p = 1`, `g ≫ q = 1`, `f ≫ q = 0`, `g ≫ p = 0`, `p ≫ f + q ≫ g = 1`), and dualising exhibits
the pullbacks `f^*`, `g^*` as a coprojection and a projection of the cohomology. -/
theorem pullbackRat_coprod_bijective_aux (X Y : TopCat) (k : ℕ) :
    Function.Bijective (LinearMap.prod
      (pullbackRat k (CategoryTheory.Limits.coprod.inl : X ⟶ X ⨿ Y))
      (pullbackRat k (CategoryTheory.Limits.coprod.inr : Y ⟶ X ⨿ Y))) := by
  obtain ⟨p, q, h1, h2, h3, h4, h5⟩ := chainC_coprod_split X Y
  let A := singularChains ℤ X
  let Bt := singularChains ℤ Y
  let Pp := singularChains ℤ (X ⨿ Y)
  let f : A ⟶ Pp := chainMap ℤ X (X ⨿ Y) CategoryTheory.Limits.coprod.inl
  let g : Bt ⟶ Pp := chainMap ℤ Y (X ⨿ Y) CategoryTheory.Limits.coprod.inr
  let p' : Pp ⟶ A := p
  let q' : Pp ⟶ Bt := q
  have h1' : f ≫ p' = 𝟙 A := h1
  have h2' : g ≫ q' = 𝟙 Bt := h2
  have h3' : f ≫ q' = 0 := h3
  have h4' : g ≫ p' = 0 := h4
  have h5' : p' ≫ f + q' ≫ g = 𝟙 Pp := h5
  -- the dualised cochain maps
  let Fd := dualComplexMap ℤ A Pp f
  let Gd := dualComplexMap ℤ Bt Pp g
  let Pd := dualComplexMap ℤ Pp A p'
  let Qd := dualComplexMap ℤ Pp Bt q'
  have e1 : Pd ≫ Fd = 𝟙 (dualComplex ℤ A) := by
    have h := dualComplexMap_comp ℤ f p'
    rw [h1', dualComplexMap_id] at h
    exact h.symm
  have e2 : Qd ≫ Gd = 𝟙 (dualComplex ℤ Bt) := by
    have h := dualComplexMap_comp ℤ g q'
    rw [h2', dualComplexMap_id] at h
    exact h.symm
  have e3 : Qd ≫ Fd = 0 := by
    have h := dualComplexMap_comp ℤ f q'
    rw [h3', dualComplexMap_zero] at h
    exact h.symm
  have e4 : Pd ≫ Gd = 0 := by
    have h := dualComplexMap_comp ℤ g p'
    rw [h4', dualComplexMap_zero] at h
    exact h.symm
  have e5 : Fd ≫ Pd + Gd ≫ Qd = 𝟙 (dualComplex ℤ Pp) := by
    have h := congrArg (dualComplexMap ℤ Pp Pp) h5'
    rw [dualComplexMap_add', dualComplexMap_comp, dualComplexMap_comp, dualComplexMap_id] at h
    exact h
  -- the induced maps on cohomology, as `ℤ`-linear maps
  let Fh : ((dualComplex ℤ Pp).homology k) →ₗ[ℤ] ((dualComplex ℤ A).homology k) :=
    (HomologicalComplex.homologyMap Fd k).hom
  let Gh : ((dualComplex ℤ Pp).homology k) →ₗ[ℤ] ((dualComplex ℤ Bt).homology k) :=
    (HomologicalComplex.homologyMap Gd k).hom
  let Ph : ((dualComplex ℤ A).homology k) →ₗ[ℤ] ((dualComplex ℤ Pp).homology k) :=
    (HomologicalComplex.homologyMap Pd k).hom
  let Qh : ((dualComplex ℤ Bt).homology k) →ₗ[ℤ] ((dualComplex ℤ Pp).homology k) :=
    (HomologicalComplex.homologyMap Qd k).hom
  have H1 : Fh.comp Ph = LinearMap.id := by
    show (HomologicalComplex.homologyMap Fd k).hom.comp (HomologicalComplex.homologyMap Pd k).hom
      = LinearMap.id
    rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp, e1,
      HomologicalComplex.homologyMap_id, ModuleCat.hom_id]
  have H2 : Gh.comp Qh = LinearMap.id := by
    show (HomologicalComplex.homologyMap Gd k).hom.comp (HomologicalComplex.homologyMap Qd k).hom
      = LinearMap.id
    rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp, e2,
      HomologicalComplex.homologyMap_id, ModuleCat.hom_id]
  have H3 : Fh.comp Qh = 0 := by
    show (HomologicalComplex.homologyMap Fd k).hom.comp (HomologicalComplex.homologyMap Qd k).hom = 0
    rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp, e3,
      HomologicalComplex.homologyMap_zero, ModuleCat.hom_zero]
  have H4 : Gh.comp Ph = 0 := by
    show (HomologicalComplex.homologyMap Gd k).hom.comp (HomologicalComplex.homologyMap Pd k).hom = 0
    rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp, e4,
      HomologicalComplex.homologyMap_zero, ModuleCat.hom_zero]
  have H5 : Ph.comp Fh + Qh.comp Gh = LinearMap.id := by
    show (HomologicalComplex.homologyMap Pd k).hom.comp (HomologicalComplex.homologyMap Fd k).hom
        + (HomologicalComplex.homologyMap Qd k).hom.comp
            (HomologicalComplex.homologyMap Gd k).hom = LinearMap.id
    rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
      ← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
      ← ModuleCat.hom_add, ← HomologicalComplex.homologyMap_add, e5,
      HomologicalComplex.homologyMap_id, ModuleCat.hom_id]
  -- base change to `ℚ`
  have hQ1 : (Fh.baseChange ℚ).comp (Ph.baseChange ℚ) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, H1, LinearMap.baseChange_id]
  have hQ2 : (Gh.baseChange ℚ).comp (Qh.baseChange ℚ) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, H2, LinearMap.baseChange_id]
  have hQ3 : (Gh.baseChange ℚ).comp (Ph.baseChange ℚ) = 0 := by
    rw [← LinearMap.baseChange_comp, H4, LinearMap.baseChange_zero]
  have hQ4 : (Fh.baseChange ℚ).comp (Qh.baseChange ℚ) = 0 := by
    rw [← LinearMap.baseChange_comp, H3, LinearMap.baseChange_zero]
  have hQ5 : (Ph.baseChange ℚ).comp (Fh.baseChange ℚ)
      + (Qh.baseChange ℚ).comp (Gh.baseChange ℚ) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_add, H5,
      LinearMap.baseChange_id]
  have hF : pullbackRat k (CategoryTheory.Limits.coprod.inl : X ⟶ X ⨿ Y) = Fh.baseChange ℚ := by
    rw [pullbackRat]
    congr 1
  have hG : pullbackRat k (CategoryTheory.Limits.coprod.inr : Y ⟶ X ⨿ Y) = Gh.baseChange ℚ := by
    rw [pullbackRat]
    congr 1
  have pt1 : ∀ x, Fh.baseChange ℚ (Ph.baseChange ℚ x) = x := fun x => by
    have h := congrArg (fun (z : _ →ₗ[ℚ] _) => z x) hQ1
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h
    exact h
  have pt2 : ∀ y, Gh.baseChange ℚ (Qh.baseChange ℚ y) = y := fun y => by
    have h := congrArg (fun (z : _ →ₗ[ℚ] _) => z y) hQ2
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h
    exact h
  have pt3 : ∀ x, Gh.baseChange ℚ (Ph.baseChange ℚ x) = 0 := fun x => by
    have h := congrArg (fun (z : _ →ₗ[ℚ] _) => z x) hQ3
    rw [LinearMap.comp_apply] at h
    exact h
  have pt4 : ∀ y, Fh.baseChange ℚ (Qh.baseChange ℚ y) = 0 := fun y => by
    have h := congrArg (fun (z : _ →ₗ[ℚ] _) => z y) hQ4
    rw [LinearMap.comp_apply] at h
    exact h
  have pt5 : ∀ x, Ph.baseChange ℚ (Fh.baseChange ℚ x)
      + Qh.baseChange ℚ (Gh.baseChange ℚ x) = x := fun x => by
    have h := congrArg (fun (z : _ →ₗ[ℚ] _) => z x) hQ5
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.id_apply] at h
    exact h
  constructor
  · rintro w w' hw
    have h1w : Fh.baseChange ℚ w = Fh.baseChange ℚ w' := by
      have h := congrArg Prod.fst hw
      rw [hF] at h
      exact h
    have h2w : Gh.baseChange ℚ w = Gh.baseChange ℚ w' := by
      have h := congrArg Prod.snd hw
      rw [hG] at h
      exact h
    rw [(pt5 w).symm, (pt5 w').symm, h1w, h2w]
  · intro v
    refine ⟨Ph.baseChange ℚ v.1 + Qh.baseChange ℚ v.2, ?_⟩
    have h1 : Fh.baseChange ℚ (Ph.baseChange ℚ v.1 + Qh.baseChange ℚ v.2) = v.1 := by
      rw [map_add, pt1 v.1, pt4 v.2, add_zero]
    have h2 : Gh.baseChange ℚ (Ph.baseChange ℚ v.1 + Qh.baseChange ℚ v.2) = v.2 := by
      rw [map_add, pt3 v.1, pt2 v.2, zero_add]
    exact Prod.ext h1 h2

/-! ## Additivity of the signature -/

/-- **Additivity of the signature under disjoint unions**, in the form in which the fundamental
class of `M ⊔ N` is displayed through the coproduct of the underlying spaces. -/
theorem sigma_disj_aux {k : ℕ} (M N : ClosedOriented (k + k))
    [FiniteDimensional ℚ (ratCohomology k (TopCat.toSSet.obj M.X))]
    [FiniteDimensional ℚ (ratCohomology k (TopCat.toSSet.obj N.X))] :
    sigma k (TopCat.toSSet.obj (M.X ⨿ N.X)) (ClosedOriented.disj M N).c
      = sigma k (TopCat.toSSet.obj M.X) M.c + sigma k (TopCat.toSSet.obj N.X) N.c := by
  let Φ : ratCohomology k (TopCat.toSSet.obj (M.X ⨿ N.X)) →ₗ[ℚ]
      (ratCohomology k (TopCat.toSSet.obj M.X) × ratCohomology k (TopCat.toSSet.obj N.X)) :=
    LinearMap.prod (pullbackRat k (CategoryTheory.Limits.coprod.inl : M.X ⟶ M.X ⨿ N.X))
      (pullbackRat k (CategoryTheory.Limits.coprod.inr : N.X ⟶ M.X ⨿ N.X))
  have hbij : Function.Bijective Φ := pullbackRat_coprod_bijective_aux M.X N.X k
  let e : ratCohomology k (TopCat.toSSet.obj (M.X ⨿ N.X)) ≃ₗ[ℚ]
      (ratCohomology k (TopCat.toSSet.obj M.X) × ratCohomology k (TopCat.toSSet.obj N.X)) :=
    LinearEquiv.ofBijective Φ hbij
  have he : (e : ratCohomology k (TopCat.toSSet.obj (M.X ⨿ N.X)) →ₗ[ℚ]
      (ratCohomology k (TopCat.toSSet.obj M.X) × ratCohomology k (TopCat.toSSet.obj N.X))) = Φ :=
    rfl
  have hform : midForm (ClosedOriented.disj M N) =
      ((midForm M).prod (midForm N)).comp (e : ratCohomology k (TopCat.toSSet.obj (M.X ⨿ N.X)) →ₗ[ℚ]
        (ratCohomology k (TopCat.toSSet.obj M.X) × ratCohomology k (TopCat.toSSet.obj N.X))) := by
    rw [he]
    apply QuadraticMap.ext
    intro x
    show ratInterForm k (TopCat.toSSet.obj (M.X ⨿ N.X)) (ClosedOriented.disj M N).c x x
        = (ratInterForm k (TopCat.toSSet.obj M.X) M.c)
            (pullbackRat k (CategoryTheory.Limits.coprod.inl : M.X ⟶ M.X ⨿ N.X) x)
            (pullbackRat k (CategoryTheory.Limits.coprod.inl : M.X ⟶ M.X ⨿ N.X) x)
          + (ratInterForm k (TopCat.toSSet.obj N.X) N.c)
            (pullbackRat k (CategoryTheory.Limits.coprod.inr : N.X ⟶ M.X ⨿ N.X) x)
            (pullbackRat k (CategoryTheory.Limits.coprod.inr : N.X ⟶ M.X ⨿ N.X) x)
    exact congrArg (fun (F : ratCohomology k (TopCat.toSSet.obj (M.X ⨿ N.X)) →ₗ[ℚ]
        ratCohomology k (TopCat.toSSet.obj (M.X ⨿ N.X)) →ₗ[ℚ] ℚ) => F x x)
      (ratInterForm_coprod_disj M N)
  calc sigma k (TopCat.toSSet.obj (M.X ⨿ N.X)) (ClosedOriented.disj M N).c
      = signature (midForm (ClosedOriented.disj M N)) := rfl
    _ = signature (((midForm M).prod (midForm N)).comp
          (e : ratCohomology k (TopCat.toSSet.obj (M.X ⨿ N.X)) →ₗ[ℚ]
            (ratCohomology k (TopCat.toSSet.obj M.X) ×
              ratCohomology k (TopCat.toSSet.obj N.X)))) := by
        rw [hform]
    _ = signature ((midForm M).prod (midForm N)) := signature_comp_linearEquiv _ e
    _ = signature (midForm M) + signature (midForm N) := signature_prod _ _
    _ = sigma k (TopCat.toSSet.obj M.X) M.c + sigma k (TopCat.toSSet.obj N.X) N.c := rfl

theorem sigma_disj {k : ℕ} (M N : Work.Bordism.ClosedOriented (k + k))
    [FiniteDimensional ℚ (Work.SignatureBordism.ratCohomology k (TopCat.toSSet.obj M.X))]
    [FiniteDimensional ℚ (Work.SignatureBordism.ratCohomology k (TopCat.toSSet.obj N.X))] :
    Work.SignatureBordism.sigma k
        (TopCat.toSSet.obj (Work.Bordism.ClosedOriented.disj M N).X)
        (Work.Bordism.ClosedOriented.disj M N).c
      = Work.SignatureBordism.sigma k (TopCat.toSSet.obj M.X) M.c
        + Work.SignatureBordism.sigma k (TopCat.toSSet.obj N.X) N.c :=
  sigma_disj_aux M N

end

end Work.Bordism
