import Mathlib
import Submission.Work.ATOM.Defs

/-!
# `Work.ATOM.homKSinglePrecomp`

Let `u : A ⟶ A` be such that precomposition with `u` is a bijection on `Hom(A, K^q)` for every
degree `q`. Then precomposition with `(singleC n).map u` is a bijection on
`Hom_{K(C)}(singleC n A, K)`.

The proof goes through `CohomologyClass (singleC n A) K 0 ≅ Hom_{K(C)}(singleC n A, K⟦0⟧)`:
* `toHom_mk_precomp` shows that this identification is compatible with precomposition, so that
  it suffices to know that the induced map on cohomology classes is bijective;
* a `0`-cocycle `singleC n A ⟶ K` is `Cocycle.fromSingleMk f` for `f : A ⟶ K.X n` with
  `f ≫ K.d n (n+1) = 0`, and precomposing with `(singleC n).map u` sends it to
  `Cocycle.fromSingleMk (u ≫ f)`; a `fromSingleMk f` is a coboundary iff
  `f = g ≫ K.d (n-1) n` for some `g : A ⟶ K.X (n-1)`. This reduces bijectivity on the
  quotient to bijectivity of `f ↦ u ≫ f` on the relevant spaces `Hom(A, K^q)`
  (at `q = n - 1`, `q = n` and `q = n + 1`);
* finally the canonical isomorphism `K⟦0⟧ ≅ K` is used: postcomposition with an isomorphism
  commutes with precomposition, so bijectivity for the target `K⟦0⟧` transfers to `K`.
-/

set_option linter.unusedSectionVars false

namespace Work.ATOM

open CategoryTheory Limits CochainComplex.HomComplex

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]

/-- The identification `CohomologyClass K' K 0 ≃ Hom_{K(C)}(K', K⟦0⟧)` given by
`CohomologyClass.toHom` is compatible with precomposition by a morphism of cochain complexes. -/
lemma toHom_mk_precomp (K' K : CochainComplex C ℤ) (F : K' ⟶ K') (z : Cocycle K' K 0) :
    CohomologyClass.toHom (CohomologyClass.mk (z.precomp F)) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map F ≫
        CohomologyClass.toHom (CohomologyClass.mk z) := by
  rw [CohomologyClass.toHom_mk, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_precomp, Functor.map_comp]

/-- Every `0`-cocycle `singleC n A ⟶ K` is obtained by precomposing another one with
`(singleC n).map u`. -/
private lemma singleC_precomp_surj (A : C) (u : A ⟶ A) (K : CochainComplex C ℤ) (n : ℤ)
    (h : ∀ q : ℤ, Function.Bijective (fun f : A ⟶ K.X q => u ≫ f))
    (z : Cocycle ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj A) K 0) :
    ∃ z' : Cocycle ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj A) K 0,
      z'.precomp ((HomologicalComplex.single C (ComplexShape.up ℤ) n).map u) = z := by
  obtain ⟨f, hf, hfz⟩ := Cocycle.fromSingleMk_surjective z n (add_zero n) (n + 1) rfl
  obtain ⟨f', hf'⟩ := (h n).surjective f
  change u ≫ f' = f at hf'
  have hf'' : f' ≫ K.d n (n + 1) = 0 := by
    refine (h (n + 1)).injective ?_
    rw [← Category.assoc, hf', hf]
    simp
  refine ⟨Cocycle.fromSingleMk f' (add_zero n) (n + 1) rfl hf'', ?_⟩
  have h1 : (Cocycle.fromSingleMk f' (add_zero n) (n + 1) rfl hf'').precomp
        ((HomologicalComplex.single C (ComplexShape.up ℤ) n).map u) =
      Cocycle.fromSingleMk (u ≫ f') (add_zero n) (n + 1) rfl (by simp [hf'']) :=
    (Cocycle.fromSingleMk_precomp (g := u) (f := f') (h := add_zero n) (q' := n + 1)
      (hq' := rfl) (hf := hf'')).symm
  have h2 : Cocycle.fromSingleMk (u ≫ f') (add_zero n) (n + 1) rfl (by simp [hf'']) =
      Cocycle.fromSingleMk f (add_zero n) (n + 1) rfl hf := by
    ext : 1
    rw [Cocycle.fromSingleMk_coe, Cocycle.fromSingleMk_coe, hf']
  rw [h1, h2]
  exact hfz

/-- `0`-cocycles `singleC n A ⟶ K` whose images under precomposition with `(singleC n).map u`
agree in cohomology already agree in cohomology. -/
private lemma singleC_precomp_congr (A : C) (u : A ⟶ A) (K : CochainComplex C ℤ) (n : ℤ)
    (h : ∀ q : ℤ, Function.Bijective (fun f : A ⟶ K.X q => u ≫ f))
    (z₁ z₂ : Cocycle ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj A) K 0)
    (hz : CohomologyClass.mk
        (z₁.precomp ((HomologicalComplex.single C (ComplexShape.up ℤ) n).map u)) =
      CohomologyClass.mk
        (z₂.precomp ((HomologicalComplex.single C (ComplexShape.up ℤ) n).map u))) :
    CohomologyClass.mk z₁ = CohomologyClass.mk z₂ := by
  obtain ⟨f₁, hf₁, hfz₁⟩ := Cocycle.fromSingleMk_surjective z₁ n (add_zero n) (n + 1) rfl
  obtain ⟨f₂, hf₂, hfz₂⟩ := Cocycle.fromSingleMk_surjective z₂ n (add_zero n) (n + 1) rfl
  have hpre₁ : z₁.precomp ((HomologicalComplex.single C (ComplexShape.up ℤ) n).map u) =
      Cocycle.fromSingleMk (u ≫ f₁) (add_zero n) (n + 1) rfl (by simp [hf₁]) := by
    rw [← hfz₁]
    exact (Cocycle.fromSingleMk_precomp (g := u) (f := f₁) (h := add_zero n) (q' := n + 1)
      (hq' := rfl) (hf := hf₁)).symm
  have hpre₂ : z₂.precomp ((HomologicalComplex.single C (ComplexShape.up ℤ) n).map u) =
      Cocycle.fromSingleMk (u ≫ f₂) (add_zero n) (n + 1) rfl (by simp [hf₂]) := by
    rw [← hfz₂]
    exact (Cocycle.fromSingleMk_precomp (g := u) (f := f₂) (h := add_zero n) (q' := n + 1)
      (hq' := rfl) (hf := hf₂)).symm
  have hz' : CohomologyClass.mk
        (Cocycle.fromSingleMk (u ≫ f₁) (add_zero n) (n + 1) rfl (by simp [hf₁])) =
      CohomologyClass.mk
        (Cocycle.fromSingleMk (u ≫ f₂) (add_zero n) (n + 1) rfl (by simp [hf₂])) := by
    rw [← hpre₁, ← hpre₂]
    exact hz
  have hmem : Cocycle.fromSingleMk (u ≫ f₁) (add_zero n) (n + 1) rfl (by simp [hf₁]) -
      Cocycle.fromSingleMk (u ≫ f₂) (add_zero n) (n + 1) rfl (by simp [hf₂]) ∈
      coboundaries ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj A) K 0 := by
    rw [← CohomologyClass.mk_eq_zero_iff, CohomologyClass.mk_sub, hz', sub_self]
  rw [← Cocycle.fromSingleMk_sub] at hmem
  obtain ⟨g, hg⟩ := (Cocycle.fromSingleMk_mem_coboundaries_iff (f := u ≫ f₁ - u ≫ f₂)
    (h := add_zero n) (q' := n + 1) (hq' := rfl) (hf := _) (q'' := n - 1)
    (hq'' := by omega)).mp hmem
  obtain ⟨g', hg'⟩ := (h (n - 1)).surjective g
  change u ≫ g' = g at hg'
  have hkey : g' ≫ K.d (n - 1) n = f₁ - f₂ := by
    refine (h n).injective ?_
    rw [← Category.assoc, hg', hg, ← CategoryTheory.Preadditive.comp_sub]
  have hmem₂ : Cocycle.fromSingleMk (f₁ - f₂) (add_zero n) (n + 1) rfl (by simp [hf₁, hf₂]) ∈
      coboundaries ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj A) K 0 :=
    (Cocycle.fromSingleMk_mem_coboundaries_iff (f := f₁ - f₂) (h := add_zero n) (q' := n + 1)
      (hq' := rfl) (hf := by simp [hf₁, hf₂]) (q'' := n - 1) (hq'' := by omega)).mpr ⟨g', hkey⟩
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    ← hfz₁, ← hfz₂, ← Cocycle.fromSingleMk_sub]
  exact hmem₂

/-- Let `C` be a preadditive category with a zero object, `A : C`, `u : A ⟶ A`, `K` a cochain
complex of `C` and `n : ℤ`. If precomposition with `u` is a bijection on `Hom(A, K^q)` for every
`q : ℤ`, then precomposition with `(singleC n).map u` is a bijection on morphisms
`singleC n A ⟶ K` in the homotopy category `K(C)`.

Route: `Hom_K(singleC n A, K) ≅ CohomologyClass (singleC n A) K 0` (up to the canonical
isomorphism `K⟦0⟧ ≅ K`), `toHom (mk (z.precomp g)) = hq.map g ≫ toHom (mk z)`, and the explicit
description `Cocycle.fromSingleMk`, `Cocycle.fromSingleMk_surjective`,
`Cocycle.fromSingleMk_precomp`, `Cocycle.fromSingleMk_mem_coboundaries_iff`: a `0`-cocycle
`singleC n A ⟶ K` is `fromSingleMk f` for `f : A ⟶ K.X n` with `f ≫ K.d n (n+1) = 0`, and
precomposition with `singleC n u` sends it to `fromSingleMk (u ≫ f)`; bijectivity of `f ↦ u ≫ f`
on these cocycles and on the corresponding coboundaries gives bijectivity on the quotient. -/
theorem homKSinglePrecomp {C : Type*} [Category C] [Preadditive C]
    [CategoryTheory.Limits.HasZeroObject C]
    (A : C) (u : A ⟶ A) (K : CochainComplex C ℤ) (n : ℤ)
    (h : ∀ q : ℤ, Function.Bijective (fun f : A ⟶ K.X q => u ≫ f)) :
    Function.Bijective (fun φ : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj A) ⟶
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K =>
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((HomologicalComplex.single C (ComplexShape.up ℤ) n).map u) ≫ φ) := by
  let Q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let S : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) n).obj A
  let F : S ⟶ S := (HomologicalComplex.single C (ComplexShape.up ℤ) n).map u
  have hZ : Function.Bijective (fun ψ : Q.obj S ⟶ Q.obj (K⟦(0 : ℤ)⟧) => Q.map F ≫ ψ) := by
    refine ⟨fun ψ₁ ψ₂ hψ => ?_, fun ψ => ?_⟩
    · change Q.map F ≫ ψ₁ = Q.map F ≫ ψ₂ at hψ
      obtain ⟨x₁, rfl⟩ := (CohomologyClass.toHom_bijective S K 0).surjective ψ₁
      obtain ⟨z₁, rfl⟩ := CohomologyClass.mk_surjective x₁
      obtain ⟨x₂, rfl⟩ := (CohomologyClass.toHom_bijective S K 0).surjective ψ₂
      obtain ⟨z₂, rfl⟩ := CohomologyClass.mk_surjective x₂
      rw [← toHom_mk_precomp S K F z₁, ← toHom_mk_precomp S K F z₂] at hψ
      rw [singleC_precomp_congr A u K n h z₁ z₂
        ((CohomologyClass.toHom_bijective S K 0).injective hψ)]
    · obtain ⟨x, rfl⟩ := (CohomologyClass.toHom_bijective S K 0).surjective ψ
      obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
      obtain ⟨z', hz'⟩ := singleC_precomp_surj A u K n h z
      refine ⟨CohomologyClass.toHom (CohomologyClass.mk z'), ?_⟩
      change Q.map F ≫ CohomologyClass.toHom (CohomologyClass.mk z') =
        CohomologyClass.toHom (CohomologyClass.mk z)
      rw [← toHom_mk_precomp S K F z', hz']
  have hgoal : Function.Bijective (fun φ : Q.obj S ⟶ Q.obj K => Q.map F ≫ φ) := by
    let eη : Q.obj (K⟦(0 : ℤ)⟧) ≅ Q.obj K :=
      Q.mapIso ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).app K)
    refine ⟨fun φ₁ φ₂ hφ => ?_, fun φ => ?_⟩
    · change Q.map F ≫ φ₁ = Q.map F ≫ φ₂ at hφ
      have h1 : Q.map F ≫ (φ₁ ≫ eη.inv) = Q.map F ≫ (φ₂ ≫ eη.inv) :=
        calc Q.map F ≫ (φ₁ ≫ eη.inv) = (Q.map F ≫ φ₁) ≫ eη.inv :=
              (Category.assoc _ _ _).symm
          _ = (Q.map F ≫ φ₂) ≫ eη.inv := by rw [hφ]
          _ = Q.map F ≫ (φ₂ ≫ eη.inv) := Category.assoc _ _ _
      have h2 := hZ.injective h1
      have h3 := congrArg (fun t => t ≫ eη.hom) h2
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h3
    · obtain ⟨ψ, hψ⟩ := hZ.surjective (φ ≫ eη.inv)
      change Q.map F ≫ ψ = φ ≫ eη.inv at hψ
      refine ⟨ψ ≫ eη.hom, ?_⟩
      change Q.map F ≫ (ψ ≫ eη.hom) = φ
      calc Q.map F ≫ (ψ ≫ eη.hom) = (Q.map F ≫ ψ) ≫ eη.hom := (Category.assoc _ _ _).symm
        _ = (φ ≫ eη.inv) ≫ eη.hom := by rw [hψ]
        _ = φ := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact hgoal

end

end Work.ATOM
