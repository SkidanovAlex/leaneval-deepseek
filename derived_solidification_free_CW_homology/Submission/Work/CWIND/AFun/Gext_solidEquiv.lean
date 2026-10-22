import Mathlib
import Submission.Work.CWIND.AFun.Setup

namespace Work.CWIND.AFun

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint
open scoped Simplicial

open Work.CWIND

/-- **CWIND/T4-a.** The comparison map `Gext X : Aconst X ⟶ A X` (the extension of the
simplicial map `const ℤ[X] ⟶ Y X` of constant simplices) is a solid-equivalence.  Proof route:
`ToolkitProp.levelwise` applied to `K := (CochainComplex.singleFunctor LightCondAb 0).obj (freeLightCondAbOfTop X)`,
`L := A X`, `f := Gext X`.  Both complexes vanish in positive degrees (`HomologicalComplex.isZero_extend_X`
for `Aconst X`, `Work.CWIND.isZero_A_X_of_pos` for `A X`, and `HomologicalComplex.isZero_single_obj_X`
for the single complex).  For `q = -(n:ℤ) ≤ 0`, `Work.CWIND.AFun.Gext_f_neg` identifies `(Gext X).f q`
with `(AconstXIso X n).hom ≫ freeLightCondAbOfTopFunctor.map (constMap X n) ≫ (AXIso X n).inv`
(which is `dFree (constMap X n)` up to the two isos, handled by `ToolkitProp.of_iso` and
`ToolkitProp.comp`), and `hconst X n` is exactly the required `SolidEquiv`.  For `q > 0` both
objects are zero, so the degreewise map is an isomorphism between zero objects. -/
theorem Gext_solidEquiv (hTK : Submission.Blueprint.ToolkitProp)
    (hconst : ∀ (X : TopCat.{0}) [T2Space X] (n : ℕ),
      Submission.Blueprint.SolidEquiv (Submission.Blueprint.dFree (Work.CWIND.constMap X n)))
    (X : TopCat.{0}) [T2Space X] :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.Q).map (Work.CWIND.AFun.Gext X)) := by
  -- `Aconst X` vanishes in positive cohomological degrees: it is the extension of a chain
  -- complex in `ℕ`-degrees, and no `n : ℕ` is sent to a positive integer.
  have hKzero : ∀ q : ℤ, 0 < q → IsZero ((Aconst X).X q) := by
    intro q hq
    exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingDownNat q (by
      intro n hn
      simp only [ComplexShape.embeddingDownNat_f] at hn
      omega)
  -- `A X` vanishes in positive cohomological degrees.
  have hLzero : ∀ q : ℤ, 0 < q → IsZero ((A X).X q) := fun q hq => isZero_A_X_of_pos X hq
  refine hTK.levelwise (Aconst X) (A X) (Gext X) hKzero hLzero ?_
  intro q
  by_cases hq : 0 < q
  · -- Positive degrees: the degreewise map is a morphism between zero objects, hence an iso.
    have hEq : (Gext X).f q = (IsZero.iso (hKzero q hq) (hLzero q hq)).hom :=
      IsZero.eq_of_src (hKzero q hq) _ _
    refine hTK.of_iso _ ?_
    rw [hEq]
    exact Functor.map_isIso _ _
  · -- Non-positive degrees: `q = -(n : ℤ)`, and `Gext_f_neg` identifies the degreewise map with
    -- the composite `(AconstXIso X n).hom ≫ dFree (constMap X n) ≫ (AXIso X n).inv` of two
    -- isomorphisms with the image of `dFree (constMap X n)`.
    --
    -- The two composites in `Gext_f_neg` are only well typed up to the definitional
    -- identifications `(AchainConst X).X n = ℤ[X]` and `ℤ[X^{Δⁿ}] = (Achain X).X n`, which are
    -- not transparent to the pattern matching performed by `rw`/`apply`; the transport is
    -- therefore carried out in term mode, with `congrArg`/`Eq.trans`.
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = -(n : ℤ) := by
      refine ⟨(-q).toNat, ?_⟩
      have h1 : ((-q).toNat : ℤ) = -q := Int.toNat_of_nonneg (by omega)
      omega
    have hA : SolidEquiv ((DerivedCategory.singleFunctor LightCondAb 0).map
        (AconstXIso X n).hom) := hTK.of_iso _ (by infer_instance)
    have hb : SolidEquiv ((DerivedCategory.singleFunctor LightCondAb 0).map
        (freeLightCondAbOfTopFunctor.map (constMap X n))) := hconst X n
    have hC : SolidEquiv ((DerivedCategory.singleFunctor LightCondAb 0).map
        (AXIso X n).inv) := hTK.of_iso _ (by infer_instance)
    have hbC : SolidEquiv ((DerivedCategory.singleFunctor LightCondAb 0).map
          (freeLightCondAbOfTopFunctor.map (constMap X n)) ≫
        (DerivedCategory.singleFunctor LightCondAb 0).map (AXIso X n).inv) :=
      hTK.comp _ _ hb hC
    have hall : SolidEquiv ((DerivedCategory.singleFunctor LightCondAb 0).map
          (AconstXIso X n).hom ≫
        ((DerivedCategory.singleFunctor LightCondAb 0).map
            (freeLightCondAbOfTopFunctor.map (constMap X n)) ≫
          (DerivedCategory.singleFunctor LightCondAb 0).map (AXIso X n).inv)) :=
      hTK.comp _ _ hA hbC
    have hkey : (DerivedCategory.singleFunctor LightCondAb 0).map ((Gext X).f (-(n : ℤ))) =
        (DerivedCategory.singleFunctor LightCondAb 0).map (AconstXIso X n).hom ≫
          ((DerivedCategory.singleFunctor LightCondAb 0).map
              (freeLightCondAbOfTopFunctor.map (constMap X n)) ≫
            (DerivedCategory.singleFunctor LightCondAb 0).map (AXIso X n).inv) := by
      have h1 := congrArg (fun m : (Aconst X).X (-(n : ℤ)) ⟶ (A X).X (-(n : ℤ)) =>
        (DerivedCategory.singleFunctor LightCondAb 0).map m) (Gext_f_neg X n)
      have h2 := Functor.map_comp (DerivedCategory.singleFunctor LightCondAb 0)
        (AconstXIso X n).hom (freeLightCondAbOfTopFunctor.map (constMap X n) ≫ (AXIso X n).inv)
      have h3 := Functor.map_comp (DerivedCategory.singleFunctor LightCondAb 0)
        (freeLightCondAbOfTopFunctor.map (constMap X n)) (AXIso X n).inv
      have h4 := congrArg (fun x => (DerivedCategory.singleFunctor LightCondAb 0).map
        (AconstXIso X n).hom ≫ x) h3
      exact (h1.trans h2).trans h4
    exact hkey.symm ▸ hall

end Work.CWIND.AFun
