import Mathlib
import Submission.Work.DSF1.Sheaf.AcyclicToolkit
import Submission.Work.DSG1.plusSingleTriangle_distinguished
import Submission.Work.DSF1.Sheaf.syzSES_shortExact
import Submission.Work.DSF1.Sheaf.syz_zero_iso
import Submission.Work.DSF1.Sheaf.epi_map_syzProj
import Submission.Work.DSF1.Sheaf.exists_natIso_homology_zero_plus_single
import Submission.Work.DSF1.Sheaf.rightDerived_iso_plusHomology
import Submission.Work.DSF1.Sheaf.plus_homologyTriangle_iso
import Submission.Work.DSF1.Sheaf.plus_homologyTriangle_isZero_iff_epi
import Submission.Work.DSF1.Sheaf.isZero_homology_plus_single_of_acyclic

/-!
# The acyclic resolution criterion for right derived functors

`Work.DSF1.Sheaf.rightDerived_isZero_of_acyclic_resolution` (obligation (H2)/(O4) of `DSF1`,
see `DSF1/DESIGN.md`): if `F : C ⥤ D` is additive and left exact, `C` has enough injectives,
`K` is an `ℕ`-indexed cochain complex of `F`-acyclic objects which is a resolution of `M`
(a quasi-isomorphism `M[0] ⟶ K`), and the `F`-image of `K` is exact in positive degrees, then
`R^n F (M) = 0` for all `n > 0`.

The proof is the classical dimension-shifting argument carried out in the bounded below derived
category `D⁺(C)`.  Write `Z^n = ker (K.d n (n+1))` (`Work.DSF1.Sheaf.syz`); the cochain complex
`K` being exact in positive degrees, there are short exact sequences
`0 → Z^n → K.X n ⟶ Z^{n+1} → 0`.  Each `K.X n` is `F`-acyclic, so the unit
`Q (F (K.X n)) ⟶ RF (Q (K.X n))` is an isomorphism; consequently the long exact sequence attached
to the distinguished triangle of the above short exact sequence (in `D⁺(C)`, transported by the
exact functor `RF` to `D⁺(D)`) gives, for `j ≥ 1`,
`H^j (RF (Σ Z^{n+1})) ≅ H^{j+1} (RF (Σ Z^n))`, while `H^1 (RF (Σ Z^n))` is the cokernel of
`F (K.X n) → F (Z^{n+1})`.  The natural isomorphism `H^0 (RF (Σ (-))) ≅ F (-)` identifies this
cokernel with `H^{n+1} (F K)`, which vanishes by hypothesis.  Hence
`H^N (RF (Σ Z^0)) = 0` for `N > 0`, and `M ≅ Z^0` together with the bridge
`R^N F (M) ≅ H^N (RF (Σ M))` concludes.

The individual ingredients are proved in the sibling files listed in the imports:
`rightDerived_iso_plusHomology` (the bridge), `plus_homologyTriangle_iso` and
`plus_homologyTriangle_isZero_iff_epi` (the long exact sequence of a distinguished triangle),
`isZero_homology_plus_single_of_acyclic` (acyclicity), `exists_natIso_homology_zero_plus_single`
(the degree-zero comparison), `syzSES_shortExact`, `syz_zero_iso`, `epi_map_syzProj` (the syzygy
short exact sequences and the epimorphy of their projections) and `AcyclicToolkit` (vocabulary).
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Work.DSF1.Sheaf

universe u v w x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.style.haveILetI false in
set_option maxHeartbeats 1600000 in
theorem rightDerived_isZero_of_acyclic_resolution {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] [CategoryTheory.EnoughInjectives C]
    {D : Type w} [CategoryTheory.Category.{x} D] [CategoryTheory.Abelian D]
    (F : CategoryTheory.Functor C D) [F.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F] (M : C) (K : CochainComplex C ℕ)
    [∀ i : ℕ, HomologicalComplex.HasHomology K i]
    (i : (CochainComplex.single₀ C).obj M ⟶ K) [QuasiIso i]
    (hK : ∀ n k : ℕ, 0 < k → CategoryTheory.Limits.IsZero ((F.rightDerived k).obj (K.X n)))
    (hKH : ∀ k : ℕ, 0 < k → CategoryTheory.Limits.IsZero
      (HomologicalComplex.homology ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) k)) :
    ∀ n : ℕ, 0 < n → CategoryTheory.Limits.IsZero ((F.rightDerived n).obj M) := by
  haveI : HasDerivedCategory C := HasDerivedCategory.standard C
  haveI : HasDerivedCategory D := HasDerivedCategory.standard D
  -- `K` is exact in positive degrees, because it is quasi-isomorphic to the one-term complex `M[0]`
  have hKex : ∀ j : ℕ, 0 < j → IsZero (K.homology j) := by
    intro j hj
    haveI : QuasiIsoAt i j := (quasiIso_iff i).mp inferInstance j
    haveI : IsIso (HomologicalComplex.homologyMap i j) :=
      (quasiIsoAt_iff_isIso_homologyMap i j).mp inferInstance
    exact IsZero.of_iso
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℕ) 0 M j (by omega))
      (asIso (HomologicalComplex.homologyMap i j)).symm
  -- the natural isomorphism `H^0 (RF (Σ (-))) ≅ F (-)`
  obtain ⟨e⟩ := exists_natIso_homology_zero_plus_single F
  -- the objects `K.X n` are `F`-acyclic
  have hac : ∀ (n : ℕ) (j : ℤ), j ≠ 0 →
      IsZero ((DerivedCategory.Plus.homologyFunctor D j).obj
        (F.rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor C 0).obj (K.X n)))) :=
    fun n j hj => isZero_homology_plus_single_of_acyclic F (K.X n) (fun k hk => hK n k hk) j hj
  -- the projections onto the next syzygy become epimorphisms after applying `F`
  have hepi : ∀ n : ℕ, Epi (F.map (syzProj K n)) :=
    fun n => epi_map_syzProj K F n (hKH (n+1) (by omega))
  -- the base case: `H^1 (RF (Σ Z^n)) = 0` for every `n`
  have base : ∀ n : ℕ, IsZero ((DerivedCategory.Plus.homologyFunctor D (1:ℤ)).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj (syz K n)))) := by
    intro n
    obtain ⟨δ, hδ⟩ := Work.DSG1.plusSingleTriangle_distinguished
      (syzSES_shortExact K n (hKex (n+1) (by omega)))
    let T : Triangle (DerivedCategory.Plus C) :=
      Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0).map (syzSES K n).f)
        ((DerivedCategory.Plus.singleFunctor C 0).map (syzSES K n).g) δ
    have hδ' : T ∈ distTriang _ := hδ
    let T' : Triangle (DerivedCategory.Plus D) := F.rightDerivedFunctorPlus.mapTriangle.obj T
    have hT' : T' ∈ distTriang _ := F.rightDerivedFunctorPlus.map_distinguished T hδ'
    have hobj₁ : T'.obj₁ = F.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor C 0).obj (syz K n)) := rfl
    have hobj₂ : T'.obj₂ = F.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor C 0).obj (K.X n)) := rfl
    have hmor₂ : T'.mor₂ = F.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor C 0).map (syzProj K n)) := rfl
    have h2 : IsZero ((DerivedCategory.Plus.homologyFunctor D ((0:ℤ)+1)).obj T'.obj₂) := by
      rw [hobj₂]; exact hac n 1 (by norm_num)
    have hiff := plus_homologyTriangle_isZero_iff_epi hT' (0:ℤ) h2
    have key : IsZero ((DerivedCategory.Plus.homologyFunctor D ((0:ℤ)+1)).obj T'.obj₁) := by
      rw [hiff]
      rw [show T'.mor₂ = F.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor C 0).map (syzProj K n)) from hmor₂]
      -- the map is the conjugate of `F (Z^n → K.X n ⟶ Z^{n+1})` by the isomorphism `e`
      have hnat := e.hom.naturality (syzProj K n)
      have hstep : (DerivedCategory.Plus.homologyFunctor D 0).map
            (F.rightDerivedFunctorPlus.map
              ((DerivedCategory.Plus.singleFunctor C 0).map (syzProj K n)))
          = e.hom.app (K.X n) ≫ F.map (syzProj K n) ≫ inv (e.hom.app (syz K (n+1))) := by
        have h2' : (DerivedCategory.Plus.homologyFunctor D 0).map
              (F.rightDerivedFunctorPlus.map
                ((DerivedCategory.Plus.singleFunctor C 0).map (syzProj K n))) ≫
              e.hom.app (syz K (n+1)) =
            e.hom.app (K.X n) ≫ F.map (syzProj K n) := hnat
        calc (DerivedCategory.Plus.homologyFunctor D 0).map
              (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map (syzProj K n)))
            = ((DerivedCategory.Plus.homologyFunctor D 0).map
                (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map (syzProj K n)))
                ≫ e.hom.app (syz K (n+1))) ≫ inv (e.hom.app (syz K (n+1))) := by
                  rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
          _ = (e.hom.app (K.X n) ≫ F.map (syzProj K n)) ≫ inv (e.hom.app (syz K (n+1))) := by
                  rw [← h2']
          _ = e.hom.app (K.X n) ≫ F.map (syzProj K n) ≫ inv (e.hom.app (syz K (n+1))) := by
                  rw [Category.assoc]
      rw [hstep]
      have hEp : Epi (e.hom.app (K.X n) ≫ F.map (syzProj K n)) :=
        (epi_comp_iff_of_epi (e.hom.app (K.X n)) (F.map (syzProj K n))).mpr (hepi n)
      have hEp' := (epi_comp_iff_of_isIso (e.hom.app (K.X n) ≫ F.map (syzProj K n))
        (inv (e.hom.app (syz K (n+1))))).mpr hEp
      rw [Category.assoc] at hEp'
      exact hEp'
    rw [hobj₁] at key
    simpa using key
  -- the dimension shifting: `H^{N+1} (RF (Σ Z^n)) ≅ H^N (RF (Σ Z^{n+1}))` for `N ≥ 1`
  have ind : ∀ N : ℕ, 0 < N → ∀ n : ℕ,
      IsZero ((DerivedCategory.Plus.homologyFunctor D (N:ℤ)).obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj (syz K n)))) := by
    intro N
    induction N with
    | zero => intro h; exact absurd h (by omega)
    | succ N ih =>
      intro _ n
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN
        simpa using base n
      · obtain ⟨δ, hδ⟩ := Work.DSG1.plusSingleTriangle_distinguished
          (syzSES_shortExact K n (hKex (n+1) (by omega)))
        let T : Triangle (DerivedCategory.Plus C) :=
          Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0).map (syzSES K n).f)
            ((DerivedCategory.Plus.singleFunctor C 0).map (syzSES K n).g) δ
        let T' : Triangle (DerivedCategory.Plus D) := F.rightDerivedFunctorPlus.mapTriangle.obj T
        have hT' : T' ∈ distTriang _ := F.rightDerivedFunctorPlus.map_distinguished T hδ
        have hobj₁ : T'.obj₁ = F.rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor C 0).obj (syz K n)) := rfl
        have hobj₃ : T'.obj₃ = F.rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor C 0).obj (syz K (n+1))) := rfl
        have h1 : IsZero ((DerivedCategory.Plus.homologyFunctor D (N:ℤ)).obj T'.obj₂) := by
          have ho : T'.obj₂ = F.rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor C 0).obj (K.X n)) := rfl
          rw [ho]; exact hac n N (by omega)
        have h2 : IsZero ((DerivedCategory.Plus.homologyFunctor D ((N:ℤ)+1)).obj T'.obj₂) := by
          have ho : T'.obj₂ = F.rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor C 0).obj (K.X n)) := rfl
          rw [ho]; exact hac n (N+1) (by omega)
        obtain ⟨eiso⟩ := plus_homologyTriangle_iso hT' (N:ℤ) h1 h2
        have key : IsZero ((DerivedCategory.Plus.homologyFunctor D ((N:ℤ)+1)).obj T'.obj₁) := by
          rw [hobj₃] at eiso
          exact IsZero.of_iso (ih hN (n+1)) eiso.symm
        rw [hobj₁] at key
        simpa using key
  -- conclusion
  intro N hN
  obtain ⟨φ⟩ := syz_zero_iso M K i
  have h1 : IsZero ((DerivedCategory.Plus.homologyFunctor D (N:ℤ)).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj (syz K 0)))) :=
    ind N hN 0
  have h2 : IsZero ((DerivedCategory.Plus.homologyFunctor D (N:ℤ)).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj M))) :=
    IsZero.of_iso h1 ((DerivedCategory.Plus.homologyFunctor D (N:ℤ)).mapIso
      (F.rightDerivedFunctorPlus.mapIso ((DerivedCategory.Plus.singleFunctor C 0).mapIso φ)))
  obtain ⟨br⟩ := rightDerived_iso_plusHomology F M N
  exact IsZero.of_iso h2 br

end Work.DSF1.Sheaf
