import Mathlib
import Submission.Work.DSF1.Sheaf.exists_cechSheafPresheaf
import Submission.Work.DSF1.Cech.cechAffineCover_quasiIso
import Submission.Work.DSF1.Modules.pushforward_unit_sections
import Submission.Work.DSF1.Sheaf.sectionsV_kernel_iso
import Submission.Work.DSF1.Sheaf.cechTrivAt_sectionsV

/-!
# Vanishing of the positive-degree homology of the sheaf-level Čech complex

Let `X` be a scheme, `U : ι → X.Opens` a family of opens covering `X`, and let

`P := Work.DSF1.Sheaf.cechSheafPresheaf X : (X.Opens)ᵒᵖ ⥤ X.Modules`

be the Čech presheaf of the structure sheaf (`P(W) = (W.ι)_* 𝒪_W`).  This file proves that the
homology of the sheaf-level Čech complex `K = (cechComplexFunctor U).obj P` vanishes in positive
degrees (as an object of the category `X.Modules` of sheaves of `𝒪_X`-modules):

`IsZero (K.homology n)` for `0 < n`.

## The mathematics

The terms of `K` are products of pushforwards of the structure sheaf along the open immersions of
the opens of the Čech nerve, so the sections of `Kⁿ` over an open `V` are the usual Čech
`n`-cochains of the family `U ⊓ V` of `V`:

`Γ(Kⁿ, V) = ∏_{x : Fin (n+1) → ι} Γ(U(x 0) ⊓ ⋯ ⊓ U(x n) ⊓ V, 𝒪_X)`,

and the differential is the alternating sum of the restriction maps.  Hence
`Γ(K•, V) = Č(U ⊓ V; 𝒪_X)` is the presheaf-level Čech complex of the restricted cover of `V` --
this is the comparison provided by `Work.DSEQ0.cechSh_sectionsV_iso` and the functor
`Work.DSEQ0.sectionsV X V` of sections over `V`.

The proof of the vanishing is local.  Since `U` covers `X`, every open `V` is covered by the
opens `V ⊓ U j`.  For `j : ι` the family `U ⊓ (V ⊓ U j)` of opens of `V ⊓ U j` contains the
member `V ⊓ U j` itself, and then the Čech complex of `U` with coefficients
`W ↦ Γ(W ⊓ (V ⊓ U j), 𝒪_X)` is contractible: inserting the index `j` at position `0` of a
simplex does not change the open of the nerve, so the corresponding coface is an isomorphism of
coefficient modules.  Consequently every Čech cocycle over `V ⊓ U j` is a coboundary over
`V ⊓ U j` (`Work.DSEQ0.cechTrivAll_sectionsV`, transported to the sections of `K` in
`Work.DSF1.Sheaf.cechTrivAt_sectionsV`).

Finally, exactness of `K` in degree `n = m + 1` is the statement that the canonical morphism
`Kᵐ ⟶ ker (K^{m+1} → K^{m+2})` is an epimorphism; epimorphisms of sheaves of `𝒪_X`-modules are
detected by local surjectivity on sections (`Work.DSF1.Sheaf.modEpi_of_local_lift`), and the local
surjectivity is precisely the local triviality of `(m+1)`-cocycles supplied by the contractibility
argument.  (The identification of the sections of `ker (K^{m+1} → K^{m+2})` with the sections of
`K^{m+1}` killed by the differential is `Work.DSF1.Sheaf.sectionsV_kernel_iso`.)

The hypotheses `hU` (the members of the cover are affine) and `haff` (intersections of affine
opens are affine) are not used: the argument is local on the topology of `X` and only needs the
covering hypothesis `hcov`.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

set_option linter.unusedVariables false

/-! ## Local criteria for morphisms of sheaves of `𝒪_X`-modules

The three lemmas below are the (elementary) sheaf-theoretic input of the final step: naturality of
the action on sections, separation, and "locally surjective on sections ⟹ epi".  They are
reproduced here (in the same form as in `Submission/Work/DSEQ0/AugMain.lean`) so that this file
does not depend on that module. -/

/-- The sections of a morphism of sheaves of `𝒪_X`-modules are natural with respect to
restriction. -/
lemma modApp_naturality {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    {V V' : X.Opens} (h : V' ≤ V) (s : (Scheme.Modules.presheaf M).obj (Opposite.op V)) :
    (Scheme.Modules.Hom.app φ V') ((Scheme.Modules.presheaf M).map (homOfLE h).op s)
      = (Scheme.Modules.presheaf N).map (homOfLE h).op
          ((Scheme.Modules.Hom.app φ V) s) := by
  have hnat := (Scheme.Modules.Hom.mapPresheaf φ).naturality (homOfLE h).op
  have h2 := congrArg
    (fun (g : (Scheme.Modules.presheaf M).obj (Opposite.op V) ⟶
        (Scheme.Modules.presheaf N).obj (Opposite.op V')) => (ConcreteCategory.hom g) s) hnat
  simpa only [AddCommGrpCat.comp_apply, Scheme.Modules.mapPresheaf_app] using h2

/-- **Separation for sheaves of `𝒪_X`-modules.**  Two sections of a sheaf of modules which agree
on a family of opens covering `V` agree. -/
lemma modSections_sep {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} {ι' : Type u}
    (W : ι' → X.Opens) {V : X.Opens} (hW : ∀ i, W i ≤ V) (hcov : V ≤ iSup W)
    {s t : (Scheme.Modules.presheaf M).obj (Opposite.op V)}
    (h : ∀ i, (Scheme.Modules.presheaf M).map (homOfLE (hW i)).op s
      = (Scheme.Modules.presheaf M).map (homOfLE (hW i)).op t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq'
    (⟨Scheme.Modules.presheaf M, Scheme.Modules.isSheaf M⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
    W V (fun i => homOfLE (hW i)) hcov s t h

/-- **Local surjectivity implies epimorphy.**  If a morphism `φ : A ⟶ B` of sheaves of
`𝒪_X`-modules has the property that every section of `B` over an open `V` is, locally on a
cover of `V` by opens `W j`, the image of a section of `A`, then `φ` is an epimorphism. -/
theorem modEpi_of_local_lift {X : AlgebraicGeometry.Scheme.{u}} {A B : X.Modules} (φ : A ⟶ B)
    (h : ∀ (V : X.Opens) (b : (Scheme.Modules.presheaf B).obj (Opposite.op V)),
      ∃ (ι' : Type u) (W : ι' → X.Opens) (hW : ∀ j, W j ≤ V) (hcov : V ≤ iSup W),
        ∀ j, ∃ a : (Scheme.Modules.presheaf A).obj (Opposite.op (W j)),
          (Scheme.Modules.Hom.app φ (W j)) a
            = (Scheme.Modules.presheaf B).map (homOfLE (hW j)).op b) :
    Epi φ := by
  refine ⟨fun {T} p q hpq => ?_⟩
  refine Scheme.Modules.hom_ext p q (fun V => ?_)
  ext b
  obtain ⟨ι', W, hW, hcov, hlift⟩ := h V b
  refine modSections_sep W hW hcov (fun j => ?_)
  obtain ⟨a, ha⟩ := hlift j
  rw [← modApp_naturality p (hW j) b, ← modApp_naturality q (hW j) b, ← ha]
  have h1 : (ConcreteCategory.hom (Scheme.Modules.Hom.app (φ ≫ p) (W j))) a
      = (ConcreteCategory.hom (Scheme.Modules.Hom.app p (W j)))
          ((ConcreteCategory.hom (Scheme.Modules.Hom.app φ (W j))) a) := by
    rw [Scheme.Modules.Hom.comp_app (U := W j) φ p, AddCommGrpCat.comp_apply]
  have h2 : (ConcreteCategory.hom (Scheme.Modules.Hom.app (φ ≫ q) (W j))) a
      = (ConcreteCategory.hom (Scheme.Modules.Hom.app q (W j)))
          ((ConcreteCategory.hom (Scheme.Modules.Hom.app φ (W j))) a) := by
    rw [Scheme.Modules.Hom.comp_app (U := W j) φ q, AddCommGrpCat.comp_apply]
  have h3 : (ConcreteCategory.hom (Scheme.Modules.Hom.app (φ ≫ p) (W j))) a
      = (ConcreteCategory.hom (Scheme.Modules.Hom.app (φ ≫ q) (W j))) a := by
    rw [hpq]
  exact h1.symm.trans (h3.trans h2)

/-- The kernel inclusion `kernel.ι f` is a monomorphism (directly from the universal property of
the kernel). -/
lemma mono_kernel_ι {C : Type*} [Category* C] [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y)
    [HasKernel f] : Mono (kernel.ι f) where
  right_cancellation {Z} g h eq := by
    apply Fork.IsLimit.hom_ext (kernelIsKernel f)
    simpa using eq

/-! ## The vanishing theorem -/

/-- **General form of the vanishing.**  For any family `U` of opens of a scheme `X` covering `X`,
the homology of the sheaf-level Čech complex of the Čech presheaf of the structure sheaf vanishes
in positive degrees.  Only the covering hypothesis is used: the proof is local on the topology of
`X` and does not need any affineness. -/
theorem cechSheafPresheaf_homology_vanishing_of_iSup (X : AlgebraicGeometry.Scheme.{u})
    {ι : Type u} (U : ι → X.Opens) (hcov : iSup U = ⊤) (n : ℕ) (hn : 0 < n) :
    CategoryTheory.Limits.IsZero
      (HomologicalComplex.homology
        ((CategoryTheory.cechComplexFunctor U).obj (Work.DSF1.Sheaf.cechSheafPresheaf X)) n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  let K : CochainComplex X.Modules ℕ := (cechComplexFunctor U).obj (cechSheafPresheaf X)
  -- Every `(m+1)`-cocycle of the section complex over an open contained in a member of `U`
  -- is a coboundary.
  have hloc : ∀ (W : X.Opens) (i₀ : ι), W ≤ U i₀ →
      ∀ x : (Work.DSEQ0.sectionsV X W).obj (K.X (m+1)),
        (Work.DSEQ0.sectionsV X W).map (K.d (m+1) (m+2)) x = 0 →
        ∃ a : (Work.DSEQ0.sectionsV X W).obj (K.X m),
          (Work.DSEQ0.sectionsV X W).map (K.d m (m+1)) a = x :=
    fun W i₀ hW x hx => cechTrivAt_sectionsV X U W i₀ hW m x hx
  -- Exactness of `K` in degree `m+1`: the canonical map to the cycles is an epimorphism.
  have hEpi : Epi (kernel.lift (K.d (m+1) (m+2)) (K.d m (m+1))
      (K.d_comp_d m (m+1) (m+2))) := by
    apply modEpi_of_local_lift
    intro V b
    refine ⟨ι, fun j => V ⊓ U j, fun j => inf_le_left, ?_, ?_⟩
    · rw [← inf_iSup_eq V U, hcov, inf_top_eq]
    · intro j
      -- the pieces of the computation at the open `V ⊓ U j`
      obtain ⟨e, he⟩ := sectionsV_kernel_iso (X := X) (V := V ⊓ U j) (K.d (m+1) (m+2))
      set bj : (Work.DSEQ0.sectionsV X (V ⊓ U j)).obj (kernel (K.d (m+1) (m+2))) :=
        (Scheme.Modules.presheaf (kernel (K.d (m+1) (m+2)))).map
          (homOfLE (inf_le_left : V ⊓ U j ≤ V)).op b with hbj
      set y : (Work.DSEQ0.sectionsV X (V ⊓ U j)).obj (K.X (m+1)) :=
        (kernel.ι ((Work.DSEQ0.sectionsV X (V ⊓ U j)).map (K.d (m+1) (m+2)))) (e.hom bj)
        with hy
      have hcond : kernel.ι ((Work.DSEQ0.sectionsV X (V ⊓ U j)).map (K.d (m+1) (m+2))) ≫
          (Work.DSEQ0.sectionsV X (V ⊓ U j)).map (K.d (m+1) (m+2)) = 0 :=
        kernel.condition _
      have hy0 : (Work.DSEQ0.sectionsV X (V ⊓ U j)).map (K.d (m+1) (m+2)) y = 0 := by
        rw [hy, ← AddCommGrpCat.comp_apply, hcond, AddCommGrpCat.zero_apply]
      -- the local triviality of the cocycle `y`
      obtain ⟨a, ha⟩ := hloc (V ⊓ U j) j inf_le_right y hy0
      refine ⟨a, ?_⟩
      -- `y` is the image of `bj` under the section map of the kernel inclusion
      have hy' : y = ((Work.DSEQ0.sectionsV X (V ⊓ U j)).map
          (kernel.ι (K.d (m+1) (m+2)))) bj := by
        rw [hy, ← AddCommGrpCat.comp_apply, he]
      -- the two composites with the kernel inclusion agree
      have hA : (ConcreteCategory.hom
            (kernel.ι ((Work.DSEQ0.sectionsV X (V ⊓ U j)).map (K.d (m+1) (m+2)))))
            ((ConcreteCategory.hom e.hom)
              ((ConcreteCategory.hom ((Work.DSEQ0.sectionsV X (V ⊓ U j)).map
                (kernel.lift (K.d (m+1) (m+2)) (K.d m (m+1))
                  (K.d_comp_d m (m+1) (m+2))))) a))
          = y := by
        rw [← AddCommGrpCat.comp_apply, he, ← AddCommGrpCat.comp_apply, ← Functor.map_comp,
          kernel.lift_ι]
        exact ha
      have hB : (ConcreteCategory.hom
            (kernel.ι ((Work.DSEQ0.sectionsV X (V ⊓ U j)).map (K.d (m+1) (m+2)))))
            ((ConcreteCategory.hom e.hom) bj) = y := by
        rw [hy', ← AddCommGrpCat.comp_apply, he]
      have h1 : (ConcreteCategory.hom e.hom)
            ((ConcreteCategory.hom ((Work.DSEQ0.sectionsV X (V ⊓ U j)).map
              (kernel.lift (K.d (m+1) (m+2)) (K.d m (m+1))
                (K.d_comp_d m (m+1) (m+2))))) a)
          = (ConcreteCategory.hom e.hom) bj :=
        (AddCommGrpCat.mono_iff_injective _).mp
          (mono_kernel_ι (((Work.DSEQ0.sectionsV X (V ⊓ U j)).map (K.d (m+1) (m+2)))))
          (hA.trans hB.symm)
      exact (AddCommGrpCat.mono_iff_injective e.hom).mp inferInstance h1
  have hexact : K.ExactAt (m+1) := by
    rw [HomologicalComplex.exactAt_iff' K m (m+1) (m+2)
      ((ComplexShape.up ℕ).prev_eq' (ComplexShape.up_mk m (m+1) (by ring)))
      ((ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk (m+1) (m+2) (by ring)))]
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    exact hEpi
  exact (HomologicalComplex.exactAt_iff_isZero_homology K (m+1)).mp hexact

theorem cechSheafPresheaf_homology_vanishing (X : AlgebraicGeometry.Scheme.{u}) {ι : Type u}
    (U : ι → X.Opens) (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i))
    (haff : ∀ V W : X.Opens, AlgebraicGeometry.IsAffineOpen V →
      AlgebraicGeometry.IsAffineOpen W → AlgebraicGeometry.IsAffineOpen (V ⊓ W))
    (hcov : sSup (Set.range U) = ⊤) (n : ℕ) (hn : 0 < n) :
    CategoryTheory.Limits.IsZero
      (HomologicalComplex.homology
        ((CategoryTheory.cechComplexFunctor U).obj (Work.DSF1.Sheaf.cechSheafPresheaf X)) n) :=
  cechSheafPresheaf_homology_vanishing_of_iSup X U (by rw [← sSup_range]; exact hcov) n hn

end Work.DSF1.Sheaf
