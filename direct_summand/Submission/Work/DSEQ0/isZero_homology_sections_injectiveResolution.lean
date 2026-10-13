import Mathlib
import Submission.Work.DSEQ0.AugDefs
import Submission.Work.DSEQ0.atv_machine
import Submission.Work.DSF1.Sheaf.cech_unit_basicOpen_exact

/-!
# Vanishing of the higher homology of the sections complex of an injective resolution

Let `Y` be an affine scheme and `I` an injective resolution of its structure sheaf
`𝒪_Y` (as a sheaf of `𝒪_Y`-modules).  The theorem below states that for `q > 0` the `q`-th
homology of the complex `Γ (Y, ⊤) (I.cocomplex)` of abelian groups vanishes.

This is Serre vanishing for the structure sheaf of an affine scheme, in the form in which it is
needed downstream: the resolution `I` is an *arbitrary* injective resolution, so one cannot quote
a statement about a particular chosen resolution, and one must not use the functor
`Γ (Y, ⊤)` on the whole category of sheaves of modules (it is not exact).  The proof follows the
classical Čech argument (Stacks 30.2.2), formalised in `Submission/Work/DSEQ0/atv_machine.lean`:

* `Work.DSEQ0.CechTrivOnBasic` is the property "the Čech complex of any finite family of basic
  opens `D (f i)` which is contained in and covers a basic open `D g` is acyclic in positive
  degrees".  For the structure sheaf it holds on an affine scheme (Stacks 30.2.1, i.e.
  `Work.DSF1.Sheaf.cech_unit_basicOpen_exact`);
* `Work.DSEQ0.cechTrivOnBasic_syz_and_lift` propagates it to all syzygies of the injective
  resolution `I.cocomplex` — whose terms are injective, hence flasque, hence have acyclic Čech
  complexes — and gives in addition the surjectivity of the projections `syzProj` onto the
  successive syzygies on sections over any basic open;
* `Work.DSEQ0.isZero_homology_mapHomologicalComplex_of_epi_map_syzProj` turns the surjectivity of
  `syzProj I.cocomplex j` over `⊤` (i.e. after applying `Γ (Y, ⊤)`) into the vanishing of the
  `(j+1)`-st homology of the sections complex.

The only adaptations needed to run the argument for `Work.DSEQ0.sectionsV Y ⊤` (rather than for the
`ModuleCat`-valued evaluation functor) are that the target category is `AddCommGrpCat`, where
epimorphisms are exactly the surjective maps (`AddCommGrpCat.epi_iff_surjective`), and that
`Work.DSF1.Sheaf.sectionsAt` / `Work.DSF1.Sheaf.sectionsMap` are *definitionally* the components
of `sectionsV Y ⊤`.

(Development note: the two sorry-free probe modules `_izhr_env.lean` and `_izhr_ax.lean` in this
directory were used to elaborate the statement against the available API and to inspect the
axioms of the theorem below.  Nothing imports them.)
-/

namespace Work.DSEQ0

open CategoryTheory AlgebraicGeometry Opposite Limits

universe u

theorem isZero_homology_sections_injectiveResolution (Y : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsAffine Y]
    (I : CategoryTheory.InjectiveResolution (SheafOfModules.unit Y.ringCatSheaf)) :
    ∀ (q : ℕ), 0 < q → CategoryTheory.Limits.IsZero
      (HomologicalComplex.homology
        (((Work.DSEQ0.sectionsV Y (⊤ : Y.Opens)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex) q) := by
  -- Stacks 30.2.1: the structure sheaf of an affine scheme is Čech-trivial on basic opens
  have hZ : Work.DSEQ0.CechTrivOnBasic Y (SheafOfModules.unit Y.ringCatSheaf) := by
    intro ι _ f g hmem hcov n hn
    exact Work.DSF1.Sheaf.cech_unit_basicOpen_exact Y f g hmem hcov n hn
  -- the `0`-th syzygy of an injective resolution of `𝒪_Y` is `𝒪_Y` itself
  have hbase : Work.DSEQ0.CechTrivOnBasic Y (Work.DSF1.Sheaf.syz I.cocomplex 0) :=
    Work.DSEQ0.CechTrivOnBasic.of_iso
      (Work.DSF1.Sheaf.syz_zero_iso (SheafOfModules.unit Y.ringCatSheaf) I.cocomplex I.ι).some hZ
  -- an injective resolution is exact in positive degrees
  have hex : ∀ n : ℕ, 0 < n → IsZero (I.cocomplex.homology n) := by
    intro n hn
    exact (HomologicalComplex.exactAt_iff_isZero_homology I.cocomplex n).mp
      (Work.DSEQ0.exactAt_of_quasiIso_single' I.ι n hn)
  have hKinj : ∀ n : ℕ, Injective (I.cocomplex.X n) := fun n => I.injective n
  -- the syzygy induction of `atv_machine`
  have hInv := Work.DSEQ0.cechTrivOnBasic_syz_and_lift Y I.cocomplex hex hKinj hbase
  intro q hq
  obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
  -- the sections functor `Γ (Y, ⊤)`, with its type pinned down
  let F : SheafOfModules.{u} Y.ringCatSheaf ⥤ AddCommGrpCat.{u} :=
    Work.DSEQ0.sectionsV Y (⊤ : Y.Opens)
  have hFadd : F.Additive := Work.DSEQ0.sectionsV_additive Y ⊤
  -- it is left exact: it is an evaluation on presheaves composed with forgetful functors
  have hFlim : PreservesFiniteLimits F :=
    Limits.comp_preservesFiniteLimits
      (SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op (⊤ : Y.Opens)))
      (CategoryTheory.forget₂
        (ModuleCat.{u} (Y.ringCatSheaf.obj.obj (Opposite.op (⊤ : Y.Opens))))
        AddCommGrpCat.{u})
  -- the surjectivity of `syzProj I.cocomplex j` over `⊤` given by the induction invariant makes
  -- `F.map (syzProj I.cocomplex j)` an epimorphism
  have hepi : Epi (F.map (Work.DSF1.Sheaf.syzProj I.cocomplex j)) := by
    -- an epimorphism of abelian groups is a surjective map
    rw [AddCommGrpCat.epi_iff_surjective]
    intro y
    have hone : Y.basicOpen (1 : Y.presheaf.obj (Opposite.op (⊤ : Y.Opens))) = ⊤ :=
      Scheme.basicOpen_one (X := Y) (U := ⊤)
    have hsurj := (hInv j).2 1
    have hsurj_top : ∀ y : Work.DSF1.Sheaf.sectionsAt (Work.DSF1.Sheaf.syz I.cocomplex (j + 1))
        (⊤ : Y.Opens),
        ∃ x : Work.DSF1.Sheaf.sectionsAt (I.cocomplex.X j) (⊤ : Y.Opens),
          Work.DSF1.Sheaf.sectionsMap (Work.DSF1.Sheaf.syzProj I.cocomplex j) (⊤ : Y.Opens) x = y :=
      hone ▸ hsurj
    obtain ⟨x, hx⟩ := hsurj_top y
    exact ⟨x, hx⟩
  exact @Work.DSEQ0.isZero_homology_mapHomologicalComplex_of_epi_map_syzProj
    (SheafOfModules.{u} Y.ringCatSheaf) _ _ (AddCommGrpCat.{u}) _ _
    I.cocomplex _ F hFadd hFlim j hepi

end Work.DSEQ0
