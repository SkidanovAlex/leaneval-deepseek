import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Submission.Work.SSGRoute.SSGStage.divRep_detecting_class
import Submission.Work.SSGRoute.Sha2Lib.detectorInterface
import Submission.Work.SSGRoute.Sha2Lib.detector_of_submodule
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

-- The `ℚ/ℤ`-coefficient objects of `Work.SSGRoute.E7cOmega` are `abbrev`s whose projections are
-- only definitionally (not reducibly) equal, so the `rfl`-level unfolding needed when an `Ext`
-- class with `divRep`-coefficients is fed to the long exact sequence of `ratDivSES` has to be
-- allowed at implicit transparency.  (`ratDivSES.lean` and `divRep_detecting_class.lean` set the
-- same option for the same reason.)
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.Sha2Lib

open CategoryTheory

/-- **The connecting map `Hom_D(N, ℚ/ℤ) → Ext¹_D(N, ℤ)` is injective for `N` of exponent `p`.**

If `ν : res_D N ⟶ ℚ/ℤ` is a `D`-morphism whose image under the connecting map of the coefficient
sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` (`Work.SSGRoute.E7cOmega.ratDivSES`) vanishes, then `ν = 0`.

The long exact sequence of `Ext` (`Abelian.Ext.covariant_sequence_exact₃`) identifies the kernel of
`δ` with the image of `Hom_D(N, ℚ)`, and `Hom_D(N, ℚ) = 0` because `N` is killed by `p` while `ℚ`
is torsion-free (`Work.SSGRoute.SSGStage.subsingleton_ext_zero_ratRep`). -/
private lemma mk0_comp_extClass_eq_zero_of_exponent {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    (D : Subgroup G) (N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hN : ∀ m : N, p • m = 0)
    (ν : Rep.res D.subtype N ⟶ Work.SSGRoute.E7cOmega.divRep D)
    (hν : (CategoryTheory.Abelian.Ext.mk₀ ν).comp
        (CategoryTheory.ShortComplex.ShortExact.extClass
          (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := D))) (zero_add 1) = 0) :
    ν = 0 := by
  haveI hsub : Subsingleton (CategoryTheory.Abelian.Ext (Rep.res D.subtype N)
      (Work.SSGRoute.E7cOmega.ratDivSES (G := D)).X₂ 0) :=
    Work.SSGRoute.SSGStage.subsingleton_ext_zero_ratRep (G := D) (p := p)
      (Rep.res D.subtype N) (fun m => hN m)
  obtain ⟨x₂, hx₂⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₃
    (Rep.res D.subtype N) (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := D))
    (CategoryTheory.Abelian.Ext.mk₀ ν) (zero_add 1) hν
  have hx0 : x₂ = 0 := Subsingleton.elim x₂ 0
  have hν0 : CategoryTheory.Abelian.Ext.mk₀ ν = 0 := by
    rw [← hx₂, hx0]
    simp
  rwa [CategoryTheory.Abelian.Ext.mk₀_eq_zero_iff] at hν0

/-- **A nonzero `ℤ`-coefficient `Ext¹` class stays nonzero after pullback along a surjection.**

Let `D ≤ G`, let `M`, `M'` be `p`-torsion `G`-modules (spelled `Rep Coeff G`), and let `c : M' ⟶ M`
be a `G`-module map that is *surjective on underlying sets*.  Then for every nonzero
`φ ∈ Ext¹_D(res_D M, ℤ)` (spelled `Abelian.Ext (Rep.res D.subtype M) (unitRep D) 1`) the pullback
`(mk₀ (resMap D.subtype c)).comp φ : Ext¹_D(res_D M', ℤ)` is nonzero.

This is the step the `C6` route uses to move detection from a cover `Ind_N^Γ(res_N M) ⟶ M` to `M`:
`Sha2Lib.detectsAt_of_coeff_surjection` (proved, on disk) consumes a *surjective* coefficient map
together with a detecting class for the cover, so a nonzero `φ` must survive the pullback for the
cover's detector to apply.  The sibling `Sha2Lib.ext_comp_mk0_ne_zero_of_section` covers only split
epis; the counit `Ind_N^Γ(res_N M) ⟶ M` is not split, so this is a genuine strengthening, and no
other declaration in the tree states it.

Route (both reviewers): by `Work.SSGRoute.SSGStage.divRep_detecting_class` (proved; needs only
`hM`, arbitrary `[Group G]`) obtain `μ : M ⟶ divRep D` with `μ ≠ 0` and
`φ = mk₀ μ ≫ (ratDivSES).extClass`; pullback along `res c` is *literally* `δ(μ ∘ res c)` by
`Ext.mk₀_comp_mk₀_assoc`, and `μ ∘ res c ≠ 0` because `res c` is onto while `μ ≠ 0`; finally `δ` is
injective, which needs only `Hom_D(M', ℚ) = 0`, supplied by `M'`'s exponent-`p` (see
`Work.E7cOmega.ext_one_unitRep_iso_divRep` (proved, degree `0 → 1`) and
`Work.SSGRoute.SSGStage.extRatRep_vanish`; note `E7cOmega.extClass_comp_injective` as on disk is the
degree `1 → 2` statement and does *not* directly supply this injectivity — the needed content is the
`hbij` inside `ext_one_unitRep_iso_divRep`).  The `[Finite M]`, `[Finite M']` hypotheses of the
statement are not needed by this route but are kept because they are exactly the detector's setting.

Formalisation: the injectivity of `δ` is `mk0_comp_extClass_eq_zero_of_exponent` above (the
`0 → 1` part of the long exact sequence plus `Hom_D(M', ℚ) = 0`), and the nonvanishing of
`res_D c ≫ μ` is right-cancellation against the epimorphism `res_D c` (`Rep.epi_iff_surjective`). -/
theorem ext_comp_mk0_ne_zero_of_surjective {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
    (D : Subgroup G) (M M' : Rep.{0} SSGRoute.PTExt.Coeff G) [Finite M] [Finite M']
    (hM : ∀ m : M, p • m = 0) (hM' : ∀ m : M', p • m = 0)
    (c : M' ⟶ M) (hc : Function.Surjective c.hom)
    (φ : CategoryTheory.Abelian.Ext (Rep.res D.subtype M)
      (SSGRoute.PTExt.unitRep D) 1) (hφ : φ ≠ 0) :
    (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap D.subtype c)).comp φ (zero_add 1) ≠ 0 := by
  -- `divRep_detecting_class` over the group `D` exhibits `φ` as `δ μ` with `μ ≠ 0`
  have hMres : ∀ m : Rep.res D.subtype M, p • m = 0 := fun m => hM m
  obtain ⟨μ, hμ, hφμ⟩ := Work.SSGRoute.SSGStage.divRep_detecting_class (G := ↥D) p
    (Rep.res D.subtype M) hMres φ hφ
  -- the pulled-back class is `δ(μ ∘ res c)` by associativity of the Yoneda product
  have key : (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap D.subtype c)).comp φ (zero_add 1)
      = (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap D.subtype c ≫ μ)).comp
          (CategoryTheory.ShortComplex.ShortExact.extClass
            (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := ↥D))) (zero_add 1) := by
    rw [hφμ, CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc]
  rw [key]
  intro hzero
  -- `δ` is injective on coefficients of a `p`-torsion module, so `μ ∘ res c = 0`
  have hν0 : Rep.resMap D.subtype c ≫ μ = 0 :=
    mk0_comp_extClass_eq_zero_of_exponent D M' hM' (Rep.resMap D.subtype c ≫ μ) hzero
  -- and `res c` is an epimorphism, so right cancellation forces `μ = 0`
  haveI : Epi (Rep.resMap D.subtype c) := (Rep.epi_iff_surjective _).2 (by
    intro y
    obtain ⟨x, hx⟩ := hc y
    exact ⟨x, by simpa using hx⟩)
  exact hμ ((cancel_epi (Rep.resMap D.subtype c)).mp (by rw [hν0]; simp))

end Work.Sha2Lib
