import Mathlib
import Submission.Work.Cohomology.MVSequence
import Submission.Work.ThomBordism.finiteGoodCoverHomology
import Submission.Work.ThomBordism.moduleFiniteHomologyBiprod

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-!
# Finite generation of homology: homotopy invariance and Mayer–Vietoris

* `moduleFinite_homology_of_homotopyEquiv` — finite generation of `H_n(·;ℤ)` transfers along a
  homotopy equivalence (through the homology isomorphism `Work.Cohomology.homologyEquiv`);
* `moduleFinite_homology_of_mv` — the **Mayer–Vietoris finiteness lemma**: for an open cover
  `X = U ∪ V`, finite generation of `H_*(U)`, `H_*(V)` and `H_*(U ∩ V)` implies it for `H_*(X)`
  (in degrees `n ≥ 1`; the degree-zero case is handled separately where it is used).
-/

open CategoryTheory Limits

namespace Work.ThomBordism.Grassmann.Torsion

noncomputable section

/-! ## Homotopy invariance -/

/-- **Finite generation of homology transfers along a homotopy equivalence.** -/
theorem moduleFinite_homology_of_homotopyEquiv {X Y : TopCat} (f : X ⟶ Y) (g : Y ⟶ X)
    (h₁ : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp f g) (CategoryTheory.CategoryStruct.id X))
    (h₂ : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp g f) (CategoryTheory.CategoryStruct.id Y))
    (n : ℕ) (hfin : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ X).homology n)) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ Y).homology n) := by
  let φ : (Work.Cohomology.singularChains ℤ X).homology n ⟶
      (Work.Cohomology.singularChains ℤ Y).homology n :=
    HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) n
  haveI hφ : IsIso φ := Work.Cohomology.homologyEquiv ℤ X Y f g h₁ h₂ n
  exact Module.Finite.of_surjective φ.hom ((ModuleCat.epi_iff_surjective φ).mp inferInstance)

/-! ## The Noetherian middle-term argument -/

/-- The middle term of an exact sequence of `ℤ`-modules with finitely generated outer terms is
finitely generated. -/
theorem moduleFinite_of_exact_pair {A B C : Type*} [AddCommGroup A] [Module ℤ A] [AddCommGroup B]
    [Module ℤ B] [AddCommGroup C] [Module ℤ C] (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C)
    (hex : f.range = g.ker) (hA : Module.Finite ℤ A) (hC : Module.Finite ℤ C) :
    Module.Finite ℤ B := by
  haveI : IsNoetherian ℤ A := isNoetherian_of_isNoetherianRing_of_finite ℤ A
  haveI : IsNoetherian ℤ C := isNoetherian_of_isNoetherianRing_of_finite ℤ C
  haveI : IsNoetherian ℤ B := isNoetherian_of_range_eq_ker f g hex
  exact inferInstance

/-! ## The Mayer–Vietoris finiteness lemma -/

/-- **Mayer–Vietoris finiteness lemma** (`n ≥ 1`): if `X = U ∪ V` with `U`, `V` open and the
homology of `U`, `V` and `U ∩ V` is finitely generated in every degree, then the homology of `X` is
finitely generated in degree `n ≥ 1`. -/
theorem moduleFinite_homology_of_mv {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ)
    (hUi : ∀ n, Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of U)).homology n))
    (hVi : ∀ n, Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of V)).homology n))
    (hUVi : ∀ n, Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of (Set.inter U V))).homology n))
    {n : ℕ} (hn : 1 ≤ n) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ X).homology n) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  -- it suffices to prove finite generation of the small chains in degree `n' + 1`
  suffices hsmall : Module.Finite ℤ (Work.Cohomology.HSmall U V (n' + 1)) by
    exact Work.ThomBordism.fgch_moduleFinite_of_iso
      (Work.Cohomology.smallIso U V hU hV hcov (n' + 1)) hsmall
  -- the exact piece of the Mayer–Vietoris sequence
  have hex := Work.Cohomology.mv_H_exact₃ U V n'
  have hker := CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hex
  haveI hA : Module.Finite ℤ
      ↑(HomologicalComplex.homology
        (Work.Cohomology.singularChains ℤ (TopCat.of U) ⊞
          Work.Cohomology.singularChains ℤ (TopCat.of V)) (n' + 1)) :=
    Work.ThomBordism.moduleFiniteHomologyBiprod (n' + 1) (hUi (n' + 1)) (hVi (n' + 1))
  haveI hC : Module.Finite ℤ ↑(Work.Cohomology.HInter U V n') := hUVi n'
  exact moduleFinite_of_exact_pair (HomologicalComplex.homologyMap (Work.Cohomology.mvRight U V) (n'+1)).hom
    (Work.Cohomology.mvδ U V n').hom hker hA hC

end

end Work.ThomBordism.Grassmann.Torsion
