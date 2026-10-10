import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.E7cOmega.subsingleton_ext_one_ratRep
import Submission.Work.Ext.extClass_postcomp_bijective_Rep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local Tate duality, surjectivity form: a non-zero `Ext¹` class comes from a non-zero functional

This is the "functional" half of node `C6` (`E7cΩ`).  For a group `G`, a prime `p` and a
`G`-module `M` killed by `p`, consider the coefficient short exact sequence
`0 → ℤ → ℚ → ℚ/ℤ → 0` of trivial representations (`Work.SSGRoute.E7cOmega.ratDivSES`) and its
connecting map

  `δ : Ext⁰_G(M, ℚ/ℤ) = Hom_G(M, ℚ/ℤ)  ⟶  Ext¹_G(M, ℤ)`,
  `δ μ = (mk₀ μ).comp (ratDivSES G).extClass`.

Because `ℚ` is divisible while `M` is torsion, both middle `Ext`-groups vanish,
`Hom_G(M, ℚ) = 0` (`Work.SSGRoute.SSGStage.subsingleton_ext_zero_ratRep`) and
`Ext¹_G(M, ℚ) = 0` (`Work.E7cOmega.subsingleton_ext_one_ratRep`, via the dictionary
`Ext¹_G(M,ℚ) ≅ H¹(G, Hom_ℤ(M,ℚ))` of `Work.SSGRoute.ext_one_iso_divisible_cohomology` and
`Hom_ℤ(M,ℚ) = 0`).  By the long exact sequence of `ratDivSES`, the connecting map is then
bijective (`Work.Ext.extClass_postcomp_bijective_Rep`):

  `Hom_G(M, ℚ/ℤ) ≅ Ext¹_G(M, ℤ)`.

In particular every non-zero class `φ ∈ Ext¹_G(M, ℤ)` is `δ(μ)` for a *non-zero* functional
`μ : M ⟶ ℚ/ℤ`:

  `∃ μ ≠ 0, φ = (mk₀ μ).comp extClass (zero_add 1)`.

The final observation `functional_of_ext_nonzero` specialises this to the local level
`G = D_w` (the decomposition group of a place `w` of `K`) with `M` restricted along
`D_w ↪ Gal(K/k)`, which is the shape in which the local half of the paper's duality is consumed.
-/

open CategoryTheory

namespace Work.E7cOmega

noncomputable section

variable {G : Type} [Group G]

/-- **Local Tate duality, surjectivity form.**  For a group `G`, a prime `p` and a `G`-module `M`
killed by `p`, every non-zero class `φ ∈ Ext¹_G(M, ℤ)` is the image of a non-zero coefficient map
`μ : M ⟶ ℚ/ℤ` under the connecting map `δ μ = (mk₀ μ).comp (ratDivSES G).extClass` of the
coefficient sequence `0 → ℤ → ℚ → ℚ/ℤ → 0`. -/
theorem exists_divRep_of_ext_nonzero_aux (p : ℕ) [Fact p.Prime]
    (M : Rep.{0} SSGRoute.PTExt.Coeff G) (hM : ∀ m : M, p • m = 0)
    (φ : CategoryTheory.Abelian.Ext M (SSGRoute.PTExt.unitRep G) 1) (hφ : φ ≠ 0) :
    ∃ μ : M ⟶ Work.SSGRoute.E7cOmega.divRep G,
      μ ≠ 0 ∧ φ = (CategoryTheory.Abelian.Ext.mk₀ μ).comp
        (CategoryTheory.ShortComplex.ShortExact.extClass
          (Work.SSGRoute.E7cOmega.ratDivSES_shortExact
            (G := G))) (zero_add 1) := by
  -- the two vanishings of the coefficients `ℚ` (in degrees `0` and `1`)
  have h₀ : Subsingleton (CategoryTheory.Abelian.Ext M
      (Work.SSGRoute.E7cOmega.ratDivSES (G := G)).X₂ 0) :=
    Work.SSGRoute.SSGStage.subsingleton_ext_zero_ratRep M hM
  have h₁ : Subsingleton (CategoryTheory.Abelian.Ext M
      (Work.SSGRoute.E7cOmega.ratDivSES (G := G)).X₂ 1) :=
    Work.E7cOmega.subsingleton_ext_one_ratRep G p M hM
  -- hence the connecting map is surjective, and `φ` is the image of some `x₃`
  obtain ⟨x₃, hx₃post⟩ := (Work.Ext.extClass_postcomp_bijective_Rep M
    (Work.SSGRoute.E7cOmega.ratDivSES (G := G))
    (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := G)) (zero_add 1) h₀ h₁).2 φ
  have hx₃ : x₃.comp (CategoryTheory.ShortComplex.ShortExact.extClass
      (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := G))) (zero_add 1) = φ := by
    rw [← Work.SSGRoute.ext_postcomp_apply (CategoryTheory.ShortComplex.ShortExact.extClass
      (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := G))) M (zero_add 1) x₃]
    exact hx₃post
  -- `mk₀` is the inverse of `Ext.addEquiv₀`, so the two ways of viewing `x₃` agree
  have h2 : (CategoryTheory.Abelian.Ext.mk₀ (CategoryTheory.Abelian.Ext.addEquiv₀ x₃)).comp
        (CategoryTheory.ShortComplex.ShortExact.extClass
          (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := G))) (zero_add 1)
      = x₃.comp (CategoryTheory.ShortComplex.ShortExact.extClass
          (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := G))) (zero_add 1) :=
    congrArg (fun z : CategoryTheory.Abelian.Ext M
          (Work.SSGRoute.E7cOmega.ratDivSES (G := G)).X₃ 0 =>
        z.comp (CategoryTheory.ShortComplex.ShortExact.extClass
          (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := G))) (zero_add 1))
      (CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply x₃)
  refine ⟨CategoryTheory.Abelian.Ext.addEquiv₀ x₃, ?_, ?_⟩
  · -- the coefficient map is non-zero: `x₃ ≠ 0`, since `φ = δ x₃ ≠ 0`
    intro hμ
    have hx₃0 : x₃ = 0 :=
      (CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply x₃).symm.trans
        ((congrArg CategoryTheory.Abelian.Ext.mk₀ hμ).trans
          (CategoryTheory.Abelian.Ext.mk₀_zero M (Work.SSGRoute.E7cOmega.divRep G)))
    have hz : x₃.comp (CategoryTheory.ShortComplex.ShortExact.extClass
        (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := G))) (zero_add 1) = 0 := by
      rw [hx₃0]
      exact CategoryTheory.Abelian.Ext.zero_comp M 0 _ 1 (zero_add 1)
    exact hφ (hx₃.symm.trans hz)
  · exact hx₃.symm.trans h2.symm

/-- **The requested statement.**  Over the decomposition group `D_w ≤ Gal(K/k)` of a place `w`,
every non-zero class in `Ext¹_{D_w}(M, ℤ)` (with `M` killed by `p`, restricted to `D_w`) is the
image of a non-zero `D_w`-equivariant functional `M ⟶ ℚ/ℤ` under the connecting map of the
coefficient sequence `0 → ℤ → ℚ → ℚ/ℤ → 0`. -/
theorem functional_of_ext_nonzero (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1) (hφ : φ ≠ 0) :
    ∃ μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
        Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w),
      μ ≠ 0 ∧ φ = (CategoryTheory.Abelian.Ext.mk₀ μ).comp
        (CategoryTheory.ShortComplex.ShortExact.extClass
          (Work.SSGRoute.E7cOmega.ratDivSES_shortExact
            (G := SSGRoute.PTExt.decompK (k := k) (K := K) w))) (zero_add 1) := by
  -- the `p`-torsion of `M` is inherited by its restriction to `D_w`
  have hM' : ∀ m : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M,
      p • m = 0 := fun m => hM m
  exact exists_divRep_of_ext_nonzero_aux p
    (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M) hM' φ hφ

end

end Work.E7cOmega
