import Mathlib
import Submission.NK.LocalCFT.Basic
import Submission.NK.LocalCFT.NormGroup.normGroup_eq_iff
import Submission.Commons.FieldTheory.Galois.exists_finite_galois_containing

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace NK.LocalCFT.Functoriality

universe u v

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **The level restrictions separate points of `Gal(F^{ab}/F)`.**

If two elements of `Gal(F^{ab}/F)` have the same restriction to every finite-dimensional normal
level `L ≤ F^{ab}`, they are equal.  Indeed, if `ρ ≠ 1` there is `y` with `ρ y ≠ y`; by
`Commons.FieldTheory.Galois.exists_finite_galois_containing` the element `y` lies in a
finite-dimensional Galois (hence normal) intermediate field `L`, and `ρ y ≠ y` means that `ρ`
does not fix `L` pointwise, i.e. its restriction to `L` is not trivial. -/
theorem eq_of_forall_levelRestrict_eq (σ τ : NK.LocalCFT.AbGal F F')
    (h : ∀ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
      [FiniteDimensional F L] [Normal F L],
      NK.LocalCFT.levelRestrict L σ = NK.LocalCFT.levelRestrict L τ) :
    σ = τ := by
  by_contra hne
  have hρ : σ * τ⁻¹ ≠ 1 := fun h1 => hne (mul_inv_eq_one.mp h1)
  obtain ⟨y, hy⟩ : ∃ y : ↥(NK.LocalReciprocity.maxAbelianSubext F F'),
      (σ * τ⁻¹) y ≠ y := by
    by_contra hcon
    push Not at hcon
    exact hρ (AlgEquiv.ext fun y => hcon y)
  obtain ⟨L, hfin, hgal, hyL⟩ :=
    Commons.FieldTheory.Galois.exists_finite_galois_containing
      (k := F) (K := ↥(NK.LocalReciprocity.maxAbelianSubext F F')) y
  haveI : FiniteDimensional F L := hfin
  haveI : Normal F L := hgal.to_normal
  have hres : NK.LocalCFT.levelRestrict L (σ * τ⁻¹) = 1 := by
    rw [map_mul, map_inv, h L, mul_inv_cancel]
  have hmem : σ * τ⁻¹ ∈ (NK.LocalCFT.levelRestrict L).ker := by
    rw [MonoidHom.mem_ker, hres]
  rw [NK.LocalCFT.levelRestrict, IntermediateField.restrictNormalHom_ker] at hmem
  exact hy ((IntermediateField.mem_fixingSubgroup_iff L (σ * τ⁻¹)).mp hmem y hyL)

theorem artin_eq_of_comp_levelRestrict_eq {F : Type u} {F' : Type v} [Field F] [Field F']
    [Algebra F F'] [IsGalois F F'] (D : NK.LocalCFT.ArtinReciprocity F F')
    (φ : Fˣ →* NK.LocalCFT.AbGal F F')
    (h : ∀ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
      [FiniteDimensional F L] [Normal F L]
      (hc : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ),
      (NK.LocalCFT.levelRestrict L).comp φ = (NK.LocalCFT.levelRestrict L).comp D.artin) :
    φ = D.artin := by
  refine MonoidHom.ext fun x => ?_
  refine eq_of_forall_levelRestrict_eq (φ x) (D.artin x) ?_
  intro L hfin hnorm
  haveI : FiniteDimensional F L := hfin
  haveI : Normal F L := hnorm
  exact DFunLike.congr_fun
    (h L (NK.LocalCFT.NormGroup.normGroup_eq_iff_commutative_gal L)) x

end NK.LocalCFT.Functoriality
