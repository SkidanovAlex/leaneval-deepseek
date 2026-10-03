import Submission.Work.ORCoherence.Imports
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Algebra.Module.FinitePresentation

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory Limits
open scoped TensorProduct

namespace Work.ORCoherence

universe u

/-- `globalDim R ≤ n` unfolds to the pointwise statement about projective dimensions. -/
theorem globalDim_le_iff' (R : Type u) [Ring R] (n : ℕ) :
    globalDim R ≤ (n : WithBot ℕ∞) ↔ ∀ M : ModuleCat.{u} R, HasProjectiveDimensionLE M n := by
  rw [globalDim, iSup_le_iff]
  exact forall_congr' (fun M => projectiveDimension_le_iff M n)

/-- If `R` has global dimension at most two, then the kernel of a linear map
`Rⁿ → R` is a projective `R`-module.  This is the dimension-shifting step in the
proof of JL Corollary 3.3. -/
theorem projective_ker_of_hasProjectiveDimensionLE {R : Type u} [Ring R]
    (h : ∀ M : ModuleCat.{u} R, HasProjectiveDimensionLE M 2)
    (n : ℕ) (φ : (Fin n →₀ R) →ₗ[R] R) :
    Projective (ModuleCat.of R (↥(LinearMap.ker φ))) := by
  have hex1 : (ShortComplex.mk (ModuleCat.ofHom (Submodule.subtype (LinearMap.range φ)))
      (ModuleCat.ofHom (Submodule.mkQ (LinearMap.range φ))) (by ext x; simp)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    simp only [ModuleCat.hom_ofHom, Submodule.range_subtype, Submodule.ker_mkQ]
  set S₁ : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.mk (ModuleCat.ofHom (Submodule.subtype (LinearMap.range φ)))
      (ModuleCat.ofHom (Submodule.mkQ (LinearMap.range φ))) (by ext x; simp) with hS₁
  have hS₁ex : S₁.Exact := hex1
  haveI hm₁ : Mono S₁.f := (ModuleCat.mono_iff_injective S₁.f).mpr Subtype.coe_injective
  haveI he₁ : Epi S₁.g := (ModuleCat.epi_iff_surjective S₁.g).mpr (Submodule.mkQ_surjective _)
  have hI2 : HasProjectiveDimensionLT (ModuleCat.of R (↥(LinearMap.range φ))) 2 := by
    have hS : S₁.ShortExact := ShortComplex.ShortExact.mk' hS₁ex hm₁ he₁
    have h₂ : HasProjectiveDimensionLT S₁.X₂ 2 :=
      inferInstanceAs (HasProjectiveDimensionLT (ModuleCat.of R R) 2)
    have h₃ : HasProjectiveDimensionLT S₁.X₃ 3 :=
      inferInstanceAs (HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ LinearMap.range φ)) 3)
    exact hS.hasProjectiveDimensionLT_X₁ 2 h₂ h₃
  let K : Submodule R (Fin n →₀ R) := LinearMap.ker φ
  let I : Submodule R R := LinearMap.range φ
  let i₀ : ↥K →ₗ[R] (Fin n →₀ R) := K.subtype
  let q₀ : (Fin n →₀ R) →ₗ[R] ↥I := φ.codRestrict I (fun x => ⟨x, rfl⟩)
  have hq₀ : q₀.comp i₀ = 0 := by
    apply LinearMap.ext
    intro x
    refine Subtype.ext ?_
    show φ (x : Fin n →₀ R) = 0
    simpa [K] using x.2
  have hK : LinearMap.ker φ = K := rfl
  have hI : LinearMap.range φ = I := rfl
  have hex2 : (ShortComplex.moduleCatMk (X₁ := ↥K) (X₂ := Fin n →₀ R) (X₃ := ↥I) i₀ q₀ hq₀).Exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    show LinearMap.range i₀ = LinearMap.ker q₀
    rw [show LinearMap.range i₀ = K from Submodule.range_subtype K,
      show LinearMap.ker q₀ = LinearMap.ker φ from LinearMap.ker_codRestrict I φ _]
  set S₂ : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.moduleCatMk (X₁ := ↥K) (X₂ := Fin n →₀ R) (X₃ := ↥I) i₀ q₀ hq₀ with hS₂
  have hS₂ex : S₂.Exact := hex2
  haveI hm₂ : Mono S₂.f := (ModuleCat.mono_iff_injective S₂.f).mpr Subtype.coe_injective
  haveI he₂ : Epi S₂.g := by
    rw [ModuleCat.epi_iff_surjective]
    intro y
    exact ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩
  have hker : HasProjectiveDimensionLT (ModuleCat.of R (↥(LinearMap.ker φ))) 1 := by
    have hS : S₂.ShortExact := ShortComplex.ShortExact.mk' hS₂ex hm₂ he₂
    have h₂ : HasProjectiveDimensionLT S₂.X₂ 1 :=
      inferInstanceAs (HasProjectiveDimensionLT (ModuleCat.of R (Fin n →₀ R)) 1)
    have h₃ : HasProjectiveDimensionLT S₂.X₃ 2 :=
      inferInstanceAs (HasProjectiveDimensionLT (ModuleCat.of R (↥(LinearMap.range φ))) 2)
    exact hS.hasProjectiveDimensionLT_X₁ 1 h₂ h₃
  exact projective_iff_hasProjectiveDimensionLT_one.mpr hker

end Work.ORCoherence

namespace Work.ORCoherence

universe u

/-- A finitely generated ideal of `R` is the range of a linear map `Rⁿ → R` (with `Rⁿ` the
free module `Fin n →₀ R`). -/
theorem exists_finsupp_linearMap_range_eq_of_fg (R : Type u) [Ring R] (I : Ideal R) (hI : I.FG) :
    ∃ (n : ℕ) (φ : (Fin n →₀ R) →ₗ[R] R), LinearMap.range φ = I := by
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  refine ⟨n, Finsupp.lift R R (Fin n) s, ?_⟩
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [Finsupp.lift_apply]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rw [← hs]
    exact Submodule.subset_span ⟨i, rfl⟩
  · rw [← hs, Submodule.span_le]
    rintro y ⟨i, rfl⟩
    exact ⟨Finsupp.single i 1, by rw [Finsupp.lift_apply, Finsupp.sum_single_index] <;> simp⟩

end Work.ORCoherence
