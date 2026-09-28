import Mathlib
import Submission.Work.Cohomology.cokernel_map_shortExact

namespace Work.Cohomology.Crux

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

/-- **The canonical cokernel of a morphism of short exact complexes is short exact.**  For a
morphism `v : S₁ ⟶ S₂` of short exact short complexes with monomorphic components, the *canonical*
maps induced on the cokernels make a short exact complex. -/
theorem cokernel_map_shortExact_canonical {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] {S₁ S₂ : CategoryTheory.ShortComplex C} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (v : S₁ ⟶ S₂) (hv₁ : CategoryTheory.Mono v.τ₁)
    (hv₂ : CategoryTheory.Mono v.τ₂) (hv₃ : CategoryTheory.Mono v.τ₃) :
    ∃ (h : CategoryTheory.CategoryStruct.comp
        (CategoryTheory.Limits.cokernel.map v.τ₁ v.τ₂ S₁.f S₂.f v.comm₁₂)
        (CategoryTheory.Limits.cokernel.map v.τ₂ v.τ₃ S₁.g S₂.g v.comm₂₃) = 0),
      (CategoryTheory.ShortComplex.mk
        (CategoryTheory.Limits.cokernel.map v.τ₁ v.τ₂ S₁.f S₂.f v.comm₁₂)
        (CategoryTheory.Limits.cokernel.map v.τ₂ v.τ₃ S₁.g S₂.g v.comm₂₃) h).ShortExact := by
  let f : cokernel v.τ₁ ⟶ cokernel v.τ₂ := cokernel.map v.τ₁ v.τ₂ S₁.f S₂.f v.comm₁₂
  let g : cokernel v.τ₂ ⟶ cokernel v.τ₃ := cokernel.map v.τ₂ v.τ₃ S₁.g S₂.g v.comm₂₃
  have hπf : cokernel.π v.τ₁ ≫ f = S₂.f ≫ cokernel.π v.τ₂ := by
    simp only [f, cokernel.map, cokernel.π_desc]
  have hπg : cokernel.π v.τ₂ ≫ g = S₂.g ≫ cokernel.π v.τ₃ := by
    simp only [g, cokernel.map, cokernel.π_desc]
  have hfg : f ≫ g = 0 := by
    rw [← cancel_epi (cokernel.π v.τ₁), comp_zero, ← Category.assoc, hπf, Category.assoc, hπg,
      ← Category.assoc, S₂.zero, zero_comp]
  refine ⟨hfg, ?_⟩
  let C₀ : ShortComplex C := ShortComplex.mk f g hfg
  change C₀.ShortExact
  let φ : S₂ ⟶ C₀ := ShortComplex.homMk (cokernel.π v.τ₁) (cokernel.π v.τ₂) (cokernel.π v.τ₃) hπf hπg
  have w₁₃ : v ≫ φ = 0 := by
    ext <;> simp [ShortComplex.comp_τ₁, φ, cokernel.condition]
  let sn : ShortComplex.SnakeInput C :=
    { L₀ := ShortComplex.mk (0 : (0 : C) ⟶ (0 : C)) (0 : (0 : C) ⟶ (0 : C)) (by simp)
      L₁ := S₁
      L₂ := S₂
      L₃ := C₀
      v₀₁ := 0
      v₁₂ := v
      v₂₃ := φ
      w₀₂ := by simp
      w₁₃ := w₁₃
      h₀ := by
        apply ShortComplex.isLimitOfIsLimitπ
        · exact (KernelFork.isLimitMapConeEquiv _ _).2 (kernel.isLimitConeZeroCone v.τ₁)
        · exact (KernelFork.isLimitMapConeEquiv _ _).2 (kernel.isLimitConeZeroCone v.τ₂)
        · exact (KernelFork.isLimitMapConeEquiv _ _).2 (kernel.isLimitConeZeroCone v.τ₃)
      h₃ := by
        apply ShortComplex.isColimitOfIsColimitπ
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).2 (cokernelIsCokernel v.τ₁)
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).2 (cokernelIsCokernel v.τ₂)
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).2 (cokernelIsCokernel v.τ₃)
      L₁_exact := h₁.exact
      epi_L₁_g := h₁.epi_g
      L₂_exact := h₂.exact
      mono_L₂_f := h₂.mono_f }
  have hex : C₀.Exact := sn.L₃_exact
  have hg : Epi sn.L₂.g := h₂.epi_g
  have hepi : Epi g := sn.epi_L₃_g
  have hδ : sn.δ = 0 := IsZero.eq_zero_of_src (X := sn.L₀.X₃) (isZero_zero C) sn.δ
  have hmono : Mono f := ShortComplex.Exact.mono_g sn.L₂'_exact hδ
  exact ShortComplex.ShortExact.mk' hex hmono hepi

end Work.Cohomology.Crux
