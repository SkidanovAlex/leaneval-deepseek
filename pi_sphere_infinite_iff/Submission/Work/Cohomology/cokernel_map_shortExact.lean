import Mathlib

/-!
# The cokernel of a morphism of short exact complexes is short exact

Given a morphism `v : S₁ ⟶ S₂` of short exact short complexes whose three components
`v.τ₁`, `v.τ₂`, `v.τ₃` are monomorphisms, the induced sequence of cokernels
`cokernel v.τ₁ ⟶ cokernel v.τ₂ ⟶ cokernel v.τ₃` is short exact.

This is the (right) `6`-term part of the snake lemma: since the components of `v` are mono,
the kernel of `v` in the abelian category `ShortComplex C` is the zero short complex, so the
snake lemma applied to `v` yields the short exactness of the cokernel complex.

## Main result

* `Work.Cohomology.cokernel_map_shortExact`
-/

namespace Work.Cohomology

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

theorem cokernel_map_shortExact {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C]
    {S₁ S₂ : CategoryTheory.ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    (v : S₁ ⟶ S₂) (hv₁ : CategoryTheory.Mono v.τ₁) (hv₂ : CategoryTheory.Mono v.τ₂)
    (hv₃ : CategoryTheory.Mono v.τ₃) :
    ∃ (f : CategoryTheory.Limits.cokernel (v.τ₁) ⟶ CategoryTheory.Limits.cokernel (v.τ₂))
      (g : CategoryTheory.Limits.cokernel (v.τ₂) ⟶ CategoryTheory.Limits.cokernel (v.τ₃))
      (h : CategoryTheory.CategoryStruct.comp f g = 0),
      (CategoryTheory.ShortComplex.mk f g h).ShortExact := by
  -- The maps induced on cokernels by `v.τ₁` and `v.τ₂` (resp. `v.τ₂` and `v.τ₃`).
  let f : cokernel v.τ₁ ⟶ cokernel v.τ₂ := cokernel.map v.τ₁ v.τ₂ S₁.f S₂.f v.comm₁₂
  let g : cokernel v.τ₂ ⟶ cokernel v.τ₃ := cokernel.map v.τ₂ v.τ₃ S₁.g S₂.g v.comm₂₃
  -- The two defining relations of `f` and `g`.
  have hπf : cokernel.π v.τ₁ ≫ f = S₂.f ≫ cokernel.π v.τ₂ := by
    simp only [f, cokernel.map, cokernel.π_desc]
  have hπg : cokernel.π v.τ₂ ≫ g = S₂.g ≫ cokernel.π v.τ₃ := by
    simp only [g, cokernel.map, cokernel.π_desc]
  -- `f ≫ g = 0` follows from those relations and `S₂.f ≫ S₂.g = 0`.
  have hfg : f ≫ g = 0 := by
    rw [← cancel_epi (cokernel.π v.τ₁), comp_zero, ← Category.assoc, hπf, Category.assoc, hπg,
      ← Category.assoc, S₂.zero, zero_comp]
  refine ⟨f, g, hfg, ?_⟩
  -- The candidate cokernel complex.
  let C₀ : ShortComplex C := ShortComplex.mk f g hfg
  -- The map `S₂ ⟶ C₀` given by the three cokernel projections.
  let φ : S₂ ⟶ C₀ := ShortComplex.homMk (cokernel.π v.τ₁) (cokernel.π v.τ₂) (cokernel.π v.τ₃) hπf hπg
  have w₁₃ : v ≫ φ = 0 := by
    ext <;> simp [ShortComplex.comp_τ₁, φ, cokernel.condition]
  -- The snake input: `0` is the kernel of `v` (since all components of `v` are mono) and
  -- `C₀` is the cokernel of `v`.
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
  -- The snake lemma gives exactness of the cokernel complex at its middle term.
  have hex : C₀.Exact := sn.L₃_exact
  -- `coker v.τ₂ ⟶ coker v.τ₃` is an epimorphism because `S₂.g` is.
  have hg : Epi sn.L₂.g := h₂.epi_g
  have hepi : Epi g := sn.epi_L₃_g
  -- Monomorphy of `f`: the connecting map `δ` of the snake sequence starts at `L₀.X₃ = 0`,
  -- hence vanishes, and exactness of `0 ⟶ coker v.τ₁ ⟶ coker v.τ₂` gives `Mono f`.
  have hδ : sn.δ = 0 := IsZero.eq_zero_of_src (X := sn.L₀.X₃) (isZero_zero C) sn.δ
  have hmono : Mono f := ShortComplex.Exact.mono_g sn.L₂'_exact hδ
  exact ShortComplex.ShortExact.mk' hex hmono hepi

end Work.Cohomology
