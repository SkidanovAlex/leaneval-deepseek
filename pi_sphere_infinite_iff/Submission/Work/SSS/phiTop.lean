import Mathlib
import Submission.Work.SSS.Packet

set_option linter.style.haveILetI false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits

/-- **A general form of the "surjectivity of `H_n` from degrees `n` and `n-1`" lemma.**
If a morphism `φ : S₁ ⟶ S₂` of short complexes is an epimorphism in the middle
(`Epi φ.τ₂`) and a monomorphism on the right (`Mono φ.τ₃`), then it induces an
epimorphism on homology.

This is proved by the "up to refinements" elementwise criterion for epimorphisms:
given a cycle `y₂` of `S₂`, lift it along the epimorphism `φ.τ₂`; the lift `x₂` is a
cycle because `φ.τ₂ ≫ S₂.g = S₁.g ≫ φ.τ₃` and `φ.τ₃` is a monomorphism. -/
lemma epi_homologyMap_of_epi_of_mono {C : Type*} [Category* C] [Abelian C]
    {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) [Epi φ.τ₂] [Mono φ.τ₃] :
    Epi (ShortComplex.homologyMap φ) := by
  rw [ShortComplex.epi_homologyMap_iff_up_to_refinements]
  intro A y₂ hy₂
  obtain ⟨A', π, hπ, x₂, hx⟩ := surjective_up_to_refinements_of_epi φ.τ₂ y₂
  refine ⟨A', π, hπ, x₂, ?_, 0, ?_⟩
  · rw [← cancel_mono φ.τ₃, Category.assoc, ← φ.comm₂₃, ← Category.assoc, ← hx,
      Category.assoc, hy₂, comp_zero, zero_comp]
  · rw [zero_comp, add_zero]
    exact hx

/-- The `HomologicalComplex` form of `epi_homologyMap_of_epi_of_mono`: if a morphism of
complexes is an epimorphism in degree `i` and a monomorphism in the next degree of the
complex shape (for a chain complex, in degree `i - 1`), then it is surjective on `H_i`. -/
lemma epi_homologyMap_of_epi_of_mono_of_next {C : Type*} [Category* C] [Abelian C]
    {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex C c} (φ : K ⟶ L) (i : ι)
    (h₂ : Epi (φ.f i)) (h₃ : Mono (φ.f (c.next i))) :
    Epi (HomologicalComplex.homologyMap φ i) := by
  haveI : Epi ((HomologicalComplex.shortComplexFunctor C c i).map φ).τ₂ := by
    rw [HomologicalComplex.shortComplexFunctor_map_τ₂]; exact h₂
  haveI : Mono ((HomologicalComplex.shortComplexFunctor C c i).map φ).τ₃ := by
    rw [HomologicalComplex.shortComplexFunctor_map_τ₃]; exact h₃
  exact epi_homologyMap_of_epi_of_mono ((HomologicalComplex.shortComplexFunctor C c i).map φ)

/-- **The image filtration reaches `H_n(C)` in degree `n`.**  For a saturated filtration `ξ` of a
chain complex `C` of `ℤ`-modules (so that the `n`-th term `ξ.F.obj n` contains every `n`-chain, the
field `Filtration.sat`), the image of `H_n(ξ.F.obj n) → H_n(C)` is all of `H_n(C)`; equivalently the
submodule `Work.SSS.Phi ξ n (n : ℤ) = im(H_n(ξ.incl n))` of `H_n(C)` is `⊤`.

Proof: lift cycles.  The map `ξ.incl n` is an isomorphism in degree `n` (`Filtration.sat`) hence
an epimorphism there, and a monomorphism of complexes hence a monomorphism in every degree
(`HomologicalComplex.mono_f_of_mono`); thus the induced map on homology in degree `n` is an
epimorphism by `epi_homologyMap_of_epi_of_mono_of_next`, which is exactly the claim that its
range is `⊤`. -/
theorem phiTop (C : ChainComplex (ModuleCat ℤ) ℕ) (ξ : Work.SSS.Filtration C) (n : ℕ) :
    Work.SSS.Phi ξ n (n : ℤ) = ⊤ := by
  rw [Work.SSS.Phi, if_neg (by omega : ¬ ((n : ℤ) < 0))]
  simp only [Int.toNat_natCast]
  rw [LinearMap.range_eq_top]
  haveI : IsIso ((ξ.incl n).f n) := ξ.sat n
  haveI : Mono (ξ.incl n) := ξ.mono_incl n
  exact (ModuleCat.epi_iff_surjective _).1
    (epi_homologyMap_of_epi_of_mono_of_next (ξ.incl n) n inferInstance inferInstance)

end Work.SSS
