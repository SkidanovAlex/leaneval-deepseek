import Mathlib
import Submission.Work.Cohomology.Singular

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Cohomology

open CategoryTheory Limits

/-- Splitting lemma: let `g : P ⟶ C` be a monomorphism with `g ≫ f = 0` whose range is exactly
the kernel of `f : C ⟶ K`, and let `σ` be a section of `f` (i.e. `σ ≫ f = 𝟙`). Then `C` is the
biproduct of `P` and `K`, with the second projection given by `σ`. -/
theorem iso_of_section_ker {P C K : ModuleCat ℤ} (f : C ⟶ K) (σ : K ⟶ C) (g : P ⟶ C)
    (hg : Mono g) (hgf : g ≫ f = 0)
    (hker : LinearMap.range (ModuleCat.Hom.hom g) = LinearMap.ker (ModuleCat.Hom.hom f))
    (hsec : σ ≫ f = 𝟙 K) :
    ∃ (e : P ⊞ K ≅ C), (biprod.inr : K ⟶ P ⊞ K) ≫ e.hom = σ := by
  -- Package `g` and `f` into a short complex, exact by hypothesis.
  let S : ShortComplex (ModuleCat ℤ) := ShortComplex.mk g f hgf
  have hS : S.Exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact hker
  -- The section `σ` of `S.g = f` splits the short complex.
  let sp : S.Splitting := ShortComplex.Splitting.ofExactOfSection S hS σ hsec hg
  refine ⟨sp.isoBinaryBiproduct.symm, ?_⟩
  rw [Iso.symm_hom, ShortComplex.Splitting.isoBinaryBiproduct_inv]
  rw [biprod.inr_desc]
  rfl

end Work.Cohomology
