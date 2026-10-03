import Mathlib
import Submission.Work.ORLyndon.ProjDim

namespace Work.ORLyndon

open CategoryTheory

/-- A left `R`-module admitting a projective resolution of length at most `n` (in the recursive
syzygy sense of `Work.ORLyndon.HasProjDimLE`) has `Ext`-theoretic projective dimension at most `n`,
i.e. `HasProjectiveDimensionLE`.  The proof is by induction on `n`, using the short exact sequence
`0 → ker f → P → M → 0` and dimension shifting
(`CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃`). -/
theorem hasProjectiveDimensionLE_of_hasProjDimLE {R : Type*} [Ring R] {M : Type*} [AddCommGroup M]
    [Module R M] {n : ℕ} (h : Work.ORLyndon.HasProjDimLE R M n) :
    CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  induction n generalizing M with
  | zero =>
    haveI : Module.Projective R M := h
    exact (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero
      (ModuleCat.of R M)).mp
      (ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of R M))
  | succ n ih =>
    rw [hasProjDimLE_succ] at h
    obtain ⟨P, hPadd, hPmod, hproj, f, hf, hker⟩ := h
    let S := f.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hf
    have h2 : HasProjectiveDimensionLT S.X₂ (n + 2) := by
      haveI : Module.Projective R P := hproj
      haveI : Projective S.X₂ := ModuleCat.projective_of_categoryTheory_projective S.X₂
      exact CategoryTheory.hasProjectiveDimensionLT_of_ge S.X₂ 1 (n + 2) (by omega)
    exact hS.hasProjectiveDimensionLT_X₃ (n + 1) (ih hker) h2

end Work.ORLyndon
