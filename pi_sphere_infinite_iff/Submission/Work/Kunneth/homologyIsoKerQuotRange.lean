import Mathlib
import Submission.Work.Kunneth.ctensAux

/-!
# `H^n` of a cochain complex of `ℤ`-modules as `ker d^n ⧸ im d^{n-1}`

Mathlib computes the homology of a short complex of modules
(`ShortComplex.moduleCatHomologyIso`) as the quotient of the kernel of `g` by the image
of `f` inside it.  This file packages the resulting description of `H^n` of a cochain
complex `C` in the form used by the Künneth development, namely the quotient

`homologyQuot C n = ker d^n ⧸ (im d^{n-1} ∩ ker d^n)`.

The proof uses `C.sc' (n-1) n (n+1)` (the degree-`n` short complex with the indices made
explicit) rather than `C.sc n`, so that `f = C.d (n-1) n` and `g = C.d n (n+1)` hold
definitionally and no rewriting of the dependent index is needed; the comparison between
`C.homology n` and the homology of `C.sc' (n-1) n (n+1)` is Mathlib's
`HomologicalComplex.homologyIsoSc'`.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

-- The general `AddCommGroup.toIntModule` instance creates a diamond with the `Module ℤ`
-- structure that a submodule inherits from its ambient module.  Remove it, exactly as is
-- done in `Submission.Work.Kunneth.ctensAux`, so that quotient modules below are formed
-- with the intended instance.
attribute [-instance] AddCommGroup.toIntModule

namespace Work.Kunneth

/-- For a short complex `S` of `ℤ`-modules, the homology computed by Mathlib's explicit
left homology data is the quotient of `ker S.g` by the image of `S.f` inside it. -/
lemma moduleCatLeftHomologyData_H_eq (S : ShortComplex (ModuleCat ℤ)) :
    S.moduleCatLeftHomologyData.H =
      ModuleCat.of ℤ (LinearMap.ker S.g.hom ⧸
        (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype) := by
  have hB : LinearMap.range S.moduleCatToCycles =
      (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype := by
    rw [show S.moduleCatToCycles =
      S.f.hom.codRestrict (LinearMap.ker S.g.hom) S.moduleCat_zero_apply from rfl]
    exact LinearMap.range_codRestrict _ _ _
  rw [ShortComplex.moduleCatLeftHomologyData_H, hB]

theorem homologyIsoKerQuotRange (C : CochainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    Nonempty (CategoryTheory.Iso (C.homology n) (homologyQuot C n)) := by
  have hprev : (ComplexShape.up ℕ).prev n = n - 1 := by
    match n with
    | 0 => simp
    | m + 1 => simp
  have hnext : (ComplexShape.up ℕ).next n = n + 1 := CochainComplex.next ℕ n
  refine ⟨C.homologyIsoSc' (n - 1) n (n + 1) hprev hnext ≪≫
    ShortComplex.moduleCatHomologyIso (C.sc' (n - 1) n (n + 1)) ≪≫ eqToIso ?_⟩
  rw [moduleCatLeftHomologyData_H_eq]
  unfold homologyQuot
  rfl

end Work.Kunneth
