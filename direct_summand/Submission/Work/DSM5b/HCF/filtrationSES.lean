import Mathlib
import Submission.Work.DSM5b.HCF.Complex
import Submission.Work.DSM5b.HCF.sizeExact
import Submission.Work.DSM5b.HCF.stcExact

namespace Work.DSM5b.HCF

open Work.DSM5b CategoryTheory

universe u

/-- **Degreewise exactness of the size filtration, honest tuple complex.**  For every cohomological
degree `m`, the degree-`m` part of the sequence
`0 → C(𝒜_{≥k+1}) → C(𝒜_{≥k}) → C(𝒜_{=k}) → 0` — a short complex of `R`-modules — is short exact.

The degree-`m` terms are the products, over all tuples `τ : Fin (m+1) → ι`, of the modules
`↥((sizeSubSys 𝒜 k).N (tupRng τ))`, and the two maps are the termwise inclusion and quotient map;
`CoeffSys.Hom.htcMap` evaluated at a tuple `τ` is definitionally the component map at `tupRng τ`, and
`CoeffSys.sizeIncl`/`CoeffSys.sizeQuot` are definitionally the `Htc (subCF _)`/`Htc (exactlyCoeff _)`
presentations of those termwise maps, so `Work.DSM5b.HCF.sizeExact` (termwise exactness) applies. -/
lemma htc_filtration_degreewise {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]
    (𝒜 : CoeffSys R ι) (k m : ℕ) :
    ((ShortComplex.mk (htcHom (CoeffSys.subInclHom 𝒜 k))
        (htcHom (CoeffSys.subQuotHom 𝒜 k))
        (htc_subIncl_comp_subQuot 𝒜 k)).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) m)).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · rw [LinearMap.exact_iff]
    exact (sizeExact 𝒜 k m).2.2
  · exact (sizeExact 𝒜 k m).1
  · exact (sizeExact 𝒜 k m).2.1

/-- **Degreewise exactness of the size filtration, sorted (increasing tuple) complex.**  For every
cohomological degree `m`, the degree-`m` part of the sequence
`0 → C(𝒜_{≥k+1}) → C(𝒜_{≥k}) → C(𝒜_{=k}) → 0` for the sorted complex is short exact.

The terms are now the products over the *increasing* tuples `τ : IncrTuple m` of the same modules,
and the component maps are again a submodule inclusion followed by its quotient map; the termwise
exactness is `Work.DSM5b.HCF.stcExact`. -/
lemma stc_filtration_degreewise {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]
    [LinearOrder ι] (𝒜 : CoeffSys R ι) (k m : ℕ) :
    ((ShortComplex.mk (stcHom (CoeffSys.subInclHom 𝒜 k))
        (stcHom (CoeffSys.subQuotHom 𝒜 k))
        (stcSubIncl_comp_subQuot 𝒜 k)).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) m)).ShortExact := by
  have h := stcExact 𝒜 k m
  apply ModuleCat.shortComplex_shortExact
  · rw [LinearMap.exact_iff]
    exact h.2.2
  · exact h.1
  · exact h.2.1

/-- **The size filtration is a short exact sequence of complexes, for the honest tuple complex and
for the sorted (increasing tuple) complex.**  `subCF 𝒜 k` is the coefficient system of coefficients
supported on subsets of size at least `k` (`Work.DSM5b.CoeffSys.subCF`),
`exactlyCoeff 𝒜 k` its quotient by the next stage (`Work.DSM5b.CoeffSys.exactlyCoeff`),
`htcHom`/`stcHom` the induced morphisms of the honest/sorted complexes
(`Work.DSM5b.htcComplex`, `Work.DSM5b.stcComplex`) and `htc_subIncl_comp_subQuot` /
`stcSubIncl_comp_subQuot` the (proved) commutation-to-zero lemmas.  Claim: both rows
`0 → C(𝒜_{≥k+1}) → C(𝒜_{≥k}) → C(𝒜_{=k}) → 0` are short exact sequences of cochain complexes of
`R`-modules.  Route: `HomologicalComplex.shortExact_of_degreewise_shortExact` together with
`ModuleCat.shortComplex_shortExact`; each degree is a product (over all tuples, resp. over the
increasing tuples) of the exact sequence of coefficient systems
`0 → ↥(N_{k+1} S) → ↥(N_k S) → ↥(N_k S)/range(inclusion) → 0`, i.e. of the standard exact sequence
of a submodule inclusion followed by the quotient map.  (`Work.DSM5b.HCF.sizeExact`, already
proved, gives the termwise exactness for the honest complex in the `SizeC`/`SizeQ` presentation;
the `Htc (subCF _)`/`Htc (exactlyCoeff _)` presentation used here is definitionally the same.) -/
theorem filtrationSES {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] [LinearOrder ι]
    (𝒜 : Work.DSM5b.CoeffSys R ι) (k : ℕ) :
    (CategoryTheory.ShortComplex.mk (Work.DSM5b.htcHom (Work.DSM5b.CoeffSys.subInclHom 𝒜 k))
        (Work.DSM5b.htcHom (Work.DSM5b.CoeffSys.subQuotHom 𝒜 k))
        (Work.DSM5b.htc_subIncl_comp_subQuot 𝒜 k)).ShortExact ∧
      (CategoryTheory.ShortComplex.mk (Work.DSM5b.stcHom (Work.DSM5b.CoeffSys.subInclHom 𝒜 k))
        (Work.DSM5b.stcHom (Work.DSM5b.CoeffSys.subQuotHom 𝒜 k))
        (Work.DSM5b.stcSubIncl_comp_subQuot 𝒜 k)).ShortExact := by
  exact ⟨HomologicalComplex.shortExact_of_degreewise_shortExact _
      (fun m => htc_filtration_degreewise 𝒜 k m),
    HomologicalComplex.shortExact_of_degreewise_shortExact _
      (fun m => stc_filtration_degreewise 𝒜 k m)⟩

end Work.DSM5b.HCF
