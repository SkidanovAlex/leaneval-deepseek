-- PORTED COPY (neutral island) of `Submission/Work/Serre/relPA_ratGenerator.lean`.
-- The only changes are: the imports of ratShuffle-island modules are redirected to the
-- copies in `Submission/Work/Serre/Neu/`, and the abbrev `singSSet` is renamed to
-- `singSSetN` (same body) so that this module can coexist with `Work.Serre.E0Defs`,
-- which declares the same name.  Declarations and proofs are unchanged.
import Mathlib
import Submission.Work.Serre.Neu.Defs
import Submission.Work.Serre.relKronEquiv
import Submission.Work.Serre.Neu.RatHyp
import Submission.Work.StemsB.RelChainsBaseChangeRat
import Submission.Work.Serre.Neu.SurjDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A rational generator of the relative homology in the detecting degree

Given a pair `(P,Q)` whose rational relative cohomology vanishes in degrees `0 < n ≤ N+1`,
`n ≠ r+1`, is trivial in degree `0` and **one-dimensional** in degree `r+1` (`hgen`), the rational
relative homology `H_{r+1}(P,Q;ℚ)` is a line: there is a relative cycle `v₀` whose class generates
it, and which is represented by an absolute chain `vt₀` (`rdRProj vt₀ = iCycles v₀`).

The proof only uses the **relative Kronecker pairing over `ℚ`**,
`Work.Serre.relKronEquiv`, which gives a linear equivalence
`H^{r+1}(P,Q;ℚ) ≃ₗ (H_{r+1}(P,Q;ℚ) →ₗ[ℚ] ℚ)`.  Hence the dual of `H_{r+1}(P,Q;ℚ)` is
one-dimensional, and over a field the finrank of a space equals the finrank of its dual, so
`H_{r+1}(P,Q;ℚ)` itself is one-dimensional (`finrank_one_of_dual_iso_rat`).  A generator is then
lifted to a cycle through the surjective `homologyπ` and to an absolute chain through the
surjective `rdRProj`.  The vanishing hypotheses `hvan`, `hzero` are not needed for this statement.
-/

namespace Work.Serre

theorem relPA_ratGenerator (P : Type) [TopologicalSpace P] (Q : Set P) (r N : ℕ)
    (hvan : ∀ n : ℕ, 0 < n → n ≤ N + 1 → n ≠ r + 1 →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.relComplex ℚ (TopCat.of P) Q).homology n))
    (hzero : CategoryTheory.Limits.IsZero ((Work.Cohomology.relComplex ℚ (TopCat.of P) Q).homology 0))
    (hgen : Nonempty ((Work.Cohomology.relComplex ℚ (TopCat.of P) Q).homology (r + 1) ≅
      ModuleCat.of ℚ ℚ)) :
    ∃ (v₀ : ↥((Work.Serre.relPA_rat P Q).cycles (r + 1)))
      (vt₀ : (Work.Cohomology.singularChains ℚ (TopCat.of P)).X (r + 1)),
      (Work.StemsB.rdRProj ℚ (TopCat.of P) Q (r + 1)) vt₀
          = (Work.Serre.relPA_rat P Q).iCycles (r + 1) v₀
      ∧ (∀ w : ↥((Work.Serre.relPA_rat P Q).homology (r + 1)),
          ∃ q : ℚ, w = q • ((Work.Serre.relPA_rat P Q).homologyπ (r + 1)) v₀) := by
  -- the relative Kronecker pairing over `ℚ` identifies `H^{r+1}` with the dual of `H_{r+1}`
  obtain ⟨eK⟩ := Work.Serre.relKronEquiv (TopCat.of P) Q (r + 1)
  obtain ⟨eC⟩ := hgen
  have hdual : Nonempty
      ((↥((Work.StemsB.relChainsR ℚ (TopCat.of P) Q).homology (r + 1)) →ₗ[ℚ] ℚ) ≃ₗ[ℚ] ℚ) :=
    ⟨eK.symm.trans eC.toLinearEquiv⟩
  -- the dual of `H_{r+1}(P,Q;ℚ)` is a line, hence so is `H_{r+1}(P,Q;ℚ)` itself
  have hfin : Module.finrank ℚ
      ↥((Work.StemsB.relChainsR ℚ (TopCat.of P) Q).homology (r + 1)) = 1 :=
    Work.Serre.finrank_one_of_dual_iso_rat hdual
  obtain ⟨u₀, hu₀, hspan⟩ := (finrank_eq_one_iff' (K := ℚ)
    (V := ↥((Work.StemsB.relChainsR ℚ (TopCat.of P) Q).homology (r + 1)))).mp hfin
  -- lift the generator to a cycle, and the cycle to an absolute chain
  have hsurj : Function.Surjective
      ((Work.StemsB.relChainsR ℚ (TopCat.of P) Q).homologyπ (r + 1)).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨v₀, hv₀⟩ := hsurj u₀
  obtain ⟨vt₀, hvt₀⟩ := Work.StemsB.rdRProj_surjective ℚ (TopCat.of P) Q (r + 1)
      ((Work.StemsB.relChainsR ℚ (TopCat.of P) Q).iCycles (r + 1) v₀)
  refine ⟨v₀, vt₀, hvt₀, ?_⟩
  intro w
  obtain ⟨c, hc⟩ := hspan w
  exact ⟨c, by rw [← hc, ← hv₀]⟩

end Work.Serre
