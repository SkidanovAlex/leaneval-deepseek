-- PORTED COPY (neutral island) of `Submission/Work/Serre/shufRat_surjective.lean`.
-- The only changes are: the imports of ratShuffle-island modules are redirected to the
-- copies in `Submission/Work/Serre/Neu/`, and the abbrev `singSSet` is renamed to
-- `singSSetN` (same body) so that this module can coexist with `Work.Serre.E0Defs`,
-- which declares the same name.  Declarations and proofs are unchanged.
import Mathlib
import Submission.Work.Serre.Neu.Defs
import Submission.Work.Serre.crossProduct_defs
import Submission.Work.Serre.tpC_homologyMap_cokernel_subsingleton
import Submission.Work.Serre.tensorRat_subsingleton_of_subsingleton
import Submission.Work.Serre.relEZ_main
import Submission.Work.StemsB.WangCohRat
import Submission.Work.StemsB.RelChainsBaseChangeRat
import Submission.Work.Cohomology.singularChains_free
import Submission.Work.Cohomology.uctDual
import Submission.Work.Serre.Neu.RatHyp
import Submission.Work.Serre.Neu.RelEZMap
import Submission.Work.Serre.ezMap_ezBilR
import Submission.Work.Serre.relKronEquiv
import Submission.Work.Serre.Neu.RelPAgen
import Submission.Work.Serre.Neu.SurjSetup2
import Submission.Work.Serre.Neu.SurjHzt
import Submission.Work.Serre.Neu.SurjCross
import Submission.Work.Serre.Neu.SurjV0

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Serre

/-- **The rational relative homology in the detecting degree is a line.** -/
theorem finrank_one_relPA (P : Type) [TopologicalSpace P] (Q : Set P) (r : ℕ)
    (hgen : Nonempty ((Work.Cohomology.relComplex ℚ (TopCat.of P) Q).homology (r + 1) ≅
      ModuleCat.of ℚ ℚ)) :
    Module.finrank ℚ ↥((Work.Serre.relPA_rat P Q).homology (r + 1)) = 1 := by
  obtain ⟨eK⟩ := Work.Serre.relKronEquiv (TopCat.of P) Q (r + 1)
  obtain ⟨eC⟩ := hgen
  exact Work.Serre.finrank_one_of_dual_iso_rat
    ⟨eK.symm.trans eC.toLinearEquiv⟩

theorem shufRat_surjective (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P]
    (Q : Set P) (r N : ℕ)
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
          ∃ q : ℚ, w = q • ((Work.Serre.relPA_rat P Q).homologyπ (r + 1)) v₀)
      ∧ (∀ m : ℕ, m + r + 1 ≤ N + 1 →
          ∃ T : (Work.Cohomology.singularChains ℚ (TopCat.of W)).homology m ⟶
              (Work.Serre.relBBA_rat W P Q).homology (m + r + 1),
            Function.Surjective T.hom ∧
            (∀ u : ↥((Work.Cohomology.singularChains ℚ (TopCat.of W)).cycles m),
              ∃ c : ↥((Work.Serre.relBBA_rat W P Q).cycles (m + r + 1)),
                (Work.StemsB.rdRProj ℚ (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q} (m + r + 1))
                    (Work.Serre.shufRat W P m (r + 1)
                      (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) vt₀)
                  = (Work.Serre.relBBA_rat W P Q).iCycles (m + r + 1) c
                ∧ T.hom (((Work.Cohomology.singularChains ℚ (TopCat.of W)).homologyπ m) u)
                    = ((Work.Serre.relBBA_rat W P Q).homologyπ (m + r + 1)) c)) := by
  obtain ⟨z, hz, hvanZ, hgenZ⟩ := Work.Serre.ratHypotheses (TopCat.of P) Q r N hvan hzero hgen
  have hzt := Work.Serre.Surj.tmul_one_homologyπ_ne_zero_of_hgen P Q r hgen z hgenZ
  obtain ⟨vtz, hvtz⟩ := Work.StemsB.rdRProj_surjective ℤ (TopCat.of P) Q (r + 1)
    ((ModuleCat.Hom.hom ((Work.Cohomology.relChains (TopCat.of P) Q).iCycles (r + 1))) z)
  refine ⟨Work.Serre.Surj.v0Of P Q r z vtz hvtz, Work.Serre.Surj.vt0Of P r vtz,
    ?_, ?_, ?_⟩
  · exact (Work.Serre.Surj.iCycles_cycleOfQ (Work.StemsB.relChainsR ℚ (TopCat.of P) Q) (r + 1)
      _ _).symm
  · intro w
    have hfin : Module.finrank ℚ ↥((Work.Serre.relPA_rat P Q).homology (r + 1)) = 1 :=
      finrank_one_relPA P Q r hgen
    obtain ⟨q, hq⟩ := Work.Serre.exists_rat_smul_eq_of_finrank_one hfin
      (u₀ := (ModuleCat.Hom.hom ((Work.Serre.relPA_rat P Q).homologyπ (r + 1)))
        (Work.Serre.Surj.v0Of P Q r z vtz hvtz))
      (u := w) (Work.Serre.Surj.v0OfClassNeZero P Q r z vtz hvtz hzt)
    exact ⟨q, hq⟩
  · intro m hm
    exact Work.Serre.Surj.crossProductQ W P Q r N z vtz hvtz hzt hvanZ hgenZ m hm



end Work.Serre
