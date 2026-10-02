import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Serre.serreE2b
import Submission.Work.Serre.C1Pair
import Submission.Work.Serre.C1Rat
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.RatHurewicz.compression_of_relPiVanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Range-Whitehead for subspace pairs: compression in a range gives homology isomorphisms

`Work.Serre.isIso_ratHomologyMap_setIncl_of_compressRel`: if the pair `(Y, A)` has the compression
property in degrees `≤ M` (`Work.RatHurewicz.CompressRel`), then the inclusion `A ↪ Y` induces an
isomorphism on rational homology in degrees `< M`.

This is the clean ("no top degree") range form of the mapping theorem that the chapter's
`Work.Serre.rangeWhiteheadPair`/`Work.Serre.serreK2` route leaves open; it is what the comparison of
a range model with a genuine Eilenberg--MacLane space consumes.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Work.Serre

noncomputable section

/-- **Compression in a range ⟹ isomorphism on rational homology in the range.**

`hcomp` is the compression property of the pair `(Y,A)` in degrees `≤ M`; then
`H_t(A;ℚ) ≅ H_t(Y;ℚ)` for `t < M`.  The proof is the pair long exact sequence together with
`SerreE2b` (relative homology vanishes below `M`), followed by the `ℤ → ℚ` transfer. -/
theorem isIso_ratHomologyMap_setIncl_of_compressRel {Y : Type} [TopologicalSpace Y] {A : Set Y}
    {M : ℕ} (hcomp : ∀ d, d ≤ M → Work.RatHurewicz.CompressRel Y A d) :
    ∀ t : ℕ, t < M → IsIso (ratHomologyMap (Work.RatHurewicz.setIncl A) t) := by
  intro t ht
  have hrel : ∀ n : ℕ, n ≤ M → IsZero ((Work.Cohomology.relChains (TopCat.of Y) A).homology n) :=
    fun n hn => by
      obtain ⟨H⟩ := simpHom_of_compress M (fun d hd => hcomp d hd)
      exact simpHomVanishing H n hn
  have hint : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of Y) A) t) := by
    have hmono : Mono (HomologicalComplex.homologyMap
        (Work.Cohomology.inclChains (TopCat.of Y) A) t) := by
      rw [(Work.Cohomology.hPair_exact₁ (TopCat.of Y) A t).mono_g_iff]
      exact IsZero.eq_of_src (hrel (t + 1) (by omega)) _ _
    have hepi : Epi (HomologicalComplex.homologyMap
        (Work.Cohomology.inclChains (TopCat.of Y) A) t) := by
      rw [(Work.Cohomology.hPair_exact₂ (TopCat.of Y) A t).epi_f_iff]
      exact IsZero.eq_of_tgt (hrel t (by omega)) _ _
    haveI := hmono
    haveI := hepi
    exact isIso_of_mono_of_epi _
  have h := isIso_homologyMap_rat_of_isIso_int (TopCat.of ↥A) (TopCat.of Y)
    (Work.Cohomology.subtypeIncl (TopCat.of Y) A) t hint
  exact h

end

end Work.Serre
