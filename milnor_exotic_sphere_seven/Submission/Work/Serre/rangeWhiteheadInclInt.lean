import Mathlib
import Submission.Work.Serre.cubePairDefs
import Submission.Work.Serre.serreE2b
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

/-- **Compression in a range implies an isomorphism on integral homology in the range.**
If the pair `(Y, A)` has the compression property up to degree `M`, then the inclusion
`A ↪ Y` induces an isomorphism on integral homology in degrees `< M`.  (The proof is the long exact
sequence of the pair together with `Work.Serre.SerreE2b`: the relative homology
`H_n(Y,A) = 0` for `n ≤ M` makes the connecting maps of the pair sequence zero, so the maps induced
by the inclusion are simultaneously mono and epi.  The same computation is carried out inside
`Submission/Work/Serre/RangeOne/Comparison.lean` as the local step `hint`). -/
theorem rangeWhiteheadInclInt {Y : Type} [TopologicalSpace Y] {A : Set Y} {M : ℕ}
    (hcomp : ∀ d, d ≤ M → Work.RatHurewicz.CompressRel Y A d) :
    ∀ t : ℕ, t < M →
      IsIso (HomologicalComplex.homologyMap (Work.Cohomology.inclChains (TopCat.of Y) A) t) := by
  intro t ht
  -- Relative homology vanishes in degrees `≤ M`, by Serre's theorem E2(b).
  have hrel : ∀ n : ℕ, n ≤ M →
      IsZero ((Work.Cohomology.relChains (TopCat.of Y) A).homology n) :=
    fun n hn => by
      obtain ⟨H⟩ := simpHom_of_compress M (fun d hd => hcomp d hd)
      exact simpHomVanishing H n hn
  -- Exactness of the pair long exact sequence then forces mono and epi.
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

end Work.Serre
