/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The group von Neumann algebra `N(G)` admits a faithful Sylvester rank function

For a countable group `G` the extended rank function `rk_G` of the group von Neumann algebra
`N(G) = ρ(G)' ⊆ B(ℓ²(G))` is

`rk_G(A) = n - dim_G (ker A†)`   for `A ∈ M_{n×m}(N(G))`,

where `dim_G` is the von Neumann dimension of a closed subspace of `⊕_{i : Fin n} ℓ²(G)`.  It
is a faithful Sylvester matrix rank function (Jaikin-Zapirain–López-Álvarez, arXiv:1810.12135,
§3.2–3.4; Lück, *L²-Invariants*, Theorem 6.7); this is the analytic input of the one-relator
coherence project.

The construction and the verification of the five axioms are in
`Work.ORVonNeumann.Rep.vnRankFunction`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.SylvesterRank
import Submission.Work.ORVonNeumann.Rep.GroupVonNeumann
import Submission.Work.ORVonNeumann.Rep.Trace
import Submission.Work.ORVonNeumann.Rep.Dimension
import Submission.Work.Rep.exists_rangeProjection
import Submission.Work.ORVonNeumann.Rep.vnCore
import Submission.Work.ORVonNeumann.Rep.vnRankFunction

namespace Work.ORVonNeumann.Rep

theorem rank_vonNeumann {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] : ∃ rk : Work.ORVonNeumann.SylvesterRankFunction (↥(Work.ORVonNeumann.groupVonNeumann G)), rk.Faithful :=
  ⟨vnRankFunction (G := G), vnRankFunction_faithful (G := G)⟩

end Work.ORVonNeumann.Rep
