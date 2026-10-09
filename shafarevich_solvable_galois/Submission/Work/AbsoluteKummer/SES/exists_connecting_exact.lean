/-
Copyright (c) 2025. All rights reserved.

# The connecting map `H⁰(G,P) → H¹(G,M)` of a short exact sequence of discrete modules

For a short exact sequence `0 → M --ι--> N --π--> P → 0` of discrete `G`-modules, there is a
connecting homomorphism `δ : H⁰(G,P) → H¹(G,M)` of the long exact sequence in continuous
cohomology, exact at `H⁰(G,P)` and at `H¹(G,M)`:

`range (H⁰(π)) = ker δ` and `range δ = ker (H¹(ι))`.

The connecting map itself, together with the two inclusions proved here, are built in
`Submission/Work/AbsoluteKummer/SES/Connecting.lean`
(`Work.AbsoluteKummer.ShortExactSeq.delta`, `S.range_mapH0_le_ker_delta`,
`S.range_delta_le_ker_mapH1`); the two reverse inclusions are
`Work.AbsoluteKummer.SES.ker_le_range_mapH0` and `Work.AbsoluteKummer.SES.ker_mapH1_le_range_delta`.
-/
import Mathlib
import Submission.Work.AbsoluteKummer.SES
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.AbsoluteKummer.Defs
import Submission.Work.AbsoluteKummer.SES.Connecting
import Submission.Work.AbsoluteKummer.SES.ker_le_range_mapH0
import Submission.Work.AbsoluteKummer.SES.ker_mapH1_le_range_delta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.SES

theorem exists_connecting_exact {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P] (S : Work.AbsoluteKummer.ShortExactSeq G M N P) : ∃ δ : Work.AbsoluteKummer.H0 G P →+ Work.AbsoluteKummer.H1 G M, (Work.GroupCohomology.mapH0 G S.pi S.pi_equivariant).range = δ.ker ∧ δ.range = (Work.AbsoluteKummer.mapH1 S.iota S.iota_equivariant).ker := by
  refine ⟨S.delta, le_antisymm S.range_mapH0_le_ker_delta (ker_le_range_mapH0 S),
    le_antisymm S.range_delta_le_ker_mapH1 (ker_mapH1_le_range_delta S)⟩

end Work.AbsoluteKummer.SES
