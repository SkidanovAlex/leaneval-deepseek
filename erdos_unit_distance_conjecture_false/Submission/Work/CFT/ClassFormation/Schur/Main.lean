import Mathlib
import Submission.Work.CFT.ClassFormation.Defs
import Submission.Work.CFT.ClassFormation.Schur.finrank_groupCohomology_eq_finrank_groupHomology
import Submission.Work.CFT.ClassFormation.Schur.finrank_homology_fp_eq
import Submission.Work.CFT.ClassFormation.Schur.dim_H1_eq_rankP_H1
import Submission.Work.CFT.ClassFormation.Schur.finite_HnZ
import Submission.Work.CFT.ClassFormation.Schur.TateH2

/-!
# The Schur bridge

For a finite group `G` and a prime `p`, with trivial `𝔽_p` coefficients,

`dim_𝔽_p H²(G, 𝔽_p) = dim_𝔽_p H¹(G, 𝔽_p) + rank_p (H_2(G, ℤ))`,

where `rank_p A = dim_𝔽_p (A ⊗_ℤ 𝔽_p)`.  This turns a bound on the Schur multiplier `H_2(G, ℤ)`
(which class field theory supplies, via `H_2(G, ℤ) ≅ Ĥ^{-1}(G, A)`) into Shafarevich's
relation-rank estimate: `r(G) ≤ d(G) + rank_p H_2(G, ℤ)` with `r(G) = dim H²(G, 𝔽_p)` and
`d(G) = dim H¹(G, 𝔽_p)`.

The proof is the composition of three ingredients:

1. **field duality** `dim H^n(G,𝔽_p) = dim H_n(G,𝔽_p)`
   (`Schur.finrank_groupCohomology_eq_finrank_groupHomology`);
2. the **homology Bockstein** `dim H_2(G,𝔽_p) = rank_p H_2(G,ℤ) + rank_p H_1(G,ℤ)`
   (`Schur.finrank_homology_fp_eq`);
3. `dim H¹(G,𝔽_p) = rank_p H_1(G,ℤ)` (`Schur.dim_H1_eq_rankP_H1`).
-/

open scoped TensorProduct

namespace Work.CFT.ClassFormation.Schur

open Work.CFT.ClassFormation

/-- **The Schur bridge (equality form).**  For a finite group `G` and a prime `p`, with trivial
`𝔽_p` coefficients,
`dim_𝔽_p H²(G, 𝔽_p) = dim_𝔽_p H¹(G, 𝔽_p) + rank_p (H_2(G, ℤ))`. -/
theorem schur_bridge (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] :
    Module.finrank (ZMod p) (Work.Tower.Shafarevich.H2Fp p G) =
      Module.finrank (ZMod p) (Work.Tower.Shafarevich.H1Fp p G)
        + rankP p (HnZ G 2 : Type) := by
  rw [finrank_groupCohomology_eq_finrank_groupHomology (ZMod p) G 2,
      finrank_homology_fp_eq p G 2 le_rfl, dim_H1_eq_rankP_H1 p G]
  simp only [Nat.reduceSub, HnHomFp, HnFp]
  omega

/-- **The Schur bridge (inequality form).**  For a finite group `G` and a prime `p`,
`dim_𝔽_p H²(G, 𝔽_p) ≤ dim_𝔽_p H¹(G, 𝔽_p) + rank_p (H_2(G, ℤ))`. -/
theorem schur_bridge_le (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] :
    Module.finrank (ZMod p) (Work.Tower.Shafarevich.H2Fp p G) ≤
      Module.finrank (ZMod p) (Work.Tower.Shafarevich.H1Fp p G)
        + rankP p (HnZ G 2 : Type) :=
  le_of_eq (schur_bridge p G)

/-- **Shafarevich's relation-rank estimate, abstract form.**  The pro-`p` relation rank is bounded
by the pro-`p` generator rank plus the `p`-rank of the Schur multiplier:
`proPRelationRank p G ≤ proPGeneratorRank p G + rank_p H_2(G, ℤ)`. -/
theorem proPRelationRank_le (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] :
    Work.Tower.Shafarevich.proPRelationRank p G ≤
      Work.Tower.Shafarevich.proPGeneratorRank p G + rankP p (HnZ G 2 : Type) :=
  le_of_eq (schur_bridge p G)

/-- **Shafarevich's relation-rank estimate from a bound on the Schur multiplier.**  If
`rank_p H_2(G, ℤ) ≤ C` then `proPRelationRank p G ≤ proPGeneratorRank p G + C`. -/
theorem proPRelationRank_le_of_rankP_le (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    {C : ℕ} (hC : rankP p (HnZ G 2 : Type) ≤ C) :
    Work.Tower.Shafarevich.proPRelationRank p G ≤
      Work.Tower.Shafarevich.proPGeneratorRank p G + C :=
  le_trans (proPRelationRank_le p G) (Nat.add_le_add_left hC _)

end Work.CFT.ClassFormation.Schur
