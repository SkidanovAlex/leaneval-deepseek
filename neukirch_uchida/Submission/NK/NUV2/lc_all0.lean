import Mathlib
import Submission.NK.NUV2.Wall
import Submission.NK.NUV2.LC.lc_of_pdg
import Submission.NK.NUV2.LC.pdg_of_leaves
import Submission.NK.NUV2.LC.RouteB.decompContainment_B
import Submission.NK.NUV2.LC.decompContinuousIso
import Submission.NK.NUV2.LC.localArithInvariants

/-! Guidance from the project lead (the requester):

## Context (orchestrator, 2026-09-23)
The old wall `NK.EndgameRepair.ClassicalChaptersRepaired` is UNSATISFIABLE — do not use it or any of its fields'
catalogues as targets: `IndecomposedDeep.DeepInputs.indexOne` fails (quartic K with 2 = 𝔭₁𝔭₂³, K_{𝔭₂} ≅ ℚ₂(∛2):
G_{ℚ₂(∛2)} ≤ D_A is self-normalising, ≅ a local Galois group, of index 3), and `TowerRankCore.finiteIndex_isClosed`
is false without `FiniteDimensional κ M`. Also avoid `LocalStructure.LocalNUExistence` (G_M ≅ G_κ ⇒ M ≅ κ is false,
Yamagata/Jarden–Ritter), `UchidaKummer.IsWeakUchida`, `CyclicPrimeReduction`.
The new wall is `NK.NUV2.ChaptersV2` (`Submission/Work/NUV2/Wall.lean`, do NOT edit): the four inputs of the proved
`NK.EndgameRepair.exists_sigma_of_correctedResiduals`. Library inputs being proved elsewhere in this workspace and
allowed as hypotheses where the statement has them: `NK.GlobalCFTdeep.FundamentalClassElement` (global
fundamental class ⇒ class-formation axioms, reciprocity C_K/N C_L ≅ Gal(L/K)ᵃᵇ via
`artinReciprocity_of_cohomologicalFieldAxiom`, Tate's theorem, Albert–Brauer–Hasse–Noether) and
`NK.LocalArtin.KernelCondition` at every completion (⇒ `NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion`).
Design rules: state every local isomorphism as a CONTINUOUS isomorphism (ϕ is a homeomorphism; this removes
Nikolov–Segal entirely); for Brauer arguments use an ODD prime p (Br(ℝ)[p] = 0). Instantiate every new sub-statement
at K = ℚ and at the quartic above as a satisfiability check before relying on it. Delegate; one lemma per step.
## This lemma: the place correspondence (NSW 12.1.9 + local invariants), leaves
1. DecompContainment: a closed subgroup H ≤ G_K topologically isomorphic to Gal(L_𝔮^sep/L_𝔮) for some number field
   L and finite place 𝔮 lies in some decomposition group D_A. Proof: open U with μ_p (p odd) on both sides;
   H²(U∩H-level, ℤ/p) ≅ ℤ/p transported (proved: `LocalCFT.Brauer.exists_ne_zero_H2Profinite_of_mulEquiv`); ABHN
   injectivity gives a nonzero local component; ABHN surjectivity rules out two places; conjugation gives H ≤ D_A.
2. ABHN for odd p (from `hFC`): H²(G_F, μ_p) → ∏_{finite v} H²(G_{F_v}, μ_p) injective, and surjective onto ⊕_S for
   finite S missing some place; colimit form for algebraic extensions (reuse `HasseTwist` `H2Twist`/`loc`).
   Injectivity alone needs only H¹(G,C_L)=0 (`H1All`) + Shapiro; surjectivity needs Σ inv = 0 (from hFC).
3. Local Brauer: H²(G_λ, μ_p) ≃ ZMod p for p-adic λ ⊇ μ_p (`BrauerTwist.LocalFieldBrauerCyclic`, `LocalCFT/Brauer/`).
4. DecompDisjoint: proved, `stabSubgroup_inf_eq_bot_of_ne`.
5. D_A ≃ₜ* Gal(K_𝔭^sep/K_𝔭) (upgrade `nonempty_mulEquiv_decompositionGroupOf_localGalois` to continuous).
   Glue G1: 1+4+5 ⇒ ϕ maps decomposition groups to decomposition groups bijectively.
6. Continuous iso of local Galois groups ⇒ equal residue characteristic and local degree (read off G^ab ≅ (κ^×)^ via
   local CFT: p = the unique ℓ with a ℤ_ℓ² quotient, degree = ℤ_p-rank − 1). Feeds
   `LocalInputs.residueChar_and_localDegree_eq_of_decompositionGroup`, `Mine.localCorrespondence_of_localData`.
   Glue G2: `LocalCorrespondence ϕ`.
Hardest: leaf 1 (colimit cohomology over infinite algebraic fixed fields; choice of the open subgroup).

UNIVERSES: everything is in `Type 0`, matching the hypotheses. Missing mathematics is NOT a reason to stop: build it (delegate). Use declare_false only for a statement that is actually false, with a counterexample.
-/

namespace NK.NUV2

/-! ## The assembly of the place correspondence from the leaves of `NUV2/LC/`

The project lead split `NK.NUV2.LCAll0` into the parallel leaves

* `NK.NUV2.LC.RouteB.decompContainment_B` — Neukirch's containment (NSW (12.1.9), hard half),
  the re-planned non-circular owner of `NK.NUV2.DecompContainment`; the ABHN statement it consumes is
  `NK.NUV2.ABHNInjectivity` / `NK.NUV2.ABHNSurjectivity` (`Submission/Work/NUV2/ABHN/Basic.lean`),
  proved in `Submission/Work/NUV2/ABHN/`;
* `NK.NUV2.LC.decompContinuousIso` — leaf 5;
* `NK.NUV2.LC.localArithInvariants` — leaf 6, from `hKC` (local CFT at every completion);
* `NK.NUV2.LC.pdg_of_leaves` — glue G1 (containment + disjointness + leaf 5);
* `NK.NUV2.LC.lc_of_pdg` — glue G2 (the place correspondence from G1 + leaf 6).

The theorem below is the assembly prescribed by the lead:
`lc_of_pdg (pdg_of_leaves (decompContainment hFC hKC) decompContinuousIso) (localArithInvariants hKC) hKC`.
It is `sorry`-free in *this* file; the leaves live in their own modules. -/

theorem lc_all0 (hFC : NK.GlobalCFTdeep.FundamentalClassElement) (hKC : NK.NUV2.KCAll) : NK.NUV2.LCAll0 :=
  NK.NUV2.LC.lc_of_pdg
    (NK.NUV2.LC.pdg_of_leaves (NK.NUV2.LC.RouteB.decompContainment_B hFC hKC)
      NK.NUV2.LC.decompContinuousIso)
    (NK.NUV2.LC.localArithInvariants hKC) hKC

end NK.NUV2
