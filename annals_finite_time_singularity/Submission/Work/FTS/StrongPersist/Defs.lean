/-
# `Work.FTS.StrongPersist` — the strong-solution route, nodes S2 and S6 of the design

Design: `Submission/Work/FTS/FTS_STRONG_ROUTE.md` §3 (table S1–S6) and §1 (`RegPkgMin`).

The IP₄-Galerkin limit of the Open2/Open3 chain cannot be shown to have the regularity the
downstream nodes need (design §3, obstructions 1–3).  The replacement route is the
*strong-solution* route: local existence in `ℋ⁶` (S1), persistence of `ℋ⁶` from the a-priori
`ℋ⁴` bound (S2), an interior Sobolev embedding (S3), the a-priori bootstrap (S4), continuation
(S5) and the `ℋ³` bound on `∂_τ g` (S6).

**This chapter owns S2 and S6.**  It fixes:

* the level-six norm `Xn6`, the level-six inner product `IP6` (the paper's recursion
  `IP^{k+1} = HkIPStep c₁ c₂ IP^k` applied twice on top of the `ℋ⁴` inner product
  `CoercivityFix.Assembly.IP4` of the coercivity chapter) and the linear part `linPart` of the
  fake-time equation;
* the strong-solution predicate `IsStrongSolOn` on a half-open fake-time interval `[0,T)`,
  with the corrected elliptic law `IsBslSolPos` of design §1/§4 (the boundary conditions only
  for `z ≥ 0`);
* the regularity packages `RegPkgMin` (copied **verbatim** from design §1) and `RegPkgH6`;
* the **k = 6 restatements of the interface clauses** consumed by the S2 Grönwall argument:
  the `ℋ⁶` product/`L₁₂` clauses (`N6Norm`), the transport clauses T1/T2/T3 at level six
  (`N6Trans`), the level-six inner-product package (`H6Coer`), the one-sided bound for the
  linear part (`H6Lin`), the level-six pairing bound for the nonlinear right-hand side
  (`H6Pair`) and the level-six energy identity (`H6EnergyDeriv`);
* the level-three operator package `L3Data` of S6.

## Layout (files, and what to import)

The chapter is split so that no file is large; the vocabulary and the clause packages live in
two modules and `Defs` is their aggregator (it carries no declaration of its own):

```lean
import Submission.Work.FTS.StrongPersist.Defs        -- = Vocab + Clauses (the aggregator)
import Submission.Work.FTS.StrongPersist.Vocab       -- vocabulary: Xn6, IP6, H6Adm, RegPkgMin, …
import Submission.Work.FTS.StrongPersist.Clauses     -- the clause packages: N6Norm, H6Coer, …
import Submission.Work.FTS.StrongPersist.Basic       -- + the elementary API and the bridges
import Submission.Work.FTS.StrongPersist.Persist     -- S2: persist_H6, persist_H6_apriori
import Submission.Work.FTS.StrongPersist.Dbd         -- S6: dbd_of_eq, dbd_of_eq_gdt
import Submission.Work.FTS.StrongPersist.IP6Clauses  -- the structural clauses of the concrete IP6
import Submission.Work.FTS.StrongPersist.H6CoerAssembly -- H6Coer for IP6, and the S2 specialisations
import Submission.Work.FTS.StrongPersist.EnergyStep  -- the energy-derivative recursion step
import Submission.Work.FTS.StrongPersist.EnergyIter  -- the energy identity of IP6 from slot facts
```

The clause packages are *interfaces*: they are the level-six analogues of the level-four
clauses `OpenPkg.N4Norm'`, `VocabO.T2Clause`, `VocabO.T3Clause` and `CoercivityStep.IsHkIP`.
The theorems of `Persist` and `Dbd` are proved *from* them.
-/
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.StrongPersist.Clauses

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
