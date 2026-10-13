import Submission.Work.DSMap.Mix2
import Submission.Work.DSM4p.Basic
import Submission.Work.DSM4p.Chart

/-!
# DSM4p — the completed levels of the Riemann extension tower

The node `DSMap.Mix2.area_M4p` requires every level of the tower to be a `PerfectoidData`
`p`-ring.  The chart levels `chartRing hgr Q.ϖ n ⊆ B[1/g]` of `DSM4p/Chart.lean` are the
algebraic skeleton (they are `p`-torsion-free and `g ∣ p^n` holds there), but they are not
complete.  This module introduces the candidate levels of the node:

  `chartComp hgr Q n := (chartRing hgr Q.ϖ n) ^` — the `p`-adic completion of the `n`-th chart
  level (`AdicCompletion (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n)`),

together with the `B`-algebra structure and the structure map `chartRing n → chartComp n`
(`AdicCompletion.of` / `algebraMap`).  The tower of completions of the inclusions
`chartLevel (n+1) ≤ chartLevel n` (`AdicCompletion.map`) is the tower of the node.

## The facts about `chartComp`

Proved in this directory (all sorry-free, axiom-clean):

1. `Work.DSM4p.chartComp_isAdicComplete` (`chartComp_isAdicComplete.lean`) —
   `IsAdicComplete (Ideal.span {(p : chartComp hgr Q n)}) (chartComp hgr Q n)`, from
   `AdicCompletion.isAdicComplete_self`;
2. `Work.DSM4p.chartComp_torsionFree` (`chartComp_torsionFree.lean`) —
   `IsSMulRegular (chartComp hgr Q n) (p : chartComp hgr Q n)`, from
   `Work.DSM4p.chartLevel_torsionFree` and the `(p)`-adic completion of a `p`-torsion-free ring;
3. `Work.DSM4p.chartComp_modPow` (`chartComp_modPow.lean`) — the comparison
   `chartComp hgr Q n ⧸ (p)^m ≃+* chartRing hgr Q.ϖ n ⧸ (p)^m`: completion does not change the
   reduction modulo `p ^ m`.  This is the bridge which transports the QRET clauses of the
   chart tower (`Work.DSM4p.ChartCokernel` and the kernel clause) to the completed tower;
4. `Work.DSM4p.chartComp_varpi` (`chartComp_varpi.lean`) — the pseudo-uniformizer data of the
   completed level: `ϖ_k ^ p = ϖ_{k-1}` for the images of `Q.ϖ`, and `ϖ_0 ^ p = p · v` with
   `v` a unit (the image of `PerfectoidData.unit`);
5. `Work.DSM4p.chartLevel_frobenius_surj` (`chartLevel_frobenius_surj.lean`) — Frobenius is
   surjective modulo `p` on the chart level itself (every element of `chartRing hgr Q.ϖ n` is a
   `p`-th power modulo `p`), the input for Frobenius-surjectivity of the completion.

**Design correction (from the project lead, curric-46).**  The route "`chartRing ⧸ p` is
reduced" is *wrong*: for perfectoid `B`, `B ⧸ p` is **not** reduced (`ϖ_0` is nilpotent modulo
`p`), and `chartRing` is the *subring* `B[ϖ_k^n/g_k] ⊆ B[1/g]`, not a localisation.  Bhatt's and
Scholze's chart levels are perfectoid only after taking the **`p`-integral (`p`-root) closure**
inside `B[1/g]` and *then* completing; the `frobInj` (and, relatedly, the kernel clause) must be
proved for that closed-and-completed ring.  A design for both is being written by the lead; the
items below are unaffected in *shape* (they are the fields one has to supply), but item 7 in
particular is expected to need the corrected level ring.

Still to do for the `PerfectoidData p (chartComp hgr Q n)` structure:

6. `frobSurj` for the completion: `∀ x, ∃ y, x - y ^ p ∈ Ideal.span {(p : chartComp …)}` —
   transfer item 5 across the comparison of item 3 at `m = 1`;
7. `frobInj` for the completion: `y ^ p ∈ Ideal.span {(p : chartComp …)} → y ∈ Ideal.span
   {algebraMap B (chartComp …) (Q.ϖ 0)}` — the standard step "Frobenius injective mod `ϖ` from
   the mod-`p` statement plus `p`-adic separatedness" (iterate `y = ϖ_0 y_1 + p y_2` using
   `ϖ_0 ^ p = p v`);
8. the transfer of the QRET clauses and of the divisibility `g ∣ p ^ n` from the chart tower to
   the tower of completions, via item 3 (the transition maps are
   `AdicCompletion.map` of the inclusions `chartLevel (n+1) ≤ chartLevel n`).

With items 1–8 the tower of completed chart levels carries the node's `PerfectoidData`,
divisibility and `IsQRETp` clauses; what remains in addition is the **kernel clause** of the
chart model (`Work.DSM4p.ChartKernel`, see `DSM4p/Main.lean` and `DSM4p/Assembly.lean`), whose
proof needs Bhatt's base-change argument (arXiv:1608.08882, Remark 3.2).

-/

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry IsLocalRing Limits

namespace Work.DSM4p

universe a

open DSMap DSMap.Mix DSMap.Mix2

section Completed

variable {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B] {gr : ℕ → B}
variable (hgr : IsRootSystem p gr) (Q : PerfectoidData p B)

/-- The `n`-th level of the Riemann extension tower: the `p`-adic completion of the `n`-th
chart level `chartRing hgr Q.ϖ n ⊆ B[1/g]`. -/
noncomputable abbrev chartComp (n : ℕ) : Type a :=
  AdicCompletion (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n)

/-- the ring structure on the completed level -/
noncomputable instance (n : ℕ) : CommRing (chartComp hgr Q n) := inferInstance

/-- the `B`-algebra structure on the completed level -/
noncomputable instance (n : ℕ) : Algebra B (chartComp hgr Q n) := inferInstance

end Completed

end Work.DSM4p
