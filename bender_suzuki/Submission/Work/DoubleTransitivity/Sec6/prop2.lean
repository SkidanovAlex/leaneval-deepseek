import Mathlib
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.DoubleTransitivity.Sec4.Defs
import Submission.Work.DoubleTransitivity.Sec5.Defs
import Submission.Work.DoubleTransitivity.Sec6.Defs
import Submission.Work.DoubleTransitivity.Sec6.lemma1
import Submission.Work.DoubleTransitivity.Sec3.prop1
import Submission.Work.DoubleTransitivity.Sec2.prop2
import Submission.Work.DoubleTransitivity.Sec2.prop1a_exists
import Submission.Work.DoubleTransitivity.Sec2.prop1a_unique
import Submission.Work.DoubleTransitivity.Sec1.unique_fixed
import Submission.Work.ThreePoints.S4Prop2.sec3_prop1
import Submission.Work.DoubleTransitivity.Sec6.coprime_generation
import Submission.Work.DoubleTransitivity.Sec6.step1
import Submission.Work.DoubleTransitivity.Sec6.exists_F_case2
import Submission.Work.DoubleTransitivity.Sec6.exists_F_case3

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec6.prop2` — Peterfalvi I Ch. I §6 Proposition 2 (p. 160)

Let `G` be a finite group with a strongly embedded subgroup `H`, `p` an odd prime, `P` a `p`-subgroup
of `G` maximal among those fixing at least three points of `Ω = G ⧸ H` with `P ≤ H`, and
`u ∈ Inv(H)` an involution normalising but not centralising `P`.  Then there is `F ≤ G` such that
`F ∩ H` is a proper Bender (= strongly embedded) subgroup of `F` and, for every involution `s ∈ F`
and every point `ω` of `Ω` fixed by `s`, one has `J(P,u) ⊆ Stab_G(ω)` and
`O_{p'}(H ∩ H^s) ⊆ O_{p'}(Stab_G(ω) ∩ H ∩ H^s)`.

The proof is the source's case split on `C_G(J(P,u))`:  ``C_G(K) ≤ H`` (Step 3, `F = N_G(P)`) or
`C_G(K) ≰ H` (Step 2, `F` of 2-rank 1 inside `C_G(K)⟨u⟩`); the two branches are proved in
`Work.DoubleTransitivity.Sec6.exists_F_case3` resp. `...exists_F_case2`.
-/

namespace Work.DoubleTransitivity.Sec6

theorem prop2 {G : Type} [Group G] [Finite G] (hFT : Submission.Blueprint.FeitThompsonProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : Work.DoubleTransitivity.MaxFixesThree p H P) (hPH : P ≤ H)
    {u : G} (hu : u ∈ Submission.Blueprint.involutions (H : Set G))
    (huN : u ∈ Subgroup.normalizer (P : Set G))
    (hnc : ¬ ∀ x ∈ P, u * x * u⁻¹ = x) :
    ∃ F : Subgroup G,
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((H ⊓ F).subgroupOf F) ∧
      ∀ s ∈ Submission.Blueprint.involutions (F : Set G),
        ∀ ω : Work.DoubleTransitivity.Omega H, (s : G) • ω = ω →
          (∀ k ∈ Submission.Blueprint.invertedBy P u, k • ω = ω) ∧
          Work.DoubleTransitivity.pPrimeCoreSub p (H ⊓ Submission.Blueprint.conj s H) ≤
            Work.DoubleTransitivity.pPrimeCoreSub p
              (MulAction.stabilizer G ω ⊓ H ⊓ Submission.Blueprint.conj s H) := by
  by_cases hC : Subgroup.centralizer
      (Subgroup.closure (Submission.Blueprint.invertedBy P u) : Set G) ≤ H
  · exact exists_F_case3 hFT hBrSz hH hp hp2 hP hPH hu huN hnc hC
  · exact exists_F_case2 hFT hBrSz hH hp hp2 hP hPH hu huN hnc hC

end Work.DoubleTransitivity.Sec6
