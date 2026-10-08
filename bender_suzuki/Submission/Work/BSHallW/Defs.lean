import Mathlib
import Submission.Work.ThmF.Tools.External

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSHallW.Defs` — the corrected Hall–Wielandt input (odd `p`)

`Work.ThmF.HallWielandtProp` (*M. Hall*, §14.4, Theorem 14.4.2, as transcribed for the ThmF chain)
is **false at `p = 2`**: in `G = PSL(2,7)` with Sylow `2`-subgroup `S ≅ D₈`, the subgroup
`A = C₄ ≤ S` is abelian and weakly closed in `S`, `G` has no normal subgroup of index `2`, but
`N_G(A) ≅ S₄` does (GAP check `Submission/Work/_audit/hw_cex.g` / `.out`; audit item **D2** of
`Submission/Work/_audit/AUDIT_bs_chain_1008.md`).  The reason is that Theorem 14.4.2's condition 2),
`e_{p-1}(u,z) = 1` for `u, z ∈ Q₁`, is *implied by* `Q₁` abelian only because `p - 1 ≥ 2`, i.e.
only for odd `p`.

This file therefore records the honest statement: `HallWielandtOddProp` is
`Work.ThmF.HallWielandtProp` with the extra hypothesis `p ≠ 2`.  Everything else (the convention
for `HasNormalIndexP`, the weak-closure hypothesis, the elementwise abelian hypothesis) is
identical, so that a caller can move between the two statements with a single extra argument.

Main declarations of the area:

* `Work.BSHallW.HallWielandtOddProp` — the corrected input;
* `Work.BSHallW.hallWielandtOdd` (`Submission/Work/BSHallW/Main.lean`) — **its proof**, from the
  delivered `Work.Grun.hall_14_4_1` (P. Hall's Theorem 14.4.1);
* `Work.BSHallW.hallWielandtOdd_of` — the corollary form with `[Fact p.Prime]`, mirroring
  `Work.ThmF.hallWielandt_of_external`;
* `Work.BSHallW.HallWielandtOddProp_of_prop` — the (trivial) implication from the uncorrected
  `Work.ThmF.HallWielandtProp` (so the corrected input is *weaker*: every consumer of
  `Work.ThmF.HallWielandtProp` that only uses odd `p` may be re-pointed at
  `HallWielandtOddProp`);
* `Work.BSHallW.ThmF16Odd.thmF16'` (`Submission/Work/BSHallW/ThmF16Odd.lean`) — the ThmF §3 chain
  re-assembled with `HallWielandtOddProp` in place of `Work.ThmF.HallWielandtProp`.
-/

set_option autoImplicit false

namespace Work.BSHallW

/-- **M. Hall §14.4, Theorem 14.4.2 (Hall–Wielandt), correct form: `p` odd.**

Let `S` be a Sylow `p`-subgroup of a finite group `G`, `p ≠ 2` a prime, and `A ≤ S` a subgroup that
is weakly closed in `S` with respect to `G` (`A^g ≤ S ⟹ A^g = A`).  If `A` is abelian, then
`G/O^p(G) ≅ N_G(A)/O^p(N_G(A))`; equivalently `G` has a normal subgroup of index `p` if and only
if `N_G(A)` does.

This is `Work.ThmF.HallWielandtProp` with the additional hypothesis `p ≠ 2` (which is necessary:
the statement fails at `p = 2`, see the module docstring). -/
def HallWielandtOddProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ (S : Sylow p G) (A : Subgroup G), A ≤ (S : Subgroup G) →
      (∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
        A.map (MulAut.conj g).toMonoidHom = A) →
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      (Work.ThmF.HasNormalIndexP p G ↔
        Work.ThmF.HasNormalIndexP p ↥(Subgroup.normalizer (A : Set G)))

/-- The corrected statement is *weaker* than the uncorrected one:
`Work.ThmF.HallWielandtProp` implies `HallWielandtOddProp`.  (This is the only implication that
holds; the reverse fails at `p = 2`.) -/
theorem HallWielandtOddProp_of_prop (h : Work.ThmF.HallWielandtProp) :
    HallWielandtOddProp :=
  fun G _ _ p hp _ => h G p hp

/-- `HallWielandtOddProp` in the argument order of `Work.ThmF.HallWielandtProp`, with `p ≠ 2`
inserted directly after `p.Prime` and before the Sylow subgroup. -/
theorem hallWielandtOdd_apply (h : HallWielandtOddProp) (G : Type) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (S : Sylow p G) (A : Subgroup G)
    (hA : A ≤ (S : Subgroup G))
    (hwc : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
      A.map (MulAut.conj g).toMonoidHom = A)
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Work.ThmF.HasNormalIndexP p G ↔
      Work.ThmF.HasNormalIndexP p ↥(Subgroup.normalizer (A : Set G)) :=
  h G p hp hp2 S A hA hwc hab

/-- The corollary form of the corrected Hall–Wielandt input, mirroring
`Work.ThmF.hallWielandt_of_external`: the `p.Prime` hypothesis is an instance argument. -/
theorem hallWielandtOdd_of (h : HallWielandtOddProp) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Sylow p G) (A : Subgroup G)
    (hA : A ≤ (S : Subgroup G))
    (hwc : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
      A.map (MulAut.conj g).toMonoidHom = A)
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Work.ThmF.HasNormalIndexP p G ↔
      Work.ThmF.HasNormalIndexP p ↥(Subgroup.normalizer (A : Set G)) :=
  h G p Fact.out hp2 S A hA hwc hab

end Work.BSHallW
