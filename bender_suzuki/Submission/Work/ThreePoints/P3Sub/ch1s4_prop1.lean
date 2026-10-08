import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.ThreePoints.P3Sub.ch1s4_transfer
import Submission.Work.ThreePoints.P3Sub.ch1s4_orbit
import Submission.Work.ThreePoints.P3Sub.ch1s4_count
import Submission.Work.DoubleTransitivity.Sec4.lemma2_part1
import Submission.Work.DoubleTransitivity.Sec4.rp_no_two_fixed_pts
import Submission.Work.DoubleTransitivity.Sec4.not_rp_twoTransitive

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi I, Ch. I §4 Prop. 1, in the form used by Ch. II §4 Prop. 3 (a)

`H` is strongly embedded in the finite group `G`, `X ≤ H`, `N ≤ N_G(X)`, and `N ⊓ H` is strongly
embedded in `N`.  If some `p`-subgroup `P ≤ N` (`p ≠ 2` prime) has exactly two fixed points on
`Ω_X = fixedPts H X`, then `N` acts `2`-transitively on `Ω_X`.

The three inputs are

* `Work.ThreePoints.P3Sub.ch1s4_orbit` — `Ω_X` is the `N`-orbit of `H` (Ch. I §2 Lemma 2 applied
  with `F = N`, using `hInv` and `heven` to make `|N ⊓ H^g|` even for every `H^g ∈ Ω_X`);
* `Work.ThreePoints.P3Sub.ch1s4_count` — the `N`-equivariant bijection
  `↥N ⧸ (N ⊓ H) ≃ Ω_X`, `n(N ⊓ H) ↦ n • (1 : G ⧸ H)` turns `hfix` into "some `p`-subgroup of
  `↥N` has exactly two fixed points on `↥N ⧸ (N ⊓ H)`";
* `Work.ThreePoints.P3Sub.ch1s4_transfer` — Ch. I §4 Prop. 1 gives `2`-transitivity of `N` on
  `↥N ⧸ (N ⊓ H)` (`Work.DoubleTransitivity.Sec4.not_rp_twoTransitive`, fed by Ch. I §4 Lemma 2
  `Sec4.lemma2_part1` and `Sec4.rp_no_two_fixed_pts`), and the orbit bijection transfers it to
  `Ω_X`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints.P3Sub

open Submission.Blueprint

/-- Ch. I §4 Prop. 1 (b) ⇒ (a): a `p`-subgroup with exactly two fixed points forces
`2`-transitivity.  This combines the contrapositive of Ch. I §4 Prop. 1 (b) (`𝓡_p ≠ ∅` implies
that no `p`-subgroup fixes exactly two points, `Sec4.rp_no_two_fixed_pts`) with Ch. I §4 Prop. 1
(a) (`¬ 𝓡_p` implies `2`-transitivity, `Sec4.not_rp_twoTransitive`). -/
theorem twoTransitive_of_two_fixed_pts {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hT : ∃ T : Subgroup G, IsPGroup p T ∧
      (Submission.Blueprint.fixedPts H T).ncard = 2) :
    MulAction.IsMultiplyPretransitive G (Work.DoubleTransitivity.Omega H) 2 := by
  obtain ⟨T, hTp, hT2⟩ := hT
  have h1 : Work.DoubleTransitivity.Sec4.Sec4Lemma2Part1 p H :=
    Work.DoubleTransitivity.Sec4.lemma2_part1 hBrSz hH hp hp2
  have hnrp : ¬ Work.DoubleTransitivity.Sec4.Rp p H :=
    fun hRp =>
      Work.DoubleTransitivity.Sec4.rp_no_two_fixed_pts hBrSz hH hp hp2 h1 hRp T hTp hT2
  exact Work.DoubleTransitivity.Sec4.not_rp_twoTransitive hBrSz hH hp hp2 h1 hnrp

theorem ch1s4_prop1 {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {X N : Subgroup G} (hXH : X ≤ H)
    (hNN : N ≤ Subgroup.normalizer (X : Set G))
    (hInv : Submission.Blueprint.involutions (Subgroup.centralizer (X : Set G) : Set G) ⊆ N)
    (heven : ∀ M : Subgroup G, (∃ g : G, M = Submission.Blueprint.conj g H) → X ≤ M →
      Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)))
    (hSE : LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((N ⊓ H).subgroupOf N))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G} (hPN : P ≤ N) (hP : IsPGroup p P)
    (hfix : (Submission.Blueprint.fixedPts H P ∩ Submission.Blueprint.fixedPts H X).ncard = 2) :
    Work.DoubleTransitivity.IsTwoTransitiveOnSub N (Submission.Blueprint.fixedPts H X) := by
  -- `Ω_X` is the `N`-orbit of `H`
  have htrans := ch1s4_orbit hH hXH hNN hInv heven hSE
  -- the `p`-subgroup `P ≤ N` has exactly two fixed points on `↥N ⧸ (N ⊓ H)`
  have hcount := ch1s4_count hXH hNN hPN htrans
  have hTp : IsPGroup p (P.subgroupOf N) :=
    hP.comap_of_injective N.subtype Subtype.coe_injective
  -- Ch. I §4 Prop. 1: `N` is `2`-transitive on `↥N ⧸ (N ⊓ H)`
  have h2 : MulAction.IsMultiplyPretransitive ↥N (↥N ⧸ (N ⊓ H).subgroupOf N) 2 :=
    twoTransitive_of_two_fixed_pts hBrSz hSE hp hp2
      ⟨P.subgroupOf N, hTp, hcount.trans hfix⟩
  -- transfer to `Ω_X`
  exact ch1s4_transfer (H := H) (L := N) (S := Submission.Blueprint.fixedPts H X) h2
    ((Work.DoubleTransitivity.pt_mem_fixedPts_iff X H).mpr hXH)
    (fun l ω hω => ch1s4_count_aux (hNN l.2) hω)
    htrans

end Work.ThreePoints.P3Sub
