import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.twoPoint_comm
import Submission.Work.ZassenhausSuzuki.exists_conjAction
import Submission.Work.ZassenhausSuzuki.QSZ_fpf_conj_action
import Submission.Work.ZassenhausSuzuki.QSZ_abelian_fpf_isCyclic
import Submission.Work.ZassenhausPSL2.Feit.qomegaData_nonempty
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q
import Submission.Work.Frobenius.Complement.isPGroup_abelian_fpf_isCyclic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `D = H ∩ Hᵗ` is cyclic in a Zassenhaus split rank-one configuration with `Q` a 2-group

Suzuki 1962, *On a class of doubly transitive groups*, Propositions 2 and 3
(`REFS/vision/suzuki1962/p0004.md`, `p0005.md`).

Let `G` be doubly transitive on `Ω = G ⧸ H` (`IsSplitRankOne.twoTransitive`), `H = Q ⋊ D`
with `Q ⊴ H` regular on `Ω ∖ {∞}` and `D = twoPoint H t = H ∩ Hᵗ` the two-point stabiliser,
and assume that no non-identity element fixes three distinct points of `Ω`
(`IsZassenhaus H`, i.e. the Zassenhaus condition `V = C_D(t) = 1`).

* **Suzuki, Prop. 2.** every `d ≠ 1` in `D` has no non-trivial fixed point on `Q`.  This is
  `QSZ_fpf_conj_action`: the conjugation action `ρ : D →* MulAut Q` of `D` on `Q`
  (`exists_conjAction`) is fixed-point-free.  In particular `|D|` divides `|Q| - 1`, so the
  order of `D` is odd.
* **Suzuki, Prop. 3.** `D` is cyclic.  Since `t` inverts `D` (`twoPoint_inverted`), `D` is
  abelian (`twoPoint_comm`); and every Sylow subgroup `P ≤ D` is an abelian `p`-group acting
  fixed-point-freely on the non-trivial group `Q`, hence cyclic by
  `Work.Frobenius.Complement.isPGroup_abelian_fpf_isCyclic`.  A finite abelian group all of
  whose Sylow subgroups are cyclic is cyclic (`IsZGroup` together with nilpotency, Mathlib's
  `IsZGroup`-instance) — this is the general statement `QSZ_abelian_fpf_isCyclic`.
-/

set_option linter.style.haveILetI false

open Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-- **The two-point stabiliser of a Zassenhaus split rank-one configuration with a `2`-group
root group is cyclic** (Suzuki 1962, Prop. 3). -/
theorem QSZ_isCyclic_twoPoint {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) :
    IsCyclic ↥(Submission.Blueprint.twoPoint H t) := by
  -- `Q` is non-trivial, so `N = ↥Q` is a non-trivial group on which `D = twoPoint H t` acts.
  have hQne : Q ≠ ⊥ := Work.ZassenhausPSL2.Feit.Q_ne_bot_of_split h
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  -- `t` inverts `D`, hence `D` is abelian.
  haveI : IsMulCommutative ↥(Submission.Blueprint.twoPoint H t) :=
    isMulCommutative_iff.mpr (fun a b =>
      Subtype.ext (twoPoint_comm h hZ hQne h2 (a : G) a.2 (b : G) b.2))
  -- the fixed-point-free conjugation action of `D` on `Q` (Suzuki, Prop. 2)
  obtain ⟨ρ, _hρ, hfpf⟩ := QSZ_fpf_conj_action h hZ
  -- an abelian group acting fixed-point-freely on a non-trivial group is cyclic (Suzuki, Prop. 3)
  exact QSZ_abelian_fpf_isCyclic ρ hfpf

end Work.ZassenhausSuzuki
