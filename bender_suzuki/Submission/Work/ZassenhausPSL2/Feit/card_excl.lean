import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.CharCore.Defs
import Submission.Work.Induction.Defs
import Submission.Work.ThmG.sum_deg_sq_excludingKernel
import Submission.Work.ThmF.Setup
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q
import Submission.Work.FeitSibley.CharQ.scriptS_vanish
import Submission.Work.CharCore.irrDeg_eq_one_of_commutative
import Submission.Work.Induction.indFun_apply_one
import Submission.Work.ZassenhausPSL2.Feit.excl_aux
import Submission.Work.ZassenhausPSL2.Feit.excl_degree_support

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausPSL2.Feit.card_excl`: the order of `𝒮 = excludingKernel H Q`

In a split rank-one Zassenhaus configuration `(H, Q, t)` with `Q` an abelian `2`-group and
`d = |D|`, `D = twoPoint H t = H ∩ Hᵗ`, the set `𝒮 = {χ ∈ Irr H | Q ⊄ ker χ}` of irreducible
characters of `H` which are non-trivial on `Q` satisfies

`|𝒮| · d = |Q| - 1`.

This is Peterfalvi II, Appendice XII (3)–(4) — the statement `F2b` of the design file
`Submission/Work/ZassenhausPSL2/_design/PSL2Core.lean`; it is the `k = (m-1)/d` of the area
notes, with `m = |Q|`, `d = |D|`.

## The argument

Three inputs suffice:

* **the degree count** `Work.ThmG.sum_deg_sq_excludingKernel`: for *any* normal `Q ≤ H`,
  `∑_{χ ∈ 𝒮} χ(1)² = |H| - [H : Q]` (the irreducible characters of `H/Q` contribute `[H : Q]`
  to `∑_{χ ∈ Irr H} χ(1)² = |H|`, by `Work.CohApps.sum_irr_deg_sq_le_ker`);
* **the degree of a member of `𝒮` is `d`** (`deg_excl` below): each `χ ∈ 𝒮` is induced from a
  non-trivial irreducible character of `Q` (`excl_induced`, Clifford theory for the normal
  abelian subgroup `Q ◁ H` whose complement `D` acts fixed point freely on `Q#`), so
  `χ(1) = [H : Q] · 1 = d` because `Q` is abelian;
* **`|H| = |Q| · d`** and **`[H : Q] = d`** (`Work.ThmF.split_card_H`, `index_subgroupOf_Q`).

Then `|𝒮| · d² = |Q| · d - d = (|Q| - 1) · d`, and cancelling the non-zero `d` gives the claim.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical
open Submission.Blueprint

namespace Work.ZassenhausPSL2.Feit

variable {G : Type} [Group G] [Fintype G]
variable {H Q : Subgroup G} {t : G}

/-- **The arithmetic core.**  Given that every `χ ∈ 𝒮 = excludingKernel H Q` has degree `d`,
the degree count of `Work.ThmG.sum_deg_sq_excludingKernel` gives `|𝒮| · d = |Q| - 1`. -/
theorem card_excl_of_deg (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (hab : IsAbelianSubgroup Q)
    (hdeg : ∀ χ ∈ excludingKernel H Q,
      Work.CharCore.irrDeg χ = Nat.card (twoPoint H t)) :
    (excludingKernel H Q).card * Nat.card (twoPoint H t) = Nat.card Q - 1 := by
  have hQn : (Q.subgroupOf H).Normal := qSubgroupOf_normal h
  -- the degree count over `𝒮`, with every degree replaced by `d`
  have hsum := Work.ThmG.sum_deg_sq_excludingKernel (G := G) (H := H) Q h.le hQn
  have hstep : ((excludingKernel H Q).card : ℝ) * (Nat.card (twoPoint H t) : ℝ) ^ 2
      = (Nat.card H : ℝ) - ((Q.subgroupOf H).index : ℝ) := by
    rw [← hsum]
    rw [Finset.sum_congr rfl (fun χ hχ => by rw [hdeg χ hχ])]
    simp [Finset.sum_const, nsmul_eq_mul]
  -- `|H| = |Q| · d` and `[H : Q] = d`
  have h1 : ((excludingKernel H Q).card : ℝ) * (Nat.card (twoPoint H t) : ℝ) ^ 2
      = (Nat.card Q : ℝ) * (Nat.card (twoPoint H t) : ℝ)
        - (Nat.card (twoPoint H t) : ℝ) := by
    rw [hstep, Work.ThmF.split_card_H h, Nat.cast_mul, index_subgroupOf_Q h]
  have hkey : (((excludingKernel H Q).card * Nat.card (twoPoint H t) : ℕ) : ℝ)
      * (Nat.card (twoPoint H t) : ℝ)
      = ((Nat.card Q - 1 : ℕ) : ℝ) * (Nat.card (twoPoint H t) : ℝ) := by
    have hm : (1 : ℕ) ≤ Nat.card Q := Nat.card_pos
    have h2 : (((excludingKernel H Q).card * Nat.card (twoPoint H t) : ℕ) : ℝ)
        = ((excludingKernel H Q).card : ℝ) * (Nat.card (twoPoint H t) : ℝ) := by
      rw [Nat.cast_mul]
    rw [h2, Nat.cast_sub hm, Nat.cast_one]
    nlinarith [h1]
  -- cancel the non-zero factor `d`
  have hdne : (Nat.card (twoPoint H t) : ℝ) ≠ 0 := by
    have h : Nat.card (twoPoint H t) ≠ 0 := Nat.card_pos.ne'
    exact_mod_cast h
  have hcast : (((excludingKernel H Q).card * Nat.card (twoPoint H t) : ℕ) : ℝ)
      = ((Nat.card Q - 1 : ℕ) : ℝ) := mul_right_cancel₀ hdne hkey
  exact Nat.cast_injective hcast

/-- **The degree of a member of `𝒮`, from the Clifford-theoretic extraction.**  If every
`χ ∈ 𝒮 = excludingKernel H Q` is `Ind_Q^H θ` for a non-trivial irreducible `θ` of `Q` (the
statement `excl_induced`), then `χ(1) = [H : Q] · 1 = d` because `Q` is abelian, i.e.
`d = |D|`, `D = twoPoint H t`. -/
theorem deg_excl_of_induced (h : IsSplitRankOne H Q t) (hab : IsAbelianSubgroup Q)
    (hind : ∀ χ ∈ excludingKernel H Q, ∃ θ : ↥(Q.subgroupOf H) → ℂ,
      θ ∈ Work.CharCore.Irr ↥(Q.subgroupOf H) ∧
      (∃ y : ↥(Q.subgroupOf H), θ y ≠ θ 1) ∧
      χ = Work.Induction.indFun (Q.subgroupOf H) θ)
    {χ : H → ℂ} (hχ : χ ∈ excludingKernel H Q) :
    Work.CharCore.irrDeg χ = Nat.card (twoPoint H t) := by
  obtain ⟨θ, hθIrr, -, hχeq⟩ := hind χ hχ
  have hχIrr : χ ∈ Work.CharCore.Irr H := (mem_excludingKernel_iff.mp hχ).1
  have hdegθ : Work.CharCore.irrDeg θ = 1 := irrDeg_eq_one_of_mem_Qsub (hab := hab) hθIrr
  have h1 : (Work.CharCore.irrDeg χ : ℂ) = (Nat.card (twoPoint H t) : ℂ) := by
    rw [← Work.CharCore.irrDeg_spec hχIrr, hχeq, Work.Induction.indFun_apply_one,
      Work.CharCore.irrDeg_spec hθIrr, hdegθ, index_subgroupOf_Q h]
    simp
  exact Nat.cast_injective h1

/-- **The degree of a member of `𝒮`.**  `𝒮 = excludingKernel H Q` consists of irreducible
characters of `H` non-trivial on `Q`; by `Work.ZassenhausPSL2.Feit.excl_degree_support` (F2a of
the design file) each of them has degree `|D|`, `D = twoPoint H t`. -/
theorem deg_excl (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (hab : IsAbelianSubgroup Q) {χ : H → ℂ} (hχ : χ ∈ excludingKernel H Q) :
    Work.CharCore.irrDeg χ = Nat.card (twoPoint H t) := by
  have hχIrr : χ ∈ Work.CharCore.Irr H := (mem_excludingKernel_iff.mp hχ).1
  have h1 : (Work.CharCore.irrDeg χ : ℂ) = (Nat.card (twoPoint H t) : ℂ) := by
    rw [← Work.CharCore.irrDeg_spec hχIrr]
    exact (excl_degree_support h hz h2 hab hχ).1
  exact Nat.cast_injective h1

/-- **The order of `𝒮 = excludingKernel H Q`** (Peterfalvi II, Appendice XII (3)–(4)):
`|𝒮| · |D| = |Q| - 1` in a split rank-one Zassenhaus configuration with abelian `Q`. -/
theorem card_excl {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : Submission.Blueprint.IsAbelianSubgroup Q) :
    (Submission.Blueprint.excludingKernel H Q).card * Nat.card (Submission.Blueprint.twoPoint H t)
      = Nat.card Q - 1 :=
  card_excl_of_deg h hz h2 hab (fun χ hχ => deg_excl h hz h2 hab hχ)

end Work.ZassenhausPSL2.Feit
