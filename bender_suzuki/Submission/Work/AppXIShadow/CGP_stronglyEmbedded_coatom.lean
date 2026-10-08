import Mathlib
import Submission.Work.AppXIShadow.Basic
import Submission.Work.AppXIShadow.AppII7
import Submission.Work.AppXIShadow.CGP_twoTransitive
import Submission.Work.AppXIShadow.isCoatom_subgroupOf_of_maximal
import Submission.Work.ThreePoints.P3NeBot.maximal_of_twoTransitive
import Submission.Work.ThreePoints.P3NeBot.p3_twoTransitive
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIShadow

open Classical LeanEval.GroupTheory.Defs

/-- **First half of A4**: in the standing context `CtxF H Q t s r P`, the subgroup
`C_G(P) ⊓ H` is strongly embedded in `C_G(P)`.

This is Peterfalvi I Ch. I §1 (6) (`Work.ThreePoints.IsStronglyEmbedded.subgroupOf_inf`, i.e.
`Work.Reductions.stronglyEmbedded_subgroupOf`) applied to `H` strongly embedded in `G` and
`X = C_G(P)`:

* `C_G(P) ⊓ H ≠ C_G(P)`, because `t ∈ C_G(P)` (`P ≤ centD H t ≤ C_G(t)`) while `t ∉ H`;
* `|C_G(P) ⊓ H|` is even, because `s ∈ C_Q(P) ≤ C_G(P) ⊓ H` has order `2`. -/
theorem CGP_inf_H_stronglyEmbedded {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t s r : G} {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      ((Subgroup.centralizer (P : Set G) ⊓ H).subgroupOf (Subgroup.centralizer (P : Set G))) := by
  have hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H := c.split.stronglyEmbedded
  -- `t` lies in `C_G(P)` (it centralises `P`), but not in `H`.
  have htC : t ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (P_le_centralizer_t c hx)
  have htH : t ∉ H := t_not_mem_H c
  -- `s ∈ C_Q(P) ≤ C_G(P) ⊓ H` has order `2`, so `C_G(P) ⊓ H` has even order.
  have hsC : s ∈ Subgroup.centralizer (P : Set G) := CQ_le_CGP c (s_mem_CQ c)
  have hsH : s ∈ H := CQ_le_H c (s_mem_CQ c)
  have hs : s ∈ Subgroup.centralizer (P : Set G) ⊓ H := ⟨hsC, hsH⟩
  have heven : Even (Nat.card ↥(Subgroup.centralizer (P : Set G) ⊓ H)) := by
    have hdvd : Nat.card ↥(Subgroup.zpowers s) ∣
        Nat.card ↥(Subgroup.centralizer (P : Set G) ⊓ H) :=
      Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hs)
    rw [Nat.card_zpowers, c.s_inv] at hdvd
    exact even_iff_two_dvd.mpr hdvd
  refine Work.ThreePoints.IsStronglyEmbedded.subgroupOf_inf
    (H := H) (X := Subgroup.centralizer (P : Set G)) hH ?_ heven
  -- properness: `(C_G(P) ⊓ H).subgroupOf C_G(P) = ⊤` would force `t ∈ H`.
  intro htop
  have hmem : t ∈ Subgroup.centralizer (P : Set G) ⊓ H :=
    Subgroup.subgroupOf_eq_top.mp htop htC
  exact htH (Subgroup.mem_inf.mp hmem).2

/-- **A4** (Peterfalvi II Ch. V §3 step (2), first half).  In the standing context
`CtxF H Q t s r P`, the subgroup `C_G(P) ⊓ H` is strongly embedded in `C_G(P)` and is a coatom
(maximal subgroup) of `C_G(P)` — equivalently, `C_G(P)` acts 2-transitively on `Ω_P = fixP H P`
with point stabiliser `C_G(P) ⊓ H = C_H(P)`.

* Strong embedding: `C_G(P) ⊓ H ≠ ⊤` (`t ∈ C_G(P)` by `Work.AppXIShadow.P_le_centralizer_t`,
  `t ∉ H`), it has even order (`s ∈ C_Q(P)` by `Work.AppXIShadow.s_mem_CQ` has order `2`), and
  for `g ∈ C_G(P) ∖ H`, `(C_G(P) ⊓ H) ⊓ (C_G(P) ⊓ H^g) ≤ H ⊓ H^g` has odd order by strong
  embedding of `H` in `G`.  (Conjugation and intersections are computed inside `↥C_G(P)`; use
  `Subgroup.map_subtype_subgroupOf`/`Subgroup.subgroupOf_inf` and
  `Subgroup.card_dvd_of_le`.)
* Maximality: by A1 (`Work.AppXIShadow.CQ_regular_on_fixP`) `C_Q(P)` is sharply transitive on
  `fixP H P ∖ {∞}`; hence `C_G(P)` is transitive on `fixP H P` and its point stabiliser
  `C_G(P) ⊓ H ⊇ C_Q(P)` is transitive on `fixP H P ∖ {∞}`, i.e. `C_G(P)` is 2-transitive on
  `fixP H P` (`Work.DoubleTransitivity.IsTwoTransitiveOnSub`).  With `P ≤ H`
  (`Work.AppXIShadow.P_le_H`), `C_G(P) ≤ N_G(P)` and `3 ≤ (Submission.Blueprint.fixedPts H P).ncard`
  (`Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD`), the maximality argument
  `Work.ThreePoints.P3NeBot.maximal_of_twoTransitive` gives `M = C_G(P) ⊓ H ∨ M = C_G(P)` for every
  `C_G(P) ⊓ H ≤ M ≤ C_G(P)`, i.e. the `subgroupOf`-form `IsCoatom`.

(`Work.AppXIShadow.stabilizer_fixPBase` identifies `MulAction.stabilizer ↥C_G(P) (fixPBase H P _)`
with `(C_G(P) ⊓ H).subgroupOf C_G(P)`, which is the form A3 consumes.) -/
theorem CGP_stronglyEmbedded_coatom {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      ((Subgroup.centralizer (P : Set G) ⊓ H).subgroupOf (Subgroup.centralizer (P : Set G))) ∧
    IsCoatom ((Subgroup.centralizer (P : Set G) ⊓ H).subgroupOf
      (Subgroup.centralizer (P : Set G))) := by
  refine ⟨CGP_inf_H_stronglyEmbedded c, ?_⟩
  -- ### 2-transitivity of `C_G(P)` on `Ω_P = fixedPts H P` (A1 + Ch. I §2)
  have h2t : Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.centralizer (P : Set G))
      (Submission.Blueprint.fixedPts H P) := CGP_twoTransitive c
  -- ### the maximality statement in `G`
  have htC : t ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (P_le_centralizer_t c hx)
  have hmax : ∀ M : Subgroup G, (Subgroup.centralizer (P : Set G) ⊓ H) ≤ M →
      M ≤ Subgroup.centralizer (P : Set G) →
      M = (Subgroup.centralizer (P : Set G) ⊓ H) ∨ M = Subgroup.centralizer (P : Set G) :=
    fun M hKM hMF => Work.ThreePoints.P3NeBot.maximal_of_twoTransitive
      (H := H) (F := Subgroup.centralizer (P : Set G)) (M := M) (X := P)
      (P_le_H c) (Subgroup.centralizer_le_normalizer (P : Set G))
      (Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD
        c.split.stronglyEmbedded c.split.invol c.split.not_mem c.P_le)
      h2t hKM hMF
  -- ### transfer to the lattice of subgroups of `C_G(P)`
  have hKF : (Subgroup.centralizer (P : Set G) ⊓ H) ≤ Subgroup.centralizer (P : Set G) :=
    inf_le_left
  have hne : (Subgroup.centralizer (P : Set G) ⊓ H) ≠ Subgroup.centralizer (P : Set G) := by
    intro h
    have htK : t ∈ Subgroup.centralizer (P : Set G) ⊓ H := by rw [h]; exact htC
    exact t_not_mem_H c (Subgroup.mem_inf.mp htK).2
  exact isCoatom_subgroupOf_of_maximal (lt_of_le_of_ne hKF hne) hmax

end Work.AppXIShadow
