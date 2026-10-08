import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q
import Submission.Work.FeitSibley.CharQ.scriptS_vanish
import Submission.Work.Frobenius.Induced.conjChar_ne_self_of_fpf
import Submission.Work.Frobenius.Induced.frobenius_induced_irr
import Submission.Work.ThmF.Setup
import Submission.Work.CharCore.irrDeg_eq_one_of_commutative
import Submission.Work.CharCore.Defs
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `excl_degree_support` (Feit's leaf F2a)

In a split rank-one Zassenhaus configuration `H = Q ⋊ D` (`Q ⊴ H` a normal subgroup,
`D = twoPoint H t = H ⊓ Hᵗ`) every irreducible character `χ` of `H` which is *not trivial on*
`Q` — i.e. `χ ∈ 𝒮 = excludingKernel H Q` — has degree `|D|` and vanishes outside `Q`.

The mathematics is the classical one for a Frobenius group `H = Q ⋊ D` whose complement `D`
acts fixed-point-freely on `Q`:

* `D` acts fixed point freely on `Q` (`ZData.dStab_fpf_on_Q`, the three-point condition, i.e.
  the Zassenhaus hypothesis);
* consequently no non-trivial `d ∈ D` fixes the class of a non-trivial `θ ∈ Irr Q`
  (`Work.Frobenius.Induced.conjChar_ne_self_of_fpf`), so the inertia group of such a `θ` is
  exactly `Q` and `Ind_Q^H θ` is irreducible, whence `χ = Ind_Q^H θ`
  (`Work.FeitSibley.CharQ.exists_indFun_of_complement_of_inertia`, the abstract form of
  Isaacs Thm 6.34);
* an induced character from a *normal* subgroup vanishes off it
  (`Work.FeitSibley.CharQ.indFun_eq_zero_of_notMem`);
* its degree is `[H : Q] · θ 1 ≠ [H : Q] = |D|` because `Q` is abelian, so every `θ ∈ Irr Q` is
  linear (`Work.CharCore.irrDeg_eq_one_of_commutative`), and `D` is a complement of the normal
  subgroup `Q` in `H` (`Work.ThmF.split_card_H`).

None of the hypotheses `IsPGroup 2 Q`, `IsAbelianSubgroup Q` (beyond abelianness of `Q` for the
degree), or simplicity of `G` is used beyond what is stated; cf. the design note
`Submission/Work/ZassenhausPSL2/NOTES_LEAD_bs_psl2core.md` §1.F.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausPSL2.Feit

variable {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}

/-- The two subgroups `Q` and `D = twoPoint H t` of `H = Q ⋊ D`, viewed inside `↥H`, are
complements there. -/
private theorem isComplement'_subgroupOf_twoPoint (h : IsSplitRankOne H Q t) :
    Subgroup.IsComplement' (Q.subgroupOf H) ((twoPoint H t).subgroupOf H) := by
  haveI hKn : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr h.normal
  have hinf' : (Q.subgroupOf H) ⊓ ((twoPoint H t).subgroupOf H) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
    have hmem : (x : G) ∈ Q ⊓ twoPoint H t := ⟨hx.1, hx.2⟩
    rw [h.inf_eq, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hsup' : Q.subgroupOf H ⊔ (twoPoint H t).subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h.le (inf_le_left : twoPoint H t ≤ H), h.sup_eq,
      Subgroup.subgroupOf_self]
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf') ?_
  rw [Set.eq_univ_iff_forall]
  intro x
  have hx : x ∈ Q.subgroupOf H ⊔ (twoPoint H t).subgroupOf H := by
    rw [hsup']; exact Subgroup.mem_top x
  rw [Subgroup.mem_sup_of_normal_left] at hx
  obtain ⟨q, hq, d, hd, hqd⟩ := hx
  exact Set.mem_mul.mpr ⟨q, hq, d, hd, hqd⟩

/-- **F2a.** Members of `𝒮 = excludingKernel H Q` have degree `|D|` and vanish off `Q`. -/
theorem excl_degree_support {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : Submission.Blueprint.IsAbelianSubgroup Q) {χ : H → ℂ}
    (hχ : χ ∈ Submission.Blueprint.excludingKernel H Q) :
    χ 1 = (Nat.card (Submission.Blueprint.twoPoint H t) : ℂ) ∧
      ∀ x : H, (x : G) ∉ Q → χ x = 0 := by
  classical
  -- `χ` is irreducible and is not trivial on `Q`
  obtain ⟨hχIrr, x₀, hx₀Q, hx₀ne⟩ := by
    simpa only [Submission.Blueprint.excludingKernel, Finset.mem_filter] using hχ
  have hKn : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr h.normal
  haveI := hKn
  have hχFrob := Work.FeitSibley.CharQ.mem_frobenius_Irr_of_mem_charCore_Irr hχIrr
  -- The complement `H = Q ⋊ D` inside `↥H`
  have hcomp := isComplement'_subgroupOf_twoPoint h
  -- Inertia step: no `1 ≠ d ∈ D` fixes an irreducible character of `Q` which is non-trivial
  -- on `Q` itself, because `D` acts fixed point freely on `Q` (`Zassenhaus`).
  have hinertia : ∀ θ : ↥(Q.subgroupOf H) → ℂ, θ ∈ Work.Frobenius.Irr ↥(Q.subgroupOf H) →
      (∃ y : ↥(Q.subgroupOf H), (y : H) ∈ (Q.subgroupOf H) ∧ θ y ≠ θ 1) →
      ∀ hh : H, hh ∈ (Submission.Blueprint.twoPoint H t).subgroupOf H → hh ≠ 1 →
        Work.Frobenius.Induced.conjChar (Q.subgroupOf H) hh θ ≠ θ := by
    intro θ hθ hθA hh hhd hh1
    refine Work.Frobenius.Induced.conjChar_ne_self_of_fpf hθ ?_ ?_
    · -- `θ` is not the principal character
      intro hθone
      obtain ⟨y, -, hyne⟩ := hθA
      rw [hθone] at hyne
      simpa using hyne
    · -- `hh ∈ D` has no non-trivial fixed point on `Q`
      intro k hk hconj
      have hconjG : (hh : G) * (k : G) * (hh : G)⁻¹ = (k : G) := by
        have := congrArg (fun z : H => (z : G)) hconj
        simpa using this
      have hk1 : (k : G) = 1 :=
        Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q H Q t h hz (hh : G) hhd
          (fun hc => hh1 (Subtype.ext hc)) (k : G) hk hconjG
      exact Subtype.ext hk1
  -- Hence `χ` is induced from `Q`
  obtain ⟨θ, hθ, hθA, hχeq⟩ := Work.FeitSibley.CharQ.exists_indFun_of_complement_of_inertia
    (G := H) (K := Q.subgroupOf H) (He := (Submission.Blueprint.twoPoint H t).subgroupOf H)
    (A := Q.subgroupOf H) hcomp (le_refl _) hinertia hχFrob ⟨x₀, hx₀Q, hx₀ne⟩
  -- `θ` is linear, as `Q` is abelian
  have hθ1 : θ 1 = 1 := by
    have hθC : θ ∈ Work.CharCore.Irr ↥(Q.subgroupOf H) :=
      (Work.CharCore.mem_Irr_iff_coherence).mpr ((Work.Frobenius.Bridge.mem_Irr_bridge).mp hθ)
    haveI hcomm : IsMulCommutative ↥(Q.subgroupOf H) := by
      rw [isMulCommutative_iff]
      intro a b
      exact Subtype.ext (Subtype.ext (hab (a : G) a.2 (b : G) b.2))
    rw [Work.CharCore.irrDeg_spec hθC, Work.CharCore.irrDeg_eq_one_of_commutative hθC]
    norm_num
  -- `[H : Q] = |D|`, since `H = Q ⋊ D`
  have hidx : (Q.subgroupOf H).index = Nat.card (Submission.Blueprint.twoPoint H t) := by
    have hsplit := Work.ThmF.split_card_H h
    have h1 := Subgroup.index_mul_card (Q.subgroupOf H)
    have hcard : Nat.card ↥(Q.subgroupOf H) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
    have h2' : (Q.subgroupOf H).index * Nat.card ↥Q
        = Nat.card ↥Q * Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
      have h3 : (Q.subgroupOf H).index * Nat.card ↥(Q.subgroupOf H)
          = Nat.card ↥Q * Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
        rw [h1, hsplit]
      rwa [hcard] at h3
    rw [Nat.mul_comm (Q.subgroupOf H).index (Nat.card ↥Q)] at h2'
    exact Nat.mul_left_cancel (Nat.card_pos (α := ↥Q)) h2'
  refine ⟨?_, ?_⟩
  · rw [hχeq, Work.Frobenius.Induced.indFun_apply_one_eq (Q.subgroupOf H) θ, hθ1, mul_one,
      hidx]
  · intro x hx
    rw [hχeq]
    exact Work.FeitSibley.CharQ.indFun_eq_zero_of_notMem θ hx

end Work.ZassenhausPSL2.Feit
