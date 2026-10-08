import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.caseC_setup
import Submission.Work.PSU3.StageA.centD_ne_bot
import Submission.Work.PSU3.StageA.not_caseA
import Submission.Work.PSU3.StageA.centD_le_W_of_PSU3Hyp
import Submission.Work.PSU3.StageA.caseC_not_suzuki_card_q2_b
import Submission.Work.PSU3.StageA.caseC_st_structure
import Submission.Work.PSU3.StageA.centD_eq_bot_of_Q_eq_Q0sub
import Submission.Work.PSU3.StageA.tst_eq_sts_of_Q_eq_Q0sub
import Submission.Work.PSU3.StageA.caseC_general
import Submission.Work.ThmF.ChV12.JformReduction
import Submission.Work.PSU3.StageA.ftfree_route
import Submission.Work.PSU3.StageA.caseWbot_abelian_eq_Q0sub_direct
import Submission.Work.RankOneUniqueness.closure_Q_t_eq_top

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.caseC_data` — the data of case c) of Peterfalvi II, Ch. VI §1

In situation (B0)–(B3) with `G` simple and `V = C_D(t) ≠ 1`, Peterfalvi's Ch. VI §1 Proposition
(p. 259) for the structure-identity data `(s, r)` of Ch. V §2 Lemma 1 b)
(`s ∈ Inv(Q)`, `r ∈ Q`, `t s t = r⁻¹ t r`) gives three alternatives:

* a) `Q = Q₀ = Q0sub H` and `orderOf (s * t) = 3`;
* b) `Q` non-abelian of order `q²` (`q = |Q₀|`), `orderOf (s * t) = 5`, `W = ⊥`;
* c) `|Q| = q³`, `orderOf (s * t) = 3`, `W ≠ ⊥`.

Both a) and b) force `W = C_V(K) = C_D(Inv H) = ⊥`, whereas `V = C_D(t) ≠ 1` (`centD_ne_bot`,
from `¬ IsZassenhaus H`) together with `V ≤ W` (`centD_le_W_of_PSU3Hyp`) gives `W ≠ ⊥`.  Hence
only c) can occur, which is the statement proved here.

## Status and the exact remaining gap (recorded for the area)

*Proved here (no gaps)*

* `mulAut_eq_one_of_odd_order_of_fixes_sqOne` — an odd-order automorphism of a commutative
  2-group fixing `Ω₁` pointwise is trivial;
* `W_eq_bot_of_abelian` — **`Q` abelian `⟹ W = ⊥`** (Ch. V §1 case 1, *without* Feit–Thompson:
  the counting argument is replaced by the operator argument above);
* `not_abelian_of_W_ne_bot` — hence `W ≠ ⊥` forces `Q` non-abelian;
* `caseC_Q0sub_subgroupOf_iff_sq` — inside `Q`, `Q₀sub H` is the set of elements of order `≤ 2`;
* `orderOf_mul_eq_three_of_st` — `t s t = s t s` (with `s² = t² = 1`, `s ≠ t`) is equivalent to
  `orderOf (s * t) = 3`.

*Delegated and proved by colleagues* (imported above)

* `caseC_not_suzuki_card_q2_b` — case b) `|Q| = q²` is impossible when `W ≠ ⊥`
  (Ch. VI §1 case 2 / §2, i.e. the type-`A` analysis);
* `caseC_st_structure` — case c): `|Q| = q³` and `W ≠ ⊥` give the structure identity
  `t s t = s t s` (Ch. VI §1 case 3).

*One outstanding input*: `Work.PSU3.StageA.centD_le_W_of_PSU3Hyp` (`V = centD H t ≤ W`).  From it
and `centD_ne_bot` (`V ≠ ⊥`), `false_of_centD_le_W` gives the third conjunct `W ≠ ⊥` in one line;
that is the wiring used by `caseC_data` below.  It is the area's deep node — Suzuki's Lemma 60 =
Peterfalvi II, Ch. VII §4, as corrected by Kantor–Seitz §§14–15 — and it is *the* acknowledged
blocking input of Stage A:

* the case analysis `chVI_prop` needs `K = J(D,t)` to be a cyclic normal subgroup of `D` in the
  branch `W = ⊥`, which the area reaches only through Appendix X + `FeitThompsonProp`
  (the project's single open hole; `ThmF.ChV12.Ksub_cyclic_normal` carries `hFT`);
* `StageB.exists_omega_of_not_fpf` presupposes a coarse frame, i.e. the conclusion `|Q| = q³`;
* the FT-free alternative is the Kantor–Seitz transfer route, isolated by the area as the black
  box `RankOneVNeqWProp` (`not_caseA.lean`), from which `stageA_W_ne_bot_of_KS` (below) derives
  `W ≠ ⊥` in four lines.  The dedicated area `Submission/Work/KantorSeitz/` has completed the
  entire transfer-theoretic half of §15, without gaps
  (`transfer_ne_one_of_fusion_control`, `exists_normal_index_p_of_fusion_control`,
  `exists_normal_index_p_of_twoPoint_fusion`, `fusion_controlled_of_fixesThree`,
  `exists_zmod_hom_of_sylow_normalizer`, `padicValNat_pow_add_one`); what remains there is the
  §13.8 Sylow-structure half (`NOTES_ks_chain.md`, "the remaining obligation").  The area has also
  already reduced `V ≤ W` to a point-stabiliser condition
  (`centD_le_W_iff_pointStabilizers`) and proved the case-a) reduction `V ≤ [D,D]`
  (`centD_le_commutator`).

Once `centD_le_W_of_PSU3Hyp` (or `RankOneVNeqWProp`) is proved, `caseC_data` has no gaps
with no further change: the conclusion is assembled here from that single input, from
`W_eq_bot_of_abelian` (which removes the abelian case without Feit–Thompson), from the
colleague-proved `caseC_not_suzuki_card_q2_b` and `caseC_st_structure`, and from
`orderOf_mul_eq_three_of_st`.

## Update (this session): the gap is *only* the third conjunct, and it is now interface-complete

`caseC_data_of_W_ne_bot` proves the entire statement from `W H t ≠ ⊥` alone; hence

* `caseC_data_of_KS : RankOneVNeqWProp → …` (uses `stageA_W_ne_bot_of_KS`),
* `caseC_data_of_centD_le_W : centD H t ≤ W H t → …` (uses `false_of_centD_le_W`),
* `caseC_data` (uses the imported node as before),

and no further change to `caseC_data` is needed once any input supplying `W ≠ ⊥` lands.

The remaining conjunct `W ≠ ⊥` is *equivalent* to `Ksub H t = Kset H t` (Ch. V §1 Prop. 2 in the
branch `V ≠ ⊥`, `W ≠ ⊥`), which in turn follows from solvability of the odd-order group
`twoPoint H t` (`Work.PSU3.StageA.Ksub_eq_Kset_of_Hyp5_of_solvable`, proved) — i.e. from
`FeitThompsonProp`.  The FT-free alternative is the classical Zassenhaus/Hering statement on
odd-order transitive linear groups over `𝔽₂`; the reductions isolated for it this session live in
`Submission/Work/ThmF/ChV12/JformReduction.lean` (`commutator_mem_of_generated_by_inverted`,
`jformOf_of_cyclic_normal_irreducible`, `CyclicNormalIrreducibleProp`, and the machine-checked
equivalence `CyclicNormalIrreducibleProp ↔ TransitiveLinearSolvable`), and
`Submission/Work/PSU3/StageA/NOTES_caseC_data_route.md` records the route and the exact gap.

New glue here: `ReductionSetEq`, `centD_eq_bot_of_Q_eq_Q0sub'`, `Q_ne_Q0sub_of_hset`
(= `not_caseA` from the "Réduction" set equality alone, without any `hst` input).

With `FeitThompsonProp` as an explicit hypothesis the two excluded cases of the Ch. VI §1
trichotomy are now available hole-free: `Work.PSU3.StageA.not_caseA_of_FT` (already proved) and
`Work.PSU3.StageA.not_caseB_of_FT` (`Submission/Work/PSU3/StageA/not_caseB_of_FT.lean`), together
with `Ksub_eq_Kset_of_FT` (Ch. V §1 Prop. 2 from `hFT` alone) and `Q_ne_Q0sub_of_FT`.  The
case-b chain used there is `Work.PSU3.StageA.caseB_tQt_subset_of_Ksub` +
`Work.PSU3.StageA.caseB_centD_eq_bot_of_Ksub_of_canonical` (both proved), which repair the
`x = 1` defect of the pre-existing `caseB_tQt_subset` (see the note §6).  So, modulo
`FeitThompsonProp` and the `W = ⊥` branch of the source's Ch. VI §1 analysis, `caseC_data` is
complete. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-! ## An automorphism of odd order of an abelian 2-group fixing the involutions -/

/-- **Odd-order automorphisms of an abelian 2-group fixing `Ω₁` pointwise are trivial.**

If every element of the commutative group `A` has `2`-power order and `α : A ≃* A` has odd order
and fixes every `x` with `x * x = 1`, then `α = 1`.  (Strong induction on `orderOf x`: for `x`
with `x ^ 2 ^ (i+1) = 1` the element `x * x` is fixed by the induction hypothesis, so
`c := α x * x⁻¹` satisfies `c * c = 1` — commutativity is used here — hence `α c = c` and
`α (α x) = α (x * c) = (x * c) * c = x`; an operator of odd order with `α ^ 2 = 1` on `x`
fixes `x`.) -/
theorem mulAut_eq_one_of_odd_order_of_fixes_sqOne {A : Type} [CommGroup A]
    (hA : ∀ x : A, ∃ n : ℕ, x ^ 2 ^ n = 1) (α : A ≃* A) (hodd : Odd (orderOf α))
    (h2 : ∀ x : A, x * x = 1 → α x = x) : α = 1 := by
  have key : ∀ i : ℕ, ∀ x : A, x ^ 2 ^ i = 1 → α x = x := by
    intro i
    induction i with
    | zero =>
        intro x hx
        simp only [pow_zero, pow_one] at hx
        rw [hx, map_one]
    | succ i ih =>
        intro x hx
        have hxx : (x * x) ^ 2 ^ i = 1 := by
          have h1 : x * x = x ^ 2 := (pow_two x).symm
          rw [h1, ← pow_mul]
          have h2' : 2 * 2 ^ i = 2 ^ (i + 1) := by ring
          rw [h2']
          exact hx
        have hfix2 : α (x * x) = x * x := ih (x * x) hxx
        set c : A := α x * x⁻¹ with hc
        have hc2 : c * c = 1 := by
          rw [hc]
          calc (α x * x⁻¹) * (α x * x⁻¹) = (α x * α x) * (x⁻¹ * x⁻¹) := by ac_rfl
            _ = α (x * x) * (x * x)⁻¹ := by rw [map_mul, mul_inv_rev]
            _ = 1 := by rw [hfix2, mul_inv_cancel]
        have hfixc : α c = c := h2 c hc2
        have hxc : α x = x * c := by
          rw [hc]
          calc α x = (α x * x⁻¹) * x := by rw [mul_assoc, inv_mul_cancel, mul_one]
            _ = x * (α x * x⁻¹) := by rw [mul_comm (α x * x⁻¹) x]
        have hα2 : α (α x) = x := by
          have h1 : α (α x) = α (x * c) := by rw [hxc]
          rw [h1, map_mul, hfixc, hxc, mul_assoc, hc2, mul_one]
        obtain ⟨m, hm⟩ := hodd
        have hfix2x : ∀ k : ℕ, ((α ^ 2) ^ k) (α x) = α x := by
          intro k
          induction k with
          | zero => rfl
          | succ k ihk =>
              rw [pow_succ', MulAut.mul_apply, ihk]
              show α (α (α x)) = α x
              rw [hα2]
        have hsplit : (α ^ (2 * m + 1)) x = α x := by
          rw [pow_succ, pow_mul, MulAut.mul_apply, hfix2x m]
        have hpow : (α ^ (2 * m + 1)) x = x := by
          rw [← hm, pow_orderOf_eq_one]; rfl
        rw [← hsplit]; exact hpow
  exact MulEquiv.ext (fun x => key (Classical.choose (hA x)) x (Classical.choose_spec (hA x)))

/-! ## Abelian `Q` forces `W = ⊥` -/

/-- **Ch. V §1 case 1 without Feit–Thompson: if `Q` is abelian then `W = C_V(K) = ⊥`.**

`W ≤ C_D(Inv H)` (Ch. II §4 Prop. 4, clause P4 of `ChIIFourProp`), so every `w ∈ W` induces on
the abelian 2-group `Q` an automorphism of odd order fixing `Ω₁(Q) = ⟨Inv H⟩` pointwise; by
`mulAut_eq_one_of_odd_order_of_fixes_sqOne` it is trivial, so `w` centralises `Q` and therefore
fixes every point of `G ⧸ H`, i.e. `w ∈ ⋂_g H^g = N_G(H) = ⊥` by simplicity. -/
theorem W_eq_bot_of_abelian {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hab : Submission.Blueprint.IsAbelianSubgroup Q) :
    Work.ThmF.W H t = ⊥ := by
  have hP4 := (hC4 G hS.situation H hS.split.stronglyEmbedded t hS.split.invol
    hS.split.not_mem).2.2.2.2.1
  have hW_eq : Work.ThmF.W H t = Submission.Blueprint.twoPoint H t ⊓
      Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G)) := by
    simpa only [Work.ThmF.W, Work.ThmF.Kset, Submission.Blueprint.centD] using hP4
  have hWQ0 : ∀ w ∈ Work.ThmF.W H t, ∀ x ∈ Work.ThmF.Q0sub H, w * x = x * w := by
    intro w hw x hx
    have hcent : w ∈ Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G)) :=
      (Subgroup.mem_inf.mp (hW_eq ▸ hw)).2
    have hle : Work.ThmF.Q0sub H ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [Work.ThmF.Q0sub]
      refine (Subgroup.closure_le _).mpr ?_
      intro y hy
      rcases Work.ThmF.mem_Q0_iff.mp hy with ⟨hyH, hy2⟩ | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hcent) y ⟨hyH, hy2⟩)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (by rw [one_mul, mul_one])
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm
  have hpow : ∀ x : ↥Q, ∃ n : ℕ, x ^ 2 ^ n = 1 := fun x => hS.two x
  refine le_antisymm ?_ bot_le
  intro w hw
  have hwD : w ∈ Submission.Blueprint.twoPoint H t :=
    Work.ThmF.centD_le_twoPoint (H := H) t (Work.ThmF.W_le_centD H t hw)
  have hwN : w ∈ Subgroup.normalizer (Q : Set G) := hS.split.normal (Subgroup.mem_inf.mp hwD).1
  have hoddw : Odd (orderOf w) :=
    Odd.of_dvd_nat (Work.ThmF.split_odd_card_twoPoint hS.split)
      (Subgroup.orderOf_dvd_natCard (Submission.Blueprint.twoPoint H t) hwD)
  have hdvd : orderOf (Work.PSU3.StageA.conjOnQ w hwN) ∣ orderOf w := by
    rw [orderOf_dvd_iff_pow_eq_one]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp only [Work.PSU3.StageA.conjOnQ_pow_coe, pow_orderOf_eq_one, one_mul, mul_one, inv_one,
      MulAut.one_apply]
  have hodd_α : Odd (orderOf (Work.PSU3.StageA.conjOnQ w hwN)) := Odd.of_dvd_nat hoddw hdvd
  letI : CommGroup ↥Q := { (inferInstance : Group ↥Q) with
    mul_comm := fun a b => Subtype.ext (hab a.1 a.2 b.1 b.2) }
  have hconj : (Work.PSU3.StageA.conjOnQ w hwN) = 1 := by
    refine mulAut_eq_one_of_odd_order_of_fixes_sqOne (A := ↥Q) ?_ _ hodd_α ?_
    · intro x; exact hpow x
    · intro x hx
      have hxG : (x : G) * (x : G) = 1 := by
        have h := congrArg Subtype.val hx
        simpa [Subgroup.coe_mul] using h
      have hxQ0 : (x : G) ∈ Work.ThmF.Q0sub H := by
        rcases eq_or_ne (x : G) 1 with h1 | h1
        · rw [h1]; exact Work.ThmF.Q0_le_Q0sub H (Work.ThmF.one_mem_Q0 H)
        · have ho : orderOf (x : G) = 2 :=
            orderOf_eq_prime (by rw [pow_two]; exact hxG) h1
          exact Work.ThmF.Q0_le_Q0sub H
            (Work.ThmF.involutions_subset_Q0 H ⟨hS.split.le x.2, ho⟩)
      have hval : (((Work.PSU3.StageA.conjOnQ w hwN) x : ↥Q) : G) = (x : G) := by
        rw [Work.PSU3.StageA.conjOnQ_coe]
        show w * (x : G) * w⁻¹ = (x : G)
        rw [hWQ0 w hw (x : G) hxQ0, mul_assoc, mul_inv_cancel, mul_one]
      exact Subtype.ext hval
  have hwQ : ∀ q ∈ Q, w * q * w⁻¹ = q :=
    (Work.PSU3.StageA.conjOnQ_eq_one_iff w hwN).mp hconj
  have hwt : w * t = t * w :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp (Work.ThmF.W_le_centD H t hw)).2
  haveI : IsSimpleGroup G := hS.simple
  have htop : Subgroup.closure ((Q : Set G) ∪ {t}) = ⊤ :=
    Work.RankOneUniqueness.closure_Q_t_eq_top hS.split
  have hWZ : w ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hle : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [← htop]
      refine (Subgroup.closure_le _).mpr ?_
      rintro y (hy | hy)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (by
          have h := hwQ y hy
          calc y * w = (w * y * w⁻¹) * w := by rw [h]
            _ = w * y := by group)
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_centralizer_singleton_iff.mpr hwt.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  have hZbot : Subgroup.center G = ⊥ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hS.simple (Subgroup.center G) (inferInstance) with h | h
    · exact h
    · exfalso
      have hHcenter : H ≤ Subgroup.center G := by rw [h]; exact le_top
      have hHnorm : H.Normal := ⟨fun a ha b => by
        have hcomm : b * a = a * b := Subgroup.mem_center_iff.mp (hHcenter ha) b
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
        exact ha⟩
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hS.simple H hHnorm with hb | ht
      · have heven : Even (Nat.card H) := hS.split.stronglyEmbedded.2.1
        rw [hb, Subgroup.card_bot] at heven
        exact absurd heven (by norm_num)
      · exact hS.split.stronglyEmbedded.1 ht
  exact Subgroup.mem_bot.mp (hZbot ▸ hWZ)

/-- **`W ≠ ⊥` forces `Q` non-abelian.**  (Contrapositive of `W_eq_bot_of_abelian`; this is the
abelian case of Ch. VI §1 removed without Feit–Thompson or the case trichotomy.) -/
theorem not_abelian_of_W_ne_bot {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hW : Work.ThmF.W H t ≠ ⊥) : ¬ Submission.Blueprint.IsAbelianSubgroup Q :=
  fun hab => hW (W_eq_bot_of_abelian hS hC4 hab)

/-! ## Two elementary facts used in the assembly -/


/-- `t * s * t = s * t * s` with `s * s = t * t = 1` and `s ≠ t` forces `orderOf (s * t) = 3`
(the case-c "structure identity" is equivalent to `orderOf (s * t) = 3`). -/
theorem orderOf_mul_eq_three_of_st {G : Type} [Group G] {s t : G}
    (hss : s * s = 1) (htt : t * t = 1) (hne : s ≠ t) (h : t * s * t = s * t * s) :
    orderOf (s * t) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · have h2 : (s * t) * (s * t) = t * s := by
      calc (s * t) * (s * t) = s * (t * s * t) := by group
        _ = s * (s * t * s) := by rw [h]
        _ = (s * s) * (t * s) := by group
        _ = t * s := by rw [hss, one_mul]
    calc (s * t) ^ 3 = (s * t) ^ 2 * (s * t) := by rw [pow_succ]
      _ = (t * s) * (s * t) := by rw [pow_two, h2]
      _ = t * (s * s) * t := by group
      _ = t * t := by rw [hss, mul_one]
      _ = 1 := htt
  · intro h1
    have h3 : s = (s * t) * t := by rw [mul_assoc, htt, mul_one]
    rw [h1, one_mul] at h3
    exact hne h3

/-! ## Case c) of Peterfalvi II, Ch. VI §1 -/

/-- **`W = ⊥` together with `V ≤ W` is a contradiction**, since `V ≠ ⊥` (`centD_ne_bot`). -/
theorem false_of_centD_le_W {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hW : Work.ThmF.W H t = ⊥)
    (hVW : Submission.Blueprint.centD H t ≤ Work.ThmF.W H t) : False :=
  centD_ne_bot hS (le_bot_iff.mp (hVW.trans (le_of_eq hW)))

/-- **`W = C_V(K) ≠ ⊥` from the Kantor–Seitz input `RankOneVNeqWProp`.**

If `W = ⊥` then `W < V = centD H t`, since `V ≠ ⊥` (`centD_ne_bot`, from `¬ IsZassenhaus H`);
with `Q` a `2`-group and the split rank-one datum, `RankOneVNeqWProp` (Peterfalvi II Ch. VII §4,
following Kantor–Seitz §§14–15) would then make `G` non-simple — contradicting `PSU3Hyp.simple`. -/
theorem stageA_W_ne_bot_of_KS {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hKS : RankOneVNeqWProp) (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    Work.ThmF.W H t ≠ ⊥ := by
  intro hbot
  have hlt : Work.ThmF.W H t < Submission.Blueprint.centD H t := by
    rw [hbot]
    exact bot_lt_iff_ne_bot.mpr (centD_ne_bot hS)
  exact hKS G H Q t hS.split hS.two hlt hS.simple

/-! ## Glue: case a) elimination conditional on the "Réduction" set equality

Combining `tst_eq_sts_of_Q_eq_Q0sub` (case a) forces the structure identity, FT-free) with
`centD_eq_bot_of_Q_eq_Q0sub` (case a) + the set equality `X5 H t = Q₀·K ∪ Q₀·K·t·Q₀` forces
`V = ⊥`), we obtain a reproof of `¬ (Q = Q0sub H)` that needs *only* the set equality `hset`
— in particular no `hst` hypothesis and no `H`-involution.  The set equality is the content of
Peterfalvi II Ch. VI §3 "Réduction" (equivalently `Ksub H t = Kset H t`). -/

/-- The set-equality hypothesis of the "Réduction" (`L5crux`-style): the set
`X5 H t = Q₀·K ∪ Q₀·K·t·Q₀` with `K = Kset H t`. -/
abbrev ReductionSetEq {G : Type} [Group G] {H : Subgroup G} {t : G} : Prop :=
  (Work.ThmF.Lemma5.X5 H t : Set G) =
    {x : G | (∃ a ∈ (Work.ThmF.Q0sub H : Set G), ∃ k ∈ Work.ThmF.Kset H t, x = a * k) ∨
      (∃ a ∈ (Work.ThmF.Q0sub H : Set G), ∃ k ∈ Work.ThmF.Kset H t,
        ∃ a' ∈ (Work.ThmF.Q0sub H : Set G), x = a * k * t * a')}

/-- **`V = centD H t = ⊥` in case a), given the "Réduction" set equality.**  No `hst` input. -/
theorem centD_eq_bot_of_Q_eq_Q0sub' {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (hQ : (Q : Set G) = Work.ThmF.Q0sub H) (hset : ReductionSetEq (H := H) (t := t)) :
    Submission.Blueprint.centD H t = ⊥ :=
  centD_eq_bot_of_Q_eq_Q0sub hS hC4 hs hs2
    (tst_eq_sts_of_Q_eq_Q0sub hS hC4 hs hs2 hr hsr hQ) hQ hset

/-- **Case a) is impossible**, given the "Réduction" set equality: `Q ≠ Q0sub H`.  This is
`not_caseA` stripped of the (redundant) `hst` hypothesis, with the single classical input
`SharpInvertingClosed` replaced by the set equality `hset` (`Ksub H t = Kset H t`). -/
theorem Q_ne_Q0sub_of_hset {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (hset : ReductionSetEq (H := H) (t := t)) : (Q : Set G) ≠ Work.ThmF.Q0sub H :=
  fun hQ => centD_ne_bot hS (centD_eq_bot_of_Q_eq_Q0sub' hS hC4 hs hs2 hr hsr hQ hset)

/-- **`caseC_data` with the missing input `W H t ≠ ⊥` as an explicit hypothesis.**

This is the whole content of `caseC_data` once the deep node is supplied: from `W ≠ ⊥`,
`Q` is non-abelian (`not_abelian_of_W_ne_bot`), hence a Suzuki `2`-group
(`caseC_isSuzuki2Grp`), and Higman's dichotomy `|Q| = |Z(Q)|²` or `³` leaves only case c); the
structure identity of `caseC_st_structure` then gives `orderOf (s*t) = 3`. -/
theorem caseC_data_of_W_ne_bot {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) {s r : G} (hs : s ∈ Q) (hs2 : orderOf s = 2)
    (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r) (hWne : Work.ThmF.W H t ≠ ⊥) :
    Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3 ∧ orderOf (s * t) = 3 ∧
      Work.ThmF.W H t ≠ ⊥ := by
  have hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q := not_abelian_of_W_ne_bot hS hC4 hWne
  -- the Suzuki structure on `Q` and Higman's cardinality dichotomy `|Q| = |Z(Q)| ^ 2` or `^ 3`
  have hZ : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1 :=
    caseC_Q0sub_subgroupOf_iff_sq hS hC4
  have hSuz2 : Work.Higman.IsSuzuki2Grp ↥Q := caseC_isSuzuki2Grp hS hC4 hnab hZ hWne
  have hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q :=
    Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp.mpr ⟨hSuz2⟩
  obtain ⟨-, -, -, hdich, -⟩ := hHig ↥Q hSuz
  have hZc : Nat.card ↥(Subgroup.center ↥Q) = Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [caseC_center_subgroupOf hS hHig hZ hSuz2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Q0sub_le_Q hS.split)).toEquiv
  rw [hZc] at hdich
  rcases hdich with h2 | h3
  · -- `|Q| = |Q₀|²` is Ch. VI §1 case b), which is killed by `W ≠ ⊥`
    exact (caseC_not_suzuki_card_q2_b hS hC4 hHig hWne hSuz h2).elim
  · -- case c): the structure identity gives `orderOf (s * t) = 3`
    refine ⟨h3, ?_, hWne⟩
    refine orderOf_mul_eq_three_of_st ?_ ?_ ?_
      (caseC_st_structure hS hC4 hHig hs hs2 hr hsr hWne h3)
    · have h := pow_orderOf_eq_one s
      rw [hs2] at h; simpa [pow_two] using h
    · have h := pow_orderOf_eq_one t
      rw [hS.split.invol] at h; simpa [pow_two] using h
    · exact fun hst => hS.split.not_mem (hst ▸ hS.split.le hs)

/-- **`caseC_data` from the Kantor–Seitz input `RankOneVNeqWProp`.**

This is the FT-free interface: the transfer-theoretic half of Kantor–Seitz §§14–15 is already
formalised in `Submission/Work/KantorSeitz/`, and `stageA_W_ne_bot_of_KS` turns
`RankOneVNeqWProp` into `W ≠ ⊥`; the rest is `caseC_data_of_W_ne_bot`. -/
theorem caseC_data_of_KS {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hKS : RankOneVNeqWProp) (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hHig : Submission.Blueprint.HigmanProp)
    {s r : G} (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q)
    (hsr : t * s * t = r⁻¹ * t * r) :
    Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3 ∧ orderOf (s * t) = 3 ∧
      Work.ThmF.W H t ≠ ⊥ :=
  caseC_data_of_W_ne_bot hS hC4 hHig hs hs2 hr hsr (stageA_W_ne_bot_of_KS hKS hS hC4)

/-- **`caseC_data` conditional on the deep node `centD_le_W_of_PSU3Hyp`.**

`V = centD H t ≤ W H t` (Suzuki's Lemma 60 / Ch. VII §4 / Kantor–Seitz §§14–15) together with
`V ≠ ⊥` (`centD_ne_bot`) gives `W ≠ ⊥` in one line. -/
theorem caseC_data_of_centD_le_W {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hVW : Submission.Blueprint.centD H t ≤ Work.ThmF.W H t)
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) {s r : G} (hs : s ∈ Q) (hs2 : orderOf s = 2)
    (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r) :
    Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3 ∧ orderOf (s * t) = 3 ∧
      Work.ThmF.W H t ≠ ⊥ :=
  caseC_data_of_W_ne_bot hS hC4 hHig hs hs2 hr hsr
    (fun hbot => false_of_centD_le_W hS hbot hVW)

-- Superseded (2026): the hole-carrying `caseC_data` was removed by the hole sweep; the proved
-- replacement is `Work.PSU3.StageA.caseC_data_of_W_ne_bot` composed with
-- `Work.PSU3.StageA.W_ne_bot_of_PSU3HypFT` (see `StageA/chVI_prop_of_FT.lean` and
-- `StageC/psu3_coords_FT.lean`).

/-! ## The Feit–Thompson-free reduction of `caseC_data`

`caseC_data` is proved above from the area's deep node `centD_le_W_of_PSU3Hyp` (`V ≤ W`).  The two
theorems below record the *other* reduction, found in this session: modulo

* `Work.ThmF.ChV12.TransitiveLinearSolvable` — an odd-order group acting faithfully and
  transitively on the nonidentity elements of an elementary abelian `2`-group is solvable.  This is
  the classical near-field / `ΓL(1, 2 ^ k)` statement; in this workspace it is reduced to the single
  lemma `Work.ThmF.ChV12.even_card_closure_of_two_ppd` (two automorphisms of primitive-prime-divisor
  order with distinct cyclic subgroups generate a group of even order) by
  `Submission/Work/ThmF/ChV12/transitiveLinearSolvable_of_ppd.lean`;
* `CaseBExcluded` — the `W = ⊥` branch of Ch. VI §1 with `Q` non-abelian (cases 2 and 3 of the
  source's Proposition, i.e. the Ch. VI §2–§3 counting for the Suzuki case),

the whole statement holds: case a) is excluded by `Q_ne_Q0sub_of_transitiveLinearSolvable`
(Ch. VI §1 case 1, through `Work.ThmF.ChV12.L5cruxProp`, whose classical closure statement is
supplied by `TransitiveLinearSolvable` in `ftfree_route.lean`), and case b) by `CaseBExcluded`.
The assembly itself is in `Submission/Work/PSU3/StageA/caseC_data_ftfree.lean`
(`Work.PSU3.StageA.caseC_data_of_TLS_and_CaseBData`): it cannot live here, because the case-b
analysis imports `Submission.Work.PSU3.StageB`, which transitively imports **this** file.
-/

/-- **Case a) is impossible**, with the `Hyp5`-style structure identity derived from `Q = Q0sub H`
(so that it applies to the structure-identity data `(s, r)` of `caseC_data`). -/
theorem Q_ne_Q0sub_of_transitiveLinearSolvable {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G} (hTLS : Work.ThmF.ChV12.TransitiveLinearSolvable)
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) {s r : G}
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r) :
    (Q : Set G) ≠ Work.ThmF.Q0sub H :=
  fun hQ => Work.PSU3.StageA.not_caseA_of_transitiveLinearSolvable hTLS hS hC4 hs hs2
    (tst_eq_sts_of_Q_eq_Q0sub hS hC4 hs hs2 hr hsr hQ) hQ

/-- **The remaining node of case b)** (Ch. VI §1 cases 2/3 plus the Ch. VI §2–§3 counting):
`Q` non-abelian together with `W H t = ⊥` is impossible. -/
def CaseBExcluded : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G},
    Work.PSU3.PSU3Hyp H Q t → Submission.Blueprint.ChIIFourProp →
    Submission.Blueprint.HigmanProp → s ∈ Q → orderOf s = 2 → r ∈ Q →
    t * s * t = r⁻¹ * t * r → Work.ThmF.W H t = ⊥ →
    ¬ Submission.Blueprint.IsAbelianSubgroup Q → False


end Work.PSU3.StageA
