import Mathlib
import Submission.Work.CORE2B.L29Parts
import Submission.Work.CORE2B.L29CallSite
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.L29_case_ii_leaf
import Submission.Work.CORE2B.four_subgroup_meets_pCore_two
import Submission.Work.CORE2B.L27_solvable_base
import Submission.Work.CORE2B.L29CallSite_L27Hyp
import Submission.Work.CORE2B.L29_d16_case_iii_excl
import Submission.Work.CORE2B.fittingPiIn_two_compl_isNilpotent_odd
import Submission.Work.RED.DihOrCycSubgroup
import Submission.Work.RED.DihedralSubgroup

namespace Work.CORE2B

open Subgroup
open scoped commutatorElement

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Leaf P4 of the lead's design pass 15 (Lemma 2.9): "`V` acts faithfully on `A := F_{2'}(N)`"

* `Work.CORE2B.C15.L29FaithfulProp` asks, at the call site `L29CallSite B V N` with the two
  trivial intersections `V ⊓ O₂(N) = ⊥` and `V ⊓ E(N) = ⊥`, for four facts about
  `A := F_{2'}(N) = O_{2'}(F(N))`: nilpotency, odd order, `V ≤ N_G(A)`, and faithfulness of the
  action of the four-group `V` on `A`.
* The first three are general facts about `F_{2'}` of any finite group; the fourth is the
  `D16`/`T.d16` case analysis for the proper subgroup `N` (`N ≺ G` a coatom, hence a D-group by
  `BenderCtx.ih`):
  * case (i) `C_N(F_{2'}(N)) ≤ F_{2'}(N)` gives `V ⊓ C_N(A) ≤ V ⊓ A = ⊥` (`V` has exponent `2`,
    `A` odd order);
  * case (ii) a central involution of `N` is impossible (`L29_case_ii_leaf`);
  * case (iii) `O₂(N)` a four-group with `N/(O₂(N)O(N))` of order `3` or `6` is impossible
    (`L29_d16_case_iii_excl`, from `four_subgroup_meets_pCore_two`);
  * case (iv) a normal quasisimple `E ◁ N` is impossible because `N` is soluble — Bender 2.7,
    applied through `L29CallSite_L27Hyp`.
-/

/-! ## Elementary helpers -/

/-- Subgroups inherit `DihOrCycSylow`: cyclic-or-dihedral Sylow 2-subgroups pass to subgroups
(`Work.RED.DihOrCycSubgroup` fed with `Work.RED.DihedralSubgroup`; the `Work.RED.GW2`
vocabulary is definitionally equal to `Work.GW2`). -/
theorem L29fp_dihOrCycSylow_subtype {G : Type} [Group G] [Finite G]
    (h : Work.GW2.DihOrCycSylow G) (N : Subgroup G) : Work.GW2.DihOrCycSylow ↥N :=
  Work.RED.DihOrCycSubgroup (fun n _ H => Work.RED.DihedralSubgroup n H) N h

/-- A proper subgroup of a finite group has strictly smaller cardinality. -/
theorem L29fp_natCard_subtype_lt_of_ne_top {G : Type} [Group G] [Finite G] (N : Subgroup G)
    (hN : N ≠ ⊤) : Nat.card ↥N < Nat.card G := by
  have h := Subgroup.card_lt_of_lt (lt_of_le_of_ne le_top hN)
  rwa [Nat.card_congr Subgroup.topEquiv.toEquiv] at h

/-- **The induction hypothesis on `N`** (`BenderCtx.ih`): a proper subgroup of the minimal
counterexample with cyclic-or-dihedral Sylow 2-subgroups is a D-group. -/
theorem L29fp_isDGroup_of_ne_top {G : Type} [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G)
    (N : Subgroup G) (hN : N ≠ ⊤) (hNcyc : Work.GW2.DihOrCycSylow ↥N) :
    Work.GW2.IsDGroup ↥N :=
  hctx.ih ↥N (L29fp_natCard_subtype_lt_of_ne_top N hN) hNcyc

/-- A subgroup of a group of odd order, of exponent two, is trivial: its elements' orders divide
both `2` and the odd number `|A|`.  In particular a Klein four-group meets an odd-order subgroup
trivially. -/
theorem L29fp_fourGroup_inf_odd_eq_bot {G : Type} [Group G] [Finite G] {V A : Subgroup G}
    (hV : Work.GW2.IsFourGroup V) (hodd : Odd (Nat.card A)) : V ⊓ A = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxV, hxA⟩ := Subgroup.mem_inf.mp hx
  have hdvd2 : orderOf x ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hV.2 x hxV
  have hdvdA : orderOf x ∣ Nat.card A := by
    have h := orderOf_dvd_natCard (⟨x, hxA⟩ : ↥A)
    rwa [← Subgroup.orderOf_coe] at h
  have hcop : Nat.Coprime 2 (Nat.card A) := Nat.coprime_two_left.mpr hodd
  have h1 : orderOf x = 1 := by
    have h := Nat.dvd_gcd hdvd2 hdvdA
    rw [hcop.gcd_eq_one] at h
    exact Nat.dvd_one.mp h
  exact orderOf_eq_one_iff.mp h1

/-- **A quasisimple subgroup is not soluble.**  `E` is perfect with simple central quotient; a
nontrivial perfect group is not soluble, and `E` is nontrivial because `E/Z(E)` is a nontrivial
simple group. -/
theorem L29fp_not_isSolvable_of_isQuasisimple {G : Type} [Group G] [Finite G]
    (E : Subgroup G) (h : Work.GW2.IsQuasisimple E) : ¬ Group.IsSolvable ↥E := by
  haveI hQ : IsSimpleGroup (↥E ⧸ Subgroup.center ↥E) := h.2
  haveI hperf : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr h.1
  haveI hnontriv : Nontrivial ↥E := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    haveI := hnt
    exact (not_subsingleton (↥E ⧸ Subgroup.center ↥E)) inferInstance
  exact Group.IsPerfect.not_isSolvable ↥E

/-- A normal quasisimple subgroup of a soluble finite group leads to a contradiction: a subgroup
of a soluble group is soluble, while a quasisimple group is not. -/
theorem L29fp_false_of_quasisimple_normal_of_solvable {N : Type} [Group N] [Finite N]
    (hN : Group.IsSolvable N) (E : Subgroup N) (h : Work.GW2.IsQuasisimple E) : False := by
  haveI : Group.IsSolvable N := hN
  haveI : Group.IsSolvable ↥E :=
    Group.isSolvable_of_isSolvable_injective (f := E.subtype) E.subtype_injective
  exact L29fp_not_isSolvable_of_isQuasisimple E h inferInstance

/-- **The `D16` case (i) conclusion implies faithfulness.**  If `C_N(F_{2'}(N)) ≤ F_{2'}(N)`, then
no nontrivial element of the four-group `V ≤ N` centralizes `A := F_{2'}(N)`: such an element
would lie in `V ⊓ C_N(A) ≤ V ⊓ A`, and `V ⊓ A = ⊥` because `V` has exponent two while `|A|` is
odd. -/
theorem L29fp_faithful_of_centralizer_le {G : Type} [Group G] [Finite G] {V N : Subgroup G}
    (hV : Work.GW2.IsFourGroup V) (hVN : V ≤ N)
    (hodd : Odd (Nat.card ((Work.GW2.fittingPi ({2}ᶜ : Set ℕ) ↥N).map N.subtype)))
    (hC : Subgroup.centralizer (Work.GW2.fittingPi ({2}ᶜ : Set ℕ) ↥N : Set ↥N) ≤
      Work.GW2.fittingPi ({2}ᶜ : Set ℕ) ↥N) :
    C15.Faithful V ((Work.GW2.fittingPi ({2}ᶜ : Set ℕ) ↥N).map N.subtype) := by
  have hbot : V ⊓ ((Work.GW2.fittingPi ({2}ᶜ : Set ℕ) ↥N).map N.subtype) = ⊥ :=
    L29fp_fourGroup_inf_odd_eq_bot hV hodd
  intro v hvV hvne hle
  have hvN : v ∈ N := hVN hvV
  -- `v` centralizes `A`, hence lies in the centralizer of `F_{2'}(N)` inside `↥N`
  have hvC : (⟨v, hvN⟩ : ↥N) ∈
      Subgroup.centralizer (Work.GW2.fittingPi ({2}ᶜ : Set ℕ) ↥N : Set ↥N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hyA : (y : G) ∈ (Work.GW2.fittingPi ({2}ᶜ : Set ℕ) ↥N).map N.subtype :=
      ⟨y, hy, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hyA)
  have hvA : v ∈ (Work.GW2.fittingPi ({2}ᶜ : Set ℕ) ↥N).map N.subtype :=
    ⟨_, hC hvC, rfl⟩
  have hmem : v ∈ V ⊓ ((Work.GW2.fittingPi ({2}ᶜ : Set ℕ) ↥N).map N.subtype) := ⟨hvV, hvA⟩
  rw [hbot] at hmem
  exact hvne (Subgroup.mem_bot.mp hmem)

/-! ## Statement of the leaf -/

theorem L29FaithfulProp_proved : Work.CORE2B.C15.L29FaithfulProp := by
  intro T h22 h26 h27 G hG hFin hFT hctx B V N hcs h1 h2
  classical
  -- the general facts about `F_{2'}(N) = O_{2'}(F(N))`
  obtain ⟨hnil, hodd⟩ := fittingPiIn_two_compl_isNilpotent_odd (G := G) N
  refine ⟨hnil, hodd, ?_, ?_⟩
  · -- `N ≤ N_G(F_{2'}(N))` because `F_{2'}(N) ◁ N`
    exact hcs.hyp.V_le_N.trans (le_normalizer_fittingPiIn_local ({2}ᶜ : Set ℕ) N)
  · -- faithfulness: the D16 case analysis for the coatom `N`
    have hNcyc : Work.GW2.DihOrCycSylow ↥N := L29fp_dihOrCycSylow_subtype hctx.sylow N
    have hND : Work.GW2.IsDGroup ↥N :=
      L29fp_isDGroup_of_ne_top hctx N hcs.hyp.N_ne_top hNcyc
    rcases T.d16 ↥N hFT hNcyc hND with hci | hcii | hciii | hciv
    · exact L29fp_faithful_of_centralizer_le hcs.hyp.four hcs.hyp.V_le_N hodd hci
    · -- case (ii): a central involution of `N`
      obtain ⟨z, hzC, hz2⟩ := hcii
      refine absurd (L29_case_ii_leaf (G := G) hctx B V N hcs.hyp h1 (z : G) z.2 ?_
        (Subgroup.orderOf_coe z ▸ hz2)) not_false
      intro n hn
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzC ⟨n, hn⟩)
    · -- case (iii): `O₂(N)` a four-group and `N/(O₂(N)O(N))` of order `3` or `6`
      exact (L29_d16_case_iii_excl (G := G) N V hcs.hyp.V_le_N hcs.hyp.four h1 hciii).elim
    · -- case (iv): a normal quasisimple `E ◁ N` (impossible, `N` soluble)
      obtain ⟨E, hEnorm, hEqs, -⟩ := hciv
      refine (L29fp_false_of_quasisimple_normal_of_solvable ?_ E hEqs).elim
      have hD : L27Hyp B N := L29CallSite_L27Hyp (G := G) B V N hcs h2
      exact (h27 G hFT hctx B N hD.M_ne_top hD.rel hD.not_le hD.t_mem hD.t_not_layer
        hD.sylow_nc hD.size).2.2

end Work.CORE2B
