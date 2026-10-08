import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.Deliverable
import Submission.Work.CORE2B.L29CallSite
import Submission.Work.CORE2B.L29_callSite_nonvacuous
import Submission.Work.CORE2B.L29_fusion_chain
import Submission.Work.CORE2B.four_subgroup_meets_pCore_two
import Submission.Work.CORE2B.L29_case_ii
import Submission.Work.CORE2B.L29_tower
import Submission.Work.CORE2B.L29_hyp_normalizer
import Submission.Work.CORE2B.isPGroup_pCoreIn_two
import Submission.Work.CORE2B.L29_case_ii_leaf
import Submission.Work.CORE2B.L29_case_iv_leaf
import Submission.Work.CORE2B.fittingPiIn_two_compl_isNilpotent_odd
import Submission.Work.CORE2B.L27su_utils
import Submission.Work.CORE2B.L29Parts
import Submission.Work.CORE2B.L29PairProp_proved
import Submission.Work.CORE2B.L29TransportProp_proved
import Submission.Work.RED.DihOrCycSubgroup
import Submission.Work.RED.DihedralSubgroup

/-!
# CORE2B leaf `L29_contra` (Bender 1981, Lemma 2.9, p. 222)

Target (`Submission/Work/CORE2B/Basic.lean`):

`L29_contra`: with `V ≤ N ≤ G`, `V` of type (2,2), `t ∈ V ≤ S`, and
`t ∈ O₂(N_G(X))` for every `1 ≠ X = [s,X] ≤ U` with `s ∈ S`, the two conditions
`V ∩ O₂(N) = 1` and `V ∩ E(N) = 1` force `False`.

## The pieces

The published proof (three lines) runs:

> Otherwise, `V` acts faithfully on `A := F_{2'}(N)`.  Then `V` contains two
> involutions, say `t` and `s`, such that `X := [s, C_A(t)] ≠ 1`.  Lying in
> `O₂(N_G(X))`, `t` centralizes `N_A(X)`, hence (by 1.1.iv) centralizes `A`, a
> contradiction.

The second sentence is **not** a consequence of "`V` acts faithfully on `A`" alone:
for `A = C₇ × C₇ × C₇`, `t = diag(1,-1,-1)`, `s = diag(1,-1,1)`, the four-group
`V = ⟨t,s⟩` acts faithfully on `A`, `C_A(t) = ⟨e₁⟩ ≠ 1`, yet `[s, C_A(t)] = 1` and
`[ts, C_A(t)] = 1`.  Filling this gap needs the D-group shape of `N` (its
`D16Prop`/`LayerProp` cases in `LocalToolkit`) **and** the fusion of involutions in the simple
group `G` (`T.fus`) — the printed "say `t` and `s`" is a *renaming* of Bender's arbitrary witness
pair `(u,v)` of 1.1(iii), legitimate only after conjugating the pair into `t` by an element of
`N_G(V)`; the group `F_{2'}(N)` is then replaced by its conjugate.  See
`NOTES_L29_contra.md` §1 and §11, and `L29_contra_h27_final.lean` for the corresponding assembly
at the call site.

## The proof (`L29_contra_proved` below)

`T.d16` applied to the D-group `↥N` (`N ≠ ⊤` by `L29Hyp`, `hctx.ih`; `T.d16`'s case (iv) is
excluded by `L29_case_iv_leaf`, which needs only `V ⊓ E(N) = ⊥`, and case (ii)/(iii) by
`L29_case_ii_leaf` / `false_of_relIndex_dvd_six`) leaves case (i)
`C_N(F_{2'}(N)) ≤ F_{2'}(N)`, which says exactly that `V` acts faithfully on `A := F_{2'}(N)`
(`L29_i_faithful`).  Then:

1. Bender 1.1(iii) (`T.c11iii`) gives `u, v ∈ V#` with `X := [⟨v⟩, C_A(u)] ≠ ⊥`
   (`L29PairProp_proved`);
2. `T.fus` gives `g ∈ N_G(V)` with `g u g⁻¹ = t`;
3. `L29TransportProp_proved` transports the pair to `(t, gvg⁻¹)` for `A^g = F_{2'}(N^g)`,
   preserving odd order, nilpotency, `V`-normalization and faithfulness;
4. Bender's printed last sentence with `u = t` (`L29_i_good_general`) now applies to `A^g` and
   gives `False`.

Steps 1–3 are separate modules of this area (`L29PairProp_proved`, `L29TransportProp_proved`);
step 4 is `L29_case_i_good_general` of `L29_case_i_good.lean`, copied below under the name
`L29_i_good_general` so that this module does not import `L27_su_not_le_h22_proved`, which
imports this one.  The helpers `L29_i_faithful`, `fourGroup_inf_odd_eq_bot`,
`not_mem_centralizer_of_faithful` and `relIndex_sup_pCoreIn_oddCoreIn_eq_index'` are likewise
small copies of lemmas proved in `L29FaithfulProp_proved` / `L29_assembly_proved`.
-/

namespace Work.CORE2B

open Subgroup
open scoped commutatorElement

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

/-- `t ≠ 1` (`BenderSetup.t_order`). -/
theorem t_ne_one (B : Work.GW2.BenderSetup G) : B.t ≠ 1 := by
  intro h
  have h2 := B.t_order
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

/-- `L29Hyp` gives `V ≤ N`, `t ∈ V`, `t ∈ N`, `V ≠ ⊥` and `V ≤ S`. -/
theorem L29Hyp_facts (B : Work.GW2.BenderSetup G) (V N : Subgroup G) (h : L29Hyp B V N) :
    V ≤ N ∧ B.t ∈ V ∧ B.t ∈ N ∧ V ≠ ⊥ ∧ V ≤ (B.S : Subgroup G) := by
  refine ⟨h.V_le_N, h.t_mem, h.V_le_N h.t_mem, ?_, h.V_le_S⟩
  intro hbot
  have ht : B.t ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact h.t_mem
  exact t_ne_one B (Subgroup.mem_bot.mp ht)

/-- A subgroup of `↥N`, normal in `↥N` and a 2-group, lies in `O₂(N)`. -/
theorem le_pCoreIn_two_of_normal_isPGroup (N : Subgroup G) (K : Subgroup ↥N)
    (hK : K.Normal) (hK2 : IsPGroup 2 K) : K.map N.subtype ≤ Work.GW2.pCoreIn 2 N := by
  haveI := hK
  have hle : K ≤ Work.GW2.pCore 2 ↥N := by
    rw [Work.GW2.pCore]
    exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hK, hK2⟩)
  rw [Work.GW2.pCoreIn]
  exact Subgroup.map_mono hle

/-- **Mechanism of Bender 1981, Lemma 2.9** (last step).  If `⟨t⟩` lies in a normal
2-subgroup of `N`, then `t ∈ O₂(N)`; since `t ∈ V` and `V ∩ O₂(N) = ⊥`, this is
impossible. -/
theorem false_of_normal_2_subgroup (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp)
    (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (V N : Subgroup G)
    (hV : L29Hyp B V N) (h1 : V ⊓ Work.GW2.pCoreIn 2 N = ⊥)
    (K : Subgroup ↥N) (hK : K.Normal) (hK2 : IsPGroup 2 K)
    (htK : (⟨B.t, hV.V_le_N hV.t_mem⟩ : ↥N) ∈ K) : False := by
  have htO2 : B.t ∈ Work.GW2.pCoreIn 2 N := by
    refine le_pCoreIn_two_of_normal_isPGroup N K hK hK2 ?_
    rw [Subgroup.mem_map]
    exact ⟨⟨B.t, hV.V_le_N hV.t_mem⟩, htK, rfl⟩
  have : B.t ∈ V ⊓ Work.GW2.pCoreIn 2 N := ⟨hV.t_mem, htO2⟩
  rw [h1] at this
  exact t_ne_one B (Subgroup.mem_bot.mp this)

/-- **Subgroups inherit `DihOrCycSylow`** (area RED, `Work.RED.DihOrCycSubgroup` fed with
`Work.RED.DihedralSubgroup`; the `Work.RED.GW2` vocabulary is definitionally equal to
`Work.GW2`). -/
theorem dihOrCycSylow_subtype {G : Type} [Group G] [Finite G] (h : Work.GW2.DihOrCycSylow G)
    (N : Subgroup G) : Work.GW2.DihOrCycSylow ↥N :=
  Work.RED.DihOrCycSubgroup (fun n _ H => Work.RED.DihedralSubgroup n H) N h

/-- A proper subgroup of a finite group has strictly smaller cardinality. -/
theorem natCard_subtype_lt_of_ne_top {G : Type} [Group G] [Finite G] (N : Subgroup G)
    (hN : N ≠ ⊤) : Nat.card ↥N < Nat.card G := by
  have h := Subgroup.card_lt_of_lt (lt_of_le_of_ne le_top hN)
  rwa [Nat.card_congr Subgroup.topEquiv.toEquiv] at h

/-- **Bender's induction hypothesis on `N`**: a proper subgroup of the minimal counterexample `G`
with cyclic-or-dihedral Sylow 2-subgroups is a D-group. -/
theorem isDGroup_of_ne_top {G : Type} [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G)
    (N : Subgroup G) (hN : N ≠ ⊤) (hNcyc : Work.GW2.DihOrCycSylow ↥N) :
    Work.GW2.IsDGroup ↥N :=
  hctx.ih ↥N (natCard_subtype_lt_of_ne_top N hN) hNcyc

/-- A non-abelian simple group has no normal subgroup of index two. -/
theorem no_index_two_normal {G : Type} [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G)
    (N : Subgroup G) (hN : N.Normal) : N.index ≠ 2 := by
  intro hidx
  haveI := hN
  rcases hctx.simple.eq_bot_or_eq_top_of_normal N with hbot | htop
  · -- `N = ⊥` forces `|G| = 2`, hence `G` abelian, contradicting `hctx.nonab`
    rw [hbot, Subgroup.index_bot] at hidx
    have hcard : Nat.card G = 2 := hidx
    have hpow : ∀ x : G, x ^ 2 = 1 := by
      intro x
      have hdvd : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
      rw [hcard] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · rw [orderOf_eq_one_iff.mp h1]; simp
      · rw [← h2]; exact pow_orderOf_eq_one x
    have hcomm : ∀ a b : G, a * b = b * a := by
      intro a b
      have ha : a⁻¹ = a := by
        have h := hpow a; rw [pow_two] at h; exact inv_eq_of_mul_eq_one_right h
      have hb : b⁻¹ = b := by
        have h := hpow b; rw [pow_two] at h; exact inv_eq_of_mul_eq_one_right h
      have hab : (a * b)⁻¹ = a * b := by
        have h := hpow (a * b); rw [pow_two] at h; exact inv_eq_of_mul_eq_one_right h
      rw [← hab, mul_inv_rev, ha, hb]
    obtain ⟨a, b, hab⟩ := hctx.nonab
    exact hab (hcomm a b)
  · rw [htop] at hidx
    simp at hidx

/-- The call-site hypotheses give `t ∉ E(N)`: `t ∈ V` and `V ∩ E(N) = ⊥`. -/
theorem t_not_mem_layerIn_of_callSite (B : Work.GW2.BenderSetup G) (V N : Subgroup G)
    (h : L29CallSite B V N) (h2 : V ⊓ Work.GW2.layerIn N = ⊥) :
    B.t ∉ Work.GW2.layerIn N := by
  intro ht
  have : B.t ∈ V ⊓ Work.GW2.layerIn N := ⟨h.hyp.t_mem, ht⟩
  rw [h2] at this
  exact t_ne_one B (Subgroup.mem_bot.mp this)

/-! ## Glue for the D16-based route to the corrected leaf

`NOTES_L29_contra.md` §10 records the plan: `h27` makes `N` soluble, and Bender's 1.6
(`T.d16`, applied to the D-group `↥N`) splits into four cases, each of which contradicts
`V ⊓ O₂(N) = ⊥`:

* case (i) `C_N(F_{2'}(N)) ≤ F_{2'}(N)`: `V` acts faithfully on `A = F_{2'}(N)`, and then
  Bender 1.1(i)/(iii)/(iv) produce `1 ≠ v ∈ V ∩ C_N(A)` (bad sub-case: `L29_fusion_chain`
  with the fusion `t ↦ s` realised in `N`; good sub-case: the normalizer tower in the
  nilpotent `A` plus `L29_tower`);
* case (ii) a central involution of `N`: `L29_case_ii`;
* case (iii) `O₂(N)` of type (2,2) with `N/(O₂(N)O(N))` of order `3` or `6`:
  `four_subgroup_meets_pCore_two`;
* case (iv) a quasisimple normal `E ◁ ↥N` with `N/E` soluble: impossible because `N` is soluble
  while quasisimple groups are not.

Cases (ii)–(iv) are formalised (see the imports); case (i) is exactly the gap in Bender's
printed proof (see `NOTES_L29_contra.md` §1 and §10). -/

/-- A coatom `N` of the subgroup lattice: every subgroup `M ≥ N` equals `N` or `⊤`. -/
theorem eq_top_or_eq_of_coatom {G : Type} [Group G] {N M : Subgroup G} (hN : IsCoatom N)
    (h : N ≤ M) : M = N ∨ M = ⊤ := by
  rcases eq_or_lt_of_le h with h' | h'
  · exact Or.inl h'.symm
  · exact Or.inr ((hN.lt_iff).mp h')

/-- **D16 case (iii) at the call site** (`four_subgroup_meets_pCore_two`): if `N/(O₂(N)O(N))`
has order dividing `6`, then `V` meets `O₂(N)`, contradicting `V ⊓ O₂(N) = ⊥`. -/
theorem false_of_relIndex_dvd_six {G : Type} [Group G] [Finite G] (N V : Subgroup G)
    (hVN : V ≤ N) (hV : Work.GW2.IsFourGroup V)
    (hix : (Work.GW2.pCoreIn 2 N ⊔ Work.GW2.oddCoreIn N).relIndex N ∣ 6)
    (h1 : V ⊓ Work.GW2.pCoreIn 2 N = ⊥) : False :=
  absurd (four_subgroup_meets_pCore_two N V hVN hV hix) (by rw [h1]; exact not_not.mpr rfl)

/-- **A quasisimple group is not soluble.**  If `E` is quasisimple then `E = [E,E]` and `E/Z(E)`
is a (nontrivial) simple group; if `E` were soluble, `E/Z(E)` would be simple *and* soluble,
hence commutative, so `E = [E,E] ≤ Z(E)` and `E/Z(E)` would be trivial. -/
theorem not_isSolvable_of_isQuasisimple {G : Type} [Group G] [Finite G] (E : Subgroup G)
    (h : Work.GW2.IsQuasisimple E) : ¬ Group.IsSolvable ↥E := by
  haveI hQ : IsSimpleGroup (↥E ⧸ Subgroup.center ↥E) := h.2
  haveI hperf : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr h.1
  haveI hnontriv : Nontrivial ↥E := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    haveI := hnt
    exact (not_subsingleton (↥E ⧸ Subgroup.center ↥E)) inferInstance
  exact Group.IsPerfect.not_isSolvable ↥E

/-- **D16 case (ii) at the call site** (`L29_case_ii`): a central involution of `N` contradicts
`V ⊓ O₂(N) = ⊥`. -/
theorem false_of_central_involution {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (N V : Subgroup G) (hSN : (B.S : Subgroup G) ≤ N) (hVN : V ≤ N)
    (hV : Work.GW2.IsFourGroup V) (hVS : V ≤ (B.S : Subgroup G)) (htV : B.t ∈ V)
    (z : G) (hz : ∀ n ∈ N, n * z = z * n) (hz2 : orderOf z = 2)
    (h1 : V ⊓ Work.GW2.pCoreIn 2 N = ⊥) : False :=
  L29_case_ii B N V hSN hVN hV hVS htV z hz hz2 h1

-- `O₂(M) ⊓ A = ⊥` for an odd-order `A` is **moved** to
-- `Submission/Work/CORE2B/L29_hyp_normalizer.lean`, which this file imports (same name,
-- `Work.CORE2B.pCoreIn_inf_eq_bot_of_odd`).

/-- **The witness at the call site.**  Combining the delegated non-vacuity lemma with the
toolkit's `hyp`: there are `s ∈ S` and `1 ≠ X ≤ U` with `X = [⟨s⟩,X]` **and**
`t ∈ O₂(N_G(X))`.  This is the input Bender's argument starts from. -/
theorem exists_witness_t_mem_pCore (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp)
    (hctx : Work.GW2.BenderCtx G) (h27 : Work.GW2.Lemma27Prop) (B : Work.GW2.BenderSetup G)
    (V N : Subgroup G) (h : L29CallSite B V N) (h2 : V ⊓ Work.GW2.layerIn N = ⊥) :
    ∃ s ∈ (B.S : Subgroup G), ∃ X : Subgroup G,
      X ≤ B.U ∧ X ≠ ⊥ ∧ ⁅Subgroup.zpowers s, X⁆ = X ∧
        B.t ∈ Work.GW2.pCoreIn 2 (Subgroup.normalizer (X : Set G)) := by
  obtain ⟨s, hs, X, hXU, hXne, hX⟩ :=
    Work.CORE2B.L29_callSite_nonvacuous T hFT hctx h27 B V N h h2
  exact ⟨s, hs, X, hXU, hXne, hX, h.hyp.hyp s X hs hXU hXne hX⟩

/-! ## The route to the target

Bender's printed proof is defective in the "bad" sub-case `C_A(t) = C_A(V)` of case (i) (see
`NOTES_L29_contra.md` §1, §11).  The defect is repaired by `T.fus`: Bender's step "`V` contains
two involutions, say `t` and `s`, such that `X := [s, C_A(t)] ≠ 1`" is the *renaming* of an
arbitrary witness pair `(u,v)` of Bender 1.1(iii) (`L29PairProp_proved`), and because `N_G(V)`
is transitive on `V#` (`T.fus`, from `IsSimpleGroup G`) the pair can be *conjugated* so that
`u = t`; the group `A = F_{2'}(N)` is replaced by the conjugate `A^g = F_{2'}(N^g)`
(`L29TransportProp_proved`), and faithfulness is unchanged because `g ∈ N_G(V)`.

The pieces used below:

* `L29PairProp_proved` (P1): Bender 1.1(iii) — a faithful four-group has a witness pair;
* `T.fus`: `N_G(V)` is transitive on `V#`;
* `L29TransportProp_proved` (P3): conjugation transport of the pair;
* `L29_i_good_general` (below): the printed last sentence with `u = t` (copied from
  `L29_case_i_good_general` under a fresh name so that this module does not import
  `L27_su_not_le_h22_proved`, which imports this one);
* D16 cases (ii)–(iv): `L29_case_ii_leaf`, `false_of_relIndex_dvd_six`, `L29_case_iv_leaf`. -/

/-- A subgroup of exponent two is commutative (copy of `fourGroup_comm` of `L29_case_i_good`). -/
private theorem fourGroup_comm' {G : Type} [Group G] (V : Subgroup G)
    (hV : Work.GW2.IsFourGroup V) : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
  intro x hxV y hyV
  have hx : x * x = 1 := by simpa [pow_two] using hV.2 x hxV
  have hy : y * y = 1 := by simpa [pow_two] using hV.2 y hyV
  have hxy : (x * y) * (x * y) = 1 := by
    simpa [pow_two] using hV.2 (x * y) (V.mul_mem hxV hyV)
  have h2 : (x * y) * (y * x) = 1 := by
    calc (x * y) * (y * x) = x * (y * y) * x := by group
      _ = x * 1 * x := by rw [hy]
      _ = x * x := by rw [mul_one]
      _ = 1 := hx
  exact (mul_left_cancel (h2.trans hxy.symm)).symm

/-- An element normalizing both `H` and `K` normalizes `H ⊓ K` (copy of `normalizer_inf_le`). -/
private theorem normalizer_inf_le' {G : Type} [Group G] (H K : Subgroup G) :
    Subgroup.normalizer (H : Set G) ⊓ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgH, hgK⟩ := hg
  rw [Subgroup.mem_normalizer_iff] at hgH hgK ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hgH x, hgK x]

/-- A subgroup of an odd-order group has odd order (copy of `odd_card_of_le`). -/
private theorem odd_card_of_le' {G : Type} [Group G] {H K : Subgroup G} (h : H ≤ K)
    (hK : Odd (Nat.card K)) : Odd (Nat.card H) := by
  have hdvd : Nat.card H ∣ Nat.card K := by
    have h1 := Subgroup.card_subgroup_dvd_card (H.subgroupOf K)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at h1
  exact Odd.of_dvd_nat hK hdvd

/-- A subgroup of a group of odd order, of exponent two, is trivial; in particular a Klein
four-group meets an odd-order subgroup trivially. -/
private theorem fourGroup_inf_odd_eq_bot {G : Type} [Group G] [Finite G] {V A : Subgroup G}
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

/-- **The `D16` case (i) conclusion implies faithfulness** (copy of
`L29fp_faithful_of_centralizer_le`): if `C_N(F_{2'}(N)) ≤ F_{2'}(N)`, then no nontrivial element
of the four-group `V ≤ N` centralizes `A := F_{2'}(N)`, because such an element would lie in
`V ⊓ C_N(A) ≤ V ⊓ A`, and `V ⊓ A = ⊥` (`V` has exponent two, `|A|` is odd). -/
theorem L29_i_faithful {G : Type} [Group G] [Finite G] {V N : Subgroup G}
    (hV : Work.GW2.IsFourGroup V) (hVN : V ≤ N)
    (hodd : Odd (Nat.card ((Work.GW2.fittingPi ({2}ᶜ : Set ℕ) ↥N).map N.subtype)))
    (hC : Subgroup.centralizer (Work.GW2.fittingPi ({2}ᶜ : Set ℕ) ↥N : Set ↥N) ≤
      Work.GW2.fittingPi ({2}ᶜ : Set ℕ) ↥N) :
    C15.Faithful V ((Work.GW2.fittingPi ({2}ᶜ : Set ℕ) ↥N).map N.subtype) := by
  have hbot : V ⊓ ((Work.GW2.fittingPi ({2}ᶜ : Set ℕ) ↥N).map N.subtype) = ⊥ :=
    fourGroup_inf_odd_eq_bot hV hodd
  intro v hvV hvne hle
  have hvN : v ∈ N := hVN hvV
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

/-- Faithfulness of `V` on `A` at the involution `t ∈ V#` is `t ∉ C_G(A)`. -/
private theorem not_mem_centralizer_of_faithful {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (V A : Subgroup G) (htV : B.t ∈ V)
    (hFaith : C15.Faithful V A) : B.t ∉ Subgroup.centralizer (A : Set G) := by
  intro hmem
  refine hFaith B.t htV (t_ne_one B) ?_
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hmem a ha

/-- **Bender's printed last sentence, with `u = t`** — the general (no `N`) form, `L29` case (i)
"good" sub-case: `V ≤ S` a Klein four-group containing `t`, `A` odd and nilpotent and
`V`-normalized, `t` not centralizing `A`, `hyp` as in `L29Hyp`; if `s ∈ V` has
`X := [⟨s⟩, C_A(t)] ≠ ⊥` then `False`.

This is a copy of `Work.CORE2B.L29_case_i_good_general` (module `L29_case_i_good`) under a fresh
name: that module imports `L27_su_not_le_h22_proved`, which imports the present module. -/
theorem L29_i_good_general {G : Type} [Group G] [Finite G] (T : Work.GW2.LocalToolkit)
    (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (V A : Subgroup G)
    (hVS : V ≤ (B.S : Subgroup G)) (htV : B.t ∈ V) (hfour : Work.GW2.IsFourGroup V)
    (hhyp : ∀ (s : G) (X : Subgroup G), s ∈ (B.S : Subgroup G) → X ≤ B.U → X ≠ ⊥ →
      ⁅Subgroup.zpowers s, X⁆ = X → B.t ∈ Work.GW2.pCoreIn 2 (normalizer (X : Set G)))
    (hAnil : Group.IsNilpotent ↥A) (hAodd : Odd (Nat.card A))
    (hVNA : V ≤ Subgroup.normalizer (A : Set G))
    (hAcen : B.t ∉ Subgroup.centralizer (A : Set G))
    (s : G) (hsV : s ∈ V)
    (hgood : ⁅Subgroup.zpowers s, (A ⊓ Subgroup.centralizer ({B.t} : Set G))⁆ ≠ ⊥) : False := by
  classical
  have hsS : s ∈ (B.S : Subgroup G) := hVS hsV
  have htNA : B.t ∈ Subgroup.normalizer (A : Set G) := hVNA htV
  have hsNA : s ∈ Subgroup.normalizer (A : Set G) := hVNA hsV
  have hstc : s * B.t = B.t * s := fourGroup_comm' V hfour s hsV B.t htV
  have hsC : s ∈ Subgroup.centralizer ({B.t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hstc
  have hsNC : s ∈ Subgroup.normalizer ((Subgroup.centralizer ({B.t} : Set G)) : Set G) :=
    (Subgroup.le_normalizer (H := Subgroup.centralizer ({B.t} : Set G))) hsC
  set K : Subgroup G := A ⊓ Subgroup.centralizer ({B.t} : Set G) with hKdef
  have hsNK : s ∈ Subgroup.normalizer (K : Set G) := by
    rw [hKdef]
    exact normalizer_inf_le' A _ ⟨hsNA, hsNC⟩
  have hsNK' : Subgroup.zpowers s ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr hsNK
  have hKodd : Odd (Nat.card K) := by
    rw [hKdef]
    exact odd_card_of_le' inf_le_left hAodd
  have hKcop : Nat.Coprime 2 (Nat.card K) := Nat.coprime_two_left.mpr hKodd
  have hs2 : s ^ 2 = 1 := hfour.2 s hsV
  have hisP : IsPGroup 2 (Subgroup.zpowers s) := by
    have hdvd : orderOf s ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hs2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2, pow_one])
  have hc11i := T.c11i G 2 (Subgroup.zpowers s) K hisP hKcop hsNK'
  set X : Subgroup G := ⁅Subgroup.zpowers s, K⁆ with hXdef
  have hXeq : ⁅Subgroup.zpowers s, X⁆ = X := by rw [hXdef]; exact hc11i.1
  have hXK : X ≤ K := by rw [hXdef]; exact le_trans le_sup_left hc11i.2.le
  have hXA : X ≤ A := le_trans hXK inf_le_left
  have hXH : X ≤ B.H := le_trans hXK inf_le_right
  have hXne : X ≠ ⊥ := by rw [hXdef, hKdef]; exact hgood
  have hXodd : Odd (Nat.card X) := odd_card_of_le' hXA hAodd
  have hXU : X ≤ B.U := L27su_odd_subgroup_le_U T hctx B X hXH hXodd
  have hcent : Subgroup.normalizer (X : Set G) ⊓ A ≤ Subgroup.centralizer ({B.t} : Set G) := by
    intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyNX, hyA⟩ := hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    set P : Subgroup G := Work.GW2.pCoreIn 2 (Subgroup.normalizer (X : Set G)) with hPdef
    have htP : B.t ∈ P := hhyp s X hsS hXU hXne hXeq
    have hcommP : B.t * y * B.t⁻¹ * y⁻¹ ∈ P := by
      have hconj : y * B.t * y⁻¹ ∈ P := conj_mem_pCoreIn hyNX htP
      have h2 : (y * B.t * y⁻¹)⁻¹ ∈ P := P.inv_mem hconj
      have h3 : y * B.t⁻¹ * y⁻¹ ∈ P := by
        rw [show (y * B.t * y⁻¹)⁻¹ = y * B.t⁻¹ * y⁻¹ from by group] at h2
        exact h2
      have h4 : B.t * (y * B.t⁻¹ * y⁻¹) ∈ P := P.mul_mem htP h3
      rwa [show B.t * (y * B.t⁻¹ * y⁻¹) = B.t * y * B.t⁻¹ * y⁻¹ from by group] at h4
    have hconjA : B.t * y * B.t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp htNA y).mp hyA
    have hcommA : B.t * y * B.t⁻¹ * y⁻¹ ∈ A := A.mul_mem hconjA (A.inv_mem hyA)
    have hbot : B.t * y * B.t⁻¹ * y⁻¹ = 1 := by
      have hmem : B.t * y * B.t⁻¹ * y⁻¹ ∈ (P ⊓ A) := ⟨hcommP, hcommA⟩
      rw [hPdef, pCoreIn_inf_eq_bot_of_odd (Subgroup.normalizer (X : Set G)) A hAodd] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hty : y * B.t = B.t * y := by
      have h : B.t * y * B.t⁻¹ = y := (mul_inv_eq_one).mp hbot
      calc y * B.t = (B.t * y * B.t⁻¹) * B.t := by rw [h]
        _ = B.t * y := by group
    exact hty
  have hAleC : A ≤ Subgroup.centralizer ({B.t} : Set G) :=
    L29_tower T.c11iv A hAnil hAodd B.t B.t_order htNA X hXA hcent
  apply hAcen
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp (hAleC ha)

/-- **Relative index plumbing**: `(O₂(N)·O(N)).relIndex N` is the index in `↥N` of
`O₂(↥N)·O(↥N)`. -/
private theorem relIndex_sup_pCoreIn_oddCoreIn_eq_index' {G : Type} [Group G] (N : Subgroup G) :
    (Work.GW2.pCoreIn 2 N ⊔ Work.GW2.oddCoreIn N).relIndex N =
      (Work.GW2.pCore 2 ↥N ⊔ Work.GW2.oddCore ↥N).index := by
  have hsup : Work.GW2.pCoreIn 2 N ⊔ Work.GW2.oddCoreIn N =
      (Work.GW2.pCore 2 ↥N ⊔ Work.GW2.oddCore ↥N).map N.subtype := by
    rw [Work.GW2.pCoreIn, Work.GW2.oddCoreIn, Subgroup.map_sup]
  rw [hsup]
  have h3 : (⊤ : Subgroup ↥N).map N.subtype = N := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have h4 : ((Work.GW2.pCore 2 ↥N ⊔ Work.GW2.oddCore ↥N).map N.subtype).relIndex
        ((⊤ : Subgroup ↥N).map N.subtype) =
      (Work.GW2.pCore 2 ↥N ⊔ Work.GW2.oddCore ↥N).relIndex (⊤ : Subgroup ↥N) :=
    Subgroup.relIndex_map_map_of_injective _ _ N.subtype_injective
  rw [h3, Subgroup.relIndex_top_right] at h4
  exact h4

/-- **Bender 1981, Lemma 2.9** (p. 222), contradiction form: with `V ≤ N ≤ G`, `V` of type (2,2),
`t ∈ V ≤ S`, and `t ∈ O₂(N_G(X))` for every `1 ≠ X = [s,X] ≤ U` with `s ∈ S`, the two
conditions `V ∩ O₂(N) = 1` and `V ∩ E(N) = 1` force `False`.

The proof is the D16 analysis of the D-group `↥N` (`T.d16`, available because `N ≠ ⊤` and
`hctx.ih`), with Bender's printed argument made correct by conjugation in the four-group:

* case (i) `C_N(F_{2'}(N)) ≤ F_{2'}(N)` makes `V` act faithfully on `A := F_{2'}(N)`
  (`L29_i_faithful`); Bender 1.1(iii) (`L29PairProp_proved`) then produces `u, v ∈ V#` with
  `X := [⟨v⟩, C_A(u)] ≠ ⊥`; `T.fus` moves `u` to `t` by `g ∈ N_G(V)`, `L29TransportProp_proved`
  conjugates the pair to `(t, gvg⁻¹)` for `A^g`, and `L29_i_good_general` (Bender's last sentence,
  which needs no `N`) gives `False`;
* case (ii), a central involution of `↥N`: `L29_case_ii_leaf`;
* case (iii), `O₂(↥N)` of type (2,2) with `↥N/(O₂·O)` of order `3` or `6`:
  `false_of_relIndex_dvd_six`;
* case (iv), a normal quasisimple subgroup of `↥N`: `L29_case_iv_leaf`. -/
theorem L29_contra_proved : Work.CORE2B.L29_contra := by
  intro T G instG instFin hFT hctx B V N h h1 h2
  have hcyc : Work.GW2.DihOrCycSylow ↥N := dihOrCycSylow_subtype hctx.sylow N
  have hD : Work.GW2.IsDGroup ↥N := isDGroup_of_ne_top hctx N h.N_ne_top hcyc
  rcases T.d16 ↥N hFT hcyc hD with hcase1 | hcase2 | hcase3 | hcase4
  · -- ## D16 case (i): `C_N(F_{2'}(N)) ≤ F_{2'}(N)`
    have hnil : Group.IsNilpotent ↥(Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) N) :=
      (fittingPiIn_two_compl_isNilpotent_odd N).1
    have hodd : Odd (Nat.card (Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) N)) :=
      (fittingPiIn_two_compl_isNilpotent_odd N).2
    -- `V` acts faithfully on `A := F_{2'}(N)`
    have hFaith : C15.Faithful V (Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) N) :=
      L29_i_faithful h.four h.V_le_N hodd hcase1
    have hVNA : V ≤ Subgroup.normalizer
        ((Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) N : Subgroup G) : Set G) :=
      h.V_le_N.trans (le_normalizer_fittingPiIn_local ({2}ᶜ : Set ℕ) N)
    -- Bender 1.1(iii): a witness pair `u, v ∈ V#` with `[⟨v⟩, C_A(u)] ≠ ⊥`
    obtain ⟨u, huV, v, hvV, hu1, hv1, hcom⟩ :=
      L29PairProp_proved T.c11iii G (Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) N) V
        hodd hVNA h.four hFaith
    -- `T.fus`: `N_G(V)` is transitive on `V#`, so some `g ∈ N_G(V)` carries `u` to `t`
    obtain ⟨n, hn2, hdih⟩ := L27su_S_dihedral hctx B
    have hno2 : ∀ M : Subgroup G, M.Normal → M.index ≠ 2 := no_index_two_normal hctx
    obtain ⟨g, hgV, hgut⟩ := (T.fus G B.S n hn2 hdih hno2).2 V h.four u huV B.t h.t_mem hu1
      (t_ne_one B)
    -- transport the pair to `(t, gvg⁻¹)` for the conjugate `A^g`
    obtain ⟨hAnil', hAodd', hVNA', hFaith', hgvgV, hcom'⟩ :=
      L29TransportProp_proved G (Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) N) V u v g B.t
        hnil hodd hVNA hFaith huV hvV hgV hgut hcom
    -- Bender's last sentence, with `u = t`
    exact L29_i_good_general T hctx B V
      (Work.GW2.conjSub g (Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) N))
      h.V_le_S h.t_mem h.four h.hyp hAnil' hAodd' hVNA'
      (not_mem_centralizer_of_faithful B V _ h.t_mem hFaith')
      (g * v * g⁻¹) hgvgV hcom'
  · -- ## D16 case (ii): a central involution of `↥N`
    obtain ⟨z, hzc, hz2⟩ := hcase2
    refine L29_case_ii_leaf hctx B V N h h1 (z : G) z.2 ?_ ?_
    · intro n hn
      have h1' : (⟨n, hn⟩ : ↥N) * z = z * ⟨n, hn⟩ := (Subgroup.mem_center_iff.mp hzc) ⟨n, hn⟩
      exact congrArg Subtype.val h1'
    · rw [Subgroup.orderOf_coe z]
      exact hz2
  · -- ## D16 case (iii): `O₂(↥N)` of type (2,2) with `↥N/(O₂·O)` of order `3` or `6`
    obtain ⟨hfour, hdisj⟩ := hcase3
    have hidx : (Work.GW2.pCore 2 ↥N ⊔ Work.GW2.oddCore ↥N).index ∣ 6 := by
      rcases hdisj with ⟨-, hcardQ⟩ | hne
      · rw [Subgroup.index_eq_card, hcardQ]
        norm_num
      · obtain ⟨e⟩ := hne
        rw [Subgroup.index_eq_card, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hix : (Work.GW2.pCoreIn 2 N ⊔ Work.GW2.oddCoreIn N).relIndex N ∣ 6 := by
      rw [relIndex_sup_pCoreIn_oddCoreIn_eq_index' N]
      exact hidx
    exact false_of_relIndex_dvd_six N V h.V_le_N h.four hix h1
  · -- ## D16 case (iv): a normal quasisimple subgroup of `↥N`
    obtain ⟨E, hEnorm, hEqs, _⟩ := hcase4
    haveI := hEnorm
    exact L29_case_iv_leaf hctx B V N h h2 E hEqs

/-- **Corollary** (the disjunction form of the contract, Bender 1981, Lemma 2.9): `V` meets
`O₂(N)` or `E(N)` non-trivially.  This is `L29_two_core_or_layer` obtained from the contradiction
form above via `Deliverable.l29_two_core_or_layer_of_contra`; `Lemma29Prop` follows with
`lemma29_of_leaves`. -/
theorem L29_two_core_or_layer_of_contra_proved (T : Work.GW2.LocalToolkit) :
    Work.CORE2B.L29_two_core_or_layer :=
  l29_two_core_or_layer_of_contra T L29_contra_proved

end Work.CORE2B
