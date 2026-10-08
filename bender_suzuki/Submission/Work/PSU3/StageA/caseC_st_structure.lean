/-
# `Work.PSU3.StageA.caseC_st_structure`

Case c) of Peterfalvi II, Ch. VI §1 (p. 259): in a simple group with split rank-one data
`H = Q ⋊ D`, `t ∉ H` an involution, if `|Q| = q³` (`q = |Q₀| = |Q0sub H|`) and
`W = C_V(K) = C_D(Inv H) ≠ 1`, then the structure identity of Ch. V §2 Lemma 1 b) has order `3`:

  `t s t = s t s`  (equivalently `orderOf (s * t) = 3`)

for the distinguished involution `s ∈ Q` (with partner `r ∈ Q`, `t s t = r⁻¹ t r`).

This is the "case c)" output of Ch. VI §1 used by the frame construction of Ch. VII; it is the
last input of `Work.PSU3.StageA.coarseFrame_exists`, and `Work.PSU3.StageA.caseC_data` now
derives the case-c data `|Q| = q³ ∧ orderOf (s*t) = 3 ∧ W ≠ 1` from it.

## Mathematical route (no Feit–Thompson; Higman + Ch. V §1, §2)

The modules below rest on `Work.PSU3.benderSTProp` (Higman's count of the model groups) and on
`Work.PSU3.StageA.lemma2cHig` (Ch. V §2 Lemma 2 c): for any subgroup `P ≤ V = C_D(t)` of prime
order there is a trichotomy.  Writing `C = C_Q(P)` and `ℓ = |C_{Q₀}(P)|`, either

  1. `orderOf (s*t) = 3`, `C` abelian, `|C| = ℓ`, or
  2. `orderOf (s*t) = 5`, `C` non-abelian of order `ℓ²` (Suzuki type A), or
  3. `orderOf (s*t) = 3`, `|C| = ℓ³`.

Choosing `P ≤ W` of prime order (`P` exists because `W ≠ 1`) we have `C = Q₀ = Q0sub H` and
`ℓ = q`: `P` centralises `Q₀` (Ch. II §4 Prop. 4) and, by the **semiregularity of `W` on
`Q ∖ Q₀`** proved here (`W_semireg`), every element of `Q` centralised by `W` lies in `Q₀`.  So
cases 2 and 3 are impossible (they would give `q = q²` resp. `q = q³` with `q ≥ 4`), and case 1
gives `orderOf (s * t) = 3`, hence `t s t = s t s`.

The semiregularity is the delicate part and follows Ch. V §1 case 1 / Ch. VI §1 case c):

* `W ≠ 1` gives `Ksub H t = Kset H t` cyclic and `Q` a Suzuki `2`-group with `Z(Q) = Q₀`
  (`Q` is not abelian, since an abelian `Q` forces `W = 1` — the classical odd-order automorphism
  argument, reproduced here in §3), so `|Q| = |Z(Q)|³ = q³`.
* For `w ∈ W#` the conjugation action `A` of `w` on `Q` has odd order, commutes with the cyclic
  `K`-action `ξ` (whose order is `q - 1`), and fixes `Z(Q)` pointwise.
* `Work.PSU3.StageA.suzuki_odd_order_fixed_eq_center` (Higman's squares/cocycle argument) then
  shows that every fixed point of `A` is central: `C_Q(W) ≤ Z(Q) = Q₀`.

## Files

Nothing here modifies an existing module; the lemmas are `private` to this file except the
target `caseC_st_structure`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.caseC_setup
import Submission.Work.PSU3.StageA.lemma2cHig
import Submission.Work.PSU3.benderSTProp
import Submission.Work.PSU3.StageA.suzuki_odd_order_fixed_eq_center
import Submission.Work.PSU3.StageA.W_centralizes_Q0sub
import Submission.Work.ThmF.ChV12.prop1a
import Submission.Work.RankOneUniqueness.closure_Q_t_eq_top
import Submission.Work.Higman.typeB

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open scoped commutatorElement

namespace Work.PSU3.StageA

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-! ## §1  Elementary helpers -/

private theorem exists_ne_one_of_ne_bot' {G : Type} [Group G] {W : Subgroup G} (h : W ≠ ⊥) :
    ∃ w ∈ W, w ≠ 1 := by
  by_contra hcon
  push Not at hcon
  exact h (eq_bot_iff.mpr (fun x hx => Subgroup.mem_bot.mpr (hcon x hx)))

private theorem mem_Q0sub_iff_sq (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : ChIIFourProp) :
    ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1 := by
  intro x
  constructor
  · intro hx
    have h := caseC_mem_Q0sub_iff hS hC4 (x : G) hx
    exact Subtype.ext (by simpa using h)
  · intro hx
    have h1 : (x : G) * (x : G) = 1 := by
      have h := congrArg (fun z : ↥Q => (z : G)) hx
      simpa using h
    rcases eq_or_ne (x : G) 1 with h | h
    · rw [h]; exact (Work.ThmF.Q0sub H).one_mem
    · have hdvd : orderOf (x : G) ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact h1
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h2 | h2
      · exact absurd (orderOf_eq_one_iff.mp h2) h
      · exact Work.ThmF.Q0_le_Q0sub H
          (Work.ThmF.mem_Q0_iff.mpr (Or.inl ⟨hS.split.le x.2, h2⟩))

private theorem ht_mul_self (hS : Work.PSU3.PSU3Hyp H Q t) : t * t = 1 := by
  have h := pow_orderOf_eq_one t
  rw [hS.split.invol] at h
  simpa [pow_two] using h

private theorem s_mul_self {s : G} (hs2 : orderOf s = 2) : s * s = 1 := by
  have h := pow_orderOf_eq_one s
  rw [hs2] at h
  simpa [pow_two] using h

private theorem tst_eq_sts_of {s t : G} (hs : s * s = 1) (ht : t * t = 1)
    (h3 : orderOf (s * t) = 3) : t * s * t = s * t * s := by
  have h1 : (s * t) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (s * t)
    rwa [h3] at this
  have h2 : (s * t) * (s * t) * (s * t) = 1 := by
    have h := h1
    rw [pow_succ, pow_two] at h
    exact h
  have hq : s * t * s * t = t * s := by
    have h := eq_inv_of_mul_eq_one_left h2
    rw [mul_inv_rev] at h
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    rw [hti, hsi] at h
    simpa [mul_assoc] using h
  have hfin : s * t * s * (t * t) = t * s * t := by
    calc s * t * s * (t * t) = (s * t * s * t) * t := by group
      _ = (t * s) * t := by rw [hq]
      _ = t * s * t := by group
  rw [ht, mul_one] at hfin
  exact hfin.symm

/-- A subgroup of `W H t` of prime order. -/
private theorem exists_prime_subgroup_W {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G}
    (hW : Work.ThmF.W H t ≠ ⊥) :
    ∃ P : Subgroup G, P ≤ Work.ThmF.W H t ∧ (Nat.card P).Prime := by
  obtain ⟨w, hwW, hw1⟩ := exists_ne_one_of_ne_bot' (G := G) hW
  have hord1 : orderOf w ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hord1
  have hpcard : p ∣ Nat.card ↥(Work.ThmF.W H t) :=
    hpdvd.trans (Subgroup.orderOf_dvd_natCard (Work.ThmF.W H t) hwW)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Work.ThmF.W H t)) p hpcard
  refine ⟨Subgroup.zpowers ((x : ↥(Work.ThmF.W H t)) : G), ?_, ?_⟩
  · intro y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hn]
    exact (Work.ThmF.W H t).zpow_mem x.2 _
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
    exact hp


/-! ## §2  Odd-order automorphisms of abelian `2`-groups fixing `Ω₁`  -/

private theorem odd_order_mulAut_eq_one_of_fixes_sqOne' {A : Type} [CommGroup A]
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


/-! ## §3  `D` acts faithfully on `Q` -/

private theorem eq_one_of_centralizes_Q' (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : ChIIFourProp) {d : G} (hd : d ∈ Submission.Blueprint.twoPoint H t)
    (hdc : ∀ q ∈ Q, d * q = q * d) : d = 1 := by
  have hsplit : IsSplitRankOne H Q t := hS.split
  obtain ⟨u, hu, hcu⟩ := (hC4 G hS.situation H hsplit.stronglyEmbedded t hsplit.invol
    hsplit.not_mem).2.1
  have huQ : u ∈ Q := caseC_involutions_subset_Q hsplit hu
  have hdu : d ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hdc u huQ)
  have hdD : d ∈ Submission.Blueprint.centD H t := by
    rw [hcu]; exact ⟨hd, hdu⟩
  have hdt : d * t = t * d :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hdD).2
  haveI : IsSimpleGroup G := hS.simple
  have htop : Subgroup.closure ((Q : Set G) ∪ {t}) = ⊤ :=
    Work.RankOneUniqueness.closure_Q_t_eq_top hsplit
  have hle : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [← htop]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y (hy | hy)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hdc y hy).symm
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr hdt.symm
  have hcent : d ∈ Subgroup.center G :=
    Subgroup.mem_center_iff.mpr
      (fun g => Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g)))
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hS.simple (Subgroup.center G) (inferInstance) with h | h
  · exact Subgroup.mem_bot.mp (h ▸ hcent)
  · exfalso
    have hHle : H ≤ Subgroup.center G := by rw [h]; exact le_top
    have hHnorm : H.Normal := ⟨fun a ha b => by
      have hcomm : b * a = a * b := Subgroup.mem_center_iff.mp (hHle ha) b
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact ha⟩
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hS.simple H hHnorm with hb | ht
    · have heven : Even (Nat.card H) := hsplit.stronglyEmbedded.2.1
      rw [hb, Subgroup.card_bot] at heven
      exact absurd heven (by norm_num)
    · exact hsplit.stronglyEmbedded.1 ht

/-! ## §4  Abelian `Q` forces `W = ⊥`, so `Q` is non-abelian -/

private theorem W_eq_bot_of_abelian' (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : ChIIFourProp)
    (hab : Submission.Blueprint.IsAbelianSubgroup Q) : Work.ThmF.W H t = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro w hw
  have hwD : w ∈ Submission.Blueprint.twoPoint H t :=
    Work.ThmF.centD_le_twoPoint (H := H) t (Work.ThmF.W_le_centD H t hw)
  have hwN : w ∈ Subgroup.normalizer (Q : Set G) := hS.split.normal (Subgroup.mem_inf.mp hwD).1
  have hoddw : Odd (orderOf w) :=
    Odd.of_dvd_nat (Work.ThmF.split_odd_card_twoPoint hS.split)
      (Subgroup.orderOf_dvd_natCard (Submission.Blueprint.twoPoint H t) hwD)
  have hdvd : orderOf (conjOnQ w hwN) ∣ orderOf w := by
    rw [orderOf_dvd_iff_pow_eq_one]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp only [conjOnQ_pow_coe, pow_orderOf_eq_one, one_mul, mul_one, inv_one, MulAut.one_apply]
  have hodd_α : Odd (orderOf (conjOnQ w hwN)) := Odd.of_dvd_nat hoddw hdvd
  letI : CommGroup ↥Q := { (inferInstance : Group ↥Q) with
    mul_comm := fun a b => Subtype.ext (hab a.1 a.2 b.1 b.2) }
  have hconj : conjOnQ w hwN = 1 := by
    refine odd_order_mulAut_eq_one_of_fixes_sqOne' (A := ↥Q) ?_ _ hodd_α ?_
    · intro x; exact hS.two x
    · intro x hx
      have hxQ0 : (x : G) ∈ Work.ThmF.Q0sub H := (mem_Q0sub_iff_sq hS hC4 x).mpr hx
      have hval : ((conjOnQ w hwN x : ↥Q) : G) = (x : G) := by
        rw [conjOnQ_coe]
        rw [W_centralizes_Q0sub hS hC4 w hw (x : G) hxQ0, mul_assoc, mul_inv_cancel, mul_one]
      exact Subtype.ext hval
  have hcent : ∀ q ∈ Q, w * q = q * w := by
    intro q hq
    have h := (conjOnQ_eq_one_iff w hwN).mp hconj q hq
    have h2 := congrArg (fun z => z * w) h
    simpa [mul_assoc] using h2
  exact Subgroup.mem_bot.mpr (eq_one_of_centralizes_Q' hS hC4 hwD hcent)

private theorem not_abelian_of_W_ne_bot' (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : ChIIFourProp)
    (hW : Work.ThmF.W H t ≠ ⊥) : ¬ Submission.Blueprint.IsAbelianSubgroup Q :=
  fun hab => hW (W_eq_bot_of_abelian' hS hC4 hab)

/-! ## §5  Higman's centre facts for a Suzuki `2`-group -/

private theorem suzuki_center_facts' {P : Type} [Group P] [Finite P]
    (hHig : Submission.Blueprint.HigmanProp) (hSuz : Work.Higman.IsSuzuki2Grp P) :
    (∀ x : P, x ^ 2 ∈ Subgroup.center P) ∧
    (∀ z : P, z ∈ Subgroup.center P → z ^ 2 = 1) ∧
    (∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center P) := by
  have htwo : Submission.Blueprint.IsSuzukiTwoGroup P :=
    Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp.mpr ⟨hSuz⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (hHig P htwo).2.1
  · intro z hz
    exact ((hHig P htwo).1 z).mp hz
  · intro x y
    have hc := (hHig P htwo).2.2.1
    have h1 : ⁅x, y⁆ ∈ commutator P :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [hc] at h1
    exact h1

/-! ## §6  The `FpfXi` structure for the `K`-action `ξ` -/

private theorem fpfXi_xi (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) (hW : Work.ThmF.W H t ≠ ⊥)
    (hZ : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3) :
    Work.Higman.FpfXi (caseC_xi hS hC4 hW) := by
  classical
  have hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q := not_abelian_of_W_ne_bot' hS hC4 hW
  have hSuz : Work.Higman.IsSuzuki2Grp ↥Q := caseC_isSuzuki2Grp hS hC4 hnab hZ hW
  have hcenter : Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q :=
    caseC_center_subgroupOf hS hHig hZ hSuz
  have hZcard : Nat.card ↥(Subgroup.center ↥Q) = Nat.card ↥(Work.ThmF.Q0sub H) := by
    have h1 : Nat.card ↥(Subgroup.center ↥Q)
        = Nat.card ↥((Work.ThmF.Q0sub H).subgroupOf Q) :=
      Nat.card_congr (MulEquiv.subgroupCongr hcenter).toEquiv
    rw [h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Q0sub_le_Q hS.split)).toEquiv
  -- the generator of `K = Ksub H t`, as an element of `G`
  set k : G := ((caseC_gen hS hC4 hW : ↥(Work.ThmF.Ksub H t)) : G) with hk
  have hkK : k ∈ Work.ThmF.Ksub H t := (caseC_gen hS hC4 hW).2
  have hkKset : k ∈ Work.ThmF.Kset H t := caseC_gen_mem_Kset hS hC4 hW
  have hkN : k ∈ Subgroup.normalizer (Q : Set G) := caseC_gen_mem_normalizer hS hC4 hW
  have hkord : orderOf k = Nat.card ↥(Work.ThmF.Ksub H t) := by
    rw [hk, Subgroup.orderOf_coe, caseC_gen_orderOf hS hC4 hW]
  have hξdef : caseC_xi hS hC4 hW = conjOnQ k hkN := by
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    have h := caseC_xi_pow_coe hS hC4 hW 1 y
    simp only [pow_one] at h
    rw [h, conjOnQ_coe, hk]
  -- `|K| = |Q₀| - 1`
  have hKsub_card : Nat.card ↥(Work.ThmF.Ksub H t) = Nat.card ↥(Work.ThmF.Q0sub H) - 1 := by
    rw [caseC_card_Ksub hS hC4 hW, caseC_card_Q0sub_eq hS hC4]
    omega
  have hdvd1 : orderOf (caseC_xi hS hC4 hW) ∣ orderOf k := by
    rw [orderOf_dvd_iff_pow_eq_one, hξdef]
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    rw [conjOnQ_pow_coe, pow_orderOf_eq_one]
    simp
  have hdvd2 : orderOf k ∣ orderOf (caseC_xi hS hC4 hW) := by
    rw [orderOf_dvd_iff_pow_eq_one]
    set m := orderOf (caseC_xi hS hC4 hW) with hm
    have hξm : (caseC_xi hS hC4 hW) ^ m = 1 := by rw [hm]; exact pow_orderOf_eq_one _
    have hkmD : k ^ m ∈ Submission.Blueprint.twoPoint H t :=
      Work.ThmF.Ksub_le_twoPoint (H := H) t ((Work.ThmF.Ksub H t).pow_mem hkK m)
    have hkmcent : ∀ q ∈ Q, k ^ m * q = q * k ^ m := by
      intro q hq
      have h1 : ((caseC_xi hS hC4 hW) ^ m) ⟨q, hq⟩ = ⟨q, hq⟩ := by rw [hξm]; rfl
      have h2 := congrArg (fun z : ↥Q => (z : G)) h1
      rw [caseC_xi_pow_coe, ← hk] at h2
      have h3 := congrArg (fun z => z * k ^ m) h2
      simpa [mul_assoc] using h3
    exact eq_one_of_centralizes_Q' hS hC4 hkmD hkmcent
  have hord_eq : orderOf (caseC_xi hS hC4 hW) = Nat.card ↥(Subgroup.center ↥Q) - 1 := by
    have h1 : orderOf (caseC_xi hS hC4 hW) = Nat.card ↥(Work.ThmF.Ksub H t) :=
      (Nat.dvd_antisymm hdvd1 hdvd2).trans hkord
    rw [h1, hKsub_card]
    congr 1
    exact hZcard.symm
  refine ⟨?_, hord_eq, ?_⟩
  · rw [hZcard]; exact hcard
  · intro n hn y hy
    have hkne : k ^ n ≠ 1 := by
      intro h1
      apply hn
      rw [hξdef]
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      rw [conjOnQ_pow_coe, h1]
      simp
    have hcomm : (y : G) * k ^ n = k ^ n * (y : G) := by
      have h2 := congrArg (fun z : ↥Q => (z : G)) hy
      rw [caseC_xi_pow_coe, ← hk] at h2
      have h3 := congrArg (fun z => z * k ^ n) h2
      simpa [mul_assoc] using h3.symm
    have hKsetmem : k ^ n ∈ Work.ThmF.Kset H t := by
      rw [← (caseC_Ksub_cyc hS hC4 hW).1]
      exact (Work.ThmF.Ksub H t).pow_mem hkK n
    have hx1 := Work.ThmF.ChV12.prop1a hS.situation hC4 H Q t hS.split (k ^ n) hKsetmem hkne
      (y : G) y.2 hcomm
    exact Subtype.ext hx1

/-- Conjugation automorphisms agree on equal group elements. -/
private theorem conjOnQ_congr {Q : Subgroup G} {g g' : G} (h : g = g')
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (hg' : g' ∈ Subgroup.normalizer (Q : Set G)) :
    conjOnQ g hg = conjOnQ g' hg' := by
  subst h
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  rfl

/-! ## §7  `W` acts semiregularly on `Q ∖ Q₀` -/

private theorem W_semireg (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) (hW : Work.ThmF.W H t ≠ ⊥)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3) :
    ∀ w ∈ Work.ThmF.W H t, w ≠ 1 → ∀ x ∈ Q, w * x = x * w → x ∈ Work.ThmF.Q0sub H := by
  classical
  have hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q := not_abelian_of_W_ne_bot' hS hC4 hW
  have hZ : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1 := mem_Q0sub_iff_sq hS hC4
  have hSuz : Work.Higman.IsSuzuki2Grp ↥Q := caseC_isSuzuki2Grp hS hC4 hnab hZ hW
  have hξ : Work.Higman.FpfXi (caseC_xi hS hC4 hW) := fpfXi_xi hS hC4 hHig hW hZ hcard
  obtain ⟨hsq, hzsq, hcomm⟩ := suzuki_center_facts' hHig hSuz
  have hcenter : Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q :=
    caseC_center_subgroupOf hS hHig hZ hSuz
  intro w hwW hw1 x hxQ hxcomm
  have hwD : w ∈ Submission.Blueprint.twoPoint H t :=
    Work.ThmF.centD_le_twoPoint (H := H) t (Work.ThmF.W_le_centD H t hwW)
  have hwN : w ∈ Subgroup.normalizer (Q : Set G) := hS.split.normal (Subgroup.mem_inf.mp hwD).1
  set A : MulAut ↥Q := conjOnQ w hwN with hAdef
  have hAcoe : ∀ y : ↥Q, ((A y : ↥Q) : G) = w * (y : G) * w⁻¹ := by
    intro y; rw [hAdef]; rfl
  -- the generator of `K` and the definition of `ξ`
  set k : G := ((caseC_gen hS hC4 hW : ↥(Work.ThmF.Ksub H t)) : G) with hk
  have hkKset : k ∈ Work.ThmF.Kset H t := caseC_gen_mem_Kset hS hC4 hW
  have hkN : k ∈ Subgroup.normalizer (Q : Set G) := caseC_gen_mem_normalizer hS hC4 hW
  have hξdef : caseC_xi hS hC4 hW = conjOnQ k hkN := by
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    have h := caseC_xi_pow_coe hS hC4 hW 1 y
    simp only [pow_one] at h
    rw [h, conjOnQ_coe, hk]
  have hwk : w * k = k * w := ((Work.ThmF.le_W_iff.mp hwW).2 k hkKset).symm
  -- `A` commutes with `ξ`
  have hAc : A * caseC_xi hS hC4 hW = caseC_xi hS hC4 hW * A := by
    rw [hAdef, hξdef]
    have hwkN : w * k ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).mul_mem hwN hkN
    have hkwN : k * w ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).mul_mem hkN hwN
    calc conjOnQ w hwN * conjOnQ k hkN
        = conjOnQ (w * k) hwkN := (conjOnQ_mul w k hwN hkN hwkN).symm
      _ = conjOnQ (k * w) hkwN := conjOnQ_congr hwk hwkN hkwN
      _ = conjOnQ k hkN * conjOnQ w hwN := conjOnQ_mul k w hkN hwN hkwN
  -- `A` fixes `Z(Q) = Q₀`
  have hAfix : ∀ z ∈ Subgroup.center ↥Q, A z = z := by
    intro z hz
    have hzQ0 : (z : G) ∈ Work.ThmF.Q0sub H := by
      have hz' : z ∈ (Work.ThmF.Q0sub H).subgroupOf Q := hcenter ▸ hz
      exact Subgroup.mem_subgroupOf.mp hz'
    have hzc := W_centralizes_Q0sub hS hC4 w hwW (z : G) hzQ0
    apply Subtype.ext
    rw [hAcoe, hzc]
    group
  -- `A ≠ 1`
  have hA1 : A ≠ 1 := by
    intro hA1
    have hforall : ∀ y ∈ Q, w * y * w⁻¹ = y := by
      intro y hy
      have h1 : ((A ⟨y, hy⟩ : ↥Q) : G) = ((⟨y, hy⟩ : ↥Q) : G) := by
        have h := congrArg (fun f : MulAut ↥Q => ((f ⟨y, hy⟩ : ↥Q) : G)) hA1
        simpa using h
      rwa [hAcoe] at h1
    have hcent : ∀ q ∈ Q, w * q = q * w := by
      intro q hq
      have h := hforall q hq
      have h2 := congrArg (fun z => z * w) h
      simpa [mul_assoc] using h2
    exact hw1 (eq_one_of_centralizes_Q' hS hC4 hwD hcent)
  -- `A` has odd order
  have hoddw : Odd (orderOf w) := by
    have h1 : orderOf (⟨w, hwD⟩ : ↥(Submission.Blueprint.twoPoint H t))
        ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) :=
      orderOf_dvd_natCard (⟨w, hwD⟩ : ↥(Submission.Blueprint.twoPoint H t))
    have h2 : orderOf (⟨w, hwD⟩ : ↥(Submission.Blueprint.twoPoint H t)) = orderOf w :=
      (Subgroup.orderOf_coe (⟨w, hwD⟩ : ↥(Submission.Blueprint.twoPoint H t))).symm
    rw [← h2]
    exact (Work.ThmF.split_odd_card_twoPoint hS.split).of_dvd_nat h1
  have hoddA : Odd (orderOf A) := by
    have hdvd : orderOf A ∣ orderOf w := by
      rw [orderOf_dvd_iff_pow_eq_one, hAdef]
      apply MulEquiv.ext
      intro y
      apply Subtype.ext
      rw [conjOnQ_pow_coe, pow_orderOf_eq_one]
      simp
    exact hoddw.of_dvd_nat hdvd
  -- the Suzuki core
  have hcore := Work.PSU3.StageA.suzuki_odd_order_fixed_eq_center hSuz hξ hsq hzsq hcomm
    hoddA hAc hAfix hA1
  have hfix : A ⟨x, hxQ⟩ = ⟨x, hxQ⟩ := by
    apply Subtype.ext
    rw [hAcoe, hxcomm]
    group
  have hmem := hcore ⟨x, hxQ⟩ hfix
  rw [hcenter] at hmem
  exact Subgroup.mem_subgroupOf.mp hmem

/-! ## §8  The case-c structure identity -/

/-- **Case c) of Peterfalvi II, Ch. VI §1.**  If `|Q| = q³` with `q = |Q0sub H|` and
`W = C_V(K) ≠ 1`, then the distinction involution `s ∈ Q` of the structure identity with `t`
has `t s t = s t s` (equivalently `orderOf (s * t) = 3`). -/
theorem caseC_st_structure {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) {s r : G} (hs : s ∈ Q) (hs2 : orderOf s = 2)
    (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (hW : Work.ThmF.W H t ≠ ⊥)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3) :
    t * s * t = s * t * s := by
  classical
  -- a subgroup of `W` of prime order
  obtain ⟨P, hPW, hPprime⟩ := exists_prime_subgroup_W (G := G) hW
  have hP : P ≤ Submission.Blueprint.centD H t := hPW.trans (Work.ThmF.W_le_centD H t)
  -- Ch. V §2 Lemma 2 c) (the three cases) for this `P`
  have htri := Work.PSU3.StageA.lemma2cHig hS hC4 Work.PSU3.benderSTProp hs hs2 hr hsr hP hPprime
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPprime
    exact Nat.not_prime_one hPprime
  -- `C_G(P) ⊓ Q = Q₀` and `C_G(P) ⊓ Q₀ = Q₀`
  have hCQ0 : Q ⊓ Subgroup.centralizer (P : Set G) = Work.ThmF.Q0sub H := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨hyQ, hycent⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨p, hpP, hp1⟩ := exists_ne_one_of_ne_bot' hPne
      exact W_semireg hS hC4 hHig hW hcard p (hPW hpP) hp1 y hyQ
        (Subgroup.mem_centralizer_iff.mp hycent p hpP)
    · intro y hy
      exact Subgroup.mem_inf.mpr ⟨Q0sub_le_Q hS.split hy, by
        rw [Subgroup.mem_centralizer_iff]
        intro p hp
        exact W_centralizes_Q0sub hS hC4 p (hPW hp) y hy⟩
  have hℓQ0 : Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) = Work.ThmF.Q0sub H := by
    refine le_antisymm inf_le_left ?_
    intro y hy
    exact Subgroup.mem_inf.mpr ⟨hy, by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      exact W_centralizes_Q0sub hS hC4 p (hPW hp) y hy⟩
  have hq4 : 4 ≤ Nat.card ↥(Work.ThmF.Q0sub H) := by
    obtain ⟨n, hn2, hncard⟩ := caseC_Q0sub_card hS hC4 hW
    rw [hncard]
    exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn2
  rcases htri with h | h | h
  · exact tst_eq_sts_of (s_mul_self hs2) (ht_mul_self hS) h.1
  · exfalso
    obtain ⟨-, -, hcardC, -⟩ := h
    rw [hCQ0, hℓQ0] at hcardC
    have hzero : Nat.card ↥(Work.ThmF.Q0sub H) * (Nat.card ↥(Work.ThmF.Q0sub H) - 1) = 0 := by
      nlinarith [hcardC]
    have hpos : 0 < Nat.card ↥(Work.ThmF.Q0sub H) * (Nat.card ↥(Work.ThmF.Q0sub H) - 1) :=
      Nat.mul_pos (by omega) (by omega)
    omega
  · exact tst_eq_sts_of (s_mul_self hs2) (ht_mul_self hS) h.1


end Work.PSU3.StageA
