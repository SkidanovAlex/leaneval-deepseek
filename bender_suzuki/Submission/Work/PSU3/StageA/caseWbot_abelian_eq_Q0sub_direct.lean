import Mathlib
import Submission.Work.PSU3.StageA.lemma2cHig
import Submission.Work.PSU3.StageA.centD_ne_bot
import Submission.Work.PSU3.BenderST.benderSTProp_holds
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.ChV12.prop1a
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.PSU3.StageA.centD_eq_centralizer_s
import Submission.Work.PSU3.StageA.distinguished_exists
import Submission.Work.Higman.Main
import Submission.Work.PSU3.StageA.caseC_not_abelian
import Submission.Work.PSU3.StageA.caseC_CQ_le_Q0sub_of_abelian

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.caseWbot_abelian_eq_Q0sub_direct`

This is `Work.PSU3.StageA.caseWbot_abelian_eq_Q0sub` with the two hypotheses `hFT` and `hW` that
its proof never uses deleted, so that it can be used without the odd order theorem.

The imports differ from the original file only in omitting
`Submission.Work.PSU3.StageA.caseC_data`: that module (correctly) depends on the present lemma, so
importing it here would create an import cycle.  Nothing in the proof below needs it.

## Route

Assume `Q` abelian.  `V = centD H t = C_D(t) ≠ ⊥` (`centD_ne_bot`, from `¬ IsZassenhaus H`), so
`V` contains a subgroup `P` of prime order; as `P ≤ D` has odd order, `P ≠ ⊥` and `|P|` is odd.

* `caseC_CQ_le_Q0sub_of_abelian` (Ch. V §2 Lemma 2 (c) in the abelian branch): for such a `P`,
  `C_Q(P) = Q ⊓ C_G(P) ≤ Q0sub H`.
* `caseWbot_false_of_abelian_of_ne_Q0sub`, proved below: if moreover `Q ≠ Q₀`, then `Q ⊋ Q₀`
  supplies `z ∈ Q` of order `≥ 4`; `v := z^(2^(j-2))` has order `4`, so `v * v` is an involution
  of `H`, and `D` is transitive on `Inv(H)` (`DTransitiveInv`), so for some `d ∈ D` the element
  `w := d v d⁻¹ ∈ Q` satisfies `w * w = s`, where `s` is the distinguished involution with
  `V = C_D(s)` (`centD_eq_centralizer_s`).  Since `Q` is abelian, the set of solutions of
  `y * y = s` inside `Q` is exactly the coset `w · Q₀`, of cardinality `q = |Q₀|`, prime to the odd
  prime `|P|`; it is `P`-stable (all of `P ≤ V` fixes `s`), so some `P`-fixed point `y` of it lies
  in `C_Q(P) ≤ Q₀`, yet `y * y = s ≠ 1` — contradicting `Q₀ = Ω₁(Q)`.

Consequently `Q ≠ Q₀` is impossible, which is the statement.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs

namespace Work.PSU3.StageA

open Submission.Blueprint

/-- **Ch. VI §1 (case 1), the final step.**  If `Q` is abelian, `Q ≠ Q₀ = Q0sub H`, and some
prime-order subgroup `P ≤ V = centD H t` satisfies `C_Q(P) ≤ Q₀`, then we reach a contradiction:
`Q ⊋ Q₀` gives `z ∈ Q` of order `≥ 4`, so `v := z^(2^(j-2))` has order `4` and `v²` is an
involution of `H`; `D` is transitive on `Inv(H)`, so `w := d v d⁻¹` (with `d ∈ D`) lies in `Q` and
satisfies `w * w = s`; the `P`-set `{y ∈ Q | y * y = s} = w · Q₀` has cardinality `|Q₀|` prime to
`|P|`, so it contains a `P`-fixed point `y ∈ C_Q(P) ≤ Q₀` with `y * y = s ≠ 1`, impossible since
`Q₀` consists of involutions. -/
private theorem caseWbot_false_of_abelian_of_ne_Q0sub_direct {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t s : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hab : Submission.Blueprint.IsAbelianSubgroup Q)
    (hne : (Q : Set G) ≠ (Work.ThmF.Q0sub H : Set G))
    (hs : s ∈ Q) (hs2 : orderOf s = 2)
    (hVeq : Submission.Blueprint.centD H t =
      Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G))
    {P : Subgroup G} (hPle : P ≤ Submission.Blueprint.centD H t)
    (hPprime : (Nat.card P).Prime)
    (hCQ : Q ⊓ Subgroup.centralizer (P : Set G) ≤ Work.ThmF.Q0sub H) : False := by
  classical
  have hsplit : IsSplitRankOne H Q t := hS.split
  have hH : IsStronglyEmbedded H := hsplit.stronglyEmbedded
  have ht2 : orderOf t = 2 := hsplit.invol
  have htH : t ∉ H := hsplit.not_mem
  have hcomm := Work.ThmF.L5.involutions_commute hS.situation hC4 hsplit
  have hQ0el := Work.ThmF.L5.Q0sub_elementary hcomm
  have hQ0mem := mem_Q0sub_iff_sq_eq_one hS hC4
  have hsInv : s ∈ involutions (H : Set G) := ⟨hsplit.le hs, hs2⟩
  set C : Subgroup G := Subgroup.centralizer (P : Set G) with hCdef
  have hCQ_le_Q0 : Q ⊓ C ≤ Work.ThmF.Q0sub H := hCQ
  have hQne : Q ≠ Work.ThmF.Q0sub H := fun hce => hne (by rw [hce])
  haveI : Fact (Nat.Prime (Nat.card ↥P)) := ⟨hPprime⟩
  -- (8) `Q ⊋ Q₀`, so there is `z ∈ Q` of order `4`
  obtain ⟨z, hzQ, hznot⟩ : ∃ z ∈ Q, z ∉ (Work.ThmF.Q0sub H : Set G) := by
    by_contra hcon
    push_neg at hcon
    exact hQne (le_antisymm hcon (Work.PSU3.StageA.Q0sub_le_Q hsplit))
  obtain ⟨j, hj⟩ := Work.PSU3.StageA.exists_orderOf_eq_two_pow_of_mem_isPGroup hS.two hzQ
  have hz2ne : z * z ≠ 1 := by
    intro hzz
    exact hznot ((hQ0mem ⟨z, hzQ⟩).mpr (Subtype.ext hzz))
  have hj2 : 2 ≤ j := by
    by_contra hcon
    have hjle : j ≤ 1 := by omega
    have hdvd : 2 ^ j ∣ 2 := by
      interval_cases j <;> norm_num
    have hzpow : z ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hj]
      exact hdvd
    exact hz2ne (by rwa [pow_two] at hzpow)
  set v : G := z ^ (2 ^ (j - 2)) with hvdef
  have hvQ : v ∈ Q := Q.pow_mem hzQ _
  have hv2 : v * v = z ^ (2 ^ (j - 1)) := by
    rw [hvdef, ← pow_add]
    congr 1
    have hjm : j - 1 = (j - 2) + 1 := by omega
    rw [hjm, pow_succ]
    ring_nf
  have hv4 : (v * v) * (v * v) = 1 := by
    rw [hv2, ← pow_add]
    have hexp : 2 ^ (j - 1) + 2 ^ (j - 1) = 2 ^ j := by
      have hjm : j = (j - 1) + 1 := by omega
      conv_rhs => rw [hjm, pow_succ]
      ring_nf
    rw [hexp]
    rw [← hj]
    exact pow_orderOf_eq_one z
  have hv2ne : v * v ≠ 1 := by
    intro hcontra
    rw [hv2] at hcontra
    have hdvd : orderOf z ∣ 2 ^ (j - 1) := orderOf_dvd_iff_pow_eq_one.mpr hcontra
    rw [hj] at hdvd
    have hle : 2 ^ j ≤ 2 ^ (j - 1) := Nat.le_of_dvd (by positivity) hdvd
    have h2 : j ≤ j - 1 := Nat.pow_le_pow_iff_right (by norm_num) |>.mp hle
    omega
  have hv2Inv : v * v ∈ involutions (H : Set G) := by
    refine ⟨hsplit.le (Q.mul_mem hvQ hvQ), ?_⟩
    have h2 : orderOf (v * v) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hv4)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hv2ne
    · exact h
  obtain ⟨d, hdD, hds⟩ := Work.ThmF.Bender.DTransitiveInv hH ht2 htH (v * v) hv2Inv s hsInv
  have hdH : d ∈ H := (Subgroup.mem_inf.mp hdD).1
  set w : G := d * v * d⁻¹ with hwdef
  have hwQ : w ∈ Q := (Subgroup.mem_normalizer_iff.mp (hsplit.normal hdH) v).mp hvQ
  have hw2 : w * w = s := by
    rw [hwdef]
    calc (d * v * d⁻¹) * (d * v * d⁻¹) = d * (v * v) * d⁻¹ := by group
      _ = s := hds
  -- (9) the `P`-set `{y ∈ Q | y² = s} = w · Q₀` has a `P`-fixed point
  set Yset : Set G := {y' : G | y' ∈ Q ∧ y' * y' = s} with hYsetdef
  have hYset_image : Yset = Set.image (fun y : G => w * y) (Work.ThmF.Q0sub H : Set G) := by
    ext y'
    constructor
    · intro hy'
      obtain ⟨hy'Q, hy'sq⟩ := hy'
      have h1 : y' * w⁻¹ = w⁻¹ * y' := hab y' hy'Q w⁻¹ (Q.inv_mem hwQ)
      refine ⟨w⁻¹ * y', ?_, ?_⟩
      · have hgoal : (w⁻¹ * y') * (w⁻¹ * y') = 1 := by
          calc (w⁻¹ * y') * (w⁻¹ * y') = w⁻¹ * (y' * w⁻¹) * y' := by group
            _ = w⁻¹ * (w⁻¹ * y') * y' := by rw [← h1]
            _ = (w⁻¹ * w⁻¹) * (y' * y') := by group
            _ = (w * w)⁻¹ * s := by
                rw [hy'sq, show w⁻¹ * w⁻¹ = (w * w)⁻¹ from by group]
            _ = s⁻¹ * s := by rw [hw2]
            _ = 1 := inv_mul_cancel s
        exact (hQ0mem ⟨w⁻¹ * y', Q.mul_mem (Q.inv_mem hwQ) hy'Q⟩).mpr (Subtype.ext hgoal)
      · show w * (w⁻¹ * y') = y'
        group
    · rintro ⟨y, hy, rfl⟩
      refine ⟨Q.mul_mem hwQ (Work.PSU3.StageA.Q0sub_le_Q hsplit hy), ?_⟩
      have hcommw : y * w = w * y := hab y (Work.PSU3.StageA.Q0sub_le_Q hsplit hy) w hwQ
      calc (w * y) * (w * y) = w * (y * w) * y := by group
        _ = w * (w * y) * y := by rw [hcommw]
        _ = (w * w) * (y * y) := by group
        _ = s := by rw [hw2, hQ0el.1 y hy, mul_one]
  have hYcard' : Yset.ncard = Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [hYset_image, Set.ncard_image_of_injective _ (fun a b h => mul_left_cancel h)]
    exact (Nat.card_coe_set_eq (Work.ThmF.Q0sub H : Set G)).symm
  have hYinv : ∀ (g : ↥P), ∀ y' ∈ Yset, ((g : G) * y' * (g : G)⁻¹) ∈ Yset := by
    intro g y' hy'
    obtain ⟨hy'Q, hy'sq⟩ := hy'
    have hgD : (g : G) ∈ twoPoint H t := (Subgroup.mem_inf.mp (hPle g.2)).1
    have hgH : (g : G) ∈ H := (Subgroup.mem_inf.mp hgD).1
    have hgs : (g : G) * s * (g : G)⁻¹ = s := by
      have hmem : (g : G) ∈ centD H t := hPle g.2
      rw [hVeq] at hmem
      have hmem' : s * (g : G) = (g : G) * s :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hmem).2 s (Set.mem_singleton s)
      rw [← hmem', mul_assoc, mul_inv_cancel, mul_one]
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hsplit.normal hgH) y').mp hy'Q, ?_⟩
    calc ((g : G) * y' * (g : G)⁻¹) * ((g : G) * y' * (g : G)⁻¹)
        = (g : G) * (y' * y') * (g : G)⁻¹ := by group
      _ = (g : G) * s * (g : G)⁻¹ := by rw [hy'sq]
      _ = s := hgs
  letI : MulAction ↥P ↥Yset :=
    { smul := fun g y' => ⟨(g : G) * (y' : G) * (g : G)⁻¹, hYinv g y' y'.2⟩
      one_smul := fun y' => Subtype.ext (by
        show ((1 : ↥P) : G) * (y' : G) * ((1 : ↥P) : G)⁻¹ = (y' : G)
        simp)
      mul_smul := fun g h y' => Subtype.ext (by
        show ((g : G) * (h : G)) * (y' : G) * ((g : G) * (h : G))⁻¹ =
          (g : G) * ((h : G) * (y' : G) * (h : G)⁻¹) * (g : G)⁻¹
        group) }
  have hpndvd : ¬ Nat.card ↥P ∣ Yset.ncard := by
    rw [hYcard']
    have hQ0p : IsPGroup 2 ↥(Work.ThmF.Q0sub H) := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro w
      exact ⟨1, Subtype.ext (by simpa [pow_two] using hQ0el.1 (w : G) w.2)⟩
    obtain ⟨kq, hkq⟩ := IsPGroup.iff_card.mp hQ0p
    have hpodd : Odd (Nat.card ↥P) :=
      Odd.of_dvd_nat (Work.ThmF.split_odd_card_twoPoint hsplit)
        (card_dvd_card_of_le P (twoPoint H t) (le_trans hPle inf_le_left))
    intro hpd
    rw [hkq] at hpd
    have hp2 : Nat.card ↥P ∣ 2 := hPprime.dvd_of_dvd_pow hpd
    rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with h | h
    · exact hPprime.ne_one h
    · rw [h] at hpodd
      exact absurd hpodd (by norm_num)
  obtain ⟨y₀, hy₀fix⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card
    (IsPGroup.card : IsPGroup (Nat.card ↥P) ↥P) ↥Yset hpndvd
  have hy₀fix' : ∀ g : ↥P, (g : G) * (y₀ : G) * (g : G)⁻¹ = (y₀ : G) := fun g =>
    congrArg Subtype.val (MulAction.mem_fixedPoints.mp hy₀fix g)
  have hy₀C : (y₀ : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h := hy₀fix' ⟨g, hg⟩
    calc (g : G) * (y₀ : G) = ((g : G) * (y₀ : G) * (g : G)⁻¹) * (g : G) := by group
      _ = (y₀ : G) * (g : G) := by rw [h]
  have hy₀Q : (y₀ : G) ∈ Q := y₀.2.1
  have hy₀sq : (y₀ : G) * (y₀ : G) = s := y₀.2.2
  have hy₀Q0 : (y₀ : G) ∈ Work.ThmF.Q0sub H :=
    hCQ_le_Q0 ⟨hy₀Q, hy₀C⟩
  have hfinal : (y₀ : G) * (y₀ : G) = 1 := by
    have h := (hQ0mem ⟨(y₀ : G), hy₀Q⟩).mp hy₀Q0
    exact congrArg Subtype.val h
  have hs1 : s ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  exact hs1 (hy₀sq ▸ hfinal)

/-- **Ch. VI §1 case 1 without Feit–Thompson or the `W = ⊥` hypothesis.**

`Work.PSU3.StageA.caseWbot_abelian_eq_Q0sub` proves `IsAbelianSubgroup Q → (Q : Set G) = Q0sub H`
for `PSU3Hyp` data, but carries two hypotheses it never uses: `hFT : FeitThompsonProp` and
`hW : W H t = ⊥` (its own docstring says "the proof below does not use `hW` (nor `hFT`)").

This is the same statement with those two unused hypotheses deleted, so that it can be used
without the odd order theorem. -/
theorem caseWbot_abelian_eq_Q0sub_direct {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hab : Submission.Blueprint.IsAbelianSubgroup Q) :
    (Q : Set G) = Work.ThmF.Q0sub H := by
  by_contra hne
  -- the distinguished involution `s ∈ Q` of the structure identity, whose centraliser in `D`
  -- is `V = C_D(t)`
  obtain ⟨s, hs, hs2, r, hr, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  have hVeq : Submission.Blueprint.centD H t =
      Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G) :=
    Work.PSU3.StageA.centD_eq_centralizer_s hS hs hs2 hr hsr
  -- `V ≠ ⊥`, so `V` has a subgroup `P` of odd prime order
  have hVne : Submission.Blueprint.centD H t ≠ ⊥ := Work.PSU3.StageA.centD_ne_bot hS
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
  have hcardV : Nat.card ↥(Submission.Blueprint.centD H t) ≠ 1 := by
    intro hc
    haveI : Subsingleton ↥(Submission.Blueprint.centD H t) := (Nat.card_eq_one_iff_unique.mp hc).1
    exact hx (Subsingleton.elim x 1)
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hcardV
  haveI : Fact (Nat.Prime p) := ⟨hpprime⟩
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Submission.Blueprint.centD H t))
    p hpdvd
  set P : Subgroup G := Subgroup.zpowers (y : G) with hPdef
  have hPle : P ≤ Submission.Blueprint.centD H t := Subgroup.zpowers_le.mpr y.2
  have hPcard : Nat.card ↥P = p := by
    rw [hPdef, Nat.card_zpowers, Subgroup.orderOf_coe, hyord]
  have hPprime : (Nat.card P).Prime := by rw [hPcard]; exact hpprime
  -- Ch. V §2 Lemma 2 (c) in the abelian branch: `C_Q(P) ≤ Q₀`
  have hCQ : Q ⊓ Subgroup.centralizer (P : Set G) ≤ Work.ThmF.Q0sub H :=
    caseC_CQ_le_Q0sub_of_abelian hS hC4 hab hPle hPprime
  exact caseWbot_false_of_abelian_of_ne_Q0sub_direct hS hC4 hab hne hs hs2 hVeq hPle hPprime hCQ

end Work.PSU3.StageA
