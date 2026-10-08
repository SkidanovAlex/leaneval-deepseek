import Mathlib
import Submission.Work.PSU3.StageA.lemma2c
import Submission.Work.PSU3.StageA.centD_ne_bot
import Submission.Work.PSU3.StageA.caseC_setup
import Submission.Work.PSU3.BenderST.benderSTProp_holds
import Submission.Work.PSU3.StageA.caseC_st_structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Case a) of Peterfalvi II Ch. VI §1 forces `t * s * t = s * t * s`

The statement proved here is `Work.PSU3.StageA.tst_eq_sts_of_Q_eq_Q0sub`: in the `PSU3`
situation (`PSU3Hyp H Q t` plus `ChIIFourProp`) with a distinguished involution `s ∈ Q`
(`s² = 1`) and `r ∈ Q` satisfying the structure identity `t * s * t = r⁻¹ * t * r` of
Peterfalvi II Ch. V §2 Lemma 1 b), the collapse

  `Q = Q0sub H = ⟨Inv H⟩`

("case a)" of Peterfalvi II Ch. VI §1, `S = Q₀`) forces `t * s * t = s * t * s`,
equivalently `orderOf (s * t) = 3`.

## Proof

`V = centD H t` is non-trivial (`Work.PSU3.StageA.centD_ne_bot`), so it contains a subgroup
`P` of prime order.  Ch. V §2 Lemma 2 c) — `Work.PSU3.StageA.lemma2c`, fed with the
unconditional model statement `Work.PSU3.benderSTProp` — then says that
`orderOf (s * t)` is `3` or `5`, the case `5` being accompanied by the *non-abelianness* of
`C = Q ⊓ C_G(P)`.

In case a) every element of `Q0sub H` is central in `Q`
(`Work.PSU3.StageA.caseC_Q0sub_central`), so `Q = Q0sub H` is abelian and hence so is
`C ≤ Q`: the `orderOf (s * t) = 5` alternative is impossible.  Thus `orderOf (s * t) = 3`,
and `(s * t)³ = 1` with `s`, `t` involutions gives `t * s * t = s * t * s`.
-/

set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.PSU3.StageA

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

private theorem exists_ne_one_of_ne_bot' {G : Type} [Group G] {W : Subgroup G} (h : W ≠ ⊥) :
    ∃ w ∈ W, w ≠ 1 := by
  by_contra hcon
  push Not at hcon
  exact h (eq_bot_iff.mpr (fun x hx => Subgroup.mem_bot.mpr (hcon x hx)))

/-- A subgroup of `V = centD H t` of prime order (exists as soon as `V ≠ ⊥`). -/
private theorem exists_prime_subgroup_centD (hV : Submission.Blueprint.centD H t ≠ ⊥) :
    ∃ P : Subgroup G, P ≤ Submission.Blueprint.centD H t ∧ (Nat.card P).Prime := by
  obtain ⟨v, hv, hv1⟩ := exists_ne_one_of_ne_bot' (G := G) hV
  have hord1 : orderOf v ≠ 1 := fun h => hv1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hord1
  have hpcard : p ∣ Nat.card ↥(Submission.Blueprint.centD H t) :=
    hpdvd.trans (Subgroup.orderOf_dvd_natCard _ hv)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Submission.Blueprint.centD H t)) p hpcard
  refine ⟨Subgroup.zpowers ((x : ↥(Submission.Blueprint.centD H t)) : G), ?_, ?_⟩
  · intro y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hn]
    exact (Submission.Blueprint.centD H t).zpow_mem x.2 _
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
    exact hp

/-- `(s * t)³ = 1` for two involutions `s`, `t` is equivalent to `t * s * t = s * t * s`. -/
private theorem tst_eq_sts_of_orderOf_three {G : Type} [Group G] {s t : G} (hs : s * s = 1)
    (ht : t * t = 1) (h3 : orderOf (s * t) = 3) : t * s * t = s * t * s := by
  have hcube : (s * t) * (s * t) * (s * t) = 1 := by
    have h := pow_orderOf_eq_one (s * t)
    rw [h3] at h
    rw [pow_succ, pow_two] at h
    exact h
  have h1 : s * t * s * t = t * s := by
    have h := eq_inv_of_mul_eq_one_left hcube
    rw [mul_inv_rev] at h
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    rw [hti, hsi] at h
    simpa [mul_assoc] using h
  have hfin : s * t * s * (t * t) = t * s * t := by
    calc s * t * s * (t * t) = (s * t * s * t) * t := by group
      _ = (t * s) * t := by rw [h1]
      _ = t * s * t := by group
  rw [ht, mul_one] at hfin
  exact hfin.symm

/-- **Case a) of Peterfalvi II Ch. VI §1.**  If `Q = Q0sub H = ⟨Inv H⟩`, then the
distinguished involution `s ∈ Q` of the structure identity `t * s * t = r⁻¹ * t * r`
satisfies `t * s * t = s * t * s` (equivalently `orderOf (s * t) = 3`). -/
theorem tst_eq_sts_of_Q_eq_Q0sub {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (hQ : (Q : Set G) = Work.ThmF.Q0sub H) :
    t * s * t = s * t * s := by
  classical
  have ht : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hS.split.invol] at h
    simpa [pow_two] using h
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  -- In case a) every element of `Q0sub H = Q` is central in `Q`: `Q` is abelian.
  have hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    intro x hx y hy
    exact caseC_Q0sub_central hS hC4 x ((Set.ext_iff.mp hQ x).mp hx) y hy
  -- A subgroup of `V = centD H t` of prime order (`V ≠ ⊥` by `centD_ne_bot`).
  obtain ⟨P, hP, hPprime⟩ :=
    exists_prime_subgroup_centD (H := H) (t := t) (Work.PSU3.StageA.centD_ne_bot hS)
  -- Ch. V §2 Lemma 2 c): `orderOf (s * t)` is `3`, or `5` with `C = Q ⊓ C_G(P)` non-abelian.
  have htri := Work.PSU3.StageA.lemma2c hS hC4 Work.PSU3.benderSTProp hs hs2 hr hsr hP hPprime
  rcases htri with ⟨h3, -, -⟩ | ⟨-, hnab, -, -⟩ | ⟨h3, -, -⟩
  · exact tst_eq_sts_of_orderOf_three hss ht h3
  · exfalso
    exact hnab fun x hx y hy =>
      hQcomm x (Subgroup.mem_inf.mp hx).1 y (Subgroup.mem_inf.mp hy).1
  · exact tst_eq_sts_of_orderOf_three hss ht h3

end Work.PSU3.StageA
