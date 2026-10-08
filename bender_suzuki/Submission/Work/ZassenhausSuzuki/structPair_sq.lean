import Mathlib
import Submission.Work.ZassenhausSuzuki.frel_center
import Submission.Work.ZassenhausSuzuki.twoPoint_card_eq_involutions
import Submission.Work.ZassenhausSuzuki.ncard_involutions_of_mulEquiv
import Submission.Work.ZassenhausSuzuki.SzA.ncard_orderOf_eq_two
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmG.rankOne_index

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- `A(K,θ)` has `|K| ^ 2` elements. -/
theorem natCard_szA {K : Type*} [Field K] (θ : K ≃+* K) :
    Nat.card (SzA K θ) = Nat.card K * Nat.card K := by
  rw [← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun x => (x.a, x.b)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun x => by cases x; rfl
      right_inv := fun p => by cases p; rfl }

/-- No square in `ZMod 3` is `-1`. -/
private lemma zmod3_sq_add_one_ne_zero : ∀ x : ZMod 3, x * x + 1 ≠ 0 := by decide

set_option maxHeartbeats 800000 in
set_option linter.unusedVariables false in
private theorem three_not_dvd_card_G_aux {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K} (hθ : IsTitsTheta θ)
    (e : Q ≃* SzA K θ) : ¬ 3 ∣ Nat.card G := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hQfin : Finite ↥Q := Subtype.finite
  haveI hSzAfin : Finite (SzA K θ) := Finite.of_injective e.symm e.symm.injective
  haveI hKfin : Finite K :=
    Finite.of_injective (fun k : K => (⟨k, 0⟩ : SzA K θ))
      (fun a b hab => by simpa using congrArg SzA.a hab)
  -- `|Q| = |K| ^ 2`
  have hQcard : Nat.card Q = Nat.card K * Nat.card K :=
    (Nat.card_congr e.toEquiv).trans (natCard_szA θ)
  -- `|D| = |K| - 1`
  have hDcard : Nat.card ↥(twoPoint H t) = Nat.card K - 1 := by
    rw [twoPoint_card_eq_involutions hsplit hzass h2]
    rw [show (involutions (Q : Set G)) = {x : G | x ∈ Q ∧ orderOf x = 2} from rfl]
    rw [ncard_involutions_of_mulEquiv (Q := Q) e]
    exact SzA.ncard_orderOf_eq_two θ
  -- `|G| = (|K|² + 1) · |K|² · (|K| - 1)`
  have hGcard : Nat.card G = (Nat.card Q + 1) * Nat.card Q * (Nat.card K - 1) := by
    calc Nat.card G = Nat.card ↥H * H.index := (Subgroup.card_mul_index H).symm
      _ = (Nat.card Q * (Nat.card K - 1)) * (Nat.card Q + 1) := by
            rw [Work.ThmF.card_H_eq_mul_of_data (Work.ThmF.IsSplitRankOne.toData hsplit),
              hDcard, Work.ThmG.rankOne_index hsplit]
      _ = (Nat.card Q + 1) * Nat.card Q * (Nat.card K - 1) := by
            rw [Nat.mul_comm (Nat.card Q * (Nat.card K - 1)) (Nat.card Q + 1),
              Nat.mul_assoc]
  -- `3` divides none of the three factors
  have h3Q : ¬ 3 ∣ Nat.card Q := by
    obtain ⟨k, hk⟩ := isPGroup_iff_card_dvd_pow.mp h2
    intro h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow (h3.trans hk)) (by norm_num)
  have h3sq : ∀ q : ℕ, ¬ 3 ∣ q * q + 1 := by
    intro q h
    have h1 : ((q * q + 1 : ℕ) : ZMod 3) = 0 := by
      have h' : (3 : ℤ) ∣ ((q * q + 1 : ℕ) : ℤ) := by exact_mod_cast h
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q * q + 1 : ℕ) : ℤ) 3).mpr h'
      simpa using this
    push_cast at h1
    exact zmod3_sq_add_one_ne_zero (q : ZMod 3) h1
  have h3Q1 : ¬ 3 ∣ Nat.card Q + 1 := by
    rw [hQcard]
    exact h3sq (Nat.card K)
  -- the Tits condition rules out `3 ∣ |K| - 1` via the cube roots of unity
  have h3D : ¬ 3 ∣ Nat.card K - 1 := by
    intro h3
    have hKu : 3 ∣ Nat.card Kˣ := by rwa [Nat.card_units]
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 hKu
    have hζ3 : (ζ : K) ^ 3 = 1 := by
      have h : ζ ^ 3 = 1 := by
        have := pow_orderOf_eq_one ζ
        rwa [hζ] at this
      simpa using congrArg (fun u : Kˣ => (u : K)) h
    have hζne : (ζ : K) ≠ 1 := by
      intro h
      have h1 : orderOf ζ = 1 := orderOf_eq_one_iff.mpr (Units.ext h)
      rw [hζ] at h1
      exact absurd h1 (by norm_num)
    have hquad : (ζ : K) ^ 2 + (ζ : K) + 1 = 0 := by
      have hmul : ((ζ : K) - 1) * ((ζ : K) ^ 2 + (ζ : K) + 1) = 0 := by
        have h : ((ζ : K) - 1) * ((ζ : K) ^ 2 + (ζ : K) + 1) = (ζ : K) ^ 3 - 1 := by
          ring
        rw [h, hζ3, sub_self]
      rcases mul_eq_zero.mp hmul with h | h
      · exact absurd (sub_eq_zero.mp h) hζne
      · exact h
    have hyquad : (θ (ζ : K)) ^ 2 + θ (ζ : K) + 1 = 0 := by
      have hmul : ((θ (ζ : K)) - 1) * ((θ (ζ : K)) ^ 2 + θ (ζ : K) + 1) = 0 := by
        have h : ((θ (ζ : K)) - 1) * ((θ (ζ : K)) ^ 2 + θ (ζ : K) + 1)
            = (θ (ζ : K)) ^ 3 - 1 := by ring
        have h3 : (θ (ζ : K)) ^ 3 = 1 := by rw [← map_pow, hζ3, map_one]
        rw [h, h3, sub_self]
      have hne : θ (ζ : K) ≠ 1 := fun h => hζne (θ.injective (by rw [h, map_one]))
      rcases mul_eq_zero.mp hmul with h | h
      · exact absurd (sub_eq_zero.mp h) hne
      · exact h
    have hy : (θ (ζ : K)) ^ 2 + θ (ζ : K) = 1 := by
      have h := eq_neg_of_add_eq_zero_left hyquad
      rwa [CharTwo.neg_eq] at h
    have ha : (ζ : K) ^ 2 + (ζ : K) = 1 := by
      have h := eq_neg_of_add_eq_zero_left hquad
      rwa [CharTwo.neg_eq] at h
    have hkey : (θ (ζ : K) + (ζ : K)) * (θ (ζ : K) + (ζ : K) + 1) = 0 := by
      have h1 : (θ (ζ : K) + (ζ : K)) * (θ (ζ : K) + (ζ : K) + 1)
          = (θ (ζ : K) + (ζ : K)) ^ 2 + (θ (ζ : K) + (ζ : K)) := by ring
      rw [h1, CharTwo.add_sq]
      have h2 : (θ (ζ : K)) ^ 2 + (ζ : K) ^ 2 + (θ (ζ : K) + (ζ : K))
          = ((θ (ζ : K)) ^ 2 + θ (ζ : K)) + ((ζ : K) ^ 2 + (ζ : K)) := by ring
      rw [h2, hy, ha, CharTwo.add_self_eq_zero]
    have ha2ne : (ζ : K) ^ 2 ≠ (ζ : K) := by
      intro h
      have h1 : (ζ : K) * ((ζ : K) - 1) = 0 := by
        have h' : (ζ : K) * ((ζ : K) - 1) = (ζ : K) ^ 2 - (ζ : K) := by ring
        rw [h', h, sub_self]
      rcases mul_eq_zero.mp h1 with h2 | h2
      · rw [h2] at hζ3; norm_num at hζ3
      · exact hζne (sub_eq_zero.mp h2)
    rcases mul_eq_zero.mp hkey with hy' | hy'
    · have hyeq : θ (ζ : K) = (ζ : K) := by
        have h := eq_neg_of_add_eq_zero_left hy'
        rwa [CharTwo.neg_eq] at h
      have h2 : θ (θ (ζ : K)) = (ζ : K) := by rw [hyeq, hyeq]
      rw [hθ.2] at h2
      exact ha2ne h2
    · have hsum : θ (ζ : K) + (ζ : K) = 1 := by
        have h := eq_neg_of_add_eq_zero_left hy'
        rwa [CharTwo.neg_eq] at h
      have hyeq : θ (ζ : K) = (ζ : K) + 1 := by
        calc θ (ζ : K) = (θ (ζ : K) + (ζ : K)) + (ζ : K) := by
              rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
          _ = 1 + (ζ : K) := by rw [hsum]
          _ = (ζ : K) + 1 := by rw [add_comm]
      have h2pow : θ (θ (ζ : K)) = θ ((ζ : K) + 1) := congrArg θ hyeq
      have h3 : θ (θ (ζ : K)) = (ζ : K) := by
        rw [h2pow, map_add, map_one, hyeq, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [hθ.2] at h3
      exact ha2ne h3
  -- combine
  intro h3
  rw [hGcard] at h3
  rcases Nat.prime_three.dvd_mul.mp h3 with h | h
  · rcases Nat.prime_three.dvd_mul.mp h with h' | h'
    · exact h3Q1 h'
    · exact h3Q h'
  · exact h3D h

/-- **The structure element squares to the structure involution** (HB XI 10.7 (b): the
Sz-specific sharpening of the structure equation).  Let `(s, ρ)` be the structure-identity pair
of a split rank-one Zassenhaus configuration (`t s t = ρ t ρ⁻¹`, `s ∈ Inv(Q)`, `ρ ∈ Q`, unique
by `Work.ThmF.ChV12.structureIdentity`), with `Q ≃* A(K,θ)` for a Tits endomorphism `θ`
(so `Q` is the non-abelian Suzuki 2-group, excluding the `PGL(2,2^f)` configuration where the
structure equation has `ρ = s`), through which the two-point stabiliser acts by the standard
torus.  Then `s = ρ * ρ`.

Suggested route (all the ingredients are already in `frel_center.lean`): with `w := s * t`,
`structPair_conj_st` gives `ρ * w * ρ⁻¹ = w * w`, and `odd_orderOf_struct_st` gives that `w` has
odd order; hence `ρ` normalises `U := ⟨w⟩` and acts on it by squaring.  The involutions of `Q`
are its central elements (`SzA.sq_eq`/`SzA.mem_center_iff` transported along `e`), and any
involution `x ≠ 1` of `Q` in the normaliser of `U` that fixes a nontrivial element of the cyclic
group `U` of odd order commutes with a generator of `U`, hence with `w`, hence lies in
`C_G(w) ∩ Q`.  So it suffices to show `C_G(w) ∩ Q = 1` (for `w = s * t`: `q ∈ Q` commutes with
`s * t` iff `t q t = q`, since `s ∈ Z(Q)`; and `t q t = q` forces `q ∈ Q ∩ Q^t = 1`) and then
that the two involutions `ρ ^ 2` and `s` of `N(U) ∩ Q` coinide. -/ 
theorem structPair_sq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K} (hθ : Work.ZassenhausSuzuki.IsTitsTheta θ)
    (e : Q ≃* Work.ZassenhausSuzuki.SzA K θ)
    (htorus : Work.ZassenhausSuzuki.TorusCoords K θ H Q t e)
    (h2 : IsPGroup 2 Q) :
    (Work.ZassenhausSuzuki.structPair hsplit).2 * (Work.ZassenhausSuzuki.structPair hsplit).2
      = (Work.ZassenhausSuzuki.structPair hsplit).1 := by
  classical
  set s : G := (structPair hsplit).1 with hsdef
  set ρ : G := (structPair hsplit).2 with hρdef
  obtain ⟨hsQ, hs2, hρQ, hstruct⟩ := structPair_spec hsplit
  have ht2 : t * t = 1 := ht_mul_self hsplit
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hs_sq : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs_sq
  have hstruct' : t * s * t = ρ * t * ρ⁻¹ := by simpa [htinv] using hstruct
  -- `s` is central in `Q`: in `A(K,θ)` its first coordinate vanishes
  have hsa : (e ⟨s, hsQ⟩).a = 0 := by
    refine a_eq_zero_of_sq_eq_one θ _ ?_
    have h : (⟨s, hsQ⟩ : ↥Q) * ⟨s, hsQ⟩ = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      exact hs_sq
    rw [← map_mul, h, map_one]
  have hscen : ∀ q : G, q ∈ Q → s * q = q * s := by
    intro q hq
    have h1 : e ⟨s, hsQ⟩ = (⟨0, (e ⟨s, hsQ⟩).b⟩ : SzA K θ) := by ext <;> simp [hsa]
    have h2 : (⟨s, hsQ⟩ : ↥Q) * ⟨q, hq⟩ = ⟨q, hq⟩ * ⟨s, hsQ⟩ := by
      apply e.injective
      rw [map_mul, map_mul, h1]
      ext <;> simp [add_comm]
    have := congrArg (fun z : ↥Q => (z : G)) h2
    simpa [Subgroup.coe_mul] using this
  -- `w = s * t` satisfies `ρ w ρ⁻¹ = w²` and `s w s⁻¹ = w⁻¹`
  set w : G := s * t with hwdef
  have hconjw : ρ * w * ρ⁻¹ = w ^ 2 := by
    rw [hwdef, pow_two]
    calc ρ * (s * t) * ρ⁻¹ = ρ * s * t * ρ⁻¹ := by group
      _ = s * ρ * t * ρ⁻¹ := by rw [← hscen ρ hρQ]
      _ = s * (ρ * t * ρ⁻¹) := by group
      _ = s * (t * s * t) := by rw [hstruct']
      _ = (s * t) * (s * t) := by group
  have hs_inv_w : s * w * s⁻¹ = w⁻¹ := by
    rw [hwdef, hsinv, mul_inv_rev, htinv, hsinv]
    calc s * (s * t) * s = (s * s) * (t * s) := by group
      _ = 1 * (t * s) := by rw [hs_sq]
      _ = t * s := one_mul _
  -- `A(K,θ)` has exponent `4`, so `ρ ^ 4 = 1`
  have hρ4 : ρ ^ 4 = 1 := by
    have h1 : (e ⟨ρ, hρQ⟩) ^ 4 = 1 := by
      have hsq : (e ⟨ρ, hρQ⟩) ^ 2
          = (⟨0, (e ⟨ρ, hρQ⟩).a * θ (e ⟨ρ, hρQ⟩).a⟩ : SzA K θ) := by
        rw [pow_two]; exact SzA.sq_eq θ _
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, pow_two]
      ext <;> simp [SzA.mul_a, SzA.mul_b, SzA.one_a, SzA.one_b, CharTwo.add_self_eq_zero]
    have h2' : (⟨ρ, hρQ⟩ : ↥Q) ^ 4 = 1 := by
      apply e.injective
      rw [map_pow, h1, map_one]
    simpa using congrArg (fun q : ↥Q => (q : G)) h2'
  -- `ρ` acts on `⟨w⟩` by squaring, so `w ^ 16 = w`
  have hgen : ∀ k : ℕ, ρ ^ k * w * (ρ ^ k)⁻¹ = w ^ 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : ρ ^ (k + 1) * w * (ρ ^ (k + 1))⁻¹
          = ρ ^ k * (ρ * w * ρ⁻¹) * (ρ ^ k)⁻¹ := by rw [pow_succ]; group
      have h2 : ρ ^ k * (ρ * w * ρ⁻¹) * (ρ ^ k)⁻¹ = w ^ 2 ^ k * w ^ 2 ^ k := by
        rw [hconjw]
        calc ρ ^ k * w ^ 2 * (ρ ^ k)⁻¹
            = (ρ ^ k * w * (ρ ^ k)⁻¹) * (ρ ^ k * w * (ρ ^ k)⁻¹) := by
              rw [pow_two]; group
          _ = w ^ 2 ^ k * w ^ 2 ^ k := by rw [ih]
      rw [h1, h2, ← pow_two, ← pow_mul, mul_comm, pow_succ']
  have hw16 : w ^ 16 = w := by
    have h := hgen 4
    simp only [hρ4, one_mul, inv_one, mul_one] at h
    rw [show (2 : ℕ) ^ 4 = 16 from by norm_num] at h
    exact h.symm
  have hw15 : w ^ 15 = 1 := by
    have h : w ^ 15 * w = 1 * w := by
      rw [one_mul, ← pow_succ]
      exact hw16
    exact mul_right_cancel h
  have hdiv : orderOf w ∣ 15 := orderOf_dvd_iff_pow_eq_one.mpr hw15
  have hwne : w ≠ 1 := by
    intro h
    have h1 : t = s⁻¹ * (s * t) := by group
    rw [← hwdef, h, mul_one, hsinv] at h1
    exact hsplit.not_mem (h1 ▸ hsplit.le hsQ)
  have hord_ne_one : orderOf w ≠ 1 := fun h => hwne (orderOf_eq_one_iff.mp h)
  -- `3 ∤ |G|` forces `orderOf w = 5`
  have h3notdvd : ¬ 3 ∣ orderOf w := by
    intro h3
    exact three_not_dvd_card_G_aux hsplit hzass h2 hθ e (h3.trans (orderOf_dvd_natCard w))
  have h5dvd : orderOf w ∣ 5 := by
    have hcop : Nat.Coprime (orderOf w) 3 :=
      ((Nat.prime_three.coprime_iff_not_dvd).mpr h3notdvd).symm
    exact hcop.dvd_of_dvd_mul_right (by rw [show 5 * 3 = 15 by norm_num]; exact hdiv)
  have hord5 : orderOf w = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).mp h5dvd with h | h
    · exact absurd h hord_ne_one
    · exact h
  have hw5 : w ^ 5 = 1 := by
    have h := pow_orderOf_eq_one w
    rwa [hord5] at h
  have hw4 : w ^ 4 = w⁻¹ := by
    have h : w ^ 4 * w = 1 := by rw [← pow_succ]; exact hw5
    calc w ^ 4 = w ^ 4 * w * w⁻¹ := by group
      _ = 1 * w⁻¹ := by rw [h]
      _ = w⁻¹ := one_mul _
  have hρ2_inv_w : ρ ^ 2 * w * (ρ ^ 2)⁻¹ = w⁻¹ := by
    have h := hgen 2
    rw [show 2 ^ 2 = 4 by norm_num, hw4] at h
    exact h
  -- `ρ ^ 2 * s` centralises `w`, and `C_G(w) ∩ Q = 1`
  have hcomm : (ρ ^ 2 * s) * w * (ρ ^ 2 * s)⁻¹ = w := by
    rw [mul_inv_rev]
    calc ρ ^ 2 * s * w * (s⁻¹ * (ρ ^ 2)⁻¹)
        = ρ ^ 2 * (s * w * s⁻¹) * (ρ ^ 2)⁻¹ := by group
      _ = ρ ^ 2 * w⁻¹ * (ρ ^ 2)⁻¹ := by rw [hs_inv_w]
      _ = (ρ ^ 2 * w * (ρ ^ 2)⁻¹)⁻¹ := by group
      _ = (w⁻¹)⁻¹ := by rw [hρ2_inv_w]
      _ = w := inv_inv w
  have hCbot : ∀ q : G, q ∈ Q → q * w * q⁻¹ = w → q = 1 := by
    intro q hq hqw
    have hqw' : q * (s * t) * q⁻¹ = s * t := by rw [← hwdef]; exact hqw
    have hqsq : s * (q * t * q⁻¹) = s * t := by
      have h1 : q * (s * t) * q⁻¹ = s * (q * t * q⁻¹) := by
        calc q * (s * t) * q⁻¹ = q * s * t * q⁻¹ := by group
          _ = s * q * t * q⁻¹ := by rw [← hscen q hq]
          _ = s * (q * t * q⁻¹) := by group
      rw [← h1]; exact hqw'
    have hq_t : q * t * q⁻¹ = t := mul_left_cancel hqsq
    have hqt : q * t = t * q := by
      calc q * t = (q * t * q⁻¹) * q := by group
        _ = t * q := by rw [hq_t]
    have htqt : t * q * t⁻¹ = q := by
      calc t * q * t⁻¹ = q * t * t⁻¹ := by rw [hqt]
        _ = q := by rw [mul_assoc, mul_inv_cancel, mul_one]
    have hqHt : q ∈ Submission.Blueprint.conj t H :=
      Subgroup.mem_map.mpr ⟨q, hsplit.le hq, by simpa [MulAut.conj_apply] using htqt⟩
    have hmem : q ∈ Q ⊓ twoPoint H t := ⟨hq, hsplit.le hq, hqHt⟩
    rw [hsplit.inf_eq] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hρ2sQ : ρ ^ 2 * s ∈ Q := Q.mul_mem (Q.pow_mem hρQ 2) hsQ
  have hone : ρ ^ 2 * s = 1 := hCbot (ρ ^ 2 * s) hρ2sQ hcomm
  have hfinal : ρ ^ 2 = s := by
    calc ρ ^ 2 = ρ ^ 2 * (s * s) := by rw [hs_sq, mul_one]
      _ = (ρ ^ 2 * s) * s := by group
      _ = 1 * s := by rw [hone]
      _ = s := one_mul _
  simp only [pow_two] at hfinal ⊢
  exact hfinal

end Work.ZassenhausSuzuki
