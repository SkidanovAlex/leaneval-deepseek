import Mathlib
import Submission.Work.ZassenhausSuzuki.frel_center_aux
import Submission.Work.ZassenhausSuzuki.twoPoint_card_eq_involutions
import Submission.Work.ZassenhausSuzuki.ncard_involutions_of_mulEquiv
import Submission.Work.ZassenhausSuzuki.SzA.ncard_orderOf_eq_two
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmG.rankOne_index
import Submission.Work.ZassenhausSuzuki.TitsAux
import Submission.Work.ZassenhausSuzuki.frel_product
import Submission.Work.ZassenhausSuzuki.frel_torus_inv
import Submission.Work.ZassenhausSuzuki.frel_torus_all
import Submission.Work.ZassenhausSuzuki.partitionszA.hLam_orbit_iff
import Submission.Work.ZassenhausSuzuki.exists_torusParam
import Submission.Work.ZassenhausSuzuki.hb6_alg
import Submission.Work.ZassenhausSuzuki.field_final
import Submission.Work.ZassenhausSuzuki.orbit_criterion
import Submission.Work.ZassenhausSuzuki.exists_k_center
import Submission.Work.ZassenhausSuzuki.twoPoint_comm

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- `A(K,θ)` has `|K| ^ 2` elements. -/
private theorem natCard_szA {K : Type*} [Field K] (θ : K ≃+* K) :
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
private theorem structPair_sq_local {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
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


/-! ## Auxiliary torus-algebra lemmas in `A(K,θ)` -/

/-- `h_λ` is multiplicative: `h_λ (x y) = h_λ x · h_λ y`. -/
private theorem hLamAut_mul {K : Type} [Field K] (θ : K ≃+* K) (u : Kˣ) (x y : SzA K θ) :
    SzA.hLam θ (u : K) (x * y) = SzA.hLam θ (u : K) x * SzA.hLam θ (u : K) y := by
  rw [← SzA.hLamHom_apply θ u (x * y), ← SzA.hLamHom_apply θ u x,
    ← SzA.hLamHom_apply θ u y, map_mul]

/-- `h_λ` is multiplicative in the `K`-form. -/
private theorem hLam_mul_K {K : Type} [Field K] (θ : K ≃+* K) (c : K) (x y : SzA K θ) :
    SzA.hLam θ c (x * y) = SzA.hLam θ c x * SzA.hLam θ c y := by
  ext <;> simp only [SzA.hLam_a, SzA.hLam_b, SzA.mul_a, SzA.mul_b, map_add, map_mul] <;> ring

/-- `h_λ` on a centre element. -/
private theorem hLam_zero {K : Type} [Field K] (θ : K ≃+* K) (c b : K) :
    SzA.hLam θ c (⟨0, b⟩ : SzA K θ) = ⟨0, c * θ c * b⟩ := by
  ext <;> simp [SzA.hLam]

/-- Product of two centre elements. -/
private theorem SzA_mul_zb {K : Type} [Field K] (θ : K ≃+* K) (z₁ z₂ : K) :
    ((⟨0, z₁⟩ : SzA K θ) * ⟨0, z₂⟩).b = z₁ + z₂ := by
  rw [SzA.mul_b]; simp

/-- **`D = twoPoint H t` acts freely on `Q ∖ {1}`.**

If `d ∈ D` commutes with `x ∈ Q^#`, then `d` fixes the three distinct points
`∞`, `t·∞` and `x·(t·∞)` of `Ω = G ⧸ H`, so `d = 1` by the Zassenhaus condition. -/
private theorem twoPoint_acts_freely {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    {d x : G} (hd : d ∈ twoPoint H t) (hxQ : x ∈ Q) (hx1 : x ≠ 1)
    (hcomm : d * x * d⁻¹ = x) : d = 1 := by
  have ht2 : t * t = 1 := RankOneUniqueness.mul_self_eq_one hsplit
  set ω : G ⧸ H := RankOneUniqueness.qPt H t x with hω
  have hdx : d * x = x * d := by
    have h := congrArg (fun z => z * d) hcomm
    simpa [mul_assoc] using h
  have hdpt : d • RankOneUniqueness.pt H = RankOneUniqueness.pt H :=
    RankOneUniqueness.smul_pt_of_mem H (RankOneUniqueness.mem_twoPoint_iff.mp hd).1
  have hdtp : d • (t • RankOneUniqueness.pt H) = t • RankOneUniqueness.pt H := by
    obtain ⟨e, he, heq⟩ := (RankOneUniqueness.mem_conj_iff H t d).mp hd.2
    have key : d * t = t * e := by rw [← heq]; group
    rw [smul_smul, key, ← smul_smul, RankOneUniqueness.smul_pt_of_mem H he]
  have hdω : d • ω = ω := by
    rw [hω, RankOneUniqueness.qPt_eq_smul, smul_smul, hdx, ← smul_smul, hdtp]
  have h12 : RankOneUniqueness.pt H ≠ t • RankOneUniqueness.pt H :=
    (RankOneUniqueness.t_smul_pt_ne hsplit).symm
  have h13 : RankOneUniqueness.pt H ≠ ω := (RankOneUniqueness.qPt_ne_pt hsplit hxQ).symm
  have h23 : t • RankOneUniqueness.pt H ≠ ω := by
    intro hcon
    have hcon1 : RankOneUniqueness.qPt H t x = t • RankOneUniqueness.pt H := hcon.symm
    have h3 : (x * t) • RankOneUniqueness.pt H = t • RankOneUniqueness.pt H := by
      rw [← smul_smul, ← RankOneUniqueness.qPt_eq_smul]; exact hcon1
    have h4 : (t⁻¹ * x * t) ∈ H := by
      have h5 : (t⁻¹ * x * t) • RankOneUniqueness.pt H = RankOneUniqueness.pt H := by
        rw [show t⁻¹ * x * t = t⁻¹ * (x * t) from by group, ← smul_smul, h3,
            smul_smul, inv_mul_cancel, one_smul]
      exact (RankOneUniqueness.smul_pt_iff H _).mp h5
    have hxmem : x ∈ conj t H := by
      rw [RankOneUniqueness.mem_conj_iff]
      exact ⟨t⁻¹ * x * t, h4, by group⟩
    have hmem : x ∈ Q ⊓ twoPoint H t := ⟨hxQ, hsplit.le hxQ, hxmem⟩
    rw [hsplit.inf_eq] at hmem
    exact hx1 (Subgroup.mem_bot.mp hmem)
  exact hzass _ _ _ h12 h13 h23 d hdpt hdtp hdω

/-! ## The `D`-component `γ` of the canonical form of `t · x · t` -/

/-- `GammaRel H Q t x d` says that `d ∈ D = twoPoint H t` is the `D`-component of the
canonical form `t x t = (b · d) · t · y` (`b ∈ Q`, `y ∈ Q`).  Equivalently, writing
`t x t = m · t · y` with `m ∈ H` (unique, `canon_unique`) and `m = b · d` (`H = Q ⋊ D`),
`d` is the `D`-part of `m`. -/
private def GammaRel {G : Type} [Group G] (H Q : Subgroup G) (t x d : G) : Prop :=
  d ∈ twoPoint H t ∧ ∃ b ∈ Q, ∃ y ∈ Q, t * x * t = (b * d) * (t * y)

/-- The `D`-component exists for every `x ∈ Q^#`. -/
private theorem GammaRel_exists {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t) {x : G} (hxQ : x ∈ Q) (hx1 : x ≠ 1) :
    ∃ d : G, GammaRel H Q t x d := by
  obtain ⟨y, hyQ, hyRel⟩ := RankOneUniqueness.f_exists hsplit hxQ hx1
  obtain ⟨m, hmH, hm⟩ := hyRel
  obtain ⟨q, hqQ, d, hdD, hqd⟩ := RankOneUniqueness.fact_exists hsplit hmH
  exact ⟨d, hdD, q, hqQ, y, hyQ, by rw [hm, hqd]; group⟩

/-- The `D`-component is unique. -/
private theorem GammaRel_unique {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t) {x d d' : G}
    (h : GammaRel H Q t x d) (h' : GammaRel H Q t x d') : d = d' := by
  obtain ⟨hdD, b, hbQ, y, hyQ, hbdy⟩ := h
  obtain ⟨hd'D, b', hb'Q, y', hy'Q, hb'd'y'⟩ := h'
  have hb : b * d ∈ H := H.mul_mem (hsplit.le hbQ) (RankOneUniqueness.mem_twoPoint_iff.mp hdD).1
  have hb' : b' * d' ∈ H :=
    H.mul_mem (hsplit.le hb'Q) (RankOneUniqueness.mem_twoPoint_iff.mp hd'D).1
  have hEq : b * d * t * y = b' * d' * t * y' := by
    rw [show b * d * t * y = (b * d) * (t * y) by group,
        show b' * d' * t * y' = (b' * d') * (t * y') by group, ← hbdy, hb'd'y']
  obtain ⟨hbd, hy⟩ := RankOneUniqueness.canon_unique hsplit hb hb' hyQ hy'Q hEq
  subst hy
  exact (RankOneUniqueness.fact_unique hsplit hbQ hb'Q hdD hd'D hbd).2

/-- `γ(ρ) = 1` for the structure element `ρ` (given `ρ * ρ = s`). -/
private theorem GammaRel_rho {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t)
    (hsq : (structPair hsplit).1 = (structPair hsplit).2 * (structPair hsplit).2) :
    GammaRel H Q t (structPair hsplit).2 1 := by
  obtain ⟨-, -, hρQ, hstruct⟩ := structPair_spec hsplit
  have ht2 : t * t = 1 := RankOneUniqueness.mul_self_eq_one hsplit
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set ρ : G := (structPair hsplit).2 with hρ
  have h1 : t * (ρ * ρ) * t = ρ * t * ρ⁻¹ := by rw [← hsq, ← hstruct, hti]
  have key : (ρ * ρ) * t * ρ = t * ρ * t := by
    have h := congrArg (fun z => t * z) h1
    rw [show t * (t * (ρ * ρ) * t) = (t * t) * (ρ * ρ) * t by group, ht2, one_mul] at h
    rw [h]; group
  refine ⟨Subgroup.one_mem _, ρ * ρ, Q.mul_mem hρQ hρQ, ρ, hρQ, ?_⟩
  rw [mul_one]
  simpa only [hρ, mul_assoc] using key.symm

/-- **Equivariance of `γ`.**  Conjugating `x` by `d ∈ D` multiplies the `D`-component by
`d` on both sides: `γ(d⁻¹ x d) = d · γ(x) · d`. -/
private theorem GammaRel_conj {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) {x γ d : G}
    (hγ : GammaRel H Q t x γ) (hdD : d ∈ twoPoint H t) :
    GammaRel H Q t (d⁻¹ * x * d) (d * γ * d) := by
  obtain ⟨hγD, b, hbQ, y, hyQ, hbdec⟩ := hγ
  have ht2 : t * t = 1 := RankOneUniqueness.mul_self_eq_one hsplit
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hdD' : d ∈ H := (RankOneUniqueness.mem_twoPoint_iff.mp hdD).1
  have hdt : t * d * t = d⁻¹ := by
    have h := twoPoint_inverted_of_zass hsplit hzass d hdD
    rwa [hti] at h
  have hdit : t * d⁻¹ * t = d := by
    have h : (t * d * t)⁻¹ = t * d⁻¹ * t := by
      rw [mul_inv_rev, mul_inv_rev, hti]; group
    rw [← h, hdt, inv_inv]
  have hdtd : d * t * d = t := by
    have h : (d * t * d) * t = 1 := by
      rw [show (d * t * d) * t = d * (t * d * t) by group, hdt, mul_inv_cancel]
    calc d * t * d = (d * t * d) * t * t⁻¹ := by group
      _ = 1 * t⁻¹ := by rw [h]
      _ = t⁻¹ := one_mul _
      _ = t := hti
  refine ⟨(twoPoint H t).mul_mem ((twoPoint H t).mul_mem hdD hγD) hdD,
    d * b * d⁻¹, RankOneUniqueness.conj_mem_of_mem hsplit hdD' hbQ,
    d * y * d⁻¹, RankOneUniqueness.conj_mem_of_mem hsplit hdD' hyQ, ?_⟩
  have hφ : ∀ z : G, MulAut.conj t z = t * z * t := fun z => by
    rw [MulAut.conj_apply, hti]
  have hφd : MulAut.conj t d = d⁻¹ := by rw [hφ, hdt]
  have hφdi : MulAut.conj t d⁻¹ = d := by rw [map_inv, hφd, inv_inv]
  have hkey : t * (d⁻¹ * x * d) * t = d * (t * x * t) * d⁻¹ := by
    rw [← hφ, map_mul, map_mul, hφdi, hφd, hφ]
  have h1 : d * (b * γ * (t * y)) * d⁻¹ = d * b * γ * t * y * d⁻¹ := by group
  have h2 : ((d * b * d⁻¹) * (d * γ * d)) * (t * (d * y * d⁻¹))
      = d * b * γ * (d * t * d) * y * d⁻¹ := by group
  rw [hkey, hbdec, h1, h2, hdtd]

/-! ## HB XI 11.11 (b) in general: the non-conjugacy of `ρ⁻¹ h⁻¹ ρ h` -/

/-- **HB XI 11.11 (b), general form.**  Let `(H,Q,t)` be a split rank-one Zassenhaus
configuration coordinated by `A(K,θ)`, let `s, ρ` be the structure-identity pair
(`t s t = ρ t ρ⁻¹`, `ρ * ρ = s`) and suppose `e s = ⟨0,1⟩`.  Then for every `1 ≠ h ∈ D =
twoPoint H t` the element `ρ⁻¹ h⁻¹ ρ h` is **not** `D`-conjugate to `ρ`. -/
private theorem structure_element_not_conjugate {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K} (hθ : Work.ZassenhausSuzuki.IsTitsTheta θ)
    (e : Q ≃* Work.ZassenhausSuzuki.SzA K θ)
    (htorus : Work.ZassenhausSuzuki.TorusCoords K θ H Q t e)
    (hs : e (⟨(Work.ZassenhausSuzuki.structPair hsplit).1,
        (Work.ZassenhausSuzuki.structPair_spec hsplit).1⟩ : Q)
      = (⟨0, 1⟩ : Work.ZassenhausSuzuki.SzA K θ)) :
    ∀ h ∈ Submission.Blueprint.twoPoint H t, h ≠ 1 →
      ¬ ∃ d₀ ∈ Submission.Blueprint.twoPoint H t,
        (Work.ZassenhausSuzuki.structPair hsplit).2⁻¹ * h⁻¹
          * (Work.ZassenhausSuzuki.structPair hsplit).2 * h
          = d₀ * (Work.ZassenhausSuzuki.structPair hsplit).2 * d₀⁻¹ := by
  classical
  obtain ⟨hsQ, hs2, hρQ, hstruct0⟩ := structPair_spec hsplit
  have ht2 : t * t = 1 := ht_mul_self hsplit
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  haveI h2p : IsPGroup 2 Q := isPGroup_two_of_mulEquiv θ e
  have hsq : (structPair hsplit).2 * (structPair hsplit).2 = (structPair hsplit).1 :=
    structPair_sq_local hsplit hzass hθ e htorus h2p
  have hstruct : t * ((structPair hsplit).2 * (structPair hsplit).2) * t
      = (structPair hsplit).2 * t * (structPair hsplit).2⁻¹ := by
    rw [hsq]; simpa [hti] using hstruct0
  have hs_sq : (structPair hsplit).1 * (structPair hsplit).1 = 1 := by
    have h := pow_orderOf_eq_one (structPair hsplit).1
    rw [hs2] at h
    simpa [pow_two] using h
  have hj2 : ((structPair hsplit).2 * (structPair hsplit).2)
      * ((structPair hsplit).2 * (structPair hsplit).2) = 1 := by
    rw [hsq]; exact hs_sq
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have h1 : (e.symm (⟨1, 0⟩ : SzA K θ) : Q) = 1 :=
      Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ (e.symm (⟨1, 0⟩ : SzA K θ)).2))
    have h2 : (⟨1, 0⟩ : SzA K θ) = 1 := by
      have := congrArg (fun q : Q => e q) h1
      simpa using this
    exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrArg SzA.a h2)
  -- the structure element `ρ` has first coordinate `1`
  set xq : Q := ⟨(structPair hsplit).2, hρQ⟩ with hxqdef
  have hρa : (e xq).a = 1 := by
    have haθa : (e xq).a * θ (e xq).a = 1 := by
      have h1 : xq * xq = (⟨(structPair hsplit).1, hsQ⟩ : Q) := by
        apply Subtype.ext; exact hsq
      have h2 : e xq * e xq = (⟨0, 1⟩ : SzA K θ) := by rw [← map_mul, h1, hs]
      have h3 := congrArg SzA.b ((SzA.sq_eq θ (e xq)).symm.trans h2)
      simpa using h3
    exact mul_theta_eq_one θ hθ haθa
  -- the torus parametrisation `D → Kˣ`
  obtain ⟨par, hpar_act, hpar_mul, hpar_inj⟩ := exists_torusParam hsplit hzass htorus
  have hpar_one : par 1 = 1 := by
    have h := hpar_mul 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [mul_one] at h
    exact (mul_left_cancel (show par 1 * 1 = par 1 * par 1 by rw [mul_one]; exact h)).symm
  have hpar_inv : ∀ d ∈ twoPoint H t, par (d⁻¹) = (par d)⁻¹ := by
    intro d hd
    have hid : d⁻¹ ∈ twoPoint H t := (twoPoint H t).inv_mem hd
    have h' : par d * par (d⁻¹) = 1 := by
      have h2 := hpar_mul d hd d⁻¹ hid
      rw [← h2, mul_inv_cancel, hpar_one]
    have := congrArg (fun z => (par d)⁻¹ * z) h'
    simpa [mul_assoc] using this
  have hD_sq : ∀ d ∈ twoPoint H t, d * d = 1 → d = 1 := by
    intro d hd hdd
    have h : par d * par d = 1 := by
      have h1 := hpar_mul d hd d hd
      rw [hdd, hpar_one] at h1
      exact h1.symm
    have h2 : par d = 1 := by
      have h3 : (par d : K) * (par d : K) = 1 := by
        simpa using congrArg (fun u : Kˣ => (u : K)) h
      have h4 : ((par d : K) + 1) * ((par d : K) + 1) = 0 := by
        have h5 : ((par d : K) + 1) * ((par d : K) + 1)
            = (par d : K) * (par d : K) + ((par d : K) + (par d : K)) + 1 := by ring
        rw [h5, CharTwo.add_self_eq_zero, add_zero, h3]
        exact CharTwo.add_self_eq_zero 1
      have h5 : (par d : K) + 1 = 0 := by
        rcases mul_eq_zero.mp h4 with h6 | h6
        · exact h6
        · exact h6
      have h6 : (par d : K) = 1 := by
        have h7 : (par d : K) + 1 = 1 + 1 := by rw [h5, CharTwo.add_self_eq_zero]
        exact add_right_cancel h7
      exact Units.ext h6
    rw [← hpar_one] at h2
    exact hpar_inj d hd 1 (Subgroup.one_mem _) h2
  have hpar_act_inv : ∀ d ∈ twoPoint H t, ∀ x : Q,
      (((e.symm (SzA.hLam θ ((par d : K)⁻¹) (e x)) : Q)) : G) = d⁻¹ * (x : G) * d := by
    intro d hd x
    have hid : d⁻¹ ∈ twoPoint H t := (twoPoint H t).inv_mem hd
    have h := hpar_act d⁻¹ hid x
    have hval : (par (d⁻¹) : K) = (par d : K)⁻¹ := by
      rw [hpar_inv d hd]; exact Units.val_inv_eq_inv_val (par d)
    rw [hval] at h
    simpa using h
  -- `s` is central in `Q`
  have hscen : ∀ x ∈ Q, (structPair hsplit).1 * x = x * (structPair hsplit).1 := by
    intro x hx
    have hcenter : ∀ y : Q, e (⟨(structPair hsplit).1, hsQ⟩ * y)
        = e (y * ⟨(structPair hsplit).1, hsQ⟩) := by
      intro y
      rw [map_mul, map_mul, hs]
      ext <;> simp [SzA.mul_a, SzA.mul_b] <;> ring
    have h := hcenter ⟨x, hx⟩
    have h2 : (⟨(structPair hsplit).1, hsQ⟩ : Q) * ⟨x, hx⟩
        = ⟨x, hx⟩ * ⟨(structPair hsplit).1, hsQ⟩ := e.injective h
    simpa using congrArg (fun z : Q => (z : G)) h2
  intro h hhD hh1 hconj
  obtain ⟨d₀, hd₀D, hd₀eq⟩ := hconj
  have hhH : h ∈ H := (RankOneUniqueness.mem_twoPoint_iff.mp hhD).1
  have hkH : ∀ x ∈ twoPoint H t, x ∈ H := fun x hx =>
    (RankOneUniqueness.mem_twoPoint_iff.mp hx).1
  -- the auxiliary element `k`
  obtain ⟨k, hkD, hkrel⟩ :=
    exists_k_center (K := K) (θ := θ) hsplit hzass h2p hθ htorus hsQ
      (structPair_fst_ne_one hsplit) hscen hhD hh1
  have hkinv : t * k * t = k⁻¹ := by
    have h := twoPoint_inverted_of_zass hsplit hzass k hkD
    rwa [hti] at h
  have hhinv : t * h * t = h⁻¹ := by
    have h := twoPoint_inverted_of_zass hsplit hzass h hhD
    rwa [hti] at h
  have hjk : k⁻¹ * ((structPair hsplit).2 * (structPair hsplit).2) * k
      = h⁻¹ * (h⁻¹ * ((structPair hsplit).2 * (structPair hsplit).2) * h
          * ((structPair hsplit).2 * (structPair hsplit).2)) * h := by
    rw [hsq]; exact hkrel
  -- `γ(ρ) = 1`
  have hgrρ : GammaRel H Q t (structPair hsplit).2 1 := GammaRel_rho hsplit hsq.symm
  -- `γ(x) = d₀⁻²` if `x = d₀ ρ d₀⁻¹`
  have hgr_d0 : GammaRel H Q t (d₀ * (structPair hsplit).2 * d₀⁻¹) (d₀⁻¹ * d₀⁻¹) := by
    have h := GammaRel_conj hsplit hzass hgrρ (d := d₀⁻¹) ((twoPoint H t).inv_mem hd₀D)
    rw [inv_inv] at h
    simpa using h
  have hgr_x_d0 : GammaRel H Q t
      ((structPair hsplit).2⁻¹ * h⁻¹ * (structPair hsplit).2 * h) (d₀⁻¹ * d₀⁻¹) := by
    rw [hd₀eq]; exact hgr_d0
  -- `γ(x) = h⁻² k²` by `hb6_alg`
  have hb6 := hb6_alg t (structPair hsplit).2 h k ht2 hstruct hj2 hhinv hkinv hjk
  have hgr_x : GammaRel H Q t
      ((structPair hsplit).2⁻¹ * h⁻¹ * (structPair hsplit).2 * h)
      ((h⁻¹ * h⁻¹) * (k * k)) := by
    have hDm : (h⁻¹ * h⁻¹) * (k * k) ∈ twoPoint H t :=
      (twoPoint H t).mul_mem
        ((twoPoint H t).mul_mem ((twoPoint H t).inv_mem hhD) ((twoPoint H t).inv_mem hhD))
        ((twoPoint H t).mul_mem hkD hkD)
    have hbQ : (structPair hsplit).2⁻¹ * (h⁻¹ * h⁻¹) * k * (structPair hsplit).2
        * k⁻¹ * (h * h) ∈ Q := by
      have hδH : (h⁻¹ * h⁻¹) * k ∈ H :=
        H.mul_mem (H.mul_mem (H.inv_mem hhH) (H.inv_mem hhH)) (hkH k hkD)
      have hconjQ := RankOneUniqueness.conj_mem_of_mem hsplit hδH hρQ
      have heq' : (structPair hsplit).2⁻¹ * (h⁻¹ * h⁻¹) * k * (structPair hsplit).2
            * k⁻¹ * (h * h)
          = (structPair hsplit).2⁻¹
            * (((h⁻¹ * h⁻¹) * k) * (structPair hsplit).2 * ((h⁻¹ * h⁻¹) * k)⁻¹) := by
        have hδinv : ((h⁻¹ * h⁻¹) * k)⁻¹ = k⁻¹ * (h * h) := by
          simp only [mul_inv_rev, inv_inv]
        rw [hδinv]
        simp only [mul_assoc]
      rw [heq']
      exact Q.mul_mem (Q.inv_mem hρQ) hconjQ
    have hyQ : k * (structPair hsplit).2⁻¹ * k⁻¹ * h * (structPair hsplit).2 * h⁻¹ ∈ Q := by
      have h1Q : k * (structPair hsplit).2⁻¹ * k⁻¹ ∈ Q :=
        RankOneUniqueness.conj_mem_of_mem hsplit (hkH k hkD) (Q.inv_mem hρQ)
      have h2Q : h * (structPair hsplit).2 * h⁻¹ ∈ Q :=
        RankOneUniqueness.conj_mem_of_mem hsplit hhH hρQ
      have heq'' : k * (structPair hsplit).2⁻¹ * k⁻¹ * h * (structPair hsplit).2 * h⁻¹
          = (k * (structPair hsplit).2⁻¹ * k⁻¹) * (h * (structPair hsplit).2 * h⁻¹) := by
        group
      rw [heq'']
      exact Q.mul_mem h1Q h2Q
    exact ⟨hDm,
      (structPair hsplit).2⁻¹ * (h⁻¹ * h⁻¹) * k * (structPair hsplit).2 * k⁻¹ * (h * h),
      hbQ,
      k * (structPair hsplit).2⁻¹ * k⁻¹ * h * (structPair hsplit).2 * h⁻¹, hyQ,
      by simpa only [mul_assoc] using hb6⟩
  have huniq : (h⁻¹ * h⁻¹) * (k * k) = d₀⁻¹ * d₀⁻¹ := GammaRel_unique hsplit hgr_x hgr_x_d0
  -- hence `d₀ = h * k⁻¹`
  have hkeq : d₀ = h * k⁻¹ := by
    have hcommD : ∀ a ∈ twoPoint H t, ∀ b ∈ twoPoint H t, a * b = b * a :=
      twoPoint_comm hsplit hzass hQne h2p
    have hsq_eq : d₀ * d₀ = (h * k⁻¹) * (h * k⁻¹) := by
      have h2 : d₀ * d₀ = (k⁻¹ * k⁻¹) * (h * h) := by
        have h := congrArg Inv.inv huniq
        simp only [mul_inv_rev, inv_inv] at h
        exact h.symm
      rw [h2]
      have hcomm : k⁻¹ * h = h * k⁻¹ :=
        hcommD k⁻¹ ((twoPoint H t).inv_mem hkD) h hhD
      have hcomm3 : (h * h) * (k⁻¹ * k⁻¹) = (k⁻¹ * k⁻¹) * (h * h) :=
        hcommD (h * h) ((twoPoint H t).mul_mem hhD hhD) (k⁻¹ * k⁻¹)
          ((twoPoint H t).mul_mem ((twoPoint H t).inv_mem hkD) ((twoPoint H t).inv_mem hkD))
      rw [show (h * k⁻¹) * (h * k⁻¹) = (h * h) * (k⁻¹ * k⁻¹) by
        rw [show (h * k⁻¹) * (h * k⁻¹) = h * (k⁻¹ * h) * k⁻¹ by group, hcomm]; group,
        hcomm3]
    have hsq1 : (d₀ * (h * k⁻¹)⁻¹) * (d₀ * (h * k⁻¹)⁻¹) = 1 := by
      have hcomm2 : d₀ * (h * k⁻¹)⁻¹ = (h * k⁻¹)⁻¹ * d₀ :=
        hcommD d₀ hd₀D ((h * k⁻¹)⁻¹)
          ((twoPoint H t).inv_mem ((twoPoint H t).mul_mem hhD ((twoPoint H t).inv_mem hkD)))
      have h0 : (d₀ * (h * k⁻¹)⁻¹) * (d₀ * (h * k⁻¹)⁻¹)
          = (d₀ * d₀) * (((h * k⁻¹) * (h * k⁻¹))⁻¹) := by
        rw [show (d₀ * (h * k⁻¹)⁻¹) * (d₀ * (h * k⁻¹)⁻¹)
              = (d₀ * d₀) * ((h * k⁻¹)⁻¹ * (h * k⁻¹)⁻¹) by
              rw [show (d₀ * (h*k⁻¹)⁻¹) * (d₀ * (h*k⁻¹)⁻¹)
                    = d₀ * ((h*k⁻¹)⁻¹ * d₀) * (h*k⁻¹)⁻¹ by group,
                  show (h*k⁻¹)⁻¹ * d₀ = d₀ * (h*k⁻¹)⁻¹ from hcomm2.symm,
                  show d₀ * (d₀ * (h*k⁻¹)⁻¹) * (h*k⁻¹)⁻¹
                    = (d₀ * d₀) * ((h*k⁻¹)⁻¹ * (h*k⁻¹)⁻¹) by group],
            show (h * k⁻¹)⁻¹ * (h * k⁻¹)⁻¹ = ((h * k⁻¹) * (h * k⁻¹))⁻¹ by
              simp only [mul_inv_rev, inv_inv]]
      rw [h0, hsq_eq, mul_inv_cancel]
    have hmem : d₀ * (h * k⁻¹)⁻¹ ∈ twoPoint H t :=
      (twoPoint H t).mul_mem hd₀D ((twoPoint H t).inv_mem ((twoPoint H t).mul_mem hhD
        ((twoPoint H t).inv_mem hkD)))
    have h1 := hD_sq (d₀ * (h * k⁻¹)⁻¹) hmem hsq1
    have h2 : d₀ = h * k⁻¹ := by
      have h3 := congrArg (fun z => z * (h * k⁻¹)) h1
      simpa [mul_assoc] using h3
    exact h2
  -- parameters
  have hpar_d0 : par d₀ = par h * (par k)⁻¹ := by
    rw [hkeq]
    rw [hpar_mul h hhD k⁻¹ ((twoPoint H t).inv_mem hkD), hpar_inv k hkD]
  -- auxiliary `Q`-elements
  have hsqeq : e (⟨(structPair hsplit).1, hsQ⟩ : Q) = (⟨0, 1⟩ : SzA K θ) := hs
  have hwr : (structPair hsplit).2⁻¹ * h⁻¹ * (structPair hsplit).2 * h
      = d₀ * (structPair hsplit).2 * d₀⁻¹ := hd₀eq
  -- first-coordinate comparison
  have hcoord : 1 + (par h : K)⁻¹ = (par h : K) * (par k : K)⁻¹ := by
    set y1 : Q := e.symm (SzA.hLam θ ((par h : K)⁻¹) (e xq)) with hy1def
    set y0 : Q := e.symm (SzA.hLam θ (par d₀ : K) (e xq)) with hy0def
    have hy1G : (y1 : G) = h⁻¹ * (structPair hsplit).2 * h := by
      rw [hy1def]; exact hpar_act_inv h hhD xq
    have hy0G : (y0 : G) = d₀ * (structPair hsplit).2 * d₀⁻¹ := by
      rw [hy0def]
      have := hpar_act d₀ hd₀D xq
      simpa using this
    have hqeq : xq⁻¹ * y1 = y0 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hy1G, hy0G]
      simpa [hxqdef, mul_assoc] using hwr
    have hy1e : e y1 = SzA.hLam θ ((par h : K)⁻¹) (e xq) := by
      rw [hy1def]; exact MulEquiv.apply_symm_apply e _
    have hy0e : e y0 = SzA.hLam θ (par d₀ : K) (e xq) := by
      rw [hy0def]; exact MulEquiv.apply_symm_apply e _
    have hLHS : (e (xq⁻¹ * y1)).a = 1 + (par h : K)⁻¹ := by
      rw [map_mul, map_inv, hy1e, SzA.mul_a, SzA.inv_a, SzA.hLam_a, hρa, mul_one, CharTwo.neg_eq]
    have hRHS : (e y0).a = (par d₀ : K) := by
      rw [hy0e, SzA.hLam_a, hρa, mul_one]
    have hEq : (e (xq⁻¹ * y1)).a = (e y0).a := by rw [hqeq]
    rw [hLHS, hRHS, hpar_d0] at hEq
    rw [Units.val_mul, Units.val_inv_eq_inv_val] at hEq
    exact hEq
  have hl0 : (par h : K) ≠ 0 := Units.ne_zero (par h)
  have hl1 : (par h : K) ≠ 1 := by
    intro hh
    exact hh1 (hpar_inj h hhD 1 (Subgroup.one_mem _) (by rw [hpar_one]; exact Units.ext hh))
  have hnu : (par k : K) = (par h : K) * (par h : K) / (1 + (par h : K)) := by
    have hl1' : (1 : K) + (par h : K) ≠ 0 := by
      intro hh
      have h2 : (par h : K) = 1 := by
        have h3 : (par h : K) + 1 = 0 := by rw [add_comm]; exact hh
        have h4 : (par h : K) + 1 = 1 + 1 := by rw [h3, CharTwo.add_self_eq_zero]
        exact add_right_cancel h4
      exact hl1 h2
    have hk0 : (par k : K) ≠ 0 := Units.ne_zero (par k)
    have h1 : (par h : K) * (par k : K)⁻¹ = 1 + (par h : K)⁻¹ := hcoord.symm
    have h2 : (par h : K) * ((par h : K) * (par k : K)⁻¹) = (par h : K) + 1 := by
      rw [h1, mul_add, mul_one, mul_inv_cancel₀ hl0]
    have h3 : (par h : K) * (par h : K) = (1 + (par h : K)) * (par k : K) := by
      have hq := congrArg (fun z : K => z * (par k : K)) h2
      have hq' : (par h : K) * (par h : K) = ((par h : K) + 1) * (par k : K) := by
        rw [← hq,
          show (par h : K) * ((par h : K) * (par k : K)⁻¹) * (par k : K)
            = (par h : K) * (par h : K) by
              rw [mul_assoc, mul_assoc, inv_mul_cancel₀ hk0, mul_one]]
      rw [add_comm 1 (par h : K)]
      exact hq'
    rw [h3, mul_div_cancel_left₀ _ hl1']
  -- the `b`-coordinate of the `k`-relation
  have hrel : (par k : K)⁻¹ * θ ((par k : K)⁻¹)
      = ((par h : K)⁻¹ * (par h : K)⁻¹) * θ ((par h : K)⁻¹ * (par h : K)⁻¹)
        + (par h : K)⁻¹ * θ ((par h : K)⁻¹) := by
    set wk : Q := e.symm (SzA.hLam θ ((par k : K)⁻¹) (e (⟨(structPair hsplit).1, hsQ⟩ : Q)))
      with hwkdef
    set w1 : Q := e.symm (SzA.hLam θ ((par h : K)⁻¹) (e (⟨(structPair hsplit).1, hsQ⟩ : Q)))
      with hw1def
    set wh : Q := e.symm (SzA.hLam θ ((par h : K)⁻¹) (e (w1 * (⟨(structPair hsplit).1, hsQ⟩ : Q))))
      with hwhdef
    have hwkG : (wk : G) = k⁻¹ * (structPair hsplit).1 * k := by
      rw [hwkdef]; exact hpar_act_inv k hkD _
    have hw1G : (w1 : G) = h⁻¹ * (structPair hsplit).1 * h := by
      rw [hw1def]; exact hpar_act_inv h hhD _
    have hwhG : (wh : G) = h⁻¹ * (h⁻¹ * (structPair hsplit).1 * h
        * (structPair hsplit).1) * h := by
      rw [hwhdef]
      have hq := hpar_act_inv h hhD (w1 * (⟨(structPair hsplit).1, hsQ⟩ : Q))
      simp only [hq, Subgroup.coe_mul, hw1G, Subgroup.coe_mk, mul_assoc]
    have hwkwh : wk = wh := Subtype.ext (by rw [hwkG, hwhG]; exact hkrel)
    have heq : e wk = e wh := by rw [hwkwh]
    have hb : (e wk).b = (e wh).b := by rw [heq]
    have hL : (e wk).b = (par k : K)⁻¹ * θ ((par k : K)⁻¹) := by
      rw [hwkdef, MulEquiv.apply_symm_apply, hsqeq, hLam_zero]
      ring
    have hR : (e wh).b = ((par h : K)⁻¹ * (par h : K)⁻¹)
        * θ ((par h : K)⁻¹ * (par h : K)⁻¹) + (par h : K)⁻¹ * θ ((par h : K)⁻¹) := by
      rw [hwhdef, MulEquiv.apply_symm_apply, map_mul, hw1def, MulEquiv.apply_symm_apply, hsqeq]
      rw [hLam_mul_K θ ((par h : K)⁻¹), ← SzA.hLam_mul]
      rw [hLam_zero, hLam_zero, SzA_mul_zb]
      ring
    rw [← hL, ← hR, hb]
  exact field_final θ (fix_of_isTitsTheta θ hθ) hl0 hl1 hnu hrel

/-- Port of `Work.ZassenhausSuzuki.structPair_value_two` (HB XI 11.11–11.12: the structure
element has coordinates `⟨1,q⟩` with `q ∈ {0,1}`) into a module that does not import
`Submission.Work.ZassenhausSuzuki.frel_center`.  Its proof is already available in
`Submission/Work/ZassenhausSuzuki/structPair_value_two.lean`; copy that file's content into your
own module, replacing the imports of `frel_center` and `structPair_sq` by `frel_center_aux` and
`Submission.Work.ZassenhausSuzuki.structPair_sq_aux` respectively (a colleague is porting the
latter in parallel; if it is not available yet, also copy the proof of
`Work.ZassenhausSuzuki.structPair_sq` from `structPair_sq.lean` into your file as a helper,
again replacing its `frel_center` import by `frel_center_aux`). -/
theorem structPair_value_two_aux {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K} (hθ : Work.ZassenhausSuzuki.IsTitsTheta θ)
    (e : Q ≃* Work.ZassenhausSuzuki.SzA K θ)
    (htorus : Work.ZassenhausSuzuki.TorusCoords K θ H Q t e)
    (hs : e (⟨(Work.ZassenhausSuzuki.structPair hsplit).1,
        (Work.ZassenhausSuzuki.structPair_spec hsplit).1⟩ : Q)
      = (⟨0, 1⟩ : Work.ZassenhausSuzuki.SzA K θ)) :
    ∃ q : K, (q = 0 ∨ q = 1) ∧
      e (⟨(Work.ZassenhausSuzuki.structPair hsplit).2,
        (Work.ZassenhausSuzuki.structPair_spec hsplit).2.2.1⟩ : Q)
        = (⟨1, q⟩ : Work.ZassenhausSuzuki.SzA K θ) := by
  classical
  obtain ⟨hsQ, hs2, hρQ, -⟩ := structPair_spec hsplit
  haveI h2p : IsPGroup 2 Q := isPGroup_two_of_mulEquiv θ e
  have hsq : (structPair hsplit).1 = (structPair hsplit).2 * (structPair hsplit).2 :=
    (structPair_sq_local hsplit hzass hθ e htorus h2p).symm
  set ρ : Q := ⟨(structPair hsplit).2, hρQ⟩ with hρdef
  set sQ : Q := ⟨(structPair hsplit).1, hsQ⟩ with hsdef
  set p : K := (e ρ).b with hpdef
  have hρval : e ρ = (⟨1, p⟩ : SzA K θ) := by
    have hmul : e ρ * e ρ = (⟨0, 1⟩ : SzA K θ) := by
      rw [← map_mul, show ρ * ρ = sQ from Subtype.ext hsq.symm, hs]
    have ha : (e ρ).a = 1 := by
      refine mul_theta_eq_one θ hθ ?_
      have h := congrArg SzA.b ((SzA.sq_eq θ (e ρ)).symm.trans hmul)
      simpa using h
    ext
    · exact ha
    · rfl
  suffices hp : p = 0 ∨ p = 1 by exact ⟨p, hp, hρval⟩
  haveI : Finite (SzA K θ) := Finite.of_equiv ↥Q e.toEquiv
  haveI hKfin : Finite K :=
    Finite.of_injective (fun k : K => (⟨k, 0⟩ : SzA K θ))
      (fun a b hab => by simpa using congrArg SzA.a hab)
  -- the two-point stabiliser is odd: `x² = 1 → x = 1` (`par` is injective)
  obtain ⟨par, hpar_act, hpar_mul, hpar_inj⟩ := exists_torusParam hsplit hzass htorus
  have hpar_one : par 1 = 1 := by
    have h := hpar_mul 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [mul_one] at h
    exact (mul_left_cancel (show par 1 * 1 = par 1 * par 1 by rw [mul_one]; exact h)).symm
  have hD_sq : ∀ d ∈ twoPoint H t, d * d = 1 → d = 1 := by
    intro d hd hdd
    have h : par d * par d = 1 := by
      have h1 := hpar_mul d hd d hd
      rw [hdd, hpar_one] at h1
      exact h1.symm
    have h2 : par d = 1 := by
      have h3 : (par d : K) * (par d : K) = 1 := by
        simpa using congrArg (fun u : Kˣ => (u : K)) h
      have h4 : ((par d : K) + 1) * ((par d : K) + 1) = 0 := by
        have h5 : ((par d : K) + 1) * ((par d : K) + 1)
            = (par d : K) * (par d : K) + ((par d : K) + (par d : K)) + 1 := by ring
        rw [h5, CharTwo.add_self_eq_zero, add_zero, h3]
        exact CharTwo.add_self_eq_zero 1
      have h5 : (par d : K) + 1 = 0 := by
        rcases mul_eq_zero.mp h4 with h6 | h6
        · exact h6
        · exact h6
      have h6 : (par d : K) = 1 := by
        have h7 : (par d : K) + 1 = 1 + 1 := by rw [h5, CharTwo.add_self_eq_zero]
        exact add_right_cancel h7
      exact Units.ext h6
    rw [← hpar_one] at h2
    exact hpar_inj d hd 1 (Subgroup.one_mem _) h2
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have h1 : (e.symm (⟨1, 0⟩ : SzA K θ) : Q) = 1 :=
      Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ (e.symm (⟨1, 0⟩ : SzA K θ)).2))
    have h2 : (⟨1, 0⟩ : SzA K θ) = 1 := by
      have := congrArg (fun q : Q => e q) h1
      simpa using this
    exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrArg SzA.a h2)
  have hcard : Nat.card ↥(twoPoint H t) = Nat.card Kˣ := by
    rw [twoPoint_card_eq_involutions hsplit hzass h2p]
    rw [show involutions (Q : Set G) = {x : G | x ∈ Q ∧ orderOf x = 2} from rfl]
    rw [ncard_involutions_of_mulEquiv (Q := Q) e]
    rw [SzA.ncard_orderOf_eq_two θ, Nat.card_units K]
  -- main inequality
  have key : ∀ ν : K, ν ≠ 0 → ν ≠ 1 → 1 + p * ν + (1 + p) * θ ν ≠ 0 := by
    intro ν hν0 hν1
    obtain ⟨d, hdD, hdact⟩ := torusLambda_surjective hsplit hzass htorus hQne hcard
      (Units.mk0 (ν⁻¹) (inv_ne_zero hν0))
    have hpar_d : par d = Units.mk0 (ν⁻¹) (inv_ne_zero hν0) := by
      apply SzA.hLamHom_injective θ
      apply MulEquiv.ext
      intro z
      have h1 : ((e.symm (SzA.hLam θ ((par d : K)) z) : Q) : G) = d * ((e.symm z : Q) : G) * d⁻¹ := by
        have h := hpar_act d hdD (e.symm z)
        rwa [e.apply_symm_apply] at h
      have h2 : ((e.symm (SzA.hLam θ (((Units.mk0 (ν⁻¹) (inv_ne_zero hν0) : Kˣ) : K)) z) : Q) : G)
          = d * ((e.symm z : Q) : G) * d⁻¹ := by
        have h := hdact (e.symm z)
        rwa [e.apply_symm_apply] at h
      have h3 : (e.symm (SzA.hLam θ ((par d : K)) z) : Q)
          = (e.symm (SzA.hLam θ (((Units.mk0 (ν⁻¹) (inv_ne_zero hν0) : Kˣ) : K)) z) : Q) :=
        Subtype.ext (h1.trans h2.symm)
      have h4 := congrArg (fun q : Q => e q) h3
      simpa using h4
    have hd1 : d ≠ 1 := by
      intro h1
      rw [h1, hpar_one] at hpar_d
      have h2 : Units.mk0 (ν⁻¹) (inv_ne_zero hν0) = (1 : Kˣ) := hpar_d.symm
      have h3 : ν = 1 := by
        have h4 : (ν⁻¹ : K) = 1 := by simpa using congrArg (fun u : Kˣ => (u : K)) h2
        rw [inv_eq_one] at h4; exact h4
      exact hν1 h3
    have hL0 : (par d : K) ≠ 0 := Units.ne_zero (par d)
    have hL1 : (par d : K) ≠ 1 := by
      intro hh
      exact hd1 (hpar_inj d hdD 1 (Subgroup.one_mem _) (by
        rw [hpar_one]; exact Units.ext hh))
    have hoc := orbit_criterion hsplit hzass h2p htorus hρval hL0 hL1 hdD hd1 (hpar_act d hdD)
    have hno : ¬ ∃ d' ∈ twoPoint H t,
        (structPair hsplit).2⁻¹ * d⁻¹ * (structPair hsplit).2 * d = d'
          * (structPair hsplit).2 * d'⁻¹ :=
      structure_element_not_conjugate hsplit hzass hθ e htorus hs d hdD hd1
    have hconv : (((e.symm (SzA.hLam θ ((par d : K)⁻¹) (e ρ))) : Q) : G)
        = d⁻¹ * (ρ : G) * d := by
      have hid : d⁻¹ ∈ twoPoint H t := (twoPoint H t).inv_mem hdD
      have h := hpar_act d⁻¹ hid ρ
      have hval : (par (d⁻¹) : K) = (par d : K)⁻¹ := by
        have h' : par d * par (d⁻¹) = 1 := by
          have h2 := hpar_mul d hdD d⁻¹ hid
          rw [← h2, mul_inv_cancel, hpar_one]
        have := congrArg (fun z => (par d)⁻¹ * z) h'
        have h'' : par (d⁻¹) = (par d)⁻¹ := by simpa [mul_assoc] using this
        rw [h'']
        exact Units.val_inv_eq_inv_val (par d)
      rw [hval] at h
      simpa using h
    have hno' : ¬ ∃ d' ∈ twoPoint H t,
        (ρ : G)⁻¹ * (((e.symm (SzA.hLam θ ((par d : K)⁻¹) (e ρ))) : Q) : G)
          = d' * (ρ : G) * d'⁻¹ := by
      rintro ⟨d', hd'D, hd'⟩
      refine hno ⟨d', hd'D, ?_⟩
      have hd'' := hd'
      rw [hconv] at hd''
      simpa [hρdef, mul_assoc] using hd''
    have hB := hoc.not.mp hno'
    have hpd : (par d : K) = ν⁻¹ := by rw [hpar_d]; rfl
    rw [hpd] at hB
    simp only [inv_inv] at hB
    intro hzero
    apply hB
    have hX : p * ν + (p + 1) * θ ν = 1 := by
      have h0 : 1 + (p * ν + (1 + p) * θ ν) = 0 := by rw [← add_assoc]; exact hzero
      have h3 : p * ν + (1 + p) * θ ν = 1 := by
        have h4 : p * ν + (1 + p) * θ ν + 1 = 0 := by
          rw [show p * ν + (1 + p) * θ ν + 1 = 1 + (p * ν + (1 + p) * θ ν) by ring]
          exact h0
        have h5 : p * ν + (1 + p) * θ ν + 1 = 1 + 1 := by rw [h4, CharTwo.add_self_eq_zero]
        exact add_right_cancel h5
      rw [← show (1 + p) = (p + 1) from add_comm 1 p]
      exact h3
    exact hX
  refine eq_zero_or_eq_one_of_forall θ (fix_of_isTitsTheta θ hθ) (y := p) ?_
  intro x hx0 hx1 hcon
  have hcon' : p * x + (1 + p) * θ x = 0 := by
    rw [← add_comm p 1]; exact hcon
  have hx10 : x + 1 ≠ 0 := by
    intro h
    exact hx1 (by
      have h2 : x + 1 = 1 + 1 := by rw [h, CharTwo.add_self_eq_zero]
      exact add_right_cancel h2)
  have hx11 : x + 1 ≠ 1 := by
    intro h
    exact hx0 (by
      have h2 : x + 1 = 0 + 1 := by rw [h, zero_add]
      exact add_right_cancel h2)
  refine key (x + 1) hx10 hx11 ?_
  have h1 : p * (x + 1) + (1 + p) * θ (x + 1) = 1 := by
    have e1 : p * (x + 1) = p * x + p := by rw [mul_add, mul_one]
    have e2 : (1 + p) * θ (x + 1) = (1 + p) * θ x + (1 + p) := by
      rw [map_add, map_one, mul_add, mul_one]
    have e3 : p + (1 + p) = 1 := by
      rw [show p + (1 + p) = (p + p) + 1 by ac_rfl, CharTwo.add_self_eq_zero, zero_add]
    rw [e1, e2]
    rw [show p * x + p + ((1 + p) * θ x + (1 + p))
          = (p * x + (1 + p) * θ x) + (p + (1 + p)) by ac_rfl, e3, hcon', zero_add]
  rw [add_assoc, h1, CharTwo.add_self_eq_zero]

end Work.ZassenhausSuzuki
