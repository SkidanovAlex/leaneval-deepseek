import Mathlib
import Submission.Work.ZassenhausSuzuki.orderOf_ringAut_eq_of_fix
import Submission.Work.ZassenhausSuzuki.not_three_dvd_card_G_of_odd
import Submission.Work.ZassenhausSuzuki.structPair_sq
import Submission.Work.ZassenhausSuzuki.frel_center
import Submission.Work.ZassenhausSuzuki.odd_m_of_isTitsTheta

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `structPair_sq_fix`: `ρ * ρ = s` for the `GF(2^m)`-coordinatised configuration

`Work.ZassenhausSuzuki.structPair_sq` proves that the structure element `ρ` of a split rank-one
Zassenhaus configuration with root group `Q ≃* A(K,θ)` satisfies `ρ * ρ = s` (`s` the structure
involution), **assuming** `θ` is a Tits endomorphism (`θ² = (·)²`).  That hypothesis enters the
proof in exactly one place: through `three_not_dvd_card_G_aux`, which uses it only to show
`3 ∤ |K| - 1` (via the cubic roots of unity of `K`).

Here we remove the Tits hypothesis in the concrete setting `K = GaloisField 2 m`, replacing it by
the arithmetic statement `3 ∤ |K| - 1`.  From `hfix : Fix θ = {0,1}` and `Odd (orderOf θ)` we get
`orderOf θ = m` (Artin, `orderOf_ringAut_eq_of_fix`), hence `m` is odd
(`odd_m_of_fix`), and then `not_three_dvd_card_G_of_odd` supplies `3 ∤ |Nat.card G|` because
`|G| = (|K|²+1)·|K|²·(|K|-1)` with `|K| = 2^m ≡ -1 (mod 3)` for odd `m`.

With `3 ∤ |Nat.card G|` in hand, the body of `structPair_sq`'s proof (which is pure group theory
plus the coordinate computation `ρ^4 = 1` in `A(K,θ)`) goes through verbatim.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- `m` is odd for a non-trivial ring automorphism of `GF(2^m)` whose fixed field is `𝔽₂`:
by Artin's theorem (`orderOf_ringAut_eq_of_fix`) `orderOf θ = m`, and `orderOf θ` is odd.  The
case `m = 0` is impossible because `GaloisField 2 0` has only two elements, so its only ring
automorphism is the identity. -/
theorem odd_m_of_fix {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1)
    (hθodd : Odd (orderOf θ))
    (hfix : ∀ x : GaloisField 2 m, θ x = x → x = 0 ∨ x = 1) : Odd m := by
  have hm : 1 ≤ m := by
    by_contra h
    push_neg at h
    have hm0 : m = 0 := by omega
    subst hm0
    refine hθ1 (RingEquiv.ext fun x => ?_)
    haveI : Fintype (GaloisField 2 0) := Fintype.ofFinite _
    have hcard : Fintype.card (GaloisField 2 0) = 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact card_galoisField_two_zero
    have h01 : x = 0 ∨ x = 1 := by
      have hmem : x ∈ ({0, 1} : Finset (GaloisField 2 0)) := by
        have hc : ({0, 1} : Finset (GaloisField 2 0)).card =
            Fintype.card (GaloisField 2 0) := by
          rw [hcard, Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
        rw [Finset.eq_univ_of_card _ hc]
        exact Finset.mem_univ x
      simpa using hmem
    rcases h01 with h | h <;> simp [h]
  rw [← orderOf_ringAut_eq_of_fix hm θ hfix]
  exact hθodd

theorem structPair_sq_fix {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1)
    (hθodd : Odd (orderOf θ)) (hfix : ∀ x : GaloisField 2 m, θ x = x → x = 0 ∨ x = 1)
    (e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)
    (htorus : Work.ZassenhausSuzuki.TorusCoords (GaloisField 2 m) θ H Q t e)
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
    have h1 : e ⟨s, hsQ⟩ = (⟨0, (e ⟨s, hsQ⟩).b⟩ : SzA (GaloisField 2 m) θ) := by
      ext <;> simp [hsa]
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
          = (⟨0, (e ⟨ρ, hρQ⟩).a * θ (e ⟨ρ, hρQ⟩).a⟩ : SzA (GaloisField 2 m) θ) := by
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
  -- `3 ∤ |G|` replaces the Tits hypothesis: `|K| = 2^m` with `m` odd forces `3 ∤ |G|`
  have hoddm : Odd m := odd_m_of_fix hθ1 hθodd hfix
  have h3G : ¬ 3 ∣ Nat.card G :=
    not_three_dvd_card_G_of_odd (e := e) hsplit hzass h2 hoddm
  -- `3 ∤ |G|` forces `orderOf w = 5`
  have h3notdvd : ¬ 3 ∣ orderOf w := by
    intro h3
    exact h3G (h3.trans (orderOf_dvd_natCard w))
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
