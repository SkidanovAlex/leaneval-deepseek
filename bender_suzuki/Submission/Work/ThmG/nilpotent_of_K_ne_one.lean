import Mathlib
import Submission.Work.ThmG.Defs
import Submission.Work.ThmG.centralizer_le_twoPoint_of_fixedPts_card_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmG.nilpotent_of_K_ne_one`

Peterfalvi II, Ch. V §1, Proposition 1 b) (p. 240): in the split rank-one situation
`H = Q ⋊ D`, `t ∉ H`, `D = H ∩ Hᵗ = twoPoint H t`, if
`K = J(D,t) = {x ∈ D | xᵗ = x⁻¹} = invertedBy (twoPoint H t) t` is non-trivial, then `Q` is
nilpotent.

Proof.  Choose `z ∈ K#` of prime order `p = orderOf z` (`primeOrder_mem_invertedBy` below).
By Ch. II §4 Prop. 2 (c) (`ChIIFourProp`), `⟨z⟩` fixes exactly two points of `Ω = G ⧸ H`; the
centraliser lemma `Work.ThmG.centralizer_le_twoPoint_of_fixedPts_card_two` then gives
`C_H(z) ≤ D`, and since `Q ⊓ D = 1` we get `C_Q(z) = 1`.  As `z ∈ D ≤ H ≤ N_G(Q)`, conjugation
by `z` defines an automorphism of `Q` whose order divides the prime `p`; Thompson's theorem
(`ThompsonFrobeniusProp`) applied to it gives that `Q` is nilpotent.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThmG

open Submission.Blueprint

/-- Thompson's theorem on Frobenius kernels, in the conjugation form used by Theorem G: if a
finite subgroup `Q` is normalised by an element `z` of prime order acting on `Q` without
non-trivial fixed points, then `Q` is nilpotent.

Conjugation by `z` is the automorphism `Subgroup.normalizerMonoidHom Q ⟨z, hzN⟩` of `Q`; its
order divides `orderOf z`, hence is `1` or the prime `orderOf z`; in the first case `Q` is
trivial. -/
theorem isNilpotent_of_fpf_conj {G : Type} [Group G] [Finite G]
    (hTh : Submission.Blueprint.ThompsonFrobeniusProp)
    {Q : Subgroup G} {z : G} (hzN : z ∈ Subgroup.normalizer (Q : Set G))
    (hprime : (orderOf z).Prime)
    (hfpf : Q ⊓ Subgroup.centralizer ({z} : Set G) = ⊥) :
    Group.IsNilpotent Q := by
  classical
  let α : MulAut ↥Q := Subgroup.normalizerMonoidHom Q ⟨z, hzN⟩
  have hα : ∀ q : ↥Q, ((α q : ↥Q) : G) = z * (q : G) * z⁻¹ := by
    intro q
    simp [α]
  -- `z` acts fixed-point-freely
  have hfpf' : ∀ q : ↥Q, α q = q → q = 1 := by
    intro q hq
    have hq' : (q : G) = z * (q : G) * z⁻¹ := by simpa [hq] using hα q
    have hcomm : (q : G) * z = z * (q : G) := eq_mul_inv_iff_mul_eq.mp hq'
    have hmem : (q : G) ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hmem' : (q : G) ∈ (Q ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) :=
      ⟨q.2, hmem⟩
    rw [hfpf] at hmem'
    exact Subtype.ext (by simpa using hmem')
  -- the order of the conjugation automorphism divides `orderOf z`
  have horder : orderOf α ∣ orderOf z := by
    have h := orderOf_map_dvd (Subgroup.normalizerMonoidHom Q)
      (⟨z, hzN⟩ : ↥(Subgroup.normalizer (Q : Set G)))
    have hZ : orderOf (⟨z, hzN⟩ : ↥(Subgroup.normalizer (Q : Set G))) = orderOf z :=
      Subgroup.orderOf_mk z hzN
    rw [hZ] at h
    simpa [α] using h
  by_cases hα1 : α = 1
  · -- the conjugation is trivial, so `Q` is trivial by fixed-point-freeness
    have hsub : Subsingleton ↥Q := ⟨fun a b => by
      have ha : a = 1 := hfpf' a (by rw [hα1]; rfl)
      have hb : b = 1 := hfpf' b (by rw [hα1]; rfl)
      rw [ha, hb]⟩
    exact @Group.isNilpotent_of_subsingleton ↥Q _ hsub
  · have hprime' : (orderOf α).Prime := by
      rcases hprime.eq_one_or_self_of_dvd (orderOf α) horder with h1 | h
      · exact absurd (orderOf_eq_one_iff.mp h1) hα1
      · rwa [h]
    exact hTh ↥Q α hprime' hfpf'

/-- Extraction of an element of prime order from `K = J(D,t) = invertedBy D t`, `D = twoPoint H t`:
conjugation by `t` is a group homomorphism, so for `x ∈ K` every power `x^n` again lies in `K`;
taking `x^(orderOf x / p)` for a prime `p ∣ orderOf x` gives an element of `K#` of prime order. -/
theorem primeOrder_mem_invertedBy {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t x : G}
    (hx : x ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t)
    (hx1 : x ≠ 1) :
    ∃ z ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t,
      z ≠ 1 ∧ (orderOf z).Prime := by
  set o : ℕ := orderOf x with ho
  have ho1 : o ≠ 1 := fun hc => hx1 (orderOf_eq_one_iff.mp hc)
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd ho1
  have hzo : orderOf (x ^ (o / p)) = p := by
    rw [orderOf_pow]
    have hgcd : (orderOf x).gcd (o / p) = o / p := by
      rw [ho.symm]
      exact Nat.gcd_eq_right (Nat.div_dvd_of_dvd hpdvd)
    rw [hgcd, ← ho]
    exact Nat.div_div_self hpdvd (by rw [ho]; exact (orderOf_pos x).ne')
  refine ⟨x ^ (o / p), ⟨?_, ?_⟩, ?_, ?_⟩
  · exact Subgroup.pow_mem _ hx.1 _
  · show t * x ^ (o / p) * t⁻¹ = (x ^ (o / p))⁻¹
    rw [(conj_pow (i := o / p) (a := t) (b := x)).symm, hx.2, inv_pow]
  · intro hc
    have h1 : orderOf (x ^ (o / p)) = 1 := by rw [hc, orderOf_one]
    rw [hzo] at h1
    exact hpprime.ne_one h1
  · rw [hzo]
    exact hpprime

theorem nilpotent_of_K_ne_one {G : Type} [Group G] [Finite G]
    (hSit : Submission.Blueprint.Situation G) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hTh : Submission.Blueprint.ThompsonFrobeniusProp)
    {H Q : Subgroup G} {t : G} (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hK : ∃ x ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, x ≠ 1) :
    Group.IsNilpotent Q := by
  classical
  obtain ⟨x, hxK, hx1⟩ := hK
  -- an element `z ∈ K#` of prime order
  obtain ⟨z, hzK, hz1, hzprime⟩ := primeOrder_mem_invertedBy hxK hx1
  have hzD : z ∈ Submission.Blueprint.twoPoint H t := hzK.1
  have hzH : z ∈ H := hzD.1
  -- Ch. II §4 Prop. 2 (c): `⟨z⟩` fixes exactly two points of `Ω = G ⧸ H`
  have hC4' := hC4 G hSit H h.stronglyEmbedded t h.invol h.not_mem
  have h2 : (fixedPts H (Subgroup.zpowers z)).ncard = 2 := hC4'.2.2.1 z hzK hz1
  -- hence `C_H(z) ≤ D`
  have hCz : Subgroup.centralizer ({z} : Set G) ⊓ H ≤ Submission.Blueprint.twoPoint H t :=
    centralizer_le_twoPoint_of_fixedPts_card_two hzD hz1 h2
  -- and, since `Q ⊓ D = 1`, we get `C_Q(z) = 1`
  have hfpf : Q ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    obtain ⟨hqQ, hqC⟩ := hq
    have hqD : q ∈ Submission.Blueprint.twoPoint H t := hCz ⟨hqC, h.le hqQ⟩
    have hqinf : q ∈ (Q ⊓ Submission.Blueprint.twoPoint H t : Subgroup G) := ⟨hqQ, hqD⟩
    rw [h.inf_eq] at hqinf
    simpa using hqinf
  -- `z` normalises `Q` because `z ∈ D ≤ H ≤ N_G(Q)`
  have hzN : z ∈ Subgroup.normalizer (Q : Set G) := h.normal hzH
  exact isNilpotent_of_fpf_conj hTh hzN hzprime hfpf

end Work.ThmG
