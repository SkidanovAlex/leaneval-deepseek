import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.Bender.Basic
import Submission.Work.ThmF.ChV12.prop1a

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.prop1b` — Peterfalvi II, Ch. V §1, Prop. 1 b): `Q` is nilpotent

Source (Peterfalvi, *Le théorème de Bender–Suzuki II*, Ch. V §1, p. 240):

> **Proposition 1.** a) If `x ∈ K - {1}`, then `C_Q(x) = 1`.  b) `Q` is nilpotent.
>
> *Proof.* a) For `x ∈ K - {1}`, `|Ω_x| = 2` (Ch. II §4 Prop. 2). Since `C_G(x)` acts on `Ω_x`,
> `C_H(x) ⊆ D`, so `C_Q(x) = 1`.
> b) `|K| = |Inv(H)| > 1` (Ch. I §2), so some `x ∈ K - {1}`; `⟨x⟩ ⊆ K` acts fixed-point-freely
> on `Q` by a), so `Q` is nilpotent by **Thompson's theorem on Frobenius kernels**.

In the split rank-one situation `H = Q ⋊ D` (`D = H ∩ Hᵗ = twoPoint H t`, `t ∉ H` an involution,
`Q ≤ H` normalised by `H`, `Q ⊓ D = ⊥`, `Q ⊔ D = H`) with `K = J(D,t) = {x ∈ D | xᵗ = x⁻¹} =
Kset H t` non-trivial, the formal proof is:

* *Prime order element of `K`.*  Conjugation by the involution `t` is multiplicative, so `K` is
  closed under powers (`pow_mem_Kset`), and for `x ∈ K#` with `p` a prime dividing `orderOf x` the
  element `z = x ^ (orderOf x / p)` again lies in `K#` and has order `p` (here `orderOf x > 1`
  because `x ≠ 1` and `G` is finite).
* *Fixed point freeness.*  Part a) of the proposition is the content of the sibling file
  `Work.ThmF.ChV12.prop1a`: from the Ch. II §4 Prop. 2 (c) fixed-point count (`hC4`), every
  `x ∈ K#` has `C_Q(x) = 1`.  Applied to `z` this says that conjugation by `z` fixes only `1`
  in `Q`.
* *Thompson.*  `z ∈ D ≤ H ≤ N_G(Q)`, so conjugation by `z` is an automorphism `α` of `Q`; its
  order divides the prime `p = orderOf z`.  If `α = 1` then fixed-point-freeness forces `Q = 1`
  (a subsingleton group is nilpotent); otherwise `orderOf α = p` is prime and
  **Thompson's theorem on Frobenius kernels** (`ThompsonFrobeniusProp`) — a finite group with a
  fixed-point-free automorphism of prime order is nilpotent — gives `Group.IsNilpotent ↥Q`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV12

open LeanEval.GroupTheory.Defs Submission.Blueprint

variable {G : Type*} [Group G] [Finite G]

/-- An element of `K = J(D,t) = Kset H t` of **prime** order exists as soon as `K` contains a
non-identity element: `K` is closed under powers (conjugation by `t` is a homomorphism), so for
`x ∈ K#` and a prime `p ∣ orderOf x` the element `x ^ (orderOf x / p)` is again in `K#` and has
order `p`. -/
private theorem primeOrder_mem_Kset {H : Subgroup G} {t x : G} (hx : x ∈ Kset H t)
    (hx1 : x ≠ 1) : ∃ z ∈ Kset H t, z ≠ 1 ∧ (orderOf z).Prime := by
  set o : ℕ := orderOf x with ho
  have ho_pos : 0 < o := by rw [ho]; exact orderOf_pos x
  have ho1 : o ≠ 1 := by rw [ho]; exact fun hc => hx1 (orderOf_eq_one_iff.mp hc)
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd ho1
  -- `x ^ (o / p)` has order `p`
  have hmain : o / (o / p) = p := Nat.div_div_self hpdvd ho_pos.ne'
  have hzo : orderOf (x ^ (o / p)) = p := by
    rw [orderOf_pow]
    have hgcd : (orderOf x).gcd (o / p) = o / p := by
      rw [ho.symm]; exact Nat.gcd_eq_right (Nat.div_dvd_of_dvd hpdvd)
    rw [hgcd, ← ho]
    exact hmain
  refine ⟨x ^ (o / p), pow_mem_Kset hx _, ?_, ?_⟩
  · intro hc
    have h1 : orderOf (x ^ (o / p)) = 1 := by rw [hc, orderOf_one]
    rw [hzo] at h1
    exact hpprime.ne_one h1
  · rw [hzo]; exact hpprime

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem prop1b {G : Type} [Group G] [Finite G] (hS : Situation G) (hC4 : ChIIFourProp) (hTF : ThompsonFrobeniusProp) (H Q : Subgroup G) (t : G) (h : IsSplitRankOne H Q t) (hK : ∃ x ∈ Kset H t, x ≠ 1) : Group.IsNilpotent ↥Q := by
  obtain ⟨x, hxK, hx1⟩ := hK
  -- an element `z ∈ K#` of prime order
  obtain ⟨z, hzK, hz1, hzprime⟩ := primeOrder_mem_Kset hxK hx1
  -- Prop. 1 a) (file `prop1a`): `⟨z⟩` acts fixed-point-freely on `Q`
  have hfpfQ : ∀ q ∈ Q, q * z = z * q → q = 1 := prop1a hS hC4 H Q t h z hzK hz1
  have hzD : z ∈ twoPoint H t := (mem_Kset_iff.mp hzK).1
  have hzH : z ∈ H := (Subgroup.mem_inf.mp hzD).1
  have hzN : z ∈ Subgroup.normalizer (Q : Set G) := h.normal hzH
  -- conjugation by `z` is an automorphism of `Q`
  let α : MulAut ↥Q := Subgroup.normalizerMonoidHom Q ⟨z, hzN⟩
  have hα : ∀ q : ↥Q, ((α q : ↥Q) : G) = z * (q : G) * z⁻¹ := by
    intro q
    simp [α]
  have hfpf : ∀ q : ↥Q, α q = q → q = 1 := by
    intro q hq
    have hq' : ((q : ↥Q) : G) = z * (q : G) * z⁻¹ := by simpa [hq] using hα q
    have hcomm : (q : G) * z = z * (q : G) := eq_mul_inv_iff_mul_eq.mp hq'
    exact Subtype.ext (hfpfQ (q : G) q.2 hcomm)
  -- the order of `α` divides the prime `orderOf z`
  have horder : orderOf α ∣ orderOf z := by
    have hdvd := orderOf_map_dvd (Subgroup.normalizerMonoidHom Q)
      (⟨z, hzN⟩ : ↥(Subgroup.normalizer (Q : Set G)))
    have hZ : orderOf (⟨z, hzN⟩ : ↥(Subgroup.normalizer (Q : Set G))) = orderOf z :=
      Subgroup.orderOf_mk z hzN
    rw [hZ] at hdvd
    simpa [α] using hdvd
  by_cases hα1 : α = 1
  · -- `α` is trivial, so every element of `Q` is fixed, i.e. `Q = 1`
    have hsub : Subsingleton ↥Q := ⟨fun a b => by
      have ha : a = 1 := hfpf a (by rw [hα1]; rfl)
      have hb : b = 1 := hfpf b (by rw [hα1]; rfl)
      rw [ha, hb]⟩
    exact @Group.isNilpotent_of_subsingleton ↥Q _ hsub
  · -- otherwise `orderOf α` is the prime `p`, and Thompson's theorem applies
    have hprime' : (orderOf α).Prime := by
      rcases hzprime.eq_one_or_self_of_dvd (orderOf α) horder with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hα1
      · rwa [h1]
    exact hTF ↥Q α hprime' hfpf

end Work.ThmF.ChV12
