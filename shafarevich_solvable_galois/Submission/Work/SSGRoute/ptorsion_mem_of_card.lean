import Mathlib.Data.ZMod.QuotientGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

namespace Work.SSGRoute

/-- **The `p`-torsion of a cyclic group lies in every subgroup whose order is divisible by `p`.**

Let `B` be a finite additive commutative group with `u : B` a cyclic generator, i.e.
`addOrderOf u = Nat.card B` (so `B ≃ ℤ/Nat.card B`), let `H ≤ B` be a subgroup with
`Nat.card H = d`, where `d ∣ Nat.card B`, and let `p` be a prime with `p ∣ d`. Then every element of
`B` killed by `p` lies in `H`.

(Sketch: in `B ≅ ℤ/n` the subgroup of order `d` is `{y : d • y = 0}` and it contains the unique
subgroup of order `p`, which is `{y : p • y = 0}` because `p ∣ d`. Formalisation route: transport
along the additive equivalence `ZMod (Nat.card B) ≃+ B`, `m ↦ m • u` (well defined since
`Nat.card B • u = 0`), or use that subgroups of a cyclic group are ordered by divisibility of their
orders.) -/
theorem ptorsion_mem_of_card {B : Type*} [AddCommGroup B] [Finite B]
    (u : B) (hu : addOrderOf u = Nat.card B) (H : AddSubgroup B) {d : ℕ}
    (hH : Nat.card H = d) (hdvd : d ∣ Nat.card B) {p : ℕ} [Fact p.Prime] (hp : p ∣ d)
    (x : B) (hx : p • x = 0) : x ∈ H := by
  classical
  -- `u` generates `B`.
  have htop : AddSubgroup.zmultiples u = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples]
    exact hu
  -- hence `x = a • u` for some integer `a`.
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a • u = x := by
    have hxmem : x ∈ AddSubgroup.zmultiples u := by rw [htop]; exact AddSubgroup.mem_top x
    exact AddSubgroup.mem_zmultiples_iff.mp hxmem
  have hxZ : (p : ℤ) • x = 0 := by
    rw [Nat.cast_smul_eq_nsmul ℤ p x]
    exact hx
  -- `p • x = 0` translates to `(p * a) • u = 0`, i.e. `Nat.card B ∣ p * a`.
  have hpa : ((p : ℤ) * a) • u = 0 := by
    rw [mul_zsmul, ha, hxZ]
  have hdiv : (Nat.card B : ℤ) ∣ (p : ℤ) * a := by
    rw [← hu, addOrderOf_dvd_iff_zsmul_eq_zero]
    exact hpa
  -- `Nat.card B = H.index * d` and `d = p * e`, so `H.index * e ∣ a`.
  obtain ⟨e, he⟩ := hp
  have hcardB : Nat.card B = H.index * d := by
    rw [← AddSubgroup.index_mul_card H, hH]
  have hBp : (Nat.card B : ℤ) = (p : ℤ) * ((H.index * e : ℕ) : ℤ) := by
    rw [hcardB, he]
    push_cast
    ring
  rw [hBp] at hdiv
  have hp0 : (p : ℤ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hqe : (((H.index * e : ℕ)) : ℤ) ∣ a := (Int.mul_dvd_mul_iff_left hp0).mp hdiv
  have hq : ((H.index : ℕ) : ℤ) ∣ a := by
    have h1 : ((H.index : ℕ) : ℤ) ∣ ((H.index * e : ℕ) : ℤ) := by
      push_cast
      exact dvd_mul_right _ _
    exact h1.trans hqe
  -- `H.index • u ∈ H` (the index annihilates the quotient `B ⧸ H`), so `x = a • u`
  -- with `H.index ∣ a` lies in `H`.
  obtain ⟨c, hc⟩ := hq
  have hmem : ((H.index : ℤ) • u) ∈ H := by
    simpa using AddSubgroup.nsmul_index_mem H u
  have hgen : x ∈ H := by
    rw [← ha, hc]
    rw [show ((↑H.index : ℤ) * c) • u = c • ((↑H.index : ℤ) • u) by rw [mul_comm, mul_zsmul]]
    exact AddSubgroup.zsmul_mem H hmem c
  exact hgen

end Work.SSGRoute
