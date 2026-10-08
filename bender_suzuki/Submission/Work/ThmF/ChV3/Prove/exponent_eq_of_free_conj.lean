import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

/-- **Peterfalvi II, Ch. V, §3**, the exponent step: if `T` is a subgroup of order `p ^ m` and
`D ≤ N_G(T)` has order `|T| - 1` and acts by conjugation with only the identity fixing a
non-identity element of `T` (`hfree`), then `T` has exponent dividing `p`.

The proof is a counting argument.  For `x ∈ T`, `x ≠ 1`, the map `d ↦ d x d⁻¹` from `D` to `T`
is injective: if `a x a⁻¹ = b x b⁻¹`, then `b⁻¹ a ∈ D` fixes `x`, so `b⁻¹ a = 1` by `hfree`.
Its image therefore has `|D| = |T| - 1` elements, all of them non-identity, and it is contained
in `T \ {1}` which also has `|T| - 1 = |D|` elements; hence the conjugates of `x` under `D` are
*all* the non-identity elements of `T`.  So every non-identity element of `T` has the same order
as `x`; since `T` is a `p`-group, this common order must be `p`. -/
theorem exponent_eq_of_free_conj {G : Type*} [Group G] [Finite G]
    {T D : Subgroup G} {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hcardT : Nat.card ↥T = p ^ m)
    (hDT : D ≤ Subgroup.normalizer (T : Set G))
    (hcardD : Nat.card ↥D = Nat.card ↥T - 1)
    (hfree : ∀ y ∈ D, ∀ x ∈ T, x ≠ 1 → y * x * y⁻¹ = x → y = 1) :
    ∀ x ∈ T, x ^ p = 1 := by
  classical
  intro x hxT
  by_cases hx1 : x = 1
  · rw [hx1, one_pow]
  -- ## The conjugates of `x` by `D` exhaust the non-identity elements of `T`.
  have hconj : ∀ z ∈ T, z ≠ 1 → ∃ y ∈ D, y * x * y⁻¹ = z := by
    intro z hzT hz1
    -- the map `d ↦ d x d⁻¹` is injective on `D`
    have hinj : Set.InjOn (fun y : G => y * x * y⁻¹) (D : Set G) := by
      intro a ha b hb hab
      beta_reduce at hab
      have h2 : b⁻¹ * (a * x * a⁻¹) * b = x := by
        rw [hab]; group
      have h3 : (b⁻¹ * a) * x * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * x * a⁻¹) * b := by
        group
      have h1 : (b⁻¹ * a) * x * (b⁻¹ * a)⁻¹ = x := by rw [h3, h2]
      have hw : b⁻¹ * a ∈ D := mul_mem (inv_mem hb) ha
      have h4 : b⁻¹ * a = 1 := hfree (b⁻¹ * a) hw x hxT hx1 h1
      exact (inv_mul_eq_one.mp h4).symm
    -- its image has `|D| = |T| - 1` elements
    have hcard_img : ((fun y : G => y * x * y⁻¹) '' (D : Set G)).ncard = Nat.card ↥T - 1 := by
      rw [hinj.ncard_image]
      rw [← Nat.card_coe_set_eq (D : Set G)]
      exact hcardD
    -- it consists of non-identity elements of `T`
    have hsub : ((fun y : G => y * x * y⁻¹) '' (D : Set G)) ⊆ {z : G | z ∈ T ∧ z ≠ 1} := by
      rintro z ⟨y, hyD, rfl⟩
      refine ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hDT hyD) x).mp hxT
      · intro h
        beta_reduce at h
        apply hx1
        have hxeq : x = y⁻¹ * (y * x * y⁻¹) * (y⁻¹)⁻¹ := by group
        rw [hxeq, h]
        simp
    -- and `T \ {1}` has `|T| - 1` elements too, so the two sets coincide
    have htcard : ({z : G | z ∈ T ∧ z ≠ 1}).ncard = Nat.card ↥T - 1 := by
      have hset : ({z : G | z ∈ T ∧ z ≠ 1}) = (T : Set G) \ {1} := by ext z; simp
      rw [hset]
      rw [Set.ncard_sdiff (s := ({1} : Set G)) (t := (T : Set G)) (by
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        rw [ha]; exact T.one_mem)]
      rw [Set.ncard_singleton, ← Nat.card_coe_set_eq (T : Set G)]
      norm_num
    have hle : ({z : G | z ∈ T ∧ z ≠ 1}).ncard ≤
        ((fun y : G => y * x * y⁻¹) '' (D : Set G)).ncard := by
      rw [htcard, hcard_img]
    have heq : (fun y : G => y * x * y⁻¹) '' (D : Set G) = {z : G | z ∈ T ∧ z ≠ 1} :=
      Set.eq_of_subset_of_ncard_le hsub hle
    have hmem : z ∈ (fun y : G => y * x * y⁻¹) '' (D : Set G) := by
      rw [heq]; exact ⟨hzT, hz1⟩
    rw [Set.mem_image] at hmem
    obtain ⟨y, hyD, hyx⟩ := hmem
    exact ⟨y, hyD, hyx⟩
  -- ## Hence all non-identity elements of `T` have the same order.
  have hkey : ∀ z ∈ T, z ≠ 1 → orderOf z = orderOf x := by
    intro z hzT hz1
    obtain ⟨y, hyD, hyz⟩ := hconj z hzT hz1
    rw [← hyz]
    have := orderOf_injective (MulAut.conj y : G →* G) (MulAut.conj y).injective x
    simpa using this
  have hxord_ne : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  -- ## `orderOf x` divides `|T| = p ^ m`, so it is a power of `p`.
  have hdvd : orderOf x ∣ p ^ m := by
    have h := orderOf_dvd_natCard (⟨x, hxT⟩ : ↥T)
    rw [Subgroup.orderOf_mk] at h
    rwa [← hcardT]
  obtain ⟨j, _hjle, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hjpos : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · exfalso; rw [h0, pow_zero] at hj; exact hxord_ne hj
    · exact hpos
  -- ## Conclusion: `x ^ p = 1`.
  by_contra hxp
  have hxp_mem : x ^ p ∈ T := pow_mem hxT p
  have hxp_ne : x ^ p ≠ 1 := hxp
  have hord : orderOf (x ^ p) = p ^ j := by
    rw [hkey (x ^ p) hxp_mem hxp_ne, hj]
  have hdvd2 : orderOf (x ^ p) ∣ p ^ (j - 1) := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have hmul : p * p ^ (j - 1) = p ^ j := by
      conv_rhs => rw [show j = (j - 1) + 1 by omega, pow_succ']
    rw [← pow_mul, hmul, ← hj, pow_orderOf_eq_one]
  have hdvd3 : p ^ j ∣ p ^ (j - 1) := by rw [← hord]; exact hdvd2
  have hle' : p ^ j ≤ p ^ (j - 1) := Nat.le_of_dvd (pow_pos hp.pos (j - 1)) hdvd3
  have hlt : p ^ (j - 1) < p ^ j := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

end Work.ThmF.ChV3.Prove
