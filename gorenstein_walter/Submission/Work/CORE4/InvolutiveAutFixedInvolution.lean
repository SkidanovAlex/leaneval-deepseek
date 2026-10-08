import Mathlib

set_option linter.style.haveILetI false

namespace Work.CORE4

/-- If a finite group `N` of even order admits an involutive automorphism `σ`, then `σ` fixes a
non-trivial involution of `N`.

The proof splits `N` into the fixed points of `σ` and the non-fixed points; the latter are
partitioned into 2-element orbits because `σ` is an involution, so the number of fixed points has
the same parity as `|N|`, hence is even. The fixed points form a subgroup, which therefore contains
an element of order `2` (Cauchy's theorem for `p = 2`). -/
theorem InvolutiveAutFixedInvolution {N : Type*} [Group N] [Finite N]
    (σ : N ≃* N) (hσ : σ * σ = 1) (heven : Even (Nat.card N)) :
    ∃ c : N, c ≠ 1 ∧ c ^ 2 = 1 ∧ σ c = c := by
  classical
  haveI : Fintype N := Fintype.ofFinite N
  -- The subgroup of fixed points of `σ`.
  let C : Subgroup N :=
    { carrier := {x | σ x = x},
      mul_mem' := by
        intro a b ha hb
        show σ (a * b) = a * b
        rw [map_mul, ha, hb]
      one_mem' := by
        show σ 1 = 1
        exact map_one σ
      inv_mem' := by
        intro a ha
        show σ a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hmem : ∀ x : N, (x ∈ C) ↔ σ x = x := fun x => Iff.rfl
  -- Cardinality of `C` as a number of fixed points.
  have hCcard : Nat.card C = (Finset.univ.filter (fun x => σ x = x)).card := by
    rw [Nat.card_eq_fintype_card]
    rw [show Fintype.card C = Fintype.card {x : N // x ∈ C} from rfl]
    rw [Fintype.card_subtype]
    congr 1
  have hσσ : ∀ x : N, σ (σ x) = x := fun x => by
    have h := congr_arg (fun f : N ≃* N => f x) hσ
    simpa using h
  -- The underlying permutation of `σ`, which is an involution (`p ^ 2 = 1`).
  let p : Equiv.Perm N := σ.toEquiv
  have hp : ∀ x, p x = σ x := fun x => rfl
  have hp2 : p ^ 2 = 1 := by
    rw [pow_two]; ext x
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    rw [hp, hp, hσσ]
  have hsupp : p.support = Finset.univ.filter (fun x => σ x ≠ x) := by
    ext x; simp [Equiv.Perm.mem_support, hp]
  -- The fixed points together with the non-fixed points exhaust `N`.
  have hsum : (Finset.univ.filter (fun x => σ x = x)).card + p.support.card = Fintype.card N := by
    rw [hsupp, Finset.card_filter_add_card_filter_not (fun x => σ x = x), Finset.card_univ]
  have hN : 2 ∣ Fintype.card N := by
    rw [← Nat.card_eq_fintype_card]; exact even_iff_two_dvd.mp heven
  have hsupp2 : 2 ∣ p.support.card := Equiv.Perm.two_dvd_card_support hp2
  -- Hence `|C|` is even: `|C| = |N| - #support` with both terms even.
  have hCeven : Even (Nat.card C) := by
    rw [even_iff_two_dvd, hCcard]
    omega
  -- Cauchy's theorem for `p = 2` inside the fixed-point subgroup.
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (even_iff_two_dvd.mp hCeven)
  refine ⟨(c : N), ?_, ?_, ?_⟩
  · have hcoe : orderOf (c : N) = 2 := (Subgroup.orderOf_coe c).trans hc
    intro h
    rw [h, orderOf_one] at hcoe
    exact absurd hcoe (by decide)
  · have hcoe : orderOf (c : N) = 2 := (Subgroup.orderOf_coe c).trans hc
    have := pow_orderOf_eq_one (c : N)
    rwa [hcoe] at this
  · exact (hmem (c : N)).mp c.2

end Work.CORE4
