import Mathlib

/-!
# `Work.CORE4.L2PAux.v2_le_centralizer_cyclic_two`

**Statement.**  If `P ≤ G` is a cyclic `2`-subgroup and `T ≤ G` is a subgroup of odd order lying
in the normalizer `N_G(P)` of `P`, then `P` centralises `T`.

**Proof.**  Fix `t ∈ T`.  Since `T ≤ N_G(P)`, conjugation by `t` restricts to an automorphism
`β` of `P`.  Because `t ∈ T` has order dividing the odd number `|T|`, `orderOf t` is odd; and
`β ^ orderOf t = 1`, so `orderOf β ∣ orderOf t` is odd too.  On the other hand `P` is a finite
cyclic group of order `2 ^ k` for some `k` (a generator `g` of `P` has `orderOf g = 2 ^ k` by
`IsPGroup.iff_orderOf`, and `Nat.card P = orderOf g`), and every automorphism of a finite cyclic
group of order `2 ^ k` has order dividing `IsCyclic.card_mulAut`'s `Nat.card (MulAut P) =
Nat.totient (2 ^ k) = 2 ^ (k - 1)`, a power of two.  Hence `β = 1`, i.e. `t` commutes with every
element of `P`.  As `t ∈ T` was arbitrary, `P ≤ C_G(T)`.

This file is deliberately `Mathlib`-only (no `Work.FUS`, no `Work.CORE2A`): the two arithmetic
facts used are proved locally below.
-/

set_option linter.style.haveILetI false

namespace Work.CORE4.L2PAux

/-! ## The automorphism of a normalized subgroup induced by conjugation -/

/-- Conjugation by `g`, restricted to a subgroup `H` that `g` normalizes; a `MulAut H`. -/
private noncomputable def conjAutOfNormalizer {G : Type*} [Group G] (g : G) (H : Subgroup G)
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : MulAut H where
  toFun x := ⟨g * (x : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (x : G)).mp x.2⟩
  invFun x := ⟨g⁻¹ * (x : G) * g, by
    have h := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (H : Set G)).inv_mem hg) (x : G)).mp x.2
    simpa using h⟩
  left_inv x := by ext; group
  right_inv x := by ext; group
  map_mul' x y := by ext; simp only [Subgroup.coe_mul]; group

@[simp] private lemma conjAutOfNormalizer_coe {G : Type*} [Group G] (g : G) (H : Subgroup G)
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (x : H) :
    ((conjAutOfNormalizer g H hg x : H) : G) = g * (x : G) * g⁻¹ := rfl

private lemma conjAutOfNormalizer_pow_coe {G : Type*} [Group G] (g : G) (H : Subgroup G)
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    ∀ (n : ℕ) (x : H),
      (((conjAutOfNormalizer g H hg) ^ n) x : G) = g ^ n * (x : G) * (g ^ n)⁻¹ := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
      intro x
      change (((conjAutOfNormalizer g H hg) ^ n) ((conjAutOfNormalizer g H hg) x) : G) =
        g ^ (n + 1) * (x : G) * (g ^ (n + 1))⁻¹
      rw [ih ((conjAutOfNormalizer g H hg) x), conjAutOfNormalizer_coe, pow_succ']
      group

/-! ## Two arithmetic facts about `MulAut` of a cyclic `2`-group -/

/-- The totient of a power of two divides that power of two. -/
private lemma totient_two_pow_dvd (k : ℕ) : Nat.totient (2 ^ k) ∣ 2 ^ k := by
  rcases k with _ | k
  · simp
  · rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k)]
    have h : 2 ^ k ∣ 2 ^ (k + 1) := pow_dvd_pow 2 (Nat.le_succ k)
    simpa using h

/-- A finite cyclic group of order `2 ^ k` has no automorphism of odd order `≠ 1`: the order of an
automorphism divides `Nat.card (MulAut A) = Nat.totient (2 ^ k) ∣ 2 ^ k`. -/
private lemma mulAut_eq_one_of_odd_order {A : Type*} [Group A] [Finite A] (hcyc : IsCyclic A)
    (k : ℕ) (hcard : Nat.card A = 2 ^ k) (β : A ≃* A) (hodd : Odd (orderOf β)) : β = 1 := by
  have hdvdAut : orderOf β ∣ Nat.card (MulAut A) := orderOf_dvd_natCard β
  rw [@IsCyclic.card_mulAut A _ _ hcyc, hcard] at hdvdAut
  have hdvd : orderOf β ∣ 2 ^ k := hdvdAut.trans (totient_two_pow_dvd k)
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj : j = 0 := by
    by_contra hj
    exact (Nat.not_even_iff_odd.mpr (hjeq ▸ hodd)) (Even.pow_of_ne_zero even_two hj)
  have hone : orderOf β = 1 := by rw [hjeq, hj, pow_zero]
  exact orderOf_eq_one_iff.mp hone

/-! ## The main theorem -/

/-- A cyclic `2`-subgroup is centralized by every odd order subgroup of its normalizer. -/
theorem v2_le_centralizer_cyclic_two {G : Type*} [Group G] (P T : Subgroup G)
    (hcyc : IsCyclic P) (hP : IsPGroup 2 P)
    (hTN : T ≤ Subgroup.normalizer (P : Set G)) (hT : Odd (Nat.card T)) :
    P ≤ Subgroup.centralizer (T : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `P` is a finite cyclic group of order `2 ^ k`.
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2)).mp hP g
  have hcard : Nat.card P = 2 ^ k := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg, hk]
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  -- Conjugation by `t` is an automorphism of `P` of odd order, hence trivial.
  set β : MulAut P := conjAutOfNormalizer t P (hTN ht) with hβdef
  have hpow : β ^ orderOf t = 1 := by
    apply MulEquiv.ext; intro x
    apply Subtype.ext
    rw [hβdef, conjAutOfNormalizer_pow_coe, pow_orderOf_eq_one]; simp
  have hdvdβ : orderOf β ∣ orderOf t := orderOf_dvd_of_pow_eq_one hpow
  have hdvdT : orderOf t ∣ Nat.card T := Subgroup.orderOf_dvd_natCard T ht
  have hoddβ : Odd (orderOf β) := Odd.of_dvd_nat hT (hdvdβ.trans hdvdT)
  have hβ1 : β = 1 := mulAut_eq_one_of_odd_order hcyc k hcard β hoddβ
  -- Hence `t p t⁻¹ = p`, i.e. `t` and `p` commute.
  have hfix : β ⟨p, hp⟩ = ⟨p, hp⟩ := by rw [hβ1]; rfl
  have hval : t * p * t⁻¹ = p := by
    have h2 := congrArg (fun z : P => (z : G)) hfix
    rw [hβdef, conjAutOfNormalizer_coe] at h2
    simpa using h2
  exact mul_inv_eq_iff_eq_mul.mp hval

end Work.CORE4.L2PAux
