import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB

/-- In a monoid, an element of order dividing two, raised to an odd power, is itself. -/
lemma pow_eq_self_of_sq_eq_one_of_odd {M : Type*} [Monoid M] {a : M} (ha : a * a = 1) {n : ℕ}
    (hn : Odd n) : a ^ n = a := by
  obtain ⟨k, rfl⟩ := hn
  have h2 : a ^ 2 = 1 := by rw [pow_two, ha]
  rw [pow_succ, pow_mul, h2, one_pow, one_mul]

/-- The inverse of an involution, raised to an odd power, is the element itself. -/
lemma inv_pow_eq_self_of_odd {M : Type*} [Group M] {a : M} (ha : a * a = 1) {n : ℕ}
    (hn : Odd n) : a⁻¹ ^ n = a := by
  have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  rw [h1]
  exact pow_eq_self_of_sq_eq_one_of_odd ha hn

/-- **Cocycles on odd-order groups into an elementary abelian 2-group are coboundaries.**

Let `P`, `A` be subgroups of a finite group `G` with `A` abelian of exponent `2`
(`hcomm`, `hsq`) and normalized by `P` (`hnorm`), and suppose `P` has odd order (`hodd`).
If `c : G → G` is a `1`-cocycle for the action of `P` on `A` by conjugation
(`hcocycle`, `hmem`), then it is a coboundary: the element `z = ∏_{p ∈ P} c p ∈ A`
satisfies `p⁻¹ * z * p = c p * z` for all `p ∈ P`. -/
theorem cocycle_prod_is_coboundary {G : Type} [Group G] [Finite G] {P A : Subgroup G}
    (hnorm : ∀ p ∈ P, ∀ a ∈ A, p⁻¹ * a * p ∈ A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hsq : ∀ a ∈ A, a * a = 1)
    (hodd : Odd (Nat.card P))
    (c : G → G) (hmem : ∀ p ∈ P, c p ∈ A)
    (hcocycle : ∀ r ∈ P, ∀ p ∈ P, c (r * p) = (p⁻¹ * c r * p) * c p) :
    ∃ z ∈ A, ∀ p ∈ P, p⁻¹ * z * p = c p * z := by
  classical
  have : Fintype P := Fintype.ofFinite P
  -- `A` is abelian, so view it as a commutative monoid to form products of its elements.
  let : CommMonoid A := { mul_comm := fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2) }
  -- The cocycle `c` as an `A`-valued map on `P`.
  let f : P → A := fun p => ⟨c (p : G), hmem (p : G) p.2⟩
  refine ⟨((∏ p : P, f p : A) : G), (∏ p : P, f p).2, ?_⟩
  intro p hp
  set q : P := ⟨p, hp⟩ with hq
  have hqp : (q : G) = p := by rw [hq]
  -- Conjugation by `q⁻¹` as an endomorphism of `A`.
  let Φ : A →* A :=
    { toFun := fun a => ⟨(q : G)⁻¹ * (a : G) * (q : G), hnorm (q : G) q.2 (a : G) a.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp [mul_assoc] }
  -- The cocycle relation becomes `Φ (f x) = f (x * q) * (f q)⁻¹`.
  have hstep : ∀ x : P, Φ (f x) = f (x * q) * (f q)⁻¹ := by
    intro x
    have hcyc : c ((x : G) * (q : G)) = ((q : G)⁻¹ * c (x : G) * (q : G)) * c (q : G) :=
      hcocycle (x : G) x.2 (q : G) q.2
    apply Subtype.ext
    show (q : G)⁻¹ * c (x : G) * (q : G) = c ((x * q : P) : G) * (c (q : G))⁻¹
    rw [Subgroup.coe_mul, hcyc]
    group
  -- Reindex the product by multiplication by `q`.
  have hreindex : (∏ x : P, f (x * q)) = ∏ x : P, f x := by
    refine Fintype.prod_equiv (Equiv.mulRight q) (fun x => f (x * q)) f ?_
    intro x; rfl
  -- `(f q)⁻¹ ^ |P| = f q` since `f q` is an involution and `|P|` is odd.
  have hpow : (f q)⁻¹ ^ (Fintype.card P) = f q := by
    apply inv_pow_eq_self_of_odd
    · apply Subtype.ext
      show c (q : G) * c (q : G) = 1
      exact hsq (c (q : G)) (hmem (q : G) q.2)
    · rw [← Nat.card_eq_fintype_card]; exact hodd
  -- Combining the previous steps: `Φ (∏ f) = (∏ f) * f q`.
  have key : Φ (∏ x : P, f x) = (∏ x : P, f x) * f q := by
    rw [map_prod Φ f Finset.univ]
    calc ∏ x : P, Φ (f x) = ∏ x : P, (f (x * q) * (f q)⁻¹) := by
          exact Finset.prod_congr rfl (fun x _ => hstep x)
      _ = (∏ x : P, f (x * q)) * (f q)⁻¹ ^ (Fintype.card P) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      _ = (∏ x : P, f x) * (f q)⁻¹ ^ (Fintype.card P) := by rw [hreindex]
      _ = (∏ x : P, f x) * f q := by rw [hpow]
  -- Translate `key` back to `G`.
  have hmain : (q : G)⁻¹ * ((∏ x : P, f x : A) : G) * (q : G)
      = c (q : G) * ((∏ x : P, f x : A) : G) := by
    have h1 : (q : G)⁻¹ * ((∏ x : P, f x : A) : G) * (q : G)
        = ((Φ (∏ x : P, f x) : A) : G) := rfl
    rw [h1, key]
    show ((∏ x : P, f x : A) : G) * c (q : G) = c (q : G) * ((∏ x : P, f x : A) : G)
    exact hcomm _ (∏ x : P, f x).2 _ (hmem (q : G) q.2)
  rw [← hqp]
  exact hmain

end Work.PSU3.StageB
