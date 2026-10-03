import Mathlib.Data.ZMod.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

open Set

/-- An equivalence of rings carries the zero set of the polynomial `X^2 + Y^4`
(interpreted on pairs, coordinatewise) onto the corresponding zero set in the
target ring. -/
private lemma X2Y4_pair_roots_ringEquiv_image {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    ((fun p : R × R => (e p.1, e p.2)) '' ({p : R × R | p.1 ^ 2 + p.2 ^ 4 = 0} : Set (R × R))) =
      {q : S × S | q.1 ^ 2 + q.2 ^ 4 = 0} := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    change (e p.1) ^ 2 + (e p.2) ^ 4 = 0
    rw [← map_pow e p.1 2, ← map_pow e p.2 4, ← map_add, hp, map_zero]
  · intro hq
    change q.1 ^ 2 + q.2 ^ 4 = 0 at hq
    refine ⟨(e.symm q.1, e.symm q.2), ?_, ?_⟩
    · change (e.symm q.1) ^ 2 + (e.symm q.2) ^ 4 = 0
      rw [← map_pow e.symm q.1 2, ← map_pow e.symm q.2 4, ← map_add, hq, map_zero]
    · simp

/-- In a product ring, the equation `X^2 + Y^4 = 0` holds exactly when both
componentwise equations hold. -/
private lemma X2Y4_pair_roots_prod_iff {R S : Type*} [CommRing R] [CommRing S]
    (q : (R × S) × (R × S)) :
    q.1 ^ 2 + q.2 ^ 4 = 0 ↔ q.1.1 ^ 2 + q.2.1 ^ 4 = 0 ∧ q.1.2 ^ 2 + q.2.2 ^ 4 = 0 := by
  constructor
  · intro hp
    constructor
    · have h1 := congrArg Prod.fst hp
      simpa [pow_two, pow_succ] using h1
    · have h2 := congrArg Prod.snd hp
      simpa [pow_two, pow_succ] using h2
  · rintro ⟨h1, h2⟩
    apply Prod.ext
    · simpa [pow_two, pow_succ] using h1
    · simpa [pow_two, pow_succ] using h2

theorem X2Y4_pair_roots_mul_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    ({x : ZMod (m * n) × ZMod (m * n) | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard) =
      ({x : ZMod m × ZMod m | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard) *
        ({x : ZMod n × ZMod n | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard) := by
  let e : ZMod (m * n) ≃+* ZMod m × ZMod n := ZMod.chineseRemainder hcop
  let S : Set (ZMod (m * n) × ZMod (m * n)) := {p | p.1 ^ 2 + p.2 ^ 4 = 0}
  let ψ : (ZMod (m * n) × ZMod (m * n)) → (ZMod m × ZMod n) × (ZMod m × ZMod n) :=
    fun p => (e p.1, e p.2)
  let B : Set ((ZMod m × ZMod n) × (ZMod m × ZMod n)) := {q | q.1 ^ 2 + q.2 ^ 4 = 0}
  let A_m : Set (ZMod m × ZMod m) := {p | p.1 ^ 2 + p.2 ^ 4 = 0}
  let A_n : Set (ZMod n × ZMod n) := {p | p.1 ^ 2 + p.2 ^ 4 = 0}
  let σ : ((ZMod m × ZMod n) × (ZMod m × ZMod n)) ≃
      ((ZMod m × ZMod m) × (ZMod n × ZMod n)) :=
    { toFun := fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2)),
      invFun := fun r => ((r.1.1, r.2.1), (r.1.2, r.2.2)),
      left_inv := by
        intro q
        rcases q with ⟨⟨a, c⟩, ⟨b, d⟩⟩
        rfl,
      right_inv := by
        intro r
        rcases r with ⟨⟨a, b⟩, ⟨c, d⟩⟩
        rfl }
  have hψinj : Function.Injective ψ := by
    intro p q hpq
    have h1 : e p.1 = e q.1 := congrArg Prod.fst hpq
    have h2 : e p.2 = e q.2 := congrArg Prod.snd hpq
    exact Prod.ext (e.injective h1) (e.injective h2)
  have himg : ψ '' S = B := by
    change ((fun p : ZMod (m * n) × ZMod (m * n) => (e p.1, e p.2)) '' S) =
      {q : (ZMod m × ZMod n) × (ZMod m × ZMod n) | q.1 ^ 2 + q.2 ^ 4 = 0}
    exact X2Y4_pair_roots_ringEquiv_image e
  have hσimg : σ '' B = A_m ×ˢ A_n := by
    ext r
    constructor
    · rintro ⟨q, hqB, rfl⟩
      have hdec := (X2Y4_pair_roots_prod_iff (R := ZMod m) (S := ZMod n) q).mp hqB
      rcases q with ⟨⟨a, c⟩, ⟨b, d⟩⟩
      change a ^ 2 + b ^ 4 = 0 ∧ c ^ 2 + d ^ 4 = 0 at hdec
      change ((a, b) ∈ A_m ∧ (c, d) ∈ A_n)
      exact ⟨hdec.1, hdec.2⟩
    · intro hr
      rcases r with ⟨⟨a, b⟩, ⟨c, d⟩⟩
      change (a, b) ∈ A_m ∧ (c, d) ∈ A_n at hr
      refine ⟨((a, c), (b, d)), ?_, ?_⟩
      · change (a, c) ^ 2 + (b, d) ^ 4 = 0
        exact (X2Y4_pair_roots_prod_iff (R := ZMod m) (S := ZMod n) ((a, c), (b, d))).mpr hr
      · rfl
  calc
    S.ncard = (ψ '' S).ncard := (Set.ncard_image_of_injective S hψinj).symm
    _ = B.ncard := by rw [himg]
    _ = (σ '' B).ncard := by rw [Set.ncard_image_of_injective B σ.injective]
    _ = (A_m ×ˢ A_n).ncard := by rw [hσimg]
    _ = A_m.ncard * A_n.ncard := Set.ncard_prod

end Commons.NumberTheory.FriedlanderIwaniec