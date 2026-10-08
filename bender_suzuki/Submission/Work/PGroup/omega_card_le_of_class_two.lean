import Mathlib
import Submission.Work.Coprime.trivial_of_trivial_on_omega1
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `|V| ≤ |Ω₁(V)| · |K|` for a class-two group

Let `V` be a finite group, `p` a prime, and `K ≤ Z(V)` a central subgroup containing the
derived subgroup `⁅V, V⁆`, with `K` of exponent dividing `p` and with every `p`-th power of an
element of `V` lying in `K`.  Then `V` has nilpotency class at most two, and the `p`-th power
map `x ↦ x ^ p` is a homomorphism `V →* V`: class two gives
`(x * y) ^ p = ⁅y, x⁆ ^ (p.choose 2) * x ^ p * y ^ p` (`tto_pow_mul_eq_commutator_pow`),
`⁅y, x⁆ ∈ K` has exponent dividing `p`, and `p` odd implies `p ∣ p.choose 2`, so the commutator
factor is trivial.

Its kernel is exactly `Ω = {x : V | x ^ p = 1}`, a normal subgroup of `V`, and its image is
contained in `K` by hypothesis.  Hence

  `|V| = |ker| · |range| = |Ω| · |V ^ p| ≤ |Ω| · |K|`.

This is the "odd order" counting lemma used when `V` is a `p`-group of class two modulo a
central subgroup of exponent `p` (cf. Feit–Thompson, Chapter II).
-/

open scoped commutatorElement

namespace Work.PGroup

theorem omega_card_le_of_class_two {V : Type*} [Group V] [Finite V] {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) {K : Subgroup V} (hKcent : K ≤ Subgroup.center V)
    (hcomm : ∀ x y : V, x * y * x⁻¹ * y⁻¹ ∈ K) (hKexp : ∀ c : K, c ^ p = 1)
    (hpow : ∀ x : V, x ^ p ∈ K) :
    ∃ Ω : Subgroup V, (∀ x : V, x ∈ Ω ↔ x ^ p = 1) ∧ Ω.Normal ∧
      Nat.card V ≤ Nat.card Ω * Nat.card K := by
  classical
  -- Pass to the Mathlib convention for commutators.
  have hcommK : ∀ x y : V, ⁅x, y⁆ ∈ K := by
    intro x y
    rw [commutatorElement_def]
    exact hcomm x y
  -- Every commutator has `p`-th power one, since it lies in the exponent-`p` subgroup `K`.
  have hcommp : ∀ a b : V, ⁅a, b⁆ ^ p = 1 := by
    intro a b
    have h : (⟨⁅a, b⁆, hcommK a b⟩ : K) ^ p = 1 := hKexp _
    simpa using congrArg Subtype.val h
  -- The `p`-th power map is multiplicative.
  have hmul : ∀ x y : V, (x * y) ^ p = x ^ p * y ^ p := by
    intro x y
    rw [Work.Coprime.tto_pow_mul_eq_commutator_pow (hKcent (hcommK y x)) p]
    have hdvd : p ∣ p.choose 2 := by
      obtain ⟨k, hk⟩ := hodd
      rw [Nat.choose_two_right]
      have hp1 : p - 1 = 2 * k := by omega
      rw [hp1, show p * (2 * k) = (p * k) * 2 by ring,
        Nat.mul_div_cancel (p * k) (by norm_num)]
      exact dvd_mul_right p k
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul, hcommp y x, one_pow, one_mul]
  -- The `p`-th power map as a monoid homomorphism `V →* V`.
  let φ : V →* V :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := hmul }
  refine ⟨φ.ker, ?_, φ.normal_ker, ?_⟩
  · intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h; simpa [φ] using h
    · intro h; simpa [φ] using h
  · -- The image of `φ` lies in `K`.
    have hrangeK : φ.range ≤ K := by
      rintro y ⟨x, rfl⟩
      simpa [φ] using hpow x
    have hle : Nat.card ↥φ.range ≤ Nat.card ↥K := Subgroup.card_le_of_le hrangeK
    calc Nat.card V = Nat.card (V ⧸ φ.ker) * Nat.card ↥φ.ker :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
      _ = Nat.card ↥φ.range * Nat.card ↥φ.ker := by
          rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
      _ = Nat.card ↥φ.ker * Nat.card ↥φ.range := Nat.mul_comm _ _
      _ ≤ Nat.card ↥φ.ker * Nat.card ↥K := Nat.mul_le_mul_left _ hle

end Work.PGroup
