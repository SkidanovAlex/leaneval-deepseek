import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_eq_two
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_two_eq_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- If `x ^ 2 + y ^ 4 = 0` with `y ≠ 0` in the field `ZMod p`, then
`(x · (y²)⁻¹)² = -1`. -/
lemma X2Y4_pair_fwd {p : ℕ} (hp : p.Prime) {x y : ZMod p} (hy : y ≠ 0)
    (h : x ^ 2 + y ^ 4 = 0) : (x * (y ^ 2)⁻¹) ^ 2 = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  have hx2 : x ^ 2 = -y ^ 4 := eq_neg_of_add_eq_zero_left h
  have hy4 : y ^ 4 = (y ^ 2) ^ 2 := by ring
  calc
    (x * (y ^ 2)⁻¹) ^ 2 = x ^ 2 * ((y ^ 2)⁻¹) ^ 2 := by ring
    _ = -y ^ 4 * ((y ^ 2)⁻¹) ^ 2 := by rw [hx2]
    _ = -(y ^ 2) ^ 2 * ((y ^ 2)⁻¹) ^ 2 := by rw [hy4]
    _ = -1 := by
      rw [neg_mul, ← mul_pow, mul_inv_cancel₀ hy2, one_pow]

/-- If `u ^ 2 = -1` then `(u · v²)² + v⁴ = 0`. -/
lemma X2Y4_pair_back {p : ℕ} (hp : p.Prime) {u v : ZMod p} (hu : u ^ 2 = -1) :
    (u * v ^ 2) ^ 2 + v ^ 4 = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  calc
    (u * v ^ 2) ^ 2 + v ^ 4 = u ^ 2 * (v ^ 2) ^ 2 + v ^ 4 := by ring
    _ = u ^ 2 * v ^ 4 + v ^ 4 := by ring
    _ = (-1) * v ^ 4 + v ^ 4 := by rw [hu]
    _ = 0 := by ring

/-- `((x · (y²)⁻¹) · y²) = x` for `y ≠ 0`. -/
lemma X2Y4_pair_retract_fwd {p : ℕ} (hp : p.Prime) {x y : ZMod p} (hy : y ≠ 0) :
    ((x * (y ^ 2)⁻¹) * y ^ 2) = x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  calc
    (x * (y ^ 2)⁻¹) * y ^ 2 = x * ((y ^ 2)⁻¹ * y ^ 2) := by ring
    _ = x * 1 := by rw [inv_mul_cancel₀ hy2]
    _ = x := by simp

/-- `((u · v²) · (v²)⁻¹) = u` for `v ≠ 0`. -/
lemma X2Y4_pair_retract_back {p : ℕ} (hp : p.Prime) {u v : ZMod p} (hv : v ≠ 0) :
    (u * v ^ 2) * (v ^ 2)⁻¹ = u := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv
  calc
    (u * v ^ 2) * (v ^ 2)⁻¹ = u * (v ^ 2 * (v ^ 2)⁻¹) := by ring
    _ = u * 1 := by rw [mul_inv_cancel₀ hv2]
    _ = u := by simp

/-- There are `p - 1` nonzero elements in `ZMod p`. -/
lemma X2Y4_ncard_ne_zero_zmod_prime {p : ℕ} (hp : p.Prime) :
    ({v : ZMod p | v ≠ 0}.ncard) = p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : ({v : ZMod p | v ≠ 0} : Set (ZMod p)) = Set.univ \ ({0} : Set (ZMod p)) := by
    ext v
    simp
  rw [h]
  rw [Set.ncard_sdiff_singleton_of_mem (a := (0 : ZMod p)) (s := (Set.univ : Set (ZMod p)))]
  · rw [Set.ncard_univ, Nat.card_zmod]
  · simp

/-- The pairs with `y = 0` contribute exactly one solution, `(0, 0)`. -/
lemma X2Y4_pair_count_split {p : ℕ} (hp : p.Prime) :
    ({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard) =
      1 + ({x : ZMod p × ZMod p | x.2 ≠ 0 ∧ x.1 ^ 2 + x.2 ^ 4 = 0}.ncard) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hS_eq : ({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0} : Set (ZMod p × ZMod p)) =
      ({(0, 0)} : Set (ZMod p × ZMod p)) ∪
        ({x : ZMod p × ZMod p | x.2 ≠ 0 ∧ x.1 ^ 2 + x.2 ^ 4 = 0}) := by
    ext z
    constructor
    · intro hz
      by_cases hz2 : z.2 = 0
      · left
        have hx : z.1 = 0 := by
          apply sq_eq_zero_iff.mp
          simpa [hz2] using hz
        exact Prod.ext hx hz2
      · right
        exact ⟨hz2, hz⟩
    · intro hz
      rcases hz with hz0 | hzB
      · rw [hz0]
        simp
      · exact hzB.2
  have hdisj : Disjoint ({(0, 0)} : Set (ZMod p × ZMod p))
      ({x : ZMod p × ZMod p | x.2 ≠ 0 ∧ x.1 ^ 2 + x.2 ^ 4 = 0}) := by
    rw [Set.disjoint_left]
    intro z hz0 hzB
    rw [Set.mem_singleton_iff] at hz0
    subst z
    exact hzB.1 rfl
  rw [hS_eq, Set.ncard_union_eq hdisj]
  simp

/-- For `y ≠ 0`, the number of solutions `x` of `x ^ 2 + y ^ 4 = 0` does not
depend on `y`; it equals the number of square roots of `-1` in `ZMod p`,
and there are `p - 1` admissible values of `y`. -/
lemma X2Y4_pair_count_nonzero {p : ℕ} (hp : p.Prime) :
    ({x : ZMod p × ZMod p | x.2 ≠ 0 ∧ x.1 ^ 2 + x.2 ^ 4 = 0}.ncard) =
      ({u : ZMod p | u ^ 2 = -1}.ncard) * (p - 1) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let B : Set (ZMod p × ZMod p) := {x | x.2 ≠ 0 ∧ x.1 ^ 2 + x.2 ^ 4 = 0}
  let T : Set (ZMod p × ZMod p) := {x | x.1 ^ 2 = -1 ∧ x.2 ≠ 0}
  let Φ : (ZMod p × ZMod p) → (ZMod p × ZMod p) := fun z => (z.1 * (z.2 ^ 2)⁻¹, z.2)
  let Ψ : (ZMod p × ZMod p) → (ZMod p × ZMod p) := fun w => (w.1 * w.2 ^ 2, w.2)
  have hΦ_mem : ∀ z : ZMod p × ZMod p, z ∈ B → Φ z ∈ T := by
    intro z hz
    have hy : z.2 ≠ 0 := hz.1
    have h1 : (Φ z).1 ^ 2 = -1 := by
      change (z.1 * (z.2 ^ 2)⁻¹) ^ 2 = -1
      exact X2Y4_pair_fwd hp hy hz.2
    exact ⟨h1, by simpa [Φ] using hy⟩
  have hΨ_mem : ∀ w : ZMod p × ZMod p, w ∈ T → Ψ w ∈ B := by
    intro w hw
    have hv : w.2 ≠ 0 := hw.2
    have h1 : (Ψ w).2 ≠ 0 := by simpa [Ψ] using hv
    have h2 : (Ψ w).1 ^ 2 + (Ψ w).2 ^ 4 = 0 := by
      change (w.1 * w.2 ^ 2) ^ 2 + w.2 ^ 4 = 0
      exact X2Y4_pair_back hp hw.1
    exact ⟨h1, h2⟩
  have hΨΦ : ∀ z : ZMod p × ZMod p, z ∈ B → Ψ (Φ z) = z := by
    intro z hz
    apply Prod.ext
    · change (z.1 * (z.2 ^ 2)⁻¹) * z.2 ^ 2 = z.1
      exact X2Y4_pair_retract_fwd hp hz.1
    · rfl
  have hΦΨ : ∀ w : ZMod p × ZMod p, w ∈ T → Φ (Ψ w) = w := by
    intro w hw
    apply Prod.ext
    · change (w.1 * w.2 ^ 2) * (w.2 ^ 2)⁻¹ = w.1
      exact X2Y4_pair_retract_back hp hw.2
    · rfl
  have hImg : Φ '' B = T := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hΦ_mem z hz
    · intro hw
      refine ⟨Ψ w, hΨ_mem w hw, hΦΨ w hw⟩
  have hInj : Set.InjOn Φ B := by
    intro z hz w hw heq
    calc
      z = Ψ (Φ z) := (hΨΦ z hz).symm
      _ = Ψ (Φ w) := congrArg Ψ heq
      _ = w := hΨΦ w hw
  have hB : B.ncard = T.ncard := by
    rw [← hImg]
    exact (Set.InjOn.ncard_image hInj).symm
  have hT : T = ({u : ZMod p | u ^ 2 = -1} ×ˢ {v : ZMod p | v ≠ 0}) := by
    ext w
    simp [T]
  calc
    ({x : ZMod p × ZMod p | x.2 ≠ 0 ∧ x.1 ^ 2 + x.2 ^ 4 = 0}.ncard) = B.ncard := rfl
    _ = T.ncard := hB
    _ = ({u : ZMod p | u ^ 2 = -1} ×ˢ {v : ZMod p | v ≠ 0}).ncard := by rw [hT]
    _ = ({u : ZMod p | u ^ 2 = -1}.ncard) * ({v : ZMod p | v ≠ 0}.ncard) := by simp
    _ = ({u : ZMod p | u ^ 2 = -1}.ncard) * (p - 1) := by
      rw [X2Y4_ncard_ne_zero_zmod_prime hp]

/-- A prime `p ≡ 3 (mod 4)`: the only solution of `x ^ 2 + y ^ 4 = 0` is
`(0, 0)`. -/
lemma X2Y4_pair_card_mod_four_three {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard) = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hS : ({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0} : Set (ZMod p × ZMod p)) =
      ({(0, 0)} : Set (ZMod p × ZMod p)) := by
    ext z
    constructor
    · intro hz
      have hz2 : z.2 = 0 := by
        by_contra hne
        have hy2 : z.2 ^ 2 ≠ 0 := pow_ne_zero 2 hne
        have hx2 : z.1 ^ 2 = -z.2 ^ 4 := eq_neg_of_add_eq_zero_left hz
        have hy4 : z.2 ^ 4 = (z.2 ^ 2) ^ 2 := by ring
        have hx2' : z.1 ^ 2 = -(z.2 ^ 2) ^ 2 := by rwa [hy4] at hx2
        exact (ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (x := z.1) (y := z.2 ^ 2) hy2 hx2') hp4
      have hx : z.1 = 0 := by
        apply sq_eq_zero_iff.mp
        simpa [hz2] using hz
      exact Prod.ext hx hz2
    · intro hz
      rw [hz]
      simp
  rw [hS]
  simp

/-- For `p = 2`, the solutions are `(0, 0)` and `(1, 1)`. -/
lemma X2Y4_pair_card_eq_two {p : ℕ} (hp : p.Prime) (h2 : p = 2) :
    ({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard) = 2 := by
  subst p
  have hdec := X2Y4_pair_count_split hp
  have hpc := X2Y4_pair_count_nonzero hp
  have hroots : ({u : ZMod 2 | u ^ 2 = -1}.ncard) = 1 := sq_roots_neg_one_mod_two_eq_one
  calc
    ({x : ZMod 2 × ZMod 2 | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard) =
        1 + ({x : ZMod 2 × ZMod 2 | x.2 ≠ 0 ∧ x.1 ^ 2 + x.2 ^ 4 = 0}.ncard) := hdec
    _ = 1 + ({u : ZMod 2 | u ^ 2 = -1}.ncard) * (2 - 1) := by rw [hpc]
    _ = 2 := by rw [hroots]

/-- For a prime `p ≡ 1 (mod 4)` there are `2 p - 1` solutions. -/
lemma X2Y4_pair_card_mod_four_one {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    ({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard) = 2 * p - 1 := by
  have hdec := X2Y4_pair_count_split hp
  have hpc := X2Y4_pair_count_nonzero hp
  have hroots : ({u : ZMod p | u ^ 2 = -1}.ncard) = 2 := sq_roots_neg_one_mod_prime_eq_two hp hp4
  calc
    ({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard) =
        1 + ({x : ZMod p × ZMod p | x.2 ≠ 0 ∧ x.1 ^ 2 + x.2 ^ 4 = 0}.ncard) := hdec
    _ = 1 + ({u : ZMod p | u ^ 2 = -1}.ncard) * (p - 1) := by rw [hpc]
    _ = 1 + 2 * (p - 1) := by rw [hroots]
    _ = 2 * p - 1 := by
      have hp2 : 2 ≤ p := hp.two_le
      omega

theorem X2Y4_pair_roots_mod_prime_card {p : ℕ} (hp : p.Prime) :
    ({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard) =
      if p % 4 = 3 then 1 else if p = 2 then 2 else 2 * p - 1 := by
  by_cases h43 : p % 4 = 3
  · rw [if_pos h43]
    exact X2Y4_pair_card_mod_four_three hp h43
  · rw [if_neg h43]
    by_cases h2 : p = 2
    · rw [if_pos h2]
      exact X2Y4_pair_card_eq_two hp h2
    · rw [if_neg h2]
      have hp4 : p % 4 = 1 := by
        have hlt : p % 4 < 4 := Nat.mod_lt p (by norm_num)
        have hmod2 : (p % 4) % 2 = 1 := by
          rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 4)]
          exact (Nat.Prime.eq_two_or_odd hp).resolve_left h2
        interval_cases p % 4 <;> omega
      exact X2Y4_pair_card_mod_four_one hp hp4

end Commons.NumberTheory.FriedlanderIwaniec