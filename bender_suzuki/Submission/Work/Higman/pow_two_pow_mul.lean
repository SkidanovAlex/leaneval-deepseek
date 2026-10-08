import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.Higman

open scoped commutatorElement

/-!
# A `2 ^ E`-power identity in a Suzuki 2-group with `[P, P] ≤ Ω₁(P)`

If a Suzuki 2-group `P` satisfies `[P, P] ≤ Ω₁(P)`, then `P` has nilpotency class two:
`[P, P] ≤ Ω₁(P) ≤ Z(P)` (`omega1_le_center`) and every commutator is an involution
(`h.mem_omega1`).  Consequently the `2 ^ E`-th power map is a homomorphism for `E ≥ 2`:

`(x * y) ^ (2 ^ E) = x ^ (2 ^ E) * y ^ (2 ^ E)`.

The proof is isolated in the purely group-theoretic lemma `pow_two_pow_mul_gen` below, which
assumes only that all commutators are central and have order dividing two.
-/

section ClassTwo

variable {G : Type*} [Group G]

/-- **Class-two squaring.**  If every commutator of `G` is central, then
`(a * b) ^ 2 = ⁅b, a⁆ * (a ^ 2 * b ^ 2)`.

Indeed `b * a = ⁅b, a⁆ * (a * b)`, and `⁅b, a⁆` commutes with `a`. -/
theorem sq_mul_sq_eq_of_commutator_central
    (hcent : ∀ a b : G, ⁅a, b⁆ ∈ Subgroup.center G) (a b : G) :
    (a * b) ^ 2 = ⁅b, a⁆ * (a ^ 2 * b ^ 2) := by
  have hc : ∀ z : G, z * ⁅b, a⁆ = ⁅b, a⁆ * z :=
    fun z => (Subgroup.mem_center_iff.mp (hcent b a)) z
  have hba : b * a = ⁅b, a⁆ * (a * b) := by rw [commutatorElement_def]; group
  have h1 : (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
  have h2 : a * (⁅b, a⁆ * (a * b)) * b = (a * ⁅b, a⁆) * (a * b) * b := by group
  have h3 : (a * ⁅b, a⁆) * (a * b) * b = (⁅b, a⁆ * a) * (a * b) * b := by rw [hc a]
  have h4 : (⁅b, a⁆ * a) * (a * b) * b = ⁅b, a⁆ * (a ^ 2 * b ^ 2) := by
    rw [pow_two, pow_two]; group
  rw [h1, hba, h2, h3, h4]

/-- A central involution can be removed from a square: if `c` is central and `c ^ 2 = 1` then
`(c * w) ^ 2 = w ^ 2`. -/
theorem sq_central_eq (G : Type*) [Group G] {c : G} (hc : c ∈ Subgroup.center G)
    (hc2 : c ^ 2 = 1) (w : G) : (c * w) ^ 2 = w ^ 2 := by
  have h : c * w = w * c := (Subgroup.mem_center_iff.mp hc w).symm
  calc (c * w) ^ 2 = (c * w) * (c * w) := by rw [pow_two]
    _ = c * (w * c) * w := by group
    _ = c * (c * w) * w := by rw [← h]
    _ = (c * c) * (w * w) := by group
    _ = c ^ 2 * w ^ 2 := by rw [pow_two, pow_two]
    _ = w ^ 2 := by rw [hc2, one_mul]

/-- **Bilinearity of the commutator.**  If every commutator is central then
`⁅a, b⁆ ^ (m * n) = ⁅a ^ m, b ^ n⁆`. -/
theorem commutator_pow_mul (hcent : ∀ a b : G, ⁅a, b⁆ ∈ Subgroup.center G)
    (a b : G) (m n : ℕ) : ⁅a, b⁆ ^ (m * n) = ⁅a ^ m, b ^ n⁆ := by
  have hca : Commute a ⁅a, b⁆ := (Subgroup.mem_center_iff.mp (hcent a b)) a
  have hcmb : Commute b ⁅a ^ m, b⁆ := (Subgroup.mem_center_iff.mp (hcent (a ^ m) b)) b
  calc ⁅a, b⁆ ^ (m * n) = (⁅a, b⁆ ^ m) ^ n := by rw [pow_mul]
    _ = ⁅a ^ m, b⁆ ^ n := by rw [Commute.commutatorElement_pow_left hca m]
    _ = ⁅a ^ m, b ^ n⁆ := Commute.commutatorElement_pow_right hcmb n

/-- **The `2 ^ E`-power identity for class-two groups with involutory commutators.**
If every commutator of `G` is central and squares to `1`, then for `E ≥ 2`
`(x * y) ^ (2 ^ E) = x ^ (2 ^ E) * y ^ (2 ^ E)`. -/
theorem pow_two_pow_mul_gen (hcent : ∀ a b : G, ⁅a, b⁆ ∈ Subgroup.center G)
    (h2c : ∀ a b : G, ⁅a, b⁆ ^ 2 = 1) {E : ℕ} (hE : 2 ≤ E) (x y : G) :
    (x * y) ^ 2 ^ E = x ^ 2 ^ E * y ^ 2 ^ E := by
  have hpow4 : (2 : ℕ) ^ 2 = 2 * 2 := by norm_num
  -- `E = 2`: `(x * y) ^ 4 = ((x * y) ^ 2) ^ 2 = (⁅y, x⁆ * x ^ 2 * y ^ 2) ^ 2 = (x ^ 2 * y ^ 2) ^ 2`
  -- and `(x ^ 2 * y ^ 2) ^ 2 = ⁅y ^ 2, x ^ 2⁆ * (x ^ 4 * y ^ 4) = x ^ 4 * y ^ 4`.
  have hbase : (x * y) ^ 2 ^ (2 : ℕ) = x ^ 2 ^ (2 : ℕ) * y ^ 2 ^ (2 : ℕ) := by
    have hcx : ⁅y ^ 2, x ^ 2⁆ = (1 : G) := by
      rw [← commutator_pow_mul hcent y x 2 2, pow_mul, h2c y x, one_pow]
    have hkey : (x ^ 2 * y ^ 2) ^ 2 = x ^ 4 * y ^ 4 := by
      rw [sq_mul_sq_eq_of_commutator_central hcent (x ^ 2) (y ^ 2), hcx, one_mul,
        ← pow_mul, ← pow_mul]
    have hconv : ∀ a : G, a ^ 4 = a ^ 2 ^ (2 : ℕ) := fun a => rfl
    calc (x * y) ^ 2 ^ (2 : ℕ) = ((x * y) ^ 2) ^ 2 := by rw [hpow4, pow_mul]
      _ = (⁅y, x⁆ * (x ^ 2 * y ^ 2)) ^ 2 := by
          rw [sq_mul_sq_eq_of_commutator_central hcent x y]
      _ = (x ^ 2 * y ^ 2) ^ 2 := sq_central_eq G (hcent y x) (h2c y x) (x ^ 2 * y ^ 2)
      _ = x ^ 4 * y ^ 4 := hkey
      _ = x ^ 2 ^ (2 : ℕ) * y ^ 2 ^ (2 : ℕ) := by rw [hconv x, hconv y]
  -- Induction step: `(x * y) ^ 2 ^ (m+1) = ((x * y) ^ 2 ^ m) ^ 2`, then the induction
  -- hypothesis and `⁅y ^ 2 ^ m, x ^ 2 ^ m⁆ = ⁅y, x⁆ ^ (2 ^ m * 2 ^ m) = 1`.
  refine Nat.le_induction hbase ?_ E hE
  intro m hm ih
  have hm1 : 1 ≤ m := by omega
  have hcm : ⁅y, x⁆ ^ (2 : ℕ) ^ m = 1 := by
    have h2m : (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hm1]
    rw [h2m, pow_mul, h2c y x, one_pow]
  have hcom1 : ⁅y ^ (2 : ℕ) ^ m, x ^ (2 : ℕ) ^ m⁆ = (1 : G) := by
    rw [← commutator_pow_mul hcent y x ((2 : ℕ) ^ m) ((2 : ℕ) ^ m), pow_mul, hcm, one_pow]
  have e1 : (x ^ 2 ^ m) ^ 2 = x ^ 2 ^ (m + 1) := by rw [← pow_mul, ← pow_succ]
  have e2 : (y ^ 2 ^ m) ^ 2 = y ^ 2 ^ (m + 1) := by rw [← pow_mul, ← pow_succ]
  calc (x * y) ^ 2 ^ (m + 1) = ((x * y) ^ 2 ^ m) ^ 2 := by rw [pow_succ, pow_mul]
    _ = (x ^ 2 ^ m * y ^ 2 ^ m) ^ 2 := by rw [ih]
    _ = ⁅y ^ 2 ^ m, x ^ 2 ^ m⁆ * ((x ^ 2 ^ m) ^ 2 * (y ^ 2 ^ m) ^ 2) :=
        sq_mul_sq_eq_of_commutator_central hcent (x ^ 2 ^ m) (y ^ 2 ^ m)
    _ = x ^ 2 ^ (m + 1) * y ^ 2 ^ (m + 1) := by rw [hcom1, one_mul, e1, e2]

end ClassTwo

theorem pow_two_pow_mul {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Work.Higman.omega1 P) {E : ℕ} (hE : 2 ≤ E) (x y : P) :
    (x * y) ^ 2 ^ E = x ^ 2 ^ E * y ^ 2 ^ E := by
  have hcent : ∀ a b : P, ⁅a, b⁆ ∈ Subgroup.center P := fun a b =>
    (hcomm.trans h.omega1_le_center)
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
  have h2c : ∀ a b : P, ⁅a, b⁆ ^ 2 = 1 := fun a b =>
    h.mem_omega1.mp
      (hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)))
  exact pow_two_pow_mul_gen hcent h2c hE x y

end Work.Higman
