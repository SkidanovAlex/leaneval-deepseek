import Mathlib
import Submission.Work.OROneRel.rightPowDefs
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.FreiheitssatzDefs
import Submission.Work.OROneRel.sigma_mk

namespace Work.OROneRel

universe u

/-! ### The exponent sum `eps` is the additive shadow of the homomorphism `sigma`

`eps t r` is the exponent sum of the generator `t` in the word `r`, while `sigma t r` is the
honest homomorphism `F(α) →* Multiplicative ℤ` with the same value.  The first two lemmas record
that `eps t r` is `(sigma t r).toAdd`; together with the multiplicativity of `sigma` this makes
`eps` additive, which is what the main induction below needs. -/

/-- `wordEps` (the vocabulary of `MagnusRewrite`) and `sigmaList` (the vocabulary of
`FreiheitssatzDefs`) are the same exponent sum. -/
lemma epsc_wordEps_eq_sigmaList {α : Type u} (t : α) (L : List (α × Bool)) :
    wordEps t L = sigmaList t L := by
  classical
  induction L with
  | nil => simp [sigmaList, wordEps]
  | cons p L ih =>
    simp only [sigmaList, wordEps, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, letterSign]

/-- The exponent sum `eps` is the additive version of the exponent-sum homomorphism `sigma`. -/
lemma epsc_eq_toAdd_sigma {α : Type u} (t : α) (r : FreeGroup α) :
    eps t r = (sigma t r).toAdd := by
  classical
  have h2 : sigma t r = Multiplicative.ofAdd (sigmaList t r.toWord) := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := r)]
    exact sigma_mk t r.toWord
  rw [eps, h2, toAdd_ofAdd, epsc_wordEps_eq_sigmaList]

/-- The exponent sum of the identity is zero. -/
lemma epsc_one {α : Type u} (t : α) : eps t (1 : FreeGroup α) = 0 := by
  simp only [epsc_eq_toAdd_sigma, map_one, toAdd_one]

/-- The exponent sum is additive. -/
lemma epsc_mul {α : Type u} (t : α) (a b : FreeGroup α) :
    eps t (a * b) = eps t a + eps t b := by
  simp only [epsc_eq_toAdd_sigma, map_mul, toAdd_mul]

/-- The exponent sum of an inverse is the negative of the exponent sum. -/
lemma epsc_inv {α : Type u} (t : α) (a : FreeGroup α) : eps t a⁻¹ = - eps t a := by
  simp only [epsc_eq_toAdd_sigma, map_inv, toAdd_inv]

/-- The exponent sum of an integral power is the multiple of the exponent sum. -/
lemma epsc_zpow {α : Type u} (t : α) (a : FreeGroup α) (n : ℤ) :
    eps t (a ^ n) = n * eps t a := by
  simp only [epsc_eq_toAdd_sigma, map_zpow, toAdd_zpow, smul_eq_mul]

/-- The exponent sum of a generator in itself is `1`. -/
lemma epsc_of_eq {α : Type u} (y : α) : eps y (FreeGroup.of y) = 1 := by
  classical
  rw [eps, FreeGroup.toWord_of]
  simp [wordEps]

/-- The exponent sum of a generator in a different generator is `0`. -/
lemma epsc_of_ne {α : Type u} {z y : α} (h : z ≠ y) : eps z (FreeGroup.of y) = 0 := by
  classical
  rw [eps, FreeGroup.toWord_of]
  simp [wordEps, Ne.symm h]

/-- `∑ z ∈ s, q z * eps z (of y) = q y`: the decoration `eps z (of y)` is a Kronecker delta, and
`hs` kills the case `y ∉ s`. -/
lemma epsc_sum_q_eps_of {α : Type u} (q : α → ℤ) (s : Finset α)
    (hs : ∀ z : α, z ∉ s → q z = 0) (y : α) :
    ∑ z ∈ s, q z * eps z (FreeGroup.of y) = q y := by
  classical
  have h : ∀ z, q z * eps z (FreeGroup.of y) = if y = z then q z else 0 := by
    intro z
    by_cases hyz : y = z
    · rw [if_pos hyz, ← hyz, epsc_of_eq, mul_one]
    · rw [if_neg hyz, epsc_of_ne (fun h' : z = y => hyz h'.symm), mul_zero]
  rw [Finset.sum_congr rfl (fun z _ => h z), Finset.sum_ite_eq]
  by_cases hy : y ∈ s
  · rw [if_pos hy]
  · rw [if_neg hy, hs y hy]

/-! ### The main identity

`rightPow t q` is the substitution `y ↦ y * t ^ (-(q y))`.  Both sides of the identity

`eps t (rightPow t q u) = eps t u - ∑ z ∈ s, q z * eps z u`

are additive in `u` (the left because `rightPow t q` is multiplicative and `eps` is additive, the
right because every `eps z` is additive), so it suffices to check the identity on the generators
`of y` and their inverses; this is exactly what `FreeGroup.induction_on` does. -/
theorem eps_rightPow {α : Type u} (t : α) (q : α → ℤ) (s : Finset α)
    (hs : ∀ z : α, z ∉ s → q z = 0) (u : FreeGroup α) :
    Work.OROneRel.eps t (Work.OROneRel.rightPow t q u) =
      Work.OROneRel.eps t u - ∑ z ∈ s, q z * Work.OROneRel.eps z u := by
  classical
  refine FreeGroup.induction_on u ?h1 ?h2 ?h3 ?h4
  · -- the identity
    simp [epsc_one]
  · -- a generator `of y`
    intro y
    rw [rightPow_of, epsc_mul, epsc_zpow, epsc_of_eq, epsc_sum_q_eps_of q s hs y]
    ring
  · -- the inverse of a generator
    intro y ih
    have h1 : eps t (rightPow t q ((FreeGroup.of y)⁻¹))
        = - eps t (rightPow t q (FreeGroup.of y)) := by
      rw [map_inv, epsc_inv]
    have hsum : ∑ z ∈ s, q z * eps z ((FreeGroup.of y)⁻¹)
        = - ∑ z ∈ s, q z * eps z (FreeGroup.of y) := by
      have hcongr : (∑ z ∈ s, q z * eps z ((FreeGroup.of y)⁻¹))
          = ∑ z ∈ s, -(q z * eps z (FreeGroup.of y)) :=
        Finset.sum_congr rfl (fun z _ => by rw [epsc_inv, mul_neg])
      rw [hcongr, Finset.sum_neg_distrib]
    rw [h1, ih, hsum, epsc_inv]
    ring
  · -- a product
    intro a b iha ihb
    have hL : eps t (rightPow t q (a * b))
        = (eps t a - ∑ z ∈ s, q z * eps z a) + (eps t b - ∑ z ∈ s, q z * eps z b) := by
      rw [map_mul, epsc_mul, iha, ihb]
    have hsum : ∑ z ∈ s, q z * eps z (a * b)
        = (∑ z ∈ s, q z * eps z a) + (∑ z ∈ s, q z * eps z b) := by
      have hcongr : (∑ z ∈ s, q z * eps z (a * b))
          = ∑ z ∈ s, (q z * eps z a + q z * eps z b) :=
        Finset.sum_congr rfl (fun z _ => by rw [epsc_mul, mul_add])
      rw [hcongr, Finset.sum_add_distrib]
    rw [hL, hsum, epsc_mul]
    ring

end Work.OROneRel
