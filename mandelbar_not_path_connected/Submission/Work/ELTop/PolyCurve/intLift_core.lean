import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Lifting a cyclic window of angle data to `ℤ`

Given a strictly ordered "window" of `m` angle intervals `(a i, b i)`, `0 ≤ i < m`, which
closes up cyclically (`b (m-1) < a 0 + 1`) and whose landing points `y i` are pairwise
distinct in the window, extend everything `m`-periodically to all of `ℤ`, adding the winding
number `k / m` to the angles.  The result `A, B, Y` is the periodic lift used to parametrize
a ray polygon: `A (k+m) = A k + 1`, `B (k+m) = B k + 1`, `Y (k+m) = Y k`, and the angles
remain strictly interlaced `A k < B k < A (k+1)`.
-/

namespace Work.ELTop.PolyCurve

theorem intLift_core {m : ℕ} (hm : 0 < m) (a b : ℤ → ℝ) (y : ℤ → ℂ)
    (hab : ∀ i : ℤ, 0 ≤ i → i < (m : ℤ) → a i < b i)
    (hba : ∀ i : ℤ, 0 ≤ i → i + 1 < (m : ℤ) → b i < a (i + 1))
    (hlast : b ((m : ℤ) - 1) < a 0 + 1)
    (hinj : ∀ i j : ℤ, 0 ≤ i → i < (m : ℤ) → 0 ≤ j → j < (m : ℤ) → y i = y j → i = j) :
    ∃ A B : ℤ → ℝ, ∃ Y : ℤ → ℂ,
      (∀ k : ℤ, A k = a (k % (m : ℤ)) + ((k / (m : ℤ) : ℤ) : ℝ)) ∧
      (∀ k : ℤ, B k = b (k % (m : ℤ)) + ((k / (m : ℤ) : ℤ) : ℝ)) ∧
      (∀ k : ℤ, Y k = y (k % (m : ℤ))) ∧
      (∀ k : ℤ, A (k + (m : ℤ)) = A k + 1) ∧
      (∀ k : ℤ, B (k + (m : ℤ)) = B k + 1) ∧
      (∀ k : ℤ, Y (k + (m : ℤ)) = Y k) ∧
      (∀ k : ℤ, A k < B k) ∧
      (∀ k : ℤ, B k < A (k + 1)) ∧
      (∀ k k' : ℤ, Y k = Y k' → ∃ q : ℤ, k' = k + (m : ℤ) * q) := by
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmpos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  refine ⟨fun k => a (k % (m : ℤ)) + ((k / (m : ℤ) : ℤ) : ℝ),
          fun k => b (k % (m : ℤ)) + ((k / (m : ℤ) : ℤ) : ℝ),
          fun k => y (k % (m : ℤ)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; rfl
  · intro k; rfl
  · intro k; rfl
  · -- `A (k+m) = A k + 1`
    intro k
    dsimp only
    have hmod : (k + (m : ℤ)) % (m : ℤ) = k % (m : ℤ) := by
      have h := Int.add_mul_emod_self_left k (m : ℤ) 1
      simpa only [mul_one] using h
    have hdiv : (k + (m : ℤ)) / (m : ℤ) = k / (m : ℤ) + 1 := by
      have h := Int.add_mul_ediv_left (b := (m : ℤ)) k 1 hmz
      simpa only [mul_one] using h
    rw [hmod, hdiv]
    push_cast
    ring
  · -- `B (k+m) = B k + 1`
    intro k
    dsimp only
    have hmod : (k + (m : ℤ)) % (m : ℤ) = k % (m : ℤ) := by
      have h := Int.add_mul_emod_self_left k (m : ℤ) 1
      simpa only [mul_one] using h
    have hdiv : (k + (m : ℤ)) / (m : ℤ) = k / (m : ℤ) + 1 := by
      have h := Int.add_mul_ediv_left (b := (m : ℤ)) k 1 hmz
      simpa only [mul_one] using h
    rw [hmod, hdiv]
    push_cast
    ring
  · -- `Y (k+m) = Y k`
    intro k
    dsimp only
    have hmod : (k + (m : ℤ)) % (m : ℤ) = k % (m : ℤ) := by
      have h := Int.add_mul_emod_self_left k (m : ℤ) 1
      simpa only [mul_one] using h
    rw [hmod]
  · -- `A k < B k`
    intro k
    dsimp only
    have hr0 : 0 ≤ k % (m : ℤ) := Int.emod_nonneg k hmz
    have hrm : k % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos k hmpos
    have h := hab (k % (m : ℤ)) hr0 hrm
    linarith
  · -- `B k < A (k+1)`
    intro k
    dsimp only
    have hr0 : 0 ≤ k % (m : ℤ) := Int.emod_nonneg k hmz
    have hrm : k % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos k hmpos
    have hk : k = (m : ℤ) * (k / (m : ℤ)) + k % (m : ℤ) :=
      (Int.mul_ediv_add_emod k (m : ℤ)).symm
    have hk1 : k + 1 = ((k % (m : ℤ)) + 1) + (m : ℤ) * (k / (m : ℤ)) := by linarith
    have hmod1 : (k + 1) % (m : ℤ) = ((k % (m : ℤ)) + 1) % (m : ℤ) := by
      rw [hk1, Int.add_mul_emod_self_left]
    have hdiv1 : (k + 1) / (m : ℤ) = ((k % (m : ℤ)) + 1) / (m : ℤ) + (k / (m : ℤ)) := by
      rw [hk1]
      exact Int.add_mul_ediv_left _ _ hmz
    rw [hmod1, hdiv1]
    have hs_le : (k % (m : ℤ)) + 1 ≤ (m : ℤ) := by linarith
    rcases lt_or_eq_of_le hs_le with hlt | heq
    · -- the next index stays inside the window
      have hs_mod : ((k % (m : ℤ)) + 1) % (m : ℤ) = (k % (m : ℤ)) + 1 :=
        Int.emod_eq_of_lt (by linarith) hlt
      have hs_div : ((k % (m : ℤ)) + 1) / (m : ℤ) = 0 :=
        Int.ediv_eq_zero_of_lt (by linarith) hlt
      rw [hs_mod, hs_div]
      have hb := hba (k % (m : ℤ)) hr0 (by linarith : k % (m : ℤ) + 1 < (m : ℤ))
      push_cast
      linarith
    · -- the window wraps around, use the closing inequality `hlast`
      have hs_mod : ((k % (m : ℤ)) + 1) % (m : ℤ) = 0 := by rw [heq, Int.emod_self]
      have hs_div : ((k % (m : ℤ)) + 1) / (m : ℤ) = 1 := by rw [heq, Int.ediv_self hmz]
      have hrm1 : k % (m : ℤ) = (m : ℤ) - 1 := by linarith
      rw [hs_mod, hs_div, hrm1]
      push_cast
      linarith [hlast]
  · -- the landing points determine the index up to a period
    intro k k' h
    have hr0 : 0 ≤ k % (m : ℤ) := Int.emod_nonneg k hmz
    have hrm : k % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos k hmpos
    have hr0' : 0 ≤ k' % (m : ℤ) := Int.emod_nonneg k' hmz
    have hrm' : k' % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos k' hmpos
    have heq : k % (m : ℤ) = k' % (m : ℤ) :=
      hinj (k % (m : ℤ)) (k' % (m : ℤ)) hr0 hrm hr0' hrm' h
    have hdvd : (m : ℤ) ∣ k - k' := by
      rw [Int.dvd_iff_emod_eq_zero]
      exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp heq
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨-c, ?_⟩
    have : k' = k - (m : ℤ) * c := by linarith
    rw [this]; ring

end Work.ELTop.PolyCurve
