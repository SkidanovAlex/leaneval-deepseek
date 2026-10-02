import Mathlib
import Submission.Work.Landing.Angles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The forward orbit of the first dynamic root angle

The first dynamic root angle `rootAngle1 = 371/1023` of the non-real period-`5` component is
periodic of (exact) period `10` under angle doubling `angDouble θ = Int.fract (-2θ)`.  We prove
that its forward orbit is exactly the cyclic set of its ten distinct iterates

`371/1023 → 281/1023 → 461/1023 → 101/1023 → 821/1023 → 404/1023 → 215/1023 → 593/1023
 → 860/1023 → 326/1023 → 371/1023`.

The only general input is that the orbit of a point of period `k` is the set of its first `k`
iterates; the remaining statements are finite computations with `Int.fract` on rationals.
-/

noncomputable section

namespace Work.Landing.Angle

open Work.Landing Function

/-- The forward orbit of a point of period `k` (with `k > 0`) under a self-map `f` is the set of
its first `k` iterates. -/
theorem angleOrbit_eq_of_period {θ : ℝ} {k : ℕ} (hk : 0 < k) (h : angDouble^[k] θ = θ) :
    angleOrbit θ = {θ' : ℝ | ∃ m : ℕ, m < k ∧ angDouble^[m] θ = θ'} := by
  ext θ'
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n % k, Nat.mod_lt _ hk, ?_⟩
    have hq : (angDouble^[k])^[n / k] θ = θ := by
      induction n / k with
      | zero => simp
      | succ j ih => rw [Function.iterate_succ_apply', ih, h]
    have hkq : angDouble^[k * (n / k)] θ = θ := by
      rw [Function.iterate_mul]; exact hq
    have hn : n = (n % k) + k * (n / k) := by
      have h2 := Nat.div_add_mod n k; omega
    have hmain : angDouble^[n] θ = angDouble^[n % k] θ := by
      conv_lhs => rw [hn]
      rw [Function.iterate_add_apply, hkq]
    exact hmain.symm
  · rintro ⟨m, _hm, hmθ⟩
    exact ⟨m, hmθ⟩

theorem angleOrbit_rootAngle :
    Work.Landing.angleOrbit Work.Landing.rootAngle1 =
      {371/1023, 281/1023, 461/1023, 101/1023, 821/1023, 404/1023, 215/1023, 593/1023,
        860/1023, 326/1023} := by
  have hperiod : angDouble^[10] rootAngle1 = rootAngle1 := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, angDouble_def,
      rootAngle1_def]
    norm_num [Int.fract]
  rw [angleOrbit_eq_of_period (k := 10) (by norm_num) hperiod]
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    interval_cases m <;>
      · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, angDouble_def,
          rootAngle1_def, Set.mem_insert_iff, Set.mem_singleton_iff]
        norm_num [Int.fract]
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, by norm_num, by rw [h]; simp only [Function.iterate_zero_apply, rootAngle1_def]⟩
    · exact ⟨1, by norm_num, by rw [h]; simp only [Function.iterate_succ_apply',
        Function.iterate_zero_apply, angDouble_def, rootAngle1_def]; norm_num [Int.fract]⟩
    · exact ⟨2, by norm_num, by rw [h]; simp only [Function.iterate_succ_apply',
        Function.iterate_zero_apply, angDouble_def, rootAngle1_def]; norm_num [Int.fract]⟩
    · exact ⟨3, by norm_num, by rw [h]; simp only [Function.iterate_succ_apply',
        Function.iterate_zero_apply, angDouble_def, rootAngle1_def]; norm_num [Int.fract]⟩
    · exact ⟨4, by norm_num, by rw [h]; simp only [Function.iterate_succ_apply',
        Function.iterate_zero_apply, angDouble_def, rootAngle1_def]; norm_num [Int.fract]⟩
    · exact ⟨5, by norm_num, by rw [h]; simp only [Function.iterate_succ_apply',
        Function.iterate_zero_apply, angDouble_def, rootAngle1_def]; norm_num [Int.fract]⟩
    · exact ⟨6, by norm_num, by rw [h]; simp only [Function.iterate_succ_apply',
        Function.iterate_zero_apply, angDouble_def, rootAngle1_def]; norm_num [Int.fract]⟩
    · exact ⟨7, by norm_num, by rw [h]; simp only [Function.iterate_succ_apply',
        Function.iterate_zero_apply, angDouble_def, rootAngle1_def]; norm_num [Int.fract]⟩
    · exact ⟨8, by norm_num, by rw [h]; simp only [Function.iterate_succ_apply',
        Function.iterate_zero_apply, angDouble_def, rootAngle1_def]; norm_num [Int.fract]⟩
    · exact ⟨9, by norm_num, by rw [h]; simp only [Function.iterate_succ_apply',
        Function.iterate_zero_apply, angDouble_def, rootAngle1_def]; norm_num [Int.fract]⟩

end Work.Landing.Angle
