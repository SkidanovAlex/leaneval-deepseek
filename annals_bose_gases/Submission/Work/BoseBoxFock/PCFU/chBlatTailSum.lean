import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseBoxFock.PCFU.chBslotAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chBlatTailSum`

The far lattice tail sum of the `(B)`-channel: for every finite set `u` of lattice vectors, the
`-5`-tail of the distance function

    d ↦ (‖latVec d‖ - 3/2)^{-5}   (over `d ∉ smLab = {-3,…,3}³`)

is bounded by the universal constant `4^5 · 227`.

## Why the constant is `4^5 · 227`

Off `smLab` the Euclidean norm `‖latVec d‖` is at least `4` (this is
`Work.BoseBoxFock.PCFU.norm_latVec_ge_of_notMem_smLab`).  Hence, with `K = ‖latVec d‖ ≥ 4`,

* `K - 3/2 ≥ K/4` (since `K ≥ 2`), so `(K - 3/2)^{-5} ≤ (K/4)^{-5} = 4^5 K^{-5}`;
* `K^{-5} ≤ K^{-4}` (since `K ≥ 1`).

So each term of the target is at most `4^5 · ‖latVec d‖^{-4}`, and the lattice sum
`∑_{d ∈ u} ‖latVec d‖^{-4} ≤ 227` is exactly the proved companion
`Work.BoseBoxFock.sum_inv_norm_latVec_le`.  This is the same mechanism (and the same constant) as
the `(B)`-tail estimate `Work.BoseBoxFock.PCFU.chBimg_far_tail`, which consumes the statement
below as its hypothesis `hlat`.
-/

namespace Work.BoseBoxFock.PCFU

/-- The pointwise reduction of the tail: off the small lattice, `(K - 3/2)^{-5} ≤ 4^5 K^{-4}`
for `K = ‖latVec d‖ ≥ 4`. -/
lemma zpow_neg_five_sub_le {K : ℝ} (hK : 4 ≤ K) :
    (K - 3 / 2) ^ (-(5 : ℤ)) ≤ 4 ^ 5 * (K ^ 4)⁻¹ := by
  have hKpos : 0 < K := by linarith
  have hDpos : 0 < K - 3 / 2 := by linarith
  have hDge : K / 4 ≤ K - 3 / 2 := by linarith
  have h1 : ((K - 3 / 2) ^ 5)⁻¹ ≤ 4 ^ 5 * (K ^ 5)⁻¹ := by
    have hp : (K / 4) ^ 5 ≤ (K - 3 / 2) ^ 5 := pow_le_pow_left₀ (by positivity) hDge 5
    have hq : ((K - 3 / 2) ^ 5)⁻¹ ≤ ((K / 4) ^ 5)⁻¹ :=
      (inv_le_inv₀ (pow_pos hDpos 5) (pow_pos (by positivity) 5)).mpr hp
    have heq : ((K / 4) ^ 5)⁻¹ = 4 ^ 5 * (K ^ 5)⁻¹ := by
      rw [div_pow, inv_div, div_eq_mul_inv]
    rwa [heq] at hq
  have h2 : 4 ^ 5 * (K ^ 5)⁻¹ ≤ 4 ^ 5 * (K ^ 4)⁻¹ := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact (inv_le_inv₀ (pow_pos hKpos 5) (pow_pos hKpos 4)).mpr
      (pow_le_pow_right₀ (by linarith) (by norm_num))
  rw [show (-(5 : ℤ)) = -(↑(5 : ℕ) : ℤ) from by norm_num, zpow_neg, zpow_natCast]
  exact le_trans h1 h2

/-- **The far lattice tail sum.**  For every finite set `u` of lattice vectors, the `-5`-tail of
`‖latVec d‖ - 3/2` over `d ∉ smLab` is at most `4^5 · 227`. -/
theorem chBlatTailSum (u : Finset (Fin 3 → ℤ)) :
    (∑ d ∈ u, if d ∈ Work.BoseBoxFock.PCFU.smLab then 0
      else (‖Work.BoseBoxFock.latVec d‖ - 3 / 2) ^ (-(5 : ℤ))) ≤ 4 ^ 5 * 227 := by
  have hpt : ∀ d : Fin 3 → ℤ,
      (if d ∈ smLab then 0 else (‖latVec d‖ - 3 / 2) ^ (-(5 : ℤ)))
        ≤ 4 ^ 5 * ((‖latVec d‖ ^ 4)⁻¹) := by
    intro d
    by_cases hd : d ∈ smLab
    · rw [if_pos hd]
      positivity
    · rw [if_neg hd]
      exact zpow_neg_five_sub_le (norm_latVec_ge_of_notMem_smLab hd)
  calc (∑ d ∈ u, if d ∈ smLab then 0 else (‖latVec d‖ - 3 / 2) ^ (-(5 : ℤ)))
      ≤ ∑ d ∈ u, 4 ^ 5 * ((‖latVec d‖ ^ 4)⁻¹) := Finset.sum_le_sum (fun d _ => hpt d)
    _ = 4 ^ 5 * ∑ d ∈ u, ((‖latVec d‖ ^ 4)⁻¹) := by rw [Finset.mul_sum]
    _ ≤ 4 ^ 5 * 227 :=
        mul_le_mul_of_nonneg_left (Work.BoseBoxFock.sum_inv_norm_latVec_le u) (by norm_num)

end Work.BoseBoxFock.PCFU
