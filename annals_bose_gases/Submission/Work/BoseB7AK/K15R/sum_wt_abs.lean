import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB7AK.K15R.inv2_low
import Submission.Work.BoseB7AK.K15R.inv4_high
import Submission.Work.BoseB7AK.K15R.lattice_wt_high
import Submission.Work.BoseB7AK.K15R.lattice_wt_low
import Submission.Work.BoseB7AK.K15R.sum_sem_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.K15R.sum_wt_abs` — the `‖q‖^{-2}`-weighted scaled momentum sum

This module supplies `K15Input.Cwt`: the constant of the *scaled weighted lattice
sum* `K15Input.sum_wt`.  For a box of side `ℓ ≥ 1` whose modes carry dual-lattice
momenta (`OnDualLattice ℓ kmom`, `Work.BoseB4.vec n = 2πn`) and for FS's parameters
`K_H ≥ 1`, `a > 0`,

    `ℓ⁻³ Σ_{q ∈ P_H^q, excited} (1+‖q‖)^{-4} ‖q‖^{-2} ≤ 1001`,

with an **absolute** constant.  Note that the statement's region
`1/(4K_Ha) ≤ ‖q‖` is *weaker* than FS's `P_H^q = {1/(2K_Ha) ≤ ‖q‖, ‖q‖ ≤ 2K_Ha}`:
the proof does not use the momentum cutoff at all, so the estimate holds for the
sum over *all* excited modes (each summand is nonnegative, so restricting to a
filtered subset can only decrease the sum).  The only role of `K_H ≥ 1` and `a > 0`
is to make `1/(4K_Ha) > 0`, which shows that the zero-momentum mode (whose lattice
index would be `0`) is *not* in the filtered set.

## The proof

Two steps.

* **The mode/lattice transfer.**  `OnDualLattice ℓ kmom` makes the labels distinct
  dual-lattice points `kmom q = ℓ⁻¹ • vec (hlat.lift q)` (`hlat.lift` is injective),
  so with `‖kmom q‖ = ‖vec (hlat.lift q)‖/ℓ` the mode sum equals the lattice sum
  over `T = (filtered).image hlat.lift` of the *scaled* summand
  `(1+‖vec n‖/ℓ)^{-4}(‖vec n‖/ℓ)^{-2}`.
* **The lattice sum.**  `T` consists of nonzero lattice indices, and we split it at
  the radius `ℓ`:
  - *low part* (`‖vec n‖ < ℓ`): `lattice_wt_low` gives `≤ ℓ³` — the `ℓ²` from
    scaling `(‖vec n‖/ℓ)^{-2} = ℓ²‖vec n‖^{-2}` combined with the linear growth
    `Σ ‖vec n‖^{-2} ≲ ℓ` of the lattice sum (`inv2_low`);
  - *high part* (`ℓ ≤ ‖vec n‖`): `(1+‖vec n‖/ℓ)^{-4} ≤ (‖vec n‖/ℓ)^{-4}` and
    `(‖vec n‖/ℓ)^{-2} ≤ 1`, so the sum is at most `ℓ⁴ Σ ‖vec n‖^{-4} ≲ ℓ³`
    (`inv4_high`).

  `ℓ³ + 1000ℓ³ = 1001ℓ³`, and multiplying by `ℓ^{-3}` gives the absolute bound
  `1001`.

The constant is deliberately crude: only existence is consumed downstream
(`Work.BoseB7AK.K15R.exists_constants`, and thence the domination field
`K15Input.K₀_wt`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7AK.K15R

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The mode/lattice transfer -/

/-- **A mode label's norm, read off its lattice index**: `kmom q = ℓ⁻¹ • vec n_q`
with `n_q = hlat.lift q`, so `‖kmom q‖ = ‖vec n_q‖/ℓ` for `ℓ > 0`. -/
private lemma norm_lift_of_dualLattice {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {ℓ : ℝ} {kmom : Mode → ℝ³} (h : OnDualLattice ℓ kmom)
    (hℓpos : 0 < ℓ) (q : Mode) :
    ‖kmom q‖ = ‖Work.BoseB4.vec (h.lift q)‖ / ℓ := by
  rw [h.lift_spec q, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓpos)]
  ring

/-- `vec 0 = 0` (`vec n = 2πn`). -/
private lemma vec_zero : Work.BoseB4.vec (0 : Fin 3 → ℤ) = 0 := by
  ext i
  simp [Work.BoseB4.vec]

/-! ## 2. The weighted scaled momentum sum -/

theorem sum_wt_abs :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (ℓ : ℝ) (hℓ : 1 ≤ ℓ) (kmom : Mode → EuclideanSpace ℝ (Fin 3))
      (hlat : Work.BoseB7AK.K15R.OnDualLattice ℓ kmom) (KH a : ℝ) (hKH : 1 ≤ KH) (ha : 0 < a),
      ℓ ^ (-(3 : ℝ)) *
        ∑ q ∈ (Work.BoseB7.excited Mode).filter (fun q => 1 / (4 * KH * a) ≤ ‖kmom q‖),
          (1 + ‖kmom q‖) ^ (-(4 : ℝ)) * ‖kmom q‖ ^ (-(2 : ℝ)) ≤ C := by
  refine ⟨1001, by norm_num, ?_⟩
  intro Mode _ _ _ ℓ hℓ kmom hlat KH a hKH ha
  have hℓpos : 0 < ℓ := lt_of_lt_of_le one_pos hℓ
  have hKpos : 0 < KH := lt_of_lt_of_le one_pos hKH
  have hpos : 0 < 1 / (4 * KH * a) :=
    one_div_pos.mpr (by positivity)
  -- the lattice indices of the filtered modes
  set T : Finset (Fin 3 → ℤ) := ((Work.BoseB7.excited Mode).filter
      (fun q => 1 / (4 * KH * a) ≤ ‖kmom q‖)).image hlat.lift with hT
  -- the transfer: the mode sum is the lattice sum over `T`, scaled
  have htrans : (∑ q ∈ (Work.BoseB7.excited Mode).filter
        (fun q => 1 / (4 * KH * a) ≤ ‖kmom q‖),
        (1 + ‖kmom q‖) ^ (-(4 : ℝ)) * ‖kmom q‖ ^ (-(2 : ℝ)))
      = ∑ n ∈ T, (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)) *
          (‖Work.BoseB4.vec n‖ / ℓ) ^ (-(2 : ℝ)) := by
    rw [hT, Finset.sum_image (fun x _ y _ hxy => hlat.lift_injective hxy)]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [norm_lift_of_dualLattice hlat hℓpos q]
  -- no lattice index of `T` is zero (the zero momentum is filtered out)
  have hne : ∀ n ∈ T, n ≠ 0 := by
    intro n hn hn0
    rw [hT] at hn
    obtain ⟨q, hq, hq2⟩ := Finset.mem_image.mp hn
    have hle : 1 / (4 * KH * a) ≤ ‖kmom q‖ := (Finset.mem_filter.mp hq).2
    have hlift0 : hlat.lift q = 0 := by rw [hq2, hn0]
    have hkm0 : kmom q = 0 := by rw [hlat.lift_spec q, hlift0, vec_zero, smul_zero]
    rw [hkm0, norm_zero] at hle
    linarith
  -- the lattice bound: split at the radius `ℓ`
  have hbound : (∑ n ∈ T, (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)) *
      (‖Work.BoseB4.vec n‖ / ℓ) ^ (-(2 : ℝ))) ≤ 1001 * ℓ ^ 3 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not T (fun n => ‖Work.BoseB4.vec n‖ < ℓ)
      (fun n => (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)) *
        (‖Work.BoseB4.vec n‖ / ℓ) ^ (-(2 : ℝ)))
    have hlow := lattice_wt_low ℓ hℓ (T.filter (fun n => ‖Work.BoseB4.vec n‖ < ℓ))
      (fun n hn => hne n (Finset.mem_filter.mp hn).1)
      (fun n hn => (Finset.mem_filter.mp hn).2)
    have hhigh := lattice_wt_high ℓ hℓ (T.filter (fun n => ¬ (‖Work.BoseB4.vec n‖ < ℓ)))
      (fun n hn => not_lt.mp (Finset.mem_filter.mp hn).2)
    linarith [hsplit, hlow, hhigh]
  rw [htrans]
  -- multiply by `ℓ^{-3}`
  have hpow : ℓ ^ (-(3 : ℝ)) * ℓ ^ (3 : ℕ) = 1 := by
    have h3 : ℓ ^ (3 : ℕ) = ℓ ^ (3 : ℝ) := (Real.rpow_natCast ℓ 3).symm
    rw [h3, ← Real.rpow_add hℓpos, show (-(3 : ℝ)) + 3 = 0 by norm_num, Real.rpow_zero]
  calc ℓ ^ (-(3 : ℝ)) * (∑ n ∈ T, (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)) *
        (‖Work.BoseB4.vec n‖ / ℓ) ^ (-(2 : ℝ)))
      ≤ ℓ ^ (-(3 : ℝ)) * (1001 * ℓ ^ 3) :=
        mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hℓpos.le _)
    _ = 1001 * (ℓ ^ (-(3 : ℝ)) * ℓ ^ (3 : ℕ)) := by ring
    _ = 1001 := by rw [hpow, mul_one]

end Work.BoseB7AK.K15R
