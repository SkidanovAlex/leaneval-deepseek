import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseBoxFock.exists_jointGramLab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.CardKmomLabLt` — the lattice-point count for the box momenta

The mode set of the honest box model is the cube of labels
`Lab N = (ZMod (2N+1))³`, with momentum `kmomLab ℓ N n = ℓ⁻¹ • vec (labVec N n)`,
i.e. the dual-lattice momentum `(2π/ℓ)·(centred integer vector)`.

This file proves the elementary but indispensable counting bound

`# {k : Lab N | ‖kmomLab ℓ N k‖ < κ} ≤ (2ℓκ/π + 1)³`,

which turns the spectral condition `‖kmomLab ℓ N k‖ < κ` into a *finite* cardinality
estimate (`ℋ_b`-type mode counts are fed into Cauchy–Schwarz below; see
`Work.BoseFixR.ModeCountBoundV2` for the quantitative consumer).

The proof is coordinatewise: the Euclidean norm dominates each coordinate, so
`‖kmomLab ℓ N k‖ < κ` forces every component of `labVec N k` to lie in
`(-R, R)` with `R = ℓκ/(2π)`.  Since `labVec N` is injective (the least-absolute
representative `ZMod.valMinAbs` is a section of `ℤ → ZMod (2N+1)`) and an integer
in `(-R, R)` is one of at most `2⌊R⌋ + 1` values, the cardinality is at most
`(2⌊R⌋ + 1)³ ≤ (2R + 1)³`.  The target's constant is the even more generous
`(2·(2R) + 1)³ = (2ℓκ/π + 1)³`, since `R = ℓκ/(2π) > 0` gives `2R + 1 ≤ 4R + 1`.

Both the coordinate estimate (`kmomLab_coord_abs_lt`) and the count
(`CardKmomLabLt`) are stated for reuse.
-/

namespace Work.BoseFixR

/-- **The coordinate estimate of the box momentum.**  If `‖kmomLab ℓ N k‖ < κ` and `ℓ > 0`
then every component of the centred integer label vector `labVec N k` is smaller than
`ℓκ/(2π)` in absolute value.

Indeed `kmomLab ℓ N k = ℓ⁻¹ • (2π · labVec N k)` componentwise, and the Euclidean norm
dominates each coordinate (`PiLp.norm_apply_le`). -/
theorem kmomLab_coord_abs_lt {ℓ κ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    {k : Work.BoseBoxFock.Lab N} (hk : ‖Work.BoseBoxFock.kmomLab ℓ N k‖ < κ) (i : Fin 3) :
    |((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)| < ℓ * κ / (2 * Real.pi) := by
  have h1 : ‖(Work.BoseBoxFock.kmomLab ℓ N k).ofLp i‖ ≤ ‖Work.BoseBoxFock.kmomLab ℓ N k‖ :=
    PiLp.norm_apply_le _ i
  have h2 : (Work.BoseBoxFock.kmomLab ℓ N k).ofLp i
      = ℓ⁻¹ * (2 * Real.pi * ((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)) := by
    simp [Work.BoseBoxFock.kmomLab, Work.BoseB4.vec]
  rw [h2, Real.norm_eq_abs] at h1
  have h3 : |ℓ⁻¹ * (2 * Real.pi * ((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ))|
      = ℓ⁻¹ * (2 * Real.pi) * |((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)| := by
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hℓ),
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    ring
  rw [h3] at h1
  have h4 : ℓ⁻¹ * (2 * Real.pi) * |((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)| < κ :=
    lt_of_le_of_lt h1 hk
  have h5 : (2 * Real.pi) * |((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)| < ℓ * κ := by
    have h6 := mul_lt_mul_of_pos_left h4 hℓ
    have h7 : ℓ * (ℓ⁻¹ * (2 * Real.pi) * |((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)|)
        = (2 * Real.pi) * |((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)| := by
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hℓ), one_mul]
    linarith [h6, h7.symm ▸ h6]
  rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
  linarith [h5]

theorem CardKmomLabLt {ℓ κ : ℝ} (hℓ : 0 < ℓ) (hκ : 0 < κ) (N : ℕ) :
    (((Finset.univ : Finset (Work.BoseBoxFock.Lab N)).filter
        (fun k => ‖Work.BoseBoxFock.kmomLab ℓ N k‖ < κ)).card : ℝ)
      ≤ (2 * ℓ * κ / Real.pi + 1) ^ 3 := by
  classical
  set R : ℝ := ℓ * κ / (2 * Real.pi) with hRdef
  have hR : 0 ≤ R := by rw [hRdef]; positivity
  set K : ℕ := ⌊R⌋₊ with hKdef
  have hKle : (K : ℝ) ≤ R := by rw [hKdef]; exact Nat.floor_le hR
  -- every label of the filtered set has all its centred integer coordinates in `[-K, K]`
  have hcoord : ∀ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).filter
        (fun k => ‖Work.BoseBoxFock.kmomLab ℓ N k‖ < κ),
      ∀ i : Fin 3, Work.BoseBoxFock.labVec N k i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    intro k hk i
    have hk' : ‖Work.BoseBoxFock.kmomLab ℓ N k‖ < κ := (Finset.mem_filter.mp hk).2
    have ha : |((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)| < R := by
      rw [hRdef]
      exact kmomLab_coord_abs_lt hℓ N hk' i
    have hnat : (Work.BoseBoxFock.labVec N k i).natAbs ≤ K := by
      rw [hKdef]
      apply Nat.le_floor
      have hcast : (((Work.BoseBoxFock.labVec N k i).natAbs : ℕ) : ℝ)
          = |((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)| := by simp
      rw [hcast]
      exact le_of_lt ha
    have h2 : ((Work.BoseBoxFock.labVec N k i).natAbs : ℤ) ≤ (K : ℤ) := by exact_mod_cast hnat
    rw [Finset.mem_Icc]
    constructor
    · have h3 : (-(Work.BoseBoxFock.labVec N k i))
          ≤ (((-(Work.BoseBoxFock.labVec N k i)).natAbs : ℤ)) := Int.le_natAbs
      rw [Int.natAbs_neg] at h3
      omega
    · have h3 : Work.BoseBoxFock.labVec N k i
          ≤ (((Work.BoseBoxFock.labVec N k i).natAbs : ℤ)) := Int.le_natAbs
      omega
  -- injectivity of `labVec` turns this into a product bound
  have hcard1 : ((Finset.univ : Finset (Work.BoseBoxFock.Lab N)).filter
        (fun k => ‖Work.BoseBoxFock.kmomLab ℓ N k‖ < κ)).card
      ≤ (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(K : ℤ)) (K : ℤ))).card := by
    rw [← Finset.card_image_of_injective _
      (Work.BoseBoxFock.GramLab.labVec_injective N)]
    apply Finset.card_le_card
    intro f hf
    rw [Finset.mem_image] at hf
    obtain ⟨k, hk, rfl⟩ := hf
    rw [Fintype.mem_piFinset]
    exact hcoord k hk
  have hcard2 : (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(K : ℤ)) (K : ℤ))).card
      = (2 * K + 1) ^ 3 := by
    rw [Fintype.card_piFinset]
    have h1 : ∀ i : Fin 3, (Finset.Icc (-(K : ℤ)) (K : ℤ)).card = 2 * K + 1 := by
      intro i
      rw [Int.card_Icc]
      have h3 : ((K : ℤ) + 1 - (-(K : ℤ))) = ((2 * K + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [h3, Int.toNat_natCast]
    rw [Finset.prod_congr rfl (fun i _ => h1 i)]
    simp [Finset.prod_const]
  have hRcard : (((2 * K + 1 : ℕ)) : ℝ) ≤ 2 * ℓ * κ / Real.pi + 1 := by
    have h1 : (((2 * K + 1 : ℕ)) : ℝ) = 2 * (K : ℝ) + 1 := by push_cast; ring
    rw [h1]
    have h2 : 2 * R = ℓ * κ / Real.pi := by rw [hRdef]; ring_nf
    have h3 : 0 ≤ ℓ * κ / Real.pi := by positivity
    have h5 : 2 * (K : ℝ) ≤ 2 * R := by linarith
    have h6 : 2 * R ≤ 2 * (ℓ * κ / Real.pi) := by linarith
    have h7 : 2 * ℓ * κ / Real.pi = 2 * (ℓ * κ / Real.pi) := by ring
    linarith
  calc (((Finset.univ : Finset (Work.BoseBoxFock.Lab N)).filter
        (fun k => ‖Work.BoseBoxFock.kmomLab ℓ N k‖ < κ)).card : ℝ)
      ≤ ((Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(K : ℤ)) (K : ℤ))).card : ℝ) := by
        exact_mod_cast hcard1
    _ = ((2 * K + 1 : ℕ) : ℝ) ^ 3 := by rw [hcard2]; push_cast; ring
    _ ≤ (2 * ℓ * κ / Real.pi + 1) ^ 3 := pow_le_pow_left₀ (by positivity) hRcard 3

end Work.BoseFixR
