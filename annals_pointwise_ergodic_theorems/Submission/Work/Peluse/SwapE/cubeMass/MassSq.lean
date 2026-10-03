import Submission.Work.Peluse.SwapE.cubeMass.SqToCubeAux

/-!
# `massAvg ⟹ massSq` (Cauchy–Schwarz) and the bridge `SqToCube ⟹ MassToCube`

This module reproduces, inside the `cubeMass` development, the two elementary steps that turn the
`massSq` form of the endgame (`SqToCube`) into the `massAvg` form (`MassToCube`):

* `massBox_card` : `#(massBox d H M) = (massBoxCard H M)^d`;
* `massAvg_sq_le` : `(massAvg d H M N f)² ≤ massSq d H M N f` — Cauchy–Schwarz for the uniform
  average over the slot box;
* `massToCube_of_sq'` : `SqToCube → MassToCube`, with exponent `2e` in place of `e`.

It is a self-contained copy of the corresponding facts of `SwapE/Reduce.lean`, so that
`Work.Peluse.SwapE.massToCube` rests only on this directory.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.SwapE

noncomputable section

open Work.Peluse

/-- `#(massBox d H M) = (massBoxCard H M)^d`: the slot box has the cardinality its normalising
constant announces. -/
theorem massBox_card (d H M : ℕ) : (massBox d H M).card = (massBoxCard H M) ^ d := by
  have hfac : (Finset.Icc (-(massHalf H M)) (massHalf H M)).card = massBoxCard H M := by
    rw [Int.card_Icc]
    unfold massHalf massBoxCard
    have h : 2 * ((H * M : ℕ) : ℤ) + 1 - -(2 * ((H * M : ℕ) : ℤ))
        = ((4 * H * M + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [h, Int.toNat_natCast]
  unfold massBox
  rw [Fintype.card_piFinset]
  simp only [hfac]
  simp

/-- Cauchy–Schwarz for a finite average: the square of the mean is at most the mean of the
squares. -/
private lemma finset_mean_sq_le {ι : Type} (s : Finset ι) (g : ι → ℝ)
    (hc : (s.card : ℝ) ≠ 0) :
    ((∑ i ∈ s, g i) / (s.card : ℝ)) ^ 2 ≤ (∑ i ∈ s, g i ^ 2) / (s.card : ℝ) := by
  have hpos : (0 : ℝ) < (s.card : ℝ) := lt_of_le_of_ne (by positivity) (Ne.symm hc)
  have hCS := sq_sum_le_card_mul_sum_sq (s := s) (f := g)
  rw [div_pow]
  have hT : (∑ i ∈ s, g i ^ 2) / (s.card : ℝ)
      = (∑ i ∈ s, g i ^ 2) * (s.card : ℝ) / (s.card : ℝ) ^ 2 := by
    field_simp
  rw [hT, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < (s.card : ℝ) ^ 2)]
  linarith [hCS]

/-- The Cauchy–Schwarz step of the endgame: the square of the average of the cube mass is at most
the average of its square. -/
theorem massAvg_sq_le (d H M N : ℕ) (f : ℤ → ℂ) :
    (massAvg d H M N f) ^ 2 ≤ massSq d H M N f := by
  have hcard : (((massBox d H M).card : ℕ) : ℝ) = ((massBoxCard H M : ℝ)) ^ d := by
    rw [massBox_card]
    push_cast
    ring
  have hc : (((massBox d H M).card : ℕ) : ℝ) ≠ 0 := by
    have h1 : (0 : ℝ) < ((massBox d H M).card : ℝ) := by
      rw [hcard]
      have hbase : (0 : ℝ) < (massBoxCard H M : ℝ) := by unfold massBoxCard; positivity
      exact pow_pos hbase d
    exact h1.ne'
  rw [massAvg, massSq, ← hcard]
  exact finset_mean_sq_le (massBox d H M) (fun n => ‖boxMass d (symIcc N) f n‖) hc

/-- **`SqToCube` implies `MassToCube`**: the passage from the average of the cube mass to its mean
square is Cauchy–Schwarz (`massAvg_sq_le`). -/
theorem massToCube_of_sq' (h : SqToCube) : MassToCube := by
  intro d hd
  obtain ⟨e, he, s', hs', C, hC, hb⟩ := h d hd
  refine ⟨2 * e, by omega, s', hs', C, hC, ?_⟩
  intro H M N θ f hH hM hf hf1 hθ hθ1 hmass
  have hsq : θ ^ 2 ≤ massSq d H M N f :=
    le_trans (pow_le_pow_left₀ hθ.le hmass 2) (massAvg_sq_le d H M N f)
  have h2 := hb H M N (θ ^ 2) f hH hM hf hf1 (by positivity) hsq
  simpa [pow_mul] using h2

end

end Work.Peluse.SwapE
