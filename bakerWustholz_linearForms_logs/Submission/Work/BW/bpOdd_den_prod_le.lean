import Mathlib
import Submission.Work.BW.bpOddDefs
import Submission.Work.BW.DefsAC
import Submission.Work.BW.oddIdx_prod_eq_prod_range
import Submission.Work.BW.prod_one_add_le_inv_one_sub_sum
import Submission.Work.BW.bpD_pair_mul_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `∑_{i<m} (2i+1) = m²`. -/
lemma bp_sum_range_odd (m : ℕ) : ∑ i ∈ Finset.range m, (2*(i:ℝ) + 1) = (m:ℝ)^2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Denominator product bound, BW (25) step (i): for `0 < η < 1/2`, `X ≥ 2` even, `X + η ≤ R` and odd
`l` with `|l| ≤ X`: `∏_{k ∈ oddIdx X} (|R² − k·l| + |k|·η) ≤ R^{2X}/(1 − η/2)`.
Route: pair `k` with `−k` (using `R² ≥ X² ≥ |k·l|`, so `|R² − k·l| = R² − |k|·|l|`), the pair product
equals `(R²+kη)² − k²l² ≤ R⁴(1 + 2kη/R²)` (as `|l| ≥ 1 > η`), there are `X/2 = m` pairs, and
`∏(1+a_j) ≤ 1/(1−Σa_j)` with `Σa_j = 2η·Σ_{i<m}(2i+1)/R² = ηX²/(2R²) ≤ η/2` since `X ≤ R`. -/
theorem bpOdd_den_prod_le {R η : ℝ} (hη : 0 < η) (hη' : η < 1/2) {X : ℕ} (hX : 2 ≤ X)
    (hXe : Even X) (hXR : (X:ℝ) + η ≤ R) {l : ℤ} (hlo : Odd l) (hl : |l| ≤ (X:ℤ)) :
    ∏ k ∈ oddIdx X, bpD R η l k ≤ R^(2*X) / (1 - η/2) := by
  have hXeven : Even X := hXe
  obtain ⟨m, hm⟩ := hXe
  have hXm : X = 2*m := by omega
  have hm2 : X / 2 = m := by omega
  have hexp : 4*m = 2*X := by omega
  have hRpos : 0 < R := by
    have : (0:ℝ) < (X:ℝ) := by
      have : 0 < X := by omega
      exact_mod_cast this
    linarith
  have hR2pos : (0:ℝ) < R^2 := by positivity
  have hXnonneg : (0:ℝ) ≤ (X:ℝ) := by positivity
  have hXleR : (X:ℝ) ≤ R := by linarith
  have hX2R : (X:ℝ)^2 ≤ R^2 := sq_le_sq' (by linarith) hXleR
  have hlne : l ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := hlo
    omega
  have hl1 : (1:ℝ) ≤ |(l:ℝ)| := by
    have hpos : (0:ℤ) < |l| := abs_pos.mpr hlne
    have h1 : (1:ℤ) ≤ |l| := by omega
    exact_mod_cast h1
  have hlη : η ≤ |(l:ℝ)| := by linarith
  have hlX : |(l:ℝ)| ≤ (X:ℝ) := by exact_mod_cast hl
  have key : ∏ i ∈ Finset.range m,
        (bpD R η l (2*(i:ℤ)+1) * bpD R η l (-(2*(i:ℤ)+1))) ≤ R^(2*X)/(1-η/2) := by
    -- (a) every pair product is nonnegative
    have hA0 : ∀ i ∈ Finset.range m,
        0 ≤ bpD R η l (2*(i:ℤ)+1) * bpD R η l (-(2*(i:ℤ)+1)) := by
      intro i _
      exact mul_nonneg (by unfold bpD; positivity) (by unfold bpD; positivity)
    -- (b) pair bound `(R²+kη)² − k²l² ≤ R⁴ + 2R²|k|η`
    have hA1 : ∀ i ∈ Finset.range m,
        bpD R η l (2*(i:ℤ)+1) * bpD R η l (-(2*(i:ℤ)+1))
          ≤ R^4 + 2*R^2*(((2*(i:ℤ)+1 : ℤ)):ℝ)*η := by
      intro i hi
      have hi' : i < m := Finset.mem_range.mp hi
      have hki : (((2*(i:ℤ)+1 : ℤ)):ℝ) = 2*(i:ℝ) + 1 := by push_cast; ring
      have hkabs : |(((2*(i:ℤ)+1 : ℤ)):ℝ)| = (((2*(i:ℤ)+1 : ℤ)):ℝ) :=
        abs_of_nonneg (by rw [hki]; positivity)
      have hkX : (((2*(i:ℤ)+1 : ℤ)):ℝ) ≤ (X:ℝ) := by
        have h1 : (2*(i:ℤ)+1) ≤ (X:ℤ) := by omega
        exact_mod_cast h1
      have hkl : |(((2*(i:ℤ)+1 : ℤ)):ℝ)| * |(l:ℝ)| ≤ R^2 := by
        rw [hkabs]
        have hmul := mul_le_mul hkX hlX (abs_nonneg _) hXnonneg
        nlinarith [hmul, hX2R]
      have hp := bpD_pair_mul_le (R := R) (η := η) (l := l) (k := (2*(i:ℤ)+1 : ℤ))
          (le_of_lt hη) hRpos hkl hlη
      rw [hkabs] at hp
      exact hp
    have hA := Finset.prod_le_prod₀ hA0 hA1
    -- (c) factor out `R⁴` from every term
    have hB : ∏ i ∈ Finset.range m, (R^4 + 2*R^2*(((2*(i:ℤ)+1 : ℤ)):ℝ)*η)
        = R^(4*m) * ∏ i ∈ Finset.range m, (1 + 2*(((2*(i:ℤ)+1 : ℤ)):ℝ)*η/R^2) := by
      have hR2 : R^2 ≠ 0 := ne_of_gt hR2pos
      have hfac : ∀ i ∈ Finset.range m,
          R^4 + 2*R^2*(((2*(i:ℤ)+1 : ℤ)):ℝ)*η
            = R^4 * (1 + 2*(((2*(i:ℤ)+1 : ℤ)):ℝ)*η/R^2) := by
        intro i _
        field_simp
      rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib]
      rw [Finset.prod_const, Finset.card_range, ← pow_mul]
    -- (d) `∏(1+a_i) ≤ 1/(1-Σa_i) ≤ 1/(1-η/2)`
    have hC : ∏ i ∈ Finset.range m, (1 + 2*(((2*(i:ℤ)+1 : ℤ)):ℝ)*η/R^2) ≤ 1/(1-η/2) := by
      have hb : ∀ i ∈ Finset.range m, 0 ≤ 2*(((2*(i:ℤ)+1 : ℤ)):ℝ)*η/R^2 := by
        intro i _
        have hKi : (0:ℝ) ≤ (((2*(i:ℤ)+1 : ℤ)):ℝ) := by
          have h2 : (0:ℤ) ≤ 2*(i:ℤ)+1 := by omega
          exact_mod_cast h2
        positivity
      have hKsm : ∑ i ∈ Finset.range m, (((2*(i:ℤ)+1 : ℤ)):ℝ) = (m:ℝ)^2 := by
        have hKi : ∀ i, (((2*(i:ℤ)+1 : ℤ)):ℝ) = 2*(i:ℝ)+1 := by
          intro i; push_cast; ring
        simp only [hKi]
        exact bp_sum_range_odd m
      have hsum : ∑ i ∈ Finset.range m, (2*(((2*(i:ℤ)+1 : ℤ)):ℝ)*η/R^2)
          = 2*η*(m:ℝ)^2/R^2 := by
        calc ∑ i ∈ Finset.range m, (2*(((2*(i:ℤ)+1 : ℤ)):ℝ)*η/R^2)
            = ∑ i ∈ Finset.range m, ((2*η/R^2) * (((2*(i:ℤ)+1 : ℤ)):ℝ)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
          _ = (2*η/R^2) * ∑ i ∈ Finset.range m, (((2*(i:ℤ)+1 : ℤ)):ℝ) :=
              (Finset.mul_sum _ _ _).symm
          _ = (2*η/R^2) * (m:ℝ)^2 := by rw [hKsm]
          _ = 2*η*(m:ℝ)^2/R^2 := by ring
      have hsumle : 2*η*(m:ℝ)^2/R^2 ≤ η/2 := by
        rw [div_le_iff₀ hR2pos]
        have hm2' : (X:ℝ)^2 = 4*(m:ℝ)^2 := by rw [hXm]; push_cast; ring
        nlinarith [hX2R, hm2', hη]
      have h1 := prod_one_add_le_inv_one_sub_sum (Finset.range m)
          (fun i => 2*(((2*(i:ℤ)+1 : ℤ)):ℝ)*η/R^2) hb (by rw [hsum]; linarith)
      refine le_trans h1 (one_div_le_one_div_of_le ?_ ?_)
      · linarith
      · linarith
    calc ∏ i ∈ Finset.range m,
            (bpD R η l (2*(i:ℤ)+1) * bpD R η l (-(2*(i:ℤ)+1)))
        ≤ ∏ i ∈ Finset.range m, (R^4 + 2*R^2*(((2*(i:ℤ)+1 : ℤ)):ℝ)*η) := hA
      _ = R^(4*m) * ∏ i ∈ Finset.range m, (1 + 2*(((2*(i:ℤ)+1 : ℤ)):ℝ)*η/R^2) := hB
      _ ≤ R^(4*m) * (1/(1-η/2)) := mul_le_mul_of_nonneg_left hC (pow_nonneg (le_of_lt hRpos) _)
      _ = R^(2*X) / (1-η/2) := by rw [hexp, mul_one_div]
  have hprod := oddIdx_prod_eq_prod_range X hXeven (fun k => bpD R η l k)
  rw [hprod, hm2]
  exact key

end Work.BW
