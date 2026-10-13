import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

theorem divz_conj2 (CΦ : ℝ) (hCΦpos : 0 < CΦ)
    (hCΦ : ∀ b : ℕ, b ≤ 6 → ∀ z θ : ℝ, 0 < z →
      |Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ| ≤ CΦ * (z / (1 + z)))
    (hleib : ∀ (j i : ℕ) (G : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen G →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.mixed j i (fun z θ => z / (1 + z) * G z θ) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
              (Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ
                * Work.Spaces.mixed (j - b) i G z θ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      ∀ (G : ℝ → ℝ → ℝ) (K : ℝ),
        Work.FTS.EllipticEst.SmoothOpen G →
        Work.Spaces.WlInfMem α 6 G → Work.Spaces.WlInf α 6 G ≤ K →
        ∀ j i : ℕ, 1 ≤ i → j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j i (fun z θ => z / (1 + z) * G z θ) z θ|
            ≤ C * K * (z / (1 + z)) * (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
  -- The constant: `Σ_{b≤j} C(j,b) = 2^j ≤ 2^6 = 64` and the mixed-derivative bound carries
  -- `1000`, so `C = 100000·CΦ` suffices.
  refine ⟨100000 * CΦ, by positivity, ?_⟩
  intro α hα G K hG hGmem hGK j i hi hji z θ hz hθ0 hθpit
  have hαpos : 0 < α := hα.1
  have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθpit⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθpit⟩
  -- expand the Leibniz rule for the radial factor `z/(1+z)`
  rw [hleib j i G hG z θ hz hθ0 hθpit]
  set w : ℝ := z / (1 + z) with hw
  set Y : ℝ := (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) with hY
  have hz1 : (0:ℝ) < 1 + z := by linarith
  have hwpos : 0 < w := by rw [hw]; positivity
  have hwnn : 0 ≤ w := le_of_lt hwpos
  have hCΦnn : 0 ≤ CΦ := le_of_lt hCΦpos
  have hYnn : 0 ≤ Y := by
    rw [hY]
    exact mul_nonneg (by linarith [Work.Spaces.sin_two_nonneg' hθI])
      (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg' hθI) _)
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 G :=
    Work.FTS.StrongPersist.N6Trans.L6FBound.WlInf6_nonneg hGmem
  have hKnn : 0 ≤ K := le_trans hWnn hGK
  -- each summand: the radial factor by `hCΦ`, the mixed derivative by `mixed_le_WlInf6`
  have hterm : ∀ b ∈ Finset.range (j + 1),
      |(j.choose b : ℝ) * (Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ
          * Work.Spaces.mixed (j - b) i G z θ)|
        ≤ (j.choose b : ℝ) * ((CΦ * w) * (1000 * (K * Y))) := by
    intro b hb
    have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hb6 : b ≤ 6 := by omega
    have h1 : |Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ| ≤ CΦ * w := by
      rw [hw]; exact hCΦ b hb6 z θ hz
    have h2 : |Work.Spaces.mixed (j - b) i G z θ| ≤ 1000 * (K * Y) := by
      have h2' := Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6 (α := α) hαpos hG hGmem
        (a := i) hi (b := j - b) (by omega) hz hθIoo
      refine le_trans h2' ?_
      have : Work.Spaces.WlInf α 6 G * Y ≤ K * Y := mul_le_mul_of_nonneg_right hGK hYnn
      exact mul_le_mul_of_nonneg_left this (by norm_num)
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (j.choose b))]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCΦnn hwnn)) (Nat.cast_nonneg _)
  have hsum1 : (∑ b ∈ Finset.range (j + 1),
        |(j.choose b : ℝ) * (Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ
          * Work.Spaces.mixed (j - b) i G z θ)|)
      ≤ ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) * ((CΦ * w) * (1000 * (K * Y))) :=
    Finset.sum_le_sum hterm
  have hchoose : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)) = (2:ℝ)^j := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  have h2j : (2:ℝ)^j ≤ 100 := by
    have hj6 : j ≤ 6 := by omega
    have h := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hj6
    norm_num at h
    linarith
  have hprod : 0 ≤ (CΦ * w) * (K * Y) :=
    mul_nonneg (mul_nonneg hCΦnn hwnn) (mul_nonneg hKnn hYnn)
  refine le_trans (le_trans (Finset.abs_sum_le_sum_abs _ _) hsum1) ?_
  rw [← Finset.sum_mul, hchoose]
  calc (2:ℝ)^j * ((CΦ * w) * (1000 * (K * Y)))
      = 1000 * (2:ℝ)^j * ((CΦ * w) * (K * Y)) := by ring
    _ ≤ 1000 * 100 * ((CΦ * w) * (K * Y)) := by
        apply mul_le_mul_of_nonneg_right _ hprod
        exact mul_le_mul_of_nonneg_left h2j (by norm_num)
    _ = 100000 * CΦ * K * w * (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
        rw [hY]; ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
