import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData6

set_option maxHeartbeats 1600000

/-- The binomial sum in closed form, order-`6` copy: `∑_{b≤j} (j choose b) = 2^j`. -/
private theorem sum_range_choose_real6 (j : ℕ) :
    (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)) = 2 ^ j := by
  rw [← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  ring

/-- **The assembly**: from a bound `Cu` for the `D_z`-jets of the cut-off factor
`1 - χ(·/L)` (uniform in the scale `L ≥ 1`) up to order `6` and a bound `Cv/z` for the
`D_z`-jets of `FM.Fstar` up to order `6`, the jets of `zfarR L = (1 - χ(·/L))·FM.Fstar`
decay like `(64·Cu·Cv)/z` on `[L, 2L]`, uniformly in `L ≥ 1`.

The proof is the order-`6` instance of the Leibniz computation of
`Work.FTS.LocDataExt.zfarR_jet_le5_of_jets`: by the Leibniz rule the `j`-th jet (`j ≤ 6`) is
`∑_{b≤j} (j choose b)·(jet_b u)·(jet_{j-b} v)`, both factors of every summand are at order
`≤ 6` (so each is `≤ (j choose b)·Cu·Cv/z`), and summing with the binomial theorem and
`2^6 = 64` gives the claim. -/
theorem zfarR_jet_le6_of_jets {Cu Cv : ℝ} (hCu1 : 1 ≤ Cu) (hCv : 0 < Cv)
    (hCu : ∀ L : ℝ, 1 ≤ L → ∀ c : ℕ, c ≤ 6 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ Cu)
    (hCvM : ∀ a : ℕ, a ≤ 6 → ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter a (fun z _ => Work.FM.Fstar z) z θ| ≤ Cv / z) :
    ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 6 →
      ∀ z ∈ Set.Icc L (2 * L), ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ 64 * Cu * Cv / z := by
  intro L hL j hj z hz θ
  have hz1 : 1 ≤ z := le_trans hL hz.1
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hz0 : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hCu0 : 0 ≤ Cu := le_trans zero_le_one hCu1
  have hCvz : 0 ≤ Cv / z := div_nonneg (le_of_lt hCv) (le_of_lt hzpos)
  rw [Work.FTS.LocDataExt.DzIter_zfarR_eq_sum L j hz0 θ]
  have hstep : ∀ b ∈ Finset.range (j + 1),
      |(j.choose b : ℝ) * (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
          * Work.Spaces.DzIter (j - b) (fun z _ => Work.FM.Fstar z) z θ)|
        ≤ (j.choose b : ℝ) * (Cu * (Cv / z)) := by
    intro b hb
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have h1 : b ≤ 6 := le_trans hbj hj
    have h2 : j - b ≤ 6 := by omega
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    rw [abs_mul]
    exact mul_le_mul (hCu L hL b h1 z hz0 θ) (hCvM (j - b) h2 z hz1 θ)
      (abs_nonneg _) hCu0
  calc |∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
        (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
          * Work.Spaces.DzIter (j - b) (fun z _ => Work.FM.Fstar z) z θ)|
      ≤ ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) * (Cu * (Cv / z)) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hstep)
    _ = (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)) * (Cu * (Cv / z)) := by
        rw [Finset.sum_mul]
    _ = 2 ^ j * (Cu * (Cv / z)) := by rw [sum_range_choose_real6]
    _ ≤ 64 * Cu * Cv / z := by
        have h64 : (2 : ℝ) ^ j ≤ 64 := by
          have h : (2 : ℝ) ^ j ≤ 2 ^ 6 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
          norm_num at h
          exact h
        have hnn : 0 ≤ Cu * (Cv / z) := mul_nonneg hCu0 hCvz
        calc 2 ^ j * (Cu * (Cv / z)) ≤ 64 * (Cu * (Cv / z)) :=
              mul_le_mul_of_nonneg_right h64 hnn
          _ = 64 * Cu * Cv / z := by ring

end Work.FTS.LocData6
