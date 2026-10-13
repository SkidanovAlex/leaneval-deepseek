/-
# `Work.FTS.LocDataExt.Zfar5` — the order-`5` jet bound of the far factor `zfarR L`

`zfarR L z = (1 - χ(z/L))·FM.Fstar z` is the radial factor of the far part of the localised
profile (`Defs.lean`).  This module proves

  `|D_z^j (zfarR L) z| ≤ A / z`   for `z ∈ [L, 2L]`, `j ≤ 5`, uniformly in `L ≥ 1`,

by the Leibniz rule `Work.FTS.LocData.DzIter_mul_smoothQuad` for the two `C^∞` factors: the
cut-off factor contributes a constant (`Work.FTS.LocDataExt.oneSubChi_jet_le5`, the uniform
bound at order `5`), the profile factor contributes `C/z` (`FMJet5.lean`), and the binomial
theorem turns the Leibniz sum into `2^j ≤ 32`.

The module keeps the hypotheses of the assembly explicit (`zfarR_jet_le5_of_jets`), so that it
can be re-instantiated with any pair of jet bounds.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.LocDataExt.FMJet5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The `D_z`-jet of `zfarR L` as the Leibniz sum of the jets of its two factors.** -/
theorem DzIter_zfarR_eq_sum (L : ℝ) (j : ℕ) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) (θ : ℝ) :
    Work.Spaces.DzIter j (fun z _ => zfarR L z) z θ
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
          (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
            * Work.Spaces.DzIter (j - b) (fun z _ => Work.FM.Fstar z) z θ) := by
  have h := Work.FTS.LocData.DzIter_mul_smoothQuad j
    (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) (fun z _ => Work.FM.Fstar z)
    (θ := θ) hz
    (Work.FTS.LocData.ZFBase.contDiffOn_slice_oneSubChi L)
    (Work.FTS.LocData.ZFBase.contDiffOn_slice_FM_Fstar)
  simpa only [zfarR_apply] using h

/-- The binomial sum in closed form: `∑_{b≤j} (j choose b) = 2^j`. -/
theorem sum_range_choose_real5 (j : ℕ) :
    (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)) = 2 ^ j := by
  rw [← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  ring

/-- **The assembly**: from a bound `Cu` for the `D_z`-jets of the cut-off factor `1 - χ(·/L)`
(uniform in the scale `L ≥ 1`) and a bound `Cv/z` for the `D_z`-jets of `FM.Fstar`, the jets of
`zfarR L` decay like `(32·Cu·Cv)/z` on `[L, 2L]`, uniformly in `L ≥ 1`. -/
theorem zfarR_jet_le5_of_jets {Cu Cv : ℝ} (hCu1 : 1 ≤ Cu) (hCv : 0 < Cv)
    (hCu : ∀ L : ℝ, 1 ≤ L → ∀ c : ℕ, c ≤ 5 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ Cu)
    (hCvM : ∀ a : ℕ, a ≤ 5 → ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter a (fun z _ => Work.FM.Fstar z) z θ| ≤ Cv / z) :
    ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 5 →
      ∀ z ∈ Set.Icc L (2 * L), ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => zfarR L z) z θ| ≤ 32 * Cu * Cv / z := by
  intro L hL j hj z hz θ
  have hz1 : 1 ≤ z := le_trans hL hz.1
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hz0 : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hCu0 : 0 ≤ Cu := le_trans zero_le_one hCu1
  have hCvz : 0 ≤ Cv / z := div_nonneg (le_of_lt hCv) (le_of_lt hzpos)
  rw [DzIter_zfarR_eq_sum L j hz0 θ]
  have hstep : ∀ b ∈ Finset.range (j + 1),
      |(j.choose b : ℝ) * (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
          * Work.Spaces.DzIter (j - b) (fun z _ => Work.FM.Fstar z) z θ)|
        ≤ (j.choose b : ℝ) * (Cu * (Cv / z)) := by
    intro b hb
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have h1 : b ≤ 5 := le_trans hbj hj
    have h2 : j - b ≤ 5 := by omega
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
    _ = 2 ^ j * (Cu * (Cv / z)) := by rw [sum_range_choose_real5]
    _ ≤ 32 * Cu * Cv / z := by
        have h32 : (2 : ℝ) ^ j ≤ 32 := by
          have h : (2 : ℝ) ^ j ≤ 2 ^ 5 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
          norm_num at h
          exact h
        have hnn : 0 ≤ Cu * (Cv / z) := mul_nonneg hCu0 hCvz
        calc 2 ^ j * (Cu * (Cv / z)) ≤ 32 * (Cu * (Cv / z)) :=
              mul_le_mul_of_nonneg_right h32 hnn
          _ = 32 * Cu * Cv / z := by ring

/-- **The order-`5` jet bound of the far factor**: `|D_z^j (zfarR L) z| ≤ A/z` on `[L,2L]`,
uniformly in `L ≥ 1` and `j ≤ 5`, from the delivered cut-off bound
(`oneSubChi_jet_le5`) and the jet bound of the profile (`FM_Fstar_jet_le5`). -/
theorem zfarR_jet_le5_clean :
    ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 5 →
      ∀ z ∈ Set.Icc L (2 * L), ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => zfarR L z) z θ| ≤ A / z := by
  obtain ⟨Cu, hCu1, hCu⟩ := oneSubChi_jet_le5
  obtain ⟨Cv, hCv, hCvle⟩ := FM_Fstar_jet_le5
  exact ⟨32 * Cu * Cv, by positivity, zfarR_jet_le5_of_jets hCu1 hCv hCu hCvle⟩

end Work.FTS.LocDataExt
