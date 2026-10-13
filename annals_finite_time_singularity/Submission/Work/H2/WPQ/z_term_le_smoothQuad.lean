import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.WPQ

open scoped Real

set_option autoImplicit false
set_option maxHeartbeats 0

/-- **The pure `D_z`-summand of the product rule, in the interior class.**  For `f`, `g` smooth
on the open quadrant with `f ∈ 𝒲^{4,∞}` and `i ≤ 4`, the `i`-th summand of the first sum of
`HkIntegrand α 4 (f·g)` is bounded pointwise by the `ℋ⁴`-integrand of `g`:

`(D_z^i (f·g) · w / sin(2θ)^{η/2})² ≤ 10^7 |f|_𝒲² · HkIntegrand α 4 g`.

Interior counterpart of `Work.Spaces.z_term_le` (hypotheses `SmoothInt f`, `SmoothNbhd g` there).
Route: Leibniz for `D_z^i` on the open quadrant (`Work.FTS.LocData.DzIter_mul_smoothQuad`),
`|D_z^b f| ≤ 15|f|_𝒲` (`Work.FTS.H2.WPQ.DzIter_le_WlInf` in `WPQ.Interior`), Cauchy–Schwarz on
the sum (`sq_sum_le_card_mul_sum_sq`, `Work.Spaces.choose_sq_le_256` — the latter is in
`Submission/Work/Spaces/WProductRule.lean`), and `Work.Spaces.sq_le_HkIntegrand_z` for the
`g`-factors.  (Note `z = 0` is fine: `w 0 = 0` makes the left side vanish.) -/
theorem z_term_le_smoothQuad {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g)
    (hfm : Work.Spaces.WlInfMem α 4 f)
    {i : ℕ} (hi : i ≤ 4) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 10 ^ 7 * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkIntegrand α 4 g z θ := by
  have hW := Work.FTS.H2.WPQ.WlInf_nonneg' hfm
  set Hv : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hHv
  have heq := Work.FTS.LocData.DzIter_mul_smoothQuad i f g hz (hf.curry_z hθ) (hg.curry_z hθ)
  have hsplit : (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv) ^ 2
      = (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
            * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2 := by
    rw [heq, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun b _ => by ring)
  rw [hsplit]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
      * (Work.Spaces.DzIter (i - b) g z θ * Hv))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hper : ∀ b ∈ Finset.range (i + 1),
      (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
          * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
        ≤ 57600 * (Work.Spaces.WlInf α 4 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hDf : |Work.Spaces.DzIter b f z θ| ≤ 15 * Work.Spaces.WlInf α 4 f :=
      Work.FTS.H2.WPQ.DzIter_le_WlInf hf hfm (by omega) hz hθ
    have hx : (Work.Spaces.DzIter b f z θ) ^ 2 ≤ (15 * Work.Spaces.WlInf α 4 f) ^ 2 := by
      have hB : (0:ℝ) ≤ 15 * Work.Spaces.WlInf α 4 f := mul_nonneg (by norm_num) hW
      have h1 := (abs_le.mp hDf).1
      have h2 := (abs_le.mp hDf).2
      nlinarith [hB, h1, h2]
    have hch : ((i.choose b : ℝ)) ^ 2 ≤ 256 :=
      Work.Spaces.choose_sq_le_256 i b hbi hi
    calc (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
            * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
        = ((i.choose b : ℝ)) ^ 2 * (Work.Spaces.DzIter b f z θ) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by ring
      _ ≤ 256 * (15 * Work.Spaces.WlInf α 4 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by
          gcongr
      _ = 57600 * (Work.Spaces.WlInf α 4 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by ring
  have hsumsq : ∑ b ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2
      ≤ 5 * Work.Spaces.HkIntegrand α 4 g z θ := by
    calc ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2
        ≤ ∑ b ∈ Finset.range (i + 1), Work.Spaces.HkIntegrand α 4 g z θ :=
          Finset.sum_le_sum (fun b hb =>
            Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ (i - b) (by omega))
      _ = ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 4 g z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ 5 * Work.Spaces.HkIntegrand α 4 g z θ := by
          have hnn := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
          have hI2 : (i : ℝ) + 1 ≤ 5 := by exact_mod_cast (by omega : i + 1 ≤ 5)
          nlinarith
  calc (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
            * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
      ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) *
          ∑ b ∈ Finset.range (i + 1),
            (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
              * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2 := hcs
    _ ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1),
          (57600 * (Work.Spaces.WlInf α 4 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
    _ = 57600 * (Work.Spaces.WlInf α 4 f) ^ 2 * (((i : ℝ) + 1)
          * ∑ b ∈ Finset.range (i + 1),
            (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 57600 * (Work.Spaces.WlInf α 4 f) ^ 2
          * (5 * (5 * Work.Spaces.HkIntegrand α 4 g z θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hI2 : (i : ℝ) + 1 ≤ 5 := by exact_mod_cast (by omega : i + 1 ≤ 5)
        exact mul_le_mul hI2 hsumsq (Finset.sum_nonneg (fun b _ => sq_nonneg _)) (by norm_num)
    _ ≤ 10 ^ 7 * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkIntegrand α 4 g z θ := by
        have hnn := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
        have h2 : 0 ≤ (Work.Spaces.WlInf α 4 f) ^ 2 := sq_nonneg _
        have hh : 57600 * (Work.Spaces.WlInf α 4 f) ^ 2
              * (5 * (5 * Work.Spaces.HkIntegrand α 4 g z θ))
            = 1440000 * ((Work.Spaces.WlInf α 4 f) ^ 2
                * Work.Spaces.HkIntegrand α 4 g z θ) := by ring
        rw [hh, show (10:ℝ)^7 * (Work.Spaces.WlInf α 4 f)^2
              * Work.Spaces.HkIntegrand α 4 g z θ
            = 10^7 * ((Work.Spaces.WlInf α 4 f)^2
                * Work.Spaces.HkIntegrand α 4 g z θ) from by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg h2 hnn)

end Work.H2.WPQ
