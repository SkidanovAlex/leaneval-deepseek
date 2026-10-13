/-
Copyright: work module for the Elgindi finite-time singularity project.

# The bound on `EC` (the angular commutator correction)

`EC α f g` is the angular commutator correction in the `f`-form split of the
`SpecialTransport` pairing (see `STEasyDefs`).  It is a sum over the five order-four slots
`i + j = 4`, `i ≥ 1`, of the terms

  `f · (D_z^jD_θ^i(∂_θ g) - ∂_θ(D_z^jD_θ^i g)) · D_z^jD_θ^i g · w² · sin(2θ)^{-γ}`.

The commutator is controlled by `comm_bound` (an iterated commutator identity), which costs
`sin(2θ)`, and `|f| ≤ 10⁴ sin(2θ) |∂_θ f|_𝒲` (`abs_DzIter_f_le`), so that the two `sin(2θ)`
factors exactly match the `γ`-weighted slots; each pair of slots is then bounded by
`gam_pair_le` against `HkIntegrand`.  The numerical constant is `114560000 = 10⁴·2864·4` per
slot, whence `25 · 114560000 = 2864000000 ≤ 4·10⁹` in total.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.H2.STEasyBnd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The numerical constant of the iterated commutator bound `comm_bound` for `i ≤ 4`:
it is `2864` (attained at `i = 4`). -/
theorem comm_coeff_le (i : ℕ) (hi : i ≤ 4) :
    (∑ r ∈ Finset.range i, ((i.choose (r + 1) : ℝ) * Asin (r + 1) * Bz (i - (r + 1))))
      ≤ 2864 := by
  interval_cases i <;>
    simp [Asin, Bz, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero,
      Nat.choose] <;>
    norm_num

/-- The per-slot bound for the angular commutator correction `EC`. -/
theorem ECterm_le {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothInt f)
    (hcont : ContinuousOn (Function.uncurry f) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hvt : Work.Spaces.VanishTheta f) (hα : 0 < α) (hα1 : α ≤ 1)
    (hWl : Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f))
    (hg : Work.Spaces.SmoothNbhd g) (hHk : Work.Spaces.HkMem α 4 g)
    {z θ : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ)) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    {i j : ℕ} (hi : i ≤ 4) (hc : 1 ≤ i ∧ i + j = 4) :
    |f z θ * ((Work.Spaces.mixed j i (Work.Spaces.pth g) z θ
        - Work.Spaces.pth (Work.Spaces.mixed j i g) z θ) * Work.Spaces.mixed j i g z θ)
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))|
      ≤ 114560000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
        * Work.Spaces.HkIntegrand α 4 g z θ := by
  obtain ⟨hi1, hij⟩ := hc
  have hj4 : j ≤ 4 := by omega
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθIθ
  have hzr : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hzI hθIθ
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := WlInf_nonneg hWl
  have hHkI : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hwnn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hSn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hS _
  have he : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg hwnn hSn
  have hMe : 0 ≤ |Work.Spaces.mixed j i g z θ|
      * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
    mul_nonneg (abs_nonneg _) he
  have hf1 : |f z θ| ≤ 10000 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by
    have h := abs_DzIter_f_le hsm hcont hvt hWl 0 (by norm_num) z hz θ hθIθ
    simpa using h
  have hcomm := comm_bound g hg j i (by omega) hzr hθ
  have hcoef := comm_coeff_le i hi
  have hTnn : 0 ≤ ∑ m ∈ Finset.Icc 1 i, |Work.Spaces.mixed j m g z θ| :=
    Finset.sum_nonneg fun m _ => abs_nonneg _
  have hsplit : ∀ m ∈ Finset.Icc 1 i,
      |Work.Spaces.mixed j m g z θ| * |Work.Spaces.mixed j i g z θ|
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    intro m hm
    obtain ⟨hm1, hmi⟩ := Finset.mem_Icc.mp hm
    exact gam_pair_le hα hHk hzI hθIθ hm1 (by omega) hi1 (by omega)
  have hsum : (∑ m ∈ Finset.Icc 1 i, |Work.Spaces.mixed j m g z θ|)
        * |Work.Spaces.mixed j i g z θ|
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ 4 * Work.Spaces.HkIntegrand α 4 g z θ := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ (fun m hm => hsplit m hm)) ?_
    rw [nsmul_eq_mul]
    have hcard : ((Finset.Icc 1 i).card : ℝ) ≤ 4 := by
      have hc4 : (Finset.Icc 1 i).card ≤ 4 := by rw [Nat.card_Icc]; omega
      exact_mod_cast hc4
    exact mul_le_mul_of_nonneg_right hcard hHkI
  have hsh : Real.sin (2 * θ) * |Work.Spaces.mixed j i (Work.Spaces.pth g) z θ
      - Work.Spaces.pth (Work.Spaces.mixed j i g) z θ|
      ≤ 2864 * ∑ m ∈ Finset.Icc 1 i, |Work.Spaces.mixed j m g z θ| := by
    rw [← abs_of_nonneg hS, ← abs_mul]
    exact le_trans hcomm (mul_le_mul_of_nonneg_right hcoef hTnn)
  calc |f z θ * ((Work.Spaces.mixed j i (Work.Spaces.pth g) z θ
          - Work.Spaces.pth (Work.Spaces.mixed j i g) z θ) * Work.Spaces.mixed j i g z θ)
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))|
      = |f z θ| * |Work.Spaces.mixed j i (Work.Spaces.pth g) z θ
            - Work.Spaces.pth (Work.Spaces.mixed j i g) z θ|
          * |Work.Spaces.mixed j i g z θ|
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hwnn, abs_of_nonneg hSn]
          ring
    _ = (|f z θ| * |Work.Spaces.mixed j i (Work.Spaces.pth g) z θ
            - Work.Spaces.pth (Work.Spaces.mixed j i g) z θ|)
          * (|Work.Spaces.mixed j i g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by ring
    _ ≤ ((10000 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
          * |Work.Spaces.mixed j i (Work.Spaces.pth g) z θ
            - Work.Spaces.pth (Work.Spaces.mixed j i g) z θ|)
          * (|Work.Spaces.mixed j i g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf1 (abs_nonneg _)) hMe
    _ = 10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
          * (Real.sin (2 * θ) * |Work.Spaces.mixed j i (Work.Spaces.pth g) z θ
            - Work.Spaces.pth (Work.Spaces.mixed j i g) z θ|)
          * (|Work.Spaces.mixed j i g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by ring
    _ ≤ 10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
          * (2864 * ∑ m ∈ Finset.Icc 1 i, |Work.Spaces.mixed j m g z θ|)
          * (|Work.Spaces.mixed j i g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsh (mul_nonneg (by norm_num) hWnn)) hMe
    _ = 10000 * 2864 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
          * ((∑ m ∈ Finset.Icc 1 i, |Work.Spaces.mixed j m g z θ|)
            * |Work.Spaces.mixed j i g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by ring
    _ ≤ 10000 * 2864 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
          * (4 * Work.Spaces.HkIntegrand α 4 g z θ) :=
        mul_le_mul_of_nonneg_left hsum
          (mul_nonneg (mul_nonneg (by norm_num) (by norm_num)) hWnn)
    _ = 114560000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
          * Work.Spaces.HkIntegrand α 4 g z θ := by ring

theorem ECBound {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothInt f)
    (hcont : ContinuousOn (Function.uncurry f) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hvt : Work.Spaces.VanishTheta f) (hα : 0 < α) (hα1 : α ≤ 1)
    (hWl : Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f))
    (hg : Work.Spaces.SmoothNbhd g) (hHk : Work.Spaces.HkMem α 4 g)
    {z θ : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ)) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.FTS.H2.EC α f g z θ|
      ≤ 4000000000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
        * Work.Spaces.HkIntegrand α 4 g z θ := by
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := WlInf_nonneg hWl
  have hHkI : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  rw [EC]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
      |(if 1 ≤ i ∧ i + j = 4 then
          f z θ * ((Work.Spaces.mixed j i (Work.Spaces.pth g) z θ
            - Work.Spaces.pth (Work.Spaces.mixed j i g) z θ)
            * Work.Spaces.mixed j i g z θ)
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)|
        ≤ 114560000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
          * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro i hi j hj
    rw [Finset.mem_range] at hi hj
    by_cases hc : 1 ≤ i ∧ i + j = 4
    · rw [if_pos hc]
      exact ECterm_le hsm hcont hvt hα hα1 hWl hg hHk hz hθ (by omega) hc
    · rw [if_neg hc, abs_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hWnn) hHkI
  calc ∑ i ∈ Finset.range 5, |∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j = 4 then
          f z θ * ((Work.Spaces.mixed j i (Work.Spaces.pth g) z θ
            - Work.Spaces.pth (Work.Spaces.mixed j i g) z θ)
            * Work.Spaces.mixed j i g z θ)
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)|
      ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (114560000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
            * Work.Spaces.HkIntegrand α 4 g z θ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        exact Finset.sum_le_sum fun j hj => hterm i hi j hj
    _ = 2864000000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
          * Work.Spaces.HkIntegrand α 4 g z θ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ 4000000000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
          * Work.Spaces.HkIntegrand α 4 g z θ := by nlinarith [hWnn, hHkI]

end Work.FTS.H2
