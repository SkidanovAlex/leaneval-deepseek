import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.DzIter_bumpZ_bound
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le
import Submission.Work.FTS.LocData.HlocFactor

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `Work.FTS.LocData.HkIntegrand_hLoc_le` — the bump `hLoc` lies in `𝓗⁴` with a decaying weight

The localised bump `hLoc α z θ = φ(z)·Γ(θ)` (`φ = bumpZ = χ(4·-5)`, `Γ(θ) = (sinθcos²θ)^{α/3}`)
is the perturbation datum of the route.  This module proves the pointwise estimate

  `HkIntegrand α 4 (hLoc α) z θ ≤ K² · angMaj α θ / (1+z)²`   on `[0,∞) × [0,π/2]`,

with `K` depending only on `α ∈ (0,1]` — in fact only on the universal constant bounding the
`D_z`-iterates of the radial bump.

The argument is a term-by-term estimate of the finite sum defining `HkIntegrand`:

* `HlocFactor` separates every derivative, `D_z^j D_θ^i (φ·Γ) = (D_θ^i Γ)(0,·)·(T1^[j] φ)`;
* the radial factor is bounded by the universal constant `Cb` of `DzIter_bumpZ_bound`;
* the angular factor of the second block is bounded by `100000·Γ` (`DthIter_Gam_abs_le`) and
  `|Γ| ≤ 1` (`Gam_bounds`);
* the weight `w = (1+z)²/z²`, `w_θ = sin(2θ)^{-γ/2}` contribute exactly `w²·sin^{-η}`, resp.
  `w²·sin^{-γ}`, and the two angular weights are the two summands of `angMaj`;
* the factor `w(z)²` is absorbed into `1/(1+z)²` on the support `[3/4,7/4]` of the bump
  (`w_sq_le_on_support`), while off the support the integrand vanishes
  (`HkIntegrand_hLoc_eq_zero_off`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

/-! ## Elementary facts -/

/-- `sin(2θ) ≥ 0` on the angular interval. -/
private theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  apply Real.sin_nonneg_of_mem_Icc
  exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `∑_{i<5} c = 5c`. -/
private theorem sum_range_five_const (c : ℝ) : (∑ _i ∈ Finset.range 5, c) = 5 * c := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  norm_num

/-! ## The two termwise bounds -/

/-- **The `D_z`-block of `HkIntegrand α 4 (hLoc α)`.**  The angular factor contributes `Γ²`, the
radial factor `(T1^[i] φ)² ≤ Cb²`, and the weight `w²·sin^{-η}`. -/
private theorem hLoc_term1_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (Cb : ℝ)
    (hCb : ∀ c ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => bumpZ z) z θ| ≤ Cb)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) {i : ℕ} (hi : i ≤ 4) :
    (Work.Spaces.DzIter i (hLoc α) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Cb ^ 2 * (Work.Spaces.w z) ^ 2
        * (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hP : ((T1^[i]) bumpZ z) ^ 2 ≤ Cb ^ 2 := by
    have h := hCb i hi z hz θ
    rw [DzIter_bumpZ_eq i θ z] at h
    have h2 := pow_le_pow_left₀ (abs_nonneg ((T1^[i]) bumpZ z)) h 2
    simpa only [sq_abs] using h2
  have hw : (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]
      congr 1
      ring
    rw [div_eq_mul_inv, mul_pow, inv_pow, h1, ← Real.rpow_neg hs0]
  have hws : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  rw [congrFun (congrFun (DzIter_hLoc α i) z) θ]
  calc ((Work.Spaces.Gam α θ * (T1^[i]) bumpZ z)
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = ((T1^[i]) bumpZ z) ^ 2 * (Work.Spaces.Gam α θ) ^ 2
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by ring
    _ ≤ Cb ^ 2 * (Work.Spaces.Gam α θ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        rw [hw]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hP (sq_nonneg _)) hws
    _ = Cb ^ 2 * (Work.Spaces.w z) ^ 2
          * (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring

/-- **The mixed block of `HkIntegrand α 4 (hLoc α)`.**  The angular factor contributes at most
`(100000·Γ)²`, the radial factor `(T1^[j] φ)² ≤ Cb²`, and the weight `W = w·sin^{-γ/2}` gives
`w²·sin^{-γ}`. -/
private theorem hLoc_term2_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (Cb : ℝ)
    (hCb : ∀ c ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => bumpZ z) z θ| ≤ Cb)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) {j i : ℕ}
    (hi : i ≤ 4) (hj : j ≤ 4) :
    (Work.Spaces.mixed j i (hLoc α) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ (10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2
        * (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hA0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hAabs : |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
      ≤ 100000 * Work.Spaces.Gam α θ := DthIter_Gam_abs_le i hi α hα hα1 hθ
  have hA : (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
      ≤ (10 : ℝ) ^ 10 * Work.Spaces.Gam α θ ^ 2 := by
    have h2 := pow_le_pow_left₀ (abs_nonneg _) hAabs 2
    rw [sq_abs, mul_pow] at h2
    have h10 : ((100000 : ℝ)) ^ 2 = (10 : ℝ) ^ 10 := by norm_num
    calc (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ (100000 : ℝ) ^ 2 * Work.Spaces.Gam α θ ^ 2 := h2
      _ = (10 : ℝ) ^ 10 * Work.Spaces.Gam α θ ^ 2 := by rw [h10]
  have hP : ((T1^[j]) bumpZ z) ^ 2 ≤ Cb ^ 2 := by
    have h := hCb j hj z hz θ
    rw [DzIter_bumpZ_eq j θ z] at h
    have h2 := pow_le_pow_left₀ (abs_nonneg ((T1^[j]) bumpZ z)) h 2
    simpa only [sq_abs] using h2
  have hWt : (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]
      congr 1
      ring
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, h1]
  have hws : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  rw [congrFun (congrFun (mixed_hLoc α j i) z) θ]
  calc ((Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ * (T1^[j]) bumpZ z)
        * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
          * ((T1^[j]) bumpZ z) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ ((10 : ℝ) ^ 10 * Work.Spaces.Gam α θ ^ 2) * Cb ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        rw [hWt]
        exact mul_le_mul_of_nonneg_right (mul_le_mul hA hP (sq_nonneg _) (by positivity)) hws
    _ = (10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2
          * (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring

/-! ## The pointwise bound against the weight `w²` -/

/-- **The pointwise bound**: on the whole quadrant, `HkIntegrand α 4 (hLoc α) ≤ K·w²·angMaj`,
where `K = (5 + 25·10^10)·Cb²` counts the `5` terms of the `D_z`-block and the at most `25`
terms of the mixed block, and where `Cb` bounds the `D_z`-iterates of the radial bump. -/
private theorem hLoc_HkIntegrand_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (Cb : ℝ)
    (hCb : ∀ c ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => bumpZ z) z θ| ≤ Cb)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 4 (hLoc α) z θ
      ≤ (5 + 25 * 10 ^ 10) * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hCb2 : 0 ≤ Cb ^ 2 := sq_nonneg Cb
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hAng : angMaj α θ = Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      + Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) + 1 :=
    angMaj_apply α θ
  have hB0 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  have hE0 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  set Bv := Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) with hBdef
  set Ev := Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hEdef
  have hAng' : angMaj α θ = Bv + Ev + 1 := by rw [hAng, hBdef, hEdef]
  have hBle : Bv ≤ angMaj α θ := by rw [hAng']; linarith [hE0]
  have hEle : Ev ≤ angMaj α θ := by rw [hAng']; linarith [hB0]
  have hsum1 : (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (hLoc α) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 5 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ := by
    calc (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (hLoc α) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range 5, (Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Ev) :=
          Finset.sum_le_sum (fun i hi => by
            rw [hEdef]
            exact hLoc_term1_le α hα hα1 Cb hCb hz hθ
              (by have h5 : i < 5 := Finset.mem_range.mp hi; omega))
      _ = 5 * (Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Ev) := sum_range_five_const _
      _ ≤ 5 * (Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEle (mul_nonneg hCb2 hw2))
            (by norm_num)
      _ = 5 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ := by ring
  have hsum2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (hLoc α) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 25 * ((10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Bv) := by
    have hT : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (hLoc α) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ (10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Bv := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ 4
      · rw [if_pos hc]
        rw [hBdef]
        exact hLoc_term2_le α hα hα1 Cb hCb hz hθ
          (by have h5 : i < 5 := Finset.mem_range.mp hi; omega)
          (by have h5 : j < 5 := Finset.mem_range.mp hj; omega)
      · rw [if_neg hc]
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCb2) hw2) hB0
    calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (hLoc α) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ ∑ i ∈ Finset.range 5, ∑ _j ∈ Finset.range 5,
            ((10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Bv) :=
          Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hT i hi))
      _ = 25 * ((10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Bv) := by
          have h1 : (∑ i ∈ Finset.range 5, ∑ _j ∈ Finset.range 5,
                ((10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Bv))
              = ∑ _i ∈ Finset.range 5,
                (5 * ((10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Bv)) :=
            Finset.sum_congr rfl (fun i _ => sum_range_five_const _)
          rw [h1, sum_range_five_const]
          ring
  have hHk : Work.Spaces.HkIntegrand α 4 (hLoc α) z θ
      = (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (hLoc α) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (hLoc α) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := rfl
  calc Work.Spaces.HkIntegrand α 4 (hLoc α) z θ
      = _ := hHk
    _ ≤ 5 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ
          + 25 * ((10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * Bv) :=
        add_le_add hsum1 hsum2
    _ ≤ 5 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ
          + 25 * ((10 : ℝ) ^ 10 * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ) := by
        refine add_le_add le_rfl ?_
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBle (by positivity))
          (by norm_num)
    _ = (5 + 25 * 10 ^ 10) * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ := by ring

/-! ## The main estimate -/

theorem HkIntegrand_hLoc_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (hLoc α) z θ ≤ K ^ 2 * angMaj α θ / (1 + z) ^ 2 := by
  obtain ⟨Cb, hCb⟩ := DzIter_bumpZ_bound
  refine ⟨(5 + 25 * 10 ^ 10) * Cb ^ 2 * (1771561 / 1296 : ℝ) + 1, ?_, ?_⟩
  · have h1 : 0 ≤ (5 + 25 * 10 ^ 10) * Cb ^ 2 * (1771561 / 1296 : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Cb)) (by norm_num)
    linarith
  · intro z hz θ hθ
    have hA0 : 0 ≤ angMaj α θ := angMaj_nonneg hθ
    have hden : 0 ≤ (1 + z) ^ 2 := sq_nonneg _
    have hmain := hLoc_HkIntegrand_le α hα hα1 Cb hCb hz hθ
    by_cases hsupp : z ∈ Set.Icc (3 / 4 : ℝ) (7 / 4)
    · have hw := w_sq_le_on_support hsupp
      have hK0 : 0 ≤ (5 + 25 * 10 ^ 10) * Cb ^ 2 :=
        mul_nonneg (by norm_num) (sq_nonneg Cb)
      have hstep : (5 + 25 * 10 ^ 10) * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ
          ≤ (5 + 25 * 10 ^ 10) * Cb ^ 2
              * ((1771561 / 1296 : ℝ) / (1 + z) ^ 2) * angMaj α θ := by
        refine mul_le_mul_of_nonneg_right ?_ hA0
        exact mul_le_mul_of_nonneg_left hw hK0
      set x := (5 + 25 * 10 ^ 10) * Cb ^ 2 * (1771561 / 1296 : ℝ) with hxdef
      have hx0 : 0 ≤ x := by
        rw [hxdef]
        exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Cb)) (by norm_num)
      have hKle : x ≤ (x + 1) ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg (x + 1)]
      calc Work.Spaces.HkIntegrand α 4 (hLoc α) z θ
          ≤ (5 + 25 * 10 ^ 10) * Cb ^ 2 * (Work.Spaces.w z) ^ 2 * angMaj α θ := hmain
        _ ≤ (5 + 25 * 10 ^ 10) * Cb ^ 2
              * ((1771561 / 1296 : ℝ) / (1 + z) ^ 2) * angMaj α θ := hstep
        _ = x * angMaj α θ / (1 + z) ^ 2 := by rw [hxdef]; ring
        _ ≤ (x + 1) ^ 2 * angMaj α θ / (1 + z) ^ 2 := by
            refine div_le_div_of_nonneg_right ?_ hden
            exact mul_le_mul_of_nonneg_right hKle hA0
    · have hzero : Work.Spaces.HkIntegrand α 4 (hLoc α) z θ = 0 :=
        HkIntegrand_hLoc_eq_zero_off hsupp θ
      rw [hzero]
      exact div_nonneg (mul_nonneg (sq_nonneg _) hA0) hden

end Work.FTS.LocData
