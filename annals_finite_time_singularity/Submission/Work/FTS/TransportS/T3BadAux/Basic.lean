/-
Copyright: work module for the Elgindi finite-time singularity project.

# `T3BadAux/Basic`: `Badz` against `Hhard`, and the slot bookkeeping for the open class

`Badz2 α f g = Badz α f g + Mismatchz α f g` is the exceptional part of the `D_z`-transport
pairing.  This file records the structural facts that let the `Badz` half be estimated
through the (already proved) radial integration-by-parts family of `Hhard`
(`Submission/Work/FTS/H2/HhardZibp.lean`):

* `Badz_eq_Hhard`: `Badz α f g z θ = Hhard α f g z θ` on `Iθ`;
* `Xz_sq_eq`/`Yz_sq_eq` and the slot bounds: each weighted block of `w²·ZU` resp.
  `w²·ZU₅` has its square equal to a single summand of `HkIntegrand α 4 g` resp.
  `HkIntegrand α 5 g`;
* `abs_Hhard_le`: `|Hhard| ≤ M (w²ZU + ∑_k Yz_k²)` when `|f| ≤ M`.

All declarations are `sorry`-free and rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.T2Defs
import Submission.Work.FTS.H2.T2HardAux
import Submission.Work.FTS.H2.HhardZibp
import Submission.Work.FTS.H2.Transport3Aux.Defs
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.HardDefs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T3BadAux

set_option autoImplicit false

set_option maxHeartbeats 1000000

/-! ## The `Badz`/`Hhard` identification -/

/-- **The exceptional order-five part of the `D_z`-pairing is the `Hhard` summand.** -/
theorem Badz_eq_Hhard (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.H2.Badz α f g z θ = Work.FTS.H2.Hhard α f g z θ := by
  obtain ⟨hW1, hW2⟩ := Work.FTS.H2.Whz_Wm_sq α hα z θ hθ
  rw [Work.FTS.H2.Badz_apply, Work.FTS.H2.Hhard]
  have hsum : (∑ k : Fin 5, Spaces.pz (Work.FTS.H2.Thard g k) z θ
        * Work.FTS.H2.Thard g k z θ * (Spaces.w z) ^ 2 * Work.FTS.H2.sghard α k θ)
      = Spaces.pz (Spaces.DzIter 4 g) z θ * Spaces.DzIter 4 g z θ * (Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Spaces.eta))
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j = 4 then
              Spaces.pz (Spaces.mixed j i g) z θ * Spaces.mixed j i g z θ
                * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
            else 0) := by
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, Work.FTS.H2.Thard, Work.FTS.H2.sghard]
    norm_num
    ring_nf
  have htop2 : f z θ * Spaces.Dz (Spaces.DzIter 4 g) z θ * Spaces.DzIter 4 g z θ
        * ((Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.eta)))
      = f z θ * z * (Spaces.pz (Spaces.DzIter 4 g) z θ * Spaces.DzIter 4 g z θ
          * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.eta))) := by
    simp only [Spaces.Dz]
    ring
  have hsum2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j = 4 then
          f z θ * Spaces.Dz (Spaces.mixed j i g) z θ * Spaces.mixed j i g z θ
            * ((Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
        else 0))
      = f z θ * z * (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j = 4 then
          Spaces.pz (Spaces.mixed j i g) z θ * Spaces.mixed j i g z θ
            * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
        else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : 1 ≤ i ∧ i + j = 4
    · rw [if_pos h, if_pos h]
      simp only [Spaces.Dz]
      ring
    · rw [if_neg h, if_neg h]
      ring
  rw [hsum, hW1, hW2, htop2, hsum2]
  ring

/-! ## The weights -/

/-- `(w / sin(2θ)^{η/2})² = w² sin(2θ)^{-η}`. -/
theorem w_div_sin_sq {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ((Work.Spaces.w z) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ
  have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hs]
    norm_num
  rw [div_pow, h1, Real.rpow_neg hs, div_eq_mul_inv]

/-- `Wt α z θ ² = w² sin(2θ)^{-γ}`. -/
theorem Wt_sq_eq {α z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hs]
    ring_nf
  rw [Spaces.Wt, Spaces.wTheta, mul_pow, h1]

/-! ## The weighted blocks -/

/-- The square of the `k`-th weighted order-four block. -/
theorem Xz_sq_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.TransportS.Xz α g k z θ) ^ 2
      = (Work.FTS.H2.Thard g k z θ) ^ 2 * Work.FTS.H2.sghard α k θ
        * (Work.Spaces.w z) ^ 2 := by
  rcases eq_or_ne k.val 0 with hk | hk
  · obtain rfl : k = 0 := Fin.ext hk
    have hX : Work.FTS.TransportS.Xz α g 0 z θ
        = Spaces.DzIter 4 g z θ * ((Work.Spaces.w z)
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
      simp [Work.FTS.TransportS.Xz]
    have hT : Work.FTS.H2.Thard g 0 z θ = Spaces.DzIter 4 g z θ := by
      simp [Work.FTS.H2.Thard_eq_mixed, Work.Spaces.mixed_zero_right]
    have hkey : (Spaces.DzIter 4 g z θ * ((Work.Spaces.w z)
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Spaces.DzIter 4 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.w z) ^ 2 := by
      rw [mul_pow, w_div_sin_sq hθ]
      ring
    rw [hX, hT, Work.FTS.H2.sghard_apply_zero α θ, hkey]
  · have hX : Work.FTS.TransportS.Xz α g k z θ
        = Spaces.mixed (4 - k.val) k.val g z θ * Spaces.Wt α z θ := by
      simp [Work.FTS.TransportS.Xz, hk]
    have hT : Work.FTS.H2.Thard g k z θ = Spaces.mixed (4 - k.val) k.val g z θ := by
      rw [Work.FTS.H2.Thard_eq_mixed]
    have hkey : (Spaces.mixed (4 - k.val) k.val g z θ * Spaces.Wt α z θ) ^ 2
        = (Spaces.mixed (4 - k.val) k.val g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2 := by
      rw [mul_pow, Wt_sq_eq (α := α) hθ]
      ring
    rw [hX, hT, Work.FTS.H2.sghard_apply_ne α k hk, hkey]

/-- The square of the `k`-th weighted order-five block. -/
theorem Yz_sq_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.TransportS.Yz α g k z θ) ^ 2
      = (Spaces.Dz (Work.FTS.H2.Thard g k) z θ) ^ 2 * Work.FTS.H2.sghard α k θ
        * (Work.Spaces.w z) ^ 2 := by
  rcases eq_or_ne k.val 0 with hk | hk
  · obtain rfl : k = 0 := Fin.ext hk
    have hY : Work.FTS.TransportS.Yz α g 0 z θ
        = Spaces.DzIter 5 g z θ * ((Work.Spaces.w z)
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
      simp [Work.FTS.TransportS.Yz]
    have hdz : Spaces.Dz (Work.FTS.H2.Thard g 0) z θ = Spaces.DzIter 5 g z θ := by
      simp [Work.FTS.TransportS.Dz_Thard]
    have hkey : (Spaces.DzIter 5 g z θ * ((Work.Spaces.w z)
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Spaces.DzIter 5 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.w z) ^ 2 := by
      rw [mul_pow, w_div_sin_sq hθ]
      ring
    rw [hY, hdz, Work.FTS.H2.sghard_apply_zero α θ, hkey]
  · have hY : Work.FTS.TransportS.Yz α g k z θ
        = Spaces.mixed (5 - k.val) k.val g z θ * Spaces.Wt α z θ := by
      simp [Work.FTS.TransportS.Yz, hk]
    have hdz : Spaces.Dz (Work.FTS.H2.Thard g k) z θ
        = Spaces.mixed (5 - k.val) k.val g z θ := by
      rw [Work.FTS.TransportS.Dz_Thard]
    have hkey : (Spaces.mixed (5 - k.val) k.val g z θ * Spaces.Wt α z θ) ^ 2
        = (Spaces.mixed (5 - k.val) k.val g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2 := by
      rw [mul_pow, Wt_sq_eq (α := α) hθ]
      ring
    rw [hY, hdz, Work.FTS.H2.sghard_apply_ne α k hk, hkey]

/-! ## The angular densities against `HkIntegrand` -/

/-- Each weighted order-four block is a single summand of `HkIntegrand α 4 g`. -/
theorem Thard_sq_le_hk (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.H2.Thard g k z θ) ^ 2 * Work.FTS.H2.sghard α k θ
        * (Work.Spaces.w z) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  rcases eq_or_ne k.val 0 with hk | hk
  · obtain rfl : k = 0 := Fin.ext hk
    have h := Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 4 (by norm_num)
    rw [mul_pow, w_div_sin_sq hθ] at h
    have hT : Work.FTS.H2.Thard g 0 z θ = Spaces.DzIter 4 g z θ := by
      simp [Work.FTS.H2.Thard_eq_mixed, Work.Spaces.mixed_zero_right]
    rw [hT, Work.FTS.H2.sghard_apply_zero α θ]
    nlinarith [h]
  · have h := Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ k.val (4 - k.val) (by omega)
      (by have := k.isLt; omega)
    rw [mul_pow, Wt_sq_eq (α := α) hθ] at h
    have hT : Work.FTS.H2.Thard g k z θ = Spaces.mixed (4 - k.val) k.val g z θ := by
      rw [Work.FTS.H2.Thard_eq_mixed]
    rw [hT, Work.FTS.H2.sghard_apply_ne α k hk]
    nlinarith [h]

/-- Each weighted order-five block is a single summand of `HkIntegrand α 5 g`. -/
theorem DzThard_sq_le_hk (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Spaces.Dz (Work.FTS.H2.Thard g k) z θ) ^ 2 * Work.FTS.H2.sghard α k θ
        * (Work.Spaces.w z) ^ 2 ≤ Work.Spaces.HkIntegrand α 5 g z θ := by
  rcases eq_or_ne k.val 0 with hk | hk
  · obtain rfl : k = 0 := Fin.ext hk
    have h := Work.Spaces.sq_le_HkIntegrand_z α 5 g z θ 5 (by norm_num)
    rw [mul_pow, w_div_sin_sq hθ] at h
    have hdz : Spaces.Dz (Work.FTS.H2.Thard g 0) z θ = Spaces.DzIter 5 g z θ := by
      simp [Work.FTS.TransportS.Dz_Thard]
    rw [hdz, Work.FTS.H2.sghard_apply_zero α θ]
    nlinarith [h]
  · have h := Work.Spaces.sq_le_HkIntegrand_mixed α 5 g z θ k.val (5 - k.val) (by omega)
      (by have := k.isLt; omega)
    rw [mul_pow, Wt_sq_eq (α := α) hθ] at h
    have hdz : Spaces.Dz (Work.FTS.H2.Thard g k) z θ
        = Spaces.mixed (5 - k.val) k.val g z θ := by
      rw [Work.FTS.TransportS.Dz_Thard]
    rw [hdz, Work.FTS.H2.sghard_apply_ne α k hk]
    nlinarith [h]

/-- `(Xz α g k)² ≤ HkIntegrand α 4 g`. -/
theorem Xz_sq_le_hk (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.TransportS.Xz α g k z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  rw [Xz_sq_eq α g k hθ]
  exact Thard_sq_le_hk α g k hθ

/-- `(Yz α g k)² ≤ HkIntegrand α 5 g`. -/
theorem Yz_sq_le_hk (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.TransportS.Yz α g k z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 5 g z θ := by
  rw [Yz_sq_eq α g k hθ]
  exact DzThard_sq_le_hk α g k hθ

/-- `w(z)²·ZU α g z θ = ∑_k (Xz α g k z θ)²`. -/
theorem w2ZU_eq (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z) ^ 2 * Work.FTS.H2.ZU α g z θ
      = ∑ k : Fin 5, (Work.FTS.TransportS.Xz α g k z θ) ^ 2 := by
  rw [Work.FTS.H2.ZU, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Xz_sq_eq α g k hθ]
  ring

/-- `w(z)²·(∑_k (D_z Θ_k)² σ_k) = ∑_k (Yz α g k)²`. -/
theorem w2ZU5_eq (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z) ^ 2 * (∑ k : Fin 5,
        (Spaces.Dz (Work.FTS.H2.Thard g k) z θ) ^ 2 * Work.FTS.H2.sghard α k θ)
      = ∑ k : Fin 5, (Work.FTS.TransportS.Yz α g k z θ) ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Yz_sq_eq α g k hθ]
  ring

/-- `w²·ZU ≤ 5·HkIntegrand α 4 g` on `Iθ`. -/
theorem w2ZU_le (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z) ^ 2 * Work.FTS.H2.ZU α g z θ
      ≤ 5 * Work.Spaces.HkIntegrand α 4 g z θ := by
  rw [w2ZU_eq α g hθ]
  calc (∑ k : Fin 5, (Work.FTS.TransportS.Xz α g k z θ) ^ 2)
      ≤ ∑ _k : Fin 5, Work.Spaces.HkIntegrand α 4 g z θ :=
        Finset.sum_le_sum fun k _ => Xz_sq_le_hk α g k hθ
    _ = 5 * Work.Spaces.HkIntegrand α 4 g z θ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

/-- `w²·(∑_k (D_z Θ_k)² σ_k) ≤ 5·HkIntegrand α 5 g` on `Iθ`. -/
theorem w2ZU5_le (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z) ^ 2 * (∑ k : Fin 5,
        (Spaces.Dz (Work.FTS.H2.Thard g k) z θ) ^ 2 * Work.FTS.H2.sghard α k θ)
      ≤ 5 * Work.Spaces.HkIntegrand α 5 g z θ := by
  rw [w2ZU5_eq α g hθ]
  calc (∑ k : Fin 5, (Work.FTS.TransportS.Yz α g k z θ) ^ 2)
      ≤ ∑ _k : Fin 5, Work.Spaces.HkIntegrand α 5 g z θ :=
        Finset.sum_le_sum fun k _ => Yz_sq_le_hk α g k hθ
    _ = 5 * Work.Spaces.HkIntegrand α 5 g z θ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

/-! ## Domination of `Hhard` -/

/-- `|Hhard α f g z θ| ≤ M·(w²ZU + ∑_k (Yz α g k z θ)²)` when `|f z θ| ≤ M` and `z ≥ 0`. -/
theorem abs_Hhard_le {α : ℝ} {f g : ℝ → ℝ → ℝ} {M z θ : ℝ} (hM : 0 ≤ M) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) (hf : |f z θ| ≤ M) :
    |Work.FTS.H2.Hhard α f g z θ|
      ≤ M * ((Work.Spaces.w z) ^ 2 * Work.FTS.H2.ZU α g z θ
          + ∑ k : Fin 5, (Work.FTS.TransportS.Yz α g k z θ) ^ 2) := by
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hterm : ∀ k : Fin 5,
      |z * (Spaces.pz (Work.FTS.H2.Thard g k) z θ * Work.FTS.H2.Thard g k z θ
            * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.sghard α k θ)|
        ≤ Work.FTS.H2.Thard g k z θ ^ 2 * Work.FTS.H2.sghard α k θ * (Work.Spaces.w z) ^ 2
          + (Work.FTS.TransportS.Yz α g k z θ) ^ 2 := by
    intro k
    have hs : 0 ≤ Work.FTS.H2.sghard α k θ := Work.FTS.H2.sghard_nonneg α k hθ
    have hzeq : z * (Spaces.pz (Work.FTS.H2.Thard g k) z θ * Work.FTS.H2.Thard g k z θ
          * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.sghard α k θ)
        = (Spaces.Dz (Work.FTS.H2.Thard g k) z θ * Work.FTS.H2.Thard g k z θ
          * (Work.Spaces.w z) ^ 2) * Work.FTS.H2.sghard α k θ := by
      simp only [Spaces.Dz]
      ring
    rw [hzeq, abs_mul, abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg hw2,
      Yz_sq_eq α g k hθ]
    have h2 : |Spaces.Dz (Work.FTS.H2.Thard g k) z θ| * |Work.FTS.H2.Thard g k z θ|
        ≤ (Spaces.Dz (Work.FTS.H2.Thard g k) z θ) ^ 2
          + (Work.FTS.H2.Thard g k z θ) ^ 2 := by
      rw [← sq_abs (Spaces.Dz (Work.FTS.H2.Thard g k) z θ),
        ← sq_abs (Work.FTS.H2.Thard g k z θ)]
      nlinarith [sq_nonneg (|Spaces.Dz (Work.FTS.H2.Thard g k) z θ|
        - |Work.FTS.H2.Thard g k z θ|)]
    have h3 : |Spaces.Dz (Work.FTS.H2.Thard g k) z θ| * |Work.FTS.H2.Thard g k z θ|
          * (Work.FTS.H2.sghard α k θ * (Work.Spaces.w z) ^ 2)
        ≤ (Spaces.Dz (Work.FTS.H2.Thard g k) z θ) ^ 2
            * (Work.FTS.H2.sghard α k θ * (Work.Spaces.w z) ^ 2)
          + (Work.FTS.H2.Thard g k z θ) ^ 2
            * (Work.FTS.H2.sghard α k θ * (Work.Spaces.w z) ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_right h2 (mul_nonneg hs hw2)
      linarith [hmul]
    linarith [h3]
  have hH : Work.FTS.H2.Hhard α f g z θ
      = f z θ * ∑ k : Fin 5, (z * (Spaces.pz (Work.FTS.H2.Thard g k) z θ
          * Work.FTS.H2.Thard g k z θ * (Work.Spaces.w z) ^ 2
          * Work.FTS.H2.sghard α k θ)) := by
    rw [Work.FTS.H2.Hhard, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hmain : |Work.FTS.H2.Hhard α f g z θ|
      ≤ M * ∑ k : Fin 5, (Work.FTS.H2.Thard g k z θ ^ 2 * Work.FTS.H2.sghard α k θ
            * (Work.Spaces.w z) ^ 2 + (Work.FTS.TransportS.Yz α g k z θ) ^ 2) := by
    rw [hH, abs_mul]
    calc |f z θ| * |∑ k : Fin 5, (z * (Spaces.pz (Work.FTS.H2.Thard g k) z θ
              * Work.FTS.H2.Thard g k z θ * (Work.Spaces.w z) ^ 2
              * Work.FTS.H2.sghard α k θ))|
        ≤ |f z θ| * ∑ k : Fin 5,
            |z * (Spaces.pz (Work.FTS.H2.Thard g k) z θ * Work.FTS.H2.Thard g k z θ
              * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.sghard α k θ)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
      _ ≤ |f z θ| * ∑ k : Fin 5,
            (Work.FTS.H2.Thard g k z θ ^ 2 * Work.FTS.H2.sghard α k θ
              * (Work.Spaces.w z) ^ 2 + (Work.FTS.TransportS.Yz α g k z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hterm k) (abs_nonneg _)
      _ ≤ M * ∑ k : Fin 5,
            (Work.FTS.H2.Thard g k z θ ^ 2 * Work.FTS.H2.sghard α k θ
              * (Work.Spaces.w z) ^ 2 + (Work.FTS.TransportS.Yz α g k z θ) ^ 2) :=
          mul_le_mul_of_nonneg_right hf
            (Finset.sum_nonneg fun k _ => add_nonneg
              (mul_nonneg (mul_nonneg (sq_nonneg _) (Work.FTS.H2.sghard_nonneg α k hθ)) hw2)
              (sq_nonneg _))
  refine le_trans hmain (mul_le_mul_of_nonneg_left ?_ hM)
  refine le_of_eq ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Work.FTS.H2.ZU]
  ring

end Work.FTS.TransportS.T3BadAux
