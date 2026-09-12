import Mathlib
import Submission.Work.Lattice.MaxNormFlow
import Submission.Work.Lattice.FlowRateSubspace
import Submission.Work.Lattice.PositionData

/-!
# The flow bound with no constant factor (top-block eigenvalue)

`Submission.FlowRate` proves `‖⋀^k a_h w‖ ≤ (k+1)·e^{h·σ_top}·‖w‖` (a `(k+1)`-loss from the
triangle inequality).  For the *differentiation* argument of §3 one needs the sharp form

    `‖⋀^k a_h w‖ ≤ e^{h·σ_top} · ‖w‖`,   `h ≥ 0`,

where `σ_top = σ_{topBlockIndex ℓ w}` is the eigenvalue of the top nonvanishing block.  The loss
is avoidable because the blocks are *orthogonal*: Pythagoras
(`Submission.ExteriorCoordinates.sum_normSq_blockElem`) turns the triangle inequality into the
sum `Σ_u (eigen_u ‖block_u w‖)²`, and every present block has `eigen_u ≤ eigen_top`
(`Submission.FlowRate.eigen_mono`).

Consequences recorded here:

* `norm_map_twoScale_le_eigen_top` — the two-scale form;
* `norm_map_eFlow_le_exp_top` — the exponential flow `a_h`, `h ≥ 0`;
* `norm_map_eFlow_iMulti_le_exp_sig` — for `w = ιMulti ℝ j b` the top block index is
  `j − finrank (span b ⊓ L)` (`Submission.TopBlockIndex`), so the bound reads
  `‖⋀^j a_h (ιMulti b)‖ ≤ e^{h·σ_{j−ω}}·‖ιMulti b‖` with `σ_u = sig d j ℓ u`, i.e. the flow rate
  of the *position* `ω = finrank (span b ⊓ L)`.

Module `Submission.Work.Lattice.FlowRateUniform`, namespace `Submission.FlowRateUniform`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks
open Submission.MaxNormFlow
open Submission.FlowRate
open Submission.FlowRateAsymptotic
open Submission.TopBlockIndex
open Submission.PositionData

namespace Submission.FlowRateUniform

variable {d : ℕ}

/-- **The sharp flow bound.**  If `u` is the top nonvanishing block of `w ≠ 0` and
`0 < a ≤ b`, then the two-scale diagonal flow satisfies
`‖⋀^k (twoScale a b ℓ) w‖ ≤ (a^(k-u)·b^u)·‖w‖`. -/
theorem norm_map_twoScale_le_eigen_top {k ℓ : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {w : WK d k} (hw : w ≠ 0) :
    ‖exteriorPower.map k (scaleMap (twoScale a b ℓ)) w‖ ≤
      (a ^ (k - topBlockIndex (d := d) ℓ w) * b ^ (topBlockIndex (d := d) ℓ w)) * ‖w‖ := by
  classical
  have hb : 0 ≤ b := le_trans (le_of_lt ha) hab
  set u : ℕ := topBlockIndex (d := d) ℓ w with hu
  have huk : u ≤ k := topBlockIndex_le (d := d) ℓ w
  have htop := isTopBlock_topBlockIndex (d := d) (ℓ := ℓ) w hw
  have hE0 : 0 ≤ a ^ (k - u) * b ^ u := mul_nonneg (pow_nonneg (le_of_lt ha) _) (pow_nonneg hb _)
  -- step 1: Pythagoras for the flowed vector
  have hstep1 : ‖exteriorPower.map k (scaleMap (twoScale a b ℓ)) w‖ ^ 2 =
      ∑ v ∈ Finset.range (k + 1),
        ((a ^ (k - v) * b ^ v) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) ^ 2 := by
    rw [← sum_normSq_blockElem (d := d) (k := k) (ℓ := ℓ)
      (exteriorPower.map k (scaleMap (twoScale a b ℓ)) w)]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    have hvk : v ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hv)
    rw [norm_blockElem_map_twoScale (d := d) (k := k) (ℓ := ℓ) (a := a) (b := b) (w := w)
      (j := v) hvk (le_of_lt ha) hb]
  -- step 2: each term is bounded by `eigen_u² ‖block_v w‖²`
  have hstep2 : ∑ v ∈ Finset.range (k + 1),
        ((a ^ (k - v) * b ^ v) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) ^ 2 ≤
      ∑ v ∈ Finset.range (k + 1),
        (a ^ (k - u) * b ^ u) ^ 2 * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖ ^ 2 := by
    refine Finset.sum_le_sum (fun v hv => ?_)
    have hvk : v ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hv)
    by_cases hvle : v ≤ u
    · have he : a ^ (k - v) * b ^ v ≤ a ^ (k - u) * b ^ u :=
        eigen_mono (k := k) (u := u) (u' := v) ha hab hvle huk
      have h1 : ((a ^ (k - v) * b ^ v) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) ^ 2 ≤
          ((a ^ (k - u) * b ^ u) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) ^ 2 := by
        have h1' := mul_le_mul_of_nonneg_right he (norm_nonneg
          (blockElem (d := d) (k := k) (ℓ := ℓ) w v))
        exact pow_le_pow_left₀ (by positivity) h1' 2
      have h2 : ((a ^ (k - u) * b ^ u) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) ^ 2 =
          (a ^ (k - u) * b ^ u) ^ 2 * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖ ^ 2 := by
        ring
      rw [h2] at h1
      exact h1
    · have hvlt : u < v := lt_of_not_ge hvle
      have hz : blockElem (d := d) (k := k) (ℓ := ℓ) w v = 0 :=
        blockElem_eq_zero_of_topBlockIndex_lt (d := d) (ℓ := ℓ) w (by rw [← hu]; exact hvlt) hvk
      rw [hz, norm_zero, mul_zero]
      norm_num
  -- step 3: factor out the constant
  have hstep3 : ∑ v ∈ Finset.range (k + 1),
        (a ^ (k - u) * b ^ u) ^ 2 * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖ ^ 2 =
      (a ^ (k - u) * b ^ u) ^ 2 * ‖w‖ ^ 2 := by
    rw [← Finset.mul_sum, ← sum_normSq_blockElem (d := d) (k := k) (ℓ := ℓ) w]
  -- conclude
  have hsq : ‖exteriorPower.map k (scaleMap (twoScale a b ℓ)) w‖ ^ 2 ≤
      ((a ^ (k - u) * b ^ u) * ‖w‖) ^ 2 := by
    rw [hstep1]
    calc ∑ v ∈ Finset.range (k + 1),
          ((a ^ (k - v) * b ^ v) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) ^ 2
        ≤ ∑ v ∈ Finset.range (k + 1),
          (a ^ (k - u) * b ^ u) ^ 2 * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖ ^ 2 := hstep2
      _ = (a ^ (k - u) * b ^ u) ^ 2 * ‖w‖ ^ 2 := hstep3
      _ = ((a ^ (k - u) * b ^ u) * ‖w‖) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hE0 (norm_nonneg _))).mp hsq

/-- **The exponential-flow form.**  For the §3 flow `a_h = twoScale (e^{−h/ℓ}) (e^{h/(d−ℓ)})`
and `h ≥ 0`: `‖⋀^k a_h w‖ ≤ e^{h·σ_u}·‖w‖` with `u = topBlockIndex ℓ w`. -/
theorem norm_map_eFlow_le_exp_top {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {h : ℝ} (hh : 0 ≤ h)
    {w : WK d k} (hw : w ≠ 0) :
    ‖exteriorPower.map k
        (scaleMap (twoScale (Real.exp (-h / (ℓ : ℝ))) (Real.exp (h / ((d - ℓ : ℕ) : ℝ))) ℓ))
        w‖ ≤
      Real.exp (h * sig (d := d) k ℓ (topBlockIndex (d := d) ℓ w)) * ‖w‖ := by
  have ha : 0 < Real.exp (-h / (ℓ : ℝ)) := Real.exp_pos _
  have hb : 0 < Real.exp (h / ((d - ℓ : ℕ) : ℝ)) := Real.exp_pos _
  have hmono : Real.exp (-h / (ℓ : ℝ)) ≤ Real.exp (h / ((d - ℓ : ℕ) : ℝ)) := by
    rw [Real.exp_le_exp]
    have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
    have hdmR : (0 : ℝ) < (((d - ℓ : ℕ)) : ℝ) := by
      rw [Nat.cast_sub (le_of_lt hℓd)]
      have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
      linarith
    have h1 : -h / (ℓ : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hℓR.le
    have h2 : 0 ≤ h / ((d - ℓ : ℕ) : ℝ) := div_nonneg hh hdmR.le
    linarith
  have hmain := norm_map_twoScale_le_eigen_top (d := d) (k := k) (ℓ := ℓ) ha hmono hw
  have heigen : Real.exp (-h / (ℓ : ℝ)) ^ (k - topBlockIndex (d := d) ℓ w) *
      Real.exp (h / ((d - ℓ : ℕ) : ℝ)) ^ (topBlockIndex (d := d) ℓ w) =
      Real.exp (h * sig (d := d) k ℓ (topBlockIndex (d := d) ℓ w)) := by
    rw [eigen_exp (d := d) (k := k) (u := topBlockIndex (d := d) ℓ w) hℓ0 hℓd h]
    congr 1
    have hs : FlowRateAsymptotic.sig (d := d) k ℓ (topBlockIndex (d := d) ℓ w)
        = -((k : ℝ) / (ℓ : ℝ)) + ((topBlockIndex (d := d) ℓ w : ℕ) : ℝ) *
            (1 / (ℓ : ℝ) + 1 / ((d : ℝ) - (ℓ : ℝ))) := rfl
    rw [hs, Nat.cast_sub (topBlockIndex_le (d := d) ℓ w), Nat.cast_sub (le_of_lt hℓd)]
    ring
  rw [heigen] at hmain
  exact hmain

/-- **The flow rate of a subspace is the flow rate of its position.**  For an `ℝ`-independent
family `b` spanning `P`, the flowed wedge satisfies
`‖⋀^j a_h (ιMulti b)‖ ≤ e^{h·σ}·‖ιMulti b‖` with `σ = sigPos d j ℓ ω`,
`ω = finrank (P ⊓ modelX ℓ)` the position. -/
theorem norm_map_eFlow_iMulti_le_exp_sigPos {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {h : ℝ}
    (hh : 0 ≤ h) (P : Submodule ℝ (RD d)) (b : Fin (Module.finrank ℝ P) → RD d)
    (hb : LinearIndependent ℝ b) (hspan : Submodule.span ℝ (Set.range b) = P) :
    ‖exteriorPower.map (Module.finrank ℝ P)
        (scaleMap (twoScale (Real.exp (-h / (ℓ : ℝ))) (Real.exp (h / ((d - ℓ : ℕ) : ℝ))) ℓ))
        (exteriorPower.ιMulti ℝ (Module.finrank ℝ P) b)‖ ≤
      Real.exp (h * sigPos d (Module.finrank ℝ P) ℓ
        (Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)))) *
        ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ P) b‖ := by
  have hw : exteriorPower.ιMulti ℝ (Module.finrank ℝ P) b ≠ 0 :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent b hb
  have h := norm_map_eFlow_le_exp_top (d := d) (k := Module.finrank ℝ P) (ℓ := ℓ) hℓ0 hℓd hh hw
  have hidx := topBlockIndex_eq_sub_meetDim (d := d) (ℓ := ℓ) P b hb hspan
  rw [hidx] at h
  exact h

end Submission.FlowRateUniform

end
