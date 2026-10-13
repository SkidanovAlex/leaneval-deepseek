/- 
Copyright: work module for the Elgindi finite-time singularity project.

# `TT.aShiftSlotAux` — the `(1,1)`-slot of `A = z²∂_z²Ψ` in the `ℋ²`-norm

Elementary (no analysis) facts about the slot `mixed 1 1 A · Wt α` whose bound is the target of
`Work.FTS.EllipticEst.TT.aShiftSlot_le`, together with the reduction of that target to the
analytic inputs `interpGamma`, `aeLtwoBound`, `aeDzNorm`, `aeStep2`, `aeStep3`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.Honest.HkSqAssembly
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.Level0ADefs
import Submission.Work.FTS.EllipticEst.H2W.AeDataAof

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem slot11_eq (A : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 1 1 A z θ
      = Real.sin (2 * θ) * Work.Spaces.Dz (Work.Spaces.pth A) z θ := by
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
    Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.Dth, Work.Spaces.Dz,
    Work.Spaces.pth, Work.Spaces.pz]
  rw [deriv_const_mul_field]
  ring

/-- `(s^a)² = s^{2a}` for `s ≥ 0`. -/
theorem rpow_sq_eq {s a : ℝ} (hs : 0 ≤ s) : (s ^ a) ^ (2 : ℕ) = s ^ (2 * a) := by
  rw [← Real.rpow_natCast (s ^ a) 2, ← Real.rpow_mul hs]
  ring_nf

/-- `s² · s^{-γ} = s^{2-γ}` for `s ≥ 0` and `2 - γ ≠ 0`. -/
theorem sq_mul_rpow_neg {s γ : ℝ} (hs : 0 ≤ s) (h2 : (2 : ℝ) - γ ≠ 0) :
    s ^ (2 : ℝ) * s ^ (-γ) = s ^ (2 - γ) := by
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h]
    by_cases hγ : γ = 0
    · subst hγ
      rw [show (-(0 : ℝ)) = 0 by norm_num, Real.rpow_zero, mul_one,
        Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0),
        Real.zero_rpow (by norm_num : (2 : ℝ) - 0 ≠ 0)]
    · rw [Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0),
        Real.zero_rpow (by simpa using hγ), zero_mul, Real.zero_rpow h2]
  · rw [← Real.rpow_add h]
    ring_nf

/-- **The pointwise weight identity of the slot.** -/
theorem slot11_sq_eq (α : ℝ) (A : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.mixed 1 1 A z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.Dz (Work.Spaces.pth A) z θ
          * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) / 2) * Work.Spaces.w z) ^ 2 := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [slot11_eq, Work.Spaces.Wt, Work.Spaces.wTheta]
  have h1 : (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ (2 : ℕ)
      = Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
    rw [rpow_sq_eq hs]
    ring_nf
  have h2 : (Real.sin (2 * θ) ^ ((2 - Work.Spaces.gam α) / 2)) ^ (2 : ℕ)
      = Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) := by
    rw [rpow_sq_eq hs]
    ring_nf
  have hgam2 : (2 : ℝ) - Work.Spaces.gam α ≠ 0 := by
    rw [Work.Spaces.gam]
    intro hc
    linarith
  have h3 : Real.sin (2 * θ) ^ (2 : ℕ)
        * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
      = Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) := by
    rw [← Real.rpow_natCast (Real.sin (2 * θ)) 2]
    exact sq_mul_rpow_neg hs hgam2
  calc (Real.sin (2 * θ) * Work.Spaces.Dz (Work.Spaces.pth A) z θ
        * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
      = Real.sin (2 * θ) ^ (2 : ℕ) * (Work.Spaces.Dz (Work.Spaces.pth A) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ (2 : ℕ) := by
        ring
    _ = Real.sin (2 * θ) ^ (2 : ℕ) * (Work.Spaces.Dz (Work.Spaces.pth A) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by rw [h1]
    _ = Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
          * (Work.Spaces.Dz (Work.Spaces.pth A) z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by
        rw [← h3]; ring
    _ = (Work.Spaces.Dz (Work.Spaces.pth A) z θ
          * Real.sin (2 * θ) ^ ((2 - Work.Spaces.gam α) / 2) * Work.Spaces.w z) ^ 2 := by
        rw [← h2]; ring

/-- **The `L²`-square of the slot.** -/
theorem L2Sq_slot11_eq (α : ℝ) (A : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 1 1 A z θ * Work.Spaces.Wt α z θ)
      = Work.Spaces.L2Sq (fun z θ => Work.Spaces.Dz (Work.Spaces.pth A) z θ
          * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) / 2) * Work.Spaces.w z) := by
  rw [Work.Spaces.L2Sq, Work.Spaces.L2Sq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  exact slot11_sq_eq α A hα hα4 hθ

/-- The zero function is honest in `ℋ⁰`. -/
theorem HkMem_zero_fun (α : ℝ) : Work.Spaces.HkMem α 0 (fun _ _ : ℝ => (0 : ℝ)) := by
  refine ⟨fun z _ => ?_, ?_⟩
  · have hz : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 (fun _ _ : ℝ => (0 : ℝ)) z θ)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
      ring
    rw [hz]
    exact integrableOn_zero
  · have hz : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun _ _ : ℝ => (0 : ℝ)) z θ) = fun _ : ℝ => (0 : ℝ) := by
      funext z
      have h1 : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 (fun _ _ : ℝ => (0 : ℝ)) z θ)
          = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
        ring
      rw [h1, integral_zero]
    rw [hz]
    exact integrableOn_zero

/-- The level-`0` `ℋ`-square is the `L²`-square against the level-`0` weight. -/
theorem HkSq_zero_eq_L2Sq (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g = Work.Spaces.L2Sq (fun z θ => g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) := by
  rw [Work.Spaces.HkSq, Work.Spaces.L2Sq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]

/-- The level-`0` `ℋ`-square of the zero function vanishes. -/
theorem HkSq_zero_fun (α : ℝ) : Work.Spaces.HkSq α 0 (fun _ _ : ℝ => (0 : ℝ)) = 0 := by
  rw [Work.Spaces.HkSq]
  have h : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun _ _ : ℝ => (0 : ℝ)) z θ) = 0 := by
    intro z
    have h1 : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 (fun _ _ : ℝ => (0 : ℝ)) z θ)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
      ring
    rw [h1, integral_zero]
  simp only [h, integral_zero]



/-! ## The `D_z²` slot split and the source slot, for the `Aof`/`Gof` datum -/

end Work.FTS.EllipticEst.TT
open Work.FTS.EllipticEst.H2W

namespace Work.FTS.EllipticEst.TT

/-- Generic five-term domination of the level-`0` integrand by an absolute-value bound. -/
theorem HkIntegrand_zero_le_five_abs {α : ℝ} {u g1 g2 g3 g4 g5 : ℝ → ℝ → ℝ}
    (h : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |u z θ| ≤ |g1 z θ| + |g2 z θ| + |g3 z θ| + |g4 z θ| + |g5 z θ|) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 u z θ
        ≤ 5 * (Work.Spaces.HkIntegrand α 0 g1 z θ + Work.Spaces.HkIntegrand α 0 g2 z θ
          + Work.Spaces.HkIntegrand α 0 g3 z θ + Work.Spaces.HkIntegrand α 0 g4 z θ
          + Work.Spaces.HkIntegrand α 0 g5 z θ) :=
  Work.FTS.EllipticEst.Honest.HkIntegrand_zero_le_five h

/-- **`D_z²` slot split.**  `HkSq α 0 (D_z²(Aof Ψ))` is controlled by the two level-`0` slots
`z²∂_z²(Aof Ψ)` and `D_z(Aof Ψ)` (with the harmless constant `20 = 5·4`). -/
theorem HkSq_zero_DzIter_two_le (α : ℝ) {Ψ : ℝ → ℝ → ℝ}
    (hAsm : Work.FTS.EllipticEst.SmoothOpen (Aof Ψ))
    (hM2 : Work.Spaces.HkMem α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Aof Ψ) z θ))
    (hM1 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 (Aof Ψ))) :
    Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Aof Ψ))
      ≤ 20 * (Work.Spaces.HkSq α 0
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Aof Ψ) z θ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Aof Ψ))) := by
  have habs : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter 2 (Aof Ψ) z θ|
        ≤ |z ^ 2 * Work.Spaces.pzIter 2 (Aof Ψ) z θ|
          + |Work.Spaces.DzIter 1 (Aof Ψ) z θ| + |Work.Spaces.DzIter 1 (Aof Ψ) z θ|
          + |Work.Spaces.DzIter 1 (Aof Ψ) z θ| + |Work.Spaces.DzIter 1 (Aof Ψ) z θ| := by
    intro z hz θ hθ hθ2
    have hsplit := Work.FTS.EllipticEst.H2W.AeDataAofAux.zsq_pzIter2_eq_open hAsm hz ⟨hθ, hθ2⟩
    have hval : Work.Spaces.DzIter 2 (Aof Ψ) z θ
        = z ^ 2 * Work.Spaces.pzIter 2 (Aof Ψ) z θ + Work.Spaces.DzIter 1 (Aof Ψ) z θ := by
      linarith [hsplit]
    rw [hval]
    have h1 : |z ^ 2 * Work.Spaces.pzIter 2 (Aof Ψ) z θ + Work.Spaces.DzIter 1 (Aof Ψ) z θ|
        ≤ |z ^ 2 * Work.Spaces.pzIter 2 (Aof Ψ) z θ|
          + |Work.Spaces.DzIter 1 (Aof Ψ) z θ| := abs_add_le _ _
    have h2 : 0 ≤ |Work.Spaces.DzIter 1 (Aof Ψ) z θ| := abs_nonneg _
    linarith
  have hpt := HkIntegrand_zero_le_five_abs (α := α) (u := Work.Spaces.DzIter 2 (Aof Ψ))
    (g1 := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Aof Ψ) z θ)
    (g2 := Work.Spaces.DzIter 1 (Aof Ψ)) (g3 := Work.Spaces.DzIter 1 (Aof Ψ))
    (g4 := Work.Spaces.DzIter 1 (Aof Ψ)) (g5 := Work.Spaces.DzIter 1 (Aof Ψ)) habs
  have hfive := Work.FTS.EllipticEst.Honest.HkSq_zero_le_sum_five
    (α := α) (f := Work.Spaces.DzIter 2 (Aof Ψ))
    (g1 := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Aof Ψ) z θ)
    (g2 := Work.Spaces.DzIter 1 (Aof Ψ)) (g3 := Work.Spaces.DzIter 1 (Aof Ψ))
    (g4 := Work.Spaces.DzIter 1 (Aof Ψ)) (g5 := Work.Spaces.DzIter 1 (Aof Ψ))
    (C := 5) (by norm_num) hM2 hM1 hM1 hM1 hM1 hpt
  refine hfive.trans ?_
  have hnn : 0 ≤ Work.Spaces.HkSq α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Aof Ψ) z θ) :=
    Work.Spaces.HkSq_nonneg α 0 _
  linarith

/-- **The source slot.**  `HkSq α 0 (Gof F) ≤ 80 HkSq α 2 F`. -/
theorem HkSq_zero_Gof_le (α : ℝ) {F : ℝ → ℝ → ℝ} (hFsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hF : Work.Spaces.HkMem α 2 F) :
    Work.Spaces.HkSq α 0 (Gof F) ≤ 80 * Work.Spaces.HkSq α 2 F := by
  have hM2 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 F) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 2 F
      ((hFsm.DzIter 2).continuousOn) hF le_rfl
  have hM1 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 F) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 1 F
      ((hFsm.DzIter 1).continuousOn) hF (by norm_num)
  have habs : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Gof F z θ| ≤ |Work.Spaces.DzIter 2 F z θ| + |Work.Spaces.DzIter 1 F z θ|
        + |Work.Spaces.DzIter 1 F z θ| + |Work.Spaces.DzIter 1 F z θ|
        + |Work.Spaces.DzIter 1 F z θ| := by
    intro z _ θ _ _
    have h := abs_add_le (Work.Spaces.DzIter 2 F z θ) (-(Work.Spaces.DzIter 1 F z θ))
    have hb := abs_nonneg (Work.Spaces.DzIter 1 F z θ)
    have h1 : |Gof F z θ| ≤ |Work.Spaces.DzIter 2 F z θ| + |Work.Spaces.DzIter 1 F z θ| := by
      simpa only [Gof, sub_eq_add_neg, abs_neg] using h
    linarith
  have hpt := HkIntegrand_zero_le_five_abs (α := α) (u := Gof F)
    (g1 := Work.Spaces.DzIter 2 F) (g2 := Work.Spaces.DzIter 1 F)
    (g3 := Work.Spaces.DzIter 1 F) (g4 := Work.Spaces.DzIter 1 F)
    (g5 := Work.Spaces.DzIter 1 F) habs
  have hfive := Work.FTS.EllipticEst.Honest.HkSq_zero_le_sum_five
    (α := α) (f := Gof F) (g1 := Work.Spaces.DzIter 2 F) (g2 := Work.Spaces.DzIter 1 F)
    (g3 := Work.Spaces.DzIter 1 F) (g4 := Work.Spaces.DzIter 1 F)
    (g5 := Work.Spaces.DzIter 1 F) (C := 5) (by norm_num) hM2 hM1 hM1 hM1 hM1 hpt
  refine hfive.trans ?_
  have h2 : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 F) ≤ Work.Spaces.HkSq α 2 F := by
    rw [HkSq_zero_eq_L2Sq]
    exact Work.Spaces.L2Sq_DzIter_le_HkSq α 2 F hF 2 le_rfl
  have h1 : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 F) ≤ Work.Spaces.HkSq α 2 F := by
    rw [HkSq_zero_eq_L2Sq]
    exact Work.Spaces.L2Sq_DzIter_le_HkSq α 2 F hF 1 (by norm_num)
  have hnn2 := Work.Spaces.HkSq_nonneg α 0 (Work.Spaces.DzIter 2 F)
  have hnn1 := Work.Spaces.HkSq_nonneg α 0 (Work.Spaces.DzIter 1 F)
  linarith

end Work.FTS.EllipticEst.TT

open Work.FTS.EllipticEst.H2W

namespace Work.FTS.EllipticEst.TT

abbrev nr := Work.FTS.EllipticEst.H2W.Ae.nrm

/-- **The assembly of the `(1,1)`-slot bound** (reduced form).  Given the mixed interpolation
`hI` for the datum `Aof Ψ`, the level-`0`  core bound `hcore` and the source bound `hGof`, the
target of `Work.FTS.EllipticEst.TT.aShiftSlot_le` follows. -/
theorem aShiftSlot_step {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {F Ψ : ℝ → ℝ → ℝ}
    {C₅ M : ℝ} (hC₅ : 0 < C₅) (hM : 0 ≤ M)
    (hI : α ^ 4 * Work.Spaces.L2Sq (fun z θ => Work.Spaces.Dz (Work.Spaces.pth (Aof Ψ)) z θ
            * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) / 2) * Work.Spaces.w z)
        ≤ C₅ * α ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Aof Ψ))
            + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aof Ψ))
            + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Aof Ψ))))
    (hcore : α ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Aof Ψ))
            + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aof Ψ))
            + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Aof Ψ)))
        ≤ M * Work.Spaces.HkSq α 0 (Gof F))
    (hGof : Work.Spaces.HkSq α 0 (Gof F) ≤ 80 * Work.Spaces.HkSq α 2 F) :
    α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.mixed 1 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          * Work.Spaces.Wt α z θ)
      ≤ (8000 * C₅ * M + 1) * Work.Spaces.HkSq α 2 F := by
  rw [L2Sq_slot11_eq α (Aof Ψ) hα hα4]
  set B : ℝ := α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Aof Ψ))
      + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aof Ψ))
      + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Aof Ψ)) with hB
  have hcore' : α ^ 2 * B ≤ M * Work.Spaces.HkSq α 0 (Gof F) := by rw [hB]; exact hcore
  have hBnn : 0 ≤ B := by
    rw [hB]
    have h1 : 0 ≤ Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Aof Ψ)) :=
      Work.Spaces.HkSq_nonneg α 0 _
    have h2 : 0 ≤ Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aof Ψ)) :=
      Work.Spaces.HkSq_nonneg α 0 _
    have h3 : 0 ≤ Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Aof Ψ)) :=
      Work.Spaces.HkSq_nonneg α 0 _
    have hα2 : 0 ≤ α ^ 2 := sq_nonneg α
    have hα4 : 0 ≤ α ^ 4 := by positivity
    nlinarith [h1, h2, h3, hα2, hα4]
  have hGnn : 0 ≤ Work.Spaces.HkSq α 0 (Gof F) := Work.Spaces.HkSq_nonneg α 0 (Gof F)
  have hHnn : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have hC₅0 : 0 ≤ C₅ := hC₅.le
  have hM0 : 0 ≤ M := hM
  have hstep : C₅ * α ^ 2 * B ≤ C₅ * (M * Work.Spaces.HkSq α 0 (Gof F)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hcore' hC₅0
  have hstep2 : C₅ * (M * Work.Spaces.HkSq α 0 (Gof F))
      ≤ C₅ * (M * (80 * Work.Spaces.HkSq α 2 F)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGof hM) hC₅0
  have hstep3 : C₅ * (M * (80 * Work.Spaces.HkSq α 2 F))
      ≤ (8000 * C₅ * M + 1) * Work.Spaces.HkSq α 2 F := by
    have hcm : 0 ≤ C₅ * M * Work.Spaces.HkSq α 2 F := mul_nonneg (mul_nonneg hC₅0 hM0) hHnn
    nlinarith [hcm, hHnn]
  exact hI.trans (hstep.trans (hstep2.trans hstep3))

end Work.FTS.EllipticEst.TT
