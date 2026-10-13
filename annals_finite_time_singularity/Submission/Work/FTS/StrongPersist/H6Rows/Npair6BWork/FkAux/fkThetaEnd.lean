/-
Copyright: work module for the Elgindi finite-time singularity project.

# `fkThetaEnd` — the closed `(FK f)·D_θf` slot estimate for a bounded radial multiplier

* `fk_end_bound` — the `g`-form of `Work.FTS.StrongPersist.H6Pair6Aux.end_bound_fts`: after the
  angular integration by parts, the pairing is dominated by `A·HkSq α 6 f` when `|g| ≤ A`;
* `fk_radial_shift` — the assembled estimate: for a radial multiplier `g` which is continuous on
  `(0,∞)` and bounded by `A`, the shifted `θ`-slot pairing is `≤ A·HkSq α 6 f`.  This is the
  `g`-form of `Work.FTS.StrongPersist.H6Pair6Aux.L12ShiftThetaLe` (the case `g = L₁₂ f`), needed
  here because the multiplier of the target is the angular moment `FK f`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaAux
import Submission.Work.FTS.CoercivityFix.Coer1.thetaIBP
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12ShiftThetaAux
import Submission.Work.FTS.StrongPersist.H6Aux.wip_Dth_ibp
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg_closed
import Submission.Work.Construction.Basic
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_avg_le
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.n5Bound
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option maxHeartbeats 1600000
/-! ## The remaining one-dimensional estimate -/

/-- **The `g`-form of `end_bound_fts`.**  After the angular integration by parts the pairing
reduces to `(q-1)·∫_z (g z·w(z)²)·∫_θ cos(2θ)σ^{-q}·h²` with `h = D_z^bD_θ^af`; since
`|q-1| ≤ 1`, `|cos| ≤ 1` and `|g z| ≤ A`, it is dominated by `A·∫∫ρ·h² ≤ A·HkSq α 6 f`
(`leaf_slot_le6`). -/
theorem fk_end_bound {α : ℝ} {f : ℝ → ℝ → ℝ} {a b : ℕ} {q A : ℝ} (g : ℝ → ℝ)
    (hα : 0 < α) (hmem6 : Work.Spaces.HkMem α 6 f) (hab : a + b ≤ 6)
    (hqabs : |q - 1| ≤ 1) (hA : 0 ≤ A) (hgA : ∀ z : ℝ, 0 < z → |g z| ≤ A)
    (hleaf : Work.FTS.TransportS.IsLeafW α a
      (fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
    (hout : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iz)
    (hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ) :
    |(q - 1) * (∫ z in Work.Spaces.Iz,
        (g z * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2))|
      ≤ A * Work.Spaces.HkSq α 6 f := by
  have hsnn : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ Real.sin (2 * θ) :=
    (Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ).mono fun θ hθ =>
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))
  have hinner_le : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      |∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2|
        ≤ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2 := by
    filter_upwards [hslice] with z hz
    refine (MeasureTheory.abs_integral_le_integral_abs).trans ?_
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) hz ?_
    filter_upwards [hsnn] with θ hθ
    have hσ : 0 ≤ (Real.sin (2 * θ)) ^ (-q) := Real.rpow_nonneg hθ _
    have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    have h2 : |(Real.sin (2 * θ)) ^ (-q)| = (Real.sin (2 * θ)) ^ (-q) := abs_of_nonneg hσ
    have h3 : |(Work.Spaces.mixed b a f z θ) ^ 2|
        = (Work.Spaces.mixed b a f z θ) ^ 2 := abs_of_nonneg (sq_nonneg _)
    rw [abs_mul, abs_mul, h2, h3]
    calc (|Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-q))
          * (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ (1 * (Real.sin (2 * θ)) ^ (-q))
          * (Work.Spaces.mixed b a f z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcos hσ) (sq_nonneg _)
      _ = (Real.sin (2 * θ)) ^ (-q) * (Work.Spaces.mixed b a f z θ) ^ 2 := by ring
  have hmaj_le : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      |(g z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2)|
        ≤ A * ((Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by
    filter_upwards [hinner_le, fkTheta_ae_pos] with z hzin hzp
    have hDnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
        * (Work.Spaces.mixed b a f z θ) ^ 2 := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [hsnn] with θ hθ
      exact mul_nonneg (Real.rpow_nonneg hθ _) (sq_nonneg _)
    have hW2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    calc |(g z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2)|
        = |g z| * (Work.Spaces.w z) ^ 2
          * |∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hW2]
      _ ≤ A * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by
          refine mul_le_mul (mul_le_mul (hgA z hzp) le_rfl (sq_nonneg _) hA) hzin
            (abs_nonneg _) (mul_nonneg hA hW2)
      _ = A * ((Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by ring
  have hmaj : MeasureTheory.IntegrableOn (fun z => A
      * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
        * (Work.Spaces.mixed b a f z θ) ^ 2)) Work.Spaces.Iz :=
    hout.const_mul A
  have htarget : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            * (Work.Spaces.mixed b a f z θ) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
          * (Work.Spaces.mixed b a f z θ) ^ 2
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
  have hleafslab := Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6 hα hmem6 a b
    (fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) hab hleaf
  calc |(q - 1) * (∫ z in Work.Spaces.Iz,
        (g z * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2))|
      = |q - 1| * |∫ z in Work.Spaces.Iz,
          (g z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
              * (Work.Spaces.mixed b a f z θ) ^ 2)| := by rw [abs_mul]
    _ ≤ 1 * |∫ z in Work.Spaces.Iz,
          (g z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
              * (Work.Spaces.mixed b a f z θ) ^ 2)| :=
        mul_le_mul_of_nonneg_right hqabs (abs_nonneg _)
    _ = |∫ z in Work.Spaces.Iz,
          (g z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
              * (Work.Spaces.mixed b a f z θ) ^ 2)| := one_mul _
    _ ≤ ∫ z in Work.Spaces.Iz,
        |(g z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
              * (Work.Spaces.mixed b a f z θ) ^ 2)| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ z in Work.Spaces.Iz, A * ((Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => abs_nonneg _) hmaj hmaj_le
    _ = A * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by
        rw [MeasureTheory.integral_const_mul]
    _ = A * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by rw [htarget]
    _ ≤ A * Work.Spaces.HkSq α 6 f := mul_le_mul_of_nonneg_left hleafslab hA

/-! ## The general radial-multiplier estimate -/

/-- **The `g`-form of `L12ShiftThetaLe`**: for an arbitrary radial multiplier `g` which is
continuous on `(0,∞)` and bounded by `A` there, the shifted `θ`-slot pairing is bounded by
`A·HkSq α 6 f`.  The proof is the angular integration by parts of the two `σ^{-q}D_θh·h`-slots
(which is why the level-`7` slot `D_θh` never has to be priced). -/
theorem fk_radial_shift : ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {f : ℝ → ℝ → ℝ} {A : ℝ},
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.Spaces.HkMem α 7 f →
    ∀ (g : ℝ → ℝ), ContinuousOn g (Set.Ioi 0) → 0 ≤ A →
      (∀ z : ℝ, 0 < z → |g z| ≤ A) →
      ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
        |∫ z in Work.Spaces.Iz, g z *
            (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b (a + 1) f z θ
              * Work.Spaces.mixed b a f z θ)|
          ≤ C * A * Work.Spaces.HkSq α 6 f := by
  refine ⟨1, one_pos, ?_⟩
  intro α f A hα hα1 hO hmem6 hmem7 g hgc hA hgA a b ρ hab hρ
  simp only [one_mul]
  have main : ∀ (q : ℝ) (ρ : ℝ → ℝ → ℝ),
      |q - 1| ≤ 1 → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
      ρ = (fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) →
      Work.FTS.TransportS.IsLeafW α a ρ →
      |∫ z in Work.Spaces.Iz, g z *
          (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b (a + 1) f z θ
            * Work.Spaces.mixed b a f z θ)|
        ≤ A * Work.Spaces.HkSq α 6 f := by
    intro q ρ hqabs hqle hq0 hρq hρlem
    subst hρq
    obtain ⟨hi0, hi1, hi2, hout, hslice⟩ :=
      fk_ibp_integrable (f := f) g hα hA hgc hgA hO hmem6 hmem7 hab hqle hq0
    -- Step A: pull the radial weight `(w z)²` out of the angular integral.
    have hAint : ∀ z : ℝ,
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
          = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ := by
      intro z
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
    have hA' : (∫ z in Work.Spaces.Iz, g z *
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ))
        = ∫ z in Work.Spaces.Iz,
            (g z * (Work.Spaces.w z) ^ 2) *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show g z *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
          = (g z * (Work.Spaces.w z) ^ 2) *
            (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
      rw [hAint z]
      ring
    -- Step B: replace `D_z^bD_θ^{a+1}f` by `D_θ(D_z^bD_θ^a f)` inside the angular integral.
    have hB : (∫ z in Work.Spaces.Iz,
            (g z * (Work.Spaces.w z) ^ 2) *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ))
        = ∫ z in Work.Spaces.Iz,
            (g z * (Work.Spaces.w z) ^ 2) *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [fkTheta_ae_pos] with z hz
      have hinner : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
          = (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ] with θ hθ
        have h2 := Work.FTS.StrongPersist.H6Pair6Aux.dth_mixed_eqOn_Q0 (f := f) hO a b
          (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz, hθ.1, hθ.2⟩)
        have h1 : Work.Spaces.mixed b (a + 1) f z θ
            = Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ := h2.symm
        rw [h1]
      show (g z * (Work.Spaces.w z) ^ 2) *
            (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
          = (g z * (Work.Spaces.w z) ^ 2) *
            (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ)
      rw [hinner]
    -- Step C: identify the iterated integral with the `ρ`-weighted pairing `wip`.
    have hC : (∫ z in Work.Spaces.Iz,
            (g z * (Work.Spaces.w z) ^ 2) *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ))
        = Work.Coercivity.wip
            (fun z θ => (g z * (Work.Spaces.w z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-q))
            (Work.Spaces.Dth (fun z θ => Work.Spaces.mixed b a f z θ))
            (fun z θ => Work.Spaces.mixed b a f z θ) := by
      rw [Work.Coercivity.wip]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show (g z * (Work.Spaces.w z) ^ 2) *
            (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ)
          = ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.Dth (fun z θ => Work.Spaces.mixed b a f z θ) z θ
              * (fun z θ => Work.Spaces.mixed b a f z θ) z θ
              * ((g z * (Work.Spaces.w z) ^ 2)
                * (Real.sin (2 * θ)) ^ (-q))
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
    -- The angular integration by parts.
    have hIBP := Work.FTS.StrongPersist.H6Aux.wip_Dth_ibp
        (h := fun z θ => Work.Spaces.mixed b a f z θ)
        (Φ := fun z => g z * (Work.Spaces.w z) ^ 2) (q := q)
        (hO.mixed b a) hi0 hi1 hi2
    rw [hA', hB, hC, hIBP]
    -- The remaining one-dimensional estimate.
    exact fk_end_bound (f := f) g hα hmem6 hab hqabs hA hgA hρlem hout hslice
  rcases hρ with hρ | hρ | ⟨ha1, hρ⟩
  · -- `ρ = w²σ^{-η}`
    subst hρ
    exact main Work.Spaces.eta Work.FTS.TransportS.leafEta
      (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta, Work.Spaces.gam]; linarith) (fun _ => le_rfl) rfl (Or.inl rfl)
  · -- `ρ = w²`
    subst hρ
    refine main 0 Work.FTS.TransportS.leafOne ?_ (by rw [Work.Spaces.gam]; linarith)
      (fun _ => by rw [Work.Spaces.eta]; norm_num) ?_ (Or.inr (Or.inl rfl))
    · rw [zero_sub, abs_neg, abs_one]
    · funext z θ
      simp [Work.FTS.TransportS.leafOne, Real.rpow_zero]
  · -- `ρ = w²σ^{-γ}` (only for `a ≥ 1`)
    subst hρ
    refine main (Work.Spaces.gam α) (Work.FTS.TransportS.leafGam α) ?_ le_rfl ?_ rfl
      (Or.inr (Or.inr ⟨ha1, rfl⟩))
    · rw [Work.Spaces.gam_sub_one, abs_of_nonneg (by linarith : (0 : ℝ) ≤ α / 10)]
      linarith
    · intro ha0; omega

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
