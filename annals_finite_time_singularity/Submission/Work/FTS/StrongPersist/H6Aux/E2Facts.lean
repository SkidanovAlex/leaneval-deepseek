/-
# `Work.FTS.StrongPersist.H6Aux.E2Facts` — the `Ê₂`-defect of the `D_z`-commutator

`Ê₂ h = (2zh + 3z·D_θh)/(1+z)² = (z/(1+z)²)·(2h + 3D_θh)` is the explicit `D_z`-commutator
defect of the clean operator `Lhat` (`Dz (Lhat h) = Lhat (Dz h) + Ê₂ h`).  Running the
commutator induction needs the two consequences of the factorisation used in the induction
step: the *pointwise* integrand domination

  `HkIntegrand α m (Ê₂ h) z θ ≤ C · HkIntegrand α (m+1) h z θ`,

and its integrated and membership forms.  Everything is a consequence of the `z`-only
multiplier estimate `ZmulBound.zmul_open` (with the bounded-jet profile `z ↦ z/(1+z)²`,
`Zop_zdiv_bound`), the additivity of the integrand
(`EllipticEst.HkIntegrand_add_le_open`), the scaling `HkIntegrand_const_mul`, and the `D_θ`-shift
domination `HkIntegrand_Dth_le_ge`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Aux.Facts
import Submission.Work.FTS.StrongPersist.H6Aux.Zop_zdiv_bound
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.EllipticEst.HkIntegrand_add_le_open
import Submission.Work.FTS.LocData.HkIntegrand_const_mul
import Submission.Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- `Ê₂ h` as the product of the bounded radial profile `z/(1+z)²` with `2h + 3D_θh`. -/
theorem E2hat_eq_prod (h : Fn) (z θ : ℝ) :
    Work.FTS.CoercivityFix.E2hat h z θ
      = (z / (1 + z) ^ 2) * (2 * h z θ + 3 * Work.Spaces.Dth h z θ) := by
  rw [Work.FTS.CoercivityFix.E2hat_eq]
  ring

/-- The profile `z ↦ z/(1+z)²` is `C^∞` on `(-1,∞)`. -/
theorem contDiffOn_zdiv (n : ℕ) :
    ContDiffOn ℝ n (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi (-1)) := by
  have hden : ContDiffOn ℝ n (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  exact contDiffOn_id.div hden (fun z hz => by
    simp only [Set.mem_Ioi] at hz
    exact pow_ne_zero 2 (by linarith))

/-- `2h + 3D_θh` is smooth on the open quadrant whenever `h` is. -/
theorem smoothOpen_two_mul_add (h : Fn) (hs : Work.FTS.EllipticEst.SmoothOpen h) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 2 * h z θ + 3 * Work.Spaces.Dth h z θ) :=
  Work.FTS.EllipticEst.smoothOpen_add
    (Work.FTS.StrongPersist.linMem_const_mul 2 hs)
    (Work.FTS.StrongPersist.linMem_const_mul 3 (hs.Dth))

/-- `Ê₂ h` is smooth on the open quadrant whenever `h` is. -/
theorem smoothOpen_E2hat {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.CoercivityFix.E2hat h) := by
  have hprod : Work.FTS.CoercivityFix.E2hat h
      = fun z θ => (fun z : ℝ => z / (1 + z) ^ 2) z
          * (fun z θ => 2 * h z θ + 3 * Work.Spaces.Dth h z θ) z θ := by
    funext z θ
    exact E2hat_eq_prod h z θ
  rw [hprod]
  exact Work.FTS.StrongPersist.linMem_mul
    (Work.FTS.StrongPersist.linMem_radial
      (contDiffOn_iff_forall_nat_le.mpr (fun n _ => contDiffOn_zdiv n)))
    (smoothOpen_two_mul_add h hs)

/-- A constant multiple of a smooth-open profile is smooth-open. -/
theorem smoothOpen_const_mul_h (c : ℝ) {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * h z θ) :=
  Work.FTS.StrongPersist.linMem_const_mul c hs

/-- **Pointwise integrand domination for `Ê₂`.** -/
theorem E2hat_HkIntegrand_le {m : ℕ} (hm : m ≤ 6) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), -(1 / 10 : ℝ) ≤ α → ∀ h : Fn,
      Work.FTS.EllipticEst.SmoothOpen h →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.Spaces.HkIntegrand α m (Work.FTS.CoercivityFix.E2hat h) z θ
          ≤ C * Work.Spaces.HkIntegrand α (m + 1) h z θ := by
  obtain ⟨K, hK, hKb⟩ := Zop_zdiv_bound
  refine ⟨Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 * 26 + 1, by
    have h1 : 0 < Work.FTS.StrongPersist.L3Aux.zmulConst m :=
      Work.FTS.StrongPersist.L3Aux.zmulConst_pos m
    have h2 : 0 < (1 + K) ^ 2 := by positivity
    have h3 : 0 < Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 * 26 :=
      mul_pos (mul_pos h1 h2) (by norm_num)
    linarith, ?_⟩
  intro α hα h hs z hz θ hθ
  have hK0 : 0 ≤ K := le_of_lt hK
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz
  have hθIθ : θ ∈ Work.Spaces.Iθ := by
    simp only [Work.Spaces.Iθ, Set.mem_Icc]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hprod : Work.FTS.CoercivityFix.E2hat h
      = fun z θ => (fun z : ℝ => z / (1 + z) ^ 2) z
          * (fun z θ => 2 * h z θ + 3 * Work.Spaces.Dth h z θ) z θ := by
    funext z θ; exact E2hat_eq_prod h z θ
  rw [hprod]
  have hsm1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 2 * h z θ) :=
    smoothOpen_const_mul_h 2 hs
  have hsm2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 3 * Work.Spaces.Dth h z θ) :=
    smoothOpen_const_mul_h 3 hs.Dth
  have hzm := Work.FTS.StrongPersist.L3Aux.zmul_open α m
    (fun z : ℝ => z / (1 + z) ^ 2) (fun z θ => 2 * h z θ + 3 * Work.Spaces.Dth h z θ)
    hK0 (fun b hb z hz' => le_trans (hKb b (by omega) z (le_of_lt hz')) le_rfl)
    (contDiffOn_iff_forall_nat_le.mpr (fun n _ => contDiffOn_zdiv n))
    (smoothOpen_two_mul_add h hs) z hz θ hθ
  have hadd := Work.FTS.EllipticEst.HkIntegrand_add_le_open α m
    (f := fun z θ => 2 * h z θ) (g := fun z θ => 3 * Work.Spaces.Dth h z θ)
    hsm1 hsm2 hzIz hθIθ
  have hcm1 := Work.FTS.LocData.HkIntegrand_const_mul α m 2 h z θ
  have hcm2 := Work.FTS.LocData.HkIntegrand_const_mul α m 3 (Work.Spaces.Dth h) z θ
  have hdth := Work.FTS.CoercivityFix.E2Bound.HkIntegrand_Dth_le_ge α hα m h z θ hzIz hθIθ
  have hmono : Work.Spaces.HkIntegrand α m h z θ ≤ Work.Spaces.HkIntegrand α (m + 1) h z θ :=
    Work.FTS.StrongPersist.HkIntegrand_le_of_le α (Nat.le_succ m) h z θ
  have hnn : 0 ≤ Work.Spaces.HkIntegrand α (m + 1) h z θ :=
    Work.Spaces.HkIntegrand_nonneg α (m + 1) h z θ
  calc Work.Spaces.HkIntegrand α m
        ((fun z θ => (fun z : ℝ => z / (1 + z) ^ 2) z
          * (fun z θ => 2 * h z θ + 3 * Work.Spaces.Dth h z θ) z θ)) z θ
      ≤ Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 *
          Work.Spaces.HkIntegrand α m (fun z θ => 2 * h z θ + 3 * Work.Spaces.Dth h z θ) z θ :=
        hzm
    _ ≤ Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 * 26 *
          Work.Spaces.HkIntegrand α (m + 1) h z θ := by
        have h26 : Work.Spaces.HkIntegrand α m (fun z θ => 2 * h z θ + 3 * Work.Spaces.Dth h z θ) z θ
            ≤ 26 * Work.Spaces.HkIntegrand α (m + 1) h z θ := by
          have e1 : Work.Spaces.HkIntegrand α m (fun z θ => 2 * h z θ) z θ
              = 4 * Work.Spaces.HkIntegrand α m h z θ := by
            rw [hcm1]; ring
          have e2 : Work.Spaces.HkIntegrand α m (fun z θ => 3 * Work.Spaces.Dth h z θ) z θ
              = 9 * Work.Spaces.HkIntegrand α m (Work.Spaces.Dth h) z θ := by
            rw [hcm2]; ring
          rw [e1, e2] at hadd
          linarith [hadd, hmono, hdth, hnn,
            Work.Spaces.HkIntegrand_nonneg α m h z θ,
            Work.Spaces.HkIntegrand_nonneg α m (Work.Spaces.Dth h) z θ]
        have hC0 : 0 ≤ Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 :=
          mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos m).le (sq_nonneg _)
        nlinarith [h26, hC0, hnn]
    _ ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 * 26 + 1)
          * Work.Spaces.HkIntegrand α (m + 1) h z θ := by nlinarith [hnn]

/-! ## The integrated and membership forms -/

/-- **The `ℋ^m`-norm of the defect `Ê₂ h`**, in the integrated form used by the induction. -/
theorem HkSq_E2hat_le {m : ℕ} (hm : m ≤ 6) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), -(1 / 10 : ℝ) ≤ α → ∀ h : Fn,
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.HkMem α (m + 1) h →
        Work.Spaces.HkSq α m (Work.FTS.CoercivityFix.E2hat h)
          ≤ C * Work.Spaces.HkSq α (m + 1) h := by
  obtain ⟨C, hC, hpt⟩ := E2hat_HkIntegrand_le hm
  refine ⟨C, hC, fun α hα h hs hmem => ?_⟩
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  -- the outer comparison, a.e. in `z`, where the slice inequality holds
  have hout : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m
          (Work.FTS.CoercivityFix.E2hat h) z θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) h z θ) := by
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iz_pos] with z hz
    have hinner : (∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α (m + 1) h z θ)
        = C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) h z θ) :=
      MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ) C _
    rw [← hinner]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α m
        (Work.FTS.CoercivityFix.E2hat h) z θ)
      ((hmem.1 z (le_of_lt hz)).const_mul C) ?_
    have hIoo : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo
    filter_upwards [hIoo] with θ hθ
    exact hpt α hα h hs z hz θ hθ
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α m (Work.FTS.CoercivityFix.E2hat h) z θ)
    (hmem.2.const_mul C) hout) ?_
  exact le_of_eq (MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iz) C
    (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) h z θ))

/-- **`ℋ^m`-membership of the defect `Ê₂ h`.** -/
theorem HkMem_E2hat (α : ℝ) (hα : -(1 / 10 : ℝ) ≤ α) (hα0 : 0 < α) {m : ℕ} (hm : m ≤ 6)
    {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h) (hmem : Work.Spaces.HkMem α (m + 1) h) :
    Work.Spaces.HkMem α m (Work.FTS.CoercivityFix.E2hat h) := by
  obtain ⟨C, hC, hpt⟩ := E2hat_HkIntegrand_le hm
  refine Work.FTS.LocData.HkMem_of_majorant α m
    (f := Work.FTS.CoercivityFix.E2hat h)
    (M := fun z θ => C * Work.Spaces.HkIntegrand α (m + 1) h z θ)
    ((Work.FTS.StrongPersist.q0Sm_of_smoothOpen (smoothOpen_E2hat hs) m).continuousOn_HkIntegrand α)
    ?_ ?_ ?_
  · intro z hz
    exact (hmem.1 z hz).const_mul C
  · have hI2 : MeasureTheory.IntegrableOn (fun z => C * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α (m + 1) h z θ)) Work.Spaces.Iz := hmem.2.const_mul C
    refine hI2.congr (Filter.Eventually.of_forall fun z => ?_)
    exact (MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ) C
      (fun θ => Work.Spaces.HkIntegrand α (m + 1) h z θ)).symm
  · intro z hz θ hθ
    by_cases hz0 : z = 0
    · rw [hz0, Work.FTS.LocData.HkIntegrand_zero_fst]
      exact mul_nonneg hC.le (Work.Spaces.HkIntegrand_nonneg α (m + 1) h 0 θ)
    · have hzpos : 0 < z := lt_of_le_of_ne (show (0 : ℝ) ≤ z from hz) (Ne.symm hz0)
      by_cases hsin : Real.sin (2 * θ) = 0
      · rw [Work.FTS.StrongPersist.HkIntegrand_eq_zero_of_sin_zero
          (α := α) hα0 (k := m) hsin]
        exact mul_nonneg hC.le (Work.Spaces.HkIntegrand_nonneg α (m + 1) h z θ)
      · have hsinpos : 0 < Real.sin (2 * θ) :=
          lt_of_le_of_ne (Work.Elliptic.sin_two_nonneg_of_mem hθ) (Ne.symm hsin)
        have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
          Work.FTS.CoercivityFix.Coer1.mem_Ioo_of_mem_Iθ_of_sin_pos hθ hsinpos
        exact hpt α hα h hs z hzpos θ hθIoo

end Work.FTS.StrongPersist.H6Aux
