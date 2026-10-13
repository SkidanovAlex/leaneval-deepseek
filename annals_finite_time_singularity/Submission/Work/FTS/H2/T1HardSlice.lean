import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Spaces.bt_aux
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.FTS.H2.IBPWeight
import Submission.Work.FTS.H2.T1HardWeightAlg
import Submission.Work.FTS.H2.IbpHardEta
import Submission.Work.FTS.H2.IbpHardMixedBlock
import Submission.Work.FTS.H2.T1HardIntZblk
import Submission.Work.FTS.H2.T1HardIntMixed
import Submission.Work.FTS.H2.HkIntegrandSlotSum
import Submission.Work.FTS.H2.T1HardAesm

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
set_option maxHeartbeats 1600000

/-! ## The generic slot bound -/

theorem t1hb_slot_bound (Kf : ℝ) (hKf0 : 0 ≤ Kf) (q : ℝ) (A v W : ℝ → ℝ)
    (hW : ∀ θ ∈ Spaces.Iθ, |W θ| ≤ (3 / 2) * Kf)
    (hint : IntegrableOn (fun θ => (v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) Spaces.Iθ)
    (hI : ∫ θ in Spaces.Iθ, A θ = -∫ θ in Spaces.Iθ, (v θ) ^ 2 * W θ * (Real.sin (2 * θ)) ^ (-q)) :
    |∫ θ in Spaces.Iθ, A θ|
      ≤ (3 / 2) * Kf * ∫ θ in Spaces.Iθ, (v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) := by
  have hs : ∀ θ ∈ Spaces.Iθ, 0 ≤ (Real.sin (2 * θ)) ^ (-q) := fun θ hθ =>
    Real.rpow_nonneg (Spaces.bt_sin_nonneg hθ) (-q)
  have hpt : ∀ θ ∈ Spaces.Iθ,
      |(v θ) ^ 2 * W θ * (Real.sin (2 * θ)) ^ (-q)|
        ≤ (3 / 2) * Kf * ((v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
    intro θ hθ
    have h1 : |W θ| ≤ (3 / 2) * Kf := hW θ hθ
    have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (-q) := hs θ hθ
    have h3 : 0 ≤ (v θ) ^ 2 := sq_nonneg _
    rw [abs_mul, abs_mul, abs_of_nonneg h3, abs_of_nonneg h2]
    calc (v θ) ^ 2 * |W θ| * (Real.sin (2 * θ)) ^ (-q)
        ≤ (v θ) ^ 2 * ((3 / 2) * Kf) * (Real.sin (2 * θ)) ^ (-q) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h3) h2
      _ = (3 / 2) * Kf * ((v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by ring
  have hintI : Integrable (fun θ => (v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      (volume.restrict Spaces.Iθ) := hint
  have hint' : Integrable (fun θ => (3 / 2) * Kf * ((v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
      (volume.restrict Spaces.Iθ) := hintI.const_mul _
  calc |∫ θ in Spaces.Iθ, A θ|
      = |∫ θ in Spaces.Iθ, (v θ) ^ 2 * W θ * (Real.sin (2 * θ)) ^ (-q)| := by rw [hI, abs_neg]
    _ ≤ ∫ θ in Spaces.Iθ, |(v θ) ^ 2 * W θ * (Real.sin (2 * θ)) ^ (-q)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ θ in Spaces.Iθ, (3 / 2) * Kf * ((v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) :=
        integral_mono_of_nonneg
          (ae_restrict_of_forall_mem measurableSet_Icc fun θ _ => abs_nonneg _)
          hint' (ae_restrict_of_forall_mem measurableSet_Icc hpt)
    _ = (3 / 2) * Kf * ∫ θ in Spaces.Iθ, (v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) :=
        MeasureTheory.integral_const_mul _ _

/-! ## The pointwise `W`-bound

`W` is the second factor produced by the angular integration by parts,
`W(θ) = D_θf(z,θ)/2 + (1-q)cos(2θ)f(z,θ)`; on the closed quadrant it is bounded by
`(3/2)Kf` as soon as `|f| ≤ Kf`, `|D_θf| ≤ Kf` and `|1-q| ≤ 1`. -/

theorem t1hb_W_bound (f : ℝ → ℝ → ℝ) (Kf q : ℝ) {z θ : ℝ} (hz : z ∈ Spaces.Iz)
    (hθ : θ ∈ Spaces.Iθ)
    (hKf : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, |f z θ| ≤ Kf)
    (hKfd : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, |Spaces.Dth f z θ| ≤ Kf)
    (hKf0 : 0 ≤ Kf) (hq : |1 - q| ≤ 1) :
    |Spaces.Dth f z θ / 2 + (1 - q) * Real.cos (2 * θ) * f z θ| ≤ (3 / 2) * Kf := by
  have h1 : |Spaces.Dth f z θ| ≤ Kf := hKfd z hz θ hθ
  have h2 : |f z θ| ≤ Kf := hKf z hz θ hθ
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have h3 : |Spaces.Dth f z θ / 2| ≤ Kf / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have h4 : |(1 - q) * Real.cos (2 * θ) * f z θ| ≤ Kf := by
    rw [abs_mul, abs_mul]
    calc |1 - q| * |Real.cos (2 * θ)| * |f z θ| ≤ 1 * 1 * Kf :=
          mul_le_mul (mul_le_mul hq hc (abs_nonneg _) (by norm_num)) h2 (abs_nonneg _)
            (by norm_num)
      _ = Kf := by ring
  calc |Spaces.Dth f z θ / 2 + (1 - q) * Real.cos (2 * θ) * f z θ|
      ≤ |Spaces.Dth f z θ / 2| + |(1 - q) * Real.cos (2 * θ) * f z θ| := abs_add_le _ _
    _ ≤ Kf / 2 + Kf := add_le_add h3 h4
    _ = (3 / 2) * Kf := by ring

/-! ## The pointwise weight identity for the five slots

The five target integrands `(block²·sin(2θ)^{-q})` become the five summands of `HkIntegrand`
after multiplication by `w(z)²`. -/

theorem t1hb_slots_eq (α z θ : ℝ) (g : ℝ → ℝ → ℝ) (hz : z ∈ Spaces.Iz)
    (hθ : θ ∈ Spaces.Iθ) :
    (Spaces.w z) ^ 2 * ((Spaces.DzIter 4 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      + (Spaces.w z) ^ 2 * ((Spaces.mixed 3 1 g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Spaces.gam α))
      + (Spaces.w z) ^ 2 * ((Spaces.mixed 2 2 g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Spaces.gam α))
      + (Spaces.w z) ^ 2 * ((Spaces.mixed 1 3 g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Spaces.gam α))
      + (Spaces.w z) ^ 2 * ((Spaces.mixed 0 4 g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Spaces.gam α))
      = (Spaces.DzIter 4 g z θ * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) ^ 2
      + (Spaces.mixed 3 1 g z θ * Spaces.Wt α z θ) ^ 2
      + (Spaces.mixed 2 2 g z θ * Spaces.Wt α z θ) ^ 2
      + (Spaces.mixed 1 3 g z θ * Spaces.Wt α z θ) ^ 2
      + (Spaces.mixed 0 4 g z θ * Spaces.Wt α z θ) ^ 2 := by
  have h1 := (T1HardWeightAlg α z θ (Spaces.DzIter 4 g z θ) (Spaces.mixed 3 1 g z θ) hz hθ).1
  have h2 := (T1HardWeightAlg α z θ (Spaces.mixed 3 1 g z θ) (Spaces.mixed 3 1 g z θ) hz hθ).2
  have h3 := (T1HardWeightAlg α z θ (Spaces.mixed 2 2 g z θ) (Spaces.mixed 2 2 g z θ) hz hθ).2
  have h4 := (T1HardWeightAlg α z θ (Spaces.mixed 1 3 g z θ) (Spaces.mixed 1 3 g z θ) hz hθ).2
  have h5 := (T1HardWeightAlg α z θ (Spaces.mixed 0 4 g z θ) (Spaces.mixed 0 4 g z θ) hz hθ).2
  rw [h1, h2, h3, h4, h5]

/-! ## The angular slice bound

For fixed `z ∈ Iz`, the angular integral of `T1Hard α f g z ·` is dominated by
`(3/2)·Kf·∫_θ HkIntegrand α 4 g z θ`: integrate each of the five order-five terms by parts in
`θ` (`IbpHardEta` for the `D_z`-slot, `IbpHardMixedBlock` for the mixed slots), bound the
resulting factor `W(θ) = D_θf/2 + (1-q)cos(2θ)f` by `(3/2)Kf` (`t1hb_W_bound`), and identify the
five remaining `θ`-integrals with the five top-order summands of the `ℋ⁴`-integrand
(`t1hb_slots_eq`, `HkIntegrandSlotSum`). -/

theorem t1hb_slice_bound (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hsmf : Spaces.SmoothNbhd f) (hsmg : Spaces.SmoothNbhd g)
    (hmemg : Spaces.HkMem α 4 g)
    (hKf : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, |f z θ| ≤ Kf)
    (hKfd : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, |Spaces.Dth f z θ| ≤ Kf)
    (hKf0 : 0 ≤ Kf) :
    ∀ z ∈ Spaces.Iz, |∫ θ in Spaces.Iθ, T1Hard α f g z θ|
      ≤ (3 / 2) * Kf * ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α 4 g z θ := by
  intro z hz
  have hz' : (0 : ℝ) ≤ z := hz
  rcases eq_or_lt_of_le hz' with hz0 | hzpos
  · subst hz0
    have hw0 : Spaces.w 0 = 0 := by simp [Spaces.w]
    have hzero : (fun θ : ℝ => T1Hard α f g 0 θ) = fun _ => (0 : ℝ) := by
      funext θ
      simp only [T1Hard, hw0]
      ring
    rw [hzero, MeasureTheory.integral_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hKf0)
      (MeasureTheory.integral_nonneg fun θ => Spaces.HkIntegrand_nonneg α 4 g 0 θ)
  · have hzI : z ∈ Spaces.Iz := le_of_lt hzpos
    set A0 : ℝ → ℝ := fun θ => f z θ * Spaces.Dth (Spaces.DzIter 4 g) z θ
      * Spaces.DzIter 4 g z θ * (Real.sin (2 * θ)) ^ (-Spaces.eta) with hA0
    set A1 : ℝ → ℝ := fun θ => f z θ * Spaces.Dth (Spaces.mixed 3 1 g) z θ
      * Spaces.mixed 3 1 g z θ * (Real.sin (2 * θ)) ^ (-Spaces.gam α) with hA1
    set A2 : ℝ → ℝ := fun θ => f z θ * Spaces.Dth (Spaces.mixed 2 2 g) z θ
      * Spaces.mixed 2 2 g z θ * (Real.sin (2 * θ)) ^ (-Spaces.gam α) with hA2
    set A3 : ℝ → ℝ := fun θ => f z θ * Spaces.Dth (Spaces.mixed 1 3 g) z θ
      * Spaces.mixed 1 3 g z θ * (Real.sin (2 * θ)) ^ (-Spaces.gam α) with hA3
    set A4 : ℝ → ℝ := fun θ => f z θ * Spaces.Dth (Spaces.mixed 0 4 g) z θ
      * Spaces.mixed 0 4 g z θ * (Real.sin (2 * θ)) ^ (-Spaces.gam α) with hA4
    set F0 : ℝ → ℝ := fun θ => (Spaces.DzIter 4 g z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta) with hF0
    set F1 : ℝ → ℝ := fun θ => (Spaces.mixed 3 1 g z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.gam α) with hF1
    set F2 : ℝ → ℝ := fun θ => (Spaces.mixed 2 2 g z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.gam α) with hF2
    set F3 : ℝ → ℝ := fun θ => (Spaces.mixed 1 3 g z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.gam α) with hF3
    set F4 : ℝ → ℝ := fun θ => (Spaces.mixed 0 4 g z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.gam α) with hF4
    have hiA0 : Integrable A0 (volume.restrict Spaces.Iθ) := by
      rw [hA0]; exact (T1HardIntZblk f g hsmf hsmg hzpos).1
    have hiF0 : Integrable F0 (volume.restrict Spaces.Iθ) := by
      rw [hF0]; exact (T1HardIntZblk f g hsmf hsmg hzpos).2
    have hiA1 : Integrable A1 (volume.restrict Spaces.Iθ) := by
      rw [hA1]; exact (T1HardIntMixed α hα hα1 f g hsmf hsmg 3 1 (by norm_num) hzpos).1
    have hiF1 : Integrable F1 (volume.restrict Spaces.Iθ) := by
      rw [hF1]; exact (T1HardIntMixed α hα hα1 f g hsmf hsmg 3 1 (by norm_num) hzpos).2
    have hiA2 : Integrable A2 (volume.restrict Spaces.Iθ) := by
      rw [hA2]; exact (T1HardIntMixed α hα hα1 f g hsmf hsmg 2 2 (by norm_num) hzpos).1
    have hiF2 : Integrable F2 (volume.restrict Spaces.Iθ) := by
      rw [hF2]; exact (T1HardIntMixed α hα hα1 f g hsmf hsmg 2 2 (by norm_num) hzpos).2
    have hiA3 : Integrable A3 (volume.restrict Spaces.Iθ) := by
      rw [hA3]; exact (T1HardIntMixed α hα hα1 f g hsmf hsmg 1 3 (by norm_num) hzpos).1
    have hiF3 : Integrable F3 (volume.restrict Spaces.Iθ) := by
      rw [hF3]; exact (T1HardIntMixed α hα hα1 f g hsmf hsmg 1 3 (by norm_num) hzpos).2
    have hiA4 : Integrable A4 (volume.restrict Spaces.Iθ) := by
      rw [hA4]; exact (T1HardIntMixed α hα hα1 f g hsmf hsmg 0 4 (by norm_num) hzpos).1
    have hiF4 : Integrable F4 (volume.restrict Spaces.Iθ) := by
      rw [hF4]; exact (T1HardIntMixed α hα hα1 f g hsmf hsmg 0 4 (by norm_num) hzpos).2
    have hWη : ∀ θ ∈ Spaces.Iθ, |Spaces.Dth f z θ / 2
        + (1 - Spaces.eta) * Real.cos (2 * θ) * f z θ| ≤ (3 / 2) * Kf :=
      fun θ hθ => t1hb_W_bound f Kf Spaces.eta hzI hθ hKf hKfd hKf0
        (by norm_num [Spaces.eta])
    have hWγ : ∀ θ ∈ Spaces.Iθ, |Spaces.Dth f z θ / 2
        + (1 - Spaces.gam α) * Real.cos (2 * θ) * f z θ| ≤ (3 / 2) * Kf :=
      fun θ hθ => t1hb_W_bound f Kf (Spaces.gam α) hzI hθ hKf hKfd hKf0 (by
        rw [Spaces.gam, abs_le]; constructor <;> linarith)
    have sb0 : |∫ θ in Spaces.Iθ, A0 θ| ≤ (3 / 2) * Kf * ∫ θ in Spaces.Iθ, F0 θ := by
      rw [hA0, hF0]
      refine t1hb_slot_bound Kf hKf0 Spaces.eta _ (fun θ => Spaces.DzIter 4 g z θ)
        (fun θ => Spaces.Dth f z θ / 2 + (1 - Spaces.eta) * Real.cos (2 * θ) * f z θ)
        ?_ ?_ ?_
      · intro θ hθ; exact hWη θ hθ
      · exact (T1HardIntZblk f g hsmf hsmg hzpos).2
      · exact IbpHardEta f (Spaces.DzIter 4 g) hsmf (Spaces.smoothNbhd_DzIter hsmg 4) hzpos
    have sb1 : |∫ θ in Spaces.Iθ, A1 θ| ≤ (3 / 2) * Kf * ∫ θ in Spaces.Iθ, F1 θ := by
      rw [hA1, hF1]
      refine t1hb_slot_bound Kf hKf0 (Spaces.gam α) _ (fun θ => Spaces.mixed 3 1 g z θ)
        (fun θ => Spaces.Dth f z θ / 2 + (1 - Spaces.gam α) * Real.cos (2 * θ) * f z θ)
        ?_ ?_ ?_
      · intro θ hθ; exact hWγ θ hθ
      · exact (T1HardIntMixed α hα hα1 f g hsmf hsmg 3 1 (by norm_num) hzpos).2
      · exact IbpHardMixedBlock α hα hα1 f g hsmf hsmg 3 1 (by norm_num) hzpos
    have sb2 : |∫ θ in Spaces.Iθ, A2 θ| ≤ (3 / 2) * Kf * ∫ θ in Spaces.Iθ, F2 θ := by
      rw [hA2, hF2]
      refine t1hb_slot_bound Kf hKf0 (Spaces.gam α) _ (fun θ => Spaces.mixed 2 2 g z θ)
        (fun θ => Spaces.Dth f z θ / 2 + (1 - Spaces.gam α) * Real.cos (2 * θ) * f z θ)
        ?_ ?_ ?_
      · intro θ hθ; exact hWγ θ hθ
      · exact (T1HardIntMixed α hα hα1 f g hsmf hsmg 2 2 (by norm_num) hzpos).2
      · exact IbpHardMixedBlock α hα hα1 f g hsmf hsmg 2 2 (by norm_num) hzpos
    have sb3 : |∫ θ in Spaces.Iθ, A3 θ| ≤ (3 / 2) * Kf * ∫ θ in Spaces.Iθ, F3 θ := by
      rw [hA3, hF3]
      refine t1hb_slot_bound Kf hKf0 (Spaces.gam α) _ (fun θ => Spaces.mixed 1 3 g z θ)
        (fun θ => Spaces.Dth f z θ / 2 + (1 - Spaces.gam α) * Real.cos (2 * θ) * f z θ)
        ?_ ?_ ?_
      · intro θ hθ; exact hWγ θ hθ
      · exact (T1HardIntMixed α hα hα1 f g hsmf hsmg 1 3 (by norm_num) hzpos).2
      · exact IbpHardMixedBlock α hα hα1 f g hsmf hsmg 1 3 (by norm_num) hzpos
    have sb4 : |∫ θ in Spaces.Iθ, A4 θ| ≤ (3 / 2) * Kf * ∫ θ in Spaces.Iθ, F4 θ := by
      rw [hA4, hF4]
      refine t1hb_slot_bound Kf hKf0 (Spaces.gam α) _ (fun θ => Spaces.mixed 0 4 g z θ)
        (fun θ => Spaces.Dth f z θ / 2 + (1 - Spaces.gam α) * Real.cos (2 * θ) * f z θ)
        ?_ ?_ ?_
      · intro θ hθ; exact hWγ θ hθ
      · exact (T1HardIntMixed α hα hα1 f g hsmf hsmg 0 4 (by norm_num) hzpos).2
      · exact IbpHardMixedBlock α hα hα1 f g hsmf hsmg 0 4 (by norm_num) hzpos
    set I0 : ℝ := ∫ θ in Spaces.Iθ, A0 θ with hI0
    set I1 : ℝ := ∫ θ in Spaces.Iθ, A1 θ with hI1
    set I2 : ℝ := ∫ θ in Spaces.Iθ, A2 θ with hI2
    set I3 : ℝ := ∫ θ in Spaces.Iθ, A3 θ with hI3
    set I4 : ℝ := ∫ θ in Spaces.Iθ, A4 θ with hI4
    set J0 : ℝ := ∫ θ in Spaces.Iθ, F0 θ with hJ0
    set J1 : ℝ := ∫ θ in Spaces.Iθ, F1 θ with hJ1
    set J2 : ℝ := ∫ θ in Spaces.Iθ, F2 θ with hJ2
    set J3 : ℝ := ∫ θ in Spaces.Iθ, F3 θ with hJ3
    set J4 : ℝ := ∫ θ in Spaces.Iθ, F4 θ with hJ4
    have s0 : |I0| ≤ (3 / 2) * Kf * J0 := by rw [hI0, hJ0]; exact sb0
    have s1 : |I1| ≤ (3 / 2) * Kf * J1 := by rw [hI1, hJ1]; exact sb1
    have s2 : |I2| ≤ (3 / 2) * Kf * J2 := by rw [hI2, hJ2]; exact sb2
    have s3 : |I3| ≤ (3 / 2) * Kf * J3 := by rw [hI3, hJ3]; exact sb3
    have s4 : |I4| ≤ (3 / 2) * Kf * J4 := by rw [hI4, hJ4]; exact sb4
    have hsplitpt : ∀ θ : ℝ, T1Hard α f g z θ
        = (Spaces.w z) ^ 2 * (A0 θ + A1 θ + A2 θ + A3 θ + A4 θ) := by
      intro θ
      simp only [T1Hard]
      rw [hA0, hA1, hA2, hA3, hA4]
      simp only []
      ring
    have hN4 : (∫ θ in Spaces.Iθ, A3 θ) + (∫ θ in Spaces.Iθ, A4 θ)
        = ∫ θ in Spaces.Iθ, (A3 θ + A4 θ) := (MeasureTheory.integral_add hiA3 hiA4).symm
    have hN3 : (∫ θ in Spaces.Iθ, A2 θ) + (∫ θ in Spaces.Iθ, (A3 θ + A4 θ))
        = ∫ θ in Spaces.Iθ, (A2 θ + (A3 θ + A4 θ)) :=
      (MeasureTheory.integral_add hiA2 (hiA3.add hiA4)).symm
    have hN2 : (∫ θ in Spaces.Iθ, A1 θ) + (∫ θ in Spaces.Iθ, (A2 θ + (A3 θ + A4 θ)))
        = ∫ θ in Spaces.Iθ, (A1 θ + (A2 θ + (A3 θ + A4 θ))) :=
      (MeasureTheory.integral_add hiA1 (hiA2.add (hiA3.add hiA4))).symm
    have hN1 : (∫ θ in Spaces.Iθ, A0 θ)
          + (∫ θ in Spaces.Iθ, (A1 θ + (A2 θ + (A3 θ + A4 θ))))
        = ∫ θ in Spaces.Iθ, (A0 θ + (A1 θ + (A2 θ + (A3 θ + A4 θ)))) :=
      (MeasureTheory.integral_add hiA0 (hiA1.add (hiA2.add (hiA3.add hiA4)))).symm
    have hsum : ∫ θ in Spaces.Iθ, T1Hard α f g z θ
        = (Spaces.w z) ^ 2 * ((∫ θ in Spaces.Iθ, A0 θ) + (∫ θ in Spaces.Iθ, A1 θ)
            + (∫ θ in Spaces.Iθ, A2 θ) + (∫ θ in Spaces.Iθ, A3 θ)
            + (∫ θ in Spaces.Iθ, A4 θ)) := by
      rw [show (fun θ : ℝ => T1Hard α f g z θ)
          = (fun θ => (Spaces.w z) ^ 2 * (A0 θ + (A1 θ + (A2 θ + (A3 θ + A4 θ))))) from by
        funext θ
        rw [hsplitpt]
        ring]
      rw [MeasureTheory.integral_const_mul]
      rw [← hN1, ← hN2, ← hN3, ← hN4]
      ring
    have htri : |∫ θ in Spaces.Iθ, T1Hard α f g z θ|
        ≤ (Spaces.w z) ^ 2 * (|I0| + |I1| + |I2| + |I3| + |I4|) := by
      rw [hsum, abs_mul, abs_of_nonneg (sq_nonneg (Spaces.w z))]
      rw [← hI0, ← hI1, ← hI2, ← hI3, ← hI4]
      have e4 := abs_add_le (I0 + I1 + I2 + I3) I4
      have e3 := abs_add_le (I0 + I1 + I2) I3
      have e2 := abs_add_le (I0 + I1) I2
      have e1 := abs_add_le I0 I1
      have hsum5 : |I0 + I1 + I2 + I3 + I4| ≤ |I0| + |I1| + |I2| + |I3| + |I4| := by linarith
      exact mul_le_mul_of_nonneg_left hsum5 (sq_nonneg (Spaces.w z))
    have hstep2 : (Spaces.w z) ^ 2 * (|I0| + |I1| + |I2| + |I3| + |I4|)
        ≤ (Spaces.w z) ^ 2 * ((3 / 2) * Kf * (J0 + J1 + J2 + J3 + J4)) := by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg (Spaces.w z))
      nlinarith [s0, s1, s2, s3, s4]
    have hcore : (Spaces.w z) ^ 2 * (J0 + J1 + J2 + J3 + J4)
        ≤ ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α 4 g z θ := by
      have g0 : Integrable (fun θ => (Spaces.w z) ^ 2 * F0 θ) (volume.restrict Spaces.Iθ) :=
        hiF0.const_mul _
      have g1 : Integrable (fun θ => (Spaces.w z) ^ 2 * F1 θ) (volume.restrict Spaces.Iθ) :=
        hiF1.const_mul _
      have g2 : Integrable (fun θ => (Spaces.w z) ^ 2 * F2 θ) (volume.restrict Spaces.Iθ) :=
        hiF2.const_mul _
      have g3 : Integrable (fun θ => (Spaces.w z) ^ 2 * F3 θ) (volume.restrict Spaces.Iθ) :=
        hiF3.const_mul _
      have g4 : Integrable (fun θ => (Spaces.w z) ^ 2 * F4 θ) (volume.restrict Spaces.Iθ) :=
        hiF4.const_mul _
      have c0 : (Spaces.w z) ^ 2 * J0 = ∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F0 θ := by
        rw [hJ0]; exact (MeasureTheory.integral_const_mul ((Spaces.w z) ^ 2) F0).symm
      have c1 : (Spaces.w z) ^ 2 * J1 = ∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F1 θ := by
        rw [hJ1]; exact (MeasureTheory.integral_const_mul ((Spaces.w z) ^ 2) F1).symm
      have c2 : (Spaces.w z) ^ 2 * J2 = ∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F2 θ := by
        rw [hJ2]; exact (MeasureTheory.integral_const_mul ((Spaces.w z) ^ 2) F2).symm
      have c3 : (Spaces.w z) ^ 2 * J3 = ∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F3 θ := by
        rw [hJ3]; exact (MeasureTheory.integral_const_mul ((Spaces.w z) ^ 2) F3).symm
      have c4 : (Spaces.w z) ^ 2 * J4 = ∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F4 θ := by
        rw [hJ4]; exact (MeasureTheory.integral_const_mul ((Spaces.w z) ^ 2) F4).symm
      have m4 : (∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F3 θ)
            + (∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F4 θ)
          = ∫ θ in Spaces.Iθ, ((Spaces.w z) ^ 2 * F3 θ + (Spaces.w z) ^ 2 * F4 θ) :=
        (MeasureTheory.integral_add g3 g4).symm
      have m3 : (∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F2 θ)
            + (∫ θ in Spaces.Iθ, ((Spaces.w z) ^ 2 * F3 θ + (Spaces.w z) ^ 2 * F4 θ))
          = ∫ θ in Spaces.Iθ, ((Spaces.w z) ^ 2 * F2 θ
              + ((Spaces.w z) ^ 2 * F3 θ + (Spaces.w z) ^ 2 * F4 θ)) :=
        (MeasureTheory.integral_add g2 (g3.add g4)).symm
      have m2 : (∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F1 θ)
            + (∫ θ in Spaces.Iθ, ((Spaces.w z) ^ 2 * F2 θ
              + ((Spaces.w z) ^ 2 * F3 θ + (Spaces.w z) ^ 2 * F4 θ)))
          = ∫ θ in Spaces.Iθ, ((Spaces.w z) ^ 2 * F1 θ + ((Spaces.w z) ^ 2 * F2 θ
              + ((Spaces.w z) ^ 2 * F3 θ + (Spaces.w z) ^ 2 * F4 θ))) :=
        (MeasureTheory.integral_add g1 (g2.add (g3.add g4))).symm
      have m1 : (∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F0 θ)
            + (∫ θ in Spaces.Iθ, ((Spaces.w z) ^ 2 * F1 θ + ((Spaces.w z) ^ 2 * F2 θ
              + ((Spaces.w z) ^ 2 * F3 θ + (Spaces.w z) ^ 2 * F4 θ))))
          = ∫ θ in Spaces.Iθ, ((Spaces.w z) ^ 2 * F0 θ + ((Spaces.w z) ^ 2 * F1 θ
              + ((Spaces.w z) ^ 2 * F2 θ + ((Spaces.w z) ^ 2 * F3 θ
              + (Spaces.w z) ^ 2 * F4 θ)))) :=
        (MeasureTheory.integral_add g0 (g1.add (g2.add (g3.add g4)))).symm
      have e1 : (Spaces.w z) ^ 2 * (J0 + J1 + J2 + J3 + J4)
          = (Spaces.w z) ^ 2 * J0 + (Spaces.w z) ^ 2 * J1 + (Spaces.w z) ^ 2 * J2
            + (Spaces.w z) ^ 2 * J3 + (Spaces.w z) ^ 2 * J4 := by ring
      have e2 : (∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F0 θ)
              + (∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F1 θ)
              + (∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F2 θ)
              + (∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F3 θ)
              + (∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F4 θ)
          = (∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F0 θ)
            + ((∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F1 θ)
            + ((∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F2 θ)
            + ((∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F3 θ)
            + (∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * F4 θ)))) := by ring
      rw [e1, c0, c1, c2, c3, c4, e2, m4, m3, m2, m1]
      refine integral_mono_of_nonneg
        (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_)
        (hmemg.1 z hzI)
        (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_)
      · have hsn := Spaces.bt_sin_nonneg hθ
        have h1 : 0 ≤ (Real.sin (2 * θ)) ^ (-Spaces.eta) := Real.rpow_nonneg hsn _
        have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (-Spaces.gam α) := Real.rpow_nonneg hsn _
        have hw : 0 ≤ (Spaces.w z) ^ 2 := sq_nonneg _
        rw [hF0, hF1, hF2, hF3, hF4]
        simp only []
        have t0 : 0 ≤ (Spaces.w z) ^ 2 * ((Spaces.DzIter 4 g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.eta)) :=
          mul_nonneg hw (mul_nonneg (sq_nonneg _) h1)
        have t1 : 0 ≤ (Spaces.w z) ^ 2 * ((Spaces.mixed 3 1 g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.gam α)) :=
          mul_nonneg hw (mul_nonneg (sq_nonneg _) h2)
        have t2 : 0 ≤ (Spaces.w z) ^ 2 * ((Spaces.mixed 2 2 g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.gam α)) :=
          mul_nonneg hw (mul_nonneg (sq_nonneg _) h2)
        have t3 : 0 ≤ (Spaces.w z) ^ 2 * ((Spaces.mixed 1 3 g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.gam α)) :=
          mul_nonneg hw (mul_nonneg (sq_nonneg _) h2)
        have t4 : 0 ≤ (Spaces.w z) ^ 2 * ((Spaces.mixed 0 4 g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.gam α)) :=
          mul_nonneg hw (mul_nonneg (sq_nonneg _) h2)
        exact add_nonneg t0 (add_nonneg t1 (add_nonneg t2 (add_nonneg t3 t4)))
      · rw [hF0, hF1, hF2, hF3, hF4]
        simp only []
        have hassoc : (Spaces.w z) ^ 2 * ((Spaces.DzIter 4 g z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-Spaces.eta))
              + ((Spaces.w z) ^ 2 * ((Spaces.mixed 3 1 g z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-Spaces.gam α))
              + ((Spaces.w z) ^ 2 * ((Spaces.mixed 2 2 g z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-Spaces.gam α))
              + ((Spaces.w z) ^ 2 * ((Spaces.mixed 1 3 g z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-Spaces.gam α))
              + (Spaces.w z) ^ 2 * ((Spaces.mixed 0 4 g z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-Spaces.gam α)))))
            = (Spaces.w z) ^ 2 * ((Spaces.DzIter 4 g z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-Spaces.eta))
              + (Spaces.w z) ^ 2 * ((Spaces.mixed 3 1 g z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-Spaces.gam α))
              + (Spaces.w z) ^ 2 * ((Spaces.mixed 2 2 g z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-Spaces.gam α))
              + (Spaces.w z) ^ 2 * ((Spaces.mixed 1 3 g z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-Spaces.gam α))
              + (Spaces.w z) ^ 2 * ((Spaces.mixed 0 4 g z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-Spaces.gam α)) := by ring
        rw [hassoc]
        exact (t1hb_slots_eq α z θ g hzI hθ).trans_le (HkIntegrandSlotSum α g z θ)
    have hstep3 : (Spaces.w z) ^ 2 * ((3 / 2) * Kf * (J0 + J1 + J2 + J3 + J4))
        ≤ (3 / 2) * Kf * ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α 4 g z θ := by
      rw [show (Spaces.w z) ^ 2 * ((3 / 2) * Kf * (J0 + J1 + J2 + J3 + J4))
          = (3 / 2) * Kf * ((Spaces.w z) ^ 2 * (J0 + J1 + J2 + J3 + J4)) by ring]
      exact mul_le_mul_of_nonneg_left hcore (by linarith)
    linarith [htri, hstep2, hstep3]

end Work.FTS.H2
