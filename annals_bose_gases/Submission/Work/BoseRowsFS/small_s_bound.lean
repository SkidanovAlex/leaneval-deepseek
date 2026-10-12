import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseB7AK.C3Q.chat_sq_div_eq_coulomb_toReal
import Submission.Work.BoseRowsFS.CoulShift.fourier_sum_shift_norm_le
import Submission.Work.BoseRowsFS.CoulShift.integral_integral_eq_toReal_lintegral
import Submission.Work.BoseRowsFS.CoulShift.lintegral_sum_shift_expansion
import Submission.Work.BoseRowsFS.far_tail_le
import Submission.Work.BoseRowsFS.near_set_finite
import Submission.Work.BoseRowsFS.ssb_Kt_Ioc_far_le
import Submission.Work.BoseRowsFS.ssb_Kt_Ioc_le
import Submission.Work.BoseRowsFS.ssb_summable_Kt_image
import Submission.Work.BoseRowsFS.sum_chat_sq_exp_eq
import Submission.Work.BoseRowsFS.theta3_image_identity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.small_s_bound` — the `s ≤ 1` half of the honest lattice row

`ℓ⁻³ ∫_{s ∈ (0,1]} Σ_{m∈S} Ŵ(k_m)² e^{-s‖k_m‖²} ds ≤ 10⁶(1+R)⁴ (∬ W(x)W(y)/‖x-y‖ + (∫W)²)`

for `k_m = (2π/ℓ)·m`, with `W ≥ 0` a.e., even, supported in the ball of radius `R ≤ ℓ`.

The ingredients (all `sorry`-free in this workspace) are

* `sum_chat_sq_exp_eq` — the full lattice sum at time `s` is `½∬WW(θ_s(x-y)+θ_s(x+y))`,
  and the finite sum over `S` is dominated by it (all summands are nonnegative);
* `LatSmall.thetaK_images` — the Poisson/theta identity in heat-kernel image form
  `ℓ⁻³θ_s(z) = Σ_m Kt_s(z + ℓm)`;
* `LatSmall.lintegral_Kt_Ioc_le` / `lintegral_Kt_Ioc_far_le` — the truncated heat kernel is
  bounded by the Coulomb kernel `1/(4π‖z‖)`, resp. by `(4π)^{-3/2}e^{-‖z‖²/4}` once `‖z‖² ≥ 6`;
* `LatSmall.lintegral_coulomb_shift_le` — the shifted Newtonian form is dominated by the
  unshifted one (shifting does not increase the Coulomb energy);
* `near_set_finite` (at most `1000` near images `ℓ‖m‖ < 2R + √6`) and `far_tail_le`
  (`Σ_{far} e^{-(ℓ‖m‖-2R)²/4} ≤ 1000(1+R)³`).

The rest of this file is the Tonelli bookkeeping and the numerical assembly.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseRowsFS

set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. `ofReal` of a nonnegative iterated Bochner integral below the iterated `∫⁻` -/

lemma ssb_ofReal_iterated_le {g : E3 → E3 → ℝ} (hg0 : ∀ x y, 0 ≤ g x y)
    (hgm : AEMeasurable (Function.uncurry g) (volume.prod volume)) :
    ENNReal.ofReal (∫ x, ∫ y, g x y) ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x y) := by
  have hsm : AEStronglyMeasurable (fun x => ∫ y, g x y) volume :=
    hgm.aestronglyMeasurable.integral_prod_right'
  have hnn : 0 ≤ᵐ[volume] fun x => ∫ y, g x y :=
    Eventually.of_forall (fun x => integral_nonneg (fun y => hg0 x y))
  have h1 : (∫ x, ∫ y, g x y) = (∫⁻ x, ENNReal.ofReal (∫ y, g x y)).toReal :=
    integral_eq_lintegral_of_nonneg_ae hnn hsm
  calc ENNReal.ofReal (∫ x, ∫ y, g x y)
      = ENNReal.ofReal ((∫⁻ x, ENNReal.ofReal (∫ y, g x y)).toReal) := by rw [h1]
    _ ≤ ∫⁻ x, ENNReal.ofReal (∫ y, g x y) := ENNReal.ofReal_toReal_le
    _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x y) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hgm.aestronglyMeasurable.prodMk_left] with x hx
        have hx0 : 0 ≤ᵐ[volume] fun y => g x y := Eventually.of_forall (hg0 x)
        have h2 : (∫ y, g x y) = (∫⁻ y, ENNReal.ofReal (g x y)).toReal :=
          integral_eq_lintegral_of_nonneg_ae hx0 hx
        rw [h2]
        exact ENNReal.ofReal_toReal_le

/-! ## 1b. The Poisson/theta identity in heat-kernel image form -/

/-- **The heat-kernel image form of the theta kernel** (unnormalised form). -/
theorem ssb_thetaK_images_aux {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (z : E3) :
    thetaK ℓ s z = ℓ ^ 3 * ∑' m : Fin 3 → ℤ, Kt s (z + ℓ • vecZ m) := by
  have hsp : (0 : ℝ) < 4 * Real.pi * s := by positivity
  have h3 := theta3_image_identity hℓ hs z
  have hsqrt : (4 * Real.pi * s) ^ (1 / 2 : ℝ) = 2 * Real.sqrt (Real.pi * s) := by
    rw [show (4 : ℝ) * Real.pi * s = 4 * (Real.pi * s) by ring,
      Real.mul_rpow (by norm_num) (by positivity : (0 : ℝ) ≤ Real.pi * s),
      Real.sqrt_eq_rpow]
    norm_num
  have hcube : (2 * Real.sqrt (Real.pi * s)) ^ 3 = (4 * Real.pi * s) ^ (3 / 2 : ℝ) := by
    rw [← hsqrt, ← Real.rpow_natCast, ← Real.rpow_mul hsp.le]
    norm_num
  have hAB : (2 * Real.sqrt (Real.pi * s) / ℓ) ^ 3
      * (ℓ ^ 3 * (4 * Real.pi * s) ^ (-(3 / 2 : ℝ))) = 1 := by
    have hℓ3 : (ℓ : ℝ) ^ 3 ≠ 0 := by positivity
    have hr : (4 * Real.pi * s) ^ (-(3 / 2 : ℝ)) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hsp _)
    rw [div_pow, hcube]
    field_simp
    rw [← Real.rpow_add hsp]
    norm_num
  have hcpos : 0 < (2 * Real.sqrt (Real.pi * s) / ℓ) ^ 3 := by positivity
  have hKt : ∀ m : Fin 3 → ℤ, Kt s (z + ℓ • vecZ m)
      = (4 * Real.pi * s) ^ (-(3 / 2 : ℝ))
        * Real.exp (-(‖z + ℓ • vecZ m‖ ^ 2 / (4 * s))) := by
    intro m
    rw [Kt, neg_div]
  have htsum : (∑' m : Fin 3 → ℤ, Kt s (z + ℓ • vecZ m))
      = (4 * Real.pi * s) ^ (-(3 / 2 : ℝ))
        * ∑' m : Fin 3 → ℤ, Real.exp (-(‖z + ℓ • vecZ m‖ ^ 2 / (4 * s))) := by
    rw [← tsum_mul_left]
    exact tsum_congr hKt
  have htheta : thetaK ℓ s z = ∑' j : Fin 3 → ℤ,
      Real.exp (-(s * ‖(2 * Real.pi / ℓ) • vecZ j‖ ^ 2))
        * Real.cos (inner ℝ ((2 * Real.pi / ℓ) • vecZ j) z) := rfl
  have hcancel : thetaK ℓ s z = ℓ ^ 3 * (4 * Real.pi * s) ^ (-(3 / 2 : ℝ))
      * ∑' m : Fin 3 → ℤ, Real.exp (-(‖z + ℓ • vecZ m‖ ^ 2 / (4 * s))) := by
    have h2 : (2 * Real.sqrt (Real.pi * s) / ℓ) ^ 3
        * (ℓ ^ 3 * (4 * Real.pi * s) ^ (-(3 / 2 : ℝ))
          * ∑' m : Fin 3 → ℤ, Real.exp (-(‖z + ℓ • vecZ m‖ ^ 2 / (4 * s))))
        = ∑' m : Fin 3 → ℤ, Real.exp (-(‖z + ℓ • vecZ m‖ ^ 2 / (4 * s))) := by
      rw [← mul_assoc, hAB, one_mul]
    refine mul_left_cancel₀ (ne_of_gt hcpos) ?_
    rw [htheta, ← h3]
    exact h2.symm
  rw [hcancel, htsum]
  ring

/-- **The heat-kernel image form of the theta kernel**: for `ℓ, s > 0` and `z : ℝ³`,

  `ℓ⁻³ θ_s(z) = Σ_{m ∈ ℤ³} Kt_s(z + ℓ·m)`. -/
theorem ssb_thetaK_images {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (z : E3) :
    ℓ ^ (-(3 : ℝ)) * thetaK ℓ s z = ∑' m : Fin 3 → ℤ, Kt s (z + ℓ • vecZ m) := by
  rw [ssb_thetaK_images_aux hℓ hs z]
  rw [← mul_assoc, ← Real.rpow_natCast ℓ 3, ← Real.rpow_add hℓ]
  norm_num

/-- **Positivity of the theta kernel** (all mode summands of the image form are heat kernels). -/
theorem ssb_thetaK_nonneg {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (z : E3) :
    0 ≤ thetaK ℓ s z := by
  have h := ssb_thetaK_images hℓ hs z
  have hS : (0 : ℝ) ≤ ∑' m : Fin 3 → ℤ, Kt s (z + ℓ • vecZ m) :=
    tsum_nonneg (fun m => Kt_nonneg hs _)
  have hcube : ℓ ^ (3 : ℝ) * ℓ ^ (-(3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hℓ]
    norm_num
  calc (0 : ℝ) ≤ ℓ ^ (3 : ℝ) * ∑' m : Fin 3 → ℤ, Kt s (z + ℓ • vecZ m) :=
        mul_nonneg (Real.rpow_nonneg hℓ.le _) hS
    _ = thetaK ℓ s z := by rw [← h, ← mul_assoc, hcube, one_mul]

/-! ## 2. The `ℝ≥0∞`-valued image kernel `Σ_m Kt_s(z + ℓm)` -/

/-- The image kernel `Σ_m ofReal (Kt_s(z + ℓ·m))` as an `ℝ≥0∞`-valued function; by
`LatSmall.thetaK_images` it equals `ofReal (ℓ⁻³ θ_s(z))`.  All its summands are nonnegative,
which makes the measurability duties of the Tonelli steps trivial. -/
def ssbKimg (ℓ s : ℝ) (z : E3) : ℝ≥0∞ :=
  ∑' m : Fin 3 → ℤ, ENNReal.ofReal (Kt s (z + ℓ • vecZ m))

lemma ssb_measurable_Kimg (ℓ : ℝ) :
    Measurable (fun q : ℝ × E3 => ssbKimg ℓ q.1 q.2) := by
  refine Measurable.ennreal_tsum (fun m => ?_)
  exact ENNReal.measurable_ofReal.comp (by unfold Kt; fun_prop)

/-- `ofReal (ℓ⁻³ θ_s(z))` is the image kernel; this is the pointwise bridge between the
Bochner side (where `θ` appears through `sum_chat_sq_exp_eq`) and the Tonelli side (where the
nonnegative `ℝ≥0∞`-valued `ssbKimg` is used). -/
lemma ssb_ofReal_thetaK {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (z : E3) :
    ENNReal.ofReal (ℓ ^ (-(3 : ℝ)) * thetaK ℓ s z) = ssbKimg ℓ s z := by
  have hsum := ssb_summable_Kt_image (ℓ := ℓ) hℓ hs z
  rw [ssb_thetaK_images hℓ hs z, ssbKimg]
  exact ENNReal.ofReal_tsum_of_nonneg (fun m => Kt_nonneg hs _) hsum

/-! ## 3. Summability of the Gaussian mode weights and of the lattice row -/

/-- **The mode weights are summable**: `Σ_j e^{-s‖k_j‖²} < ∞` for `ℓ, s > 0`.  This is
`ssb_summable_Kt_image` at `z = 0` with the heat-kernel prefactor stripped. -/
lemma ssb_summable_kvec_gauss {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) :
    Summable (fun j : Fin 3 → ℤ => Real.exp (-(s * ‖kvec ℓ j‖ ^ 2))) := by
  set c : ℝ := (2 * Real.pi / ℓ) ^ 2 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  set t : ℝ := ℓ ^ 2 / (4 * s * c) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have hK := ssb_summable_Kt_image (ℓ := ℓ) hℓ htpos (0 : E3)
  have h4 : (0 : ℝ) < 4 * Real.pi * t := by rw [ht]; positivity
  have hexp : ∀ m : Fin 3 → ℤ, ℓ ^ 2 * ‖vecZ m‖ ^ 2 / (4 * t) = s * (c * ‖vecZ m‖ ^ 2) := by
    intro m
    rw [ht]
    field_simp
  have hsplit : ∀ m : Fin 3 → ℤ, Kt t (0 + ℓ • vecZ m)
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(s * ‖kvec ℓ m‖ ^ 2)) := by
    intro m
    rw [Kt, zero_add, norm_smul, Real.norm_of_nonneg hℓ.le, mul_pow, neg_div, hexp m,
      norm_kvec hℓ.le, mul_pow, hc]
  refine (hK.congr hsplit).mul_left ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)))⁻¹
    |>.congr (fun m => ?_)
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos h4 _)), one_mul]

/-- `chat` is dominated by the `L¹` mass. -/
lemma ssb_abs_chat_le_mass {W : E3 → ℝ} (hW : MeasureTheory.Integrable W) (k : E3) :
    |Work.BoseFixR.chat W k| ≤ ∫ x, |W x| := by
  rw [Work.BoseB7AK.W1low.chat_eq_integral_cos hW k]
  refine le_trans abs_integral_le_integral_abs ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) (hW.abs)
    (Eventually.of_forall fun y => ?_)
  calc |W y * Real.cos (inner ℝ k y)| = |W y| * |Real.cos (inner ℝ k y)| := abs_mul _ _
    _ ≤ |W y| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
    _ = |W y| := mul_one _

/-- **The lattice row is summable** at every `s > 0`: `Σ_j Ŵ(k_j)² e^{-s‖k_j‖²} < ∞`, by
domination with `(∫‖W‖)² Σ_j e^{-s‖k_j‖²}`. -/
lemma ssb_summable_row {W : E3 → ℝ} (hW : MeasureTheory.Integrable W) {ℓ s : ℝ}
    (hℓ : 0 < ℓ) (hs : 0 < s) :
    Summable (fun j : Fin 3 → ℤ =>
      (Work.BoseFixR.chat W (kvec ℓ j)) ^ 2 * Real.exp (-(s * ‖kvec ℓ j‖ ^ 2))) := by
  have hg := ssb_summable_kvec_gauss hℓ hs
  have hm : ∀ j : Fin 3 → ℤ, ‖(Work.BoseFixR.chat W (kvec ℓ j)) ^ 2
      * Real.exp (-(s * ‖kvec ℓ j‖ ^ 2))‖
      ≤ (∫ x, |W x|) ^ 2 * Real.exp (-(s * ‖kvec ℓ j‖ ^ 2)) := by
    intro j
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (sq_nonneg _)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    calc (Work.BoseFixR.chat W (kvec ℓ j)) ^ 2
        = |Work.BoseFixR.chat W (kvec ℓ j)| ^ 2 := by rw [sq_abs]
      _ ≤ (∫ x, |W x|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (ssb_abs_chat_le_mass hW (kvec ℓ j)) 2
  exact Summable.of_norm_bounded (hg.mul_left ((∫ x, |W x|) ^ 2)) hm

/-! ## 3b. The truncated heat-kernel bounds and the shift inequality -/

/-- `s ↦ Kt_s(z)` is integrable on `(0,∞)` for `z ≠ 0`. -/
lemma ssb_integrableOn_Ioi_Kt {z : E3} (hz : z ≠ 0) :
    MeasureTheory.IntegrableOn (fun s : ℝ => Kt s z) (Set.Ioi (0 : ℝ)) := by
  by_contra h
  have h0 : (∫ s in Set.Ioi (0 : ℝ), Kt s z) = 0 := integral_undef h
  rw [integral_Kt_eq z hz] at h0
  have hpos : 0 < 1 / (4 * Real.pi * ‖z‖) := by
    have := norm_pos_iff.mpr hz
    positivity
  linarith

/-- **The truncated heat kernel is dominated by the Coulomb kernel.** -/
lemma ssb_lintegral_Kt_Ioc_le {z : E3} (hz : z ≠ 0) :
    (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s z))
      ≤ ENNReal.ofReal (1 / (4 * Real.pi * ‖z‖)) := by
  have hint : MeasureTheory.IntegrableOn (fun s : ℝ => Kt s z) (Set.Ioc (0 : ℝ) 1) :=
    (ssb_integrableOn_Ioi_Kt hz).mono_set (fun s hs => hs.1)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] (fun s : ℝ => Kt s z) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
    exact Kt_nonneg hs.1 z
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
  exact ENNReal.ofReal_le_ofReal (ssb_Kt_Ioc_le hz)

/-- **The far truncated heat kernel decays Gaussianly.** -/
lemma ssb_lintegral_Kt_Ioc_far_le {z : E3} (hz : 6 ≤ ‖z‖ ^ 2) :
    (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s z))
      ≤ ENNReal.ofReal ((4 * Real.pi) ^ (-(3 / 2 : ℝ)) * Real.exp (-‖z‖ ^ 2 / 4)) := by
  have h0 : 0 < ‖z‖ := by
    by_contra h
    have hz0 : ‖z‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [hz0] at hz
    norm_num at hz
  have hint : MeasureTheory.IntegrableOn (fun s : ℝ => Kt s z) (Set.Ioc (0 : ℝ) 1) :=
    (ssb_integrableOn_Ioi_Kt (norm_pos_iff.mp h0)).mono_set (fun s hs => hs.1)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] (fun s : ℝ => Kt s z) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
    exact Kt_nonneg hs.1 z
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
  exact ENNReal.ofReal_le_ofReal (ssb_Kt_Ioc_far_le hz)

/-- **The shift inequality** for the Newtonian kernel in `ℝ≥0∞` form: the shifted double
`∫⁻` is dominated by the unshifted one.  Proved from the corpus Fourier identity applied to
`V` and to `V + V(·+a)` (whose Fourier transform has norm at most `2‖𝓕V‖`). -/
theorem ssb_lintegral_coulomb_shift_le {V : E3 → ℝ} (hVI : MeasureTheory.Integrable V)
    (hV0 : ∀ x, 0 ≤ V x) (a : E3) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (V x * V (y + a) / ‖x - y‖))
      ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (V x * V y / ‖x - y‖) := by
  classical
  set A0 : ℝ≥0∞ := ∫⁻ x, ∫⁻ y, ENNReal.ofReal (V x * V y / ‖x - y‖) with hA0
  set Aa : ℝ≥0∞ := ∫⁻ x, ∫⁻ y, ENNReal.ofReal (V x * V (y + a) / ‖x - y‖) with hAa
  set S : E3 → ℝ := fun x => V x + V (x + a) with hS
  have hS0 : ∀ x, 0 ≤ S x := fun x => by
    simp only [hS]; exact add_nonneg (hV0 x) (hV0 _)
  have hSI : MeasureTheory.Integrable S := hVI.add (hVI.comp_add_right a)
  have hVmeas : AEMeasurable V volume := hVI.aestronglyMeasurable.aemeasurable
  have hIdV := Commons.Analysis.Fourier.coulomb_energy_fourier_lintegral_eq hVI hV0
  have hIdS := Commons.Analysis.Fourier.coulomb_energy_fourier_lintegral_eq hSI hS0
  have hexp : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (S x * S y / ‖x - y‖)) = 2 * A0 + 2 * Aa := by
    simp only [hS, hA0, hAa]
    exact CoulShift.lintegral_sum_shift_expansion hVmeas hV0 a
  have hcmp : (∫⁻ q, ENNReal.ofReal
        (‖FourierTransform.fourier (fun x : E3 => (S x : ℂ)) q‖ ^ 2 / ‖q‖ ^ 2))
      ≤ 4 * (∫⁻ q, ENNReal.ofReal
        (‖FourierTransform.fourier (fun x : E3 => (V x : ℂ)) q‖ ^ 2 / ‖q‖ ^ 2)) := by
    rw [← lintegral_const_mul' (4 : ℝ≥0∞) _ (by norm_num)]
    refine lintegral_mono (fun q => ?_)
    have hfun : (fun x : E3 => (S x : ℂ)) = fun x => (V x : ℂ) + (V (x + a) : ℂ) := by
      funext x
      simp only [hS, Complex.ofReal_add]
    have hnorm : ‖FourierTransform.fourier (fun x : E3 => (S x : ℂ)) q‖
        ≤ 2 * ‖FourierTransform.fourier (fun x : E3 => (V x : ℂ)) q‖ := by
      rw [hfun]
      exact CoulShift.fourier_sum_shift_norm_le (F := fun x : E3 => (V x : ℂ)) hVI.ofReal a q
    rcases eq_or_ne q 0 with hq | hq
    · rw [hq]; simp
    · have hq2 : 0 < ‖q‖ ^ 2 := pow_pos (norm_pos_iff.mpr hq) 2
      have h2 : ‖FourierTransform.fourier (fun x : E3 => (S x : ℂ)) q‖ ^ 2
          ≤ 4 * ‖FourierTransform.fourier (fun x : E3 => (V x : ℂ)) q‖ ^ 2 := by
        have h := pow_le_pow_left₀
          (norm_nonneg (FourierTransform.fourier (fun x : E3 => (S x : ℂ)) q)) hnorm 2
        nlinarith [h]
      rw [show (4 : ℝ≥0∞) * ENNReal.ofReal
          (‖FourierTransform.fourier (fun x : E3 => (V x : ℂ)) q‖ ^ 2 / ‖q‖ ^ 2)
          = ENNReal.ofReal (4 * (‖FourierTransform.fourier (fun x : E3 => (V x : ℂ)) q‖ ^ 2
              / ‖q‖ ^ 2)) from by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [show (4 : ℝ) * (‖FourierTransform.fourier (fun x : E3 => (V x : ℂ)) q‖ ^ 2 / ‖q‖ ^ 2)
          = 4 * ‖FourierTransform.fourier (fun x : E3 => (V x : ℂ)) q‖ ^ 2 / ‖q‖ ^ 2 by ring]
      exact div_le_div_of_nonneg_right h2 hq2.le
  have hpi0 : (ENNReal.ofReal Real.pi) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]; linarith [Real.pi_pos]
  have hpitop : (ENNReal.ofReal Real.pi) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hstep : ENNReal.ofReal Real.pi * (2 * A0 + 2 * Aa) ≤ ENNReal.ofReal Real.pi * (4 * A0) := by
    calc ENNReal.ofReal Real.pi * (2 * A0 + 2 * Aa)
        = ENNReal.ofReal Real.pi * (∫⁻ x, ∫⁻ y, ENNReal.ofReal (S x * S y / ‖x - y‖)) := by
          rw [hexp]
      _ = ∫⁻ q, ENNReal.ofReal
            (‖FourierTransform.fourier (fun x : E3 => (S x : ℂ)) q‖ ^ 2 / ‖q‖ ^ 2) := hIdS.symm
      _ ≤ 4 * (∫⁻ q, ENNReal.ofReal
            (‖FourierTransform.fourier (fun x : E3 => (V x : ℂ)) q‖ ^ 2 / ‖q‖ ^ 2)) := hcmp
      _ = ENNReal.ofReal Real.pi * (4 * A0) := by
          rw [hIdV]
          ring
  have hcancel : ∀ x y : ℝ≥0∞, ENNReal.ofReal Real.pi * x ≤ ENNReal.ofReal Real.pi * y → x ≤ y := by
    intro x y h
    calc x = (ENNReal.ofReal Real.pi)⁻¹ * (ENNReal.ofReal Real.pi * x) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hpi0 hpitop, one_mul]
      _ ≤ (ENNReal.ofReal Real.pi)⁻¹ * (ENNReal.ofReal Real.pi * y) :=
          (by gcongr)
      _ = y := by rw [← mul_assoc, ENNReal.inv_mul_cancel hpi0 hpitop, one_mul]
  have hbasic : 2 * (A0 + Aa) ≤ 2 * (2 * A0) := by
    calc 2 * (A0 + Aa) = 2 * A0 + 2 * Aa := by ring
      _ ≤ 4 * A0 := hcancel _ _ hstep
      _ = 2 * (2 * A0) := by ring
  have h2c : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2t : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hA0Aa : A0 + Aa ≤ 2 * A0 := by
    have h := hbasic
    calc A0 + Aa = (2 : ℝ≥0∞)⁻¹ * (2 * (A0 + Aa)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel h2c h2t, one_mul]
      _ ≤ (2 : ℝ≥0∞)⁻¹ * (2 * (2 * A0)) := by gcongr
      _ = 2 * A0 := by rw [← mul_assoc, ENNReal.inv_mul_cancel h2c h2t, one_mul]
  rcases eq_or_ne A0 ⊤ with hA0top | hA0fin
  · rw [hA0top, hAa]; exact le_top
  · have h3 : Aa ≤ A0 := by
      rw [show (2 : ℝ≥0∞) * A0 = A0 + A0 by ring] at hA0Aa
      rw [add_comm A0 Aa] at hA0Aa
      exact (ENNReal.add_le_add_iff_right hA0fin).mp hA0Aa
    rw [hAa, hA0]
    exact h3

/-! ## 4. The `s`-pointwise bound: row ≤ ½ image sum -/

/-- **The `s`-pointwise bound.**  For `s > 0` the lattice row at time `s` (over the finite set
`S`) is dominated by half of the pair form of the image kernel `Σ_m Kt_s(z + ℓm)`.  The proof
uses `sum_chat_sq_exp_eq` for the full lattice sum, the finite-sum ≤ tsum step, and the
pointwise rewriting `ofReal (ℓ⁻³θ_s(z)) = Σ_m ofReal (Kt_s(z + ℓm))`. -/
lemma ssb_pointwise {W : E3 → ℝ} {ℓ : ℝ} (hW : MeasureTheory.Integrable W)
    (hW0 : ∀ x, 0 ≤ W x) (hℓ : 0 < ℓ) (S : Finset (Fin 3 → ℤ)) {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (ℓ ^ (-(3 : ℝ)) * ∑ m ∈ S, (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2
        * Real.exp (-(s * ‖kvec ℓ m‖ ^ 2)))
      ≤ (1 / 2 : ℝ≥0∞) * ∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
          * (ssbKimg ℓ s (p.1 - p.2) + ssbKimg ℓ s (p.1 + p.2)) := by
  have hsum := ssb_summable_row hW hℓ hs
  have hrow : (∑ m ∈ S, (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2
        * Real.exp (-(s * ‖kvec ℓ m‖ ^ 2)))
      ≤ ∑' j : Fin 3 → ℤ, (Work.BoseFixR.chat W (kvec ℓ j)) ^ 2
        * Real.exp (-(s * ‖kvec ℓ j‖ ^ 2)) :=
    Summable.sum_le_tsum S (fun j _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hsum
  have hident : (∑' j : Fin 3 → ℤ, (Work.BoseFixR.chat W (kvec ℓ j)) ^ 2
        * Real.exp (-(s * ‖kvec ℓ j‖ ^ 2)))
      = (1 / 2) * ∫ x, ∫ y, W x * W y * (thetaK ℓ s (x - y) + thetaK ℓ s (x + y)) :=
    sum_chat_sq_exp_eq hW hℓ hs
  have hℓ3 : (0 : ℝ) ≤ ℓ ^ (-(3 : ℝ)) := Real.rpow_nonneg hℓ.le _
  have hθm : Measurable (fun z : E3 => thetaK ℓ s z) := by
    have hK : Measurable (fun z : E3 => ssbKimg ℓ s z) :=
      (ssb_measurable_Kimg ℓ).comp (measurable_const.prodMk measurable_id)
    have hEq : ∀ z : E3, thetaK ℓ s z = ℓ ^ 3 * (ssbKimg ℓ s z).toReal := by
      intro z
      have h := ssb_ofReal_thetaK hℓ hs z
      have h2 : ℓ ^ (-(3 : ℝ)) * thetaK ℓ s z = (ssbKimg ℓ s z).toReal := by
        have hc := congrArg ENNReal.toReal h
        rwa [ENNReal.toReal_ofReal (mul_nonneg hℓ3 (ssb_thetaK_nonneg hℓ hs z))] at hc
      calc thetaK ℓ s z = ℓ ^ 3 * (ℓ ^ (-(3 : ℝ)) * thetaK ℓ s z) := by
            rw [← mul_assoc, ← Real.rpow_natCast ℓ 3, ← Real.rpow_add hℓ]
            norm_num
        _ = ℓ ^ 3 * (ssbKimg ℓ s z).toReal := by rw [h2]
    rw [funext hEq]
    exact measurable_const.mul hK.ennreal_toReal
  have hg0 : ∀ x y : E3, 0 ≤ W x * W y * (thetaK ℓ s (x - y) + thetaK ℓ s (x + y)) := fun x y =>
    mul_nonneg (mul_nonneg (hW0 x) (hW0 y))
      (add_nonneg (ssb_thetaK_nonneg hℓ hs _) (ssb_thetaK_nonneg hℓ hs _))
  have hgm : AEMeasurable (Function.uncurry (fun x y : E3 =>
      W x * W y * (thetaK ℓ s (x - y) + thetaK ℓ s (x + y)))) (volume.prod volume) := by
    have ha : AEMeasurable (fun p : E3 × E3 => W p.1) (volume.prod volume) :=
      hW.aestronglyMeasurable.aemeasurable.comp_fst
    have hb : AEMeasurable (fun p : E3 × E3 => W p.2) (volume.prod volume) :=
      hW.aestronglyMeasurable.aemeasurable.comp_snd
    have hc : AEMeasurable (fun p : E3 × E3 => thetaK ℓ s (p.1 - p.2)) (volume.prod volume) :=
      ((hθm.comp (measurable_fst.sub measurable_snd))).aemeasurable
    have hd : AEMeasurable (fun p : E3 × E3 => thetaK ℓ s (p.1 + p.2)) (volume.prod volume) :=
      ((hθm.comp (measurable_fst.add measurable_snd))).aemeasurable
    exact (ha.mul hb).mul (hc.add hd)
  have key : ∀ p : E3 × E3,
      ENNReal.ofReal (ℓ ^ (-(3 : ℝ))) * ENNReal.ofReal (W p.1 * W p.2 *
          (thetaK ℓ s (p.1 - p.2) + thetaK ℓ s (p.1 + p.2)))
        = ENNReal.ofReal (W p.1 * W p.2)
            * (ssbKimg ℓ s (p.1 - p.2) + ssbKimg ℓ s (p.1 + p.2)) := by
    intro p
    have ha : 0 ≤ W p.1 * W p.2 := mul_nonneg (hW0 p.1) (hW0 p.2)
    have hb1 : 0 ≤ thetaK ℓ s (p.1 - p.2) := ssb_thetaK_nonneg hℓ hs _
    have hb2 : 0 ≤ thetaK ℓ s (p.1 + p.2) := ssb_thetaK_nonneg hℓ hs _
    calc ENNReal.ofReal (ℓ ^ (-(3 : ℝ))) * ENNReal.ofReal (W p.1 * W p.2 *
            (thetaK ℓ s (p.1 - p.2) + thetaK ℓ s (p.1 + p.2)))
        = ENNReal.ofReal (ℓ ^ (-(3 : ℝ)) * (W p.1 * W p.2 *
            (thetaK ℓ s (p.1 - p.2) + thetaK ℓ s (p.1 + p.2)))) :=
          (ENNReal.ofReal_mul hℓ3).symm
      _ = ENNReal.ofReal ((W p.1 * W p.2) * (ℓ ^ (-(3 : ℝ)) *
            (thetaK ℓ s (p.1 - p.2) + thetaK ℓ s (p.1 + p.2)))) := by
          congr 1
          ring
      _ = ENNReal.ofReal (W p.1 * W p.2) * ENNReal.ofReal (ℓ ^ (-(3 : ℝ)) *
            (thetaK ℓ s (p.1 - p.2) + thetaK ℓ s (p.1 + p.2))) := ENNReal.ofReal_mul ha
      _ = ENNReal.ofReal (W p.1 * W p.2) * (ENNReal.ofReal (ℓ ^ (-(3 : ℝ))) *
            ENNReal.ofReal (thetaK ℓ s (p.1 - p.2) + thetaK ℓ s (p.1 + p.2))) := by
          rw [ENNReal.ofReal_mul hℓ3]
      _ = ENNReal.ofReal (W p.1 * W p.2) * (ENNReal.ofReal (ℓ ^ (-(3 : ℝ))) *
            (ENNReal.ofReal (thetaK ℓ s (p.1 - p.2))
              + ENNReal.ofReal (thetaK ℓ s (p.1 + p.2)))) := by
          rw [ENNReal.ofReal_add hb1 hb2]
      _ = ENNReal.ofReal (W p.1 * W p.2) *
            (ssbKimg ℓ s (p.1 - p.2) + ssbKimg ℓ s (p.1 + p.2)) := by
          rw [mul_add, ← ENNReal.ofReal_mul hℓ3, ← ENNReal.ofReal_mul hℓ3,
            ssb_ofReal_thetaK hℓ hs, ssb_ofReal_thetaK hℓ hs]
  have hfirst : ENNReal.ofReal (ℓ ^ (-(3 : ℝ)) * ∑ m ∈ S, (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2
        * Real.exp (-(s * ‖kvec ℓ m‖ ^ 2)))
      ≤ ENNReal.ofReal (ℓ ^ (-(3 : ℝ))) * ENNReal.ofReal ((1 / 2) * ∫ x, ∫ y,
          W x * W y * (thetaK ℓ s (x - y) + thetaK ℓ s (x + y))) := by
    rw [ENNReal.ofReal_mul hℓ3]
    gcongr
    exact hrow.trans_eq hident
  have hsecond : ENNReal.ofReal (ℓ ^ (-(3 : ℝ))) * ENNReal.ofReal ((1 / 2) * ∫ x, ∫ y,
        W x * W y * (thetaK ℓ s (x - y) + thetaK ℓ s (x + y)))
      ≤ ENNReal.ofReal (ℓ ^ (-(3 : ℝ))) * ((1 / 2 : ℝ≥0∞) * ∫⁻ x, ∫⁻ y,
          ENNReal.ofReal (W x * W y * (thetaK ℓ s (x - y) + thetaK ℓ s (x + y)))) := by
    gcongr
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      show ENNReal.ofReal ((1 / 2 : ℝ)) = (1 / 2 : ℝ≥0∞) from by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num]
    gcongr
    exact ssb_ofReal_iterated_le hg0 hgm
  have hthird : ENNReal.ofReal (ℓ ^ (-(3 : ℝ))) * ((1 / 2 : ℝ≥0∞) * ∫⁻ x, ∫⁻ y,
        ENNReal.ofReal (W x * W y * (thetaK ℓ s (x - y) + thetaK ℓ s (x + y))))
      = (1 / 2 : ℝ≥0∞) * ∫⁻ p : E3 × E3, ENNReal.ofReal (ℓ ^ (-(3 : ℝ))) *
          ENNReal.ofReal (W p.1 * W p.2 * (thetaK ℓ s (p.1 - p.2) + thetaK ℓ s (p.1 + p.2))) := by
    rw [lintegral_lintegral (f := fun x y : E3 => ENNReal.ofReal
      (W x * W y * (thetaK ℓ s (x - y) + thetaK ℓ s (x + y)))) hgm.ennreal_ofReal]
    rw [← mul_assoc, mul_comm (ENNReal.ofReal (ℓ ^ (-(3 : ℝ)))) (1 / 2 : ℝ≥0∞), mul_assoc,
      ← lintegral_const_mul' (ENNReal.ofReal (ℓ ^ (-(3 : ℝ))))
        (fun z : E3 × E3 => ENNReal.ofReal (W z.1 * W z.2 *
          (thetaK ℓ s (z.1 - z.2) + thetaK ℓ s (z.1 + z.2)))) ENNReal.ofReal_ne_top]
    rfl
  refine hfirst.trans (hsecond.trans ?_)
  rw [hthird, lintegral_congr key]

/-! ## 5. Null sets: the shift never vanishes -/

lemma ssb_ae_sub_add_ne_zero (c : E3) :
    ∀ᵐ p ∂(volume.prod volume), p.1 - p.2 + c ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  rw [show {p : E3 × E3 | ¬ (p.1 - p.2 + c ≠ 0)} = {p : E3 × E3 | p.2 = p.1 + c} by
    ext p
    simp only [Set.mem_ofPred_eq, not_not]
    constructor
    · intro h
      exact (calc p.1 + c = (p.1 - p.2 + c) + p.2 := by abel
        _ = 0 + p.2 := by rw [h]
        _ = p.2 := by rw [zero_add]).symm
    · intro h
      calc p.1 - p.2 + c = (p.1 + c) - p.2 := by abel
        _ = p.2 - p.2 := by rw [h]
        _ = 0 := by abel]
  calc (volume.prod volume) {p : E3 × E3 | p.2 = p.1 + c}
      = ∫⁻ x : E3, volume (Prod.mk x ⁻¹' {p : E3 × E3 | p.2 = p.1 + c}) :=
        MeasureTheory.Measure.prod_apply
          (measurableSet_eq_fun measurable_snd (measurable_fst.add measurable_const))
    _ = ∫⁻ _x : E3, (0 : ℝ≥0∞) := by
        refine lintegral_congr (fun x => ?_)
        have hsp : Prod.mk x ⁻¹' {p : E3 × E3 | p.2 = p.1 + c} = {x + c} := by
          ext y
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        rw [hsp, measure_singleton]
    _ = 0 := MeasureTheory.lintegral_zero

lemma ssb_ae_add_add_ne_zero (c : E3) :
    ∀ᵐ p ∂(volume.prod volume), p.1 + p.2 + c ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  rw [show {p : E3 × E3 | ¬ (p.1 + p.2 + c ≠ 0)} = {p : E3 × E3 | p.2 = -p.1 - c} by
    ext p
    simp only [Set.mem_ofPred_eq, not_not]
    constructor
    · intro h
      exact (calc -p.1 - c = -((p.1 + p.2 + c) - p.2) := by abel
        _ = -(0 - p.2) := by rw [h]
        _ = p.2 := by abel).symm
    · intro h
      calc p.1 + p.2 + c = (p.2 - (-p.1 - c)) := by abel
        _ = 0 := by rw [h]; abel]
  calc (volume.prod volume) {p : E3 × E3 | p.2 = -p.1 - c}
      = ∫⁻ x : E3, volume (Prod.mk x ⁻¹' {p : E3 × E3 | p.2 = -p.1 - c}) :=
        MeasureTheory.Measure.prod_apply
          (measurableSet_eq_fun measurable_snd ((measurable_fst.neg).sub measurable_const))
    _ = ∫⁻ _x : E3, (0 : ℝ≥0∞) := by
        refine lintegral_congr (fun x => ?_)
        have hsp : Prod.mk x ⁻¹' {p : E3 × E3 | p.2 = -p.1 - c} = {-x - c} := by
          ext y
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        rw [hsp, measure_singleton]
    _ = 0 := MeasureTheory.lintegral_zero

/-! ## 6. The `s`-integral of the pointwise bound -/

/-- **The `s`-integral of the pointwise bound**: Tonelli turns the `s`-integral of the pair form
into the pair integral of the per-`m` `s`-integrals of the image kernel. -/
lemma ssb_sIntegral_le {W : E3 → ℝ} {ℓ : ℝ} (hW : MeasureTheory.Integrable W)
    (hW0 : ∀ x, 0 ≤ W x) (hℓ : 0 < ℓ) (S : Finset (Fin 3 → ℤ)) :
    (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (ℓ ^ (-(3 : ℝ)) * ∑ m ∈ S,
        (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2 * Real.exp (-(s * ‖kvec ℓ m‖ ^ 2))))
      ≤ (1 / 2 : ℝ≥0∞) * ∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
          * ((∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 - p.2))
              + (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 + p.2))) := by
  have h1 : (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (ℓ ^ (-(3 : ℝ)) * ∑ m ∈ S,
        (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2 * Real.exp (-(s * ‖kvec ℓ m‖ ^ 2))))
      ≤ ∫⁻ s in Set.Ioc (0 : ℝ) 1, (1 / 2 : ℝ≥0∞) * ∫⁻ p : E3 × E3,
          ENNReal.ofReal (W p.1 * W p.2)
            * (ssbKimg ℓ s (p.1 - p.2) + ssbKimg ℓ s (p.1 + p.2)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
    exact ssb_pointwise hW hW0 hℓ S hs.1
  have hKms : ∀ z : E3, Measurable (fun s : ℝ => ssbKimg ℓ s z) := fun z =>
    (ssb_measurable_Kimg ℓ).comp (measurable_id.prodMk measurable_const)
  have hG : AEMeasurable (Function.uncurry (fun (s : ℝ) (p : E3 × E3) =>
      ENNReal.ofReal (W p.1 * W p.2)
        * (ssbKimg ℓ s (p.1 - p.2) + ssbKimg ℓ s (p.1 + p.2))))
      ((volume.restrict (Set.Ioc 0 1)).prod (volume.prod volume)) := by
    have hK1 : AEMeasurable (fun q : ℝ × (E3 × E3) => ssbKimg ℓ q.1 (q.2.1 - q.2.2))
        ((volume.restrict (Set.Ioc 0 1)).prod (volume.prod volume)) :=
      (((ssb_measurable_Kimg ℓ).comp
        (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).sub
          (measurable_snd.comp measurable_snd))))).aemeasurable
    have hK2 : AEMeasurable (fun q : ℝ × (E3 × E3) => ssbKimg ℓ q.1 (q.2.1 + q.2.2))
        ((volume.restrict (Set.Ioc 0 1)).prod (volume.prod volume)) :=
      (((ssb_measurable_Kimg ℓ).comp
        (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).add
          (measurable_snd.comp measurable_snd))))).aemeasurable
    have hWm : AEMeasurable (fun q : ℝ × (E3 × E3) => ENNReal.ofReal (W q.2.1 * W q.2.2))
        ((volume.restrict (Set.Ioc 0 1)).prod (volume.prod volume)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (((hW.aestronglyMeasurable.aemeasurable.comp_fst).comp_snd).mul
          ((hW.aestronglyMeasurable.aemeasurable.comp_snd).comp_snd))
    exact hWm.mul (hK1.add hK2)
  have hmain : (∫⁻ s in Set.Ioc (0 : ℝ) 1, ∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
        * (ssbKimg ℓ s (p.1 - p.2) + ssbKimg ℓ s (p.1 + p.2)))
      ≤ ∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
          * ((∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 - p.2))
              + (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 + p.2))) := by
    have hswap : (∫⁻ s in Set.Ioc (0 : ℝ) 1, ∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
        * (ssbKimg ℓ s (p.1 - p.2) + ssbKimg ℓ s (p.1 + p.2)))
        = ∫⁻ p : E3 × E3, ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (W p.1 * W p.2)
          * (ssbKimg ℓ s (p.1 - p.2) + ssbKimg ℓ s (p.1 + p.2)) :=
      MeasureTheory.lintegral_lintegral_swap (f := fun (s : ℝ) (p : E3 × E3) =>
        ENNReal.ofReal (W p.1 * W p.2) * (ssbKimg ℓ s (p.1 - p.2) + ssbKimg ℓ s (p.1 + p.2))) hG
    rw [hswap]
    refine lintegral_mono (fun p => ?_)
    rw [MeasureTheory.lintegral_const_mul'
      (ENNReal.ofReal (W p.1 * W p.2)) _ ENNReal.ofReal_ne_top,
      MeasureTheory.lintegral_add_left (hKms (p.1 - p.2)) _]
  refine h1.trans ?_
  rw [MeasureTheory.lintegral_const_mul' (1 / 2 : ℝ≥0∞) _ (by norm_num)]
  exact mul_le_mul_of_nonneg_left hmain (by positivity)

/-! ## 7. The per-`m` bounds -/

/-- The unshifted Coulomb double `∫⁻` is `ofReal` of the Bochner double integral. -/
lemma ssb_A0_eq {W : E3 → ℝ} (hW : MeasureTheory.Integrable W) (hW0 : ∀ x, 0 ≤ W x)
    (hcd : MeasureTheory.Integrable (fun p : E3 × E3 => W p.1 * W p.2 / ‖p.1 - p.2‖)) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖))
      = ENNReal.ofReal (∫ x, ∫ y, W x * W y / ‖x - y‖) := by
  have hnn : ∀ p : E3 × E3, 0 ≤ W p.1 * W p.2 / ‖p.1 - p.2‖ := fun p =>
    div_nonneg (mul_nonneg (hW0 p.1) (hW0 p.2)) (norm_nonneg _)
  have hm : AEMeasurable (Function.uncurry (fun x y : E3 => W x * W y / ‖x - y‖))
      (volume.prod volume) :=
    ((hW.aestronglyMeasurable.aemeasurable.comp_fst).mul
      (hW.aestronglyMeasurable.aemeasurable.comp_snd)).div (by fun_prop)
  have hprod : (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2 / ‖p.1 - p.2‖)) ≠ ⊤ := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hcd (Eventually.of_forall hnn)]
    exact ENNReal.ofReal_ne_top
  have hiter : (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2 / ‖p.1 - p.2‖))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖) := by
    rw [MeasureTheory.lintegral_lintegral
      (f := fun x y : E3 => ENNReal.ofReal (W x * W y / ‖x - y‖)) hm.ennreal_ofReal]
    rfl
  have hfin : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)) ≠ ⊤ := by
    rw [← hiter]; exact hprod
  rw [CoulShift.integral_integral_eq_toReal_lintegral
    (fun x y => div_nonneg (mul_nonneg (hW0 x) (hW0 y)) (norm_nonneg _)) hm hfin]
  exact (ENNReal.ofReal_toReal hfin).symm

/-- The inner `y`-substitution `y ↦ y + c` in the shifted Coulomb kernel. -/
lemma ssb_lintegral_shift (W : E3 → ℝ) (x c : E3) :
    (∫⁻ y : E3, ENNReal.ofReal (W x * W y / ‖x - y + c‖))
      = ∫⁻ y : E3, ENNReal.ofReal (W x * W (y + c) / ‖x - y‖) := by
  rw [← MeasureTheory.lintegral_add_right_eq_self
    (fun y : E3 => ENNReal.ofReal (W x * W y / ‖x - y + c‖)) c]
  refine lintegral_congr (fun y => ?_)
  rw [show x - (y + c) + c = x - y by abel]

/-- The pair `∫⁻` of `W ⊗ W` is `ofReal` of the square of the mass. -/
lemma ssb_pair_eq {W : E3 → ℝ} (hW : MeasureTheory.Integrable W) (hW0 : ∀ x, 0 ≤ W x) :
    (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2))
      = ENNReal.ofReal ((∫ x, W x) * ∫ x, W x) := by
  have hm : AEMeasurable (Function.uncurry (fun x y : E3 => ENNReal.ofReal (W x * W y)))
      (volume.prod volume) := by
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    exact ((hW.aestronglyMeasurable.aemeasurable.comp_fst).mul
      (hW.aestronglyMeasurable.aemeasurable.comp_snd))
  have hiter : (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y) := by
    rw [MeasureTheory.lintegral_lintegral
      (f := fun x y : E3 => ENNReal.ofReal (W x * W y)) hm]
    rfl
  rw [hiter]
  have hstep : ∀ x : E3, (∫⁻ y : E3, ENNReal.ofReal (W x * W y))
      = ENNReal.ofReal (W x * ∫ y, W y) := by
    intro x
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hW.const_mul (W x))
      (Eventually.of_forall (fun y => mul_nonneg (hW0 x) (hW0 y)))]
    congr 1
    rw [MeasureTheory.integral_const_mul]
  rw [lintegral_congr hstep]
  have hstep2 : (∫⁻ x : E3, ENNReal.ofReal (W x * ∫ y, W y))
      = ENNReal.ofReal ((∫ x, W x) * ∫ y, W y) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hW.mul_const _)
      (Eventually.of_forall (fun x => mul_nonneg (hW0 x) (integral_nonneg hW0)))]
    congr 1
    rw [MeasureTheory.integral_mul_const]
  rw [hstep2]

/-- **Near (and zero) image bound**: the shifted heat kernel contributes at most `D/(4π)`. -/
lemma ssb_term_near_le {W : E3 → ℝ} (hW : MeasureTheory.Integrable W) (hW0 : ∀ x, 0 ≤ W x)
    (hcd : MeasureTheory.Integrable (fun p : E3 × E3 => W p.1 * W p.2 / ‖p.1 - p.2‖))
    (c : E3) :
    (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (p.1 - p.2 + c))))
      ≤ ENNReal.ofReal ((∫ x, ∫ y, W x * W y / ‖x - y‖) / (4 * Real.pi)) := by
  have hae := ssb_ae_sub_add_ne_zero c
  have h1 : (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (p.1 - p.2 + c))))
      ≤ ∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
          * ENNReal.ofReal ((1 / (4 * Real.pi)) * (1 / ‖p.1 - p.2 + c‖)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with p hp
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (ssb_lintegral_Kt_Ioc_le hp).trans (le_of_eq ?_)
    rw [show 1 / (4 * Real.pi * ‖p.1 - p.2 + c‖)
        = (1 / (4 * Real.pi)) * (1 / ‖p.1 - p.2 + c‖) by ring]
  refine h1.trans ?_
  have h2 : (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
        * ENNReal.ofReal ((1 / (4 * Real.pi)) * (1 / ‖p.1 - p.2 + c‖)))
      = ENNReal.ofReal (1 / (4 * Real.pi))
        * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y + c‖) := by
    have hmap : (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
          * ENNReal.ofReal ((1 / (4 * Real.pi)) * (1 / ‖p.1 - p.2 + c‖)))
        = ∫⁻ p : E3 × E3, ENNReal.ofReal (1 / (4 * Real.pi)) * ENNReal.ofReal
            (W p.1 * W p.2 / ‖p.1 - p.2 + c‖) := by
      refine lintegral_congr (fun p => ?_)
      have ha : (0 : ℝ) ≤ W p.1 * W p.2 := mul_nonneg (hW0 p.1) (hW0 p.2)
      have hk : (0 : ℝ) ≤ 1 / (4 * Real.pi) := by positivity
      have hmid : W p.1 * W p.2 * (1 / (4 * Real.pi) * (1 / ‖p.1 - p.2 + c‖))
          = 1 / (4 * Real.pi) * (W p.1 * W p.2 * (1 / ‖p.1 - p.2 + c‖)) := by ring
      have heq : W p.1 * W p.2 * (1 / ‖p.1 - p.2 + c‖)
          = W p.1 * W p.2 / ‖p.1 - p.2 + c‖ := by ring
      rw [← ENNReal.ofReal_mul ha, hmid, ENNReal.ofReal_mul hk, heq]
    rw [hmap, MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    have hm : AEMeasurable (Function.uncurry (fun x y : E3 =>
        ENNReal.ofReal (W x * W y / ‖x - y + c‖))) (volume.prod volume) := by
      have h1' : AEMeasurable (fun p : E3 × E3 => W p.1) (volume.prod volume) :=
        hW.aestronglyMeasurable.aemeasurable.comp_fst
      have h2' : AEMeasurable (fun p : E3 × E3 => W p.2) (volume.prod volume) :=
        hW.aestronglyMeasurable.aemeasurable.comp_snd
      exact ENNReal.measurable_ofReal.comp_aemeasurable
        ((h1'.mul h2').div (by fun_prop))
    have hiter2 : (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2 / ‖p.1 - p.2 + c‖))
        = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y + c‖) := by
      rw [MeasureTheory.lintegral_lintegral (f := fun x y : E3 =>
        ENNReal.ofReal (W x * W y / ‖x - y + c‖)) hm]
      rfl
    exact hiter2
  have h3 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y + c‖))
      ≤ ENNReal.ofReal (∫ x, ∫ y, W x * W y / ‖x - y‖) := by
    calc (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y + c‖))
        = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W (y + c) / ‖x - y‖) :=
          lintegral_congr (fun x => ssb_lintegral_shift W x c)
      _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖) :=
          ssb_lintegral_coulomb_shift_le hW hW0 c
      _ = ENNReal.ofReal (∫ x, ∫ y, W x * W y / ‖x - y‖) := ssb_A0_eq hW hW0 hcd
  rw [h2]
  calc ENNReal.ofReal (1 / (4 * Real.pi))
        * (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y + c‖))
      ≤ ENNReal.ofReal (1 / (4 * Real.pi))
          * ENNReal.ofReal (∫ x, ∫ y, W x * W y / ‖x - y‖) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = ENNReal.ofReal ((∫ x, ∫ y, W x * W y / ‖x - y‖) / (4 * Real.pi)) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (4 * Real.pi))]
        congr 1
        ring

/-- **Far image bound**: far images decay Gaussianly. -/
lemma ssb_term_far_le {W : E3 → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 1 ≤ ℓ) (hRℓ : R ≤ ℓ)
    (hW : MeasureTheory.Integrable W) (hW0 : ∀ x, 0 ≤ W x)
    (hWs : tsupport W ⊆ Metric.ball 0 R) (m : Fin 3 → ℤ)
    (hm : m ≠ 0 ∧ ¬ (ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)) :
    (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (p.1 - p.2 + ℓ • vecZ m))))
      ≤ ENNReal.ofReal ((4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-((ℓ * ‖vecZ m‖ - 2 * R) ^ 2) / 4) * (∫ x, W x) ^ 2) := by
  have hnm : Real.sqrt 6 ≤ ℓ * ‖vecZ m‖ - 2 * R := by
    have := not_lt.mp hm.2
    linarith
  set cst : ℝ := (4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
    Real.exp (-((ℓ * ‖vecZ m‖ - 2 * R) ^ 2) / 4) with hcst
  have hcst0 : 0 ≤ cst := by
    rw [hcst]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
  have hfar : ∀ᵐ p ∂(volume.prod volume), ENNReal.ofReal (W p.1 * W p.2)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (p.1 - p.2 + ℓ • vecZ m)))
      ≤ ENNReal.ofReal (W p.1 * W p.2) * ENNReal.ofReal cst := by
    refine Eventually.of_forall (fun p => ?_)
    rcases eq_or_ne (W p.1 * W p.2) 0 with h0 | h0
    · rw [h0, ENNReal.ofReal_zero, zero_mul, zero_mul]
    · have h1 : W p.1 ≠ 0 := fun h => h0 (by rw [h, zero_mul])
      have h2 : W p.2 ≠ 0 := fun h => h0 (by rw [h, mul_zero])
      have hx : ‖p.1‖ < R := by
        have := hWs (subset_closure h1)
        simpa [Metric.mem_ball, dist_eq_norm] using this
      have hy : ‖p.2‖ < R := by
        have := hWs (subset_closure h2)
        simpa [Metric.mem_ball, dist_eq_norm] using this
      have hlt : ‖p.1 - p.2‖ < 2 * R := by
        calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
          _ < R + R := by linarith
          _ = 2 * R := by ring
      have hge : ℓ * ‖vecZ m‖ - 2 * R ≤ ‖p.1 - p.2 + ℓ • vecZ m‖ := by
        have hrev : ‖ℓ • vecZ m‖ - ‖-(p.1 - p.2)‖ ≤ ‖ℓ • vecZ m - (-(p.1 - p.2))‖ :=
          (le_abs_self _).trans (abs_norm_sub_norm_le _ _)
        rw [norm_neg] at hrev
        have hnorm : ‖ℓ • vecZ m‖ = ℓ * ‖vecZ m‖ := by
          rw [norm_smul, Real.norm_of_nonneg (le_of_lt (lt_of_lt_of_le one_pos hℓ))]
        rw [hnorm] at hrev
        have hsimp : ℓ • vecZ m - (-(p.1 - p.2)) = p.1 - p.2 + ℓ • vecZ m := by abel
        rw [hsimp] at hrev
        linarith
      have hsq : (ℓ * ‖vecZ m‖ - 2 * R) ^ 2 ≤ ‖p.1 - p.2 + ℓ • vecZ m‖ ^ 2 :=
        pow_le_pow_left₀ (by linarith [Real.sqrt_nonneg 6]) hge 2
      have h6 : (6 : ℝ) ≤ ‖p.1 - p.2 + ℓ • vecZ m‖ ^ 2 := by
        rw [← Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
        exact le_trans (pow_le_pow_left₀ (Real.sqrt_nonneg 6) hnm 2) hsq
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (ssb_lintegral_Kt_Ioc_far_le h6).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hcst]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      linarith [hsq]
  calc (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (p.1 - p.2 + ℓ • vecZ m))))
      ≤ ∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2) * ENNReal.ofReal cst :=
        lintegral_mono_ae hfar
    _ = ∫⁻ p : E3 × E3, ENNReal.ofReal cst * ENNReal.ofReal (W p.1 * W p.2) :=
        lintegral_congr (fun p => mul_comm _ _)
    _ = ENNReal.ofReal cst * ∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2) :=
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal cst * ENNReal.ofReal ((∫ x, W x) * ∫ x, W x) := by
        rw [ssb_pair_eq hW hW0]
    _ = ENNReal.ofReal (cst * (∫ x, W x) ^ 2) := by
        rw [← ENNReal.ofReal_mul hcst0]
        congr 1
        ring

/-- **Near (and zero) image bound for the `x+y` family.** -/
lemma ssb_term_near_add_le {W : E3 → ℝ} (hW : MeasureTheory.Integrable W) (hW0 : ∀ x, 0 ≤ W x)
    (hWe : ∀ x, W (-x) = W x)
    (hcd : MeasureTheory.Integrable (fun p : E3 × E3 => W p.1 * W p.2 / ‖p.1 - p.2‖))
    (c : E3) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (x + y + c))))
      ≤ ENNReal.ofReal ((∫ x, ∫ y, W x * W y / ‖x - y‖) / (4 * Real.pi)) := by
  have hsub : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (x + y + c))))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (x - y + c))) := by
    refine lintegral_congr (fun x => ?_)
    rw [← MeasureTheory.lintegral_neg_eq_self (f := fun y : E3 => ENNReal.ofReal (W x * W y)
      * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (x + y + c))))]
    refine lintegral_congr (fun y => ?_)
    rw [show x + -y + c = x - y + c by abel, hWe]
  rw [hsub]
  rw [MeasureTheory.lintegral_lintegral (f := fun x y : E3 => ENNReal.ofReal (W x * W y)
    * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (x - y + c)))) (by
      have h1' : AEMeasurable (fun p : E3 × E3 => W p.1) (volume.prod volume) :=
        hW.aestronglyMeasurable.aemeasurable.comp_fst
      have h2' : AEMeasurable (fun p : E3 × E3 => W p.2) (volume.prod volume) :=
        hW.aestronglyMeasurable.aemeasurable.comp_snd
      have h3' : AEMeasurable (fun p : E3 × E3 =>
          ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (p.1 - p.2 + c)))
          (volume.prod volume) :=
        (Measurable.lintegral_prod_left (by
          unfold Kt
          fun_prop :
          Measurable (Function.uncurry (fun (s : ℝ) (p : E3 × E3) =>
            ENNReal.ofReal (Kt s (p.1 - p.2 + c)))))).aemeasurable
      exact ((h1'.mul h2').ennreal_ofReal).mul h3')]
  exact ssb_term_near_le hW hW0 hcd c

/-- **Far image bound for the `x+y` family.** -/
lemma ssb_term_far_add_le {W : E3 → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 1 ≤ ℓ) (hRℓ : R ≤ ℓ)
    (hW : MeasureTheory.Integrable W) (hW0 : ∀ x, 0 ≤ W x) (hWe : ∀ x, W (-x) = W x)
    (hWs : tsupport W ⊆ Metric.ball 0 R) (m : Fin 3 → ℤ)
    (hm : m ≠ 0 ∧ ¬ (ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (x + y + ℓ • vecZ m))))
      ≤ ENNReal.ofReal ((4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-((ℓ * ‖vecZ m‖ - 2 * R) ^ 2) / 4) * (∫ x, W x) ^ 2) := by
  have hsub : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (x + y + ℓ • vecZ m))))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (x - y + ℓ • vecZ m))) := by
    refine lintegral_congr (fun x => ?_)
    rw [← MeasureTheory.lintegral_neg_eq_self (f := fun y : E3 => ENNReal.ofReal (W x * W y)
      * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (x + y + ℓ • vecZ m))))]
    refine lintegral_congr (fun y => ?_)
    rw [show x + -y + ℓ • vecZ m = x - y + ℓ • vecZ m by abel, hWe]
  rw [hsub]
  rw [MeasureTheory.lintegral_lintegral (f := fun x y : E3 => ENNReal.ofReal (W x * W y)
    * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (x - y + ℓ • vecZ m)))) (by
      have h1' : AEMeasurable (fun p : E3 × E3 => W p.1) (volume.prod volume) :=
        hW.aestronglyMeasurable.aemeasurable.comp_fst
      have h2' : AEMeasurable (fun p : E3 × E3 => W p.2) (volume.prod volume) :=
        hW.aestronglyMeasurable.aemeasurable.comp_snd
      have h3' : AEMeasurable (fun p : E3 × E3 =>
          ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (p.1 - p.2 + ℓ • vecZ m)))
          (volume.prod volume) :=
        (Measurable.lintegral_prod_left (by
          unfold Kt
          fun_prop :
          Measurable (Function.uncurry (fun (s : ℝ) (p : E3 × E3) =>
            ENNReal.ofReal (Kt s (p.1 - p.2 + ℓ • vecZ m)))))).aemeasurable
      exact ((h1'.mul h2').ennreal_ofReal).mul h3')]
  exact ssb_term_far_le hR hℓ hRℓ hW hW0 hWs m hm

/-! ## 8. Summability of the far tail and the lattice split -/

/-- Summability of the Gaussian lattice sum over `ℤ³` at scale `1/8`. -/
lemma ssb_summable_vecZ_gauss :
    Summable (fun m : Fin 3 → ℤ => Real.exp (-(‖vecZ m‖ ^ 2 / 8))) := by
  have h := ssb_summable_kvec_gauss (ℓ := 1) (s := 1 / (8 * (2 * Real.pi) ^ 2))
    one_pos (by positivity)
  refine h.congr (fun j => ?_)
  rw [norm_kvec (by norm_num : (0 : ℝ) ≤ 1)]
  congr 1
  field_simp

/-- The far tail of the image lattice is summable. -/
lemma ssb_summable_far {ℓ R : ℝ} (hℓ : 1 ≤ ℓ) (hR : 0 ≤ R) :
    Summable (fun m : {m : Fin 3 → ℤ // m ≠ 0 ∧ ¬ (ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)} =>
      Real.exp (-((ℓ * ‖vecZ m.1‖ - 2 * R) ^ 2) / 4)) := by
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le one_pos hℓ
  have hg := (ssb_summable_vecZ_gauss.mul_left (Real.exp (R ^ 2))).subtype
    (fun m : Fin 3 → ℤ => m ≠ 0 ∧ ¬ (ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6))
  refine Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) (fun m => ?_) hg
  simp only [Function.comp_apply]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : ℓ ^ 2 * ‖vecZ m.1‖ ^ 2 / 8 - R ^ 2 ≤ (ℓ * ‖vecZ m.1‖ - 2 * R) ^ 2 / 4 := by
    nlinarith [sq_nonneg (ℓ * ‖vecZ m.1‖ - 4 * R)]
  have h2 : ‖vecZ m.1‖ ^ 2 / 8 - R ^ 2 ≤ ℓ ^ 2 * ‖vecZ m.1‖ ^ 2 / 8 - R ^ 2 := by
    have h3 : ‖vecZ m.1‖ ^ 2 ≤ ℓ ^ 2 * ‖vecZ m.1‖ ^ 2 := by
      have h4 : (1 : ℝ) ≤ ℓ ^ 2 := by nlinarith
      calc ‖vecZ m.1‖ ^ 2 = 1 * ‖vecZ m.1‖ ^ 2 := by ring
        _ ≤ ℓ ^ 2 * ‖vecZ m.1‖ ^ 2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
    linarith
  linarith

/-- The far tail is bounded by `1000(1+R)³` in the `ℝ≥0∞` form. -/
lemma ssb_far_tsum_le {ℓ R : ℝ} (hℓ : 1 ≤ ℓ) (hR : 0 ≤ R) (hRℓ : R ≤ ℓ) :
    (∑' m : {m : Fin 3 → ℤ // m ≠ 0 ∧ ¬ (ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)},
      ENNReal.ofReal (Real.exp (-((ℓ * ‖vecZ m.1‖ - 2 * R) ^ 2) / 4)))
      ≤ ENNReal.ofReal (1000 * (1 + R) ^ 3) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => (Real.exp_pos _).le) (ssb_summable_far hℓ hR)]
  exact ENNReal.ofReal_le_ofReal (far_tail_le hℓ hR hRℓ)

/-! ## 9. The lattice split and the numerical assembly -/

/-- **The lattice split.**  A nonnegative lattice sum is dominated by its finite near part (plus
the `m = 0` term) and its far part. -/
lemma ssb_tsum_split {ℓ R : ℝ} {a : (Fin 3 → ℤ) → ℝ≥0∞} {N : Finset (Fin 3 → ℤ)}
    (hNm : ∀ m ∈ N, m ≠ 0 ∧ ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)
    (hNsub : ∀ m : Fin 3 → ℤ, m ≠ 0 → ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6 → m ∈ N) :
    (∑' m : Fin 3 → ℤ, a m) ≤ (∑ m ∈ N, a m) + a 0
      + (∑' m : {m : Fin 3 → ℤ // m ≠ 0 ∧ ¬ (ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)},
          a m.1) := by
  classical
  have hzero : (0 : Fin 3 → ℤ) ∉ N := fun h => (hNm 0 h).1 rfl
  have hPf : ∀ m : Fin 3 → ℤ,
      (m = 0 ∨ (m ≠ 0 ∧ ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6) →
        m ∈ N ∪ {(0 : Fin 3 → ℤ)}) := by
    intro m hm
    rcases hm with h | h
    · exact Finset.mem_union_right _ (by simp [h])
    · exact Finset.mem_union_left _ (hNsub m h.1 h.2)
  have hQg : ∀ m : Fin 3 → ℤ, ¬ (m = 0 ∨ (m ≠ 0 ∧ ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)) →
      m ≠ 0 ∧ ¬ (ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6) := by
    intro m hm
    refine ⟨fun h => hm (Or.inl h), fun h => hm (Or.inr ⟨?_, h⟩)⟩
    intro h0; exact hm (Or.inl h0)
  have hsplit : (∑' m : Fin 3 → ℤ, a m)
      = (∑' m : Fin 3 → ℤ,
          ({m : Fin 3 → ℤ | m = 0 ∨ (m ≠ 0 ∧ ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)}.indicator a) m)
        + (∑' m : Fin 3 → ℤ,
          ({m : Fin 3 → ℤ | ¬ (m = 0 ∨ (m ≠ 0 ∧ ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6))}.indicator a) m) := by
    rw [← ENNReal.tsum_add]
    refine tsum_congr (fun m => ?_)
    by_cases h : m ∈ {m : Fin 3 → ℤ | m = 0 ∨ (m ≠ 0 ∧ ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)}
    · have h2 : m ∉ {m : Fin 3 → ℤ |
          ¬ (m = 0 ∨ (m ≠ 0 ∧ ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6))} := by
        simp only [Set.mem_ofPred_eq, not_not] at h ⊢
        exact h
      rw [Set.indicator_of_mem h, Set.indicator_of_notMem h2]
      simp
    · have h2 : m ∈ {m : Fin 3 → ℤ |
          ¬ (m = 0 ∨ (m ≠ 0 ∧ ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6))} := by
        simp only [Set.mem_ofPred_eq] at h ⊢
        exact h
      rw [Set.indicator_of_notMem h, Set.indicator_of_mem h2]
      simp
  have hfirst : (∑' m : Fin 3 → ℤ,
        ({m : Fin 3 → ℤ | m = 0 ∨ (m ≠ 0 ∧ ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)}.indicator a) m)
      ≤ (∑ m ∈ N, a m) + a 0 := by
    have hfin : (∑' m : Fin 3 → ℤ,
          ({m : Fin 3 → ℤ | m = 0 ∨ (m ≠ 0 ∧ ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)}.indicator a) m)
        = ∑ m ∈ (N ∪ {(0 : Fin 3 → ℤ)}),
            ({m : Fin 3 → ℤ | m = 0 ∨ (m ≠ 0 ∧ ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)}.indicator a) m := by
      refine tsum_eq_sum (fun m hm => ?_)
      rw [Set.indicator_of_notMem]
      intro hmem
      exact hm (hPf m hmem)
    rw [hfin, Finset.sum_union (by simp [hzero])]
    have hsum0 : ({m : Fin 3 → ℤ | m = 0 ∨ (m ≠ 0 ∧ ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)}.indicator a)
        (0 : Fin 3 → ℤ) = a 0 := by
      rw [Set.indicator_of_mem (f := a) (show (0 : Fin 3 → ℤ) ∈ {m : Fin 3 → ℤ |
          m = 0 ∨ (m ≠ 0 ∧ ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)} from Or.inl rfl)]
    rw [Finset.sum_singleton, hsum0]
    refine add_le_add ?_ le_rfl
    refine le_of_eq ?_
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Set.indicator_of_mem (f := a) (show x ∈ {m : Fin 3 → ℤ |
        m = 0 ∨ (m ≠ 0 ∧ ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)} from Or.inr (hNm x hx))]
  have hsecond : (∑' m : Fin 3 → ℤ,
        ({m : Fin 3 → ℤ | ¬ (m = 0 ∨ (m ≠ 0 ∧ ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6))}.indicator a) m)
      ≤ (∑' m : {m : Fin 3 → ℤ // m ≠ 0 ∧ ¬ (ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)},
          a m.1) := by
    rw [← tsum_subtype {m : Fin 3 → ℤ | ¬ (m = 0 ∨ (m ≠ 0 ∧ ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6))} a]
    refine ENNReal.tsum_comp_le_tsum_of_injective (f := fun m :
        {m : Fin 3 → ℤ // ¬ (m = 0 ∨ (m ≠ 0 ∧ ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6))} =>
        (⟨m.1, hQg m.1 m.2⟩ : {m : Fin 3 → ℤ // m ≠ 0 ∧ ¬ (ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)}))
      (fun x y hxy => by
        have := Subtype.mk.injEq _ _ _ _ ▸ hxy
        exact Subtype.ext (by simpa using congrArg Subtype.val hxy))
      (fun m => a m.1)
  rw [hsplit]
  exact add_le_add hfirst hsecond

/-! ## 10. The core bound and the target -/

/-- The `x - y` family unfolding: the `s`-integral of the image kernel is the sum over the
lattice of the per-`m` `s`-integrals. -/
lemma ssb_Qpair_sub {W : E3 → ℝ} {ℓ : ℝ} (hW : MeasureTheory.Integrable W) :
    (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 - p.2)))
      = ∑' m : Fin 3 → ℤ, ∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
          * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (p.1 - p.2 + ℓ • vecZ m))) := by
  have hQ : ∀ z : E3, (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s z)
      = ∑' m : Fin 3 → ℤ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal (Kt s (z + ℓ • vecZ m)) := by
    intro z
    unfold ssbKimg
    rw [MeasureTheory.lintegral_tsum]
    intro m
    exact (ENNReal.measurable_ofReal.comp (by unfold Kt; fun_prop)).aemeasurable
  have hpt : ∀ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 - p.2))
      = ∑' m : Fin 3 → ℤ, ENNReal.ofReal (W p.1 * W p.2)
          * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (p.1 - p.2 + ℓ • vecZ m))) := by
    intro p
    rw [hQ (p.1 - p.2), ENNReal.tsum_mul_left]
  rw [lintegral_congr hpt, MeasureTheory.lintegral_tsum]
  intro m
  have hA : AEMeasurable (fun p : E3 × E3 => ∫⁻ s in Set.Ioc (0 : ℝ) 1,
      ENNReal.ofReal (Kt s (p.1 - p.2 + ℓ • vecZ m))) (volume.prod volume) :=
    (Measurable.lintegral_prod_left (by unfold Kt; fun_prop :
      Measurable (Function.uncurry (fun (s : ℝ) (p : E3 × E3) =>
        ENNReal.ofReal (Kt s (p.1 - p.2 + ℓ • vecZ m)))))).aemeasurable
  exact ((hW.aestronglyMeasurable.aemeasurable.comp_fst).mul
    (hW.aestronglyMeasurable.aemeasurable.comp_snd)).ennreal_ofReal.mul hA

/-- The `x + y` family unfolding, in iterated form. -/
lemma ssb_Qpair_add {W : E3 → ℝ} {ℓ : ℝ} (hW : MeasureTheory.Integrable W) :
    (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 + p.2)))
      = ∑' m : Fin 3 → ℤ, ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y)
          * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (x + y + ℓ • vecZ m))) := by
  have hQ : ∀ z : E3, (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s z)
      = ∑' m : Fin 3 → ℤ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal (Kt s (z + ℓ • vecZ m)) := by
    intro z
    unfold ssbKimg
    rw [MeasureTheory.lintegral_tsum]
    intro m
    exact (ENNReal.measurable_ofReal.comp (by unfold Kt; fun_prop)).aemeasurable
  have hpt : ∀ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 + p.2))
      = ∑' m : Fin 3 → ℤ, ENNReal.ofReal (W p.1 * W p.2)
          * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (p.1 + p.2 + ℓ • vecZ m))) := by
    intro p
    rw [hQ (p.1 + p.2), ENNReal.tsum_mul_left]
  rw [lintegral_congr hpt, MeasureTheory.lintegral_tsum]
  · refine tsum_congr (fun m => ?_)
    refine (MeasureTheory.lintegral_lintegral (f := fun x y : E3 => ENNReal.ofReal (W x * W y)
      * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (x + y + ℓ • vecZ m)))) ?_).symm
    have h1 : AEMeasurable (fun p : E3 × E3 => W p.1) (volume.prod volume) :=
        hW.aestronglyMeasurable.aemeasurable.comp_fst
    have h2 : AEMeasurable (fun p : E3 × E3 => W p.2) (volume.prod volume) :=
      hW.aestronglyMeasurable.aemeasurable.comp_snd
    have h3 : AEMeasurable (fun p : E3 × E3 => ∫⁻ s in Set.Ioc (0 : ℝ) 1,
        ENNReal.ofReal (Kt s (p.1 + p.2 + ℓ • vecZ m))) (volume.prod volume) :=
      (Measurable.lintegral_prod_left (by unfold Kt; fun_prop :
        Measurable (Function.uncurry (fun (s : ℝ) (p : E3 × E3) =>
          ENNReal.ofReal (Kt s (p.1 + p.2 + ℓ • vecZ m)))))).aemeasurable
    exact ((h1.mul h2).ennreal_ofReal).mul h3
  · intro m
    have hA : AEMeasurable (fun p : E3 × E3 => ∫⁻ s in Set.Ioc (0 : ℝ) 1,
        ENNReal.ofReal (Kt s (p.1 + p.2 + ℓ • vecZ m))) (volume.prod volume) :=
      (Measurable.lintegral_prod_left (by unfold Kt; fun_prop :
        Measurable (Function.uncurry (fun (s : ℝ) (p : E3 × E3) =>
          ENNReal.ofReal (Kt s (p.1 + p.2 + ℓ • vecZ m)))))).aemeasurable
    exact ((hW.aestronglyMeasurable.aemeasurable.comp_fst).mul
      (hW.aestronglyMeasurable.aemeasurable.comp_snd)).ennreal_ofReal.mul hA

/-- **The small-`s` lattice row**, for a pointwise nonnegative kernel. -/
theorem ssb_core {W : E3 → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ1 : 1 ≤ ℓ) (hRℓ : R ≤ ℓ)
    (hW : MeasureTheory.Integrable W) (hW0 : ∀ x, 0 ≤ W x) (hWe : ∀ x, W (-x) = W x)
    (hWs : tsupport W ⊆ Metric.ball 0 R)
    (hcd : MeasureTheory.Integrable (fun p : E3 × E3 => W p.1 * W p.2 / ‖p.1 - p.2‖))
    (S : Finset (Fin 3 → ℤ)) :
    ℓ ^ (-(3 : ℝ)) * (∫ s in Set.Ioc (0 : ℝ) 1, ∑ m ∈ S,
        (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2 * Real.exp (-(s * ‖kvec ℓ m‖ ^ 2)))
      ≤ (10 ^ 6 * (1 + R) ^ 4) * ((∫ x, ∫ y, W x * W y / ‖x - y‖) + (∫ x, W x) ^ 2) := by
  classical
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le one_pos hℓ1
  have hR0 : 0 ≤ R := hR.le
  obtain ⟨N, hNm, hNsub, hNcard⟩ := near_set_finite hℓ1 hRℓ
  set D : ℝ := ∫ x, ∫ y, W x * W y / ‖x - y‖ with hD
  set M : ℝ := ∫ x, W x with hM
  have hD0 : 0 ≤ D := by
    rw [hD]
    exact integral_nonneg (fun x => integral_nonneg (fun y =>
      div_nonneg (mul_nonneg (hW0 x) (hW0 y)) (norm_nonneg _)))
  have hM0 : 0 ≤ M := by rw [hM]; exact integral_nonneg hW0
  have hcard : ((N.card : ℕ) : ℝ≥0∞) ≤ 1000 := by exact_mod_cast hNcard
  set a : (Fin 3 → ℤ) → ℝ≥0∞ := fun m => ∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
      * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (p.1 - p.2 + ℓ • vecZ m))) with ha
  set b : (Fin 3 → ℤ) → ℝ≥0∞ := fun m => ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y)
      * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Kt s (x + y + ℓ • vecZ m))) with hb
  have hfar1 : (4 * Real.pi) ^ (-(3 / 2 : ℝ)) ≤ 1 := by
    have h1 : (1 : ℝ) ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
    rw [Real.rpow_neg (by linarith [h1] : (0 : ℝ) ≤ 4 * Real.pi)]
    exact inv_le_one_of_one_le₀ (by
      calc (1 : ℝ) = (4 * Real.pi) ^ (0 : ℝ) := (Real.rpow_zero _).symm
        _ ≤ (4 * Real.pi) ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by norm_num))
  -- the far sums, for the two families
  have hfar_common : ∀ (c : (Fin 3 → ℤ) → ℝ≥0∞)
      (hc : ∀ m : {m : Fin 3 → ℤ // m ≠ 0 ∧ ¬ (ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)},
        c m.1 ≤ ENNReal.ofReal ((4 * Real.pi) ^ (-(3 / 2 : ℝ))
          * Real.exp (-((ℓ * ‖vecZ m.1‖ - 2 * R) ^ 2) / 4) * M ^ 2)),
      (∑' m : {m : Fin 3 → ℤ // m ≠ 0 ∧ ¬ (ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)}, c m.1)
        ≤ ENNReal.ofReal (1000 * (1 + R) ^ 3 * M ^ 2) := by
    intro c hc
    refine le_trans (ENNReal.tsum_le_tsum hc) ?_
    have hte : (∑' m : {m : Fin 3 → ℤ // m ≠ 0 ∧ ¬ (ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)},
          ENNReal.ofReal ((4 * Real.pi) ^ (-(3 / 2 : ℝ))
            * Real.exp (-((ℓ * ‖vecZ m.1‖ - 2 * R) ^ 2) / 4) * M ^ 2))
        = (∑' m : {m : Fin 3 → ℤ // m ≠ 0 ∧ ¬ (ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)},
            ENNReal.ofReal (Real.exp (-((ℓ * ‖vecZ m.1‖ - 2 * R) ^ 2) / 4)))
          * ENNReal.ofReal ((4 * Real.pi) ^ (-(3 / 2 : ℝ)) * M ^ 2) := by
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr (fun m => ?_)
      have he : (4 * Real.pi) ^ (-(3 / 2 : ℝ))
            * Real.exp (-((ℓ * ‖vecZ m.1‖ - 2 * R) ^ 2) / 4) * M ^ 2
          = Real.exp (-((ℓ * ‖vecZ m.1‖ - 2 * R) ^ 2) / 4)
            * ((4 * Real.pi) ^ (-(3 / 2 : ℝ)) * M ^ 2) := by ring
      have hpos : (0 : ℝ) ≤ Real.exp (-((ℓ * ‖vecZ m.1‖ - 2 * R) ^ 2) / 4) := by positivity
      rw [he, ENNReal.ofReal_mul hpos]
    rw [hte]
    refine le_trans (mul_le_mul_left (ssb_far_tsum_le hℓ1 hR0 hRℓ) _) ?_
    have hk1 : (0 : ℝ) ≤ 1000 * (1 + R) ^ 3 := by positivity
    have hk2 : (0 : ℝ) ≤ (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * M ^ 2 := by positivity
    rw [← ENNReal.ofReal_mul hk1]
    refine ENNReal.ofReal_le_ofReal ?_
    have hM2 : (0 : ℝ) ≤ M ^ 2 := sq_nonneg M
    have hstep : (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * M ^ 2 ≤ 1 * M ^ 2 :=
      mul_le_mul_of_nonneg_right hfar1 hM2
    calc 1000 * (1 + R) ^ 3 * ((4 * Real.pi) ^ (-(3 / 2 : ℝ)) * M ^ 2)
        ≤ 1000 * (1 + R) ^ 3 * (1 * M ^ 2) := mul_le_mul_of_nonneg_left hstep hk1
      _ = 1000 * (1 + R) ^ 3 * M ^ 2 := by ring
  -- numeric endgame helper
  have hnum : 1001 * (D / (4 * Real.pi)) + 1000 * (1 + R) ^ 3 * M ^ 2
      ≤ 10 ^ 6 * (1 + R) ^ 4 * (D + M ^ 2) := by
    have h1R : (1 : ℝ) ≤ 1 + R := by linarith
    have h14 : (1 : ℝ) ≤ (1 + R) ^ 4 := one_le_pow₀ h1R
    have hA : 1001 * (D / (4 * Real.pi)) ≤ 10 ^ 6 * D := by
      rw [show 1001 * (D / (4 * Real.pi)) = (1001 / (4 * Real.pi)) * D by ring]
      refine mul_le_mul_of_nonneg_right ?_ hD0
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three]
    have hB : 1000 * (1 + R) ^ 3 * M ^ 2 ≤ 10 ^ 6 * (1 + R) ^ 4 * M ^ 2 := by
      have hM2' : (0 : ℝ) ≤ M ^ 2 := sq_nonneg M
      have hfac : 1000 * (1 + R) ^ 3 ≤ 10 ^ 6 * (1 + R) ^ 4 := by
        have h34 : (1 + R) ^ 3 ≤ (1 + R) ^ 4 :=
          pow_le_pow_right₀ h1R (by norm_num : (3 : ℕ) ≤ 4)
        have h13 : (1 : ℝ) ≤ (1 + R) ^ 3 := one_le_pow₀ h1R
        nlinarith
      exact mul_le_mul_of_nonneg_right hfac hM2'
    calc 1001 * (D / (4 * Real.pi)) + 1000 * (1 + R) ^ 3 * M ^ 2
        ≤ 10 ^ 6 * D + 10 ^ 6 * (1 + R) ^ 4 * M ^ 2 := add_le_add hA hB
      _ ≤ 10 ^ 6 * (1 + R) ^ 4 * D + 10 ^ 6 * (1 + R) ^ 4 * M ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_right (by nlinarith [h14]) hD0) le_rfl
      _ = 10 ^ 6 * (1 + R) ^ 4 * (D + M ^ 2) := by ring
  -- ### the two families
  have hkey : ∀ r : ℝ, ENNReal.ofReal (1000 * r) = 1000 * ENNReal.ofReal r := by
    intro r
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ (1000 : ℝ))]
    norm_num
  have hcombine : ∀ (X : ℝ≥0∞),
      X ≤ ENNReal.ofReal (1000 * (D / (4 * Real.pi))) + ENNReal.ofReal (D / (4 * Real.pi))
          + ENNReal.ofReal (1000 * (1 + R) ^ 3 * M ^ 2) →
      X ≤ ENNReal.ofReal (1001 * (D / (4 * Real.pi)) + 1000 * (1 + R) ^ 3 * M ^ 2) := by
    have hDpi : (0 : ℝ) ≤ D / (4 * Real.pi) := div_nonneg hD0 (by positivity)
    have hfar0 : (0 : ℝ) ≤ 1000 * (1 + R) ^ 3 * M ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by linarith [hR0]) 3)) (sq_nonneg M)
    have hkey2 : 1000 * (D / (4 * Real.pi)) + D / (4 * Real.pi)
        = 1001 * (D / (4 * Real.pi)) := by ring
    have hAeq : ENNReal.ofReal (1000 * (D / (4 * Real.pi))) + ENNReal.ofReal (D / (4 * Real.pi))
        = ENNReal.ofReal (1001 * (D / (4 * Real.pi))) := by
      rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1000) hDpi) hDpi, hkey2]
    have hBeq : ENNReal.ofReal (1001 * (D / (4 * Real.pi)))
          + ENNReal.ofReal (1000 * (1 + R) ^ 3 * M ^ 2)
        = ENNReal.ofReal (1001 * (D / (4 * Real.pi)) + 1000 * (1 + R) ^ 3 * M ^ 2) :=
      (ENNReal.ofReal_add (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1001) hDpi) hfar0).symm
    intro X hX
    refine hX.trans (le_of_eq ?_)
    calc ENNReal.ofReal (1000 * (D / (4 * Real.pi))) + ENNReal.ofReal (D / (4 * Real.pi))
            + ENNReal.ofReal (1000 * (1 + R) ^ 3 * M ^ 2)
        = (ENNReal.ofReal (1000 * (D / (4 * Real.pi))) + ENNReal.ofReal (D / (4 * Real.pi)))
            + ENNReal.ofReal (1000 * (1 + R) ^ 3 * M ^ 2) := rfl
      _ = ENNReal.ofReal (1001 * (D / (4 * Real.pi)))
            + ENNReal.ofReal (1000 * (1 + R) ^ 3 * M ^ 2) := by rw [hAeq]
      _ = ENNReal.ofReal (1001 * (D / (4 * Real.pi)) + 1000 * (1 + R) ^ 3 * M ^ 2) := hBeq
  have hA1 : (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 - p.2)))
      ≤ ENNReal.ofReal (1001 * (D / (4 * Real.pi)) + 1000 * (1 + R) ^ 3 * M ^ 2) := by
    have hna : (∑ m ∈ N, a m) ≤ ENNReal.ofReal (1000 * (D / (4 * Real.pi))) := by
      refine le_trans (Finset.sum_le_sum (fun m _ =>
        ssb_term_near_le hW hW0 hcd (ℓ • vecZ m))) ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      refine le_trans (mul_le_mul_left hcard _) ?_
      exact le_of_eq (hkey _).symm
    have h0 : a 0 ≤ ENNReal.ofReal (D / (4 * Real.pi)) := by
      rw [ha]
      simpa using ssb_term_near_le hW hW0 hcd (0 : E3)
    have hfa : (∑' m : {m : Fin 3 → ℤ // m ≠ 0 ∧ ¬ (ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)},
        a m.1) ≤ ENNReal.ofReal (1000 * (1 + R) ^ 3 * M ^ 2) :=
      hfar_common a (fun m => ssb_term_far_le hR hℓ1 hRℓ hW hW0 hWs m.1 m.2)
    rw [ssb_Qpair_sub hW]
    refine le_trans (ssb_tsum_split hNm hNsub)
      (hcombine _ (add_le_add (add_le_add hna h0) hfa))
  have hA2 : (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 + p.2)))
      ≤ ENNReal.ofReal (1001 * (D / (4 * Real.pi)) + 1000 * (1 + R) ^ 3 * M ^ 2) := by
    have hna : (∑ m ∈ N, b m) ≤ ENNReal.ofReal (1000 * (D / (4 * Real.pi))) := by
      refine le_trans (Finset.sum_le_sum (fun m _ =>
        ssb_term_near_add_le hW hW0 hWe hcd (ℓ • vecZ m))) ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      refine le_trans (mul_le_mul_left hcard _) ?_
      exact le_of_eq (hkey _).symm
    have h0 : b 0 ≤ ENNReal.ofReal (D / (4 * Real.pi)) := by
      rw [hb]
      simpa using ssb_term_near_add_le hW hW0 hWe hcd (0 : E3)
    have hfa : (∑' m : {m : Fin 3 → ℤ // m ≠ 0 ∧ ¬ (ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6)},
        b m.1) ≤ ENNReal.ofReal (1000 * (1 + R) ^ 3 * M ^ 2) :=
      hfar_common b (fun m => ssb_term_far_add_le hR hℓ1 hRℓ hW hW0 hWe hWs m.1 m.2)
    rw [ssb_Qpair_add hW]
    refine le_trans (ssb_tsum_split hNm hNsub)
      (hcombine _ (add_le_add (add_le_add hna h0) hfa))
  -- ### the `s`-integral and the conclusion
  have hstep : (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (ℓ ^ (-(3 : ℝ)) * ∑ m ∈ S,
        (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2 * Real.exp (-(s * ‖kvec ℓ m‖ ^ 2))))
      ≤ ENNReal.ofReal (1001 * (D / (4 * Real.pi)) + 1000 * (1 + R) ^ 3 * M ^ 2) := by
    have hQ1m : AEMeasurable (fun p : E3 × E3 => ENNReal.ofReal (W p.1 * W p.2)
        * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 - p.2))) (volume.prod volume) := by
      refine AEMeasurable.mul ?_ ?_
      · exact ((hW.aestronglyMeasurable.aemeasurable.comp_fst).mul
          (hW.aestronglyMeasurable.aemeasurable.comp_snd)).ennreal_ofReal
      · have hm : Measurable (fun p : E3 × E3 =>
            ∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 - p.2)) :=
          Measurable.lintegral_prod_left (f := fun (q : ℝ) (p : E3 × E3) =>
            ssbKimg ℓ q (p.1 - p.2))
            ((ssb_measurable_Kimg ℓ).comp (measurable_fst.prodMk
              ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))))
        exact hm.aemeasurable
    have hdist : (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
          * ((∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 - p.2))
              + (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 + p.2))))
        = (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
              * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 - p.2)))
          + (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2)
              * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 + p.2))) := by
      have hfun : (fun p : E3 × E3 => ENNReal.ofReal (W p.1 * W p.2)
            * ((∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 - p.2))
              + (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 + p.2))))
          = fun p : E3 × E3 => ENNReal.ofReal (W p.1 * W p.2)
              * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 - p.2))
            + ENNReal.ofReal (W p.1 * W p.2)
              * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 + p.2)) := by
        funext p
        ring
      rw [hfun]
      exact MeasureTheory.lintegral_add_left' (f := fun p : E3 × E3 =>
        ENNReal.ofReal (W p.1 * W p.2)
          * (∫⁻ s in Set.Ioc (0 : ℝ) 1, ssbKimg ℓ s (p.1 - p.2))) hQ1m _
    refine (ssb_sIntegral_le hW hW0 hℓ0 S).trans ?_
    rw [hdist]
    refine le_trans (mul_le_mul_of_nonneg_left (add_le_add hA1 hA2) (by norm_num)) ?_
    have hX : (1 / 2 : ℝ≥0∞)
          * ENNReal.ofReal (1001 * (D / (4 * Real.pi)) + 1000 * (1 + R) ^ 3 * M ^ 2)
        = ENNReal.ofReal (1001 * (D / (4 * Real.pi)) + 1000 * (1 + R) ^ 3 * M ^ 2) / 2 := by
      rw [one_div, ENNReal.div_eq_inv_mul]
    rw [mul_add, hX, ENNReal.add_halves]
  -- the Bochner/`∫⁻` conversion
  have hLHS : ℓ ^ (-(3 : ℝ)) * (∫ s in Set.Ioc (0 : ℝ) 1, ∑ m ∈ S,
        (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2 * Real.exp (-(s * ‖kvec ℓ m‖ ^ 2)))
      = (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (ℓ ^ (-(3 : ℝ)) * ∑ m ∈ S,
          (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2 * Real.exp (-(s * ‖kvec ℓ m‖ ^ 2)))).toReal := by
    have hFnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] (fun s : ℝ => ∑ m ∈ S,
        (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2 * Real.exp (-(s * ‖kvec ℓ m‖ ^ 2))) :=
      Eventually.of_forall (fun s =>
        Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))
    have hFm : AEStronglyMeasurable (fun s : ℝ => ∑ m ∈ S,
        (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2 * Real.exp (-(s * ‖kvec ℓ m‖ ^ 2)))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      fun_prop
    rw [integral_eq_lintegral_of_nonneg_ae hFnn hFm]
    have hsplit : (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (ℓ ^ (-(3 : ℝ)) * ∑ m ∈ S,
          (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2 * Real.exp (-(s * ‖kvec ℓ m‖ ^ 2))))
        = ENNReal.ofReal (ℓ ^ (-(3 : ℝ))) * (∫⁻ s in Set.Ioc (0 : ℝ) 1,
            ENNReal.ofReal (∑ m ∈ S,
              (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2 * Real.exp (-(s * ‖kvec ℓ m‖ ^ 2)))) := by
      rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr (fun s => ?_)
      exact ENNReal.ofReal_mul (Real.rpow_nonneg hℓ0.le _)
    rw [hsplit, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hℓ0.le _)]
  rw [hLHS]
  refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hstep) ?_
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact hnum

/-- **The small-`s` lattice row** (the target statement). -/
theorem small_s_bound {W : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ1 : 1 ≤ ℓ)
    (hRℓ : R ≤ ℓ)
    (hW : MeasureTheory.Integrable W) (hW0 : ∀ᵐ x, 0 ≤ W x)
    (hWe : ∀ x, W (-x) = W x)
    (hWs : tsupport W ⊆ Metric.ball 0 R)
    (hcd : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      W p.1 * W p.2 / ‖p.1 - p.2‖))
    (S : Finset (Fin 3 → ℤ)) (hS : ∀ m ∈ S, m ≠ 0) :
    ℓ ^ (-(3 : ℝ)) * (∫ s in Set.Ioc (0 : ℝ) 1,
        ∑ m ∈ S, (Work.BoseFixR.chat W (Work.BoseRowsFS.kvec ℓ m)) ^ 2
          * Real.exp (-(s * ‖Work.BoseRowsFS.kvec ℓ m‖ ^ 2)))
      ≤ (10 ^ 6 * (1 + R) ^ 4) *
          ((∫ x, ∫ y, W x * W y / ‖x - y‖) + (∫ x, W x) ^ 2) := by
  -- reduce to the pointwise positive representative `W⁺ = max W 0`
  set V : E3 → ℝ := fun x => max (W x) 0 with hV
  have hVW : V =ᵐ[volume] W := hW0.mono (fun x hx => by simp only [hV, max_eq_left hx])
  have hV0 : ∀ x, 0 ≤ V x := fun x => le_max_right _ _
  have hVI : MeasureTheory.Integrable V := hW.congr hVW.symm
  have hVe : ∀ x, V (-x) = V x := fun x => by simp only [hV, hWe x]
  have hVs : tsupport V ⊆ Metric.ball 0 R :=
    closure_mono (fun x hx => by
      simp only [Function.mem_support] at hx ⊢
      exact fun h => hx (by simp only [hV, h, max_self])) |>.trans hWs
  have hVcd : MeasureTheory.Integrable (fun p : E3 × E3 => V p.1 * V p.2 / ‖p.1 - p.2‖) := by
    refine MeasureTheory.Integrable.mono' hcd.norm ?_ ?_
    · have hm : AEMeasurable (fun p : E3 × E3 => V p.1 * V p.2 / ‖p.1 - p.2‖)
          (volume.prod volume) := by
        have h1 : AEMeasurable (fun p : E3 × E3 => V p.1) (volume.prod volume) :=
          hVI.aestronglyMeasurable.aemeasurable.comp_fst
        have h2 : AEMeasurable (fun p : E3 × E3 => V p.2) (volume.prod volume) :=
          hVI.aestronglyMeasurable.aemeasurable.comp_snd
        exact (h1.mul h2).div (by fun_prop)
      exact hm.aestronglyMeasurable
    · filter_upwards with p
      have h1 : |V p.1| ≤ |W p.1| := by
        rw [hV, abs_of_nonneg (le_max_right _ _)]
        exact max_le (le_abs_self _) (abs_nonneg _)
      have h2 : |V p.2| ≤ |W p.2| := by
        rw [hV, abs_of_nonneg (le_max_right _ _)]
        exact max_le (le_abs_self _) (abs_nonneg _)
      have hWn : ‖W p.1 * W p.2 / ‖p.1 - p.2‖‖
          = |W p.1| * |W p.2| / ‖p.1 - p.2‖ := by
        rw [Real.norm_eq_abs, abs_div, abs_mul,
          abs_of_nonneg (norm_nonneg (p.1 - p.2))]
      have hVn : ‖V p.1 * V p.2 / ‖p.1 - p.2‖‖
          = |V p.1| * |V p.2| / ‖p.1 - p.2‖ := by
        rw [Real.norm_eq_abs, abs_div, abs_mul,
          abs_of_nonneg (norm_nonneg (p.1 - p.2))]
      rw [hWn, hVn]
      exact div_le_div_of_nonneg_right
        (mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)) (norm_nonneg (p.1 - p.2))
  have hchat : ∀ k : E3, Work.BoseFixR.chat V k = Work.BoseFixR.chat W k :=
    fun k => Work.BoseB7AK.C3Q.chat_congr_ae hVW k
  have hD : (∫ x, ∫ y, V x * V y / ‖x - y‖) = ∫ x, ∫ y, W x * W y / ‖x - y‖ := by
    refine integral_congr_ae ?_
    filter_upwards [hVW] with x hx
    refine integral_congr_ae ?_
    filter_upwards [hVW] with y hy
    rw [hx, hy]
  have hM : (∫ x, V x) = ∫ x, W x := integral_congr_ae hVW
  rw [← hD, ← hM]
  simp only [← hchat]
  exact ssb_core hR hℓ1 hRℓ hVI hV0 hVe hVs hVcd S

end Work.BoseRowsFS
