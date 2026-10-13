/-
Copyright: work module for the Elgindi finite-time singularity project.

# Honesty of the angular pairings: `IPMem` for the mixed products

`IPMem g h` (AngSecond/Defs.lean) is the honesty of the weighted pairing
`IP g h = ∫_z ∫_θ g z θ * h z θ * w z² * σ θ`: the integrand is integrable slicewise in `θ`
and then the slice integrals are integrable in `z`.  The I₁ computation of §7 of
Elgindi, Annals 194 (3) 2021, pairs *different* functions -- `G`, `Φ`, `H` and the weighted
`cw · Φ` -- so it needs `IPMem` for mixed pairs, while the natural input is only the honesty of
the diagonal pairings `IPMem g g`, `IPMem h h`.

The bridge is the elementary inequality `2|ab| ≤ a² + b²`: for `κ = w z² σ θ ≥ 0`,
`|g h κ| ≤ (g²κ + h²κ)/2`, so `IPMem g g ∧ IPMem h h` gives `IPMem g h` for smooth `g h`.  The
same argument with the bounded factor `cw` gives `IPMem (cw · Φ) (cw · Φ)`.

Main results of this file:

* `IPMem_of_diag_smooth` -- mixed honesty from the two diagonal honesties for smooth profiles;
* `IPMem_cw_mul_diag` -- `IPMem (cw · g) (cw · g)` from `IPMem g g` (`|cw| ≤ 2` on `[0,∞)`);
* `I1_honesty` -- the four pairings needed by the `I₁` computation.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.AngSecond.I1_defs
import Submission.Work.FTS.EllipticEst.AngSecond.IP_abs_le_of_mem
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.AngSecond

open Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## Elementary pieces -/

/-- The open quadrant `(0,∞) × (0,π/2)` is contained in the open set `nbhU` on which
`SmoothNbhd` is stated. -/
private theorem quadrant_subset_nbhU :
    Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) ⊆ Work.Spaces.nbhU :=
  Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num))
    (Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos]))

/-- The radial weight `w2 z = w z ^ 2` is measurable (as a rational function of `z`). -/
private theorem measurable_w2 : Measurable w2 := by
  change Measurable (fun z : ℝ => (((1 + z) ^ 2) / z ^ 2) ^ 2)
  fun_prop

/-- The weight `(z, θ) ↦ w2 z * σ θ` is jointly measurable. -/
private theorem measurable_w2_mul_sig :
    Measurable (fun p : ℝ × ℝ => w2 p.1 * sig p.2) :=
  (measurable_w2.comp measurable_fst).mul (measurable_sig.comp measurable_snd)

/-- **AM–GM domination.**  If `F²κ` and `G²κ` are integrable on `s` and `κ ≥ 0` on `s`, then
`F G κ` is integrable on `s`:  pointwise `|F G κ| ≤ (F²κ + G²κ)/2`. -/
theorem integrableOn_mul_of_sq_aux {s : Set ℝ} (hs : MeasurableSet s) {F G κ : ℝ → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict s))
    (hG : AEStronglyMeasurable G (volume.restrict s))
    (hκm : Measurable κ) (hκnn : ∀ θ ∈ s, 0 ≤ κ θ)
    (hF2 : IntegrableOn (fun θ => F θ * F θ * κ θ) s)
    (hG2 : IntegrableOn (fun θ => G θ * G θ * κ θ) s) :
    IntegrableOn (fun θ => F θ * G θ * κ θ) s := by
  refine ((hF2.add hG2).mul_const (1 / 2)).mono'
    ((hF.mul hG).mul hκm.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_of_forall_mem hs hκnn] with θ hθ
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hθ]
  have hAM : 2 * (|F θ| * |G θ|) ≤ F θ * F θ + G θ * G θ := by
    nlinarith [sq_nonneg (|F θ| - |G θ|), sq_abs (F θ), sq_abs (G θ)]
  calc (|F θ| * |G θ|) * κ θ
      ≤ ((F θ * F θ + G θ * G θ) / 2) * κ θ :=
        mul_le_mul_of_nonneg_right (by linarith) hθ
    _ = (F θ * F θ * κ θ + G θ * G θ * κ θ) * (1 / 2) := by ring

/-- `cw z = 2(z-1)/(1+z)` is bounded by `2` on `[0,∞)`. -/
theorem abs_cw_le_two {z : ℝ} (hz : z ∈ Work.Spaces.Iz) : |cw z| ≤ 2 := by
  rw [Work.Spaces.Iz, Set.mem_Ici] at hz
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have h2 : |z - 1| ≤ z + 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [cw, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (le_of_lt h1), div_le_iff₀ h1]
  linarith

/-- `cw` is measurable. -/
private theorem measurable_cw : Measurable cw := by
  change Measurable (fun z : ℝ => 2 * (z - 1) / (1 + z))
  fun_prop

/-! ## Mixed honesty from the diagonal honesties -/

/-- **`IPMem g h` from `IPMem g g` and `IPMem h h` for smooth profiles.**

Slicewise, `|g h| w²σ ≤ (g² w²σ + h² w²σ)/2`, so the slice integrability of the cross product
follows from the two diagonal ones (`integrableOn_mul_of_sq_aux`); integrating in `θ` and using
the same inequality again bounds the `z`-integrand by `(A z + B z)/2`, where `A`, `B` are the
honest diagonal `z`-integrands.  The a.e. strong measurability of the `z`-integrand comes from
the joint continuity of `(z,θ) ↦ g z θ h z θ` on the open quadrant
(`Work.Spaces.aesm_of_continuousOn_Qd`) together with the joint measurability of `w²σ`. -/
theorem IPMem_of_diag_smooth {g h : ℝ → ℝ → ℝ} (hgm : Work.Spaces.SmoothNbhd g)
    (hhm : Work.Spaces.SmoothNbhd h) (hg : IPMem g g) (hh : IPMem h h) : IPMem g h := by
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => g z θ * h z θ * w2 z * sig θ) Work.Spaces.Iθ := by
    intro z hz
    have hκm : Measurable (fun θ : ℝ => w2 z * sig θ) := measurable_sig.const_mul (w2 z)
    have hκnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ w2 z * sig θ :=
      fun θ hθ => mul_nonneg (w2_nonneg z) (sig_nonneg hθ)
    have hF2 : IntegrableOn (fun θ => g z θ * g z θ * (w2 z * sig θ)) Work.Spaces.Iθ :=
      (hg.1 z hz).congr (Eventually.of_forall (fun θ => by ring))
    have hG2 : IntegrableOn (fun θ => h z θ * h z θ * (w2 z * sig θ)) Work.Spaces.Iθ :=
      (hh.1 z hz).congr (Eventually.of_forall (fun θ => by ring))
    exact (integrableOn_mul_of_sq_aux measurableSet_Icc (aesm_slice_of_smoothNbhd hgm hz)
      (aesm_slice_of_smoothNbhd hhm hz) hκm hκnn hF2 hG2).congr
      (Eventually.of_forall (fun θ => by ring))
  refine ⟨hslice, ?_⟩
  have hjoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => g p.1 p.2 * h p.1 p.2 * w2 p.1 * sig p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2 * h p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
      (hgm.continuousOn.mono quadrant_subset_nbhU).mul
        (hhm.continuousOn.mono quadrant_subset_nbhU)
    have hgh : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1 p.2 * h p.1 p.2)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => g p.1 p.2 * h p.1 p.2) hcont
    refine (hgh.mul measurable_w2_mul_sig.aestronglyMeasurable).congr ?_
    filter_upwards with p
    simp only [Pi.mul_apply]
    ring
  refine (((hg.2).add (hh.2)).mul_const (1 / 2)).mono' hjoint.integral_prod_right' ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
  rw [Real.norm_eq_abs]
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      |g z θ * h z θ * w2 z * sig θ|
        ≤ (g z θ * g z θ * w2 z * sig θ + h z θ * h z θ * w2 z * sig θ) * (1 / 2) := by
    intro θ hθ
    have hw2 : 0 ≤ w2 z := w2_nonneg z
    have hsig : 0 ≤ sig θ := sig_nonneg hθ
    have hAM : 2 * (|g z θ| * |h z θ|) ≤ g z θ * g z θ + h z θ * h z θ := by
      nlinarith [sq_nonneg (|g z θ| - |h z θ|), sq_abs (g z θ), sq_abs (h z θ)]
    have hstep : |g z θ| * |h z θ| ≤ (g z θ * g z θ + h z θ * h z θ) / 2 := by linarith
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hw2, abs_of_nonneg hsig]
    calc ((|g z θ| * |h z θ|) * w2 z) * sig θ
        ≤ (((g z θ * g z θ + h z θ * h z θ) / 2) * w2 z) * sig θ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstep hw2) hsig
      _ = (g z θ * g z θ * w2 z * sig θ + h z θ * h z θ * w2 z * sig θ) * (1 / 2) := by ring
  have h1 : |∫ θ in Work.Spaces.Iθ, g z θ * h z θ * w2 z * sig θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |g z θ * h z θ * w2 z * sig θ| :=
    abs_integral_le_integral_abs
  have h2 : (∫ θ in Work.Spaces.Iθ, |g z θ * h z θ * w2 z * sig θ|)
      ≤ ∫ θ in Work.Spaces.Iθ,
          (g z θ * g z θ * w2 z * sig θ + h z θ * h z θ * w2 z * sig θ) * (1 / 2) :=
    integral_mono_of_nonneg (Eventually.of_forall (fun θ => abs_nonneg _))
      (((hg.1 z hz).add (hh.1 z hz)).mul_const (1 / 2))
      (ae_restrict_of_forall_mem measurableSet_Icc hpt)
  have h3 : (∫ θ in Work.Spaces.Iθ,
        (g z θ * g z θ * w2 z * sig θ + h z θ * h z θ * w2 z * sig θ) * (1 / 2))
      = ((∫ θ in Work.Spaces.Iθ, g z θ * g z θ * w2 z * sig θ)
          + (∫ θ in Work.Spaces.Iθ, h z θ * h z θ * w2 z * sig θ)) * (1 / 2) := by
    rw [integral_mul_const, integral_add (hg.1 z hz) (hh.1 z hz)]
  exact le_trans h1 (le_trans h2 h3.le)

/-! ## The bounded weight `cw` -/

/-- **`IPMem (cw · g) (cw · g)` from `IPMem g g`.**  Since `|cw| ≤ 2` on `[0,∞)`, the extra
factor is bounded: pointwise `(cw z · g)² ≤ 4 g²`, and the `z`-integrand of the pair is
`cw z²` times an integrable function. -/
theorem IPMem_cw_mul_diag {g : ℝ → ℝ → ℝ} (hg : IPMem g g) :
    IPMem (fun z θ => cw z * g z θ) (fun z θ => cw z * g z θ) := by
  have hA : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, g z θ * g z θ * w2 z * sig θ)
      Work.Spaces.Iz := hg.2
  constructor
  · intro z hz
    refine ((hg.1 z hz).const_mul (cw z ^ 2)).congr (Eventually.of_forall (fun θ => ?_))
    ring
  · have hcm : Measurable (fun z : ℝ => cw z ^ 2) := by
      change Measurable (fun z : ℝ => (2 * (z - 1) / (1 + z)) ^ 2)
      fun_prop
    have hbd : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), ‖cw z ^ 2‖ ≤ (4 : ℝ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := abs_cw_le_two hz
      nlinarith [abs_nonneg (cw z), sq_abs (cw z)]
    have hbdd : IntegrableOn (fun z => cw z ^ 2 * (∫ θ in Work.Spaces.Iθ,
        g z θ * g z θ * w2 z * sig θ)) Work.Spaces.Iz :=
      hA.bdd_mul hcm.aestronglyMeasurable hbd
    refine hbdd.congr (Eventually.of_forall (fun z => ?_))
    show cw z ^ 2 * (∫ θ in Work.Spaces.Iθ, g z θ * g z θ * w2 z * sig θ)
      = ∫ θ in Work.Spaces.Iθ, (cw z * g z θ) * (cw z * g z θ) * w2 z * sig θ
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

/-! ## The four pairings of `I₁` -/

theorem I1_honesty (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ)
    (hU : Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.AngSecond.G Ψ)
      (Work.FTS.EllipticEst.AngSecond.G Ψ))
    (hφ : Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.AngSecond.Phi Ψ)
      (Work.FTS.EllipticEst.AngSecond.Phi Ψ))
    (hH : Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.AngSecond.H Ψ)
      (Work.FTS.EllipticEst.AngSecond.H Ψ)) :
    Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.AngSecond.G Ψ)
        (Work.FTS.EllipticEst.AngSecond.Phi Ψ)
      ∧ Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.AngSecond.G Ψ)
          (Work.FTS.EllipticEst.AngSecond.H Ψ)
      ∧ Work.FTS.EllipticEst.AngSecond.IPMem
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
            * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ)
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
            * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ)
      ∧ Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.AngSecond.G Ψ)
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
            * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ) := by
  have hGsm : Work.Spaces.SmoothNbhd (G Ψ) := smoothNbhd_G Ψ hΨ
  have hΦsm : Work.Spaces.SmoothNbhd (Phi Ψ) := smoothNbhd_Phi Ψ hΨ
  have hHsm : Work.Spaces.SmoothNbhd (H Ψ) := smoothNbhd_H Ψ hΨ
  have hcwΦ : Work.Spaces.SmoothNbhd (fun z θ => cw z * Phi Ψ z θ) :=
    smoothNbhd_cw_Phi Ψ hΨ
  refine ⟨IPMem_of_diag_smooth hGsm hΦsm hU hφ,
    IPMem_of_diag_smooth hGsm hHsm hU hH, IPMem_cw_mul_diag hφ, ?_⟩
  exact IPMem_of_diag_smooth hGsm hcwΦ hU (IPMem_cw_mul_diag hφ)

end Work.AngSecond
