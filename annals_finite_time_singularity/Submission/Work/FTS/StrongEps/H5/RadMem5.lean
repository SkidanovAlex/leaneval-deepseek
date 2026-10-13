/-
# `H5/RadMem5` — the level-`5` radial `ℋ⁵`-membership and *level-`5`* norm bound

`Work.FTS.StrongEps.H5.RadHkMemXn_gen` gives, for a radial profile `r` whose `D_z`-iterates of
order `≤ k` are bounded by `C·z²/(1+z)³`, the `ℋᵏ`-membership of the lift `(z,θ) ↦ r z`
together with a bound on the **level-`4`** norm `Xn α (·) = HkNorm α 4 (·)`.  The level-`5`
scaled atoms (`z/(1+z)·F_*` and friends) need the *level-`5`* norm of the same lift, which this
file supplies:

`HkNorm α 5 (fun z _ => r z) ≤ √(12·10⁴) · C`.

The proof is the exact value of `HkSq` for a radial lift
(`HkSq α 5 (r) = (∫_z Σ_{i≤5}(D_z^i r)²w²) · K_θ`, from `Work.Elliptic.HkSq_rad`) together with
the pointwise bound `(D_z^i r)²w² ≤ (C/(1+z))²` and the two integrals `∫_{Iz}(1/(1+z))² ≤ 2`
(`Work.FTS.H2.InvOneAddSq`), `K_θ = ∫_θ sin(2θ)^{-η} ≤ 10⁴` (`Work.Spaces.sin_two_rpow`).
The membership itself is quoted from `RadHkMemXn_gen`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.H5.RadHkMemXn_gen
import Submission.Work.FTS.H2.InvOneAddSq
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

set_option autoImplicit false

/-- The level-`5` radial density `Σ_{i≤5} (D_z^i r)² w²`. -/
def Rint5 (r : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (5 + 1), (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2

theorem Rint5_nonneg (r : ℝ → ℝ) (z : ℝ) : 0 ≤ Rint5 r z :=
  Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The exact value of `HkSq α 5` of a radial lift. -/
theorem HkSq_rad_eq5 (α : ℝ) (r : ℝ → ℝ) :
    Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z)
      = (∫ z in Work.Spaces.Iz, Rint5 r z)
          * Work.FTS.Nonlinear.RadialProd.Kth := by
  rw [Work.Elliptic.HkSq_rad α 5 r]
  simp only [Rint5, Work.FTS.Nonlinear.RadialProd.Kth, Work.FTS.Nonlinear.RadialProd.smE]

/-- `K_θ = ∫_θ sin(2θ)^{-η} ≤ 10⁴`. -/
theorem Kth_le_1e4 : Work.FTS.Nonlinear.RadialProd.Kth ≤ 10 ^ 4 := by
  have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).2
  have hexp : -(Work.Spaces.eta) + 1 = (1 : ℝ) / 100 := by rw [Work.Spaces.eta]; norm_num
  rw [hexp] at h
  have h2 : (100 : ℝ) / ((1 : ℝ) / 100) = 10000 := by norm_num
  rw [h2] at h
  norm_num at h ⊢
  simpa only [Work.FTS.Nonlinear.RadialProd.Kth, Work.FTS.Nonlinear.RadialProd.smE] using h

/-- The `z`-integral of `(1/(1+z))²` over `Iz = [0,∞)` is at most `2`. -/
theorem int_inv_one_add_sq_Iz :
    (∫ z in Work.Spaces.Iz, (1 / (1 + z)) ^ 2) ≤ 2 := by
  have hbd : (∫ z in (Set.Ioi (0 : ℝ)), (1 / (1 + z)) ^ 2) ≤ 2 :=
    Work.FTS.H2.InvOneAddSq.2
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))] at hbd
  exact hbd

/-- The `ℋ⁵`-density `Rint5 r` of a radial profile with `|D_z^i r z| ≤ C0·z²/(1+z)³` is
integrable on `Iz`, with integral at most `12·C0²`. -/
theorem Rint5_integral_le {r : ℝ → ℝ} {C0 : ℝ} (hC0 : 0 < C0)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n r (Set.Ioi 0))
    (hb : ∀ i : ℕ, i ≤ 5 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter i r z| ≤ C0 * z ^ 2 / (1 + z) ^ 3) :
    (∫ z in Work.Spaces.Iz, Rint5 r z) ≤ 12 * C0 ^ 2 := by
  -- ### the pointwise slot bound
  have hslot : ∀ (i : ℕ), i ≤ 5 → ∀ z ∈ Work.Spaces.Iz,
      (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ (C0 / (1 + z)) ^ 2 := by
    intro i hi z hz
    have hz0 : 0 ≤ z := hz
    have habs := hb i hi z hz0
    have hsq : (Work.Elliptic.DzdIter i r z) ^ 2 ≤ (C0 * z ^ 2 / (1 + z) ^ 3) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hprod := mul_le_mul_of_nonneg_right hsq (sq_nonneg (Work.Spaces.w z))
    rcases eq_or_lt_of_le hz0 with hz' | hz'
    · rw [← hz']
      have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by simp [Work.Spaces.w]
      rw [hw0]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero, div_one]
      exact sq_nonneg C0
    · refine hprod.trans (le_of_eq ?_)
      rw [Work.Spaces.w]
      field_simp
  have hsum_le : ∀ z ∈ Work.Spaces.Iz, Rint5 r z ≤ 6 * (C0 / (1 + z)) ^ 2 := by
    intro z hz
    calc Rint5 r z
        ≤ ∑ _i ∈ Finset.range 6, (C0 / (1 + z)) ^ 2 :=
          Finset.sum_le_sum (fun i hi => hslot i (by
            have := Finset.mem_range.mp hi; omega) z hz)
      _ = 6 * (C0 / (1 + z)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  -- ### integrability of the majorant
  have hmaj_int : MeasureTheory.IntegrableOn
      (fun z : ℝ => 6 * (C0 / (1 + z)) ^ 2) Work.Spaces.Iz := by
    have h1 : MeasureTheory.Integrable (fun z : ℝ =>
        (6 * C0 ^ 2) * (1 / (1 + z)) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul _
    have h2 : MeasureTheory.Integrable (fun z : ℝ => 6 * (C0 / (1 + z)) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      h1.congr (Filter.Eventually.of_forall fun z => by ring)
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))] at h2
    exact h2
  -- ### the integral comparison
  have hmono : (∫ z in Work.Spaces.Iz, Rint5 r z)
      ≤ ∫ z in Work.Spaces.Iz, 6 * (C0 / (1 + z)) ^ 2 :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => Rint5_nonneg r z) hmaj_int
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
        exact hsum_le z hz)
  have hInt2 : (∫ z in Work.Spaces.Iz, 6 * (C0 / (1 + z)) ^ 2)
      = 6 * C0 ^ 2 * ∫ z in Work.Spaces.Iz, (1 / (1 + z)) ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  have hIz_le2 : (∫ z in Work.Spaces.Iz, (1 / (1 + z)) ^ 2) ≤ 2 := int_inv_one_add_sq_Iz
  rw [hInt2] at hmono
  have h6 : 6 * C0 ^ 2 * (∫ z in Work.Spaces.Iz, (1 / (1 + z)) ^ 2) ≤ 6 * C0 ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left hIz_le2 (by positivity)
  linarith

/-- **The level-`5` radial norm bound.**  A radial profile with
`|D_z^i r z| ≤ C0·z²/(1+z)³` for `i ≤ 5` has an `ℋ⁵`-lift whose level-`5` norm is at most
`√(12·10⁴)·C0`. -/
theorem RadMem5 {r : ℝ → ℝ} {C0 : ℝ} (hC0 : 0 < C0)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n r (Set.Ioi 0))
    (hb : ∀ i : ℕ, i ≤ 5 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter i r z| ≤ C0 * z ^ 2 / (1 + z) ^ 3) :
    ∃ Cr : ℝ, 0 < Cr ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
      Work.Spaces.HkMem α 5 (fun z (_ : ℝ) => r z) ∧
      Work.Spaces.HkNorm α 5 (fun z (_ : ℝ) => r z) ≤ Cr * C0 := by
  have hRint5_le := Rint5_integral_le hC0 hsm hb
  obtain ⟨C', hC'pos, hgen⟩ := RadHkMemXn_gen (r := r) (C := C0) (k := 5) hC0 hsm hb
  refine ⟨Real.sqrt (12 * 10 ^ 4), by positivity, fun α hαI => ?_⟩
  obtain ⟨hmem, _⟩ := hgen α hαI
  refine ⟨hmem, ?_⟩
  have hKth0 : 0 ≤ Work.FTS.Nonlinear.RadialProd.Kth :=
    le_trans zero_le_one Work.FTS.Nonlinear.RadialProd.one_le_Kth
  have hKth_le : Work.FTS.Nonlinear.RadialProd.Kth ≤ 10 ^ 4 := Kth_le_1e4
  have hRint5nn : 0 ≤ ∫ z in Work.Spaces.Iz, Rint5 r z :=
    MeasureTheory.integral_nonneg fun z => Rint5_nonneg r z
  rw [show Work.Spaces.HkNorm α 5 (fun z (_ : ℝ) => r z)
      = Real.sqrt (Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z)) from rfl, HkSq_rad_eq5]
  calc Real.sqrt ((∫ z in Work.Spaces.Iz, Rint5 r z)
        * Work.FTS.Nonlinear.RadialProd.Kth)
      ≤ Real.sqrt ((12 * C0 ^ 2) * 10 ^ 4) :=
        Real.sqrt_le_sqrt (mul_le_mul hRint5_le hKth_le hKth0 (by positivity))
    _ = Real.sqrt (12 * 10 ^ 4) * C0 := by
        rw [show (12 * C0 ^ 2) * 10 ^ 4 = (12 * 10 ^ 4) * C0 ^ 2 by ring,
          Real.sqrt_mul (by norm_num), Real.sqrt_sq hC0.le]

end Work.FTS.StrongEps.H5
