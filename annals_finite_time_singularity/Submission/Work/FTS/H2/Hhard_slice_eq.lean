import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.T2Defs
import Submission.Work.FTS.H2.T2HardAux
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkAux
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.H2.T2SliceAux

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

/-! ## Auxiliary lemmas for `Hhard_slice_eq` -/

/-- The angular slice `θ ↦ H z θ` of a function smooth on a neighbourhood of the closed
quadrant is a.e. strongly measurable on `Iθ`. -/
private theorem aesm_slice {H : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd H) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun θ => H z θ) (volume.restrict Work.Spaces.Iθ) :=
  (continuousOn_slice hsm hz).aestronglyMeasurable
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)

/-- If `φ` is integrable on `Iθ` and `ψ` is bounded there (and a.e. strongly measurable),
then `ψ · φ` is integrable on `Iθ`. -/
private theorem integrableOn_mul_of_bound {φ ψ : ℝ → ℝ}
    (hφ : IntegrableOn φ Work.Spaces.Iθ)
    (hψ : AEStronglyMeasurable ψ (volume.restrict Work.Spaces.Iθ)) {C : ℝ}
    (hC : ∀ θ ∈ Work.Spaces.Iθ, |ψ θ| ≤ C) :
    IntegrableOn (fun θ => ψ θ * φ θ) Work.Spaces.Iθ := by
  have h0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_refl 0, by linarith [Real.pi_pos]⟩
  have hCnn : 0 ≤ C := le_trans (abs_nonneg (ψ 0)) (hC 0 h0)
  have hg : Integrable (fun θ => C * |φ θ|) (volume.restrict Work.Spaces.Iθ) :=
    hφ.abs.const_mul C
  refine hg.mono' (hψ.mul hφ.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
    with θ hθ
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC θ hθ) (abs_nonneg (φ θ))

/-- `Thard g k` is smooth on a neighbourhood of the closed quadrant. -/
private theorem smoothNbhd_Thard (g : ℝ → ℝ → ℝ) (hsmg : Work.Spaces.SmoothNbhd g)
    (k : Fin 5) : Work.Spaces.SmoothNbhd (Thard g k) := by
  have h : Thard g k = Work.Spaces.mixed (4 - k.val) k.val g := Thard_eq_mixed g k
  rw [h]
  exact Work.Spaces.smoothNbhd_mixed hsmg (4 - k.val) k.val

/-- The angular weight `sghard α k` is a.e. strongly measurable on `Iθ`. -/
private theorem aesm_sghard (α : ℝ) (k : Fin 5) :
    AEStronglyMeasurable (sghard α k) (volume.restrict Work.Spaces.Iθ) := by
  have h : sghard α k = fun θ => (Real.sin (2 * θ))
      ^ (-(if k.val = 0 then Work.Spaces.eta else Work.Spaces.gam α)) := sghard_eq α k
  rw [h]
  exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _)
    |>.aestronglyMeasurable

/-- A mixed derivative `D_z^j D_θ^i g` with `i ≥ 1` carries the factor `sin(2θ)`: its
angular slice at fixed `z` is bounded by a constant times `sin(2θ)`. -/
private theorem abs_mixed_le_sin_mul (g : ℝ → ℝ → ℝ) (hsmg : Work.Spaces.SmoothNbhd g)
    (j i : ℕ) (hi : 1 ≤ i) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.mixed j i g z θ| ≤ C * Real.sin (2 * θ) := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hR : Work.Spaces.SmoothNbhd
      (Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i' g))) :=
    Work.Spaces.smoothNbhd_DzIter
      (Work.Spaces.SmoothNbhd.pth (Work.Spaces.smoothNbhd_DthIter hsmg i')) j
  obtain ⟨C, hCnn, hC⟩ := exists_nonneg_bound_abs (continuousOn_slice hR hz)
  refine ⟨C, hCnn, fun θ hθ => ?_⟩
  have hsin : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  simp only [mixed_sin_factor j i' g]
  rw [abs_mul, abs_of_nonneg hsin, mul_comm C (Real.sin (2 * θ))]
  exact mul_le_mul_of_nonneg_left (hC θ hθ) hsin

/-- The `z`-derivative of a mixed derivative with `i ≥ 1` also carries the factor
`sin(2θ)`. -/
private theorem abs_pz_mixed_le_sin_mul (g : ℝ → ℝ → ℝ) (hsmg : Work.Spaces.SmoothNbhd g)
    (j i : ℕ) (hi : 1 ≤ i) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.pz (Work.Spaces.mixed j i g) z θ| ≤ C * Real.sin (2 * θ) := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hR : Work.Spaces.SmoothNbhd (Work.Spaces.pz
      (Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i' g)))) :=
    (Work.Spaces.smoothNbhd_DzIter
      (Work.Spaces.SmoothNbhd.pth (Work.Spaces.smoothNbhd_DthIter hsmg i')) j).pz
  obtain ⟨C, hCnn, hC⟩ := exists_nonneg_bound_abs (continuousOn_slice hR hz)
  refine ⟨C, hCnn, fun θ hθ => ?_⟩
  have hsin : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  rw [pz_mixed_sin_factor j i' g z θ, abs_mul, abs_of_nonneg hsin,
    mul_comm C (Real.sin (2 * θ))]
  exact mul_le_mul_of_nonneg_left (hC θ hθ) hsin

/-- The `k = 0` "hard" core is integrable in `θ` on `Iθ`. -/
private theorem integrableOn_core_zero (g : ℝ → ℝ → ℝ) (hsmg : Work.Spaces.SmoothNbhd g)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    IntegrableOn (fun θ => Work.Spaces.pz (Work.Spaces.DzIter 4 g) z θ
      * Work.Spaces.DzIter 4 g z θ * (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  have hsmooth1 : Work.Spaces.SmoothNbhd (Work.Spaces.DzIter 4 g) :=
    Work.Spaces.smoothNbhd_DzIter hsmg 4
  have h1 : ContinuousOn (fun θ => Work.Spaces.pz (Work.Spaces.DzIter 4 g) z θ)
      Work.Spaces.Iθ := continuousOn_slice hsmooth1.pz hz
  have h2 : ContinuousOn (fun θ => Work.Spaces.DzIter 4 g z θ) Work.Spaces.Iθ :=
    continuousOn_slice hsmooth1 hz
  obtain ⟨B1, hB1nn, hB1⟩ := exists_nonneg_bound_abs h1
  obtain ⟨B2, hB2nn, hB2⟩ := exists_nonneg_bound_abs h2
  have hCnn : 0 ≤ B1 * B2 * (Work.Spaces.w z) ^ 2 :=
    mul_nonneg (mul_nonneg hB1nn hB2nn) (sq_nonneg _)
  have hg : Integrable (fun θ => B1 * B2 * (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).1.const_mul _
  have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.pz (Work.Spaces.DzIter 4 g) z θ
      * Work.Spaces.DzIter 4 g z θ * (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) :=
    (((h1.aestronglyMeasurable
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)).mul
      (h2.aestronglyMeasurable
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc))).mul
      aestronglyMeasurable_const).mul
      (((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _)
        |>.aestronglyMeasurable)
  refine hg.mono' haesm ?_
  filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
    with θ hθ
  have hsin : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_nonneg hsin _
  have hwnn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hwnn,
    abs_of_nonneg hsnn]
  have hAB : |Work.Spaces.pz (Work.Spaces.DzIter 4 g) z θ| * |Work.Spaces.DzIter 4 g z θ|
      ≤ B1 * B2 := mul_le_mul (hB1 θ hθ) (hB2 θ hθ) (abs_nonneg _) hB1nn
  have hfac : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg hwnn hsnn
  calc |Work.Spaces.pz (Work.Spaces.DzIter 4 g) z θ| * |Work.Spaces.DzIter 4 g z θ|
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = (|Work.Spaces.pz (Work.Spaces.DzIter 4 g) z θ| * |Work.Spaces.DzIter 4 g z θ|)
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
    _ ≤ (B1 * B2) * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_right hAB hfac
    _ = B1 * B2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        ring

/-- The mixed (`k ≥ 1`) "hard" core is integrable in `θ` on `Iθ`, for `α ≤ 1`. -/
private theorem integrableOn_core_mixed (α : ℝ) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ)
    (hsmg : Work.Spaces.SmoothNbhd g) (j i : ℕ) (hi : 1 ≤ i) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    IntegrableOn (fun θ => Work.Spaces.pz (Work.Spaces.mixed j i g) z θ
      * Work.Spaces.mixed j i g z θ * (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
  obtain ⟨C1, hC1nn, hC1⟩ := abs_pz_mixed_le_sin_mul g hsmg j i hi hz
  obtain ⟨C2, hC2nn, hC2⟩ := abs_mixed_le_sin_mul g hsmg j i hi hz
  have hgam2 : Work.Spaces.gam α < 2 := by rw [Work.Spaces.gam]; linarith
  have hgam2' : 0 ≤ 2 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hsm_mix : Work.Spaces.SmoothNbhd (Work.Spaces.mixed j i g) :=
    Work.Spaces.smoothNbhd_mixed hsmg j i
  have hp : ContinuousOn (fun θ => Work.Spaces.pz (Work.Spaces.mixed j i g) z θ)
      Work.Spaces.Iθ := continuousOn_slice hsm_mix.pz hz
  have hm : ContinuousOn (fun θ => Work.Spaces.mixed j i g z θ) Work.Spaces.Iθ :=
    continuousOn_slice hsm_mix hz
  have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.pz (Work.Spaces.mixed j i g) z θ
      * Work.Spaces.mixed j i g z θ * (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (volume.restrict Work.Spaces.Iθ) :=
    (((hp.aestronglyMeasurable
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)).mul
      (hm.aestronglyMeasurable
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc))).mul
      aestronglyMeasurable_const).mul
      (((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _)
        |>.aestronglyMeasurable)
  refine IntegrableOn.of_bound Work.Spaces.volume_Iθ_lt_top haesm
    (C1 * C2 * (Work.Spaces.w z) ^ 2) ?_
  filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
    with θ hθ
  have hsin : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hsin _
  have hwnn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hwnn,
    abs_of_nonneg hsnn]
  have hAB : |Work.Spaces.pz (Work.Spaces.mixed j i g) z θ|
      * |Work.Spaces.mixed j i g z θ| ≤ (C1 * Real.sin (2 * θ)) * (C2 * Real.sin (2 * θ)) :=
    mul_le_mul (hC1 θ hθ) (hC2 θ hθ) (abs_nonneg _) (mul_nonneg hC1nn hsin)
  have hs_le : Real.sin (2 * θ)
      * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ 1 := by
    have := sq_mul_rpow_neg_le_one (Real.sin (2 * θ)) (Work.Spaces.gam α) hsin
      (Real.sin_le_one _) hgam2 hgam2'
    simpa [pow_two, mul_assoc] using this
  have hCnn : 0 ≤ C1 * C2 * (Work.Spaces.w z) ^ 2 :=
    mul_nonneg (mul_nonneg hC1nn hC2nn) hwnn
  calc |Work.Spaces.pz (Work.Spaces.mixed j i g) z θ| * |Work.Spaces.mixed j i g z θ|
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (|Work.Spaces.pz (Work.Spaces.mixed j i g) z θ|
          * |Work.Spaces.mixed j i g z θ|)
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    _ ≤ ((C1 * Real.sin (2 * θ)) * (C2 * Real.sin (2 * θ)))
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
        mul_le_mul_of_nonneg_right hAB (mul_nonneg hwnn hsnn)
    _ = C1 * C2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ) * (Real.sin (2 * θ)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by ring
    _ ≤ C1 * C2 * (Work.Spaces.w z) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hs_le hCnn
    _ = C1 * C2 * (Work.Spaces.w z) ^ 2 := by ring

/-- For fixed `z ∈ Iz` the angular integral of the "hard" integrand `Hhard α f g` splits into
its five summands, i.e. `∫_θ Σ_k = Σ_k ∫_θ` for the five order-five terms.  This is the
identity which turns the left-hand side of `Work.FTS.H2.T2HardPart` (the sum inside the
`θ`-integral) into the left-hand side of `Work.FTS.H2.T2Hard` (the sum outside it).

Route.  `Hhard α f g z θ = f z θ * z * ∑ k : Fin 5, (pz (Thard g k) * Thard g k * w² * sghard α k) z θ`,
so by `Finset.mul_sum` and `MeasureTheory.integral_congr` the left-hand side is
`∫_θ ∑ k, (f z θ * z * pz (Thard g k) z θ * Thard g k z θ * w² * sghard α k θ)`, and it
remains to show that each of the five summands is integrable on `Iθ` for the fixed `z`, so
that `MeasureTheory.integral_finset_sum` applies.

Integrability of a summand: all factors other than `Thard g k z θ` and the angular weight are
bounded functions of `θ` on the compact `Iθ` for fixed `z` (`f`, `pz (Thard g k)` are smooth
on a neighbourhood of the quadrant, and `w z` is a constant in `θ`; see
`Work.FTS.H2.abs_slice_le_boxSup` and `Work.Spaces.smoothNbhd_mixed`), so it suffices to bound
`|Thard g k z θ| · sghard α k θ`.  For `k ≥ 1`, `Thard g k = mixed (4 - k.val) k.val g` with
`k.val ≥ 1` and `sghard α k = sin(2θ)^{-γ}` with `1 < γ ≤ 11/10`: the mixed derivative carries
one explicit factor of `sin(2θ)` (`Work.FTS.H2.mixed_eq_sin_mul'`, from `D_θ = sin(2θ) ∂_θ`
and the fact that an angular factor commutes with `D_z^j`), so the product is at most
`C(z) · sin(2θ)^{1-γ}`, integrable on `Iθ` because `-1 < 1 - γ ≤ 0`
(`Work.Spaces.sin_two_rpow`).  For `k = 0`, `Thard g 0 = D_z^4 g` and
`sghard α 0 = sin(2θ)^{-η}` with `η = 99/100 ∈ (0,1)`, so the product is at most
`C(z) · sin(2θ)^{-η}`, again integrable (`sin_two_rpow`).  The hypothesis `α ≤ 1` (hence
`γ ≤ 11/10 < 3`) is needed: without it the `k ≥ 1` summands are not integrable on `Iθ` and
the identity genuinely fails. -/
theorem Hhard_slice_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (hsmf : Work.Spaces.SmoothNbhd f) (hsmg : Work.Spaces.SmoothNbhd g)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ∫ θ in Work.Spaces.Iθ, Hhard α f g z θ
      = ∑ k : Fin 5, ∫ θ in Work.Spaces.Iθ,
          f z θ * z * Work.Spaces.pz (Thard g k) z θ * Thard g k z θ
            * (Work.Spaces.w z) ^ 2 * sghard α k θ := by
  -- Each of the five summands is integrable on `Iθ` for the fixed `z`.
  have hint : ∀ k : Fin 5, Integrable (fun θ => f z θ * z * Work.Spaces.pz (Thard g k) z θ
      * Thard g k z θ * (Work.Spaces.w z) ^ 2 * sghard α k θ)
      (volume.restrict Work.Spaces.Iθ) := by
    intro k
    have hψ : AEStronglyMeasurable (fun θ => f z θ * z)
        (volume.restrict Work.Spaces.Iθ) :=
      (aesm_slice hsmf hz).mul aestronglyMeasurable_const
    have hbnd : ∀ θ ∈ Work.Spaces.Iθ, |f z θ * z| ≤ Work.Spaces.boxSup z f * z := by
      intro θ hθ
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ z from hz)]
      exact mul_le_mul_of_nonneg_right
        (abs_slice_le_boxSup f hsmf hz θ hθ) (show (0 : ℝ) ≤ z from hz)
    have hfac : (fun θ => f z θ * z * Work.Spaces.pz (Thard g k) z θ * Thard g k z θ
        * (Work.Spaces.w z) ^ 2 * sghard α k θ)
        = fun θ => (f z θ * z) * (Work.Spaces.pz (Thard g k) z θ * Thard g k z θ
          * (Work.Spaces.w z) ^ 2 * sghard α k θ) := by
      funext θ
      ring
    rw [hfac]
    rcases eq_or_ne k.val 0 with hk0 | hk0
    · -- the `D_z^4`-slot (`k = 0`), weight `sin(2θ)^{-η}`
      have hT : Thard g k = Work.Spaces.DzIter 4 g := by
        rw [Thard_eq_mixed g k, hk0]
        exact Work.Spaces.mixed_zero_right 4 g
      have hS : sghard α k = fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        rw [sghard_eq α k, if_pos hk0]
      have hcore : IntegrableOn (fun θ => Work.Spaces.pz (Thard g k) z θ
          * Thard g k z θ * (Work.Spaces.w z) ^ 2 * sghard α k θ) Work.Spaces.Iθ := by
        refine (integrableOn_core_zero g hsmg hz).congr ?_
        filter_upwards with θ
        simp only [hT, hS]
      exact integrableOn_mul_of_bound hcore hψ hbnd
    · -- the mixed slots (`k ≥ 1`), weight `sin(2θ)^{-γ}`
      have hk1 : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk0
      have hT : Thard g k = Work.Spaces.mixed (4 - k.val) k.val g := Thard_eq_mixed g k
      have hS : sghard α k = fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [sghard_eq α k, if_neg hk0]
      have hcore : IntegrableOn (fun θ => Work.Spaces.pz (Thard g k) z θ
          * Thard g k z θ * (Work.Spaces.w z) ^ 2 * sghard α k θ) Work.Spaces.Iθ := by
        refine (integrableOn_core_mixed α hα1 g hsmg (4 - k.val) k.val hk1 hz).congr ?_
        filter_upwards with θ
        simp only [hT, hS]
      exact integrableOn_mul_of_bound hcore hψ hbnd
  -- Pointwise expansion of `Hhard` and the sum/integral interchange.
  have hpt : ∀ θ : ℝ, Hhard α f g z θ = ∑ k : Fin 5,
      (f z θ * z * Work.Spaces.pz (Thard g k) z θ * Thard g k z θ
        * (Work.Spaces.w z) ^ 2 * sghard α k θ) := by
    intro θ
    simp only [Hhard]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  rw [integral_finsetSum Finset.univ fun k _ => hint k]

end Work.FTS.H2
