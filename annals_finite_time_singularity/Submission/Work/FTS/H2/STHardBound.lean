/-
Copyright: work module for the Elgindi finite-time singularity project.

# The bound on the "hard" part of the `SpecialTransport` pairing

`HardF α f g z θ` is the sum of the five order-five slots of the pairing `(f ∂_θ g, g)_{ℋ⁴}`
in the `f`-form.  Integrating over `θ` and integrating by parts in each slot
(`HardSlotBound`) bounds each slot integral by `(q K + 3K/2)∫_θ sin(2θ)^{-q}v²`, and each
of those energies is bounded by the `ℋ⁴`-energy of `g` (`slot_energy_dz`,
`slot_energy_mixed`).  This gives

  `|∫_θ HardF α f g z θ| ≤ 150000·|∂_θ f|_{𝒲^{4,∞}}·∫_θ HkIntegrand α 4 g z θ`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.STHardBnd
import Submission.Work.FTS.H2.HardSlotBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

/-! ## Auxiliary facts -/

/-- `θ ↦ G z θ` is differentiable on `(0,π/2)` for `G` smooth on an open set `V` containing
`(z,·)` there, with derivative `∂_θ G`. -/
theorem hasDerivAt_slice_of_contDiffOn {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) {z : ℝ}
    (hz : ∀ θ ∈ Set.Ioo 0 (π / 2), (z, θ) ∈ V) :
    ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (fun θ' => G z θ') (Work.Spaces.pth G z θ) θ := by
  intro θ hθ
  have h1 : ContDiffAt ℝ ⊤ (Function.uncurry G) (z, θ) := h.contDiffAt (hV.mem_nhds (hz θ hθ))
  have h2 : ContDiffAt ℝ ⊤ (fun θ' => G z θ') θ := Work.Spaces.contDiffAt_slice_right h1
  exact (h2.differentiableAt (by norm_num)).hasDerivAt

/-- The energy of the `D_z`-slot is bounded by the `ℋ⁴`-energy. -/
theorem slot_energy_dz {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hHk : Work.Spaces.HkMem α 4 g) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) * (Work.Spaces.DzIter 4 g z θ) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg ?_ (hHk.1 z hz) ?_
  · filter_upwards [ae_restrict_mem hIθ] with θ hθ
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _))
  · filter_upwards [ae_restrict_mem hIθ] with θ hθ
    have hW := (Whz_Wm_sq α hα z θ hθ).1
    calc (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
          * (Work.Spaces.DzIter 4 g z θ) ^ 2)
        = (Work.Spaces.DzIter 4 g z θ) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by ring
      _ = (Work.Spaces.DzIter 4 g z θ * Whz z θ) ^ 2 := by rw [← hW]; ring
      _ ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
          Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 4 le_rfl

/-- The energy of a mixed slot is bounded by the `ℋ⁴`-energy. -/
theorem slot_energy_mixed {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hHk : Work.Spaces.HkMem α 4 g) {z : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg ?_ (hHk.1 z hz) ?_
  · filter_upwards [ae_restrict_mem hIθ] with θ hθ
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _))
  · filter_upwards [ae_restrict_mem hIθ] with θ hθ
    have hW := (Whz_Wm_sq α hα z θ hθ).2
    calc (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i g z θ) ^ 2)
        = (Work.Spaces.mixed j i g z θ) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
      _ = (Work.Spaces.mixed j i g z θ * Wm α z θ) ^ 2 := by rw [← hW]; ring
      _ ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij

/-! ## The bound on `HardF` -/

theorem HardBound {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.Spaces.SmoothInt f)
    (hcont : ContinuousOn (Function.uncurry f) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hvt : Work.Spaces.VanishTheta f)
    (hWl : Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f))
    (hg : Work.Spaces.SmoothNbhd g) (hHk : Work.Spaces.HkMem α 4 g)
    {z : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ)) :
    |∫ θ in Work.Spaces.Iθ, HardF α f g z θ|
      ≤ 150000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
        * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hzIoi : z ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by have h0 : (0:ℝ) < z := hz; linarith)
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := WlInf_nonneg hWl
  have hIθ : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hHkI : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ :=
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hKnn : (0 : ℝ) ≤ 10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) :=
    mul_nonneg (by norm_num) hWnn
  have heta_pos : 0 < Work.Spaces.eta := by norm_num [Work.Spaces.eta]
  have heta4 : 0 < 1 + (0 : ℝ) - Work.Spaces.eta := by norm_num [Work.Spaces.eta]
  have hgam_pos : 0 < Work.Spaces.gam α := by linarith [Work.Spaces.one_lt_gam hα]
  have hq4gam : 0 < 1 + (1 : ℝ) - Work.Spaces.gam α := by
    have h2 : Work.Spaces.gam α ≤ 11 / 10 := by rw [Work.Spaces.gam]; linarith
    linarith
  -- the two pointwise bounds on `f` and `∂_θ f`
  have hf1 : ∀ θ ∈ Work.Spaces.Iθ, |f z θ|
      ≤ (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) * Real.sin (2 * θ) := by
    intro θ hθ
    have h := abs_DzIter_f_le hsm hcont hvt hWl 0 (by norm_num) z hz θ hθ
    calc |f z θ| ≤ 10000 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := h
      _ = (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) * Real.sin (2 * θ) := by ring
  have hf2 : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.pth f z θ|
      ≤ 3 * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) := by
    intro θ hθ
    have h := Work.Spaces.WlInf_z_bound α 4 (Work.Spaces.pth f) hWl 0 (by norm_num)
      z θ hzI hθ
    have h' : |Work.Spaces.pth f z θ| ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by
      simpa using h
    linarith
  -- the derivative hypotheses
  have hdf : ∀ θ ∈ Set.Ioo 0 (π / 2),
      HasDerivAt (fun θ' => f z θ') (Work.Spaces.pth f z θ) θ :=
    hasDerivAt_slice_of_contDiffOn isOpen_strp hsm.1 (fun θ hθ => ⟨hzIoi, hθ⟩)
  have hdg1 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      HasDerivAt (fun θ' => Work.Spaces.DzIter 4 g z θ')
        (Work.Spaces.pth (Work.Spaces.DzIter 4 g) z θ) θ :=
    hasDerivAt_slice_of_contDiffOn Work.Spaces.isOpen_nbhU
      (Work.Spaces.smoothNbhd_DzIter hg 4) (fun θ hθ => Work.Spaces.mem_nbhU hzI
        ⟨hθ.1.le, hθ.2.le⟩)
  have hdg2 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      HasDerivAt (fun θ' => Work.Spaces.mixed 3 1 g z θ')
        (Work.Spaces.pth (Work.Spaces.mixed 3 1 g) z θ) θ :=
    hasDerivAt_slice_of_contDiffOn Work.Spaces.isOpen_nbhU
      (Work.Spaces.smoothNbhd_mixed hg 3 1) (fun θ hθ => Work.Spaces.mem_nbhU hzI
        ⟨hθ.1.le, hθ.2.le⟩)
  have hdg3 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      HasDerivAt (fun θ' => Work.Spaces.mixed 2 2 g z θ')
        (Work.Spaces.pth (Work.Spaces.mixed 2 2 g) z θ) θ :=
    hasDerivAt_slice_of_contDiffOn Work.Spaces.isOpen_nbhU
      (Work.Spaces.smoothNbhd_mixed hg 2 2) (fun θ hθ => Work.Spaces.mem_nbhU hzI
        ⟨hθ.1.le, hθ.2.le⟩)
  have hdg4 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      HasDerivAt (fun θ' => Work.Spaces.mixed 1 3 g z θ')
        (Work.Spaces.pth (Work.Spaces.mixed 1 3 g) z θ) θ :=
    hasDerivAt_slice_of_contDiffOn Work.Spaces.isOpen_nbhU
      (Work.Spaces.smoothNbhd_mixed hg 1 3) (fun θ hθ => Work.Spaces.mem_nbhU hzI
        ⟨hθ.1.le, hθ.2.le⟩)
  have hdg5 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      HasDerivAt (fun θ' => Work.Spaces.mixed 0 4 g z θ')
        (Work.Spaces.pth (Work.Spaces.mixed 0 4 g) z θ) θ :=
    hasDerivAt_slice_of_contDiffOn Work.Spaces.isOpen_nbhU
      (Work.Spaces.smoothNbhd_mixed hg 0 4) (fun θ hθ => Work.Spaces.mem_nbhU hzI
        ⟨hθ.1.le, hθ.2.le⟩)
  -- the pointwise data of the five slots
  obtain ⟨C1, C1', hC1, hC1', hvm1, hv11, hv21⟩ := dzSlot_data g hg hzI
  obtain ⟨C2, C2', hC2, hC2', hvm2, hv12, hv22⟩ := mixedSlot_data g hg 3 1 (by norm_num) hzI
  obtain ⟨C3, C3', hC3, hC3', hvm3, hv13, hv23⟩ := mixedSlot_data g hg 2 2 (by norm_num) hzI
  obtain ⟨C4, C4', hC4, hC4', hvm4, hv14, hv24⟩ := mixedSlot_data g hg 1 3 (by norm_num) hzI
  obtain ⟨C5, C5', hC5, hC5', hvm5, hv15, hv25⟩ := mixedSlot_data g hg 0 4 (by norm_num) hzI
  have hfm : ContinuousOn (fun θ => f z θ) Work.Spaces.Iθ := by
    have h1 : ContinuousOn (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ := by fun_prop
    have h2 := hcont.comp h1 (fun θ hθ => ⟨hzI, hθ⟩)
    simpa [Function.comp_def, Function.uncurry] using h2
  -- the decomposition of `HardF`
  have hHardF : HardF α f g z = fun θ => (Work.Spaces.w z) ^ 2 *
      (slotTerm f (Work.Spaces.DzIter 4 g) Work.Spaces.eta z θ
        + (slotTerm f (Work.Spaces.mixed 3 1 g) (Work.Spaces.gam α) z θ
          + (slotTerm f (Work.Spaces.mixed 2 2 g) (Work.Spaces.gam α) z θ
            + (slotTerm f (Work.Spaces.mixed 1 3 g) (Work.Spaces.gam α) z θ
              + slotTerm f (Work.Spaces.mixed 0 4 g) (Work.Spaces.gam α) z θ)))) := by
    funext θ
    simp only [HardF, slotTerm]
    ring
  rw [hHardF]
  -- the five slot terms and their energies
  set G1 : ℝ → ℝ := slotTerm f (Work.Spaces.DzIter 4 g) Work.Spaces.eta z with hG1
  set G2 : ℝ → ℝ := slotTerm f (Work.Spaces.mixed 3 1 g) (Work.Spaces.gam α) z with hG2
  set G3 : ℝ → ℝ := slotTerm f (Work.Spaces.mixed 2 2 g) (Work.Spaces.gam α) z with hG3
  set G4 : ℝ → ℝ := slotTerm f (Work.Spaces.mixed 1 3 g) (Work.Spaces.gam α) z with hG4
  set G5 : ℝ → ℝ := slotTerm f (Work.Spaces.mixed 0 4 g) (Work.Spaces.gam α) z with hG5
  set J1 : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      * (Work.Spaces.DzIter 4 g z θ) ^ 2 with hJ1
  set J2 : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed 3 1 g z θ) ^ 2 with hJ2
  set J3 : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed 2 2 g z θ) ^ 2 with hJ3
  set J4 : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed 1 3 g z θ) ^ 2 with hJ4
  set J5 : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed 0 4 g z θ) ^ 2 with hJ5
  set H : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ with hH
  have hJ1nn : 0 ≤ J1 := by
    rw [hJ1]; refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem hIθ] with θ hθ
    exact mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _)
  have hJ2nn : 0 ≤ J2 := by
    rw [hJ2]; refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem hIθ] with θ hθ
    exact mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _)
  have hJ3nn : 0 ≤ J3 := by
    rw [hJ3]; refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem hIθ] with θ hθ
    exact mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _)
  have hJ4nn : 0 ≤ J4 := by
    rw [hJ4]; refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem hIθ] with θ hθ
    exact mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _)
  have hJ5nn : 0 ≤ J5 := by
    rw [hJ5]; refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem hIθ] with θ hθ
    exact mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _)
  -- the five integrability results
  have hI1 : MeasureTheory.IntegrableOn G1 Work.Spaces.Iθ := by
    rw [hG1]
    exact hardSlotIntegrable (f := f) (v := Work.Spaces.DzIter 4 g) (z := z)
      (q := Work.Spaces.eta) (K := 10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
      (C := C1) (C' := C1') (p := 0)
      heta_pos heta4 hKnn hC1 hC1' hfm hvm1 hf1 hv11 hv21
  have hI2 : MeasureTheory.IntegrableOn G2 Work.Spaces.Iθ := by
    rw [hG2]
    exact hardSlotIntegrable (f := f) (v := Work.Spaces.mixed 3 1 g) (z := z)
      (q := Work.Spaces.gam α) (K := 10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
      (C := C2) (C' := C2') (p := 1)
      hgam_pos hq4gam hKnn
      hC2 hC2' hfm hvm2 hf1 hv12 hv22
  have hI3 : MeasureTheory.IntegrableOn G3 Work.Spaces.Iθ := by
    rw [hG3]
    exact hardSlotIntegrable (f := f) (v := Work.Spaces.mixed 2 2 g) (z := z)
      (q := Work.Spaces.gam α) (K := 10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
      (C := C3) (C' := C3') (p := 1)
      hgam_pos hq4gam hKnn
      hC3 hC3' hfm hvm3 hf1 hv13 hv23
  have hI4 : MeasureTheory.IntegrableOn G4 Work.Spaces.Iθ := by
    rw [hG4]
    exact hardSlotIntegrable (f := f) (v := Work.Spaces.mixed 1 3 g) (z := z)
      (q := Work.Spaces.gam α) (K := 10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
      (C := C4) (C' := C4') (p := 1)
      hgam_pos hq4gam hKnn
      hC4 hC4' hfm hvm4 hf1 hv14 hv24
  have hI5 : MeasureTheory.IntegrableOn G5 Work.Spaces.Iθ := by
    rw [hG5]
    exact hardSlotIntegrable (f := f) (v := Work.Spaces.mixed 0 4 g) (z := z)
      (q := Work.Spaces.gam α) (K := 10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
      (C := C5) (C' := C5') (p := 1)
      hgam_pos hq4gam hKnn
      hC5 hC5' hfm hvm5 hf1 hv15 hv25
  -- the five slot bounds
  have hb1 : |∫ θ in Work.Spaces.Iθ, G1 θ| ≤ (Work.Spaces.eta
      * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) + 3
        * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) / 2) * J1 := by
    rw [hG1, hJ1]
    exact HardSlotBound (f := f) (v := Work.Spaces.DzIter 4 g) (z := z)
      (q := Work.Spaces.eta) (K := 10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
      (C := C1) (C' := C1') (p := 0)
      heta_pos (by norm_num) heta4 hKnn hC1 hC1' hdf hdg1 hf1 hf2 hv11 hv21
  have hb2 : |∫ θ in Work.Spaces.Iθ, G2 θ| ≤ (Work.Spaces.gam α
      * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) + 3
        * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) / 2) * J2 := by
    rw [hG2, hJ2]
    exact HardSlotBound (f := f) (v := Work.Spaces.mixed 3 1 g) (z := z)
      (q := Work.Spaces.gam α) (K := 10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
      (C := C2) (C' := C2') (p := 1)
      hgam_pos (by norm_num) hq4gam hKnn hC2 hC2' hdf hdg2 hf1 hf2 hv12 hv22
  have hb3 : |∫ θ in Work.Spaces.Iθ, G3 θ| ≤ (Work.Spaces.gam α
      * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) + 3
        * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) / 2) * J3 := by
    rw [hG3, hJ3]
    exact HardSlotBound (f := f) (v := Work.Spaces.mixed 2 2 g) (z := z)
      (q := Work.Spaces.gam α) (K := 10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
      (C := C3) (C' := C3') (p := 1)
      hgam_pos (by norm_num) hq4gam hKnn hC3 hC3' hdf hdg3 hf1 hf2 hv13 hv23
  have hb4 : |∫ θ in Work.Spaces.Iθ, G4 θ| ≤ (Work.Spaces.gam α
      * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) + 3
        * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) / 2) * J4 := by
    rw [hG4, hJ4]
    exact HardSlotBound (f := f) (v := Work.Spaces.mixed 1 3 g) (z := z)
      (q := Work.Spaces.gam α) (K := 10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
      (C := C4) (C' := C4') (p := 1)
      hgam_pos (by norm_num) hq4gam hKnn hC4 hC4' hdf hdg4 hf1 hf2 hv14 hv24
  have hb5 : |∫ θ in Work.Spaces.Iθ, G5 θ| ≤ (Work.Spaces.gam α
      * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) + 3
        * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) / 2) * J5 := by
    rw [hG5, hJ5]
    exact HardSlotBound (f := f) (v := Work.Spaces.mixed 0 4 g) (z := z)
      (q := Work.Spaces.gam α) (K := 10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
      (C := C5) (C' := C5') (p := 1)
      hgam_pos (by norm_num) hq4gam hKnn hC5 hC5' hdf hdg5 hf1 hf2 hv15 hv25
  -- the energy bounds
  have he1 : (Work.Spaces.w z) ^ 2 * J1 ≤ H := by
    rw [hJ1, hH]; exact slot_energy_dz hα hHk hzI
  have he2 : (Work.Spaces.w z) ^ 2 * J2 ≤ H := by
    rw [hJ2, hH]; exact slot_energy_mixed hα hHk hzI 3 1 (by norm_num) (by norm_num)
  have he3 : (Work.Spaces.w z) ^ 2 * J3 ≤ H := by
    rw [hJ3, hH]; exact slot_energy_mixed hα hHk hzI 2 2 (by norm_num) (by norm_num)
  have he4 : (Work.Spaces.w z) ^ 2 * J4 ≤ H := by
    rw [hJ4, hH]; exact slot_energy_mixed hα hHk hzI 1 3 (by norm_num) (by norm_num)
  have he5 : (Work.Spaces.w z) ^ 2 * J5 ≤ H := by
    rw [hJ5, hH]; exact slot_energy_mixed hα hHk hzI 0 4 (by norm_num) (by norm_num)
  -- the numerical bounds `q K + 3K/2 ≤ 3K`
  have hq1 : Work.Spaces.eta * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) + 3
      * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) / 2
      ≤ 3 * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) := by
    have h2 : Work.Spaces.eta = 99 / 100 := rfl
    rw [h2]; nlinarith [hWnn]
  have hq2 : Work.Spaces.gam α * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) + 3
      * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) / 2
      ≤ 3 * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) := by
    have h2 : Work.Spaces.gam α ≤ 11 / 10 := by rw [Work.Spaces.gam]; linarith
    nlinarith [hWnn]
  -- splitting the integral
  have hsplit : ∫ θ in Work.Spaces.Iθ, (G1 θ + (G2 θ + (G3 θ + (G4 θ + G5 θ))))
      = (∫ θ in Work.Spaces.Iθ, G1 θ)
        + ((∫ θ in Work.Spaces.Iθ, G2 θ)
          + ((∫ θ in Work.Spaces.Iθ, G3 θ)
            + ((∫ θ in Work.Spaces.Iθ, G4 θ) + ∫ θ in Work.Spaces.Iθ, G5 θ))) := by
    have hI2345 : MeasureTheory.IntegrableOn (G2 + (G3 + (G4 + G5))) Work.Spaces.Iθ :=
      hI2.add (hI3.add (hI4.add hI5))
    have hI345 : MeasureTheory.IntegrableOn (G3 + (G4 + G5)) Work.Spaces.Iθ :=
      hI3.add (hI4.add hI5)
    have hI45 : MeasureTheory.IntegrableOn (G4 + G5) Work.Spaces.Iθ := hI4.add hI5
    have h1 : ∫ θ in Work.Spaces.Iθ, (G1 θ + (G2 θ + (G3 θ + (G4 θ + G5 θ))))
        = (∫ θ in Work.Spaces.Iθ, G1 θ)
          + ∫ θ in Work.Spaces.Iθ, (G2 θ + (G3 θ + (G4 θ + G5 θ))) :=
      integral_add hI1 hI2345
    have h2 : ∫ θ in Work.Spaces.Iθ, (G2 θ + (G3 θ + (G4 θ + G5 θ)))
        = (∫ θ in Work.Spaces.Iθ, G2 θ)
          + ∫ θ in Work.Spaces.Iθ, (G3 θ + (G4 θ + G5 θ)) :=
      integral_add hI2 hI345
    have h3 : ∫ θ in Work.Spaces.Iθ, (G3 θ + (G4 θ + G5 θ))
        = (∫ θ in Work.Spaces.Iθ, G3 θ)
          + ∫ θ in Work.Spaces.Iθ, (G4 θ + G5 θ) :=
      integral_add hI3 hI45
    have h4 : ∫ θ in Work.Spaces.Iθ, (G4 θ + G5 θ)
        = (∫ θ in Work.Spaces.Iθ, G4 θ) + ∫ θ in Work.Spaces.Iθ, G5 θ :=
      integral_add hI4 hI5
    rw [h1, h2, h3, h4]
  have htri : |(∫ θ in Work.Spaces.Iθ, G1 θ)
        + ((∫ θ in Work.Spaces.Iθ, G2 θ)
          + ((∫ θ in Work.Spaces.Iθ, G3 θ)
            + ((∫ θ in Work.Spaces.Iθ, G4 θ) + ∫ θ in Work.Spaces.Iθ, G5 θ)))|
      ≤ |∫ θ in Work.Spaces.Iθ, G1 θ| + (|∫ θ in Work.Spaces.Iθ, G2 θ|
          + (|∫ θ in Work.Spaces.Iθ, G3 θ|
            + (|∫ θ in Work.Spaces.Iθ, G4 θ| + |∫ θ in Work.Spaces.Iθ, G5 θ|))) := by
    refine le_trans (abs_add_le _ _) (add_le_add le_rfl ?_)
    refine le_trans (abs_add_le _ _) (add_le_add le_rfl ?_)
    refine le_trans (abs_add_le _ _) (add_le_add le_rfl ?_)
    exact abs_add_le _ _
  -- the bound on the sum of the five slot integrals
  have hkey : |∫ θ in Work.Spaces.Iθ, (G1 θ + (G2 θ + (G3 θ + (G4 θ + G5 θ))))|
      ≤ 3 * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
        * (J1 + (J2 + (J3 + (J4 + J5)))) := by
    have h3Knn : (0 : ℝ) ≤ 3 * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) := by
      linarith [hKnn]
    calc |∫ θ in Work.Spaces.Iθ, (G1 θ + (G2 θ + (G3 θ + (G4 θ + G5 θ))))|
        = |(∫ θ in Work.Spaces.Iθ, G1 θ)
            + ((∫ θ in Work.Spaces.Iθ, G2 θ)
              + ((∫ θ in Work.Spaces.Iθ, G3 θ)
                + ((∫ θ in Work.Spaces.Iθ, G4 θ) + ∫ θ in Work.Spaces.Iθ, G5 θ)))| := by
          rw [hsplit]
      _ ≤ |∫ θ in Work.Spaces.Iθ, G1 θ| + (|∫ θ in Work.Spaces.Iθ, G2 θ|
            + (|∫ θ in Work.Spaces.Iθ, G3 θ|
              + (|∫ θ in Work.Spaces.Iθ, G4 θ| + |∫ θ in Work.Spaces.Iθ, G5 θ|))) := htri
      _ ≤ (Work.Spaces.eta * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) + 3
              * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) / 2) * J1
            + ((Work.Spaces.gam α * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) + 3
              * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) / 2) * J2
              + ((Work.Spaces.gam α * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) + 3
                * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) / 2) * J3
                + ((Work.Spaces.gam α * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) + 3
                  * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) / 2) * J4
                  + (Work.Spaces.gam α * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) + 3
                    * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) / 2) * J5))) := by
          exact add_le_add hb1 (add_le_add hb2 (add_le_add hb3 (add_le_add hb4 hb5)))
      _ ≤ 3 * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) * J1
            + (3 * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) * J2
              + (3 * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) * J3
                + (3 * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) * J4
                  + 3 * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) * J5))) := by
          exact add_le_add (mul_le_mul_of_nonneg_right hq1 hJ1nn)
            (add_le_add (mul_le_mul_of_nonneg_right hq2 hJ2nn)
              (add_le_add (mul_le_mul_of_nonneg_right hq2 hJ3nn)
                (add_le_add (mul_le_mul_of_nonneg_right hq2 hJ4nn)
                  (mul_le_mul_of_nonneg_right hq2 hJ5nn))))
      _ = 3 * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
            * (J1 + (J2 + (J3 + (J4 + J5)))) := by ring
  -- the final assembly
  rw [integral_const_mul, abs_mul, abs_of_nonneg (sq_nonneg (Work.Spaces.w z))]
  have hstep : (Work.Spaces.w z) ^ 2
        * |∫ θ in Work.Spaces.Iθ, (G1 θ + (G2 θ + (G3 θ + (G4 θ + G5 θ))))|
      ≤ 3 * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
        * ((Work.Spaces.w z) ^ 2 * J1 + ((Work.Spaces.w z) ^ 2 * J2
          + ((Work.Spaces.w z) ^ 2 * J3 + ((Work.Spaces.w z) ^ 2 * J4
            + (Work.Spaces.w z) ^ 2 * J5)))) := by
    refine le_trans (mul_le_mul_of_nonneg_left hkey (sq_nonneg _)) (le_of_eq ?_)
    ring
  refine le_trans hstep ?_
  have hstep2 : 3 * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
        * ((Work.Spaces.w z) ^ 2 * J1 + ((Work.Spaces.w z) ^ 2 * J2
          + ((Work.Spaces.w z) ^ 2 * J3 + ((Work.Spaces.w z) ^ 2 * J4
            + (Work.Spaces.w z) ^ 2 * J5))))
      ≤ 3 * (10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) * (H + (H + (H + (H + H)))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith [hKnn])
    exact add_le_add he1 (add_le_add he2 (add_le_add he3 (add_le_add he4 he5)))
  refine le_trans hstep2 ?_
  rw [hH]
  exact le_of_eq (by ring)

end Work.FTS.H2
