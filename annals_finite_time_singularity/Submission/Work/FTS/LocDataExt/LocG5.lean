/-
# `Work.FTS.LocDataExt.LocG5` — the order-`5` membership and `RegQ α 5` of the localised datum

This module assembles the order-`5` interior-regularity class of the localised datum of N9,
using the generic separable majorant of `Majorant5.lean`:

* `hB_zfar5` — the radial bound for the far summand `-(α/c)·zfarR L·Γ`: below `L` the cut-off
  kills it, above `L` the (uniform in `L`) jet bound `|D_z^j zfarR L| ≤ A/z` and `w² ≤ 64/(1+z)²`
  give `((D_z^j·)·w)² ≤ (α/c)²A²·64/(1+z)²`;
* `zfarR_jet_le5_Ici` — the jet bound for `zfarR L` on all of `[L,∞)`: on `[L,2L]` from the
  uniform estimate, beyond `2L` from the jets of `FM.Fstar` (where `zfarR L` agrees with
  `FM.Fstar`), so the two order-`5` jet inputs are the *only* hypotheses of the assembly;
* `HkIntegrand_locG_le5`, `HkMem_locG5`, `regQ_locG5` — the pointwise majorant, the membership
  and the class `RegQ α 5`;
* `galData_exists5` — the order-`5` form of the chapter's deliverable (the four hypotheses of
  `galerkin_bound` at the datum, with `RegQ α 5` in place of `RegQ α 4`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocDataExt.Majorant5
import Submission.Work.FTS.LocDataExt.Traces
import Submission.Work.FTS.LocData.Main
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The radial bound for the far summand -/

/-- **The radial bound of the far summand** `-(α/c)·zfarR L z`: from the jet bound
`|D_z^j zfarR L z| ≤ A/z` (on `z ≥ L`; below `L` the cut-off vanishes). -/
theorem hB_zfar5 (α L : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L)
    (hAz : ∀ j ≤ 5, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => zfarR L z) z θ| ≤ A / z) :
    ∀ j ≤ 5, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => -(α / Work.Spaces.c α) * zfarR L z) z θ
          * Work.Spaces.w z) ^ 2
        ≤ ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) / (1 + z) ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro j hj z hz θ
  rw [DzIter_const_mul]
  have hsplit : ((-(α / Work.Spaces.c α)
        * Work.Spaces.DzIter j (fun z _ => zfarR L z) z θ) * Work.Spaces.w z) ^ 2
      = (α / Work.Spaces.c α) ^ 2
        * ((Work.Spaces.DzIter j (fun z _ => zfarR L z) z θ) * Work.Spaces.w z) ^ 2 := by
    ring
  rw [hsplit]
  have hmain : ((Work.Spaces.DzIter j (fun z _ => zfarR L z) z θ) * Work.Spaces.w z) ^ 2
      ≤ A ^ 2 * 64 / (1 + z) ^ 2 := by
    by_cases hzL : z < L
    · -- the cut-off vanishes near `z`
      have hzabs : |z| < L := by rw [abs_of_nonneg hz]; exact hzL
      have hev : ∀ᶠ z' in 𝓝 z, zfarR L z' = 0 := by
        filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hzabs] with z' hz'
        rw [zfarR_apply, Work.Stability.chi_eq_one (by
          rw [abs_div, abs_of_pos hLpos, div_le_one hLpos]
          exact le_of_lt hz')]
        ring
      have hzero : Work.Spaces.DzIter j (fun z _ => zfarR L z) z θ = 0 :=
        Work.FTS.LocData.ZFBase.DzIter_eq_zero_of_eventually_zero
          (hev.mono (fun z' hz' => fun _ => hz')) j
      rw [hzero]
      have : 0 ≤ A ^ 2 * 64 / (1 + z) ^ 2 :=
        div_nonneg (mul_nonneg (sq_nonneg A) (by norm_num)) (sq_nonneg _)
      simpa using this
    · push_neg at hzL
      have hzpos : 0 < z := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hL) hzL
      have h1 := hAz j hj z hzL θ
      have h2 : ((Work.Spaces.DzIter j (fun z _ => zfarR L z) z θ) * Work.Spaces.w z) ^ 2
          ≤ (A / z * Work.Spaces.w z) ^ 2 := by
        rw [mul_pow, mul_pow]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have h3 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rwa [sq_abs] at h3
      refine h2.trans ?_
      have hnum : (1 + z) ^ 4 / z ^ 6 ≤ 64 / (1 + z) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 6) (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
        have h : (1 + z) ^ 6 ≤ 64 * z ^ 6 := by
          have h1 : 1 + z ≤ 2 * z := by linarith
          calc (1 + z) ^ 6 ≤ (2 * z) ^ 6 := pow_le_pow_left₀ (by linarith) h1 6
            _ = 64 * z ^ 6 := by ring
        nlinarith [h]
      calc (A / z * Work.Spaces.w z) ^ 2 = A ^ 2 * ((1 + z) ^ 4 / z ^ 6) := by
            rw [Work.Spaces.w]
            field_simp <;> ring
        _ ≤ A ^ 2 * (64 / (1 + z) ^ 2) := mul_le_mul_of_nonneg_left hnum (sq_nonneg A)
        _ = A ^ 2 * 64 / (1 + z) ^ 2 := by ring
  calc (α / Work.Spaces.c α) ^ 2
        * ((Work.Spaces.DzIter j (fun z _ => zfarR L z) z θ) * Work.Spaces.w z) ^ 2
      ≤ (α / Work.Spaces.c α) ^ 2 * (A ^ 2 * 64 / (1 + z) ^ 2) :=
        mul_le_mul_of_nonneg_left hmain (sq_nonneg _)
    _ = (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64 / (1 + z) ^ 2 := by ring

/-! ## The jet bound for `zfarR L` on all of `[L,∞)` -/

/-- **The `D_z`-jets of `zfarR L` decay like `1/z` on `[L,∞)`**: on `[L,2L]` from the uniform
estimate `hAz`, beyond `2L` from the jets of `FM.Fstar` (with which `zfarR L` agrees there). -/
theorem zfarR_jet_le5_Ici (L : ℝ) (hL : 1 ≤ L) {A CF : ℝ} (hA : 0 ≤ A) (hCF : 0 ≤ CF)
    (hAz : ∀ j ≤ 5, ∀ z ∈ Set.Icc L (2 * L), ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => zfarR L z) z θ| ≤ A / z)
    (hF : ∀ j ≤ 5, ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z) :
    ∀ j ≤ 5, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => zfarR L z) z θ| ≤ max A CF / z := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro j hj z hz θ
  have hzpos : 0 < z := lt_of_lt_of_le hLpos hz
  by_cases h : z ≤ 2 * L
  · have h1 := hAz j hj z ⟨hz, h⟩ θ
    refine h1.trans ?_
    exact div_le_div_of_nonneg_right (le_max_left A CF) (le_of_lt hzpos)
  · push_neg at h
    -- beyond `2L`, `zfarR L` agrees with `FM.Fstar`
    have hev : ∀ᶠ z' in 𝓝 z, zfarR L z' = Work.FM.Fstar z' := by
      filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds h] with z' hz'
      exact zfarR_eq_FM_Fstar_of_ge hLpos (le_of_lt hz')
    rw [DzIter_z_congr_of_eventuallyEq (σ := fun z => Work.FM.Fstar z) hev j θ]
    have h1 := hF j hj z (by linarith) θ
    refine h1.trans ?_
    exact div_le_div_of_nonneg_right (le_max_right A CF) (le_of_lt hzpos)

/-! ## The pointwise majorant of the `ℋ⁵`-integrand of `locG`, and the membership -/

/-- The localised perturbation as the sum of its far and bump parts (pointwise). -/
theorem locG_split (α L β : ℝ) :
    Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)
      = fun z θ => (-(α / Work.Spaces.c α) * zfarR L z) * Work.Spaces.Gam α θ
          + (β * Work.FTS.LocData.bumpZ z) * Work.Spaces.Gam α θ := by
  funext z θ
  rw [locG_eq_locR_Gam]
  change locR α L β z * Work.Spaces.Gam α θ
    = -(α / Work.Spaces.c α) * zfarR L z * Work.Spaces.Gam α θ
      + β * Work.FTS.LocData.bumpZ z * Work.Spaces.Gam α θ
  rw [locR_apply]
  ring

/-- **The pointwise `ℋ⁵`-majorant of the localised datum**, from the two radial jet bounds. -/
theorem HkIntegrand_locG_le5 (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) {A : ℝ}
    (hA : 0 ≤ A)
    (hAz : ∀ j ≤ 5, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => zfarR L z) z θ| ≤ A / z) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 5 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) z θ
        ≤ K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
  obtain ⟨R₂, hR₂, hB₂⟩ := hB_bumpZ5
  have hR₁ : 0 ≤ (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64 := by positivity
  have hB₁ := hB_zfar5 (A := A) α L hA hL hAz
  set R₂' : ℝ := β ^ 2 * R₂ with hR₂'def
  have hR₂' : 0 ≤ R₂' := by rw [hR₂'def]; positivity
  have hB₂' : ∀ j ≤ 5, ∀ z ∈ Work.Spaces.Iz, ∀ θ' : ℝ,
      (Work.Spaces.DzIter j (fun z _ => β * Work.FTS.LocData.bumpZ z) z θ'
          * Work.Spaces.w z) ^ 2 ≤ R₂' / (1 + z) ^ 2 := by
    intro j hj z hz θ'
    rw [DzIter_const_mul]
    have h := hB₂ j hj z hz θ'
    rw [show (β * Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ'
          * Work.Spaces.w z) ^ 2
        = β ^ 2 * ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ'
          * Work.Spaces.w z) ^ 2) from by ring, hR₂'def]
    calc β ^ 2 * ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ'
          * Work.Spaces.w z) ^ 2)
        ≤ β ^ 2 * (R₂ / (1 + z) ^ 2) := mul_le_mul_of_nonneg_left h (sq_nonneg β)
      _ = β ^ 2 * R₂ / (1 + z) ^ 2 := by ring
  have hcpos : 0 < Work.Spaces.c α := by
    exact lt_of_lt_of_le (by norm_num) (Work.FTS.LocData.c_ge_three_fifths α hα hα1)
  have hs1 : Work.FTS.LocData.SmoothQuad
      (fun z θ => (-(α / Work.Spaces.c α) * zfarR L z) * Work.Spaces.Gam α θ) :=
    smoothQuad_sepGam (α := α) (by
      refine (ContDiffOn.const_smul (-(α / Work.Spaces.c α)) (contDiffOn_zfarR L)).congr
        (fun z _ => ?_)
      simp [smul_eq_mul])
  have hs2 : Work.FTS.LocData.SmoothQuad
      (fun z θ => (β * Work.FTS.LocData.bumpZ z) * Work.Spaces.Gam α θ) :=
    smoothQuad_sepGam (α := α) (by
      refine (ContDiffOn.const_smul β (Work.FTS.LocData.contDiff_bumpZ.contDiffOn)).congr
        (fun z _ => ?_)
      simp [smul_eq_mul])
  refine ⟨2 * (((6 : ℝ) + 36 * 10 ^ 10) * (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64)
      + 2 * ((6 : ℝ) + 36 * 10 ^ 10) * R₂', by positivity, fun z hz θ hθ => ?_⟩
  have hΓ : ∀ i ≤ 5, ∀ θ' ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ') ^ 2
        ≤ (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ') ^ 2 :=
    fun i hi θ' hθ' => hGam5 α hα hα1 hi hθ'
  have hA1 := HkIntegrand_sepGam_le α hα 5 (ρ := fun z => -(α / Work.Spaces.c α) * zfarR L z)
    (R := (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) (Rθ := (10 : ℝ) ^ 10) hR₁ (by positivity)
    (fun j hj z hz θ' => hB₁ j hj z hz θ') hΓ hz hθ
  have hA2 := HkIntegrand_sepGam_le α hα 5 (ρ := fun z => β * Work.FTS.LocData.bumpZ z)
    (R := R₂') (Rθ := (10 : ℝ) ^ 10) hR₂' (by positivity)
    (fun j hj z hz θ' => hB₂' j hj z hz θ') hΓ hz hθ
  rw [locG_split α L β]
  refine (Work.FTS.LocData.HkIntegrand_add_le α 5 hs1 hs2 hz hθ).trans ?_
  refine (add_le_add (mul_le_mul_of_nonneg_left hA1 (by norm_num))
    (mul_le_mul_of_nonneg_left hA2 (by norm_num))).trans ?_
  push_cast
  exact le_of_eq (by ring)

/-- **The localised datum lies in `ℋ⁵`**, from the two radial jet bounds. -/
theorem HkMem_locG5 (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) {A : ℝ} (hA : 0 ≤ A)
    (hAz : ∀ j ≤ 5, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => zfarR L z) z θ| ≤ A / z) :
    Work.Spaces.HkMem α 5 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) := by
  obtain ⟨K, hK, hmaj⟩ := HkIntegrand_locG_le5 α L β hα hα1 hL hA hAz
  refine Work.FTS.LocData.HkMem_of_majorant
    (f := Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α))
    (M := fun z θ => K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) α 5
    (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 5 _
      (Work.FTS.LocData.SmoothQuad_locG α L β hα hα1 (Work.FTS.LocData.SmoothQuad_hLoc α))) ?_ ?_ ?_
  · intro z hz
    exact (Work.FTS.LocData.integrableOn_angMaj_majorant α K hα hα1).1 z hz
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α K hα hα1).2
  · intro z hz θ hθ
    exact hmaj z hz θ hθ

/-- **The localised datum lies in `RegQ α 5`**, from the two radial jet bounds (`A` for the far
factor `zfarR L`, `CF` for the plain profile `FM.Fstar`; the angular jet is
`DthIter_Gam_abs_le5`, unconditional). -/
theorem regQ_locG5 (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) {A CF : ℝ} (hA : 0 ≤ A)
    (hCF : 0 ≤ CF)
    (hAz : ∀ j ≤ 5, ∀ z ∈ Set.Icc L (2 * L), ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => zfarR L z) z θ| ≤ A / z)
    (hF : ∀ j ≤ 5, ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z) :
    Work.FTS.Nonlin.RegQ α 5 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) := by
  refine ⟨Work.FTS.LocData.SmoothQuad_locG α L β hα hα1 (Work.FTS.LocData.SmoothQuad_hLoc α),
    HkMem_locG5 α L β hα hα1 hL (le_trans hA (le_max_left A CF))
      (zfarR_jet_le5_Ici L hL hA hCF hAz hF), ?_⟩
  refine bdryTraces_locG α L β hα hL (k := 5) (CΓ := 100000) (CF := CF) (by norm_num) hCF ?_ hF
  intro i hi θ hθ
  exact DthIter_Gam_abs_le5 i hi α hα hα1 hθ

/-! ## The order-`5` deliverable -/

/-- **The order-`5` deliverable**: the localised datum satisfies the hypotheses of
`galerkin_bound` with `RegQ α 5` in place of `RegQ α 4`.  The two radial jet bounds are the
only inputs beyond N9 (the angular jet `DthIter_Gam_abs_le5` and the traces are unconditional
here). -/
theorem galData_exists5 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {A CF : ℝ} (hA : 0 ≤ A) (hCF : 0 ≤ CF)
    (hAz : ∀ L : ℝ, 1 ≤ L → ∀ j ≤ 5, ∀ z ∈ Set.Icc L (2 * L), ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => zfarR L z) z θ| ≤ A / z)
    (hF : ∀ j ≤ 5, ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∃ β : ℝ,
      |β| ≤ α ^ 2 ∧
      Work.FTS.LocData.DataAdm α (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) ∧
      Work.Construction.L12 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) 0 = 0 ∧
      Work.FTS.Nonlin.RegQ α 5 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) ≤ α ^ 2 := by
  obtain ⟨L₀, hL₀⟩ := Work.FTS.LocData.locData_small α hα hα1 (α ^ 2) (by positivity)
  refine ⟨max L₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  obtain ⟨β, hβ, hL12, hnorm, hadm⟩ := hL₀ L (le_trans (le_max_left _ _) hL)
  exact ⟨β, hβ, hadm, hL12, regQ_locG5 α L β hα hα1 hL1 hA hCF (hAz L hL1) hF, hnorm⟩

end Work.FTS.LocDataExt
