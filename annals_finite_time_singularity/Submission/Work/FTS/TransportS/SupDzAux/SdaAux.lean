import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.DynGEquation
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonEnergyAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## Elementary bounds on the two weights -/

/-- `1 ≤ (w z)²` for `z > 0`. -/
theorem one_le_w_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  have hz' : (1 : ℝ) ≤ (1 + z) / z := by
    rw [le_div_iff₀ hz]; linarith
  have hw : Work.Spaces.w z = ((1 + z) / z) ^ 2 := by rw [Work.Spaces.w, div_pow]
  rw [hw]
  exact one_le_pow₀ (one_le_pow₀ hz')

/-- `w z ≠ 0` for `z > 0`. -/
theorem w_ne_zero {z : ℝ} (hz : 0 < z) : Work.Spaces.w z ≠ 0 := by
  have h : Work.Spaces.w z = ((1 + z) / z) ^ 2 := by rw [Work.Spaces.w, div_pow]
  rw [h]
  exact pow_ne_zero 2 (div_ne_zero (by linarith) (ne_of_gt hz))

/-- `1 ≤ σ θ` on the open interval. -/
theorem one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ :=
  Work.FTS.EllipticEst.sliceLim_one_le_sEta hθ

/-- `0 ≤ σ θ` on `Iθ`. -/
theorem sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-- `σ` is integrable on `Iθ` (the `p = -η` case of `sin_two_rpow`). -/
theorem sEta_integrableOn :
    IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
  (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
    (by norm_num [Work.Spaces.eta])).1


/-- `volume.restrict Iθ = volume.restrict (0,π/2)`: the two endpoints are a null set. -/
theorem restrict_Iθ_eq_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm


/-! ## The level-`0` integrand in product form -/

/-- **The level-`0` `Hk`-integrand as a product**: on `Iθ`,
`HkIntegrand α 0 g z θ = w(z)² · (g z θ² · σ θ)`. -/
theorem HkIntegrand_zero_eq' {α : ℝ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (g : ℝ → ℝ → ℝ)
    (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  rw [HkIntegrand_zero_eq, sq_profile_eq g z θ (sin_two_nonneg_of_mem_Iθ hθ),
    Work.FTS.EllipticEst.sEta]
  ring

/-- The same identity almost everywhere on `Iθ`. -/
theorem HkIntegrand_zero_eq_ae (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (fun θ => Work.Spaces.HkIntegrand α 0 g z θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
  rw [Filter.EventuallyEq, Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards with θ hθ
  exact HkIntegrand_zero_eq' hθ g z

/-! ## Slicewise integrability provided by the honesty of the class -/

/-- **The `θ`-slice of `∂_θθΨ` is `σ`-square integrable**, for every `z > 0`: this is the first
component of `memB`. -/
theorem hon_memB_sigma {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have h2 := (h.memB.1 z (le_of_lt hz)).congr
    (HkIntegrand_zero_eq_ae α (Work.Spaces.pthIter 2 Ψ) z)
  have h4 := h2.const_mul (1 / (Work.Spaces.w z) ^ 2)
  have h3 : (fun θ => (1 / (Work.Spaces.w z) ^ 2)
        * ((Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)))
      = fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    funext θ
    rw [← mul_assoc, one_div, inv_mul_cancel₀ (pow_ne_zero 2 (w_ne_zero hz)), one_mul]
  rw [h3] at h4
  exact h4


/-- **The `θ`-slice of `F` is `σ`-square integrable**, for every `z > 0`: this is the first component
of `memF`. -/
theorem hon_memF_sigma {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  have h2 := (h.memF.1 z (le_of_lt hz)).congr (HkIntegrand_zero_eq_ae α F z)
  have h4 := h2.const_mul (1 / (Work.Spaces.w z) ^ 2)
  have h3 : (fun θ => (1 / (Work.Spaces.w z) ^ 2)
        * ((Work.Spaces.w z) ^ 2 * ((F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      = fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    funext θ
    rw [← mul_assoc, one_div, inv_mul_cancel₀ (pow_ne_zero 2 (w_ne_zero hz)), one_mul]
  rw [h3] at h4
  exact h4

/-- **Unweighted transfer**: a slice that is a.e. strongly measurable and `σ`-square integrable is
square integrable (because `σ ≥ 1` a.e. on `Iθ`). -/
theorem integrableOn_sq_of_sigma {g : ℝ → ℝ}
    (haesm : AEStronglyMeasurable g (volume.restrict Work.Spaces.Iθ))
    (h : IntegrableOn (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => (g θ) ^ 2) Work.Spaces.Iθ := by
  refine Integrable.mono' (μ := volume.restrict Work.Spaces.Iθ) h (haesm.pow 2) ?_
  rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  have h0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 := by
    rw [MeasureTheory.ae_iff]; simp
  have h1 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ Real.pi / 2 := by
    rw [MeasureTheory.ae_iff]; simp
  filter_upwards [h0, h1] with θ hθ0 hθ1 hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hioo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0), lt_of_le_of_ne hθ.2 hθ1⟩
  have hs : (1 : ℝ) ≤ Work.FTS.EllipticEst.sEta θ := one_le_sEta hioo
  nlinarith [hs, sq_nonneg (g θ)]

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.TransportS.SupDzAux.SdaAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.SupDzAux

/-- A multiplier depending on the angle only passes through the radial iterates `D_z^j`:
`D_z^j (c(θ) · g) (z,θ) = c(θ) · D_z^j g (z,θ)`. -/
theorem sda_DzIter_const_mul_th (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => c θ * g z θ) z θ
      = c θ * Work.Spaces.DzIter j g z θ := by
  induction j generalizing z θ with
  | zero => rfl
  | succ j ih =>
      show z * deriv (fun z' => Work.Spaces.DzIter j (fun z θ => c θ * g z θ) z' θ) z
        = c θ * (z * deriv (fun z' => Work.Spaces.DzIter j g z' θ) z)
      have hev : (fun z' => Work.Spaces.DzIter j (fun z θ => c θ * g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => c θ * Work.Spaces.DzIter j g z' θ) :=
        Filter.Eventually.of_forall fun z' => ih z' θ
      rw [hev.deriv_eq, deriv_const_mul_field]
      ring

/-- **The mixed slot is the angular derivative of the radial iterate**, on the open quadrant:
`D_z^j D_θ f = sin(2θ) · ∂_θ(D_z^j f)` for `f` of class `C^∞` on the open quadrant. -/
theorem sda_mixed_one_eq_sin_pth {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π/2)) :
    Work.Spaces.mixed j 1 f z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter j f) z θ := by
  have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hid : Work.Spaces.pth (Work.Spaces.DzIter j f) z θ
      = Work.Spaces.DzIter j (Work.Spaces.pth f) z θ :=
    Work.Blocks.pth_DzIter_eqOn_Q0 hf j hQ
  rw [hid]
  have hDth : Work.Spaces.DthIter 1 f
      = (fun z θ => Real.sin (2 * θ) * Work.Spaces.pth f z θ) := rfl
  show Work.Spaces.DzIter j (Work.Spaces.DthIter 1 f) z θ
      = Real.sin (2 * θ) * Work.Spaces.DzIter j (Work.Spaces.pth f) z θ
  rw [hDth, sda_DzIter_const_mul_th]

/-- The angular weight `sin(2θ)^{2-γ}` applied to the square of `∂_θ(D_z^b f)` is dominated by
the `ℋ⁴`-integrand (the `θ`-derivative of a `D_z`-iterate is a mixed slot, and `1 ≤ w`). -/
theorem sda_ang_slice_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {b : ℕ} (hb : b ≤ 2) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π/2)) :
    (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hid := sda_mixed_one_eq_sin_pth hf b hz hθ
  have hwt := Work.Spaces.bt_mixed_weight_gen α z θ hα hα1 hθI
    (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) (Work.Spaces.mixed b 1 f z θ) hid
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  have hnn : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hsin _) (sq_nonneg _)
  have hw1 : 1 ≤ Work.Spaces.w z := Work.FTS.TransportS.one_le_w hz
  have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ hw1 (n := 2)
  calc (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
      ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
        le_mul_of_one_le_right hnn hw2
    _ = (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by ring
    _ = (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := hwt
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ 1 b le_rfl (by omega)

/-- The angular weight `sin(2θ)^{2-γ}` applied to `(w · ∂_θ(D_z^{b+1} f))²` is dominated by the
`ℋ⁴`-integrand: this is the `(mixed (b+1) 1 f · Wt)²` slot. -/
theorem sda_ang_slice_le_w {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {b : ℕ} (hb : b ≤ 2) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π/2)) :
    (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth (Work.Spaces.DzIter (b+1) f) z θ * Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hid := sda_mixed_one_eq_sin_pth hf (b+1) hz hθ
  have hwt := Work.Spaces.bt_mixed_weight_gen α z θ hα hα1 hθI
    (Work.Spaces.pth (Work.Spaces.DzIter (b+1) f) z θ) (Work.Spaces.mixed (b+1) 1 f z θ) hid
  calc (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth (Work.Spaces.DzIter (b+1) f) z θ * Work.Spaces.w z) ^ 2
      = (Work.Spaces.pth (Work.Spaces.DzIter (b+1) f) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by ring
    _ = (Work.Spaces.mixed (b+1) 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := hwt
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ 1 (b+1) (by omega) (by omega)

/-- **Tonelli for the `ℋ⁴`-integrand of an open-class datum.**  For `F` of class `C^∞` on the
open quadrant with `HkMem α 4 F`, the iterated integral of `HkIntegrand α 4 F` in the order
`∫_θ ∫_z` equals `HkSq α 4 F`, its partially integrated function is integrable on the angles, and
for almost every angle the radial slice is integrable.  (The `SmoothOpen`-version of
`Work.FTS.H2.HkSqSwap`.) -/
theorem sda_HkSqSwap_open (α : ℝ) (f : ℝ → ℝ → ℝ) (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) :
    (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ
        = Work.Spaces.HkSq α 4 f) ∧
      MeasureTheory.Integrable
        (fun σ : ℝ => ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s σ)
          Work.Spaces.Iz) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry fun z θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_HkIntegrand α 4)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz)
  have houter : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2
  obtain ⟨h1, h2, h3⟩ :=
    Work.FTS.H2.swap_iterated_integral_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hnn haesm hslice houter
  exact ⟨by rw [Work.Spaces.HkSq]; exact h1, h2, h3⟩

end Work.FTS.TransportS.SupDzAux
end
end
