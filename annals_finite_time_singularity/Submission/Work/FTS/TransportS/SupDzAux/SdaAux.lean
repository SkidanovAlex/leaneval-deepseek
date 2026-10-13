/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliaries for the weighted angular `∂_θ D_z^b` bound `sup_dz_ang_le`

This module collects the five ingredients of the proof of
`Work.FTS.TransportS.SupDzAux.sup_dz_ang_le`
(`Submission/Work/FTS/TransportS/SupDzAux/sup_dz_ang_le.lean`):

* `sda_DzIter_const_mul_th` — `D_z^j (c(θ) · g) = c(θ) · D_z^j g` (a multiplier depending on
  the angle only passes through the radial iterates);
* `sda_mixed_one_eq_sin_pth` — on the open quadrant and for an open-class `C^∞` datum,
  `D_z^j D_θ f = sin(2θ) · ∂_θ (D_z^j f)`: the identity that turns the angular derivative of the
  radial iterate into the mixed slot of the `ℋ⁴`-integrand.  It is
  `Work.Blocks.pth_DzIter_eqOn_Q0` (`∂_θ` commutes with `D_z^j` on the quadrant) together with
  `D_θ f = sin(2θ) ∂_θ f`;
* `sda_ang_slice_le`, `sda_ang_slice_le_w` — the two pointwise domination statements that make
  the window inequality of `Work.FTS.TransportS.half_line_window_bound` fit the weight
  `sin(2θ)^{2-γ}`.  Both are the pure algebra of `Work.Spaces.bt_mixed_weight_gen` followed by a
  single slot bound `Work.Spaces.sq_le_HkIntegrand_mixed`;
* `sda_HkSqSwap_open` — Tonelli for the `ℋ⁴`-integrand of an **open-class** datum: the iterated
  integral `∫_θ ∫_z HkIntegrand α 4 f` is `HkSq α 4 f`, its partially integrated function is
  integrable, and for almost every angle the radial slice is integrable.  This is the
  `SmoothOpen`-version of `Work.FTS.H2.HkSqSwap` (whose hypothesis is the stronger, analytic
  `SmoothNbhd`); the a.e. strong measurability comes from
  `Work.Spaces.aesm_of_continuousOn_Qd` applied to
  `Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`.

All declarations are `sorry`-free and rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.bt_aux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow
import Submission.Work.FTS.H2.HkSqSwap
import Submission.Work.Blocks.alphaDz_pth_core_clean

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
