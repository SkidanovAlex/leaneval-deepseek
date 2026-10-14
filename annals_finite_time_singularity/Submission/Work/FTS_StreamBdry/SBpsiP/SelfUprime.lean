import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS_StreamBdry.SB0.sb0_gauge_alg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB0

theorem sb0_gauge_alg {a ρ B θ κ Ainv : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hB : 0 < B) :
    ρ ^ 2 * Ainv * (κ * ((ρ ^ (3 * a) / B) ^ (-(3 / (3 * a))) / Real.cos θ))
      = κ * Ainv * B ^ (1 / a) / (ρ * Real.cos θ) := by
  -- `-(3/(3a)) = -(1/a)`, and `(ρ^(3a)/B)^(-(1/a)) = ρ^(-3)·B^(1/a)`.
  have hD : (ρ ^ (3 * a) / B) ^ (-(3 / (3 * a))) = ρ ^ (-3 : ℝ) * B ^ (1 / a) := by
    have h3 : (3 : ℝ) / (3 * a) = 1 / a := by field_simp
    have e1 : (3 : ℝ) * a * (-(1 / a)) = -3 := by field_simp
    have e2 : (-1 : ℝ) * (-(1 / a)) = 1 / a := by field_simp
    have h1 : ρ ^ (3 * a) / B = ρ ^ (3 * a) * B⁻¹ := by rw [div_eq_mul_inv]
    rw [h1, h3, Real.mul_rpow (Real.rpow_nonneg hρ.le _) (inv_nonneg.mpr hB.le)]
    rw [← Real.rpow_mul hρ.le (3 * a) (-(1 / a)), e1]
    rw [← Real.rpow_neg_one B]
    rw [← Real.rpow_mul hB.le (-1) (-(1 / a)), e2]
  -- the radial powers `ρ² · ρ^(-3) = ρ⁻¹`.
  have hρinv : ρ ^ (2 : ℕ) * ρ ^ (-3 : ℝ) = ρ⁻¹ := by
    have h2 := Real.rpow_add hρ (2 : ℝ) (-3)
    rw [show (2 : ℝ) + (-3) = (-1 : ℝ) by norm_num, Real.rpow_neg_one] at h2
    rw [Real.rpow_ofNat ρ 2] at h2
    exact h2.symm
  by_cases hc : Real.cos θ = 0
  · simp [hc]
  · have step2 : ρ ^ 2 * ((ρ ^ (3 * a) / B) ^ (-(3 / (3 * a)))) = B ^ (1 / a) * ρ⁻¹ := by
      rw [hD]
      rw [show ρ ^ 2 * (ρ ^ (-3 : ℝ) * B ^ (1 / a))
            = (ρ ^ 2 * ρ ^ (-3 : ℝ)) * B ^ (1 / a) by ring, hρinv]
      ring
    calc ρ ^ 2 * Ainv * (κ * ((ρ ^ (3 * a) / B) ^ (-(3 / (3 * a))) / Real.cos θ))
        = (ρ ^ 2 * ((ρ ^ (3 * a) / B) ^ (-(3 / (3 * a))))) * (Ainv * κ / Real.cos θ) := by
          ring
      _ = (B ^ (1 / a) * ρ⁻¹) * (Ainv * κ / Real.cos θ) := by rw [step2]
      _ = κ * Ainv * B ^ (1 / a) / (ρ * Real.cos θ) := by field_simp

end Work.FTS_StreamBdry.SB0
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB0.sb0_hsm_psiHatP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB0

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.StreamBdryIface (oddPerS psiHatP psiP)

set_option autoImplicit false

/-- `psiHatP` agrees with the odd-extended `U`-slot part of the canonical slice on the
half-plane `w > 0` (on `w ≤ 0` it is identically `0` by definition). -/
lemma psiHatP_eq_oddPerS {αG : ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam} {τ : ℝ} :
    ∀ w θ : ℝ, 0 < w →
      psiHatP αG Φs E g w θ τ = oddPerS (psiP αG (slice (PsiCan Φs E g) τ)) w θ := by
  intro w θ hw
  simp [psiHatP, hw]

theorem sb0_hsm_psiHatP {a : ℝ} (ha : 0 < a) {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hPsm : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 2
      (Function.uncurry (Work.FTS.StreamBdryIface.oddPerS
        (Work.FTS.StreamBdryIface.psiP (Work.FTS.Regularity.pExp a)
          (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))))
      (Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2) - 1) (Real.pi / 2 + 1)))
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ w θ : ℝ, 0 < w → 0 < θ → θ < Real.pi / 2 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ =>
        Work.FTS.StreamBdryIface.psiHatP (Work.FTS.Regularity.pExp a) Φs E g p.1 p.2 τ) (w, θ) := by
  intro w θ hw _hθ _hθlt
  -- the half-strip `Ioi 0 ×ˢ Ioo (-(π/2)-1) (π/2+1)` is an open neighbourhood of `(w,θ)`
  have hopen : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2) - 1) (Real.pi / 2 + 1)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hmem : (w, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2) - 1) (Real.pi / 2 + 1) :=
    ⟨hw, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  -- on that half-strip `psiHatP` coincides with the uncurried `oddPerS ∘ psiP` (since `w' > 0` there)
  have hcongr : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ =>
        Work.FTS.StreamBdryIface.psiHatP (Work.FTS.Regularity.pExp a) Φs E g p.1 p.2 τ)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2) - 1) (Real.pi / 2 + 1)) :=
    (hPsm τ hτ).congr (by
      rintro ⟨p1, p2⟩ ⟨hp1, -⟩
      simp only [Function.uncurry]
      exact psiHatP_eq_oddPerS p1 p2 hp1)
  exact hcongr.contDiffAt (hopen.mem_nhds hmem)

end Work.FTS_StreamBdry.SB0
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB0.sb0_psiFieldAdd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB0

theorem sb0_psiFieldAdd {f g : ℝ → ℝ → ℝ} {x : Work.Cyl.R3}
    (hf : DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) (Work.Cyl.radial x, Work.Cyl.axial x))
    (hg : DifferentiableAt ℝ (fun p : ℝ × ℝ => g p.1 p.2) (Work.Cyl.radial x, Work.Cyl.axial x)) :
    Work.Cyl.psiField (fun r z => f r z + g r z) x = Work.Cyl.psiField f x + Work.Cyl.psiField g x := by
  -- the two slices of `f` and `g` at `(r, z) = (radial x, axial x)`
  have hfz : DifferentiableAt ℝ (fun z' : ℝ => f (Work.Cyl.radial x) z') (Work.Cyl.axial x) :=
    Work.Cyl.differentiableAt_slice_snd f _ _ hf
  have hgz : DifferentiableAt ℝ (fun z' : ℝ => g (Work.Cyl.radial x) z') (Work.Cyl.axial x) :=
    Work.Cyl.differentiableAt_slice_snd g _ _ hg
  have hfr : DifferentiableAt ℝ (fun r' : ℝ => f r' (Work.Cyl.axial x)) (Work.Cyl.radial x) :=
    Work.Cyl.differentiableAt_slice_fst f _ _ hf
  have hgr : DifferentiableAt ℝ (fun r' : ℝ => g r' (Work.Cyl.axial x)) (Work.Cyl.radial x) :=
    Work.Cyl.differentiableAt_slice_fst g _ _ hg
  -- additivity of the two partial derivatives at that point
  have hpz : Work.Cyl.pdZ (fun r z => f r z + g r z) (Work.Cyl.radial x) (Work.Cyl.axial x)
      = Work.Cyl.pdZ f (Work.Cyl.radial x) (Work.Cyl.axial x)
        + Work.Cyl.pdZ g (Work.Cyl.radial x) (Work.Cyl.axial x) := by
    unfold Work.Cyl.pdZ
    exact deriv_add hfz hgz
  have hpr : Work.Cyl.pdR (fun r z => f r z + g r z) (Work.Cyl.radial x) (Work.Cyl.axial x)
      = Work.Cyl.pdR f (Work.Cyl.radial x) (Work.Cyl.axial x)
        + Work.Cyl.pdR g (Work.Cyl.radial x) (Work.Cyl.axial x) := by
    unfold Work.Cyl.pdR
    exact deriv_add hfr hgr
  -- `psiField = cylField (∂_zψ) (-ψ/r - ∂_rψ)`, and `cylField` acts pointwise
  simp only [Work.Cyl.psiField, Work.Cyl.cylField, hpz, hpr]
  rw [add_div, add_smul,
    show -((f (Work.Cyl.radial x) (Work.Cyl.axial x)
            + g (Work.Cyl.radial x) (Work.Cyl.axial x)) / Work.Cyl.radial x)
        - (Work.Cyl.pdR f (Work.Cyl.radial x) (Work.Cyl.axial x)
           + Work.Cyl.pdR g (Work.Cyl.radial x) (Work.Cyl.axial x))
      = (-(f (Work.Cyl.radial x) (Work.Cyl.axial x) / Work.Cyl.radial x)
          - Work.Cyl.pdR f (Work.Cyl.radial x) (Work.Cyl.axial x))
        + (-(g (Work.Cyl.radial x) (Work.Cyl.axial x) / Work.Cyl.radial x)
          - Work.Cyl.pdR g (Work.Cyl.radial x) (Work.Cyl.axial x)) from by
      rw [add_div]; ring]
  rw [add_smul]
  abel

end Work.FTS_StreamBdry.SB0
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB0.sb0_psiFieldJump =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB0.sb0_psiFieldJump`

The meridian stream function produced by the StreamBdry reduction is
`ψ(r,z) = c/r` for `z > 0` and `ψ(r,z) = -c/r` for `z ≤ 0` — the odd extension in `z` of
`c/r`.  This file proves that away from the axis and away from the equatorial plane the
no-swirl velocity field `Work.Cyl.psiField ψ` generated by it vanishes identically:

* `u_r = ∂_z ψ = 0`, because the profile is locally constant in `z` at every `z ≠ 0`
  (the `z`-slice of `ψ` is constantly `c/r` on a neighbourhood of a point `z > 0` and
  constantly `-(c/r)` on a neighbourhood of a point `z < 0`);
* `u_z = -ψ/r - ∂_rψ = ∓c/r² ± c/r² = 0`, because `∂_rψ = -(ψ/r)` for `r ≠ 0`
  (both are `∓ c/r²`).

So the jump of the profile across the equatorial plane is invisible to `psiField`; this is
the formal content of the "gauge/jump" bookkeeping in the StreamBdry layer.
-/

noncomputable section

open scoped Topology Filter

namespace Work.FTS_StreamBdry.SB0

set_option autoImplicit false

/-- `deriv (fun r' => c / r') r = -((c/r)/r)` for `r ≠ 0`. -/
private lemma hasDerivAt_const_div (c : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun r' : ℝ => c / r') (-((c / r) / r)) r := by
  have h : HasDerivAt (fun r' : ℝ => c / r') (c * (-(r ^ 2)⁻¹)) r := by
    simpa only [div_eq_mul_inv] using (hasDerivAt_inv hr).const_mul c
  have h2 : c * (-(r ^ 2)⁻¹) = -((c / r) / r) := by field_simp
  rwa [← h2]

/-- The `z`-slice of the jump profile `z' ↦ (if 0 < z' then c/r else -(c/r))` is locally
constant at every `z ≠ 0`, hence has vanishing derivative there. -/
private lemma pdZ_jump (c r : ℝ) {z : ℝ} (hz : z ≠ 0) :
    deriv (fun z' => (if 0 < z' then c / r else -(c / r))) z = 0 := by
  have h : (fun z' : ℝ => (if 0 < z' then c / r else -(c / r)))
      =ᶠ[nhds z] (fun _ => (if 0 < z then c / r else -(c / r))) := by
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · filter_upwards [isOpen_Iio.eventually_mem hlt] with z' hz'
      rw [ite_eq_right (not_lt.mpr hz'.le), ite_eq_right (not_lt.mpr hlt.le)]
    · filter_upwards [isOpen_Ioi.eventually_mem hgt] with z' hz'
      have hz'' : (0 : ℝ) < z' := hz'
      rw [ite_eq_left hz'', ite_eq_left hgt]
  rw [Filter.EventuallyEq.deriv_eq h]
  simp

/-- The jump profile satisfies the stream-function identity `∂_rψ + ψ/r = 0` at every
`r ≠ 0` (both sides equal `∓c/r²`, the sign being that of `z`). -/
private lemma pdR_jump (c : ℝ) {r z : ℝ} (hr : r ≠ 0) :
    -((if 0 < z then c / r else -(c / r)) / r)
      - deriv (fun r' => (if 0 < z then c / r' else -(c / r'))) r = 0 := by
  by_cases hz : 0 < z
  · have h : (fun r' : ℝ => (if 0 < z then c / r' else -(c / r')))
        = (fun r' : ℝ => c / r') := by
      funext r'; rw [ite_eq_left hz]
    rw [h, (hasDerivAt_const_div c hr).deriv, ite_eq_left hz]
    ring
  · have h : (fun r' : ℝ => (if 0 < z then c / r' else -(c / r')))
        = (fun r' : ℝ => -(c / r')) := by
      funext r'; rw [ite_eq_right hz]
    have h2 : HasDerivAt (fun r' : ℝ => -(c / r')) (-(-((c / r) / r))) r :=
      (hasDerivAt_const_div c hr).neg
    rw [h, h2.deriv, ite_eq_right hz]
    ring

/-- The jump profile `ψ(r,z) = c/r` (`z > 0`), `-(c/r)` (`z ≤ 0`) generates the zero
no-swirl field away from the axis and the equatorial plane. -/
theorem sb0_psiFieldJump (c : ℝ) {x : Work.Cyl.R3}
    (hr : 0 < Work.Cyl.radial x) (hz : Work.Cyl.axial x ≠ 0) :
    Work.Cyl.psiField (fun r z => if 0 < z then c / r else -(c / r)) x = 0 := by
  have hr' : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  have hpdZ : Work.Cyl.pdZ (fun r z => if 0 < z then c / r else -(c / r))
      (Work.Cyl.radial x) (Work.Cyl.axial x) = 0 := pdZ_jump c _ hz
  have hpdR : -((if 0 < Work.Cyl.axial x then c / Work.Cyl.radial x
              else -(c / Work.Cyl.radial x)) / Work.Cyl.radial x)
      - Work.Cyl.pdR (fun r z => if 0 < z then c / r else -(c / r))
          (Work.Cyl.radial x) (Work.Cyl.axial x) = 0 :=
    pdR_jump c hr'
  show (Work.Cyl.pdZ (fun r z => if 0 < z then c / r else -(c / r))
          (Work.Cyl.radial x) (Work.Cyl.axial x) / Work.Cyl.radial x) • Work.Cyl.radialVec x
      + (-((if 0 < Work.Cyl.axial x then c / Work.Cyl.radial x
              else -(c / Work.Cyl.radial x)) / Work.Cyl.radial x)
          - Work.Cyl.pdR (fun r z => if 0 < z then c / r else -(c / r))
              (Work.Cyl.radial x) (Work.Cyl.axial x)) • Work.Cyl.eZ = 0
  rw [hpdZ, hpdR]
  simp

end Work.FTS_StreamBdry.SB0
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB1.Engine =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB1.Engine` — the SB1′ structural argument

`sb1_gauge` (SB1′) says that on the open quadrant `Qd` every `C³` stream function whose `U`-slot is
bounded (`SlotBd`) differs from the particular solution `psiP` by a multiple of the gauge mode
`gaugeMode αG = z^{-3/αG}/cos θ`.

The argument, with `k = 3/αG`, `W := Ψ - psiP`:

1. the level-0 ODE `αG·D_zΨ + 3Ψ = -s2·U'(Ψ)` holds for `Ψ` **by definition** (`ode_of_Uprime`) and
   for `psiP` by `psiP_ode`; hence `αG·D_zW + 3W = 0`, so `z ↦ z^k W(z,θ)` is constant
   (`rpow_mul_const_of_hom`, `W_eq`);
2. differentiating that constancy in `θ` gives, for every `z ∈ (0,1)`,
   `z^k·V(W)(z,θ) = (1/2)^k·V(W)(1/2,θ)`; the left side is bounded by `z^k(M + C(θ))`
   (`SlotBd` for `V Ψ`, `VopPsiPBnd` for `V (psiP)`) while the right side is independent of `z`,
   so it vanishes and `V(W)(z,θ) = c'(θ) - tan θ·c(θ)` gives the `θ`-ODE `c' = tan θ·c`;
3. `θ ↦ c(θ)·cos θ` therefore has zero derivative on `(0,π/2)`, hence `c = κ/cos θ`, and
   `W = z^{-k}c(θ) = κ·gaugeMode`.

Everything is conditional on the three engine lemmas `PsiPOde`, `PsiPDiff`, `VopPsiPBnd`
(proved in `SB1/psiP_ode`, `SB1/psiP_diff`, `SB1/psiP_Vop_bnd`).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB1

open Work.FTS.StreamBdryIface (Uprime SlotBd gaugeMode psiP)
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## §0 Elementary facts -/

lemma isOpen_Qd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo

lemma nhds_Qd {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    Work.Construction.Qd ∈ 𝓝 (z, θ) := isOpen_Qd.mem_nhds h

lemma Qd_nonempty : ((1 : ℝ), π / 4) ∈ Work.Construction.Qd :=
  mem_Qd.mpr ⟨by norm_num, by norm_num [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- The `z`-slices of a `C³` function are differentiable. -/
lemma diffAt_z_slice {Ψ : Fn} {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    DifferentiableAt ℝ (fun z' => Ψ z' θ) z := by
  have hc : ContDiffAt ℝ 3 (Function.uncurry Ψ) (z, θ) := h3.contDiffAt (nhds_Qd h)
  have hd : DifferentiableAt ℝ (Function.uncurry Ψ) (z, θ) :=
    hc.differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (fun z' : ℝ => (z', θ)) z := by fun_prop
  simpa [Function.comp_def] using hd.comp z hg

/-- The `θ`-slices of a `C³` function are differentiable. -/
lemma diffAt_th_slice {Ψ : Fn} {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    DifferentiableAt ℝ (fun θ' => Ψ z θ') θ := by
  have hc : ContDiffAt ℝ 3 (Function.uncurry Ψ) (z, θ) := h3.contDiffAt (nhds_Qd h)
  have hd : DifferentiableAt ℝ (Function.uncurry Ψ) (z, θ) :=
    hc.differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  simpa [Function.comp_def] using hd.comp θ hg

/-- The `z`-slices of `psiP` are differentiable (engine hypothesis `PsiPDiff`). -/
lemma diffAt_z_psiP {αG M : ℝ} {Ψ : Fn} (hpdiff : PsiPDiff αG M Ψ) {z θ : ℝ}
    (h : (z, θ) ∈ Work.Construction.Qd) :
    DifferentiableAt ℝ (fun z' => psiP αG Ψ z' θ) z := (hpdiff z θ h).1

/-- The `θ`-slices of `psiP` are differentiable (engine hypothesis `PsiPDiff`). -/
lemma diffAt_th_psiP {αG M : ℝ} {Ψ : Fn} (hpdiff : PsiPDiff αG M Ψ) {z θ : ℝ}
    (h : (z, θ) ∈ Work.Construction.Qd) :
    DifferentiableAt ℝ (fun θ' => psiP αG Ψ z θ') θ := (hpdiff z θ h).2

/-- `pz` of the difference `Ψ - psiP`, pointwise. -/
lemma pz_sub_psiP {αG M : ℝ} {Ψ : Fn} {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hpdiff : PsiPDiff αG M Ψ) :
    Work.Spaces.pz (fun z' θ' => Ψ z' θ' - psiP αG Ψ z' θ') z θ
      = Work.Spaces.pz Ψ z θ - Work.Spaces.pz (psiP αG Ψ) z θ := by
  simp only [Work.Spaces.pz]
  rw [show (fun z' => Ψ z' θ - psiP αG Ψ z' θ)
      = ((fun z' => Ψ z' θ) - (fun z' => psiP αG Ψ z' θ)) from rfl,
    deriv_sub (diffAt_z_slice h h3) (diffAt_z_psiP hpdiff h)]

/-- `pth` of the difference `Ψ - psiP`, pointwise. -/
lemma pth_sub_psiP {αG M : ℝ} {Ψ : Fn} {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hpdiff : PsiPDiff αG M Ψ) :
    Work.Spaces.pth (fun z' θ' => Ψ z' θ' - psiP αG Ψ z' θ') z θ
      = Work.Spaces.pth Ψ z θ - Work.Spaces.pth (psiP αG Ψ) z θ := by
  simp only [Work.Spaces.pth]
  rw [show (fun θ' => Ψ z θ' - psiP αG Ψ z θ')
      = ((fun θ' => Ψ z θ') - (fun θ' => psiP αG Ψ z θ')) from rfl,
    deriv_sub (diffAt_th_slice h h3) (diffAt_th_psiP hpdiff h)]

/-- `V` of the difference is the difference of the `V`'s (definitional apart from `pth_sub`). -/
lemma Vop_sub_psiP {αG M : ℝ} {Ψ : Fn} {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hpdiff : PsiPDiff αG M Ψ) :
    Work.Construction.Vop (fun z' θ' => Ψ z' θ' - psiP αG Ψ z' θ') z θ
      = Work.Construction.Vop Ψ z θ - Work.Construction.Vop (psiP αG Ψ) z θ := by
  rw [Work.Construction.Vop, Work.Construction.Vop, Work.Construction.Vop,
    pth_sub_psiP h h3 hpdiff]
  ring

/-! ## §1 The homogeneous ODE and the constancy in `z` -/

lemma rpow_mul_const_le {αG : ℝ} (hαG : 0 < αG) {f : ℝ → ℝ}
    (hf : ∀ z ∈ Ioi (0 : ℝ), DifferentiableAt ℝ f z)
    (hode : ∀ z ∈ Ioi (0 : ℝ), αG * z * deriv f z + 3 * f z = 0)
    {z₁ z₂ : ℝ} (h1 : 0 < z₁) (h2 : 0 < z₂) (hle : z₁ ≤ z₂) :
    z₁ ^ (3 / αG) * f z₁ = z₂ ^ (3 / αG) * f z₂ := by
  have hαG' : αG ≠ 0 := ne_of_gt hαG
  have hderiv : ∀ z ∈ uIcc z₁ z₂, HasDerivAt (fun z => z ^ (3 / αG) * f z) 0 z := by
    intro z hz
    rw [Set.uIcc_of_le hle] at hz
    have hzpos : 0 < z := lt_of_lt_of_le h1 hz.1
    have hzI : z ∈ Ioi (0 : ℝ) := hzpos
    have h1d : HasDerivAt (fun z : ℝ => z ^ (3 / αG))
        ((3 / αG) * z ^ (3 / αG - 1)) z :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hzpos))
    have h2d : HasDerivAt f (deriv f z) z := (hf z hzI).hasDerivAt
    refine (h1d.mul h2d).congr_deriv ?_
    have hp : z ^ (3 / αG) = z ^ (3 / αG - 1) * z := by
      rw [← Real.rpow_add_one (ne_of_gt hzpos)]
      norm_num
    have hbr : (3 / αG) * f z + z * deriv f z = 0 := by
      have h0 := hode z hzI
      have hz' : z * deriv f z = -(3 * f z) / αG := by
        rw [eq_div_iff hαG']
        linarith
      rw [hz']
      field_simp
      ring
    rw [hp]
    have hcl : (3 / αG) * z ^ (3 / αG - 1) * f z + z ^ (3 / αG - 1) * z * deriv f z
        = z ^ (3 / αG - 1) * ((3 / αG) * f z + z * deriv f z) := by ring
    rw [hcl, hbr, mul_zero]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume z₁ z₂)
  simp only [intervalIntegral.integral_zero] at hftc
  linarith

/-- The homogeneous ODE `αG·D_z f + 3f = 0` makes `z ↦ z^{3/αG} f z` constant. -/
lemma rpow_mul_const_of_hom {αG : ℝ} (hαG : 0 < αG) {f : ℝ → ℝ}
    (hf : ∀ z ∈ Ioi (0 : ℝ), DifferentiableAt ℝ f z)
    (hode : ∀ z ∈ Ioi (0 : ℝ), αG * z * deriv f z + 3 * f z = 0)
    {z₁ z₂ : ℝ} (h1 : 0 < z₁) (h2 : 0 < z₂) :
    z₁ ^ (3 / αG) * f z₁ = z₂ ^ (3 / αG) * f z₂ := by
  rcases le_total z₁ z₂ with hle | hle
  · exact rpow_mul_const_le hαG hf hode h1 h2 hle
  · exact (rpow_mul_const_le hαG hf hode h2 h1 hle).symm

/-- The homogeneous ODE for `W = Ψ - psiP` (difference of the two level-0 ODEs). -/
lemma W_hom {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn} {z θ : ℝ}
    (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hode : PsiPOde αG M Ψ) (hpdiff : PsiPDiff αG M Ψ) :
    αG * z * deriv (fun z' => Ψ z' θ - psiP αG Ψ z' θ) z
      + 3 * (Ψ z θ - psiP αG Ψ z θ) = 0 := by
  have hpz := pz_sub_psiP (αG := αG) h h3 hpdiff
  have hA := ode_of_Uprime (αG := αG) Ψ h
  have hB := hode z θ h
  simp only [Work.Spaces.pz] at hpz hA hB
  rw [hpz]
  linarith

/-- The constant in `z`: `c(θ) = (1/2)^{3/αG}·W(1/2,θ)`. -/
def cfun (αG : ℝ) (Ψ : Fn) (θ : ℝ) : ℝ :=
  (1 / 2 : ℝ) ^ (3 / αG) * (Ψ (1 / 2) θ - psiP αG Ψ (1 / 2) θ)

lemma half_mem_Qd {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) :
    ((1 / 2 : ℝ), θ) ∈ Work.Construction.Qd :=
  mem_Qd.mpr ⟨by norm_num, hθ.1, hθ.2⟩

/-- **Constancy in `z`**: `Ψ - psiP = z^{-3/αG}·c(θ)`. -/
lemma W_eq {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn} {z θ : ℝ}
    (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hode : PsiPOde αG M Ψ) (hpdiff : PsiPDiff αG M Ψ) :
    Ψ z θ - psiP αG Ψ z θ = z ^ (-(3 / αG)) * cfun αG Ψ θ := by
  have hθ : θ ∈ Ioo (0 : ℝ) (π / 2) := Qd_theta_mem h
  have hz : 0 < z := Qd_pos h
  have hf : ∀ z' ∈ Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => Ψ z' θ - psiP αG Ψ z' θ) z' := by
    intro z' hz'
    exact (diffAt_z_slice (mem_Qd.mpr ⟨hz', hθ.1, hθ.2⟩) h3).sub
      (diffAt_z_psiP hpdiff (mem_Qd.mpr ⟨hz', hθ.1, hθ.2⟩))
  have hode' : ∀ z' ∈ Ioi (0 : ℝ),
      αG * z' * deriv (fun z'' => Ψ z'' θ - psiP αG Ψ z'' θ) z'
        + 3 * (Ψ z' θ - psiP αG Ψ z' θ) = 0 :=
    fun z' hz' => W_hom hαG (mem_Qd.mpr ⟨hz', hθ.1, hθ.2⟩) h3 hode hpdiff
  have hc := rpow_mul_const_of_hom hαG hf hode' hz (by norm_num : (0 : ℝ) < 1 / 2)
  have hzk : z ^ (3 / αG) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hz _)
  have hW : Ψ z θ - psiP αG Ψ z θ = cfun αG Ψ θ / z ^ (3 / αG) := by
    rw [eq_div_iff hzk, mul_comm (Ψ z θ - psiP αG Ψ z θ)]
    simpa only [cfun] using hc
  rw [hW, Real.rpow_neg (le_of_lt hz), div_eq_mul_inv, mul_comm]

/-- The constancy, in the `z^k·W` form. -/
lemma rpow_mul_W_eq {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn} {z θ : ℝ}
    (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hode : PsiPOde αG M Ψ) (hpdiff : PsiPDiff αG M Ψ) :
    z ^ (3 / αG) * (Ψ z θ - psiP αG Ψ z θ) = cfun αG Ψ θ := by
  have hθ : θ ∈ Ioo (0 : ℝ) (π / 2) := Qd_theta_mem h
  have hz : 0 < z := Qd_pos h
  have h1 := W_eq (αG := αG) (M := M) hαG h h3 hode hpdiff
  rw [h1]
  have hz' : z ^ (-(3 / αG)) * z ^ (3 / αG) = 1 := by
    rw [← Real.rpow_add hz]
    norm_num
  rw [← mul_assoc, mul_comm (z ^ (3 / αG)) (z ^ (-(3 / αG))), hz', one_mul]

/-! ## §2 The `θ`-ODE for the constant -/

/-- `cfun` is differentiable in `θ`. -/
lemma differentiableAt_cfun {αG M : ℝ} {Ψ : Fn} {θ : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hpdiff : PsiPDiff αG M Ψ) : DifferentiableAt ℝ (cfun αG Ψ) θ := by
  have hmem := half_mem_Qd hθ
  have hd := (diffAt_th_slice hmem h3).sub (diffAt_th_psiP hpdiff hmem)
  have hc : DifferentiableAt ℝ
      (fun θ' => (1 / 2 : ℝ) ^ (3 / αG) * (Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ')) θ :=
    hd.const_mul _
  exact hc

/-- `|L| ≤ z^k·D` for all `z ∈ (0,1)` with `D ≥ 0`, `k > 0` forces `L = 0`. -/
lemma eq_zero_of_abs_le_rpow_mul {k L D : ℝ} (hk : 0 < k) (hD : 0 ≤ D)
    (h : ∀ z ∈ Ioo (0 : ℝ) 1, |L| ≤ z ^ k * D) : L = 0 := by
  have hmemI : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    rw [show 𝓝[>] (0 : ℝ) = 𝓝 (0 : ℝ) ⊓ 𝓟 (Ioi 0) from rfl, mem_inf_principal]
    refine Filter.mem_of_superset (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)) ?_
    intro x hx
    simp only [mem_setOf_eq, mem_Iio] at hx ⊢
    intro h0
    exact ⟨h0, by linarith⟩
  have htend : Tendsto (fun z : ℝ => z ^ k * D) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun z : ℝ => z ^ k) 0 :=
      Real.continuousAt_rpow_const 0 k (Or.inr (le_of_lt hk))
    have h0 : (0 : ℝ) ^ k = 0 := Real.zero_rpow (ne_of_gt hk)
    have h1 : Tendsto (fun z : ℝ => z ^ k) (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) ^ k)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    rw [h0] at h1
    simpa using h1.mul_const D
  have hev : ∀ᶠ z in 𝓝[>] (0 : ℝ), |L| ≤ z ^ k * D :=
    Filter.mem_of_superset hmemI fun z hz => h z hz
  have hle : |L| ≤ 0 := ge_of_tendsto htend hev
  exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))

/-- The heart of SB1′: `z^k·V(W)` is independent of `z`.  Proved by differentiating the constancy
of `W` in `θ`: both `W z` and `W (1/2)` are `z^{-k}c(θ)` resp. `(1/2)^{-k}c(θ)`. -/
lemma VopW_rpow_const {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn} {z θ : ℝ}
    (hz1 : z < 1) (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hode : PsiPOde αG M Ψ) (hpdiff : PsiPDiff αG M Ψ) :
    z ^ (3 / αG) * (Work.Construction.Vop Ψ z θ - Work.Construction.Vop (psiP αG Ψ) z θ)
      = (1 / 2 : ℝ) ^ (3 / αG)
        * (Work.Construction.Vop Ψ (1 / 2) θ
            - Work.Construction.Vop (psiP αG Ψ) (1 / 2) θ) := by
  have hθ : θ ∈ Ioo (0 : ℝ) (π / 2) := Qd_theta_mem h
  have hz : 0 < z := Qd_pos h
  have hzhalf : ((1 / 2 : ℝ), θ) ∈ Work.Construction.Qd := half_mem_Qd hθ
  have hI : Ioo (0 : ℝ) (π / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hdc := differentiableAt_cfun (αG := αG) (M := M) hθ h3 hpdiff
  have hWz_ev : (fun θ' => Ψ z θ' - psiP αG Ψ z θ') =ᶠ[𝓝 θ]
      (fun θ' => z ^ (-(3 / αG)) * cfun αG Ψ θ') := by
    filter_upwards [hI] with θ' hθ'
    exact W_eq (αG := αG) (M := M) hαG (mem_Qd.mpr ⟨hz, hθ'.1, hθ'.2⟩) h3 hode hpdiff
  have hWh_ev : (fun θ' => Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ') =ᶠ[𝓝 θ]
      (fun θ' => (1 / 2 : ℝ) ^ (-(3 / αG)) * cfun αG Ψ θ') := by
    filter_upwards [hI] with θ' hθ'
    exact W_eq (αG := αG) (M := M) hαG (half_mem_Qd hθ') h3 hode hpdiff
  have hdz : deriv (fun θ' => Ψ z θ' - psiP αG Ψ z θ') θ
      = z ^ (-(3 / αG)) * deriv (cfun αG Ψ) θ := by
    rw [hWz_ev.deriv_eq]
    exact deriv_const_mul _ hdc
  have hdh : deriv (fun θ' => Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ') θ
      = (1 / 2 : ℝ) ^ (-(3 / αG)) * deriv (cfun αG Ψ) θ := by
    rw [hWh_ev.deriv_eq]
    exact deriv_const_mul _ hdc
  have hzz : z ^ (-(3 / αG)) * z ^ (3 / αG) = 1 := by
    rw [← Real.rpow_add hz]
    norm_num
  have hhh : (1 / 2 : ℝ) ^ (-(3 / αG)) * (1 / 2 : ℝ) ^ (3 / αG) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
    norm_num
  have hkey1 : z ^ (3 / αG) * deriv (fun θ' => Ψ z θ' - psiP αG Ψ z θ') θ
      = (1 / 2 : ℝ) ^ (3 / αG)
        * deriv (fun θ' => Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ') θ := by
    rw [hdz, hdh, ← mul_assoc, mul_comm (z ^ (3 / αG)) (z ^ (-(3 / αG))), hzz, one_mul,
      ← mul_assoc, mul_comm ((1 / 2 : ℝ) ^ (3 / αG)) ((1 / 2 : ℝ) ^ (-(3 / αG))), hhh, one_mul]
  have hkey2 : z ^ (3 / αG) * (Ψ z θ - psiP αG Ψ z θ)
      = (1 / 2 : ℝ) ^ (3 / αG) * (Ψ (1 / 2) θ - psiP αG Ψ (1 / 2) θ) := by
    rw [rpow_mul_W_eq (αG := αG) (M := M) hαG h h3 hode hpdiff,
      rpow_mul_W_eq (αG := αG) (M := M) hαG hzhalf h3 hode hpdiff]
  have hL : Work.Construction.Vop Ψ z θ - Work.Construction.Vop (psiP αG Ψ) z θ
      = deriv (fun θ' => Ψ z θ' - psiP αG Ψ z θ') θ
        - Real.tan θ * (Ψ z θ - psiP αG Ψ z θ) := by
    have hd := pth_sub_psiP (αG := αG) h h3 hpdiff
    simp only [Work.Spaces.pth] at hd
    rw [Work.Construction.Vop, Work.Construction.Vop, Work.Spaces.pth, Work.Spaces.pth]
    rw [hd]
    ring
  have hR : Work.Construction.Vop Ψ (1 / 2) θ - Work.Construction.Vop (psiP αG Ψ) (1 / 2) θ
      = deriv (fun θ' => Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ') θ
        - Real.tan θ * (Ψ (1 / 2) θ - psiP αG Ψ (1 / 2) θ) := by
    have hd := pth_sub_psiP (αG := αG) hzhalf h3 hpdiff
    simp only [Work.Spaces.pth] at hd
    rw [Work.Construction.Vop, Work.Construction.Vop, Work.Spaces.pth, Work.Spaces.pth]
    rw [hd]
    ring
  rw [hL, hR]
  rw [show z ^ (3 / αG) * (deriv (fun θ' => Ψ z θ' - psiP αG Ψ z θ') θ
        - Real.tan θ * (Ψ z θ - psiP αG Ψ z θ))
      = z ^ (3 / αG) * deriv (fun θ' => Ψ z θ' - psiP αG Ψ z θ') θ
        - Real.tan θ * (z ^ (3 / αG) * (Ψ z θ - psiP αG Ψ z θ)) from by ring]
  rw [show (1 / 2 : ℝ) ^ (3 / αG) * (deriv (fun θ' => Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ') θ
        - Real.tan θ * (Ψ (1 / 2) θ - psiP αG Ψ (1 / 2) θ))
      = (1 / 2 : ℝ) ^ (3 / αG) * deriv (fun θ' => Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ') θ
        - Real.tan θ * ((1 / 2 : ℝ) ^ (3 / αG)
            * (Ψ (1 / 2) θ - psiP αG Ψ (1 / 2) θ)) from by ring]
  rw [hkey1, hkey2]

/-- `V(W)` vanishes on the half-line `θ = 1/2`: the constant of integration is not a general
function of `θ` but `κ/cos θ`. -/
lemma VopW_half_eq_zero {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn} {θ : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) (hode : PsiPOde αG M Ψ) (hpdiff : PsiPDiff αG M Ψ)
    (hbnd : VopPsiPBnd αG M Ψ) :
    (1 / 2 : ℝ) ^ (3 / αG)
      * (Work.Construction.Vop Ψ (1 / 2) θ - Work.Construction.Vop (psiP αG Ψ) (1 / 2) θ)
      = 0 := by
  obtain ⟨C, hC⟩ := hbnd θ hθ
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC (1 / 2) ⟨by norm_num, by norm_num⟩)
  have hM0 : 0 ≤ M :=
    le_trans (abs_nonneg _)
      (SlotBd.V_le hslot (z := 1) (θ := π / 4) Qd_nonempty (j := 0) (by norm_num))
  have hbdd : ∀ z ∈ Ioo (0 : ℝ) 1,
      |(1 / 2 : ℝ) ^ (3 / αG)
        * (Work.Construction.Vop Ψ (1 / 2) θ
            - Work.Construction.Vop (psiP αG Ψ) (1 / 2) θ)| ≤ z ^ (3 / αG) * (M + C) := by
    intro z hz
    have hmem : (z, θ) ∈ Work.Construction.Qd := mem_Qd.mpr ⟨hz.1, hθ.1, hθ.2⟩
    have h1 := VopW_rpow_const (αG := αG) (M := M) hαG hz.2 hmem h3 hode hpdiff
    have h2 : |Work.Construction.Vop Ψ z θ - Work.Construction.Vop (psiP αG Ψ) z θ|
        ≤ M + C := by
      refine (abs_sub _ _).trans ?_
      exact add_le_add (SlotBd.V_le hslot hmem (j := 0) (by norm_num)) (hC z hz)
    calc |(1 / 2 : ℝ) ^ (3 / αG)
          * (Work.Construction.Vop Ψ (1 / 2) θ
              - Work.Construction.Vop (psiP αG Ψ) (1 / 2) θ)|
        = |z ^ (3 / αG)
            * (Work.Construction.Vop Ψ z θ - Work.Construction.Vop (psiP αG Ψ) z θ)| := by
          rw [← h1]
      _ = z ^ (3 / αG)
            * |Work.Construction.Vop Ψ z θ - Work.Construction.Vop (psiP αG Ψ) z θ| := by
          rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz.1 _)]
      _ ≤ z ^ (3 / αG) * (M + C) :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt (Real.rpow_pos_of_pos hz.1 _))
  exact eq_zero_of_abs_le_rpow_mul (by positivity) (add_nonneg hM0 hC0) hbdd

/-- The `θ`-ODE for the constant of integration: `c'(θ) = tan θ·c(θ)`. -/
lemma deriv_cfun {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn} {θ : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) (hode : PsiPOde αG M Ψ) (hpdiff : PsiPDiff αG M Ψ)
    (hbnd : VopPsiPBnd αG M Ψ) :
    deriv (cfun αG Ψ) θ = Real.tan θ * cfun αG Ψ θ := by
  have hmem : ((1 / 2 : ℝ), θ) ∈ Work.Construction.Qd := half_mem_Qd hθ
  have hV := VopW_half_eq_zero (αG := αG) (M := M) hαG hθ h3 hslot hode hpdiff hbnd
  have h1 : deriv (cfun αG Ψ) θ
      = (1 / 2 : ℝ) ^ (3 / αG)
        * deriv (fun θ' => Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ') θ := by
    rw [show cfun αG Ψ
        = (fun θ' => (1 / 2 : ℝ) ^ (3 / αG)
            * (Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ')) from rfl]
    exact deriv_const_mul _
      ((diffAt_th_slice hmem h3).sub (diffAt_th_psiP hpdiff hmem))
  have h2 : deriv (fun θ' => Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ') θ
      = (Work.Construction.Vop Ψ (1 / 2) θ
          - Work.Construction.Vop (psiP αG Ψ) (1 / 2) θ)
        + Real.tan θ * (Ψ (1 / 2) θ - psiP αG Ψ (1 / 2) θ) := by
    have hd := pth_sub_psiP (αG := αG) hmem h3 hpdiff
    simp only [Work.Spaces.pth] at hd
    rw [hd, Work.Construction.Vop, Work.Construction.Vop, Work.Spaces.pth, Work.Spaces.pth]
    ring
  rw [h1, h2, mul_add, hV, zero_add]
  rw [show (1 / 2 : ℝ) ^ (3 / αG) * (Real.tan θ * (Ψ (1 / 2) θ - psiP αG Ψ (1 / 2) θ))
      = Real.tan θ
        * ((1 / 2 : ℝ) ^ (3 / αG) * (Ψ (1 / 2) θ - psiP αG Ψ (1 / 2) θ)) from by ring]
  rfl

/-- **The constant is `κ/cos θ`**: `c(θ)·cos θ` is constant on `(0,π/2)`. -/
lemma cos_mul_cfun_const {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn} {θ : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) (hode : PsiPOde αG M Ψ) (hpdiff : PsiPDiff αG M Ψ)
    (hbnd : VopPsiPBnd αG M Ψ) :
    cfun αG Ψ θ * Real.cos θ = cfun αG Ψ (π / 4) * Real.cos (π / 4) := by
  have hπ4 : π / 4 ∈ Ioo (0 : ℝ) (π / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  set d : ℝ → ℝ := fun t => cfun αG Ψ t * Real.cos t with hd
  have hderiv : ∀ t ∈ uIcc θ (π / 4), HasDerivAt d 0 t := by
    intro t ht
    rcases Set.mem_uIcc.mp ht with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have ht' : t ∈ Ioo (0 : ℝ) (π / 2) :=
        ⟨lt_of_lt_of_le hθ.1 ha, lt_of_le_of_lt hb hπ4.2⟩
      have hdiff := differentiableAt_cfun (αG := αG) (M := M) ht' h3 hpdiff
      have hcos : HasDerivAt Real.cos (-Real.sin t) t := Real.hasDerivAt_cos t
      have hprod : HasDerivAt (fun t => cfun αG Ψ t * Real.cos t) 0 t := by
        refine (hdiff.hasDerivAt.mul hcos).congr_deriv ?_
        rw [deriv_cfun (αG := αG) (M := M) hαG ht' h3 hslot hode hpdiff hbnd,
          Real.tan_eq_sin_div_cos]
        have hct : Real.cos t ≠ 0 := ne_of_gt (cos_pos_of_Ioo ht')
        field_simp
        ring
      exact hprod
    · have ht' : t ∈ Ioo (0 : ℝ) (π / 2) :=
        ⟨lt_of_lt_of_le hπ4.1 ha, lt_of_le_of_lt hb hθ.2⟩
      have hdiff := differentiableAt_cfun (αG := αG) (M := M) ht' h3 hpdiff
      have hcos : HasDerivAt Real.cos (-Real.sin t) t := Real.hasDerivAt_cos t
      have hprod : HasDerivAt (fun t => cfun αG Ψ t * Real.cos t) 0 t := by
        refine (hdiff.hasDerivAt.mul hcos).congr_deriv ?_
        rw [deriv_cfun (αG := αG) (M := M) hαG ht' h3 hslot hode hpdiff hbnd,
          Real.tan_eq_sin_div_cos]
        have hct : Real.cos t ≠ 0 := ne_of_gt (cos_pos_of_Ioo ht')
        field_simp
        ring
      exact hprod
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume θ (π / 4))
  simp only [intervalIntegral.integral_zero] at hftc
  linarith

/-! ## §3 SB1′ -/

/-- **SB1′ from the three engine lemmas.** -/
theorem sb1_gauge_of_parts {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M)
    (hode : PsiPOde αG M Ψ) (hpdiff : PsiPDiff αG M Ψ) (hbnd : VopPsiPBnd αG M Ψ) :
    ∃ κ : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Ψ z θ = psiP αG Ψ z θ + κ * gaugeMode αG z θ := by
  refine ⟨cfun αG Ψ (π / 4) * Real.cos (π / 4), ?_⟩
  intro z θ h
  have hθ : θ ∈ Ioo (0 : ℝ) (π / 2) := Qd_theta_mem h
  have hW := W_eq (αG := αG) (M := M) hαG h h3 hode hpdiff
  have hc := cos_mul_cfun_const (αG := αG) (M := M) hαG hθ h3 hslot hode hpdiff hbnd
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (cos_pos_of_Qd h)
  have hcf : cfun αG Ψ θ = (cfun αG Ψ (π / 4) * Real.cos (π / 4)) / Real.cos θ := by
    rw [eq_div_iff hcos]
    linarith [hc]
  have hΨ : Ψ z θ = psiP αG Ψ z θ + z ^ (-(3 / αG)) * cfun αG Ψ θ := by linarith [hW]
  rw [hΨ, hcf, gaugeMode]
  ring

end Work.FTS_StreamBdry.SB1
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB1.contDiffOn_uncurry_Uprime =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB1.contDiffOn_uncurry_Uprime`

`U'(Ψ) = Uop αG Ψ / s2` with `Uop αG Ψ = -3Ψ - αG z ∂_zΨ` and `s2 θ = sin 2θ` is `C¹`
on the open quadrant `Qd = (0,∞) × (0,π/2)` as soon as `Ψ` is `C³` there.

Route: `Ψ` is `C¹` on `Qd` (`h3.of_le`), and `∂_zΨ` is `C¹` on `Qd` by
`Work.Spaces.uncurry_partial_c1` (the curried `z`-partial of a `C²` function on an open
set), so the numerator `-3Ψ - αG z ∂_zΨ` is `C¹`; the denominator `sin 2θ` is `C^∞` and
non-zero on `Qd` (`0 < 2θ < π`), so `ContDiffOn.div` applies.  The division is exactly the
definition of `Uprime`, so the last step is `rfl` after unfolding.
-/

namespace Work.FTS_StreamBdry.SB1

open Set

theorem contDiffOn_uncurry_Uprime {αG : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.FTS.StreamBdryIface.Uprime αG Ψ))
      Work.Construction.Qd := by
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have h2 : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd :=
    h3.of_le (by norm_num)
  have hpz : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz Ψ)) Work.Construction.Qd :=
    (Work.Spaces.uncurry_partial_c1 hQd h2).1
  have hnum : ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
      -3 * Function.uncurry Ψ p - αG * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p)
      Work.Construction.Qd := by
    refine (contDiffOn_const.mul (h2.of_le (m := 1) (by norm_num))).sub ?_
    exact (contDiffOn_const.mul (contDiff_fst.contDiffOn)).mul hpz
  have hden : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.Construction.Qd :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hne : ∀ p ∈ Work.Construction.Qd, Real.sin (2 * p.2) ≠ 0 := by
    intro p hp
    have hθ1 : 0 < p.2 := hp.2.1
    have hθ2 : p.2 < Real.pi / 2 := hp.2.2
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith [Real.pi_pos]))
  have hquot := hnum.div hden hne
  refine hquot.congr (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry, Work.FTS.StreamBdryIface.Uprime, Work.Construction.Uop,
    Work.Construction.s2, Work.Spaces.pz, Pi.div_apply]

end Work.FTS_StreamBdry.SB1
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.Defs` — vocabulary and the W0/W1/W2/W3 leaf interface for SB2/SB5

Transcription of the lead's per-leaf plan `sources/ftsV2/fts_sb25_leafplans.{md,lean}`
(curric-46, 2026-10-10) into the `FTS_StreamBdry` subproject.  The mathematical content is
*identical*; the statements are re-packaged as `Prop`-valued definitions (`<Leaf> ... : Prop`)
so that a delegated lemma can be stated with no notation beyond a fully qualified name, and so
that the leaf interface is documented in one place.

Vocabulary added here: `Lgs` (the ground-state-transformed operator, `bslOp α (s2·u) = s2·Lgs α u`)
and `phiB` (the explicit FIX-SB5 barrier, `𝓐 phiB = -15/4` exactly).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP psiHatP SB5Barrier oddPerS)
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## §0 Vocabulary -/

/-- **The ground-state-transformed operator**: `bslOp α (s2·u) = s2 · Lgs α u`.  It has no
zero-order and no mixed term (sympy residual ≡ 0). -/
def Lgs (α : ℝ) (u : Fn) : Fn := fun z θ =>
  -(α ^ 2) * Work.Spaces.DzIter 2 u z θ - 5 * α * Work.Spaces.Dz u z θ
    - Work.Spaces.pthIter 2 u z θ
    - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * Work.Spaces.pth u z θ

/-- **The explicit FIX-SB5 barrier**: `phiB' = -G/m` with `m = 4 sin²θ cos³θ`,
`G = 1 - 5 sin³θ + 3 sin⁵θ`; then `𝓐 phiB = -15/4` exactly, `phiB ≥ 0`, and `phiB → ∞` at both
ends (`phiB ≥ 1/(4 sin θ)` and `phiB ≥ 1/(16(1 - sin θ))`). -/
def phiB (θ : ℝ) : ℝ :=
  1 / (4 * Real.sin θ) + 1 / (16 * (1 - Real.sin θ)) + 3 / (16 * (1 + Real.sin θ))
    - 3 / 16 * Real.log (1 - Real.sin θ) - 9 / 16 * Real.log (1 + Real.sin θ) + 1

/-! ## §1 The leaf statements (W0/W1/W2/W3 of the plan) -/

/-- **C1 `gaugeMode_facts`**: the gauge mode is smooth on `Qd`, is `Vop`-free and is
`bslOp`-harmonic. -/
def GaugeModeFacts (αG : ℝ) : Prop :=
  ContDiffOn ℝ ⊤ (Function.uncurry (gaugeMode αG)) Work.Construction.Qd ∧
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.Vop (gaugeMode αG) z θ = 0 ∧
        Work.Elliptic.bslOp αG (gaugeMode αG) z θ = 0


/-- **C3 `law_Dform`**: the elliptic law in `D`-form, `∂_θV(P) = -(α²D²P + 5αDP + 6P) - F`. -/
def LawDform (α : ℝ) (F P : Fn) : Prop :=
  ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → Work.Elliptic.bslOp α P z θ = F z θ) →
      ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        Work.Spaces.pth (Work.Construction.Vop P) z θ
          = -(α ^ 2 * Work.Spaces.DzIter 2 P z θ + 5 * α * Work.Spaces.Dz P z θ
              + 6 * P z θ) - F z θ

/-- **B2 `lip_edge_trace`**: a uniformly `θ`-Lipschitz function on a strip has continuous edge
traces, approached at linear rate. -/
def LipEdgeTrace (f : Fn) (a b K : ℝ) : Prop :=
  a < b → ContinuousOn (Function.uncurry f) (Ioi 0 ×ˢ Ioo a b) →
    (∀ z θ, 0 < z → θ ∈ Ioo a b → DifferentiableAt ℝ (fun θ' => f z θ') θ) →
    (∀ z θ, 0 < z → θ ∈ Ioo a b → |Work.Spaces.pth f z θ| ≤ K) →
      ∃ fa fb : ℝ → ℝ, ContinuousOn fa (Ioi 0) ∧ ContinuousOn fb (Ioi 0) ∧
        ∀ z θ, 0 < z → θ ∈ Ioo a b →
          |f z θ - fa z| ≤ K * (θ - a) ∧ |f z θ - fb z| ≤ K * (b - θ)

/-- **B3 `axis_tan_bound`** (1-D): if `V := f' - tan·f` converges to `v₀` at rate
`A(π/2 - θ)`, then `tan θ·f → -v₀/2` at that rate. -/
def AxisTanBound (f : ℝ → ℝ) (v0 A B : ℝ) : Prop :=
  (∀ θ ∈ Ioo (0 : ℝ) (π / 2), DifferentiableAt ℝ f θ) →
    (∀ θ ∈ Ioo (0 : ℝ) (π / 2), |f θ| ≤ B) →
    (∀ θ ∈ Ioo (0 : ℝ) (π / 2),
      |deriv f θ - Real.tan θ * f θ - v0| ≤ A * (π / 2 - θ)) →
      ∀ θ ∈ Ioo (0 : ℝ) (π / 2),
        |Real.tan θ * f θ + v0 / 2| ≤ |v0| * (π / 2 - θ) ^ 2 + 3 * A * (π / 2 - θ)

/-- **B4 `axis_d2_bound`** (1-D): the axis expansion to second order. -/
def AxisD2Bound (f : ℝ → ℝ) (v0 B ε θ0 : ℝ) : Prop :=
  θ0 ∈ Ioo (0 : ℝ) (π / 2) →
    (∀ θ ∈ Ioo (0 : ℝ) (π / 2),
      DifferentiableAt ℝ f θ ∧ DifferentiableAt ℝ (deriv f) θ) →
    (∀ θ ∈ Ioo (0 : ℝ) (π / 2), |f θ| ≤ B) →
    (∀ t ∈ Ico θ0 (π / 2), |deriv f t - Real.tan t * f t - v0| ≤ ε * (π / 2 - t)) →
    (∀ t ∈ Ico θ0 (π / 2),
      |deriv (fun s => deriv f s - Real.tan s * f s) t| ≤ ε) →
      |deriv (deriv f) θ0| ≤ 6 * ε + |v0| * (π / 2 - θ0)

/-- **B5 `psiP_edge_zero`**: the edge limits of `psiP` at `θ = 0`. -/
def PsiPEdgeZero (αG M L Mf : ℝ) (F Ψ : Fn) : Prop :=
  Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ →
    ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd →
    SlotBd αG Ψ M → SrcOK F L Mf →
    (∃ K' : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1
        (Work.Construction.Vop (psiP αG Ψ))) z θ| ≤ K') →
      ∀ z0 : ℝ, 0 < z0 →
        let P := psiP αG Ψ
        Tendsto (Function.uncurry P) (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) ∧
        Tendsto (Function.uncurry (Work.Spaces.pz P))
          (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) ∧
        Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz P)))
          (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) ∧
        Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth P)))
          (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) ∧
        (∃ l, Tendsto (Function.uncurry (Work.Spaces.pth P))
          (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 l)) ∧
        (∃ l, Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth P)))
            (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 l) ∧
          Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz P)))
            (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 l))

/-- **B6 `psiP_edge_axis`**: the edge limits of `psiP` at `θ = π/2`. -/
def PsiPEdgeAxis (αG M L Mf : ℝ) (F Ψ : Fn) : Prop :=
  Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ →
    ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd →
    SlotBd αG Ψ M → SrcOK F L Mf →
    (∃ K' : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1
        (Work.Construction.Vop (psiP αG Ψ))) z θ| ≤ K') →
      ∀ z0 : ℝ, 0 < z0 →
        let P := psiP αG Ψ
        Tendsto (Function.uncurry P) (𝓝[Work.Construction.Qd] (z0, π / 2)) (𝓝 0) ∧
        Tendsto (Function.uncurry (Work.Spaces.pz P))
          (𝓝[Work.Construction.Qd] (z0, π / 2)) (𝓝 0) ∧
        Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz P)))
          (𝓝[Work.Construction.Qd] (z0, π / 2)) (𝓝 0) ∧
        Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth P)))
          (𝓝[Work.Construction.Qd] (z0, π / 2)) (𝓝 0) ∧
        (∃ l, Tendsto (Function.uncurry (Work.Spaces.pth P))
          (𝓝[Work.Construction.Qd] (z0, π / 2)) (𝓝 l)) ∧
        (∃ l, Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth P)))
            (𝓝[Work.Construction.Qd] (z0, π / 2)) (𝓝 l) ∧
          Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz P)))
            (𝓝[Work.Construction.Qd] (z0, π / 2)) (𝓝 l))

/-- **B7a `glue_line_C1`**: `C¹` gluing across the line `θ = c`. -/
def GlueLineC1 (h : Fn) (c r : ℝ) : Prop :=
  0 < r →
    ContDiffOn ℝ 1 (Function.uncurry h)
      (Ioi 0 ×ˢ (Ioo (c - r) c ∪ Ioo c (c + r))) →
    ContinuousOn (Function.uncurry h) (Ioi 0 ×ˢ Ioo (c - r) (c + r)) →
    (∀ z0 : ℝ, 0 < z0 → ∃ l, Tendsto (Function.uncurry (Work.Spaces.pz h))
      (𝓝[Ioi 0 ×ˢ (Ioo (c - r) c ∪ Ioo c (c + r))] (z0, c)) (𝓝 l)) →
    (∀ z0 : ℝ, 0 < z0 → ∃ l, Tendsto (Function.uncurry (Work.Spaces.pth h))
      (𝓝[Ioi 0 ×ˢ (Ioo (c - r) c ∪ Ioo c (c + r))] (z0, c)) (𝓝 l)) →
      ContDiffOn ℝ 1 (Function.uncurry h) (Ioi 0 ×ˢ Ioo (c - r) (c + r)) ∧
      ContinuousOn (Function.uncurry (Work.Spaces.pz h)) (Ioi 0 ×ˢ Ioo (c - r) (c + r)) ∧
      ContinuousOn (Function.uncurry (Work.Spaces.pth h)) (Ioi 0 ×ˢ Ioo (c - r) (c + r))

/-- **B7b `contDiffOn_two_of_partials`**: `C¹` with `C¹` partials gives `C²` on an open set. -/
def ContDiffTwoOfPartials (h : Fn) (U : Set (ℝ × ℝ)) : Prop :=
  IsOpen U → ContDiffOn ℝ 1 (Function.uncurry h) U →
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz h)) U →
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth h)) U →
      ContDiffOn ℝ 2 (Function.uncurry h) U

/-- **B7c `glue_line_C2`**: `C²` gluing across `θ = c`. -/
def GlueLineC2 (h : Fn) (c r : ℝ) : Prop :=
  0 < r →
    ContDiffOn ℝ 2 (Function.uncurry h) (Ioi 0 ×ˢ (Ioo (c - r) c ∪ Ioo c (c + r))) →
    ContinuousOn (Function.uncurry h) (Ioi 0 ×ˢ Ioo (c - r) (c + r)) →
    (∀ D ∈ ({Work.Spaces.pz h, Work.Spaces.pth h, Work.Spaces.pz (Work.Spaces.pz h),
        Work.Spaces.pth (Work.Spaces.pz h), Work.Spaces.pz (Work.Spaces.pth h),
        Work.Spaces.pth (Work.Spaces.pth h)} : Set Fn),
      ∀ z0 : ℝ, 0 < z0 → ∃ l, Tendsto (Function.uncurry D)
        (𝓝[Ioi 0 ×ˢ (Ioo (c - r) c ∪ Ioo c (c + r))] (z0, c)) (𝓝 l)) →
      ContDiffOn ℝ 2 (Function.uncurry h) (Ioi 0 ×ˢ Ioo (c - r) (c + r))

/-- **B8a `oddPerS_pieces`**: `oddPerS P` is odd in `θ` on the strip and agrees with `P` (resp.
`-P(-·)`, `-P(π - ·)`) on the three pieces (given `P z (π/2) = 0`). -/
def OddPerSPieces (P : Fn) : Prop :=
  (∀ z, P z (π / 2) = 0) →
    (∀ w θ, oddPerS P w (-θ) = -oddPerS P w θ) ∧
    (∀ w θ, 0 < θ → θ ≤ π / 2 → oddPerS P w θ = P w θ) ∧
    (∀ w θ, -(π / 2) ≤ θ → θ < 0 → oddPerS P w θ = -P w (-θ)) ∧
    (∀ w θ, π / 2 < θ → θ < π → oddPerS P w θ = -P w (π - θ)) ∧
    (∀ w, oddPerS P w 0 = 0)

/-- **E1 `phiB_barrier`**: `phiB` witnesses `SB5Barrier` with `Cφ = 15/4` and `𝓐 phiB = -15/4`. -/
def PhiBBarrier : Prop :=
  ContDiffOn ℝ 2 phiB (Ioo 0 (π / 2)) ∧ (∀ θ ∈ Ioo (0 : ℝ) (π / 2), 0 ≤ phiB θ) ∧
    Tendsto phiB (𝓝[>] 0) atTop ∧ Tendsto phiB (𝓝[<] (π / 2)) atTop ∧
    ∀ θ ∈ Ioo (0 : ℝ) (π / 2),
      -deriv (deriv phiB) θ
        - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * deriv phiB θ = -(15 / 4)

/-- **E2a `bslOp_dilate`**: `bslOp` commutes with dilations in `z`. -/
def BslOpDilate (α lam : ℝ) (P : Fn) : Prop :=
  ∀ z θ, Work.Elliptic.bslOp α (fun z' θ' => P (lam * z') θ') z θ
    = Work.Elliptic.bslOp α P (lam * z) θ

/-- **E2b `bslOp_lincomb`**: `bslOp` is linear at points of the open quadrant where both arguments
are `C²`.  (The restriction to `Qd` is necessary: `Real.tan` is not differentiable at `π/2`, so the
`∂_θ(tan θ·X)` slot of `Lzero` is not additive at `θ = π/2`; see the counterexample found by the
prover of the unrestricted version.) -/
def BslOpLincomb (α a b : ℝ) (P Q : Fn) : Prop :=
  ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ContDiffAt ℝ 2 (Function.uncurry P) (z, θ) →
    ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ) →
      Work.Elliptic.bslOp α (fun z' θ' => a * P z' θ' + b * Q z' θ') z θ
        = a * Work.Elliptic.bslOp α P z θ + b * Work.Elliptic.bslOp α Q z θ

/-- **E3 `bslOp_eq_s2_Lgs`**: the ground-state identity `bslOp α Q = s2 · Lgs α (Q/s2)` on `Qd`. -/
def BslOpEqS2Lgs (α : ℝ) (Q : Fn) : Prop :=
  ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ) →
    Work.Elliptic.bslOp α Q z θ
      = Work.Construction.s2 θ * Lgs α (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ

/-- **E4a `Lgs_nonneg_of_max`**: the coordinatewise maximum principle at an interior maximum. -/
def LgsNonnegOfMax (α : ℝ) (v : Fn) : Prop :=
  ∀ z0 θ0, 0 < z0 → θ0 ∈ Ioo (0 : ℝ) (π / 2) →
    ContDiffAt ℝ 2 (Function.uncurry v) (z0, θ0) →
    IsLocalMax (fun z => v z θ0) z0 → IsLocalMax (fun θ => v z0 θ) θ0 →
      0 ≤ Lgs α v z0 θ0

/-- **E4b `Lgs_barrier`**: `Lgs` of the barrier `w = (M + δφ)(z/L)^{-k} + η`. -/
def LgsBarrier (α k L M δ η : ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiffOn ℝ 2 φ (Ioo 0 (π / 2)) → 0 < L →
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Lgs α (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) z θ
        = (z / L) ^ (-k) * (α * k * (5 - α * k) * (M + δ * φ θ)
            + δ * (-deriv (deriv φ) θ
              - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * deriv φ θ))

/-- **E4c `sb5_compare`**: comparison on the half-strip `z ≥ L`. -/
def Sb5Compare (α k L Mb : ℝ) (Q : Fn) : Prop :=
  0 < α → 0 < L → 0 < α * k → α * k < 5 → SB5Barrier →
    ContDiffOn ℝ 2 (Function.uncurry Q) Work.Construction.Qd →
    (∀ z θ, L < z → θ ∈ Ioo (0 : ℝ) (π / 2) →
      Work.Elliptic.bslOp α Q z θ = 0) →
    (∀ z θ, L ≤ z → θ ∈ Ioo (0 : ℝ) (π / 2) →
      |Q z θ| ≤ Mb * Work.Construction.s2 θ) →
    (∀ ε > 0, ∃ R, ∀ z θ, R ≤ z → θ ∈ Ioo (0 : ℝ) (π / 2) →
      |Q z θ| ≤ ε * Work.Construction.s2 θ) →
      ∀ z θ, L ≤ z → θ ∈ Ioo (0 : ℝ) (π / 2) →
        |Q z θ| ≤ Mb * Work.Construction.s2 θ * (L / z) ^ k

/-- **E5 `unif_decay_ratio`**: pointwise decay plus uniform `∂_θ`-bounds and vanishing at the ends
give `|P| ≤ ε·s2` uniformly in `θ` for `z ≥ R`. -/
def UnifDecayRatio (P : Fn) (K : ℝ) : Prop :=
  (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    DifferentiableAt ℝ (fun θ' => P z θ') θ ∧
      DifferentiableAt ℝ (fun θ' => Work.Spaces.pth P z θ') θ) →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.pth P z θ| ≤ K) →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.pthIter 2 P z θ| ≤ K) →
    (∀ z, 0 < z → Tendsto (fun θ => P z θ) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun θ => P z θ) (𝓝[<] (π / 2)) (𝓝 0)) →
    (∀ θ ∈ Ioo (0 : ℝ) (π / 2), Tendsto (fun z => P z θ) atTop (𝓝 0)) →
      ∀ ε > 0, ∃ R, ∀ z θ, R ≤ z → θ ∈ Ioo (0 : ℝ) (π / 2) →
        |P z θ| ≤ ε * Work.Construction.s2 θ

/-- **E6a `dq1_facts`**: the first log-difference quotient. -/
def Dq1Facts (g : ℝ → ℝ) (L B : ℝ) : Prop :=
  0 < L → (∀ z, L ≤ z → DifferentiableAt ℝ g z) →
    (∀ z, L ≤ z → |z * deriv g z| ≤ B) →
      (∀ h > 0, ∀ z, L ≤ z → |(g (Real.exp h * z) - g z) / h| ≤ B) ∧
      (∀ z, L < z → Tendsto (fun h => (g (Real.exp h * z) - g z) / h) (𝓝[>] 0)
        (𝓝 (z * deriv g z)))

/-- **E6b `dq2_facts`**: the second log-difference quotient. -/
def Dq2Facts (g : ℝ → ℝ) (L B : ℝ) : Prop :=
  0 < L →
    (∀ z, L ≤ z → DifferentiableAt ℝ g z ∧
      DifferentiableAt ℝ (fun z' => z' * deriv g z') z) →
    ContinuousOn (fun z => z * deriv (fun z' => z' * deriv g z') z) (Ici L) →
    (∀ z, L ≤ z → |z * deriv (fun z' => z' * deriv g z') z| ≤ B) →
      (∀ h > 0, ∀ z, L ≤ z →
        |(g (Real.exp (2 * h) * z) - 2 * g (Real.exp h * z) + g z) / h ^ 2| ≤ B) ∧
      (∀ z, L < z → Tendsto
        (fun h => (g (Real.exp (2 * h) * z) - 2 * g (Real.exp h * z) + g z) / h ^ 2)
        (𝓝[>] 0) (𝓝 (z * deriv (fun z' => z' * deriv g z') z)))

end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB3.DzJDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB3

open Work.FTS.StreamBdryIface (Uprime SlotBd)

set_option autoImplicit false

/-- **The scaled parameter integral** `J c g z θ = ∫_0^1 v^c · g (z v, θ) dv`. -/
def J (c : ℝ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => ∫ v in (0 : ℝ)..1, v ^ c * g (z * v) θ

@[simp] lemma J_apply (c : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    J c g z θ = ∫ v in (0 : ℝ)..1, v ^ c * g (z * v) θ := rfl

/-- `Iint` *is* the scaled parameter integral of the slot `U'(Ψ)` at `c = 3/αG - 1`. -/
lemma Iint_eq_J (αG : ℝ) (Ψ : ℝ → ℝ → ℝ) :
    Iint αG Ψ = J (3 / αG - 1) (Uprime αG Ψ) := rfl

/-- The open quadrant is open. -/
theorem isOpen_Qd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo

/-- **Slice continuity of a scaled slice.**  If `g` is jointly continuous on the open quadrant,
then for `x > 0` and `θ ∈ (0,π/2)` the `v`-slice `v ↦ g (x v, θ)` is continuous on `(0,∞)`.
(Every point `(x v, θ)` with `v > 0` lies in the open quadrant, where `g` is continuous.) -/
theorem continuousOn_scaled_slice {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) Work.Construction.Qd)
    {x : ℝ} (hx : 0 < x) {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) :
    ContinuousOn (fun v => g (x * v) θ) (Ioi 0) := by
  have h1 : ContinuousOn (fun v : ℝ => (x * v, θ)) (Ioi 0) := by fun_prop
  have h2 := hg.comp h1 (fun v hv => ⟨mul_pos hx hv, hθ⟩)
  simpa [Function.comp_def, Function.uncurry] using h2

end Work.FTS_StreamBdry.SB3
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB3.P2Aux.fam_ode_deriv_bound_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB3.P2Aux

open scoped Real Topology
open Set Filter


end Work.FTS_StreamBdry.SB3.P2Aux
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB4.psiP_lipschitz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB4.psiP_lipschitz`

The `U`-slot part `psiP αG Ψ = -(s2 θ/αG)·∫₀¹ v^{3/αG-1}·U'(Ψ)(zv,θ) dv` of the stream function
inherits the `z`-Lipschitz regularity of the slot `U'(Ψ)` on `Ioc 0 1`, with the sharp constant:

if `|U'(Ψ)(z,θ) - U'(Ψ)(z',θ)| ≤ C·|z - z'|` for `z, z' ∈ (0,1]` and `θ ∈ Iθ`, then

`|psiP(z,θ) - psiP(z',θ)| ≤ (s2 θ · C/(3 + αG))·|z - z'|`.

The engine (lemma `rpow_mul_lip_integral_le` below) is the elementary estimate
`|∫₀¹ v^{p-1}(g(zv) - g(z'v)) dv| ≤ C·|z-z'|/(p+1)` for a `C`-Lipschitz `g` on `Ioc 0 1` and
`p > 0`: extend `g` to a globally Lipschitz `G` (`LipschitzOnWith.extend_real`), so that the
integrands are dominated by `v^{p-1}` and one may apply `integral_sub` and
`norm_integral_le_of_norm_le`; the arithmetic is `∫₀¹ v^p = 1/(p+1)` and
`(s2/αG)·(1/(3/αG + 1)) = s2/(3 + αG)`.
-/

noncomputable section

open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB4

/-- **The integral Lipschitz estimate.**  If `g` is `C`-Lipschitz on `Ioc 0 1` and `p > 0`, then the
parameter-dependent integrals `z ↦ ∫₀¹ v^{p-1}·g(z·v) dv` are Lipschitz with constant
`C/(p+1)` on `Ioc 0 1`. -/
lemma rpow_mul_lip_integral_le {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C) {g : ℝ → ℝ}
    (hg : ∀ x ∈ Set.Ioc 0 1, ∀ y ∈ Set.Ioc 0 1, |g x - g y| ≤ C * |x - y|)
    {z z' : ℝ} (hz : z ∈ Set.Ioc 0 1) (hz' : z' ∈ Set.Ioc 0 1) :
    |(∫ v in (0:ℝ)..1, v ^ (p - 1) * g (z * v))
        - (∫ v in (0:ℝ)..1, v ^ (p - 1) * g (z' * v))|
      ≤ C * |z - z'| / (p + 1) := by
  have hp1 : -1 < p - 1 := by linarith
  have hp1' : -1 < p := by linarith
  set K : ℝ≥0 := Real.toNNReal C with hKdef
  have hK : (K : ℝ) = C := Real.coe_toNNReal C hC
  have hLip : LipschitzOnWith K g (Set.Ioc 0 1) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq, hK]
    exact hg x hx y hy
  -- extend `g` to a globally Lipschitz function, so that the integrands are dominated by `v^{p-1}`
  obtain ⟨G, hGlip, hGeq⟩ := hLip.extend_real
  have hGdiff : ∀ x y : ℝ, |G x - G y| ≤ C * |x - y| := by
    intro x y
    have h := hGlip.dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq, hK] at h
    exact h
  have integrable_G : ∀ {w : ℝ},
      IntervalIntegrable (fun v : ℝ => v ^ (p - 1) * G (w * v)) volume 0 1 := by
    intro w
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine MeasureTheory.Integrable.mono'
      (g := fun v : ℝ => v ^ (p - 1) * (|G 0| + C * |w|)) ?_ ?_ ?_
    · have h1 : IntervalIntegrable (fun v : ℝ => v ^ (p - 1)) volume 0 1 :=
        intervalIntegral.intervalIntegrable_rpow' hp1
      have h2 : IntervalIntegrable (fun v : ℝ => v ^ (p - 1) * (|G 0| + C * |w|))
          volume 0 1 := h1.mul_const _
      rwa [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h2
    · refine ContinuousOn.aestronglyMeasurable (μ := volume) ?_ measurableSet_Ioc
      refine ContinuousOn.mul ?_ ?_
      · exact fun v hv =>
          (Real.continuousAt_rpow_const v (p - 1) (Or.inl (ne_of_gt hv.1))).continuousWithinAt
      · exact (hGlip.continuous.comp (continuous_const.mul continuous_id)).continuousOn
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun v hv => ?_
      have hv0 : 0 ≤ v := le_of_lt hv.1
      have hrpow : 0 ≤ v ^ (p - 1) := Real.rpow_nonneg hv0 _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrpow]
      have hb : |G (w * v)| ≤ |G 0| + C * |w| := by
        have h1 : |G (w * v) - G 0| ≤ C * |w * v| := by
          have h := hGdiff (w * v) 0
          simpa using h
        have h2 : |w * v| ≤ |w| := by
          rw [abs_mul]
          calc |w| * |v| ≤ |w| * 1 :=
                mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg hv0]; exact hv.2) (abs_nonneg w)
            _ = |w| := mul_one _
        calc |G (w * v)| = |G (w * v) - G 0 + G 0| := by ring_nf
          _ ≤ |G (w * v) - G 0| + |G 0| := abs_add_le _ _
          _ ≤ C * |w| + |G 0| :=
              add_le_add (le_trans h1 (mul_le_mul_of_nonneg_left h2 hC)) le_rfl
          _ = |G 0| + C * |w| := by ring
      exact mul_le_mul_of_nonneg_left hb hrpow
  have hInt_z := integrable_G (w := z)
  have hInt_z' := integrable_G (w := z')
  have hmem : ∀ v ∈ Set.Ioc 0 1, z * v ∈ Set.Ioc 0 1 := fun v hv =>
    ⟨mul_pos hz.1 hv.1, by nlinarith [hz.1, hz.2, hv.1, hv.2]⟩
  have hmem' : ∀ v ∈ Set.Ioc 0 1, z' * v ∈ Set.Ioc 0 1 := fun v hv =>
    ⟨mul_pos hz'.1 hv.1, by nlinarith [hz'.1, hz'.2, hv.1, hv.2]⟩
  -- replace `g` by its extension `G` in the two integrals
  have hcz : (∫ v in (0:ℝ)..1, v ^ (p - 1) * g (z * v))
      = ∫ v in (0:ℝ)..1, v ^ (p - 1) * G (z * v) := by
    refine intervalIntegral.integral_congr_ae ?_
    refine Filter.Eventually.of_forall fun v hv => ?_
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
    have hxv : g (z * v) = G (z * v) := hGeq (hmem v hv)
    rw [hxv]
  have hcz' : (∫ v in (0:ℝ)..1, v ^ (p - 1) * g (z' * v))
      = ∫ v in (0:ℝ)..1, v ^ (p - 1) * G (z' * v) := by
    refine intervalIntegral.integral_congr_ae ?_
    refine Filter.Eventually.of_forall fun v hv => ?_
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
    have hxv : g (z' * v) = G (z' * v) := hGeq (hmem' v hv)
    rw [hxv]
  rw [hcz, hcz', ← intervalIntegral.integral_sub hInt_z hInt_z']
  have hint_g : IntervalIntegrable (fun v : ℝ => C * |z - z'| * v ^ p) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hp1').const_mul _
  have hbound : ∀ᵐ v ∂(volume : Measure ℝ), v ∈ Set.Ioc 0 1 →
      ‖v ^ (p - 1) * G (z * v) - v ^ (p - 1) * G (z' * v)‖ ≤ C * |z - z'| * v ^ p := by
    refine Filter.Eventually.of_forall fun v hv => ?_
    have hv0 : 0 ≤ v := le_of_lt hv.1
    have hrpow : 0 ≤ v ^ (p - 1) := Real.rpow_nonneg hv0 _
    rw [Real.norm_eq_abs]
    have hkey : v ^ (p - 1) * G (z * v) - v ^ (p - 1) * G (z' * v)
        = v ^ (p - 1) * (G (z * v) - G (z' * v)) := by ring
    rw [hkey, abs_mul, abs_of_nonneg hrpow]
    have h1 : |G (z * v) - G (z' * v)| ≤ C * |z * v - z' * v| := hGdiff _ _
    have h2 : |z * v - z' * v| = |z - z'| * v := by
      rw [← sub_mul, abs_mul, abs_of_nonneg hv0]
    rw [h2] at h1
    have h3 : v ^ p = v ^ (p - 1) * v := by
      have h := Real.rpow_add_one (x := v) (ne_of_gt hv.1) (p - 1)
      rw [sub_add_cancel] at h
      exact h
    rw [h3]
    calc v ^ (p - 1) * |G (z * v) - G (z' * v)| ≤ v ^ (p - 1) * (C * (|z - z'| * v)) :=
          mul_le_mul_of_nonneg_left h1 hrpow
      _ = C * |z - z'| * (v ^ (p - 1) * v) := by ring
  have hstep : |∫ v in (0:ℝ)..1, (v ^ (p - 1) * G (z * v) - v ^ (p - 1) * G (z' * v))|
      ≤ ∫ v in (0:ℝ)..1, C * |z - z'| * v ^ p := by
    have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := 1)
      (by norm_num) (f := fun v => v ^ (p - 1) * G (z * v) - v ^ (p - 1) * G (z' * v))
      (g := fun v => C * |z - z'| * v ^ p) hbound hint_g
    simpa only [Real.norm_eq_abs] using h
  have hval : (∫ v in (0:ℝ)..1, C * |z - z'| * v ^ p) = C * |z - z'| / (p + 1) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hp1')]
    rw [Real.one_rpow, Real.zero_rpow (by linarith : p + 1 ≠ 0), sub_zero]
    rw [mul_one_div]
  exact hstep.trans (le_of_eq hval)

theorem psiP_lipschitz {αG : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hU : ∀ z ∈ Set.Ioc 0 1, ∀ z' ∈ Set.Ioc 0 1, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.StreamBdryIface.Uprime αG Ψ z θ - Work.FTS.StreamBdryIface.Uprime αG Ψ z' θ|
        ≤ C * |z - z'|) :
    ∃ K : ℝ → NNReal, ∀ θ ∈ Work.Spaces.Iθ,
      (K θ : ℝ) = Work.Construction.s2 θ * C / (3 + αG) ∧
      LipschitzOnWith (K θ) (fun z => Work.FTS.StreamBdryIface.psiP αG Ψ z θ) (Set.Ioc 0 1) := by
  refine ⟨fun θ => Real.toNNReal (Work.Construction.s2 θ * C / (3 + αG)), ?_⟩
  intro θ hθ
  have hs2 : 0 ≤ Work.Construction.s2 θ := by
    rw [Work.Construction.s2_eq]
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hKval : ((Real.toNNReal (Work.Construction.s2 θ * C / (3 + αG))) : ℝ)
      = Work.Construction.s2 θ * C / (3 + αG) := Real.coe_toNNReal _ (by positivity)
  refine ⟨hKval, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro z hz z' hz'
  rw [Real.dist_eq, Real.dist_eq, hKval]
  have hα3 : 0 < 3 / αG := by positivity
  have hkey := rpow_mul_lip_integral_le (p := 3 / αG) (C := C) hα3 hC
    (g := fun v => Work.FTS.StreamBdryIface.Uprime αG Ψ v θ)
    (fun x hx y hy => hU x hx y hy θ hθ) hz hz'
  have hpsi : ∀ w : ℝ, Work.FTS.StreamBdryIface.psiP αG Ψ w θ
      = -(Work.Construction.s2 θ / αG) *
        (∫ v in (0:ℝ)..1, v ^ (3 / αG - 1)
          * Work.FTS.StreamBdryIface.Uprime αG Ψ (w * v) θ) :=
    fun w => Work.FTS_StreamBdry.psiP_eq_Iint αG Ψ w θ
  have hcoef : (0:ℝ) ≤ Work.Construction.s2 θ / αG := by positivity
  set Iz : ℝ := ∫ v in (0:ℝ)..1, v ^ (3 / αG - 1)
    * Work.FTS.StreamBdryIface.Uprime αG Ψ (z * v) θ with hIz
  set Iz' : ℝ := ∫ v in (0:ℝ)..1, v ^ (3 / αG - 1)
    * Work.FTS.StreamBdryIface.Uprime αG Ψ (z' * v) θ with hIz'
  have hkey' : |Iz - Iz'| ≤ C * |z - z'| / (3 / αG + 1) := by
    rw [hIz, hIz']
    exact hkey
  have hfin : (Work.Construction.s2 θ / αG) * (C * |z - z'| / (3 / αG + 1))
      = Work.Construction.s2 θ * C / (3 + αG) * |z - z'| := by
    have hz1 : (3:ℝ) / αG + 1 = (3 + αG) / αG := by
      have hαne : αG ≠ 0 := ne_of_gt hαG
      field_simp
    have h3ne : (3 + αG) ≠ 0 := by positivity
    have hαne : αG ≠ 0 := ne_of_gt hαG
    rw [hz1]
    field_simp
  rw [hpsi z, hpsi z']
  rw [show -(Work.Construction.s2 θ / αG) * Iz - -(Work.Construction.s2 θ / αG) * Iz'
      = -(Work.Construction.s2 θ / αG) * (Iz - Iz') from by ring]
  rw [abs_mul, abs_neg, abs_of_nonneg hcoef]
  exact le_trans (mul_le_mul_of_nonneg_left hkey' hcoef) (le_of_eq hfin)

end Work.FTS_StreamBdry.SB4
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB6.UprimeAux.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.UprimeAux.Defs` — the weight `wfun` of the singular `θ`-ODE

The lemma `Work.FTS_StreamBdry.SB6.uprime_le` bounds `∂_θ u` where

  `u(z,θ) = psiP αG Ψ z θ / sin 2θ`   on `Qd = (0,∞) × (0,π/2)`,

i.e. the `θ`-derivative of the `U`-slot part of the stream function divided by `sin 2θ`.  The
content is the ground-state ODE of `Work.FTS_StreamBdry.SB3.P2Aux.bslOp_div_s2_hasDerivAt`:
on `Qd`

  `u'' + c(θ) u' = H`,   `c(θ) = 4 cos 2θ / sin 2θ - tan θ`,

with `|H| ≤ A / sin 2θ + C`.  The integrating factor of this singular equation is
`exp (∫ c) = sin²(2θ) cos θ = 4 wfun θ` with

  `wfun θ = sin²θ · cos³θ`,

which vanishes like `θ²` at `θ = 0` and like `(π/2 - θ)³` at `θ = π/2`.  Consequently
`G := wfun · u'` satisfies `G' = wfun · H`, hence `G` is controlled by
`gwt A C θ = wfun θ · (A / sin 2θ + C) = A·wfun θ/sin 2θ + C·wfun θ`, and the two endpoints are
harmless because `wfun θ / sin 2θ = sin θ cos²θ / 2` is *bounded* (indeed `→ 0`).
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB6.UprimeAux

set_option autoImplicit false

/-- The integrating factor weight `wfun θ = sin²θ·cos³θ` of the singular `θ`-equation:
`wfun' = wfun · (4 cos 2θ / sin 2θ - tan θ)` on `(0, π/2)`. -/
def wfun (θ : ℝ) : ℝ := Real.sin θ ^ 2 * Real.cos θ ^ 3

/-- The pointwise bound function for the right hand side: with `|H| ≤ A/sin 2θ + C` one has
`|wfun · H| ≤ gwt A C`. -/
def gwt (A C θ : ℝ) : ℝ := A * (wfun θ / Real.sin (2 * θ)) + C * wfun θ

@[simp] theorem wfun_def (θ : ℝ) : wfun θ = Real.sin θ ^ 2 * Real.cos θ ^ 3 := rfl
@[simp] theorem gwt_def (A C θ : ℝ) :
    gwt A C θ = A * (wfun θ / Real.sin (2 * θ)) + C * wfun θ := rfl

end Work.FTS_StreamBdry.SB6.UprimeAux
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB6.infra =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.infra` — elementary helpers for the SB6 rates

`sin 2θ ≤ 2(π/2 - θ)`, the `|·|`-combination lemmas, `M ≥ 0` from `SlotBd`, and the two
one-sided squeezes.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP oddPerS)

set_option autoImplicit false

/-- `s2 θ = sin 2θ ≤ 2(π/2 - θ)` for `θ ≤ π/2`. -/
lemma s2_le_two_mul_sub {θ : ℝ} (hθ : θ ≤ Real.pi / 2) :
    Work.Construction.s2 θ ≤ 2 * (Real.pi / 2 - θ) := by
  rw [Work.Construction.s2_eq]
  have h : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
    rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
  rw [h]
  exact Real.sin_le (by linarith)

/-- `|a| ≤ A`, `|b| ≤ B`, `|c| ≤ C`, `|d| ≤ D` give `|a + b + c + d| ≤ A + B + C + D`. -/
lemma abs_four_le {a b c d A B C D : ℝ} (h1 : |a| ≤ A) (h2 : |b| ≤ B) (h3 : |c| ≤ C)
    (h4 : |d| ≤ D) : |a + b + c + d| ≤ A + B + C + D := by
  have h12 : |a + b| ≤ A + B := (abs_add_le a b).trans (add_le_add h1 h2)
  have h123 : |a + b + c| ≤ A + B + C := (abs_add_le (a + b) c).trans (add_le_add h12 h3)
  exact (abs_add_le (a + b + c) d).trans (add_le_add h123 h4)

/-- The same for the shape `|a + b - c - d|` in which the identity `pthIter2_eq` is stated. -/
lemma abs_four_sub_le {a b c d A B C D : ℝ} (h1 : |a| ≤ A) (h2 : |b| ≤ B) (h3 : |c| ≤ C)
    (h4 : |d| ≤ D) : |a + b - c - d| ≤ A + B + C + D := by
  have he : a + b - c - d = a + b + (-c) + (-d) := by ring
  rw [he]
  exact abs_four_le h1 h2 (by simpa using h3) (by simpa using h4)

/-- `|a + b + c| ≤ |a| + |b| + |c|`. -/
lemma abs_three_le {a b c : ℝ} : |a + b + c| ≤ |a| + |b| + |c| := by
  have h1 : |a + b| ≤ |a| + |b| := abs_add_le a b
  calc |a + b + c| ≤ |a + b| + |c| := abs_add_le (a + b) c
    _ ≤ |a| + |b| + |c| := by linarith [h1]

/-- `M ≥ 0`, forced by `SlotBd` at any point of the (nonempty) quadrant. -/
lemma M_nonneg {αG M : ℝ} {Ψ : ℝ → ℝ → ℝ} (hslot : SlotBd αG Ψ M) : 0 ≤ M := by
  have h1 : ((1 : ℝ), Real.pi / 4) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr
      ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  exact le_trans (abs_nonneg _) (Work.FTS_StreamBdry.SlotBd.Uprime_le hslot h1)


/-- Squeeze at the right endpoint: `|Q θ| ≤ M·s2 θ` near `π/2` gives `Q θ → 0` as `θ → π/2⁻`. -/
lemma tendsto_zero_of_abs_le_s2_right {Q : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Q θ| ≤ M * Work.Construction.s2 θ) :
    Filter.Tendsto Q (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hs : Filter.Tendsto (fun θ : ℝ => Work.Construction.s2 θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hcont : Continuous (fun θ : ℝ => Work.Construction.s2 θ) := by
      change Continuous fun θ : ℝ => Real.sin (2 * θ)
      fun_prop
    have h0 : Work.Construction.s2 (Real.pi / 2) = 0 := by
      rw [Work.Construction.s2_eq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    simpa only [h0] using (hcont.tendsto (Real.pi / 2)).mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun θ : ℝ => |Q θ|)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    refine squeeze_zero' ?_ ?_ (by simpa only [mul_zero] using hs.const_mul M)
    · filter_upwards with θ using abs_nonneg _
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2))]
        with θ hθ hθ2
      exact h θ ⟨hθ2, hθ⟩
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using h2)


end Work.FTS_StreamBdry.SB6
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SBpsiP.SelfUprime` — finite-order smoothness of the slot iterates

The `U`-slot `U'(Ψ) = U(Ψ)/sin 2θ` with `U(Ψ) = -3Ψ - αG·z∂_zΨ` is `C²` on the open quadrant
`Qd` as soon as `Ψ` is `C³` there (`∂_z` costs one order, the division by the nonvanishing
`sin 2θ` costs none), and each application of `D_z = z∂_z` costs one further order:

  `Ψ ∈ C³(Qd)  ⟹  D_z^j U'(Ψ) ∈ C^{2-j}(Qd)`,   `j ≤ 2`.

This is what turns the `SlotBd` hypotheses (continuity of `D_z^j U'(Ψ)`, `j ≤ 2`) into the
hypotheses of the differentiation identity `SBpsiP.J_Dz_eq`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SBpsiP

open Work.FTS.StreamBdryIface (Uprime)

set_option autoImplicit false

/-- `U'(Ψ)` is `C²` on the open quadrant for a `C³` `Ψ`. -/
theorem Uprime_contDiffOn_two {αG : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    ContDiffOn ℝ 2 (Function.uncurry (Uprime αG Ψ)) Work.Construction.Qd := by
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have h2 : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd := h3.of_le (by norm_num)
  have hpz : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz Ψ)) Work.Construction.Qd :=
    Work.FTS.EllipticEst.EllGap.MLevelBookkeeping.contDiffOn_uncurry_pz_of_isOpen hQd h3
  have hnum : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      -3 * Function.uncurry Ψ p - αG * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p)
      Work.Construction.Qd :=
    (contDiffOn_const.mul h2).sub ((contDiffOn_const.mul contDiff_fst.contDiffOn).mul hpz)
  have hden : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.Construction.Qd :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hne : ∀ p ∈ Work.Construction.Qd, Real.sin (2 * p.2) ≠ 0 := by
    intro p hp
    have hθ1 : 0 < p.2 := hp.2.1
    have hθ2 : p.2 < Real.pi / 2 := hp.2.2
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  refine (hnum.div hden hne).congr (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry, Uprime, Work.Construction.Uop, Work.Construction.s2,
    Work.Spaces.pz, Pi.div_apply]

/-- `D_z U'(Ψ)` is `C¹` on the open quadrant. -/
theorem DzUprime_contDiffOn_one {αG : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.Dz (Uprime αG Ψ))) Work.Construction.Qd := by
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have hU : ContDiffOn ℝ 2 (Function.uncurry (Uprime αG Ψ)) Work.Construction.Qd :=
    Uprime_contDiffOn_two h3
  have hpz : ContDiffOn ℝ 1
      (Function.uncurry (Work.Spaces.pz (Uprime αG Ψ))) Work.Construction.Qd :=
    Work.FTS.EllipticEst.EllGap.MLevelBookkeeping.contDiffOn_uncurry_pz_of_isOpen hQd hU
  refine (contDiff_fst.contDiffOn.mul hpz).congr (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  rfl

/-- `D_z(D_z U'(Ψ))` is continuous on the open quadrant. -/
theorem Dz2Uprime_contDiffOn_zero {αG : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    ContDiffOn ℝ 0
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dz (Uprime αG Ψ))))
      Work.Construction.Qd := by
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have hDz1 : ContDiffOn ℝ 1
      (Function.uncurry (Work.Spaces.Dz (Uprime αG Ψ))) Work.Construction.Qd :=
    DzUprime_contDiffOn_one h3
  have hpz : ContDiffOn ℝ 0
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.Dz (Uprime αG Ψ))))
      Work.Construction.Qd :=
    Work.FTS.EllipticEst.EllGap.MLevelBookkeeping.contDiffOn_uncurry_pz_of_isOpen hQd hDz1
  refine (contDiff_fst.contDiffOn.mul hpz).congr (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  rfl

/-- **Finite-order smoothness of the slot iterates**: `D_z^j U'(Ψ) ∈ C^{2-j}` on `Qd`, `j ≤ 2`. -/
theorem UprimeIterSmooth_self {αG : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    ∀ j : ℕ, j ≤ 2 → ContDiffOn ℝ (2 - j)
      (Function.uncurry (Work.Spaces.DzIter j (Uprime αG Ψ))) Work.Construction.Qd := by
  have hU := Uprime_contDiffOn_two (αG := αG) h3
  have hDz1 := DzUprime_contDiffOn_one (αG := αG) h3
  have hDz2 := Dz2Uprime_contDiffOn_zero (αG := αG) h3
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · exact hU
  · exact hDz1
  · exact hDz2

end Work.FTS_StreamBdry.SBpsiP
end
end
