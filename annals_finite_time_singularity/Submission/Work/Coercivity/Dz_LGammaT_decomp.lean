import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.zAux
import Submission.Work.Coercivity.Basic
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.pz_aux
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Elliptic.pth_DzIter
import Submission.Work.FM.Core
import Submission.Work.FM.Core2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- `∂_z (L₁₂ f)(z) = - Kavg f z / z` for `z > 0` (from `HardyHyp`). -/
theorem L12f_zDeriv (f : ℝ → ℝ → ℝ) (hf : HardyHyp f) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' => L12f f z') (-(Kavg f z / z)) z := by
  have hcont : ContinuousAt (FM.L12dens Spaces.K f) z := hf.hcont z (by simpa using hz)
  have h := FM.hasDerivAt_L12 (K := Spaces.K) (f := f) hf.hint hcont hz
  have hden : FM.L12dens Spaces.K f z = Kavg f z / z := by
    rw [FM.L12dens_eq (K := Spaces.K) (f := f) (s := z) (ne_of_gt hz), Kavg, Spaces.Iθ]
  rw [hden] at h
  simpa only [L12f] using h

/-- `∂_z (D_z f) = ∂_z f + z ∂_z² f`, at a point where the `z`-slice is differentiable
one more time. -/
theorem pz_Dz_eq' {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (fun t => Spaces.pz f t θ) z) :
    Spaces.pz (Spaces.Dz f) z θ = Spaces.pz f z θ + z * Spaces.pz (Spaces.pz f) z θ := by
  have h1 : HasDerivAt (fun t : ℝ => t * Spaces.pz f t θ)
      (1 * Spaces.pz f z θ + z * Spaces.pz (Spaces.pz f) z θ) z :=
    (hasDerivAt_id z).mul h.hasDerivAt
  rw [show Spaces.pz (Spaces.Dz f) z θ
      = deriv (fun t : ℝ => t * Spaces.pz f t θ) z from rfl, h1.deriv]
  ring

theorem Dz_LGammaT_decomp (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hsm : Spaces.SmoothNbhd f) (hfH : HardyHyp f) :
    ∀ z θ, 0 < z → θ ∈ Spaces.Iθ → Spaces.Dz (LGammaT α f) z θ = SumI α f z θ := by
  intro z θ hz hθ
  have hzI : z ∈ Spaces.Iz := by rw [Spaces.Iz]; exact le_of_lt hz
  have hy : (z, θ) ∈ Spaces.nbhU := Spaces.mem_nbhU hzI hθ
  have hmem : Spaces.nbhU ∈ 𝓝 (z, θ) := Spaces.isOpen_nbhU.mem_nhds hy
  have h1z : (1 + z) ≠ 0 := by positivity
  have htop : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hcd : ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ) := ContDiffOn.contDiffAt hsm hmem
  have hAc : ContDiffAt ℝ ⊤ (fun t : ℝ => f t θ) z := Spaces.contDiffAt_slice_left hcd
  have hA1c : ContDiffAt ℝ ⊤ (fun t : ℝ => Spaces.pz f t θ) z :=
    Spaces.contDiffAt_slice_left
      ((Spaces.contDiffOn_uncurry_pz Spaces.isOpen_nbhU hsm).contDiffAt hmem)
  have hBc : ContDiffAt ℝ ⊤ (fun t : ℝ => Spaces.pth f t θ) z :=
    Spaces.contDiffAt_slice_left
      ((Spaces.contDiffOn_uncurry_pth Spaces.isOpen_nbhU hsm).contDiffAt hmem)
  have hA1diff : DifferentiableAt ℝ (fun t => Spaces.pz f t θ) z := hA1c.differentiableAt htop
  have hA : HasDerivAt (fun t : ℝ => f t θ) (Spaces.pz f z θ) z :=
    (hAc.differentiableAt htop).hasDerivAt
  have hA1 : HasDerivAt (fun t : ℝ => Spaces.pz f t θ) (Spaces.pz (Spaces.pz f) z θ) z :=
    hA1diff.hasDerivAt
  have hB : HasDerivAt (fun t : ℝ => Spaces.pth f t θ) (Spaces.pz (Spaces.pth f) z θ) z :=
    (hBc.differentiableAt htop).hasDerivAt
  have hΛ : HasDerivAt (fun t : ℝ => L12f f t) (-(Kavg f z / z)) z := L12f_zDeriv f hfH hz
  -- the auxiliary function, in the `c⁻¹`-normalised form
  let H : ℝ → ℝ := fun t =>
    f t θ + t * Spaces.pz f t θ + (-(2 * f t θ)) / (1 + t)
      + (-(2 * Spaces.Gam α θ * (Spaces.c α)⁻¹)) * (t * ((1 + t) ^ 2)⁻¹) * L12f f t
      + (-(3 * Real.sin (2 * θ))) * Spaces.pth f t θ / (1 + t)
      + (Spaces.Gam α θ * (Spaces.c α)⁻¹ * C0 f) * (2 * t ^ 2 * ((1 + t) ^ 3)⁻¹)
  have hGH : (fun t : ℝ => LGammaT α f t θ) =ᶠ[𝓝 z] H := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    simp only [H, LGammaT, LGamma, L, Proj, Transport, Spaces.Dth, Spaces.Dz, C0,
      div_eq_mul_inv, mul_inv_rev]
    ring
  -- derivatives of the six summands
  have hden : HasDerivAt (fun t : ℝ => 1 + t) (1 : ℝ) z :=
    (hasDerivAt_id z).const_add 1
  have hd1 : HasDerivAt (fun t : ℝ => f t θ) (Spaces.pz f z θ) z := hA
  have hd2 : HasDerivAt (fun t : ℝ => t * Spaces.pz f t θ)
      (1 * Spaces.pz f z θ + z * Spaces.pz (Spaces.pz f) z θ) z :=
    (hasDerivAt_id z).mul hA1
  have hnum3 : HasDerivAt (fun t : ℝ => -(2 * f t θ)) (-(2 * Spaces.pz f z θ)) z := by
    simpa only [neg_mul] using hA.const_mul (-2)
  have hd3 : HasDerivAt (fun t : ℝ => (-(2 * f t θ)) / (1 + t))
      (((-(2 * Spaces.pz f z θ)) * (1 + z) - (-(2 * f z θ)) * 1) / (1 + z) ^ 2) z :=
    hnum3.div hden h1z
  have hsq : HasDerivAt (fun t : ℝ => (1 + t) ^ 2) (2 * (1 + z)) z := by
    have hraw := hden.pow 2
    have hfun : ((fun t : ℝ => 1 + t) ^ 2) =ᶠ[𝓝 z] (fun t : ℝ => (1 + t) ^ 2) :=
      Filter.Eventually.of_forall (fun t => by simp)
    exact (hraw.congr_of_eventuallyEq hfun).congr_deriv (by simp)
  have hinv : HasDerivAt (fun t : ℝ => ((1 + t) ^ 2)⁻¹)
      (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2) z := hsq.inv (by positivity)
  have hprod : HasDerivAt (fun t : ℝ => t * ((1 + t) ^ 2)⁻¹)
      (1 * ((1 + z) ^ 2)⁻¹ + z * (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2)) z :=
    (hasDerivAt_id z).mul hinv
  have hd4 : HasDerivAt
      (fun t : ℝ => (-(2 * Spaces.Gam α θ * (Spaces.c α)⁻¹)) * (t * ((1 + t) ^ 2)⁻¹)
        * L12f f t)
      ((-(2 * Spaces.Gam α θ * (Spaces.c α)⁻¹)) * (1 * ((1 + z) ^ 2)⁻¹
          + z * (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2)) * L12f f z
        + ((-(2 * Spaces.Gam α θ * (Spaces.c α)⁻¹)) * (z * ((1 + z) ^ 2)⁻¹))
          * (-(Kavg f z / z))) z :=
    (hprod.const_mul (-(2 * Spaces.Gam α θ * (Spaces.c α)⁻¹))).mul hΛ
  have hnum5 : HasDerivAt (fun t : ℝ => (-(3 * Real.sin (2 * θ))) * Spaces.pth f t θ)
      ((-(3 * Real.sin (2 * θ))) * Spaces.pz (Spaces.pth f) z θ) z := hB.const_mul _
  have hd5 : HasDerivAt
      (fun t : ℝ => (-(3 * Real.sin (2 * θ))) * Spaces.pth f t θ / (1 + t))
      ((((-(3 * Real.sin (2 * θ))) * Spaces.pz (Spaces.pth f) z θ) * (1 + z)
          - (-(3 * Real.sin (2 * θ))) * Spaces.pth f z θ * 1) / (1 + z) ^ 2) z :=
    hnum5.div hden h1z
  have hsq2 : HasDerivAt (fun t : ℝ => 2 * t ^ 2) (4 * z) z := by
    have hraw := ((hasDerivAt_id z).pow 2).const_mul 2
    have hfun : (fun y : ℝ => 2 * (id ^ 2) y) =ᶠ[𝓝 z] (fun t : ℝ => 2 * t ^ 2) :=
      Filter.Eventually.of_forall (fun t => by simp)
    exact (hraw.congr_of_eventuallyEq hfun).congr_deriv (by simp; ring)
  have hcube : HasDerivAt (fun t : ℝ => (1 + t) ^ 3) (3 * (1 + z) ^ 2) z := by
    have hraw := hden.pow 3
    have hfun : ((fun t : ℝ => 1 + t) ^ 3) =ᶠ[𝓝 z] (fun t : ℝ => (1 + t) ^ 3) :=
      Filter.Eventually.of_forall (fun t => by simp)
    exact (hraw.congr_of_eventuallyEq hfun).congr_deriv (by simp)
  have hinv3 : HasDerivAt (fun t : ℝ => ((1 + t) ^ 3)⁻¹)
      (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2) z := hcube.inv (by positivity)
  have hinner : HasDerivAt (fun t : ℝ => 2 * t ^ 2 * ((1 + t) ^ 3)⁻¹)
      (4 * z * ((1 + z) ^ 3)⁻¹
        + 2 * z ^ 2 * (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2)) z :=
    hsq2.mul hinv3
  have hd6 : HasDerivAt
      (fun t : ℝ => (Spaces.Gam α θ * (Spaces.c α)⁻¹ * C0 f)
        * (2 * t ^ 2 * ((1 + t) ^ 3)⁻¹))
      ((Spaces.Gam α θ * (Spaces.c α)⁻¹ * C0 f) * (4 * z * ((1 + z) ^ 3)⁻¹
          + 2 * z ^ 2 * (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2))) z :=
    hinner.const_mul _
  let E : ℝ := Spaces.pz f z θ + (1 * Spaces.pz f z θ + z * Spaces.pz (Spaces.pz f) z θ)
      + (((-(2 * Spaces.pz f z θ)) * (1 + z) - (-(2 * f z θ)) * 1) / (1 + z) ^ 2)
      + ((-(2 * Spaces.Gam α θ * (Spaces.c α)⁻¹)) * (1 * ((1 + z) ^ 2)⁻¹
            + z * (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2)) * L12f f z
          + ((-(2 * Spaces.Gam α θ * (Spaces.c α)⁻¹)) * (z * ((1 + z) ^ 2)⁻¹))
            * (-(Kavg f z / z)))
      + ((((-(3 * Real.sin (2 * θ))) * Spaces.pz (Spaces.pth f) z θ) * (1 + z)
          - (-(3 * Real.sin (2 * θ))) * Spaces.pth f z θ * 1) / (1 + z) ^ 2)
      + (Spaces.Gam α θ * (Spaces.c α)⁻¹ * C0 f) * (4 * z * ((1 + z) ^ 3)⁻¹
          + 2 * z ^ 2 * (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2))
  have hHderiv : HasDerivAt H E z := by
    dsimp only [E]
    exact ((((hd1.add hd2).add hd3).add hd4).add hd5).add hd6
  have hderivG : deriv (fun t : ℝ => LGammaT α f t θ) z = E := by
    rw [hGH.deriv_eq]
    exact hHderiv.deriv
  -- the `D_θ(D_z f)` expansion
  have hpthDz : Spaces.pth (Spaces.Dz f) z θ = z * Spaces.pz (Spaces.pth f) z θ :=
    Work.Elliptic.pth_DzIter f hsm 1 z θ hzI hθ
  show z * deriv (fun t : ℝ => LGammaT α f t θ) z = SumI α f z θ
  rw [hderivG]
  dsimp only [E]
  simp only [SumI, Z1, Z2, Z3, Z4, Z5, Z6, Z7, L, Spaces.Dth]
  rw [show Spaces.Dz (Spaces.Dz f) z θ = z * Spaces.pz (Spaces.Dz f) z θ from rfl,
    pz_Dz_eq' (f := f) hA1diff, hpthDz]
  simp only [Spaces.Dz]
  simp only [div_eq_mul_inv, mul_inv_rev]
  field_simp
  ring

end Work.Coercivity
