import ChallengeDeps
import Submission.NeckEq
import Submission.NeckSmooth
import Submission.ModelPkg
import Mathlib

/-!
# expOf-flow curves solve the geodesic ODE (child task)

Model-level (E with C3 symmetric PD metric g).  At the base point `b` the flow `Φ` satisfies
per-base flow clauses over `closedBall (b,0) 1` for times `Icc (-Tf) Tf`:
   hΦ : ∀ z ∈ closedBall (b,0) 1, Φ z 0 = z ∧ ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t
`τu < Tf`, `‖v‖ ≤ τu`.  The curve σ(x) := expOf b Φ τu (x • v) is a genuine model geodesic:
for every x ∈ (0,1):
  (a) HasDerivAt σ (τu • (Φ (b, τu⁻¹ • v) (τu * x)).2) x
  (b) HasDerivAt (deriv σ) (accel (g (σ x)) (fderiv ℝ g (σ x)) (deriv σ x)) x
-/

open scoped ENNReal ContDiff Topology
open Set Metric Filter

namespace Submission
namespace FlowOdeChild

open Submission.Model

set_option synthInstance.maxHeartbeats 10000000
set_option maxHeartbeats 32000000

theorem flow_exp_geodesic_ode {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (g : E → Submission.Model.Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (b : E) {Tf : ℝ} (hTf : 0 < Tf)
    (Φ : E × E → ℝ → E × E)
    (hΦ : ∀ z ∈ closedBall (b, 0) 1, Φ z 0 = z ∧
       ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    {τu : ℝ} (hτu0 : 0 < τu) (hτuTf : τu < Tf) {v : E} (hv : ‖v‖ ≤ τu)
    (σ : ℝ → E) (hσ : σ = fun x => expOf b Φ τu (x • v)) :
    ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt σ (τu • (Φ (b, τu⁻¹ • v) (τu * x)).2) x ∧
      HasDerivAt (deriv σ)
        (Submission.Model.accel (g (σ x)) (fderiv ℝ g (σ x)) (deriv σ x)) x := by
  intro x hx
  let z : E × E := (b, τu⁻¹ • v)
  have hz : z ∈ closedBall (b, 0) 1 := by
    simpa [z] using slice_data_mem b τu hτu0 (v := v) hv
  -- the window membership for τu*u with u ∈ (0,1)
  have hwin (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : τu * u ∈ Icc (-Tf) Tf := by
    have hpos : 0 < τu * u := mul_pos hτu0 hu.1
    have hlt : τu * u < τu := by
      simpa using (mul_lt_mul_of_pos_left hu.2 hτu0)
    constructor <;> linarith [hpos, hlt, hτuTf]
  -- the ray identity σ u = (Φ z (τu*u)).1 valid on Ioo (0,1)
  have hσ_eq (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : σ u = (Φ z (τu * u)).1 := by
    have hray := exp_ray_value (g := g) (hg := hg) (hinv := hinv) b (Tf := Tf) hTf Φ hΦ
      (τ := τu) hτu0 hτuTf (v := v) hv (s := u) (le_of_lt hu.1) (le_of_lt hu.2)
    have hσu : σ u = expOf b Φ τu (u • v) := by rw [hσ]
    calc
      σ u = expOf b Φ τu (u • v) := hσu
      _ = (Φ (b, τu⁻¹ • v) (u * τu)).1 := hray
      _ = (Φ z (τu * u)).1 := by
        have hmu : u * τu = τu * u := by ring
        simp [z, hmu]
  -- (a) for any u ∈ (0,1): σ has the claimed derivative
  have hA (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt σ (τu • (Φ z (τu * u)).2) u := by
    have hd := flow_reparam_hasDerivAt (g := g) (hg := hg) (hinv := hinv) b (Tf := Tf) hTf Φ
      (z := z) hz hΦ (τe := τu) (t := u) (hwin u hu)
    have hEv : σ =ᶠ[𝓝 u] (fun u : ℝ => (Φ z (τu * u)).1) := by
      refine eventually_of_mem (isOpen_Ioo.mem_nhds hu) ?_
      intro w hw
      exact hσ_eq w hw
    exact hd.congr_of_eventuallyEq hEv
  constructor
  · -- part (a) at x
    simpa [z] using hA x hx
  · -- part (b): the derivative of deriv σ at x
    let w : ℝ → E := fun u => τu • (Φ z (τu * u)).2
    have hwin_oo : τu * x ∈ Ioo (-Tf) Tf := by
      have hpos : 0 < τu * x := mul_pos hτu0 hx.1
      have hlt : τu * x < τu := by
        simpa using (mul_lt_mul_of_pos_left hx.2 hτu0)
      constructor <;> linarith [hpos, hlt, hτuTf]
    have hsplit := split_flow_geodesic (g := g) (hg := hg) (hinv := hinv) (b, (0 : E)) hTf
      (closedBall (b, 0) 1) Φ hΦ (z := z) hz
    have hd0 : HasDerivAt (fun s : ℝ => (Φ z s).2)
        (accel (g ((Φ z (τu * x)).1)) (fderiv ℝ g ((Φ z (τu * x)).1)) ((Φ z (τu * x)).2))
        (τu * x) := by
      simpa using (hsplit.2 (τu * x) hwin_oo)
    have hlin : HasDerivAt (fun u : ℝ => τu * u) τu x := by
      simpa using ((hasDerivAt_id (𝕜 := ℝ) x).const_mul τu)
    have hd1 : HasDerivAt (fun u : ℝ => (Φ z (τu * u)).2)
        (τu • accel (g ((Φ z (τu * x)).1)) (fderiv ℝ g ((Φ z (τu * x)).1))
          ((Φ z (τu * x)).2)) x := by
      exact (hd0.scomp x hlin)
    have hd2 : HasDerivAt (fun u : ℝ => τu • (Φ z (τu * u)).2)
        (τu • (τu • accel (g ((Φ z (τu * x)).1)) (fderiv ℝ g ((Φ z (τu * x)).1))
          ((Φ z (τu * x)).2))) x := by
      exact hd1.const_smul τu
    have hxσ : σ x = (Φ z (τu * x)).1 := hσ_eq x hx
    have hv_eq : τu • (τu • accel (g ((Φ z (τu * x)).1)) (fderiv ℝ g ((Φ z (τu * x)).1))
          ((Φ z (τu * x)).2)) =
        accel (g (σ x)) (fderiv ℝ g (σ x)) (τu • (Φ z (τu * x)).2) := by
      rw [← hxσ]
      rw [smul_smul]
      rw [← pow_two]
      rw [← accel_smul (g (σ x)) (fderiv ℝ g (σ x)) ((Φ z (τu * x)).2) τu]
    have hw : HasDerivAt w (accel (g (σ x)) (fderiv ℝ g (σ x)) (w x)) x := by
      simpa [w] using hd2.congr_deriv hv_eq
    have hw_deriv : w =ᶠ[𝓝 x] deriv σ := by
      refine eventually_of_mem (isOpen_Ioo.mem_nhds hx) (fun u hu => ?_)
      have hdu : deriv σ u = w u := by
        simpa [w] using (hA u hu).deriv
      exact hdu.symm
    have hB : HasDerivAt (deriv σ) (accel (g (σ x)) (fderiv ℝ g (σ x)) (w x)) x := by
      exact hw.congr_of_eventuallyEq hw_deriv.symm
    have hderx : deriv σ x = w x := by
      simpa [w] using (hA x hx).deriv
    exact hB.congr_deriv (by simp [hderx])

end FlowOdeChild
end Submission
