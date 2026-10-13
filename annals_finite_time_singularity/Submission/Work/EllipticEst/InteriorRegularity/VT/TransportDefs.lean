/-
Copyright: work module for the Elgindi finite-time singularity project (Annals 194(3) 2021).

# The final conversion of the strip problem (weight `(5+2α)/α`): the vocabulary

This is the `VT` (weight `(5+2α)/α`) companion of `IR/finalConvertDefs.lean` (which handles the
weight `(5-α)/α`).  The weak formulation of `bslOp α Ψ = F` lives on the strip
`stripE = {0 < θ < π/2}` of `E2` in the `(s,θ)`-coordinates `s = (log z)/α`, and its unknown
`Ws α Ψ = wt α · Ψ(e^{αs},θ)` agrees a.e. (for `volume.restrict stripE`) with a `C^∞` function
`Φ : E2 → ℂ`.  The conclusion of `VT.finalTransport` is an honest `C^∞` representative of `Ψ`
on the *open quadrant* `Q0 = (0,∞) × (0,π/2)`.

Everything here is the definitional/algebraic preparation; the two substantial steps live in
`VT/SmoothOpenPhiPrimeV.lean` (`SmoothOpen (PhiPrimeV α Φ)`) and `VT/AeEqPhiPrimeV.lean`
(the a.e. identity), and are assembled in `VT/finalTransport.lean`.

The map `coords : ℝ × ℝ → E2` plays the role of the identification `ℝ × ℝ ≃ E2`
(it is a measure-preserving measurable embedding, `VT/Basic.lean`).
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Submission.Work.EllipticEst.InteriorRegularity.VT.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false

/-! ## The substitution and the candidate representative -/

/-- The `s`-coordinate `(log z)/α` of the substitution `z = e^{αs}`. -/
def sigmV (α : ℝ) (p : ℝ × ℝ) : ℝ := Real.log p.1 / α

/-- The inverse substitution `(z,θ) ↦ (s,θ) = ((log z)/α, θ)` as a point of `E2`. -/
def PhiInvV (α : ℝ) (p : ℝ × ℝ) : E2 := coords (sigmV α p) p.2

/-- The candidate smooth representative of `Ψ` on the open quadrant, read off from `Φ`: it is
`Φ` at the inverse substitution divided by the weight factor `wt` of the strip model, namely
`α e^{((5+2α)/α)·log z} cos θ`.  (The value at `z ≤ 0` is irrelevant and set to `0`.) -/
def PhiPrimeV (α : ℝ) (Φ : E2 → ℂ) : ℝ → ℝ → ℝ :=
  fun z θ => if 0 < z then
    (Φ (PhiInvV α (z, θ))).re
      / (α * Real.exp (((5 + 2 * α) / α) * Real.log z) * Real.cos θ)
  else 0

/-- The substitution `(s,θ) ↦ (e^{αs},θ)` of the half-strip onto the quadrant. -/
def TsubV (α : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (Real.exp (α * p.1), p.2)

/-- The half-strip `ℝ × (0,π/2)` in the `(s,θ)`-coordinates, i.e. the pre-image of `stripE`
under `coords`, resp. the image of the quadrant `Q0` under `(z,θ) ↦ ((log z)/α, θ)`. -/
def AsigV : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

/-! ## Elementary facts about the substitution -/

lemma mem_AsigV {p : ℝ × ℝ} : p ∈ AsigV ↔ 0 < p.2 ∧ p.2 < Real.pi / 2 := by
  simp [AsigV]

lemma coords_preimage_stripE :
    (fun p : ℝ × ℝ => coords p.1 p.2) ⁻¹' stripE = AsigV := by
  ext p
  simp only [Set.mem_preimage, mem_AsigV, stripE, Set.mem_ofPred_eq, coords_one, Set.mem_Ioo]

lemma PhiInvV_mem_stripE {α : ℝ} {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    PhiInvV α p ∈ stripE := by
  rw [Work.FTS.EllipticEst.mem_Q0] at hp
  simp only [stripE, PhiInvV]
  exact hp.2

lemma PhiInvV_exp {α : ℝ} (hα : α ≠ 0) (q : ℝ × ℝ) :
    PhiInvV α (Real.exp (α * q.1), q.2) = coords q.1 q.2 := by
  have h : sigmV α (Real.exp (α * q.1), q.2) = q.1 := by
    show Real.log (Real.exp (α * q.1)) / α = q.1
    rw [Real.log_exp, mul_div_cancel_left₀ q.1 hα]
  rw [PhiInvV, h]

lemma TsubV_mem_Q0 {α : ℝ} {q : ℝ × ℝ} (hq : q ∈ AsigV) :
    TsubV α q ∈ Work.FTS.EllipticEst.Q0 := by
  have hq' : 0 < q.2 ∧ q.2 < Real.pi / 2 := mem_AsigV.mp hq
  rw [Work.FTS.EllipticEst.mem_Q0]
  exact ⟨Real.exp_pos _, hq'.1, hq'.2⟩

/-- The substitution `(s,θ) ↦ (e^{αs},θ)` is differentiable everywhere. -/
lemma differentiable_TsubV (α : ℝ) : Differentiable ℝ (TsubV α) :=
  (Differentiable.exp (differentiable_fst.const_mul α)).prodMk differentiable_snd

/-! ## The weight factor at the inverse substitution -/

/-- The weight `wt α` at the inverted substitution, in the `exp`-form which exhibits the
smoothness in `z`. -/
lemma wt_PhiInvV_eq {α : ℝ} (hα : 0 < α) {z θ : ℝ} :
    wt α (PhiInvV α (z, θ))
      = α * Real.exp (((5 + 2 * α) / α) * Real.log z) * Real.cos θ := by
  show wt α (coords (Real.log z / α) θ)
      = α * Real.exp (((5 + 2 * α) / α) * Real.log z) * Real.cos θ
  rw [wt_coords hα.ne' (Real.log z / α) θ]
  rw [show (5 + 2 * α) * (Real.log z / α) = ((5 + 2 * α) / α) * Real.log z from by
    rw [div_mul_eq_mul_div, mul_div_assoc]]

lemma wt_pos_of_PhiInvV {α : ℝ} (hα : 0 < α) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < wt α (PhiInvV α (z, θ)) := by
  rw [wt_PhiInvV_eq hα]
  exact mul_pos (mul_pos hα (Real.exp_pos _))
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)

/-- The candidate representative, written with the weight factor `wt` as denominator. -/
lemma PhiPrimeV_eq_div {α : ℝ} (hα : 0 < α) {Φ : E2 → ℂ} {z θ : ℝ} (hz : 0 < z) :
    PhiPrimeV α Φ z θ = (Φ (PhiInvV α (z, θ))).re / wt α (PhiInvV α (z, θ)) := by
  simp only [PhiPrimeV, ite_eq_left hz]
  rw [wt_PhiInvV_eq hα]

/-- The candidate representative, evaluated at the exponential substitution. -/
lemma PhiPrimeV_exp {α : ℝ} (hα : α ≠ 0) {Φ : E2 → ℂ} (q : ℝ × ℝ) :
    PhiPrimeV α Φ (Real.exp (α * q.1)) q.2
      = (Φ (coords q.1 q.2)).re
          / (α * Real.exp ((5 + 2 * α) * q.1) * Real.cos q.2) := by
  simp only [PhiPrimeV, ite_eq_left (Real.exp_pos (α * q.1)), PhiInvV_exp hα, Real.log_exp]
  rw [show (5 + 2 * α) / α * (α * q.1) = (5 + 2 * α) * q.1 from by
    rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ q.1 hα]]

/-- The transported unknown `Ws α Ψ`, read at a point `coords s θ` of the strip coordinates. -/
@[simp] lemma Ws_coords (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (s θ : ℝ) :
    Ws α Ψ (coords s θ) = ((wt α (coords s θ) * Ψ (Real.exp (α * s)) θ : ℝ) : ℂ) := by
  simp [Ws, coords_zero, coords_one]

/-! ## Smoothness of the coordinate map -/

theorem contDiff_coords {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun p : ℝ × ℝ => coords p.1 p.2) := by
  have h : (fun p : ℝ × ℝ => coords p.1 p.2) =
      fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1 := by
    funext p
    ext i
    fin_cases i <;> simp [coords, e0, e1]
  rw [h]
  exact (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)

end Work.EllipticEst.InteriorRegularity.VT
