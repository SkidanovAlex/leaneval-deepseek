/-
# `Work.FTS.BSIdent.Defs` — the vocabulary of the Biot–Savart identification

This is the entry point of the subproject `Submission/Work/FTS/BSIdent/`, which owns **audit
§5 item 4** of `Submission/Work/FTS/FTS_PHYS_BRIDGE.md`: the identification, on the *open* set
`Uax = {x₃ ≠ 0, r ≠ 0}`, of the reconstructed physical velocity with the stream-function field of
the fake-time solution,

  `physVel (−physOmega α A B g C) x t = Cyl.psiField (fun r z => merPsi α A B Φ C r z t) x`
  for `t ∈ (0,T)`, `x ∈ Uax`,

i.e. the statement `hid` of `blowupAtTop_of_regPkg'`.

## The mathematical content of the identification

The physical vorticity of the dynamic rescaling is the swirl field

  `physOmega α A B g C x t = A(τ(t))⁻¹ · F(ρ(x)^{3α}/B(τ(t)), θ(x)) · e_θ(x)`,   `τ = clockInv C`

(`Work.FTS.Physical.physOmega`, `merProfile`).  Two facts pin the stream function of this field:

* **the sign** (`FTS_PHYS_BRIDGE.md` correction 1, `Physical/SignConvention.lean`): the workspace
  curl identity for a swirl field is
  `vorticity (psiField (ρ²Φ(ρ^p,θ))) = −(bslOp p Φ (ρ^p,θ)) • e_θ`, so the field of vorticity
  `+F e_θ` is the stream-function field of the *negated* stream function.  The design therefore
  takes the physical vorticity to be `ω := −physOmega` (the negated field), so that the stream
  function of `ω` is `+ρ²A⁻¹Φ(ρ^p/B, θ)`;
* **the elliptic law**: `ψ = ρ²A⁻¹Φ(ρ^p/B,θ)` has vorticity `−A⁻¹ · bslOp p Φ (ρ^p/B, θ) e_θ`,
  which equals `−physOmega` exactly when `bslOp p Φ (w,θ) = F(w,θ)`, i.e. when `Φ` solves the
  paper's (PolarBSL) with source the full profile `F = F_* + g` — the law `Work.Elliptic.IsBslSol`
  (in the *self-similar* variable `z = ρ^p/B`; the `B`-rescaling is a symmetry of `bslOp`, proved
  in `Work.R1G3.bslOp_scale`).

Consequently the ansatz field `v := psiField (merPsi … · t)` has vorticity exactly `ω`, and the
identification `BS ω = v` follows from the inverse Biot–Savart law (`Work.LWP.BiotSavartInverse`)
as soon as `v` lies in the class of that law (C¹, divergence-free, integrable vorticity, decay).

## The objects defined here

* `Uax` — the domain of the identification: off the axis and off the plane `x₃ = 0` (the two
  measure-zero sets on which the polar description degenerates);
* `PhiOdd` — the **odd extension in `θ`** of the self-similar stream function `Φ(·,·,τ)`, i.e.
  `θ ↦ if 0 ≤ θ then Φ θ else −Φ(−θ)`.  This is the function that makes the ansatz field odd and
  makes the identity hold on both signs of `x₃` (the physical vorticity profile `profile p g` of
  `Work.ConstructionInstance` is *by definition* the odd extension of `F_* + g`); the hat in the
  design's `Φ̂` is exactly this extension;
* `ssPsi` — the self-similar stream function at fake time `τ`, `w θ ↦ A(τ)⁻¹·Φ̂(w,θ,τ)`;
* `merPsi` — the design's meridian stream function `(r,z) ↦ ρ(r,z)²·A(τ)⁻¹·Φ̂(ρ(r,z)^p/B(τ),θ,τ)`,
  with `p = 3α` (`Work.FTS.Regularity.pExp`) and `τ = clockInv C t`.

Everything else of the chapter builds on these; nothing of the fixed interfaces
(`ChallengeDeps`, `Work.Cyl`, `Work.FTS.Physical`, `Work.FTS.Regularity`) is redefined.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.div_psiField
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Physical.Meridian

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology

namespace Work.FTS.BSIdent

set_option autoImplicit false

/-- `ℝ³`, definitionally `Work.Cyl.R3`, `Work.LWP.R3` and `Work.FTS.Physical.R3`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- A family of self-similar profiles `(z,θ,τ) ↦ Φ z θ τ`. -/
abbrev Fam : Type := ℝ → ℝ → ℝ → ℝ

/-! ## The domain `Uax` of the identification -/

/-- **The domain of the identification**: the complement of the axis `r = 0` and of the plane
`x₃ = 0`.  On it the polar coordinates `(ρ,θ)` are differentiable, `θ ≠ 0` (so the odd extension
of the profile is in its smooth branch) and `ρ > 0` (so `z = ρ^p/B > 0` lies in the open quadrant
of the elliptic law). -/
def Uax : Set R3 := {x | x 2 ≠ 0 ∧ x 0 ^ 2 + x 1 ^ 2 ≠ 0}

theorem mem_Uax {x : R3} (h : x ∈ Uax) : x 2 ≠ 0 ∧ x 0 ^ 2 + x 1 ^ 2 ≠ 0 := h

/-- The polar radius is positive on `Uax`. -/
theorem radial_pos_of_mem_Uax {x : R3} (h : x ∈ Uax) : 0 < Work.Cyl.radial x := by
  rw [Work.Cyl.radial_pos_iff]
  by_contra hcon
  push_neg at hcon
  exact h.2 (by rw [hcon.1, hcon.2]; norm_num)

/-- The axial coordinate is nonzero on `Uax`. -/
theorem axial_ne_zero_of_mem_Uax {x : R3} (h : x ∈ Uax) : Work.Cyl.axial x ≠ 0 := h.1

/-- On `Uax`, `θ(x) ≠ 0`. -/
theorem theta_ne_zero_of_mem_Uax {x : R3} (h : x ∈ Uax) : Work.Cyl.theta x ≠ 0 := by
  have hr : 0 < Work.Cyl.radial x := radial_pos_of_mem_Uax h
  have hdiv : Work.Cyl.axial x / Work.Cyl.radial x ≠ 0 := div_ne_zero h.1 (ne_of_gt hr)
  intro hθ
  exact hdiv (Real.arctan_eq_zero_iff.mp hθ)

/-- `Uax` avoids the axis. -/
theorem radial_ne_zero_of_mem_Uax {x : R3} (h : x ∈ Uax) : Work.Cyl.radial x ≠ 0 :=
  ne_of_gt (radial_pos_of_mem_Uax h)

/-- On `Uax` the polar radius `ρ(x) = ‖x‖` is positive. -/
theorem rho_pos_of_mem_Uax {x : R3} (h : x ∈ Uax) : 0 < Work.Cyl.rho x := by
  rw [Work.Cyl.rho, Real.sqrt_pos]
  have := radial_pos_of_mem_Uax h
  have hsq := Work.Cyl.radial_sq x
  nlinarith [sq_nonneg (Work.Cyl.axial x)]

/-- `Uax` is measurable. -/
theorem measurableSet_Uax : MeasurableSet Uax := by
  have h1 : MeasurableSet ((fun x : R3 => x 2) ⁻¹' ({0} : Set ℝ)) :=
    MeasurableSet.preimage (measurableSet_singleton 0) (by fun_prop)
  have h2 : MeasurableSet ((fun x : R3 => x 0 ^ 2 + x 1 ^ 2) ⁻¹' ({0} : Set ℝ)) :=
    MeasurableSet.preimage (measurableSet_singleton 0) (by fun_prop)
  have hU : Uax = ((fun x : R3 => x 2) ⁻¹' ({0} : Set ℝ))ᶜ ∩
      ((fun x : R3 => x 0 ^ 2 + x 1 ^ 2) ⁻¹' ({0} : Set ℝ))ᶜ := by
    ext x; simp [Uax]
  rw [hU]
  exact h1.compl.inter h2.compl

/-- **Every coordinate hyperplane of `ℝ³` is Lebesgue-null.** -/
theorem volume_coord_eq_zero (i : Fin 3) (c : ℝ) :
    volume {x : R3 | x i = c} = 0 := by
  have hmap : Measure.map (WithLp.toLp 2 : (Fin 3 → ℝ) → R3) volume = volume :=
    (PiLp.volume_preserving_toLp (Fin 3)).map_eq
  rw [← hmap, MeasureTheory.Measure.map_apply (by fun_prop) (by measurability)]
  have h : (WithLp.toLp 2 : (Fin 3 → ℝ) → R3) ⁻¹' {x : R3 | x i = c}
      = {v : Fin 3 → ℝ | v i = c} := by
    ext v; simp
  rw [h, MeasureTheory.volume_pi]
  exact MeasureTheory.Measure.pi_hyperplane (fun _ : Fin 3 => (volume : Measure ℝ)) i c

/-- The complement of `Uax` (the axis together with the plane `x₃ = 0`) is Lebesgue-null. -/
theorem volume_Uax_compl : volume (Uaxᶜ : Set R3) = 0 := by
  have hsub : (Uaxᶜ : Set R3) ⊆ {x : R3 | x 2 = 0} ∪ {x : R3 | x 0 = 0} := by
    intro x hx
    by_cases h1 : x 2 = 0
    · exact Or.inl h1
    · right
      have h2 : x 0 ^ 2 + x 1 ^ 2 = 0 := not_not.mp (fun hc => hx ⟨h1, hc⟩)
      have hA : x 0 ^ 2 = 0 := by nlinarith [sq_nonneg (x 1)]
      simpa using (sq_eq_zero_iff.mp hA)
  exact measure_mono_null hsub
    (measure_union_null (volume_coord_eq_zero 2 0) (volume_coord_eq_zero 0 0))

/-- Almost every point of `ℝ³` lies in `Uax`. -/
theorem ae_mem_Uax : ∀ᵐ x ∂(volume : Measure R3), x ∈ Uax := by
  rw [MeasureTheory.ae_iff]
  exact volume_Uax_compl

/-! ## The polar dictionary at a point -/

/-- `ρ` in the point coordinates is `rhoP` in the meridian coordinates. -/
theorem rhoP_radial_axial (x : R3) :
    Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.rho x := by
  rw [Work.Cyl.rhoP, Work.Cyl.rho, Work.Cyl.radial_sq]

/-- `θ` is `thetaP` in the meridian coordinates. -/
theorem thetaP_radial_axial (x : R3) :
    Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.theta x := rfl

/-! ## The odd extension in `θ` -/

/-- **The odd extension in `θ`** of a family `Φ`: `Φ̂(z,θ,τ) = Φ(z,θ,τ)` for `θ ≥ 0` and
`Φ̂(z,θ,τ) = −Φ(z,−θ,τ)` for `θ < 0`.  This is the extension for which the physical vorticity
profile of `Work.ConstructionInstance` (`profile p g`, the odd extension of `F_* + g`) is the
source, and it is the `Φ̂` of the design's `merPsi`. -/
def PhiOdd (Φ : Fam) : Fam := fun z θ τ => if 0 ≤ θ then Φ z θ τ else -(Φ z (-θ) τ)

theorem PhiOdd_of_nonneg {Φ : Fam} {z θ τ : ℝ} (h : 0 ≤ θ) :
    PhiOdd Φ z θ τ = Φ z θ τ := ite_eq_left h

theorem PhiOdd_of_neg {Φ : Fam} {z θ τ : ℝ} (h : ¬ 0 ≤ θ) :
    PhiOdd Φ z θ τ = -(Φ z (-θ) τ) := ite_eq_right h

/-- **The odd extension is odd in `θ`.** -/
theorem PhiOdd_neg_theta {Φ : Fam} (h0 : ∀ z τ, Φ z 0 τ = 0) (z θ τ : ℝ) :
    PhiOdd Φ z (-θ) τ = -(PhiOdd Φ z θ τ) := by
  by_cases h : 0 ≤ θ
  · by_cases h' : 0 ≤ -θ
    · have hθ0 : θ = 0 := le_antisymm (by linarith) h
      subst hθ0
      simp [PhiOdd_of_nonneg le_rfl, h0 z τ]
    · rw [PhiOdd_of_neg h', PhiOdd_of_nonneg h, neg_neg]
  · have hpos : 0 ≤ -θ := by linarith
    rw [PhiOdd_of_neg h, PhiOdd_of_nonneg hpos, neg_neg]

/-- At `θ = 0` the odd extension vanishes as soon as `Φ` does. -/
theorem PhiOdd_zero_theta {Φ : Fam} (h : ∀ z τ, Φ z 0 τ = 0) (z τ : ℝ) :
    PhiOdd Φ z 0 τ = 0 := by
  rw [PhiOdd_of_nonneg le_rfl]; exact h z τ

/-! ## The self-similar and the meridian stream function -/

/-- **The self-similar stream function** at fake time `τ`: `w θ ↦ A(τ)⁻¹ · Φ̂(w,θ,τ)`.  This is
the function whose `bslOp p` is (up to the odd extension) the profile `F(·,·,τ)`, by the elliptic
law. -/
noncomputable def ssPsi (A : ℝ → ℝ) (Φ : Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun w θ => (A τ)⁻¹ * PhiOdd Φ w θ τ

theorem ssPsi_apply (A : ℝ → ℝ) (Φ : Fam) (τ w θ : ℝ) :
    ssPsi A Φ τ w θ = (A τ)⁻¹ * PhiOdd Φ w θ τ := rfl

/-- **The meridian stream function of the reconstruction** (the design's `merPsi`):

  `merPsi α A B Φ C r z t = ρ(r,z)² · A(τ(t))⁻¹ · Φ̂(ρ(r,z)^{3α}/B(τ(t)), θ(r,z), τ(t))`,

with `τ(t) = clockInv C t`, `ρ(r,z) = √(r²+z²)`, `θ(r,z) = arctan(z/r)` and `Φ̂` the odd
extension in `θ` of `Φ`.  It is the stream function of the reconstructed velocity field
`psiField (merPsi … · t)`: `vorticity (psiField (merPsi … · t)) = −physOmega α A B g C · t` (this
is `Work.FTS.BSIdent.vorticity_psiField_merPsi`), whence `physVel (−physOmega …) = psiField …`
by Biot–Savart inversion. -/
noncomputable def merPsi (α : ℝ) (A B : ℝ → ℝ) (Φ : Fam) (C : Physical.PhysClock) :
    ℝ → ℝ → ℝ → ℝ :=
  fun r z t => Work.Cyl.rhoP r z ^ 2 * (A (Physical.clockInv C t))⁻¹
    * PhiOdd Φ (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z) (Physical.clockInv C t)

theorem merPsi_apply (α : ℝ) (A B : ℝ → ℝ) (Φ : Fam) (C : Physical.PhysClock) (r z t : ℝ) :
    merPsi α A B Φ C r z t = Work.Cyl.rhoP r z ^ 2 * (A (Physical.clockInv C t))⁻¹
      * PhiOdd Φ (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
          (Work.Cyl.thetaP r z) (Physical.clockInv C t) := rfl

/-- The meridian stream function is `ρ²` times the self-similar stream function evaluated at
`w = ρ^p/B(τ)`. -/
theorem merPsi_eq_rhoP_sq_mul_ssPsi (α : ℝ) (A B : ℝ → ℝ) (Φ : Fam) (C : Physical.PhysClock)
    (r z t : ℝ) :
    merPsi α A B Φ C r z t = Work.Cyl.rhoP r z ^ 2 *
      ssPsi A Φ (Physical.clockInv C t)
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z) := by
  rw [merPsi_apply, ssPsi_apply]
  ring

/-- **On the branch `θ > 0` the odd extension is the identity**: the meridian stream function is
the plain `ρ²·A⁻¹·Φ(ρ^p/B, θ)` there.  This is the form a caller needs to compare `merPsi` with the
fake-time stream function `Φ` itself. -/
theorem merPsi_apply_of_theta_pos (α : ℝ) (A B : ℝ → ℝ) (Φ : Fam) (C : Physical.PhysClock)
    {r z t : ℝ} (hθ : 0 < Work.Cyl.thetaP r z) :
    merPsi α A B Φ C r z t = Work.Cyl.rhoP r z ^ 2 * (A (Physical.clockInv C t))⁻¹
      * Φ (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
          (Work.Cyl.thetaP r z) (Physical.clockInv C t) := by
  rw [merPsi_apply, PhiOdd_of_nonneg (le_of_lt hθ)]

/-- **The meridian stream function at a point, in the point's polar coordinates.** -/
theorem merPsi_at (α : ℝ) (A B : ℝ → ℝ) (Φ : Fam) (C : Physical.PhysClock) (x : R3)
    (t : ℝ) :
    merPsi α A B Φ C (Work.Cyl.radial x) (Work.Cyl.axial x) t
      = Work.Cyl.rho x ^ 2 * (A (Physical.clockInv C t))⁻¹
        * PhiOdd Φ (Work.Cyl.rho x ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
            (Work.Cyl.theta x) (Physical.clockInv C t) := by
  rw [merPsi_apply, rhoP_radial_axial, thetaP_radial_axial]

end Work.FTS.BSIdent
