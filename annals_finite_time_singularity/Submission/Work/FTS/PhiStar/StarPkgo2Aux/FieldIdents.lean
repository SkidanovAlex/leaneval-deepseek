/-
# The field identities `Ŷ ↔ ℛ, 𝒱, 𝒰` of `StarPkgo2Aux`

`Work.FTS.PhiStar.CoreAux.FieldsDefs` defines the eleven fields of `StarPkgo2` as combinations of
the single rescaled quantity `Ŷ = ((z+1)/z)·Φ̃_*/sin 2θ` (`EH`, `EV`, `EVz`, `EU`, `EUz`, `EPU`),
and the transport coefficients `ℛ, 𝒱, 𝒰` of `Work.Construction` are computed on `Φ̃_* = sin 2θ · Φ`
with `Φ = Φ̃_*/sin 2θ` (`Work.FTS.H2.StarPkg.Rop_sin_two_mul`, `Vop_sin_two_mul`,
`Uop_sin_two_mul`).  This file is the bridge between the two normal forms: for an *arbitrary*
pair `(Ψ, Y)` linked on the open quadrant `Q0` by `Y = ((z+1)/z)·Ψ/sin 2θ`, the six identities

* `(z+1)/z·ℛ(Ψ) = EH(Y)`,  `𝒱(Ψ) = EV(Y)`,  `(z+1)/z·𝒱(Ψ) = EVz(Y)`,
* `𝒰(Ψ)/sin 2θ = EU(Y)`,  `(z+1)/z·(𝒰(Ψ)/sin 2θ) = EUz(Y)`,  `∂_θ𝒰(Ψ) = EPU(Y)`

hold on `Q0`.  The statements are pointwise, so all the derivative transfers are performed with
`AgreeOnQ` (agreement on the open quadrant) and its `pz`/`pth` projections: `Y` is compared with
the explicit function `(z+1)/z·(Ψ/sin 2θ)`, and `Ψ` with `sin 2θ·(Ψ/sin 2θ)`, both on `Q0`.

The point `(z,θ)` is kept generic; only `SmoothOpen Ψ` (so that the `θ`-slices of `Ψ` and of
`∂_zΨ` are differentiable at interior angles and Clairaut holds) and `sin(2θ) ≠ 0` on `Q0` are
used.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs
import Submission.Work.FTS.H2.StarPkg.Subst
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.StarPkgo2Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary derivative facts -/

/-- `∂_θ sin 2θ = 2 cos 2θ`. -/
private lemma hasDerivAt_s2 (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Work.Construction.s2 θ') (2 * Real.cos (2 * θ)) θ := by
  have h2' : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h2'
  have h' : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    convert h using 1
    ring
  show HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ
  exact h'

/-- `sin 2θ ≠ 0` for an interior angle. -/
private lemma s2_ne_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Construction.s2 θ ≠ 0 := by
  have hp : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  simpa [Work.Construction.s2] using ne_of_gt hp

/-- `∂_z (Ψ/sin 2θ) = ∂_zΨ/sin 2θ`. -/
private lemma pz_div_s2 (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ
      = Work.Spaces.pz Ψ z θ / Work.Construction.s2 θ := by
  show deriv (fun z' : ℝ => Ψ z' θ / Work.Construction.s2 θ) z
      = deriv (fun z' : ℝ => Ψ z' θ) z / Work.Construction.s2 θ
  have h : (fun z' : ℝ => Ψ z' θ / Work.Construction.s2 θ)
      = fun z' : ℝ => (Work.Construction.s2 θ)⁻¹ * Ψ z' θ := by
    funext z'; rw [div_eq_mul_inv, mul_comm]
  rw [h, deriv_const_mul_field, div_eq_mul_inv]
  exact mul_comm _ _

/-- `∂_θ (Ψ/sin 2θ) = (∂_θΨ·sin 2θ − Ψ·2cos 2θ)/sin 2θ²`. -/
private lemma pth_div_s2 {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hd : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ)
    (hs2 : Work.Construction.s2 θ ≠ 0) :
    Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ
      = (Work.Spaces.pth Ψ z θ * Work.Construction.s2 θ
          - Ψ z θ * (2 * Real.cos (2 * θ))) / (Work.Construction.s2 θ) ^ 2 := by
  have h := hd.hasDerivAt.div (hasDerivAt_s2 θ) hs2
  show deriv ((fun θ' : ℝ => Ψ z θ') / (fun θ' : ℝ => Work.Construction.s2 θ')) θ = _
  exact h.deriv

/-- `∂_z ((z+1)/z) = -1/z²`. -/
private lemma hasDerivAt_zfac (z : ℝ) (hz : z ≠ 0) :
    HasDerivAt (fun z' : ℝ => (z' + 1) / z') (-1 / z ^ 2) z := by
  have h0 := ((hasDerivAt_id z).add_const 1).div (hasDerivAt_id z) hz
  have h1 : HasDerivAt (fun z' : ℝ => (z' + 1) / z')
      ((1 * z - (z + 1) * 1) / z ^ 2) z := h0
  have hd : (1 * z - (z + 1) * 1) / z ^ 2 = -1 / z ^ 2 := by ring
  simpa only [hd] using h1

/-- `∂_z ((z+1)/z·g) = -g/z² + ((z+1)/z)·∂_zg`. -/
private lemma pz_zfac_mul {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : z ≠ 0)
    (hd : DifferentiableAt ℝ (fun z' => g z' θ) z) :
    Work.Spaces.pz (fun z θ => (z + 1) / z * g z θ) z θ
      = -g z θ / z ^ 2 + (z + 1) / z * Work.Spaces.pz g z θ := by
  have h := (hasDerivAt_zfac z hz).mul hd.hasDerivAt
  show deriv ((fun z' : ℝ => (z' + 1) / z') * (fun z' : ℝ => g z' θ)) z
      = -g z θ / z ^ 2 + (z + 1) / z * deriv (fun z' => g z' θ) z
  rw [h.deriv]
  ring

/-- `∂_θ ((z+1)/z·g) = ((z+1)/z)·∂_θg`. -/
private lemma pth_zfac_mul (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z θ => (z + 1) / z * g z θ) z θ
      = (z + 1) / z * Work.Spaces.pth g z θ := by
  show deriv (fun θ' : ℝ => (z + 1) / z * g z θ') θ = (z + 1) / z * deriv (fun θ' => g z θ') θ
  rw [deriv_const_mul_field]

/-! ## Congruence of `∂_z`, `∂_θ` of `Ψ` with `sin 2θ·(Ψ/sin 2θ)` -/

/-- On `Q0` the `z`-derivative of `Ψ` and of `sin 2θ·(Ψ/sin 2θ)` agree. -/
private lemma pz_mul_s2_div (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ} (hs2 : Work.Construction.s2 θ ≠ 0) :
    Work.Spaces.pz Ψ z θ
      = Work.Spaces.pz (fun z θ => Work.Construction.s2 θ * (Ψ z θ / Work.Construction.s2 θ))
        z θ := by
  refine Work.FTS.EllipticEst.pz_congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun z' => (mul_div_cancel₀ _ hs2).symm

/-- On `Q0` the `θ`-derivative of `Ψ` and of `sin 2θ·(Ψ/sin 2θ)` agree. -/
private lemma pth_mul_s2_div (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ} (hs2 : Work.Construction.s2 θ ≠ 0) :
    Work.Spaces.pth Ψ z θ
      = Work.Spaces.pth (fun z θ => Work.Construction.s2 θ * (Ψ z θ / Work.Construction.s2 θ))
        z θ := by
  refine Work.FTS.EllipticEst.pth_congr_of_eventuallyEq ?_
  have hcont : ContinuousAt (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    have h : (fun θ' : ℝ => Work.Construction.s2 θ') = fun θ' : ℝ => Real.sin (2 * θ') := rfl
    rw [h]; fun_prop
  filter_upwards [hcont.eventually_ne hs2] with θ' hne
  exact (mul_div_cancel₀ _ hne).symm

/-- `ℛ(Ψ) = ℛ(sin 2θ·(Ψ/sin 2θ))` on `Q0`. -/
private lemma Rop_AgreeOnQ (α : ℝ) (Ψ : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.AgreeOnQ (Work.Construction.Rop α Ψ)
      (Work.Construction.Rop α
        (fun z θ => Work.Construction.s2 θ * (Ψ z θ / Work.Construction.s2 θ))) := by
  intro z θ hz hθ hlt
  have hs2 : Work.Construction.s2 θ ≠ 0 := s2_ne_of_mem_Ioo ⟨hθ, hlt⟩
  have hval : Ψ z θ = Work.Construction.s2 θ * (Ψ z θ / Work.Construction.s2 θ) :=
    (mul_div_cancel₀ _ hs2).symm
  simp only [Work.Construction.Rop]
  conv_lhs => rw [hval, pz_mul_s2_div Ψ hs2, pth_mul_s2_div Ψ hs2]

/-- `𝒱(Ψ) = 𝒱(sin 2θ·(Ψ/sin 2θ))` on `Q0`. -/
private lemma Vop_AgreeOnQ (Ψ : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.AgreeOnQ (Work.Construction.Vop Ψ)
      (Work.Construction.Vop
        (fun z θ => Work.Construction.s2 θ * (Ψ z θ / Work.Construction.s2 θ))) := by
  intro z θ hz hθ hlt
  have hs2 : Work.Construction.s2 θ ≠ 0 := s2_ne_of_mem_Ioo ⟨hθ, hlt⟩
  have hval : Ψ z θ = Work.Construction.s2 θ * (Ψ z θ / Work.Construction.s2 θ) :=
    (mul_div_cancel₀ _ hs2).symm
  simp only [Work.Construction.Vop]
  conv_lhs => rw [hval, pth_mul_s2_div Ψ hs2]

/-- `𝒰(Ψ) = 𝒰(sin 2θ·(Ψ/sin 2θ))` on `Q0`. -/
private lemma Uop_AgreeOnQ (α : ℝ) (Ψ : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.AgreeOnQ (Work.Construction.Uop α Ψ)
      (Work.Construction.Uop α
        (fun z θ => Work.Construction.s2 θ * (Ψ z θ / Work.Construction.s2 θ))) := by
  intro z θ hz hθ hlt
  have hs2 : Work.Construction.s2 θ ≠ 0 := s2_ne_of_mem_Ioo ⟨hθ, hlt⟩
  have hval : Ψ z θ = Work.Construction.s2 θ * (Ψ z θ / Work.Construction.s2 θ) :=
    (mul_div_cancel₀ _ hs2).symm
  simp only [Work.Construction.Uop]
  conv_lhs => rw [hval, pz_mul_s2_div Ψ hs2]

/-! ## The derivatives of `Y = ((z+1)/z)·(Ψ/sin 2θ)` in terms of `Φ = Ψ/sin 2θ` -/

/-- `∂_zY = -(Ψ/sin 2θ)/z² + ((z+1)/z)·∂_z(Ψ/sin 2θ)`. -/
private lemma pz_AgreeOnQ_zfac {Ψ Y : ℝ → ℝ → ℝ}
    (hY : Work.FTS.EllipticEst.AgreeOnQ Y
      (fun z θ => (z + 1) / z * (Ψ z θ / Work.Construction.s2 θ)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hd : DifferentiableAt ℝ (fun z' => Ψ z' θ) z) :
    Work.Spaces.pz Y z θ
      = -(Ψ z θ / Work.Construction.s2 θ) / z ^ 2
        + (z + 1) / z * Work.Spaces.pz (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ := by
  rw [hY.pz z θ hz hθ.1 hθ.2]
  exact pz_zfac_mul (g := fun z θ => Ψ z θ / Work.Construction.s2 θ) (ne_of_gt hz)
    (hd.div_const _)

/-- `∂_θY = ((z+1)/z)·∂_θ(Ψ/sin 2θ)`. -/
private lemma pth_AgreeOnQ_zfac {Ψ Y : ℝ → ℝ → ℝ}
    (hY : Work.FTS.EllipticEst.AgreeOnQ Y
      (fun z θ => (z + 1) / z * (Ψ z θ / Work.Construction.s2 θ)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pth Y z θ
      = (z + 1) / z * Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ := by
  rw [hY.pth z θ hz hθ.1 hθ.2]
  exact pth_zfac_mul (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ

/-- `∂_z∂_θY = -∂_θ(Ψ/sin 2θ)/z² + ((z+1)/z)·∂_z∂_θ(Ψ/sin 2θ)`. -/
private lemma pz_pth_AgreeOnQ_zfac {Ψ Y : ℝ → ℝ → ℝ}
    (hY : Work.FTS.EllipticEst.AgreeOnQ Y
      (fun z θ => (z + 1) / z * (Ψ z θ / Work.Construction.s2 θ)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hd : DifferentiableAt ℝ
      (fun z' => Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z' θ) z) :
    Work.Spaces.pz (Work.Spaces.pth Y) z θ
      = -(Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ) / z ^ 2
        + (z + 1) / z
          * Work.Spaces.pz (Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ)) z θ := by
  have hpt : Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.pth Y)
      (fun z θ => (z + 1) / z
        * Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ) := by
    intro z' θ' hz' hθ' hlt'
    exact (hY.pth z' θ' hz' hθ' hlt').trans
      (pth_zfac_mul (fun z θ => Ψ z θ / Work.Construction.s2 θ) z' θ')
  rw [hpt.pz z θ hz hθ.1 hθ.2]
  exact pz_zfac_mul (g := fun z θ =>
      Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ) (ne_of_gt hz) hd

/-! ## The mixed derivative of `Φ = Ψ/sin 2θ` -/

/-- `∂_z((A·a − B·b)/a²) = (∂_zA·a − ∂_zB·b)/a²` for `a`, `b` functions of `θ` only. -/
private lemma pz_explicit_div {A B : ℝ → ℝ → ℝ} {ac bc : ℝ → ℝ} {z θ : ℝ}
    (hA : DifferentiableAt ℝ (fun z' => A z' θ) z)
    (hB : DifferentiableAt ℝ (fun z' => B z' θ) z) :
    Work.Spaces.pz (fun z θ => (A z θ * ac θ - B z θ * bc θ) / (ac θ) ^ 2) z θ
      = (Work.Spaces.pz A z θ * ac θ - Work.Spaces.pz B z θ * bc θ) / (ac θ) ^ 2 := by
  have h := (((hA.hasDerivAt).mul_const (ac θ)).sub ((hB.hasDerivAt).mul_const (bc θ))).div_const
    ((ac θ) ^ 2)
  exact h.deriv

/-- `∂_z∂_θ(Ψ/sin 2θ) = (∂_z∂_θΨ·sin 2θ − ∂_zΨ·2cos 2θ)/sin 2θ²`. -/
private lemma pz_pth_div_s2 {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pz (Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ)) z θ
      = (Work.Spaces.pz (Work.Spaces.pth Ψ) z θ * Work.Construction.s2 θ
          - Work.Spaces.pz Ψ z θ * (2 * Real.cos (2 * θ))) / (Work.Construction.s2 θ) ^ 2 := by
  have hpt : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ))
      (fun z θ => (Work.Spaces.pth Ψ z θ * Work.Construction.s2 θ
          - Ψ z θ * (2 * Real.cos (2 * θ))) / (Work.Construction.s2 θ) ^ 2) := by
    intro z' θ' hz' hθ' hlt'
    have hd : DifferentiableAt ℝ (fun θ'' => Ψ z' θ'') θ' :=
      ((hsm.curry_θ hz').differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds ⟨hθ', hlt'⟩)
    exact pth_div_s2 hd (s2_ne_of_mem_Ioo ⟨hθ', hlt'⟩)
  rw [hpt.pz z θ hz hθ.1 hθ.2]
  exact pz_explicit_div (A := Work.Spaces.pth Ψ) (B := Ψ) (ac := Work.Construction.s2)
    (bc := fun θ => 2 * Real.cos (2 * θ))
    ((hsm.pth).hasDerivAt_slice hθ hz).differentiableAt
    (hsm.hasDerivAt_slice hθ hz).differentiableAt

/-- The `z`-slice of `∂_θ(Ψ/sin 2θ)` is differentiable at an interior point. -/
private lemma diff_z_pth_div_s2 {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ
      (fun z' => Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z' θ) z := by
  have hev : (fun z' => Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => (Work.Spaces.pth Ψ z' θ * Work.Construction.s2 θ
          - Ψ z' θ * (2 * Real.cos (2 * θ))) / (Work.Construction.s2 θ) ^ 2) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact pth_div_s2 (((hsm.curry_θ hz').differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)) (s2_ne_of_mem_Ioo hθ)
  have hdA : DifferentiableAt ℝ (fun z' => Work.Spaces.pth Ψ z' θ) z :=
    ((hsm.pth).hasDerivAt_slice hθ hz).differentiableAt
  have hdB : DifferentiableAt ℝ (fun z' => Ψ z' θ) z :=
    (hsm.hasDerivAt_slice hθ hz).differentiableAt
  have hdex : DifferentiableAt ℝ (fun z' => (Work.Spaces.pth Ψ z' θ * Work.Construction.s2 θ
      - Ψ z' θ * (2 * Real.cos (2 * θ))) / (Work.Construction.s2 θ) ^ 2) z :=
    ((hdA.mul_const _).sub (hdB.mul_const _)).div_const _
  exact hdex.congr_of_eventuallyEq hev

/-! ## The six field identities -/

theorem FieldIdents (α : ℝ) (Ψ Y : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hY : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Y z θ = (z + 1) / z * (Ψ z θ / Work.Construction.s2 θ)) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.FTS.PhiStar.EH α Y z θ = (z + 1) / z * Work.Construction.Rop α Ψ z θ ∧
      Work.FTS.PhiStar.EV Y z θ = Work.Construction.Vop Ψ z θ ∧
      Work.FTS.PhiStar.EVz Y z θ = (z + 1) / z * Work.Construction.Vop Ψ z θ ∧
      Work.FTS.PhiStar.EU α Y z θ = Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ ∧
      Work.FTS.PhiStar.EUz α Y z θ
        = (z + 1) / z * (Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ) ∧
      Work.FTS.PhiStar.EPU α Y z θ = Work.Spaces.pth (Work.Construction.Uop α Ψ) z θ := by
  intro z θ hz
  obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hz
  have hzne : z ≠ 0 := ne_of_gt hz0
  have hz1ne : (1 : ℝ) + z ≠ 0 := by positivity
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hs2ne : Work.Construction.s2 θ ≠ 0 := s2_ne_of_mem_Ioo hθI
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  -- `Y` as an `AgreeOnQ`-statement
  have hAg : Work.FTS.EllipticEst.AgreeOnQ Y
      (fun z θ => (z + 1) / z * (Ψ z θ / Work.Construction.s2 θ)) :=
    fun z θ hz' hθ' hlt' => hY z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ', hlt'⟩)
  -- differentiability of the relevant slices
  have hdzΨ : DifferentiableAt ℝ (fun z' => Ψ z' θ) z :=
    (hsm.hasDerivAt_slice hθI hz0).differentiableAt
  have hdθΨ : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ :=
    ((hsm.curry_θ hz0).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθI)
  have hdθΦ : DifferentiableAt ℝ (fun θ' => Ψ z θ' / Work.Construction.s2 θ') θ :=
    hdθΨ.div (hasDerivAt_s2 θ).differentiableAt hs2ne
  -- the value of `Y` and its derivatives, in terms of `Φ = Ψ/sin 2θ`
  have hval : Y z θ = (z + 1) / z * (Ψ z θ / Work.Construction.s2 θ) := hY z θ hz
  have hpzY := pz_AgreeOnQ_zfac hAg hz0 hθI hdzΨ
  have hpthY := pth_AgreeOnQ_zfac hAg hz0 hθI
  have hpzpthY := pz_pth_AgreeOnQ_zfac hAg hz0 hθI (diff_z_pth_div_s2 hsm hz0 hθI)
  -- the derivatives of `Φ` in terms of `Ψ`
  have hpzΦ : Work.Spaces.pz (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ
      = Work.Spaces.pz Ψ z θ / Work.Construction.s2 θ := pz_div_s2 Ψ z θ
  have hpthΦ : Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ
      = (Work.Spaces.pth Ψ z θ * Work.Construction.s2 θ
          - Ψ z θ * (2 * Real.cos (2 * θ))) / (Work.Construction.s2 θ) ^ 2 :=
    pth_div_s2 hdθΨ hs2ne
  have hpzpthΦ : Work.Spaces.pz (Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ)) z θ
      = (Work.Spaces.pz (Work.Spaces.pth Ψ) z θ * Work.Construction.s2 θ
          - Work.Spaces.pz Ψ z θ * (2 * Real.cos (2 * θ))) / (Work.Construction.s2 θ) ^ 2 :=
    pz_pth_div_s2 hsm hz0 hθI
  -- the transport coefficients, in terms of `Φ`
  have hRop : Work.Construction.Rop α Ψ z θ
      = 2 * (Ψ z θ / Work.Construction.s2 θ)
        + 2 * α * Real.sin θ ^ 2
          * (z * Work.Spaces.pz (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ)
        + Work.Construction.s2 θ
          * Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ :=
    (Rop_AgreeOnQ α Ψ z θ hz0 hθ0 hθ1).trans
      (Work.FTS.H2.StarPkg.Rop_sin_two_mul α (fun z θ => Ψ z θ / Work.Construction.s2 θ)
        z θ hcos hdθΦ)
  have hVop : Work.Construction.Vop Ψ z θ
      = 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * (Ψ z θ / Work.Construction.s2 θ)
        + Work.Construction.s2 θ
          * Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ :=
    (Vop_AgreeOnQ Ψ z θ hz0 hθ0 hθ1).trans
      (Work.FTS.H2.StarPkg.Vop_sin_two_mul (fun z θ => Ψ z θ / Work.Construction.s2 θ)
        z θ hcos hdθΦ)
  have hUop : Work.Construction.Uop α Ψ z θ
      = -(Work.Construction.s2 θ
          * (3 * (Ψ z θ / Work.Construction.s2 θ)
            + α * (z * Work.Spaces.pz (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ))) :=
    (Uop_AgreeOnQ α Ψ z θ hz0 hθ0 hθ1).trans
      (Work.FTS.H2.StarPkg.Uop_sin_two_mul α (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ)
  -- `𝒰` and `∂_θ𝒰`
  have hEU : Work.FTS.PhiStar.EU α Y z θ
      = Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ := by
    rw [Work.FTS.PhiStar.EU, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk, hUop]
    rw [hval, hpzY, hpzΦ]
    field_simp; ring
  have hcd : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ) :=
    (hsm.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hz)
  have hdθpzΨ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz Ψ z θ') θ :=
    ((hsm.pz).curry_θ hz0).differentiableOn (by simp) |>.differentiableAt
      (isOpen_Ioo.mem_nhds hθI)
  have hpthUop : Work.Spaces.pth (Work.Construction.Uop α Ψ) z θ
      = -3 * Work.Spaces.pth Ψ z θ - α * z * Work.Spaces.pz (Work.Spaces.pth Ψ) z θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => Ψ z θ') (Work.Spaces.pth Ψ z θ) θ := hdθΨ.hasDerivAt
    have h2 : HasDerivAt (fun θ' : ℝ => Work.Spaces.pz Ψ z θ')
        (Work.Spaces.pth (Work.Spaces.pz Ψ) z θ) θ := hdθpzΨ.hasDerivAt
    have h3 : HasDerivAt (fun θ' : ℝ => -3 * Ψ z θ' - α * z * Work.Spaces.pz Ψ z θ')
        (-3 * Work.Spaces.pth Ψ z θ - α * z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ) θ :=
      (h1.const_mul (-3)).sub (h2.const_mul (α * z))
    have hcl : Work.Spaces.pth (Work.Spaces.pz Ψ) z θ
        = Work.Spaces.pz (Work.Spaces.pth Ψ) z θ := (Work.Spaces.pz_pth_comm hcd).symm
    show deriv (fun θ' : ℝ => -3 * Ψ z θ' - α * z * Work.Spaces.pz Ψ z θ') θ = _
    rw [h3.deriv, hcl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `(z+1)/z·ℛ(Ψ) = EH(Y)`
    rw [Work.FTS.PhiStar.EH, Work.FTS.PhiStar.Yblk, Work.FTS.PhiStar.Tblk, hRop]
    rw [hval, hpzY, hpthY]
    field_simp; ring
  · -- `𝒱(Ψ) = EV(Y)`
    rw [Work.FTS.PhiStar.EV, Work.FTS.PhiStar.EVz, Work.FTS.PhiStar.Tblk, hVop]
    rw [hval, hpthY]
    field_simp
  · -- `(z+1)/z·𝒱(Ψ) = EVz(Y)`
    rw [Work.FTS.PhiStar.EVz, Work.FTS.PhiStar.Tblk, hVop]
    rw [hval, hpthY]
    field_simp
  · -- `𝒰(Ψ)/sin 2θ = EU(Y)`
    exact hEU
  · -- `(z+1)/z·(𝒰(Ψ)/sin 2θ) = EUz(Y)`
    rw [Work.FTS.PhiStar.EUz, ← hEU, Work.FTS.PhiStar.EU]
    field_simp
  · -- `∂_θ𝒰(Ψ) = EPU(Y)`
    rw [Work.FTS.PhiStar.EPU, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk, hpthUop]
    rw [hval, hpzY, hpthY, hpzpthY]
    rw [hpzΦ, hpthΦ, hpzpthΦ]
    field_simp; ring

end Work.FTS.PhiStar.StarPkgo2Aux
