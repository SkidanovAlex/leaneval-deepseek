/-
# Row 19 — the algebraic infrastructure for `abs_DthIter_four_VsW_le`

This module collects the structural facts used by the proof of
`Work.FTS.Nonlinear.Pieces.RNP.row19.abs_DthIter_four_VsW_le` (the `(k = 1, j = 4)` slot of
`𝒱(Φ̃_*) = Vop (PhiTs α Φs)`, one order above the frozen `𝒲^{4,∞}`-field).

The starting point is the **pure algebra identity**

  `∂_θ 𝒰(Ψ) = -(2 𝒱(Ψ) + ℛ(Ψ) + α · D_z 𝒱(Ψ))`

for

  `𝒰(Ψ) = -3Ψ - α z ∂_zΨ`,   `𝒱(Ψ) = ∂_θΨ - tan θ · Ψ`,
  `ℛ(Ψ) = (2 sin θ · Ψ + α sin θ · z ∂_zΨ + cos θ · ∂_θΨ)/cos θ`,

which holds on the open quadrant (only Clairaut's theorem is needed, no differential equation).
Since `𝒱 = ℛ + tan θ · 𝒰` (i.e. `tan θ · 𝒰 = 𝒱 - ℛ`), the identity is equivalent to the more
familiar `∂_θ 𝒰 = tan θ · 𝒰 - 3𝒱 - D_z𝒱`; the displayed form is the one in which no `tan` occurs,
and it converts the (unknown) `θ`-derivative of `𝒱` into the fields that `StarPkg` *does*
control (`𝒰`, hence `∂_θ𝒰` in `𝒲^{5,∞}`, and `ℛ`, hence `D_θ^4 ℛ` in the `z`-weighted
`𝒲^{4,∞}`-field).

The rest of the file is the elementary calculus of `D_θ^i` used to apply the identity: locality
on the open quadrant, additivity on sums of `SmoothQuad` functions, and commutation with
multiplication by a `z`-only factor.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Split
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19aux
import Submission.Work.FTS.Nonlinear.Pieces.RNP.N1ss_smoothQuad
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.n3Bound
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.StarUBound
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.Nonlinear.Pieces.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false

/-! ## The algebraic identity `∂_θ 𝒰 = -(2𝒱 + ℛ + α D_z𝒱)` -/

/-- **The identity of row 19.**  For `Ψ` which is `C^∞` on the open quadrant and `(z,θ)` in that
quadrant,

  `∂_θ 𝒰(Ψ) = -(2 𝒱(Ψ) + ℛ(Ψ) + α · D_z 𝒱(Ψ))`.

Proof: write `a = ∂_θΨ`, `b = ∂_z∂_θΨ = ∂_θ∂_zΨ` (Clairaut), `c = ∂_zΨ`, `d = Ψ`.  Then
`∂_θ 𝒰 = -3a - αzb`, while `𝒱 = a - tan θ·d`, `∂_z𝒱 = b - tan θ·c` and
`ℛ = 2 tan θ·d + α tan θ·z c + a`; the two sides differ by
`2a - 2 tan θ d + 2 tan θ d + a - 3a + α z tan θ c - α z tan θ c = 0`. -/
theorem pth_Uop_eq_neg {α : ℝ} {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad Ψ)
    {z θ : ℝ} (hz : -1 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pth (Work.Construction.Uop α Ψ) z θ
      = -(2 * Work.Construction.Vop Ψ z θ + Work.Construction.Rop α Ψ z θ
          + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ) := by
  have hquad : (z, θ) ∈ Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hz, hθ⟩
  have hquad_open : IsOpen (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hcd : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ) :=
    (hsm.contDiffAt (hquad_open.mem_nhds hquad)).of_le (by simp [Work.Stability.smoothOrder])
  have hsm_pz : Work.FTS.LocData.SmoothQuad (Work.Spaces.pz Ψ) :=
    Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry
      (Work.FTS.LocData.contDiffOn_pz Work.Spaces.isOpen_quadU hsm)
  have hsm_pth : Work.FTS.LocData.SmoothQuad (Work.Spaces.pth Ψ) :=
    Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry
      (Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hsm)
  have hd1 : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ :=
    ((hsm.curry_θ hz).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz Ψ z θ') θ :=
    ((hsm_pz.curry_θ hz).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have hdz1 : DifferentiableAt ℝ (fun z' => Ψ z' θ) z :=
    ((hsm.curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  have hdz2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pth Ψ z' θ) z :=
    ((hsm_pth.curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  have hcl : Work.Spaces.pz (Work.Spaces.pth Ψ) z θ = Work.Spaces.pth (Work.Spaces.pz Ψ) z θ :=
    Work.Spaces.pz_pth_comm (f := Ψ) hcd
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hL : Work.Spaces.pth (Work.Construction.Uop α Ψ) z θ
      = -3 * Work.Spaces.pth Ψ z θ - α * z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ := by
    change deriv ((fun θ' => -3 * Ψ z θ') - fun θ' => α * z * Work.Spaces.pz Ψ z θ') θ = _
    rw [deriv_sub (hd1.const_mul (-3)) (hd2.const_mul (α * z)),
      deriv_const_mul (-3) hd1, deriv_const_mul (α * z) hd2]
    rfl
  have hV1 : Work.Construction.Vop Ψ z θ = Work.Spaces.pth Ψ z θ - Real.tan θ * Ψ z θ := rfl
  have hR1 : Work.Construction.Rop α Ψ z θ
      = (2 * Real.sin θ * Ψ z θ + α * Real.sin θ * z * Work.Spaces.pz Ψ z θ
          + Real.cos θ * Work.Spaces.pth Ψ z θ) / Real.cos θ := rfl
  have hDz : Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ
      = z * (Work.Spaces.pz (Work.Spaces.pth Ψ) z θ - Real.tan θ * Work.Spaces.pz Ψ z θ) := by
    change z * Work.Spaces.pz (Work.Construction.Vop Ψ) z θ = _
    have hVe : Work.Construction.Vop Ψ
        = fun z θ => Work.Spaces.pth Ψ z θ - Real.tan θ * Ψ z θ := rfl
    rw [hVe]
    change z * deriv ((fun z' => Work.Spaces.pth Ψ z' θ) - fun z' => Real.tan θ * Ψ z' θ) z = _
    rw [deriv_sub hdz2 (hdz1.const_mul (Real.tan θ)),
      deriv_const_mul (Real.tan θ) hdz1]
    rfl
  rw [hL, hV1, hR1, hDz, ← hcl, Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-! ## The calculus of `D_θ^i` on the open quadrant -/

/-- **Locality** of `D_θ^i` on the open quadrant: functions that agree on the quadrant have the
same iterated `D_θ`-derivatives there.  (No smoothness is needed; only the fact that `D_θ` is a
`θ`-derivative.) -/
theorem DthIter_congr_Ioi {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, -1 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ) (i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i F z θ = Work.Spaces.DthIter i G z θ := by
  induction i with
  | zero => intro z θ hz h1 h2; exact h z θ hz h1 h2
  | succ n ih =>
    intro z θ hz h1 h2
    have heq : (fun θ' => Work.Spaces.DthIter n F z θ')
        =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n G z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨h1, h2⟩)]
        with θ' hθ'
      exact ih z θ' hz hθ'.1 hθ'.2
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    rw [heq.deriv_eq]

/-- The identically vanishing function has vanishing `D_θ`-iterates. -/
theorem DthIter_zero_fun (i : ℕ) :
    ∀ z θ, Work.Spaces.DthIter i (fun _ : ℝ => fun _ : ℝ => (0 : ℝ)) z θ = 0 := by
  induction i with
  | zero => intro z θ; rfl
  | succ n ih =>
    intro z θ
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    have h0 : (fun θ' : ℝ => Work.Spaces.DthIter n (fun _ : ℝ => fun _ : ℝ => (0 : ℝ)) z θ')
        = fun _ : ℝ => (0 : ℝ) := funext (fun θ' => ih z θ')
    rw [h0, deriv_const]
    ring

/-- **Additivity** of `D_θ^i` on sums of functions which are `C^∞` on the open quadrant. -/
theorem DthIter_add_smoothQuad {F G : ℝ → ℝ → ℝ}
    (hF : Work.FTS.LocData.SmoothQuad F) (hG : Work.FTS.LocData.SmoothQuad G) (i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i (fun z θ => F z θ + G z θ) z θ
        = Work.Spaces.DthIter i F z θ + Work.Spaces.DthIter i G z θ := by
  induction i with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
    intro z θ hz h1 h2
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
    have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => F z θ + G z θ) z θ')
        =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n F z θ' + Work.Spaces.DthIter n G z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      exact ih z θ' hz hθ'.1 hθ'.2
    have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n F z θ') θ :=
      hF.differentiableAt_slice_DthIter n hz hθ
    have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n G z θ') θ :=
      hG.differentiableAt_slice_DthIter n hz hθ
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    rw [heq.deriv_eq,
      show (fun θ' => Work.Spaces.DthIter n F z θ' + Work.Spaces.DthIter n G z θ')
        = (fun θ' => Work.Spaces.DthIter n F z θ') + fun θ' => Work.Spaces.DthIter n G z θ'
        from rfl, deriv_add hd1 hd2]
    ring

/-- Multiplication by a `z`-only factor commutes with `D_θ^i` (pointwise, with no regularity
hypotheses: the constant rule for `deriv` is unconditional). -/
theorem DthIter_mul_zfactor (i : ℕ) (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    ∀ z θ, Work.Spaces.DthIter i (fun z θ => c z * g z θ) z θ
      = c z * Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => intro z θ; rfl
  | succ n ih =>
    intro z θ
    have hfe : (fun θ' => Work.Spaces.DthIter n (fun z θ => c z * g z θ) z θ')
        = fun θ' => c z * Work.Spaces.DthIter n g z θ' := funext (fun θ' => ih z θ')
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    rw [hfe, Work.FTS.Nonlinear.Pieces.RowsN0Aux.deriv_const_mul']
    ring

end Work.FTS.Nonlinear.Pieces.RNP.row19
