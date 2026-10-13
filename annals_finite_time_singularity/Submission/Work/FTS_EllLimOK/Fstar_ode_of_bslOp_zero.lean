/-
Copyright: work module for the Elgindi finite-time singularity project.

# The Euler ODE satisfied by the angular moment `F_*δ` of a box-regular solution of `L δ = 0`

Elgindi, Annals 194 (3) 2021, §'Elliptic Regularity Estimates'.  Integrating the elliptic
equation

  `L(δ) = -α²z² ∂_zzδ - α(5+α)z ∂_zδ - ∂_θθδ + ∂_θ(tan θ · δ) - 6δ = 0`

against the angular weight `φ(θ) = sin θ cos²θ` (which lies in the kernel of the adjoint of the
`α = 0` part, `Work.Elliptic.Lzero_orthogonal`) gives the ordinary differential equation

  `α²z² Ψ_*''(z) + α(5+α)z Ψ_*'(z) = 0`

for the angular moment `Ψ_*(z) = F_*δ(z) = ∫_0^{π/2} δ(z,θ) sinθcos²θ dθ`.

The data class is the finite-order one of this area, `Work.FTS_EllLimOK.BoxReg δ`: `δ` is
jointly `C²` on every closed box `[a,b] × [0,π/2]` with `0 < a ≤ b`.  This is enough, because
* the two `z`-derivatives of the parametrised angular integral are the integrals of the formal
  derivatives (`Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt`, fed with the box
  calculus `Work.FTS_EllLimOK.boxReg_facts`: the slices `θ ↦ δ s θ` and `θ ↦ ∂_zδ s θ` are
  differentiable in `s` at *every* angle `θ ∈ [0,π/2]`, and `∂_zδ`, `∂_z²δ` are jointly
  continuous up to the two boundary angles);
* the moment identity `Work.FTS.ClassC.Fstar_bslOp_moment` turns `L δ = 0` into the Euler
  relation `α²z² F_*(∂_z²δ) + α(5+α)z F_*(∂_zδ) = 0`;
* the Dirichlet values `δ z 0 = δ z (π/2) = 0` give the orthogonality of `φ` against `L₀`.

The proof is complete: no unfinished goals.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.FTS_EllLimOK.Phi_deriv
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Elliptic.PsiStar_ode
import Submission.Work.Coercivity.contDiffOn_infty_integral_Itheta
import Submission.Work.FTS.ClassC.Fstar_bslOp_moment
import Submission.Work.FTS.ClassC.Fstar_eq_zero_of_bslOp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## The box calculus at a fixed radial point -/

/-- The box calculus of `Work.FTS_EllLimOK.boxReg_facts`, transported to the box
`[z/2, 2z] × [0,π/2]` around a fixed `z > 0`: the slices of `δ` and of `∂_zδ` are
differentiable in the radial variable at every angle of `Iθ`, and the two partials `∂_zδ`,
`∂_z²δ` are jointly continuous on the (radially open) box. -/
private theorem box_facts_at {δ : ℝ → ℝ → ℝ} (hbox : BoxReg δ) {z : ℝ} (hz : 0 < z) :
    (∀ s ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Work.Spaces.Iθ,
      HasDerivAt (fun s' : ℝ => δ s' θ) (Work.Spaces.pz δ s θ) s) ∧
    (∀ s ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Work.Spaces.Iθ,
      HasDerivAt (fun s' : ℝ => Work.Spaces.pz δ s' θ) (Work.Spaces.pzIter 2 δ s θ) s) ∧
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz δ p.1 p.2)
      (Set.Ioo (z / 2) (2 * z) ×ˢ Work.Spaces.Iθ) ∧
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 δ p.1 p.2)
      (Set.Ioo (z / 2) (2 * z) ×ˢ Work.Spaces.Iθ) := by
  have hab : z / 2 < 2 * z := by linarith
  have hδ : ContDiffOn ℝ 2 (Function.uncurry δ)
      (Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc 0 (π / 2)) :=
    hbox (z / 2) (2 * z) (by linarith) (le_of_lt hab)
  obtain ⟨hsl, hslpz, hpc, hp2c⟩ := boxReg_facts hab hδ
  have hsub : Set.Ioo (z / 2) (2 * z) ×ˢ Work.Spaces.Iθ
      ⊆ Set.Ioo (z / 2) (2 * z) ×ˢ Set.Icc 0 (π / 2) := by
    intro p hp
    exact ⟨hp.1, hp.2⟩
  exact ⟨fun s hs θ hθ => hsl s hs θ hθ, fun s hs θ hθ => hslpz s hs θ hθ,
    hpc.mono hsub, hp2c.mono hsub⟩

/-- The angular slices of the two radial partials of a box-regular datum are continuous on the
(compact, closed) angular interval. -/
private theorem slices_continuous {δ : ℝ → ℝ → ℝ} (hbox : BoxReg δ) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.pz δ z θ) Work.Spaces.Iθ ∧
    ContinuousOn (fun θ : ℝ => Work.Spaces.pzIter 2 δ z θ) Work.Spaces.Iθ := by
  obtain ⟨-, -, hpc, hp2c⟩ := box_facts_at hbox hz
  have hzV : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
  have h1 : ContinuousOn (fun θ : ℝ => Work.Spaces.pz δ z θ) Work.Spaces.Iθ := by
    have h := hpc.comp (continuousOn_const.prodMk continuousOn_id)
      (fun θ hθ => ⟨hzV, hθ⟩)
    simpa only [Function.comp_def, id_eq] using h
  have h2 : ContinuousOn (fun θ : ℝ => Work.Spaces.pzIter 2 δ z θ) Work.Spaces.Iθ := by
    have h := hp2c.comp (continuousOn_const.prodMk continuousOn_id)
      (fun θ hθ => ⟨hzV, hθ⟩)
    simpa only [Function.comp_def, id_eq] using h
  exact ⟨h1, h2⟩

/-! ## The two derivatives of the angular moment -/

/-- **Differentiation under the angular integral sign.**  For box-regular `δ` and `z > 0`, the
angular moment `F_*δ` has the two expected radial derivatives. -/
private theorem hasDerivAt_moment {δ : ℝ → ℝ → ℝ} (hbox : BoxReg δ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Work.Elliptic.Fstar δ) (Work.Elliptic.Fstar (Work.Spaces.pz δ) z) z ∧
    HasDerivAt (Work.Elliptic.Fstar (Work.Spaces.pz δ))
      (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 δ) z) z := by
  obtain ⟨hsl, hslpz, hpc, hp2c⟩ := box_facts_at hbox hz
  have hzV : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
  have hab : z / 2 < 2 * z := by linarith
  have hcontδ : ContinuousOn (fun p : ℝ × ℝ => δ p.1 p.2)
      (Set.Ioo (z / 2) (2 * z) ×ˢ Work.Spaces.Iθ) := by
    have hδ : ContDiffOn ℝ 2 (Function.uncurry δ)
        (Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc 0 (π / 2)) :=
      hbox (z / 2) (2 * z) (by linarith) (le_of_lt hab)
    refine hδ.continuousOn.mono ?_
    intro p hp
    exact ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, hp.2⟩
  have hφ : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
      (Set.Ioo (z / 2) (2 * z) ×ˢ Work.Spaces.Iθ) := by
    unfold Work.Elliptic.sinCos2
    fun_prop
  constructor
  · refine Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt
      (g := fun s θ => δ s θ * Work.Elliptic.sinCos2 θ)
      (g' := fun s θ => Work.Spaces.pz δ s θ * Work.Elliptic.sinCos2 θ)
      isOpen_Ioo hzV ?_ ?_ ?_
    · exact hcontδ.mul hφ
    · exact hpc.mul hφ
    · intro θ hθ s hs
      exact (hsl s hs θ hθ).mul_const _
  · refine Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt
      (g := fun s θ => Work.Spaces.pz δ s θ * Work.Elliptic.sinCos2 θ)
      (g' := fun s θ => Work.Spaces.pzIter 2 δ s θ * Work.Elliptic.sinCos2 θ)
      isOpen_Ioo hzV ?_ ?_ ?_
    · exact hpc.mul hφ
    · exact hp2c.mul hφ
    · intro θ hθ s hs
      exact (hslpz s hs θ hθ).mul_const _

/-- The second angular moment `F_*(∂_z²δ)` is continuous on `(0,∞)`. -/
private theorem continuousOn_fstar_pzIter2 {δ : ℝ → ℝ → ℝ} (hbox : BoxReg δ) :
    ContinuousOn (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 δ)) (Set.Ioi (0 : ℝ)) := by
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  obtain ⟨-, -, hpc, hp2c⟩ := box_facts_at hbox hzpos
  have hzV : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
  have hφ : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
      (Set.Ioo (z / 2) (2 * z) ×ˢ Work.Spaces.Iθ) := by
    unfold Work.Elliptic.sinCos2
    fun_prop
  have hcont := Work.Coercivity.continuousOn_integral_Itheta_of_continuousOn
    (g := fun s θ => Work.Spaces.pzIter 2 δ s θ * Work.Elliptic.sinCos2 θ)
    isOpen_Ioo (hp2c.mul hφ)
  exact (hcont.continuousAt (isOpen_Ioo.mem_nhds hzV)).continuousWithinAt

/-! ## The main theorem -/

theorem Fstar_ode_of_bslOp_zero {α : ℝ} (hα : 0 < α) {δ : ℝ → ℝ → ℝ}
    (hsol : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Elliptic.bslOp α δ z θ = 0)
    (hbox : Work.FTS_EllLimOK.BoxReg δ)
    (h0 : ∀ z ∈ Set.Ioi (0 : ℝ), δ z 0 = 0)
    (h1 : ∀ z ∈ Set.Ioi (0 : ℝ), δ z (π / 2) = 0) :
    ContDiffOn ℝ 2 (Work.Elliptic.Fstar δ) (Set.Ioi (0 : ℝ)) ∧
      ∀ z ∈ Set.Ioi (0 : ℝ),
        α ^ 2 * z ^ 2 * deriv (deriv (Work.Elliptic.Fstar δ)) z
          + α * (5 + α) * z * deriv (Work.Elliptic.Fstar δ) z = 0 := by
  have hD1 : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (Work.Elliptic.Fstar δ)
      (Work.Elliptic.Fstar (Work.Spaces.pz δ) z) z :=
    fun z hz => (hasDerivAt_moment hbox hz).1
  have hD2 : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (Work.Elliptic.Fstar (Work.Spaces.pz δ))
      (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 δ) z) z :=
    fun z hz => (hasDerivAt_moment hbox hz).2
  have hcont2 : ContinuousOn (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 δ))
      (Set.Ioi (0 : ℝ)) := continuousOn_fstar_pzIter2 hbox
  -- the derivative of `F_*(∂_zδ)` is `F_*(∂_z²δ)` on `(0,∞)`
  have hcont_deriv : ContinuousOn (deriv (Work.Elliptic.Fstar (Work.Spaces.pz δ)))
      (Set.Ioi (0 : ℝ)) :=
    hcont2.congr (fun z hz => (hD2 z hz).deriv)
  -- `F_*(∂_zδ)` is `C¹`
  have hI1_cd1 : ContDiffOn ℝ 1 (Work.Elliptic.Fstar (Work.Spaces.pz δ))
      (Set.Ioi (0 : ℝ)) := by
    refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
      (f := Work.Elliptic.Fstar (Work.Spaces.pz δ)) (n := (0 : WithTop ℕ∞))
      (s := Set.Ioi (0 : ℝ)) isOpen_Ioi).2 ⟨?_, ?_, ?_⟩
    · exact fun z hz => (hD2 z hz).differentiableAt.differentiableWithinAt
    · intro h
      exact absurd h (by simp)
    · rw [contDiffOn_zero]
      exact hcont_deriv
  refine ⟨?_, ?_⟩
  · -- `F_*δ` is `C²`
    refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (f := Work.Elliptic.Fstar δ)
      (n := (1 : WithTop ℕ∞)) (s := Set.Ioi (0 : ℝ)) isOpen_Ioi).2 ⟨?_, ?_, ?_⟩
    · exact fun z hz => (hD1 z hz).differentiableAt.differentiableWithinAt
    · intro h
      exact absurd h (by simp)
    · exact hI1_cd1.congr (fun z hz => (hD1 z hz).deriv)
  · -- the Euler ODE
    intro z hz
    have hder1 : deriv (Work.Elliptic.Fstar δ) z
        = Work.Elliptic.Fstar (Work.Spaces.pz δ) z := (hD1 z hz).deriv
    have hder2 : deriv (deriv (Work.Elliptic.Fstar δ)) z
        = Work.Elliptic.Fstar (Work.Spaces.pzIter 2 δ) z := by
      have hns : deriv (Work.Elliptic.Fstar δ)
          =ᶠ[𝓝 z] Work.Elliptic.Fstar (Work.Spaces.pz δ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with s hs
        exact (hD1 s hs).deriv
      rw [Filter.EventuallyEq.deriv_eq hns]
      exact (hD2 z hz).deriv
    rw [hder2, hder1]
    -- the integrability side conditions of the moment identity
    obtain ⟨hslc, h2c⟩ := slices_continuous hbox hz
    have hφ : ContinuousOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
      unfold Work.Elliptic.sinCos2
      fun_prop
    have hIntA : IntegrableOn
        (fun θ : ℝ => (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 δ z θ
          * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      ((continuousOn_const.mul h2c).mul hφ).integrableOn_compact isCompact_Icc
    have hIntB : IntegrableOn
        (fun θ : ℝ => (α * (5 + α) * z) * Work.Spaces.pz δ z θ
          * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      ((continuousOn_const.mul hslc).mul hφ).integrableOn_compact isCompact_Icc
    have hIntL : IntegrableOn
        (fun θ : ℝ => Work.Elliptic.Lzero δ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      Work.Elliptic.integrableOn_Lzero_mul_sinCos2 δ z (hbox.slice hz)
    have hmom := Work.FTS.ClassC.Fstar_bslOp_moment (α := α) (Ψ := δ) (z := z)
      (hbox.slice hz) (h0 z hz) (h1 z hz) hIntA hIntB hIntL
    -- the moment of the equation vanishes, since the equation does
    have hz0 : Work.Elliptic.Fstar (Work.Elliptic.bslOp α δ) z = 0 := by
      have h := Work.FTS.ClassC.Fstar_bslOp_eq_Fstar (α := α) (F := fun _ _ => (0 : ℝ))
        (Ψ := δ) (z := z) (fun θ hθ hθ2 => hsol z hz θ ⟨hθ, hθ2⟩)
      rw [h]
      simp [Work.Elliptic.Fstar]
    rw [hz0] at hmom
    linarith [hmom]

end Work.FTS_EllLimOK
