import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.CurrySmooth

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

/-! ## The four summands of `𝓛_Γ^T` and their `θ`-derivatives

`𝓛_Γ^T f = 𝓛 f - (2zΓ/(c(1+z)²))L₁₂(f) - Transport f + (Γ/c)(2z²/(1+z)³)C₀(f)`,
where `C₀(f) = L₁₂(Transport f)(0)`.  The two "Γ-correction" summands are packaged
as `T1fun` and `T4fun`; since `L₁₂(f)` and `C₀(f)` do not depend on `θ`, their
`θ`-derivatives are the `D_θΓ`-multiples appearing in `T2` and `T4`. -/

/-- The `L₁₂`-term of `𝓛_Γ`: `(2zΓ(θ)/(c(1+z)²))·L₁₂(f)(z)`. -/
def T1fun (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * L12f f z

/-- The projector term of `𝓛_Γ^T`: `(Γ(θ)/c)(2z²/(1+z)³)·C₀(f)`. -/
def T4fun (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * C0 f

/-- `𝓛_Γ^T` is the sum of the coercive part `𝓛 f` and the three corrections. -/
theorem LGammaT_eq_sum (α : ℝ) (f : ℝ → ℝ → ℝ) :
    LGammaT α f = fun z θ =>
      L f z θ - T1fun α f z θ - Transport f z θ + T4fun α f z θ := by
  funext z θ
  simp only [LGammaT, LGamma, Proj, T1fun, T4fun, C0]
  ring

/-- `Γ` is differentiable on the open angular interval, for every exponent `α`. -/
theorem differentiableAt_Gam (α : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun t => Spaces.Gam α t) θ := by
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < Real.pi / 2 := hθ.2
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
  have hG : Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by positivity
  have hprod : HasDerivAt (fun t => Real.sin t * Real.cos t ^ 2)
      (Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) θ :=
    (Real.hasDerivAt_sin θ).mul ((Real.hasDerivAt_cos θ).pow 2)
  exact (hprod.rpow_const (p := α / 3) (Or.inl hG)).differentiableAt

/-- `D_θΓ = sin(2θ)·Γ'` in the form used by the expansion. -/
theorem DthGam_eq_sin (α : ℝ) (z θ : ℝ) :
    DthGam α z θ = Real.sin (2 * θ) * deriv (fun t => Spaces.Gam α t) θ := rfl

/-- The `θ`-derivative of the `L₁₂`-term. -/
theorem pth_T1fun (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Spaces.pth (T1fun α f) z θ
      = (2 * z / (Spaces.c α * (1 + z) ^ 2)) * L12f f z
          * deriv (fun t => Spaces.Gam α t) θ := by
  show deriv (fun θ' => T1fun α f z θ') θ = _
  have e : (fun θ' => T1fun α f z θ')
      = (fun θ' => ((2 * z / (Spaces.c α * (1 + z) ^ 2)) * L12f f z)
          * Spaces.Gam α θ') := by
    funext θ'; simp only [T1fun]; ring
  rw [e, deriv_const_mul_field]

/-- The `θ`-derivative of the projector term. -/
theorem pth_T4fun (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Spaces.pth (T4fun α f) z θ
      = ((2 * z ^ 2 / (1 + z) ^ 3) * C0 f / Spaces.c α)
          * deriv (fun t => Spaces.Gam α t) θ := by
  show deriv (fun θ' => T4fun α f z θ') θ = _
  have e : (fun θ' => T4fun α f z θ')
      = (fun θ' => (((2 * z ^ 2 / (1 + z) ^ 3) * C0 f / Spaces.c α))
          * Spaces.Gam α θ') := by
    funext θ'; simp only [T4fun]; ring
  rw [e, deriv_const_mul_field]

/-- The `θ`-derivative of the transport term: `∂_θ(3 D_θ f/(1+z)) = (3/(1+z))∂_θ D_θ f`. -/
theorem pth_Transport (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Spaces.pth (Transport f) z θ = (3 / (1 + z)) * Spaces.pth (Spaces.Dth f) z θ := by
  show deriv (fun θ' => Transport f z θ') θ = _
  have e : (fun θ' => Transport f z θ')
      = (fun θ' => (3 / (1 + z)) * Spaces.Dth f z θ') := by
    funext θ'; simp only [Transport]; ring
  rw [e, deriv_const_mul_field]
  rfl

/-- The `z`-derivative of `D_θ f`, used to identify `𝓛(D_θ f)`. -/
theorem pz_Dth_val (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Spaces.pz (Spaces.Dth f) z θ = Real.sin (2 * θ) * Spaces.pz (Spaces.pth f) z θ := by
  show deriv (fun z' => Spaces.Dth f z' θ) z
      = Real.sin (2 * θ) * deriv (fun z' => Spaces.pth f z' θ) z
  have e : (fun z' => Spaces.Dth f z' θ)
      = (fun z' => Real.sin (2 * θ) * Spaces.pth f z' θ) := by
    funext z'; simp only [Spaces.Dth]
  rw [e, deriv_const_mul_field]

/-- **The `θ`-derivative of `𝓛`.**  On a neighbourhood of the quadrant,
`D_θ` commutes with `𝓛`; the point of the statement is that the mixed second
derivative of `f` has been rewritten by Clairaut so that the result has the shape
of `𝓛(D_θ f)`. -/
theorem pth_L {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd f) {z θ : ℝ}
    (hy : (z, θ) ∈ Spaces.nbhU) :
    Spaces.pth (L f) z θ
      = Spaces.pth f z θ + z * Spaces.pz (Spaces.pth f) z θ
        - (2 / (1 + z)) * Spaces.pth f z θ := by
  have hcd : ContDiffOn ℝ ⊤ (Function.uncurry f) Spaces.nbhU := hsm
  have hcf : ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ) :=
    ContDiffOn.contDiffAt hcd (Spaces.isOpen_nbhU.mem_nhds hy)
  have hcd2 : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) := hcf.of_le (by norm_num)
  have hf_diff : DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    Spaces.differentiableAt_curry_right (hcf.differentiableAt (by norm_num))
  have hpz_sm : ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.pz f)) Spaces.nbhU :=
    Spaces.contDiffOn_uncurry_pz Spaces.isOpen_nbhU hcd
  have hpz_diff : DifferentiableAt ℝ (fun θ' => Spaces.pz f z θ') θ :=
    Spaces.differentiableAt_curry_right
      ((ContDiffOn.contDiffAt hpz_sm (Spaces.isOpen_nbhU.mem_nhds hy)).differentiableAt
        (by norm_num))
  have e : (fun θ' => L f z θ')
      = (fun θ' => f z θ' + z * Spaces.pz f z θ' - (2 / (1 + z)) * f z θ') := by
    funext θ'; simp only [L, Spaces.Dz]; ring
  show deriv (fun θ' => L f z θ') θ = _
  rw [e]
  rw [show (fun θ' : ℝ => f z θ' + z * Spaces.pz f z θ' - (2 / (1 + z)) * f z θ')
      = (((fun θ' : ℝ => f z θ') + (fun θ' : ℝ => z * Spaces.pz f z θ'))
          - (fun θ' : ℝ => (2 / (1 + z)) * f z θ')) from rfl]
  rw [deriv_sub (hf_diff.add (hpz_diff.const_mul z)) (hf_diff.const_mul (2 / (1 + z)))]
  rw [deriv_add hf_diff (hpz_diff.const_mul z)]
  rw [deriv_const_mul_field, deriv_const_mul_field]
  rw [show deriv (fun θ' => f z θ') θ = Spaces.pth f z θ from rfl,
      show deriv (fun θ' => Spaces.pz f z θ') θ = Spaces.pth (Spaces.pz f) z θ from rfl,
      ← Work.Spaces.pz_pth_comm hcd2]

/-- The `θ`-derivative of `D_θ f` multiplied by `sin(2θ)` is `D_θ(D_θ f)`. -/
theorem Dth_pth_Dth (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Real.sin (2 * θ) * Spaces.pth (Spaces.Dth f) z θ = Spaces.Dth (Spaces.Dth f) z θ := rfl

/-- `𝓛_Γ^T` written out: the `θ`-slice is the sum of the four pieces. -/
theorem LGammaT_slice (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    (fun θ' => LGammaT α f z θ')
      = (fun θ' => L f z θ' - T1fun α f z θ' - Transport f z θ' + T4fun α f z θ') := by
  funext θ'
  exact congrFun (congrFun (LGammaT_eq_sum α f) z) θ'

/-- **The expansion of `D_θ(𝓛_Γ^T f)`.** -/
theorem dth_LGammaT_expansion (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : Spaces.SmoothNbhd f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Spaces.Dth (LGammaT α f) z θ
      = Aop (Spaces.Dth f) z θ + T2 α f z θ + T4 α f z θ := by
  have hy : (z, θ) ∈ Spaces.nbhU :=
    Spaces.mem_nbhU (by rw [Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz)
      (by rw [Spaces.Iθ, Set.mem_Icc]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hcf : ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ) :=
    ContDiffOn.contDiffAt hf (Spaces.isOpen_nbhU.mem_nhds hy)
  have hf_diff : DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    Spaces.differentiableAt_curry_right (hcf.differentiableAt (by norm_num))
  have hpz_sm : ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.pz f)) Spaces.nbhU :=
    Spaces.contDiffOn_uncurry_pz Spaces.isOpen_nbhU hf
  have hpz_diff : DifferentiableAt ℝ (fun θ' => Spaces.pz f z θ') θ :=
    Spaces.differentiableAt_curry_right
      ((ContDiffOn.contDiffAt hpz_sm (Spaces.isOpen_nbhU.mem_nhds hy)).differentiableAt
        (by norm_num))
  have hDdiff : DifferentiableAt ℝ (fun θ' => Spaces.Dth f z θ') θ :=
    Spaces.differentiableAt_curry_right
      ((ContDiffOn.contDiffAt (Spaces.SmoothNbhd.Dth hf)
        (Spaces.isOpen_nbhU.mem_nhds hy)).differentiableAt (by norm_num))
  have dG := differentiableAt_Gam α hθ
  have dL : DifferentiableAt ℝ (fun θ' => L f z θ') θ := by
    rw [show (fun θ' => L f z θ')
        = (fun θ' => f z θ' + z * Spaces.pz f z θ' - (2 / (1 + z)) * f z θ') from by
      funext θ'; simp only [L, Spaces.Dz]; ring]
    exact (hf_diff.add (hpz_diff.const_mul z)).sub (hf_diff.const_mul (2 / (1 + z)))
  have dT1 : DifferentiableAt ℝ (fun θ' => T1fun α f z θ') θ := by
    rw [show (fun θ' => T1fun α f z θ')
        = (fun θ' => ((2 * z / (Spaces.c α * (1 + z) ^ 2)) * L12f f z)
            * Spaces.Gam α θ') from by
      funext θ'; simp only [T1fun]; ring]
    exact dG.const_mul _
  have dTr : DifferentiableAt ℝ (fun θ' => Transport f z θ') θ := by
    rw [show (fun θ' => Transport f z θ')
        = (fun θ' => (3 / (1 + z)) * Spaces.Dth f z θ') from by
      funext θ'; simp only [Transport]; ring]
    exact hDdiff.const_mul _
  have dT4 : DifferentiableAt ℝ (fun θ' => T4fun α f z θ') θ := by
    rw [show (fun θ' => T4fun α f z θ')
        = (fun θ' => (((2 * z ^ 2 / (1 + z) ^ 3) * C0 f / Spaces.c α))
            * Spaces.Gam α θ') from by
      funext θ'; simp only [T4fun]; ring]
    exact dG.const_mul _
  have hpth : Spaces.pth (LGammaT α f) z θ
      = Spaces.pth (L f) z θ - Spaces.pth (T1fun α f) z θ
        - Spaces.pth (Transport f) z θ + Spaces.pth (T4fun α f) z θ := by
    show deriv (fun θ' => LGammaT α f z θ') θ = _
    rw [LGammaT_slice]
    rw [show (fun θ' : ℝ => L f z θ' - T1fun α f z θ' - Transport f z θ' + T4fun α f z θ')
        = (((fun θ' : ℝ => L f z θ') - (fun θ' : ℝ => T1fun α f z θ'))
            - (fun θ' : ℝ => Transport f z θ')) + (fun θ' : ℝ => T4fun α f z θ') from rfl]
    rw [deriv_add ((dL.sub dT1).sub dTr) dT4]
    rw [deriv_sub (dL.sub dT1) dTr]
    rw [deriv_sub dL dT1]
    rfl
  rw [show Spaces.Dth (LGammaT α f) z θ
      = Real.sin (2 * θ) * Spaces.pth (LGammaT α f) z θ from rfl]
  rw [hpth, pth_L hf hy, pth_T1fun, pth_Transport, pth_T4fun]
  rw [show Aop (Spaces.Dth f) z θ
        = L (Spaces.Dth f) z θ - (3 / (1 + z)) * Spaces.Dth (Spaces.Dth f) z θ from rfl]
  rw [show L (Spaces.Dth f) z θ
        = Spaces.Dth f z θ + Spaces.Dz (Spaces.Dth f) z θ
            - 2 * Spaces.Dth f z θ / (1 + z) from rfl]
  rw [show Spaces.Dz (Spaces.Dth f) z θ = z * Spaces.pz (Spaces.Dth f) z θ from rfl]
  rw [pz_Dth_val]
  rw [show Spaces.Dth (Spaces.Dth f) z θ
        = Real.sin (2 * θ) * Spaces.pth (Spaces.Dth f) z θ from rfl]
  rw [show Spaces.Dth f z θ = Real.sin (2 * θ) * Spaces.pth f z θ from rfl]
  rw [show T2 α f z θ
        = -(DthGam α z θ) * (2 * z / (Spaces.c α * (1 + z) ^ 2)) * L12f f z from rfl]
  rw [show T4 α f z θ
        = (DthGam α z θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * C0 f from rfl]
  rw [DthGam_eq_sin]
  ring

end Work.Coercivity
