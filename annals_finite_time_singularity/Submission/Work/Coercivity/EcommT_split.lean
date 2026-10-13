/-
# The splitting of the commutator defect `[D_θ, 𝓛_Γ^T]` into `Γ(θ)·F₁(z) + D_θΓ(θ)·F₂(z)`

The paper (Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (3) 2021, §"Higher order
derivatives and the inner product on `ℋ^k`") uses that the commutator defect

  `E₁ = D_θ 𝓛_Γ^T f - 𝓛_Γ^T (D_θ f)`

*separates*: `θ` enters only through the prescribed angular profile `Γ` and its derivative,

  `E₁(z,θ) = Γ(θ)·F₁(z) + D_θΓ(θ)·F₂(z)`,

with radial factors `F₁`, `F₂` built out of `L₁₂(D_θ f)`, `L₁₂(f)` and the two projector
constants `L₁₂(Transport f)(0)`, `L₁₂(Transport(D_θ f))(0)`.  That separation is what turns
the `ℋ^n`-estimate for `E₁` into a sum of products of an *angular* integral (`∫(D_θ^iΓ)²`)
and a *radial* integral (`∫(D_z^jF)²w²`).

The proof is an instance of the pointwise expansion
`D_θ(𝓛_Γ^T f) = Aop(D_θ f) + T2 + T4` of `thetaDerivative`
(`dth_LGammaT_expansion`, which uses Clairaut's theorem for the one non-trivial
commutation `D_θ 𝓛 = 𝓛 D_θ`) combined with the decomposition
`𝓛_Γ^T g = Aop g - T1fun g + T4fun g` of `LGammaT_eq_sum`: the `Aop(D_θ f)` terms cancel,
the `θ`-derivative of the radial `L₁₂`-profiles contributes `D_θΓ`-multiples, and what
remains is the stated separation.  The four summands are converted into the radial-profile
form by the elementary coefficient identities at the top of the file.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.dth_LGammaT_expansion

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The summands of `𝓛_Γ^T` in radial-profile form

`𝓛_Γ^T = 𝓛 - T1fun - Transport + T4fun` with
`T1fun = (2zΓ/(c(1+z)²))·L₁₂`, `T4fun = (Γ/c)(2z²/(1+z)³)·C₀`, and likewise for the two
`D_θΓ`-terms `T2`, `T4` of `D_θ(𝓛_Γ^T)`.  Writing each of them as `Γ(θ)·pcoef(z)·(…)` or
`Γ(θ)·Wcoef(z)·(…)` (respectively with `D_θΓ` in place of `Γ`) is what lets the final
pointwise identity be closed by `ring`.

The identities say, for instance,
`(Γ/c)(2z²/(1+z)³) = Γ·Wcoef`, i.e. `Γ` is a common factor of numerator and the
denominator `c(1+z)³` may be gathered: this is the field identity
`(a/c)·(b/d) = a·(b/(cd))` (`div_mul_div_comm`), valid with no non-vanishing hypothesis
because Lean's division is total on `ℝ`. -/

theorem T1fun_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    T1fun α f z θ = Spaces.Gam α θ * CT.pcoef α z * L12f f z := by
  simp only [T1fun, CT.pcoef]; ring

theorem T2_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    T2 α f z θ = -(DthGam α z θ) * CT.pcoef α z * L12f f z := by
  simp only [T2, CT.pcoef]

theorem T4fun_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    T4fun α f z θ = Spaces.Gam α θ * CT.Wcoef α z * C0 f := by
  rw [T4fun, CT.Wcoef, div_mul_div_comm]; ring

theorem T4_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    T4 α f z θ = DthGam α z θ * CT.Wcoef α z * C0 f := by
  rw [T4, CT.Wcoef, div_mul_div_comm]; ring

/-- `D_θΓ` is the same object whether it is seen as the `θ`-derivative of the lifted
angular profile `CT.GamF α` (its definition in `CTDefs`) or as the `thetaAux` function
`DthGam α`; the two definitions differ only by the definitional unfolding of `CT.ang`. -/
theorem DthGamF_eq_DthGam (α : ℝ) (z θ : ℝ) : CT.DthGamF α z θ = DthGam α z θ := rfl

/-! ## The splitting -/

theorem EcommT_split (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : Work.Spaces.SmoothNbhd f) :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Coercivity.CT.EcommT α f z θ
        = Work.Coercivity.CT.GamF α z θ * Work.Coercivity.CT.F1 α f z
          + Work.Coercivity.CT.DthGamF α z θ * Work.Coercivity.CT.F2 α f z := by
  intro z θ hz hθ
  -- the expansion of `D_θ(𝓛_Γ^T f)` and the decomposition of `𝓛_Γ^T (D_θ f)`
  have hD := dth_LGammaT_expansion α f hf hz hθ
  have hL : LGammaT α (Spaces.Dth f) z θ
      = L (Spaces.Dth f) z θ - T1fun α (Spaces.Dth f) z θ
        - Transport (Spaces.Dth f) z θ + T4fun α (Spaces.Dth f) z θ := by
    have h := congrFun (congrFun (LGammaT_eq_sum α (Spaces.Dth f)) z) θ
    simpa using h
  simp only [CT.EcommT]
  rw [hD, hL]
  -- the coercive part `Aop (D_θ f) = 𝓛(D_θ f) - (3/(1+z))D_θ(D_θ f)` cancels against the
  -- same terms of the decomposition of `𝓛_Γ^T (D_θ f)`; the surviving terms are the
  -- radial-profile expressions, which `ring` collects into `Γ·F₁ + D_θΓ·F₂`.
  simp only [Aop, Transport, T1fun_eq, T2_eq, T4_eq, T4fun_eq, DthGamF_eq_DthGam,
    CT.GamF_apply, CT.F1, CT.F2, CT.A1, CT.A2, CT.KC0, CT.KC1, C0, CT.pcoef, CT.Wcoef]
  ring

end Work.Coercivity
