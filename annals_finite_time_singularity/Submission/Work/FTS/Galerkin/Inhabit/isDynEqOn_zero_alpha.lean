import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Construction.MufunS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Galerkin.Inhabit

/-!
## Inhabitation of the dynamic modulated equation at `α = 0`

Everything in the right hand side of the fake-time equation degenerates at `α = 0` for the
identically zero family: `Fstar 0 = 0`, `L₁₂` of the zero profile vanishes, the nonlinear terms
`N₀`, `N`, `N_*` vanish on `F = F_* + g = 0`, `Φ = 0`, `g = 0`, the modulation constants
`μ̄ = (1/2α)(…)`, `λ = -2μ̄/(1+μ̄)` and the singular part `Θ = (1/4α)sin(2θ)L₁₂(F)` are all
killed by the factors `1/α` (junk value `0` at `α = 0`), and the linear operator
`𝓛_Γ^T = 𝓛_Γ - 𝕡∘Transport` is zero on the zero profile.  The helper lemmas below record this
degeneration pointwise; the final theorem is then immediate.
-/

/-- The identically zero fake-time family. -/
private abbrev zeroFam : Work.FTS.Galerkin.Fam := fun _ _ _ => (0 : ℝ)

/-- The profile `F_*` at `α = 0` is the zero profile (the prefactor `α` kills it). -/
private theorem fstar_zero : Work.Construction.Fstar 0 = fun _ _ => (0 : ℝ) := by
  funext z θ; simp [Work.Construction.Fstar]

/-- `slice` of the zero family is the zero profile. -/
private theorem slice_zero (τ : ℝ) : Work.FTS.Galerkin.slice zeroFam τ = fun _ _ => (0 : ℝ) :=
  rfl

/-- `F_*(τ) = F_* + g(τ)` at `α = 0` with `g = 0` is `F_* 0`, the zero profile. -/
private theorem Ftau_zero (τ : ℝ) : Work.Construction.Ftau 0 zeroFam τ
    = Work.Construction.Fstar 0 := by
  funext z θ; simp [Work.Construction.Ftau]

/-- `L₁₂` of the identically zero profile vanishes. -/
private theorem L12_zero : Work.Construction.L12 (fun _ _ => (0 : ℝ)) = fun _ => 0 := by
  funext z
  simp [Work.Construction.L12, Work.FM.L12, Work.FM.L12dens]

/-- The full quadratic term `N₀` vanishes at `α = 0` on the zero data. -/
private theorem N0_zero (τ z θ : ℝ) :
    Work.Construction.N0 0 (Work.Construction.Ftau 0 zeroFam τ)
      (Work.FTS.Galerkin.slice zeroFam τ) z θ = 0 := by
  rw [Ftau_zero, slice_zero]
  simp [Work.Construction.N0, fstar_zero, Work.Construction.L12, Work.FM.L12, Work.FM.L12dens]

/-- The elliptic-correction term `N` vanishes at `α = 0` on the zero data: the singular part
`Θ = (1/(4α))sin(2θ)L₁₂(F)` is killed by `1/(4·0) = 0`, and the remaining terms all carry a
factor `F = 0` or `(F,K) = 0`. -/
private theorem N_zero (τ z θ : ℝ) :
    Work.Construction.N 0 (Work.Construction.Ftau 0 zeroFam τ)
      (Work.FTS.Galerkin.slice zeroFam τ) z θ = 0 := by
  rw [Ftau_zero, slice_zero]
  simp [Work.Construction.N, fstar_zero, Work.Construction.FK, Work.Construction.PhiTil,
    Work.Construction.Theta, Work.Construction.Rop, Work.Construction.Uop, Work.Construction.Vop]

/-- The linear term `N_*` vanishes on the zero profile. -/
private theorem Nstar_zero (μ lam : ℝ) (z θ : ℝ) :
    Work.Construction.Nstar μ lam (fun _ _ => (0 : ℝ)) z θ = 0 := by
  simp [Work.Construction.Nstar, Work.Spaces.Dz, Work.Spaces.pz]

/-- The linear term `N_*` vanishes on the slice of the zero family. -/
private theorem Nstar_slice (μ lam τ z θ : ℝ) :
    Work.Construction.Nstar μ lam (Work.FTS.Galerkin.slice zeroFam τ) z θ = 0 := by
  rw [slice_zero]; exact Nstar_zero μ lam z θ

/-- The dynamical modulation constant `μ̄(τ)` vanishes at `α = 0`: both of its prefactors are
`1/(2·0) = 0`. -/
private theorem muDyn_zero (τ : ℝ) : Work.FTS.Galerkin.muDyn 0 zeroFam zeroFam τ = 0 := by
  simp [Work.FTS.Galerkin.muDyn, Work.Construction.mufunS]

/-- The second modulation constant `λ(τ) = -2μ̄/(1+μ̄)` vanishes at `α = 0`. -/
private theorem lamDyn_zero (τ : ℝ) : Work.FTS.Galerkin.lamDyn 0 zeroFam zeroFam τ = 0 := by
  simp [Work.FTS.Galerkin.lamDyn, Work.Construction.lamfun, muDyn_zero]

/-- The paper's `μ̄ = L₁₂(N₀)(0) + L₁₂(N)(0)` vanishes at `α = 0` on the zero data. -/
private theorem mubar_zero (τ : ℝ) :
    Work.Construction.mubar
      (Work.Construction.N0 0 (Work.Construction.Ftau 0 zeroFam τ)
        (Work.FTS.Galerkin.slice zeroFam τ))
      (Work.Construction.N 0 (Work.Construction.Ftau 0 zeroFam τ)
        (Work.FTS.Galerkin.slice zeroFam τ)) = 0 := by
  simp [Work.Construction.mubar, N0_zero, N_zero, Work.Construction.L12, Work.FM.L12,
    Work.FM.L12dens]

/-- The right hand side `gRHS = -μ̄·AK + N₀ + N + N_*` of the fake-time equation vanishes at
`α = 0` on the zero data. -/
private theorem dynRHS_zero (τ z θ : ℝ) : Work.FTS.Galerkin.dynRHS 0 zeroFam zeroFam τ z θ = 0 := by
  simp [Work.FTS.Galerkin.dynRHS, Work.Construction.gRHS, muDyn_zero, lamDyn_zero,
    mubar_zero, N0_zero, N_zero, Nstar_slice]

/-- `𝓛_Γ^T` vanishes on the zero profile at `α = 0`. -/
private theorem LGammaT_zero (z θ : ℝ) : Work.Coercivity.LGammaT 0 (fun _ _ => (0 : ℝ)) z θ = 0 := by
  simp [Work.Coercivity.LGammaT, Work.Coercivity.LGamma, Work.Coercivity.L,
    Work.Coercivity.Proj, Work.Coercivity.Transport, Work.Coercivity.L12f,
    Work.FM.L12, Work.FM.L12dens, Work.Spaces.Dz, Work.Spaces.pz, Work.Spaces.Dth,
    Work.Spaces.pth]

/-- `𝓛_Γ^T` vanishes on the slice of the zero family at `α = 0`. -/
private theorem LGammaT_slice_zero (τ z θ : ℝ) :
    Work.Coercivity.LGammaT 0 (Work.FTS.Galerkin.slice zeroFam τ) z θ = 0 := by
  rw [slice_zero]; exact LGammaT_zero z θ

/-- The linear part `-𝓛_Γ^T g` of the fake-time equation vanishes at `α = 0` on the zero family. -/
private theorem dynLin_zero (τ z θ : ℝ) : Work.FTS.Galerkin.dynLin 0 zeroFam τ z θ = 0 := by
  simp [Work.FTS.Galerkin.dynLin, LGammaT_slice_zero]

/-- **Inhabitation of the dynamic equation at `α = 0`:** the identically zero family solves the
dynamic modulated equation at `α = 0` (with the identically zero stream function).

Intended proof: all the defining functions of the right hand side degenerate at `α = 0`:
`Fstar 0 = 0`, `L12 (Fstar 0) = 0`, `L₁₂` of the zero function is `0`, the terms of `N0 0 F g`,
`N 0 F Φ` and `Nstar μ λ g` all vanish on the open quadrant for `F = 0`, `g = 0`, `Φ = 0`, so
`muDyn 0 0 0 = 0`, `dynRHS 0 0 0 = 0` on `Qd`, `dynLin 0 0 = 0` (since `LGammaT 0 0 = 0` and
`deriv (fun _ => 0) = 0`), and `HasDerivWithinAt (fun _ => 0) 0 (Set.Ici 0) τ` holds. -/
theorem isDynEqOn_zero_alpha :
    Work.FTS.Galerkin.IsDynEqOn 0 (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) := by
  change Work.FTS.Galerkin.IsDynEqOn 0 zeroFam zeroFam
  intro z θ τ hτ hz
  rw [dynLin_zero, dynRHS_zero]
  simpa using hasDerivWithinAt_const (c := (0 : ℝ)) (x := τ) (s := Set.Ici 0)

end Work.FTS.Galerkin.Inhabit
