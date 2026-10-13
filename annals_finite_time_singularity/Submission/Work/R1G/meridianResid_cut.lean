/-
# `Work.R1G.meridianResid_cut` — the meridian residual of a radially cut field

The G-route of `Work.R1G` needs the meridian residual of the **cut** field
`W ↦ χ(ρ/L)·W` in terms of the meridian residual of `W` and an explicit cut-off term.  This file
proves that identity:

  `meridianResid (χ(ρ/L)·W) ψ = χ(ρ/L)·meridianResid W ψ
      + (χ'(ρ/L)/L)·( (∂_zψ)·(r/ρ) - (ψ/r + ∂_rψ)·(z/ρ) )·W`,

the point being that `χ(ρ/L)` is a function of the **radial** variable alone, so (i) the
`∂_t`-derivative of the cut field costs nothing, and (ii) the two remaining terms of the meridian
residual pick up the radial/axial derivatives `∂_rχ = χ'(ρ/L)/L · (r/ρ)`, `∂_zχ = χ'(ρ/L)/L · (z/ρ)`
of the cut-off.  With `W = W₀` the uncut self-similar field this is exactly the `χ'(ρ/L)/L·K·W₀`
cut-off term of the deficit cancellation (see the module docs of `Submission/Work/R1G/Defs.lean`).

The proof is a pointwise chain/product rule: `∂_t`, `∂_r`, `∂_z` of the product `χ(ρ/L)·W`, followed
by the `χ∘(ρ/L)`-chain rule and a ring rearrangement.  The supporting lemmas
(`pdR_mul`, `pdZ_mul` -- the product rule for the curried partials `Work.Cyl.pdR`, `Work.Cyl.pdZ`
-- and the chain rules `pdR_chi_rhoP_div`, `pdZ_chi_rhoP_div`) are proved here and are reusable.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.R1G.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.R1G

/-! ## Derivatives of `ρ` and of the cut-off `χ(ρ/L)` -/

/-- `r' ↦ ρ(r',z) = √(r'²+z²)` has radial derivative `r/ρ` at `r > 0` (the radial counterpart of
`Work.Cyl.hasDerivAt_rhoP_snd`). -/
lemma hasDerivAt_rhoP_fst' (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z) (r / Work.Cyl.rhoP r z) r := by
  have hsq : HasDerivAt (fun r' : ℝ => r' ^ 2 + z ^ 2) (2 * r) r := by
    have h : HasDerivAt (fun r' : ℝ => r' ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r)
    simpa using h.const_add (z ^ 2)
  have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  have h := hsq.sqrt hne
  have hfun : (fun r' : ℝ => Work.Cyl.rhoP r' z) = fun r' => Real.sqrt (r' ^ 2 + z ^ 2) := by
    funext r'; rw [Work.Cyl.rhoP]
  rw [hfun]
  convert h using 1
  rw [Work.Cyl.rhoP]
  field_simp

/-- **The radial derivative of the cut-off** `χ(ρ(·,z)/L)`:
`∂_r χ(ρ/L) = χ'(ρ/L)/L · (r/ρ)`, i.e. the chain rule through `ρ/L`. -/
lemma pdR_chi_rhoP_div (L r z : ℝ) (hr : 0 < r) :
    Work.Cyl.pdR (fun r' z' => Work.Stability.chi (Work.Cyl.rhoP r' z' / L)) r z
      = deriv Work.Stability.chi (Work.Cyl.rhoP r z / L) / L * (r / Work.Cyl.rhoP r z) := by
  rw [Work.Cyl.pdR]
  have hchi : DifferentiableAt ℝ Work.Stability.chi (Work.Cyl.rhoP r z / L) :=
    (Work.Stability.chi_contDiff.differentiable (by simp)).differentiableAt
  have hρ := hasDerivAt_rhoP_fst' r z hr
  have hdiv : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z / L) ((r / Work.Cyl.rhoP r z) / L) r :=
    hρ.div_const L
  have h : deriv (fun r' : ℝ => Work.Stability.chi (Work.Cyl.rhoP r' z / L)) r
      = deriv Work.Stability.chi (Work.Cyl.rhoP r z / L) * ((r / Work.Cyl.rhoP r z) / L) := by
    rw [show (fun r' : ℝ => Work.Stability.chi (Work.Cyl.rhoP r' z / L))
        = Work.Stability.chi ∘ (fun r' : ℝ => Work.Cyl.rhoP r' z / L) from rfl,
      deriv_comp r hchi hdiv.differentiableAt, hdiv.deriv]
  rw [h]
  ring

/-- **The axial derivative of the cut-off** `χ(ρ(r,·)/L)`:
`∂_z χ(ρ/L) = χ'(ρ/L)/L · (z/ρ)`. -/
lemma pdZ_chi_rhoP_div (L r z : ℝ) (hr : 0 < r) :
    Work.Cyl.pdZ (fun r' z' => Work.Stability.chi (Work.Cyl.rhoP r' z' / L)) r z
      = deriv Work.Stability.chi (Work.Cyl.rhoP r z / L) / L * (z / Work.Cyl.rhoP r z) := by
  rw [Work.Cyl.pdZ]
  have hchi : DifferentiableAt ℝ Work.Stability.chi (Work.Cyl.rhoP r z / L) :=
    (Work.Stability.chi_contDiff.differentiable (by simp)).differentiableAt
  have hρ := Work.Cyl.hasDerivAt_rhoP_snd r z hr
  have hdiv : HasDerivAt (fun z' : ℝ => Work.Cyl.rhoP r z' / L) ((z / Work.Cyl.rhoP r z) / L) z :=
    hρ.div_const L
  have h : deriv (fun z' : ℝ => Work.Stability.chi (Work.Cyl.rhoP r z' / L)) z
      = deriv Work.Stability.chi (Work.Cyl.rhoP r z / L) * ((z / Work.Cyl.rhoP r z) / L) := by
    rw [show (fun z' : ℝ => Work.Stability.chi (Work.Cyl.rhoP r z' / L))
        = Work.Stability.chi ∘ (fun z' : ℝ => Work.Cyl.rhoP r z' / L) from rfl,
      deriv_comp z hchi hdiv.differentiableAt, hdiv.deriv]
  rw [h]
  ring

lemma differentiableAt_chi_rhoP_div_fst (L r z : ℝ) (hr : 0 < r) :
    DifferentiableAt ℝ (fun r' : ℝ => Work.Stability.chi (Work.Cyl.rhoP r' z / L)) r := by
  have hchi : DifferentiableAt ℝ Work.Stability.chi (Work.Cyl.rhoP r z / L) :=
    (Work.Stability.chi_contDiff.differentiable (by simp)).differentiableAt
  have h : DifferentiableAt ℝ (Work.Stability.chi ∘
      (fun r' : ℝ => Work.Cyl.rhoP r' z / L)) r :=
    hchi.comp r ((hasDerivAt_rhoP_fst' r z hr).div_const L).differentiableAt
  simpa [Function.comp_def] using h

lemma differentiableAt_chi_rhoP_div_snd (L r z : ℝ) (hr : 0 < r) :
    DifferentiableAt ℝ (fun z' : ℝ => Work.Stability.chi (Work.Cyl.rhoP r z' / L)) z := by
  have hchi : DifferentiableAt ℝ Work.Stability.chi (Work.Cyl.rhoP r z / L) :=
    (Work.Stability.chi_contDiff.differentiable (by simp)).differentiableAt
  have h : DifferentiableAt ℝ (Work.Stability.chi ∘
      (fun z' : ℝ => Work.Cyl.rhoP r z' / L)) z :=
    hchi.comp z ((Work.Cyl.hasDerivAt_rhoP_snd r z hr).div_const L).differentiableAt
  simpa [Function.comp_def] using h

/-! ## The product rule for the curried partials -/

/-- **The radial product rule** for `Work.Cyl.pdR`:
`∂_r(f·g) = (∂_rf)·g + f·(∂_rg)`. -/
lemma pdR_mul {f g : ℝ → ℝ → ℝ} {r z : ℝ}
    (hf : DifferentiableAt ℝ (fun r' => f r' z) r)
    (hg : DifferentiableAt ℝ (fun r' => g r' z) r) :
    Work.Cyl.pdR (fun r' z' => f r' z' * g r' z') r z
      = Work.Cyl.pdR f r z * g r z + f r z * Work.Cyl.pdR g r z := by
  simp only [Work.Cyl.pdR]
  rw [show (fun r' : ℝ => f r' z * g r' z) = (fun r' => f r' z) * (fun r' => g r' z) from rfl,
    deriv_mul hf hg]

/-- **The axial product rule** for `Work.Cyl.pdZ`:
`∂_z(f·g) = (∂_zf)·g + f·(∂_zg)`. -/
lemma pdZ_mul {f g : ℝ → ℝ → ℝ} {r z : ℝ}
    (hf : DifferentiableAt ℝ (fun z' => f r z') z)
    (hg : DifferentiableAt ℝ (fun z' => g r z') z) :
    Work.Cyl.pdZ (fun r' z' => f r' z' * g r' z') r z
      = Work.Cyl.pdZ f r z * g r z + f r z * Work.Cyl.pdZ g r z := by
  simp only [Work.Cyl.pdZ]
  rw [show (fun z' : ℝ => f r z' * g r z') = (fun z' => f r z') * (fun z' => g r z') from rfl,
    deriv_mul hf hg]

/-! ## The meridian residual of a cut field -/

/-- **The meridian residual of the radially cut field `χ(ρ/L)·W`.**  Since the cut-off factor
`χ(ρ/L)` does not depend on the time and depends on `(r,z)` only through `ρ`, the residual of the
product is the product of the residuals plus the explicit cut-off term
`(χ'(ρ/L)/L)·( (∂_zψ)(r/ρ) - (ψ/r + ∂_rψ)(z/ρ) )·W`.

This is the identity of the deficit cancellation of the G-route: at `W = W₀` (the uncut
self-similar vorticity) the bracket is the meridian form of the `K`-factor of the paper's cut-off,
cf. `Work.CoreResiduals.r1Deficit`. -/
theorem meridianResid_cut {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {W ψ : ℝ → ℝ → ℝ → ℝ} {r z t : ℝ} (hr : 0 < r)
    (hWr : DifferentiableAt ℝ (fun r' : ℝ => W r' z t) r)
    (hWz : DifferentiableAt ℝ (fun z' : ℝ => W r z' t) z)
    (hWt : DifferentiableAt ℝ (fun s : ℝ => W r z s) t) :
    Work.CoreResiduals.meridianResid
        (fun r z t => Work.Stability.chi (Work.Cyl.rhoP r z / P.L) * W r z t) ψ r z t
      = Work.Stability.chi (Work.Cyl.rhoP r z / P.L)
          * Work.CoreResiduals.meridianResid W ψ r z t
        + (deriv Work.Stability.chi (Work.Cyl.rhoP r z / P.L) / P.L)
            * (Work.Cyl.pdZ (fun r z => ψ r z t) r z * (r / Work.Cyl.rhoP r z)
              - (ψ r z t / r + Work.Cyl.pdR (fun r z => ψ r z t) r z)
                  * (z / Work.Cyl.rhoP r z))
            * W r z t := by
  have hWct : deriv (fun s : ℝ => Work.Stability.chi (Work.Cyl.rhoP r z / P.L) * W r z s) t
      = Work.Stability.chi (Work.Cyl.rhoP r z / P.L) * deriv (fun s : ℝ => W r z s) t :=
    deriv_const_mul _ hWt
  have hWcr : Work.Cyl.pdR
        (fun r' z' => Work.Stability.chi (Work.Cyl.rhoP r' z' / P.L) * W r' z' t) r z
      = Work.Cyl.pdR (fun r' z' => Work.Stability.chi (Work.Cyl.rhoP r' z' / P.L)) r z
          * W r z t
        + Work.Stability.chi (Work.Cyl.rhoP r z / P.L)
          * Work.Cyl.pdR (fun r' z' => W r' z' t) r z :=
    pdR_mul (differentiableAt_chi_rhoP_div_fst P.L r z hr) hWr
  have hWcz : Work.Cyl.pdZ
        (fun r' z' => Work.Stability.chi (Work.Cyl.rhoP r' z' / P.L) * W r' z' t) r z
      = Work.Cyl.pdZ (fun r' z' => Work.Stability.chi (Work.Cyl.rhoP r' z' / P.L)) r z
          * W r z t
        + Work.Stability.chi (Work.Cyl.rhoP r z / P.L)
          * Work.Cyl.pdZ (fun r' z' => W r' z' t) r z :=
    pdZ_mul (differentiableAt_chi_rhoP_div_snd P.L r z hr) hWz
  simp only [Work.CoreResiduals.meridianResid]
  rw [hWct, hWcr, hWcz, pdR_chi_rhoP_div P.L r z hr, pdZ_chi_rhoP_div P.L r z hr]
  ring

end Work.R1G
