import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.Defs
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.Transfer
import Submission.Work.Cyl.Elliptic
import Submission.Work.Cyl.FieldDeriv
import Submission.Work.Elliptic.pdRR_add_pdZZ_comp_polar
import Submission.Work.Elliptic.first_derivs_mul_pow_rpow
import Submission.Work.Elliptic.pdRR_mul_pow_rpow
import Submission.Work.Elliptic.pth_tan_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The polar change of variables for the axisymmetric Biot--Savart operator

This file proves `Work.Elliptic.cylOp_polar`: with `ρ = rhoP r z = √(r²+z²)`,
`θ = thetaP r z = arctan (z/r)` and `ψ(r,z) = ρ² Ψ (ρ^α, θ)`, the cylindrical elliptic
operator `cylOp` of (3dBSL) reproduces the operator `bslOp` of (PolarBSL) in the self-similar
variables `R = ρ^α`, `θ`.

The proof follows the paper's computation line by line:

* `pdRR_add_pdZZ_comp_polar` (delegated): the Cartesian Laplacian of `(r,z) ↦ F (ρ r z) (θ r z)`
  is the polar Laplacian `F_ρρ + F_ρ/ρ + F_θθ/ρ²`;
* `first_derivs_mul_pow_rpow`, `pdRR_mul_pow_rpow` (delegated): the first and second `p`-derivatives
  of `(p,q) ↦ p² Ψ (p^α) q`;
* `Work.Cyl.pdR_comp_polar_rho` (existing): the radial derivative of `F ∘ (ρ,θ)`;
* `pth_tan_mul` (delegated): the angular derivative of `tan θ · Ψ`.

Only the pointwise algebra of the final step is done here.
-/

noncomputable section

open scoped Real Topology

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## Slice derivatives of the polar coordinates in the radial variable -/

private lemma hasDerivAt_rhoP_fst (r z : ℝ) (hr : 0 < r) :
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

private lemma hasDerivAt_thetaP_fst (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.thetaP r' z) (-z / Work.Cyl.rhoP r z ^ 2) r := by
  have hdiv : HasDerivAt (fun r' : ℝ => z / r') (-z / r ^ 2) r := by
    have h := (hasDerivAt_const (x := r) z).div (hasDerivAt_id r) (ne_of_gt hr)
    have hfun : ((fun x : ℝ => z) / id : ℝ → ℝ) = fun r' => z / r' := by
      funext x; simp [Pi.div_apply]
    rw [hfun] at h
    convert h using 1
    simp
  have h := hdiv.arctan
  have hfun : (fun r' : ℝ => Work.Cyl.thetaP r' z) = fun r' => Real.arctan (z / r') := by
    funext r'; rw [Work.Cyl.thetaP]
  rw [hfun]
  convert h using 1
  rw [Work.Cyl.rhoP]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

/-! ## The partial derivatives of a `C²` function are differentiable -/

private theorem diffAt2_pdR_of_contDiffAt_two (f : ℝ → ℝ → ℝ) (r z : ℝ)
    (h : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (r, z)) :
    Work.Cyl.DiffAt2 (Work.Cyl.pdR f) r z := by
  show DifferentiableAt ℝ (fun p : ℝ × ℝ => Work.Cyl.pdR f p.1 p.2) (r, z)
  have hev : ∀ᶠ p in 𝓝 ((r, z) : ℝ × ℝ),
      DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) p :=
    (h.eventually (by simp)).mono (fun p hp => hp.differentiableAt (by simp))
  have heq : (fun p : ℝ × ℝ => Work.Cyl.pdR f p.1 p.2) =ᶠ[𝓝 (r, z)]
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) p (1, 0)) := by
    filter_upwards [hev] with p hp
    exact (Work.Cyl.fderiv_prod_apply_fst f p.1 p.2 hp).symm
  rw [Filter.EventuallyEq.differentiableAt_iff heq]
  have hG : DifferentiableAt ℝ (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2)) (r, z) :=
    (h.fderiv_right_succ).differentiableAt_one
  exact hG.clm_apply (differentiableAt_const ((1, 0) : ℝ × ℝ))

private theorem diffAt2_pdZ_of_contDiffAt_two (f : ℝ → ℝ → ℝ) (r z : ℝ)
    (h : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (r, z)) :
    Work.Cyl.DiffAt2 (Work.Cyl.pdZ f) r z := by
  show DifferentiableAt ℝ (fun p : ℝ × ℝ => Work.Cyl.pdZ f p.1 p.2) (r, z)
  have hev : ∀ᶠ p in 𝓝 ((r, z) : ℝ × ℝ),
      DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) p :=
    (h.eventually (by simp)).mono (fun p hp => hp.differentiableAt (by simp))
  have heq : (fun p : ℝ × ℝ => Work.Cyl.pdZ f p.1 p.2) =ᶠ[𝓝 (r, z)]
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) p (0, 1)) := by
    filter_upwards [hev] with p hp
    exact (Work.Cyl.fderiv_prod_apply_snd f p.1 p.2 hp).symm
  rw [Filter.EventuallyEq.differentiableAt_iff heq]
  have hG : DifferentiableAt ℝ (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2)) (r, z) :=
    (h.fderiv_right_succ).differentiableAt_one
  exact hG.clm_apply (differentiableAt_const ((0, 1) : ℝ × ℝ))

/-! ## The two-variable function `(p,q) ↦ p² Ψ (p^α) q` is `C²` -/

private theorem contDiffAt_uncurry_mul_pow (Ψ : ℝ → ℝ → ℝ) (α ρ θ : ℝ) (hρ : 0 < ρ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (ρ ^ α, θ)) :
    ContDiffAt ℝ 2 (Function.uncurry (fun p q => p ^ 2 * Ψ (p ^ α) q)) (ρ, θ) := by
  show ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.1 ^ 2 * Ψ (y.1 ^ α) y.2) (ρ, θ)
  have hsq : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.1 ^ 2) (ρ, θ) := by fun_prop
  have hpow : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.1 ^ α) (ρ, θ) := by
    have h1 : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.1) (ρ, θ) := contDiffAt_fst
    have hr : ContDiffAt ℝ 2 (fun x : ℝ => x ^ α) ρ :=
      Real.contDiffAt_rpow_const (x := ρ) (p := α) (n := 2) (Or.inl (ne_of_gt hρ))
    have h := hr.comp (ρ, θ) h1
    simpa [Function.comp_def] using h
  have hpsi : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => Ψ (y.1 ^ α) y.2) (ρ, θ) := by
    have hpair : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => (y.1 ^ α, y.2)) (ρ, θ) :=
      hpow.prodMk (contDiffAt_snd : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.2) (ρ, θ))
    have h := hΨ.comp (ρ, θ) hpair
    simpa [Function.comp_def, Function.uncurry_apply_pair] using h
  exact hsq.mul hpsi

/-! ## The polar form of `tan` -/

private lemma tan_thetaP {r : ℝ} (hr : 0 < r) (z : ℝ) :
    Real.tan (Work.Cyl.thetaP r z) = z / r := by
  rw [Real.tan_eq_sin_div_cos, Work.Cyl.sin_thetaP hr z, Work.Cyl.cos_thetaP hr z]
  field_simp [Work.Cyl.rhoP_ne_zero hr z]

end Work.Elliptic

namespace Work.Elliptic

theorem cylOp_polar (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (Work.Cyl.rhoP r z ^ α, Work.Cyl.thetaP r z)) :
    Work.Cyl.cylOp (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z
      = Work.Elliptic.bslOp α Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := by
  have hρpos : 0 < (Work.Cyl.rhoP r z) := Work.Cyl.rhoP_pos hr z
  have hρne : (Work.Cyl.rhoP r z) ≠ 0 := ne_of_gt hρpos
  have hcosne : Real.cos (Work.Cyl.thetaP r z) ≠ 0 := ne_of_gt (Work.Cyl.cos_thetaP_pos hr z)
  -- the model function `(p,q) ↦ p²Ψ(p^α,q)` is `C²` and its partials are differentiable
  have hF2 : ContDiffAt ℝ 2 (Function.uncurry (fun p q => p ^ 2 * Ψ (p ^ α) q)) ((Work.Cyl.rhoP r z), (Work.Cyl.thetaP r z)) :=
    contDiffAt_uncurry_mul_pow Ψ α _ _ hρpos hΨ
  have hF2' : Work.Cyl.DiffAt2 (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) := hF2.differentiableAt (by simp)
  have hpdRF : Work.Cyl.DiffAt2 (Work.Cyl.pdR (fun p q => p ^ 2 * Ψ (p ^ α) q)) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) :=
    diffAt2_pdR_of_contDiffAt_two _ _ _ hF2
  have hpdZF : Work.Cyl.DiffAt2 (Work.Cyl.pdZ (fun p q => p ^ 2 * Ψ (p ^ α) q)) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) :=
    diffAt2_pdZ_of_contDiffAt_two _ _ _ hF2
  have hpdRΨ : Work.Cyl.DiffAt2 (Work.Cyl.pdR Ψ) (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) :=
    diffAt2_pdR_of_contDiffAt_two Ψ _ _ hΨ
  -- the polar Laplacian and the radial derivative
  have hLap : Work.Cyl.pdRR (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z + Work.Cyl.pdZZ (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z
      = Work.Cyl.pdRR (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) + Work.Cyl.pdR (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) / (Work.Cyl.rhoP r z)
        + Work.Cyl.pdZZ (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) / (Work.Cyl.rhoP r z) ^ 2 := by
    exact pdRR_add_pdZZ_comp_polar (fun p q => p ^ 2 * Ψ (p ^ α) q) r z hr hF2 hpdRF hpdZF
  have hDr : Work.Cyl.pdR (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z
      = Real.cos (Work.Cyl.thetaP r z) * Work.Cyl.pdR (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)
        - Real.sin (Work.Cyl.thetaP r z) / (Work.Cyl.rhoP r z) * Work.Cyl.pdZ (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) := by
    exact Work.Cyl.pdR_comp_polar_rho (fun p q => p ^ 2 * Ψ (p ^ α) q) r z hr hF2'
  -- the partial derivatives of the model function
  have hD1 : Work.Cyl.pdR (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)
      = 2 * (Work.Cyl.rhoP r z) * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) + α * (Work.Cyl.rhoP r z) ^ (α + 1) * Work.Cyl.pdR Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := by
    exact (first_derivs_mul_pow_rpow Ψ α (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) hρpos hΨ).1
  have hD2 : Work.Cyl.pdZ (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) = (Work.Cyl.rhoP r z) ^ 2 * Work.Cyl.pdZ Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := by
    exact (first_derivs_mul_pow_rpow Ψ α (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) hρpos hΨ).2.1
  have hD3 : Work.Cyl.pdZZ (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) = (Work.Cyl.rhoP r z) ^ 2 * Work.Cyl.pdZZ Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := by
    exact (first_derivs_mul_pow_rpow Ψ α (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) hρpos hΨ).2.2
  have hD4 : Work.Cyl.pdRR (fun p q => p ^ 2 * Ψ (p ^ α) q) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)
      = 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) + α * (α + 3) * (Work.Cyl.rhoP r z ^ α) * Work.Cyl.pdR Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) + α ^ 2 * (Work.Cyl.rhoP r z) ^ (2 * α) * Work.Cyl.pdRR Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := by
    exact pdRR_mul_pow_rpow Ψ α (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) hρpos hΨ hpdRΨ
  -- the angular derivative of `tan θ · Ψ`
  have hslice : DifferentiableAt ℝ (fun θ' => Ψ (Work.Cyl.rhoP r z ^ α) θ') (Work.Cyl.thetaP r z) :=
    Work.Cyl.differentiableAt_slice_snd Ψ _ _ (hΨ.differentiableAt (by simp))
  have htan : Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)
      = Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) / Real.cos (Work.Cyl.thetaP r z) ^ 2 + Real.tan (Work.Cyl.thetaP r z) * Work.Cyl.pdZ Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := by
    exact pth_tan_mul Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) hcosne hslice
  -- the `pz`/`pdR` dictionary is definitional
  have hId1 : Work.Spaces.pzIter 2 Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) = Work.Cyl.pdRR Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := rfl
  have hId2 : Work.Spaces.pz Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) = Work.Cyl.pdR Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := rfl
  have hId3 : Work.Spaces.pthIter 2 Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) = Work.Cyl.pdZZ Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := rfl
  -- trig and `rpow` rewrites
  have hcosθ : Real.cos (Work.Cyl.thetaP r z) = r / (Work.Cyl.rhoP r z) := Work.Cyl.cos_thetaP hr z
  have hsinθ : Real.sin (Work.Cyl.thetaP r z) = z / (Work.Cyl.rhoP r z) := Work.Cyl.sin_thetaP hr z
  have htanθ : Real.tan (Work.Cyl.thetaP r z) = z / r := tan_thetaP hr z
  have hpow1 : (Work.Cyl.rhoP r z) ^ (α + 1) = (Work.Cyl.rhoP r z ^ α) * (Work.Cyl.rhoP r z) := Real.rpow_add_one hρne α
  have hpow2 : (Work.Cyl.rhoP r z) ^ (2 * α) = (Work.Cyl.rhoP r z ^ α) ^ 2 := by
    rw [show (2 : ℝ) * α = α * 2 by ring, Real.rpow_mul hρpos.le, Real.rpow_two]
  -- the computation
  rw [show Work.Cyl.cylOp (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z
      = -Work.Cyl.pdRR (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z - Work.Cyl.pdZZ (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z
        - Work.Cyl.pdR (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z / r + (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z / r ^ 2 from rfl]
  rw [Work.Elliptic.bslOp_apply]
  simp only [Work.Elliptic.Lzero]
  rw [show -Work.Cyl.pdRR (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z - Work.Cyl.pdZZ (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z
      = -(Work.Cyl.pdRR (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z + Work.Cyl.pdZZ (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) r z) by ring, hLap, hDr,
    hD1, hD2, hD3, hD4, hId1, hId2, hId3, htan, hcosθ, hsinθ, htanθ, hpow1, hpow2]
  field_simp
  ring

end Work.Elliptic
