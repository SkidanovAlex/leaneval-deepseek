/-
Copyright: work module for the Elgindi finite-time singularity project.

# `smoothOpen_linPart` — the linear part `𝓛_Γ^T` preserves finite-order smoothness
on the open quadrant

The operator of the `StrongEps` scheme,

  `𝓛_Γ^T(f) = 𝓛(f) − (2zΓ(θ)/(c(1+z)²))·L₁₂(f) − 𝕡(3 sin(2θ)∂_θf/(1+z))`

(`Work.Coercivity.LGammaT`) is a *pointwise* combination of

* `f` and `D_z f = z∂_z f` (the `C^n`-slots of the profile),
* the angular factor `Γ(θ) = (sin θcos²θ)^{α/3}` and the constant `c(α)`,
* the *radial* function `L₁₂(f)(z)`, smooth on `(0,∞)` by hypothesis,
* the radial function `D_θ f` and the *constant* `L₁₂(Transport f)(0)` (the latter is
  evaluated at `z = 0`, so it contributes only a constant to `𝕡`).

Hence, if `f` is `C^n` on the open quadrant for every `n` and `L₁₂(f)` is `C^n` on `(0,∞)`
for every `n`, then so is `𝓛_Γ^T(f)`: the only divisions by a non-constant are by
`1 + z ≠ 0` and by `c(α)`, and the latter is harmless because `x / c = x · c⁻¹` for a
*constant* `c` (no non-vanishing is needed).

The finite-order `D`-calculus on an open set (`∂_z`, `∂_θ` lower the order by one) is
re-established here as the four `private` helpers `pz_fin`/`Dz_fin`/`pth_fin`/`Dth_fin`,
so that this file's import cone stays inside the `StrongEps`/`Coercivity` chapters.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn)

/-! ## The finite-order `D`-calculus on an open set

`∂_z`, `∂_θ` lower the differentiability order by one, and `D_z`, `D_θ` are the products of
those with the smooth factors `z` and `sin(2θ)`.  These are the *finite-order* forms of the
calculus of `Work.FTS.LocData.SmoothChain`; they are repeated here (in the `StrongEps`
namespace, `private`) so that this module does not have to import the `LocData` chapter.
-/

/-- `∂_z` lowers the differentiability order by one on an open set. -/
private theorem pz_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by norm_num : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  exact hchain p hp

/-- `D_z` lowers the differentiability order by one on an open set. -/
private theorem Dz_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hpz := pz_fin hV h
  have hfun : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p) V :=
    contDiff_fst.contDiffOn.mul hpz
  refine hfun.congr (fun p hp => ?_)
  rfl

/-- `∂_θ` lowers the differentiability order by one on an open set. -/
private theorem pth_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by norm_num : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  exact hchain p hp

/-- `D_θ` lowers the differentiability order by one on an open set. -/
private theorem Dth_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hpth := pth_fin hV h
  have hsin : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hfun : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth G) p) V :=
    hsin.mul hpth
  refine hfun.congr (fun p hp => ?_)
  rfl

/-! ## The angular factor `Γ` -/

/-- `Γ(θ) = (sin θ·cos²θ)^{α/3}` is `C^n` on the open quadrant, for every `n` and every `α`:
the base is positive and smooth there and we take an arbitrary real power of it. -/
private theorem gam_smooth (α : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Quad := by
  have hbase : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2) Quad :=
    (((Real.contDiff_sin.comp contDiff_snd).mul
      ((Real.contDiff_cos.comp contDiff_snd).pow 2)).contDiffOn).of_le le_top
  have hpos : ∀ p ∈ Quad, 0 < Real.sin p.2 * Real.cos p.2 ^ 2 := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := mem_Quad.mp hp
    have hs : 0 < Real.sin p.2 :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
    positivity
  simpa only [Work.Spaces.Gam] using
    hbase.rpow_const_of_ne (fun p hp => ne_of_gt (hpos p hp))

/-! ## The main theorem -/

theorem smoothOpen_linPart {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    (hL12 : ∀ n : ℕ, ContDiffOn ℝ n (Work.Coercivity.L12f f) (Set.Ioi 0)) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Coercivity.LGammaT α f))
      Work.FTS.StrongEps.Quad := by
  intro n
  -- the open quadrant and the standing non-vanishing factor `1 + z`
  have hQ : IsOpen Quad := isOpen_Ioi.prod isOpen_Ioo
  have hden : ContDiffOn ℝ n (fun p : ℝ × ℝ => (1 : ℝ) + p.1) Quad :=
    contDiffOn_const.add contDiffOn_fst
  have h1z : ∀ p ∈ Quad, (1 : ℝ) + p.1 ≠ 0 := by
    intro p hp; have := (mem_Quad.mp hp).1; linarith
  -- the profile and its two first derivatives
  have hf0 : ContDiffOn ℝ n (Function.uncurry f) Quad := hf n
  have hDz : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz f)) Quad :=
    Dz_fin hQ (hf (n + 1))
  have hDth : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dth f)) Quad :=
    Dth_fin hQ (hf (n + 1))
  have hGam : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Quad := gam_smooth α n
  have hL12f : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Coercivity.L12f f p.1) Quad :=
    (hL12 n).comp contDiffOn_fst (fun p hp => (mem_Quad.mp hp).1)
  have hinv : ContDiffOn ℝ n (fun p : ℝ × ℝ => ((1 : ℝ) + p.1)⁻¹) Quad := hden.inv h1z
  -- the two rational coefficients, in the form in which `ContDiffOn` composition is easy
  have hcoef1 : ContDiffOn ℝ n
      (fun p : ℝ × ℝ =>
        2 * p.1 * Work.Spaces.Gam α p.2 * (Work.Spaces.c α)⁻¹ * ((1 + p.1)⁻¹) ^ 2) Quad :=
    (((contDiffOn_const.mul contDiffOn_fst).mul hGam).mul contDiffOn_const).mul (hinv.pow 2)
  have hcoef : ContDiffOn ℝ n
      (fun p : ℝ × ℝ =>
        2 * p.1 * Work.Spaces.Gam α p.2 / (Work.Spaces.c α * (1 + p.1) ^ 2)) Quad := by
    refine hcoef1.congr (fun p hp => ?_)
    have hz : (1 : ℝ) + p.1 ≠ 0 := h1z p hp
    field_simp
  have hproj1 : ContDiffOn ℝ n
      (fun p : ℝ × ℝ =>
        Work.Spaces.Gam α p.2 * (Work.Spaces.c α)⁻¹
          * (2 * p.1 ^ 2 * ((1 + p.1)⁻¹) ^ 3)
          * (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) Quad :=
    ((hGam.mul contDiffOn_const).mul
      ((contDiffOn_const.mul (contDiffOn_fst.pow 2)).mul (hinv.pow 3))).mul contDiffOn_const
  have hproj : ContDiffOn ℝ n
      (fun p : ℝ × ℝ =>
        (Work.Spaces.Gam α p.2 / Work.Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)
          * (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) Quad := by
    refine hproj1.congr (fun p hp => ?_)
    have hz : (1 : ℝ) + p.1 ≠ 0 := h1z p hp
    field_simp
  -- the six summands of the full expression
  have hC : ContDiffOn ℝ n (fun p : ℝ × ℝ => 2 * Function.uncurry f p / (1 + p.1)) Quad :=
    (contDiffOn_const.mul hf0).div hden h1z
  have hD : ContDiffOn ℝ n
      (fun p : ℝ × ℝ =>
        2 * p.1 * Work.Spaces.Gam α p.2 / (Work.Spaces.c α * (1 + p.1) ^ 2)
          * Work.Coercivity.L12f f p.1) Quad :=
    hcoef.mul hL12f
  have hE : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => 3 * Function.uncurry (Work.Spaces.Dth f) p / (1 + p.1)) Quad :=
    (contDiffOn_const.mul hDth).div hden h1z
  -- the definitional unfolding of `𝓛_Γ^T` as a function of the point `(z,θ)`
  have hG : ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      ((Function.uncurry f p + Function.uncurry (Work.Spaces.Dz f) p)
        - 2 * Function.uncurry f p / (1 + p.1)
        - (2 * p.1 * Work.Spaces.Gam α p.2 / (Work.Spaces.c α * (1 + p.1) ^ 2)
            * Work.Coercivity.L12f f p.1))
      - (3 * Function.uncurry (Work.Spaces.Dth f) p / (1 + p.1)
        - ((Work.Spaces.Gam α p.2 / Work.Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0))) Quad :=
    (((hf0.add hDz).sub hC).sub hD).sub (hE.sub hproj)
  refine hG.congr (fun p hp => ?_)
  rfl

end Work.FTS.StrongEps
