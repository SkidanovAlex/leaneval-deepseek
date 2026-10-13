import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.FieldDeriv
import Submission.Work.Cyl.pdR_comp_polar_rho
import Submission.Work.Cyl.pdZ_comp_polar_rho

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-!
# The polar Laplacian identity for `G(r,z) = F(ρ(r,z), θ(r,z))`

With `ρ(r,z) = √(r²+z²)` and `θ(r,z) = arctan(z/r)` (`r > 0`), the Cartesian Laplacian of the
composite `G = F ∘ (ρ,θ)` is the "polar" Laplacian of `F`:

`∂_rr G + ∂_zz G = F_{ρρ} + F_ρ/ρ + F_{θθ}/ρ²`.

The proof expands the two second derivatives by the chain rule.  Every occurrence of `cos θ` and
`sin θ` is rewritten as `r/ρ` and `z/ρ`, and the two expansions are added; the mixed terms
`F_{ρθ}, F_{θρ}` and the first order term `F_θ` cancel, while `ρ_r² + ρ_z² = 1`,
`θ_r² + θ_z² = 1/ρ²` and `ρ_rr + ρ_zz = 1/ρ` give the remaining coefficients.
-/

namespace Work.Elliptic

open Work.Cyl
open Filter
open scoped Topology

/-! ## Derivatives of the polar coordinate functions in the radial variable -/

/-- `r ↦ ρ(r,z) = √(r²+z²)` has derivative `r/ρ` in the radial variable. -/
theorem hasDerivAt_rhoP_fst' (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => rhoP r' z) (r / rhoP r z) r := by
  have hsq : HasDerivAt (fun r' : ℝ => r' ^ 2 + z ^ 2) (2 * r) r := by
    simpa using ((hasDerivAt_pow 2 r).add_const (z ^ 2))
  have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  have h := hsq.sqrt hne
  have hval : (2 * r) / (2 * Real.sqrt (r ^ 2 + z ^ 2)) = r / rhoP r z := by
    rw [rhoP]; field_simp
  rw [hval] at h
  exact h

/-- `r ↦ θ(r,z) = arctan(z/r)` has derivative `-z/ρ²` in the radial variable. -/
theorem hasDerivAt_thetaP_fst' (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => thetaP r' z) (-z / rhoP r z ^ 2) r := by
  have hdiv : HasDerivAt (fun r' : ℝ => z / r') (-z / r ^ 2) r := by
    have h := (hasDerivAt_const (x := r) z).div (hasDerivAt_id r) (ne_of_gt hr)
    have hfun : ((fun x : ℝ => z) / id : ℝ → ℝ) = fun r' => z / r' := by
      funext x; simp [Pi.div_apply]
    rw [hfun] at h
    convert h using 1
    simp
  have h := hdiv.arctan
  have hfun : (fun r' : ℝ => thetaP r' z) = fun r' => Real.arctan (z / r') := by
    funext r'; rw [thetaP]
  rw [hfun]
  convert h using 1
  rw [rhoP]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

/-! ## Eventual differentiability of `F` along a continuous curve -/

/-- If `F` is `C²` at `(R t₀, Z t₀)` and `R, Z` are continuous at `t₀`, then `F` is differentiable
at `(R s, Z s)` for all `s` near `t₀`. -/
theorem eventually_diffAt2_comp (F : ℝ → ℝ → ℝ) (R Z : ℝ → ℝ) (t₀ : ℝ)
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (R t₀, Z t₀))
    (hR : ContinuousAt R t₀) (hZ : ContinuousAt Z t₀) :
    ∀ᶠ s in 𝓝 t₀, DiffAt2 F (R s) (Z s) := by
  have h1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (R t₀, Z t₀), DifferentiableAt ℝ (Function.uncurry F) p := by
    obtain ⟨u, hu_open, hu_mem, hu⟩ := hF.contDiffOn' le_rfl (fun h => by simp at h)
    have hu' : ContDiffOn ℝ 2 (Function.uncurry F) u := by simpa using hu
    filter_upwards [hu_open.mem_nhds hu_mem] with p hp
    exact (hu'.differentiableOn (by norm_num)).differentiableAt (hu_open.mem_nhds hp)
  have hcont : ContinuousAt (fun s : ℝ => (R s, Z s)) t₀ := hR.prodMk hZ
  exact hcont.eventually h1

/-! ## The two second-order chain rules -/

/-- Chain rule in the radial variable: differentiating
`r ↦ cos θ(r,z) · F_ρ - (sin θ(r,z)/ρ(r,z)) · F_θ`
(the expression for `∂_r (F ∘ (ρ,θ))` given by `pdR_comp_polar_rho`). -/
theorem deriv_pdR_comp_polar (F : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hpdR : DiffAt2 (pdR F) (rhoP r z) (thetaP r z))
    (hpdZ : DiffAt2 (pdZ F) (rhoP r z) (thetaP r z)) :
    deriv (fun s => Real.cos (thetaP s z) * pdR F (rhoP s z) (thetaP s z)
             - Real.sin (thetaP s z) / rhoP s z * pdZ F (rhoP s z) (thetaP s z)) r
      = z^2/(rhoP r z)^3 * pdR F (rhoP r z) (thetaP r z)
        + r^2/(rhoP r z)^2 * pdRR F (rhoP r z) (thetaP r z)
        - r*z/(rhoP r z)^3 * pdZR F (rhoP r z) (thetaP r z)
        + 2*r*z/(rhoP r z)^4 * pdZ F (rhoP r z) (thetaP r z)
        - r*z/(rhoP r z)^3 * pdRZ F (rhoP r z) (thetaP r z)
        + z^2/(rhoP r z)^4 * pdZZ F (rhoP r z) (thetaP r z) := by
  have hρne : rhoP r z ≠ 0 := rhoP_ne_zero hr z
  have hρ : HasDerivAt (fun s : ℝ => rhoP s z) (r / rhoP r z) r :=
    hasDerivAt_rhoP_fst' r z hr
  have hθ : HasDerivAt (fun s : ℝ => thetaP s z) (-z / rhoP r z ^ 2) r :=
    hasDerivAt_thetaP_fst' r z hr
  have hc : HasDerivAt (fun s : ℝ => Real.cos (thetaP s z))
      (Real.sin (thetaP r z) * (z / rhoP r z ^ 2)) r := by
    have h := (Real.hasDerivAt_cos (thetaP r z)).comp r hθ
    convert h using 1
    · rfl
    · ring
  have hs : HasDerivAt (fun s : ℝ => Real.sin (thetaP s z))
      (-Real.cos (thetaP r z) * (z / rhoP r z ^ 2)) r := by
    have h := (Real.hasDerivAt_sin (thetaP r z)).comp r hθ
    convert h using 1
    · rfl
    · ring
  have hP : HasDerivAt (fun s : ℝ => pdR F (rhoP s z) (thetaP s z))
      (pdRR F (rhoP r z) (thetaP r z) * (r / rhoP r z)
        + pdZR F (rhoP r z) (thetaP r z) * (-z / rhoP r z ^ 2)) r :=
    hasDerivAt_comp_two (pdR F) (fun s : ℝ => rhoP s z) (fun s : ℝ => thetaP s z)
      (r / rhoP r z) (-z / rhoP r z ^ 2) r hpdR hρ hθ
  have hQ : HasDerivAt (fun s : ℝ => pdZ F (rhoP s z) (thetaP s z))
      (pdRZ F (rhoP r z) (thetaP r z) * (r / rhoP r z)
        + pdZZ F (rhoP r z) (thetaP r z) * (-z / rhoP r z ^ 2)) r :=
    hasDerivAt_comp_two (pdZ F) (fun s : ℝ => rhoP s z) (fun s : ℝ => thetaP s z)
      (r / rhoP r z) (-z / rhoP r z ^ 2) r hpdZ hρ hθ
  have hΦ : HasDerivAt (fun s => Real.cos (thetaP s z) * pdR F (rhoP s z) (thetaP s z)
             - Real.sin (thetaP s z) / rhoP s z * pdZ F (rhoP s z) (thetaP s z)) _ r :=
    (hc.mul hP).sub ((hs.div hρ hρne).mul hQ)
  rw [hΦ.deriv]
  simp only [Pi.div_apply, Function.comp_apply]
  rw [cos_thetaP hr z, sin_thetaP hr z]
  field_simp
  ring

/-- Chain rule in the axial variable: differentiating
`z ↦ sin θ(r,z) · F_ρ + (cos θ(r,z)/ρ(r,z)) · F_θ`
(the expression for `∂_z (F ∘ (ρ,θ))` given by `pdZ_comp_polar_rho`). -/
theorem deriv_pdZ_comp_polar (F : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hpdR : DiffAt2 (pdR F) (rhoP r z) (thetaP r z))
    (hpdZ : DiffAt2 (pdZ F) (rhoP r z) (thetaP r z)) :
    deriv (fun t => Real.sin (thetaP r t) * pdR F (rhoP r t) (thetaP r t)
             + Real.cos (thetaP r t) / rhoP r t * pdZ F (rhoP r t) (thetaP r t)) z
      = r^2/(rhoP r z)^3 * pdR F (rhoP r z) (thetaP r z)
        + z^2/(rhoP r z)^2 * pdRR F (rhoP r z) (thetaP r z)
        + r*z/(rhoP r z)^3 * pdZR F (rhoP r z) (thetaP r z)
        - 2*r*z/(rhoP r z)^4 * pdZ F (rhoP r z) (thetaP r z)
        + r*z/(rhoP r z)^3 * pdRZ F (rhoP r z) (thetaP r z)
        + r^2/(rhoP r z)^4 * pdZZ F (rhoP r z) (thetaP r z) := by
  have hρne : rhoP r z ≠ 0 := rhoP_ne_zero hr z
  have hρ : HasDerivAt (fun t : ℝ => rhoP r t) (z / rhoP r z) z := hasDerivAt_rhoP_snd r z hr
  have hθ : HasDerivAt (fun t : ℝ => thetaP r t) (r / rhoP r z ^ 2) z :=
    hasDerivAt_thetaP_snd r z hr
  have hs := (Real.hasDerivAt_sin (thetaP r z)).comp z hθ
  have hc := (Real.hasDerivAt_cos (thetaP r z)).comp z hθ
  have hP : HasDerivAt (fun t : ℝ => pdR F (rhoP r t) (thetaP r t))
      (pdRR F (rhoP r z) (thetaP r z) * (z / rhoP r z)
        + pdZR F (rhoP r z) (thetaP r z) * (r / rhoP r z ^ 2)) z :=
    hasDerivAt_comp_two (pdR F) (fun t : ℝ => rhoP r t) (fun t : ℝ => thetaP r t)
      (z / rhoP r z) (r / rhoP r z ^ 2) z hpdR hρ hθ
  have hQ : HasDerivAt (fun t : ℝ => pdZ F (rhoP r t) (thetaP r t))
      (pdRZ F (rhoP r z) (thetaP r z) * (z / rhoP r z)
        + pdZZ F (rhoP r z) (thetaP r z) * (r / rhoP r z ^ 2)) z :=
    hasDerivAt_comp_two (pdZ F) (fun t : ℝ => rhoP r t) (fun t : ℝ => thetaP r t)
      (z / rhoP r z) (r / rhoP r z ^ 2) z hpdZ hρ hθ
  have hΦ : HasDerivAt (fun t => Real.sin (thetaP r t) * pdR F (rhoP r t) (thetaP r t)
             + Real.cos (thetaP r t) / rhoP r t * pdZ F (rhoP r t) (thetaP r t)) _ z :=
    (hs.mul hP).add ((hc.div hρ hρne).mul hQ)
  rw [hΦ.deriv]
  simp only [Pi.div_apply, Function.comp_apply]
  rw [cos_thetaP hr z, sin_thetaP hr z]
  field_simp
  ring

/-! ## The second derivatives of `G = F ∘ (ρ,θ)` -/

/-- `∂_rr (F ∘ (ρ,θ))` expanded by the chain rule. -/
theorem pdRR_comp_polar (F : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (rhoP r z, thetaP r z))
    (hpdR : DiffAt2 (pdR F) (rhoP r z) (thetaP r z))
    (hpdZ : DiffAt2 (pdZ F) (rhoP r z) (thetaP r z)) :
    pdRR (fun r' z' => F (rhoP r' z') (thetaP r' z')) r z
      = z^2/(rhoP r z)^3 * pdR F (rhoP r z) (thetaP r z)
        + r^2/(rhoP r z)^2 * pdRR F (rhoP r z) (thetaP r z)
        - r*z/(rhoP r z)^3 * pdZR F (rhoP r z) (thetaP r z)
        + 2*r*z/(rhoP r z)^4 * pdZ F (rhoP r z) (thetaP r z)
        - r*z/(rhoP r z)^3 * pdRZ F (rhoP r z) (thetaP r z)
        + z^2/(rhoP r z)^4 * pdZZ F (rhoP r z) (thetaP r z) := by
  have hev : (fun s => pdR (fun r' z' => F (rhoP r' z') (thetaP r' z')) s z)
      =ᶠ[𝓝 r] (fun s => Real.cos (thetaP s z) * pdR F (rhoP s z) (thetaP s z)
             - Real.sin (thetaP s z) / rhoP s z * pdZ F (rhoP s z) (thetaP s z)) := by
    filter_upwards [eventually_diffAt2_comp F (fun s => rhoP s z) (fun s => thetaP s z) r hF
        (hasDerivAt_rhoP_fst' r z hr).continuousAt
        (hasDerivAt_thetaP_fst' r z hr).continuousAt,
      eventually_gt_nhds hr] with s hsF hsr
    exact pdR_comp_polar_rho F s z hsr hsF
  show deriv (fun r' => pdR (fun r' z' => F (rhoP r' z') (thetaP r' z')) r' z) r = _
  rw [hev.deriv_eq]
  exact deriv_pdR_comp_polar F r z hr hpdR hpdZ

/-- `∂_zz (F ∘ (ρ,θ))` expanded by the chain rule. -/
theorem pdZZ_comp_polar (F : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (rhoP r z, thetaP r z))
    (hpdR : DiffAt2 (pdR F) (rhoP r z) (thetaP r z))
    (hpdZ : DiffAt2 (pdZ F) (rhoP r z) (thetaP r z)) :
    pdZZ (fun r' z' => F (rhoP r' z') (thetaP r' z')) r z
      = r^2/(rhoP r z)^3 * pdR F (rhoP r z) (thetaP r z)
        + z^2/(rhoP r z)^2 * pdRR F (rhoP r z) (thetaP r z)
        + r*z/(rhoP r z)^3 * pdZR F (rhoP r z) (thetaP r z)
        - 2*r*z/(rhoP r z)^4 * pdZ F (rhoP r z) (thetaP r z)
        + r*z/(rhoP r z)^3 * pdRZ F (rhoP r z) (thetaP r z)
        + r^2/(rhoP r z)^4 * pdZZ F (rhoP r z) (thetaP r z) := by
  have hev : (fun s => pdZ (fun r' z' => F (rhoP r' z') (thetaP r' z')) r s)
      =ᶠ[𝓝 z] (fun t => Real.sin (thetaP r t) * pdR F (rhoP r t) (thetaP r t)
             + Real.cos (thetaP r t) / rhoP r t * pdZ F (rhoP r t) (thetaP r t)) := by
    filter_upwards [eventually_diffAt2_comp F (fun t => rhoP r t) (fun t => thetaP r t) z hF
        (hasDerivAt_rhoP_snd r z hr).continuousAt
        (hasDerivAt_thetaP_snd r z hr).continuousAt] with t htF
    exact pdZ_comp_polar_rho F r t hr htF
  show deriv (fun z' => pdZ (fun r' z' => F (rhoP r' z') (thetaP r' z')) r z') z = _
  rw [hev.deriv_eq]
  exact deriv_pdZ_comp_polar F r z hr hpdR hpdZ

/-! ## The algebraic step -/

/-- The two second-order expansions add up to the polar Laplacian of `F`. -/
theorem pdRR_add_pdZZ_expansions (A B C D E G r z ρ : ℝ) (hρ : ρ ≠ 0) (h2 : ρ ^ 2 = r ^ 2 + z ^ 2) :
    (z^2/ρ^3 * A + r^2/ρ^2 * B - r*z/ρ^3 * C + 2*r*z/ρ^4 * D - r*z/ρ^3 * E + z^2/ρ^4 * G)
      + (r^2/ρ^3 * A + z^2/ρ^2 * B + r*z/ρ^3 * C - 2*r*z/ρ^4 * D + r*z/ρ^3 * E + r^2/ρ^4 * G)
      = B + A/ρ + G/ρ^2 := by
  field_simp
  rw [h2]
  ring

theorem pdRR_add_pdZZ_comp_polar (F : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (Work.Cyl.rhoP r z, Work.Cyl.thetaP r z))
    (hpdR : Work.Cyl.DiffAt2 (Work.Cyl.pdR F) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z))
    (hpdZ : Work.Cyl.DiffAt2 (Work.Cyl.pdZ F) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdRR (fun r' z' => F (Work.Cyl.rhoP r' z') (Work.Cyl.thetaP r' z')) r z
      + Work.Cyl.pdZZ (fun r' z' => F (Work.Cyl.rhoP r' z') (Work.Cyl.thetaP r' z')) r z
      = Work.Cyl.pdRR F (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)
        + Work.Cyl.pdR F (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) / Work.Cyl.rhoP r z
        + Work.Cyl.pdZZ F (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) / (Work.Cyl.rhoP r z) ^ 2 := by
  rw [pdRR_comp_polar F r z hr hF hpdR hpdZ, pdZZ_comp_polar F r z hr hF hpdR hpdZ]
  exact pdRR_add_pdZZ_expansions (pdR F (rhoP r z) (thetaP r z)) (pdRR F (rhoP r z) (thetaP r z))
    (pdZR F (rhoP r z) (thetaP r z)) (pdZ F (rhoP r z) (thetaP r z))
    (pdRZ F (rhoP r z) (thetaP r z)) (pdZZ F (rhoP r z) (thetaP r z)) r z (rhoP r z)
    (rhoP_ne_zero hr z) (rhoP_sq r z)

end Work.Elliptic
