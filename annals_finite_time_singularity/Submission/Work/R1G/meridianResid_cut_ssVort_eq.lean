/-
# `Work.R1G.meridianResid_cut_ssVort_eq`

The pointwise meridian residual identity for the **cut self-similar pair**.  Combining
`Work.R1G.meridianResid_cut` (the residual of a radially cut field `χ(ρ/L)·W` in terms of the
residual of `W` plus the explicit cut-off term) with `Work.R1G.meridianResid_ssVort_eq` (the
residual of the *uncut* self-similar pair `(ssVort p λ F, ssPsi p λ Φ)`), the meridian residual of
the cut self-similar vorticity is

  `χ(ρ/L)·(2λ²)⁻¹·( 2κ·(F + D_zF) + UVR p F Φ )  +  (χ'(ρ/L)/L)·K·ssVort`,

`K = (∂_zψ)(r/ρ) - (ψ/r + ∂_rψ)(z/ρ)` being the meridian `K`-factor of the cut-off term, evaluated
at `ψ = ssPsi p λ Φ`.  This is the identity of the G-route's deficit cancellation.

The only extra input beyond the two cited identities is the differentiability of the self-similar
vorticity `ssVort p λ F` in each variable, which the helper lemmas
(`differentiableAt_ssVort_fst`, `_snd`, `_time`) supply from the `ContDiffAt` hypotheses on `F`
through the two-variable chain rule `Work.Cyl.hasDerivAt_comp_two`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.R1G.Defs
import Submission.Work.R1G.meridianResid_cut
import Submission.Work.R1G.meridianResid_ssVort_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.R1G

/-! ## Derivatives of `ρ^p/c` in the radial variable -/

/-- The radial counterpart of `Work.Cyl.hasDerivAt_rhoP_rpow_div_snd`:
`r' ↦ ρ(r',z)^p/c` has derivative `p·(ρ^p/c)·(r/ρ²)` at `r > 0`. -/
lemma hasDerivAt_rhoP_rpow_div_fst (r z p c : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p / c)
      (p * (Work.Cyl.rhoP r z ^ p / c) * (r / Work.Cyl.rhoP r z ^ 2)) r := by
  have hne : Work.Cyl.rhoP r z ≠ 0 := Work.Cyl.rhoP_ne_zero hr z
  have hρp : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p)
      (p * Work.Cyl.rhoP r z ^ p * (r / Work.Cyl.rhoP r z ^ 2)) r := by
    have h := (Real.hasDerivAt_rpow_const (x := Work.Cyl.rhoP r z) (p := p) (Or.inl hne)).comp r
      (hasDerivAt_rhoP_fst' r z hr)
    have hfun : ((fun x : ℝ => x ^ p) ∘ fun r' => Work.Cyl.rhoP r' z)
        = fun r' => Work.Cyl.rhoP r' z ^ p := by funext x; rfl
    rw [hfun] at h
    convert h using 1
    rw [Real.rpow_sub_one hne]
    field_simp
  have h := hρp.div_const c
  convert h using 1
  ring

/-- The radial counterpart of `Work.Cyl.hasDerivAt_thetaP_snd`:
`r' ↦ θ(r',z) = arctan(z/r')` has derivative `-z/ρ²` at `r > 0`. -/
lemma hasDerivAt_thetaP_fst (r z : ℝ) (hr : 0 < r) :
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

/-! ## Differentiability of the self-similar vorticity -/

/-- `r' ↦ ssVort p λ F r' z t` is differentiable at `r > 0`: the two-variable chain rule along the
radial slice. -/
lemma differentiableAt_ssVort_fst {p : ℝ} {lam : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {r z t : ℝ}
    (hr : 0 < r)
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)) :
    DifferentiableAt ℝ (fun r' : ℝ => Work.CoreResiduals.ssVort p lam F r' z t) r := by
  have hR : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p / lam t)
      (p * (Work.Cyl.rhoP r z ^ p / lam t) * (r / Work.Cyl.rhoP r z ^ 2)) r :=
    hasDerivAt_rhoP_rpow_div_fst r z p (lam t) hr
  have hZ : HasDerivAt (fun r' : ℝ => Work.Cyl.thetaP r' z) (-z / Work.Cyl.rhoP r z ^ 2) r :=
    hasDerivAt_thetaP_fst r z hr
  have h := Work.Cyl.hasDerivAt_comp_two F (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p / lam t)
    (fun r' : ℝ => Work.Cyl.thetaP r' z) _ _ r hF hR hZ
  have h2 := h.const_mul ((lam t)⁻¹)
  show DifferentiableAt ℝ
    (fun r' : ℝ => (lam t)⁻¹ * F (Work.Cyl.rhoP r' z ^ p / lam t) (Work.Cyl.thetaP r' z)) r
  exact h2.differentiableAt

/-- `z' ↦ ssVort p λ F r z' t` is differentiable at `z`: the two-variable chain rule along the
axial slice. -/
lemma differentiableAt_ssVort_snd {p : ℝ} {lam : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {r z t : ℝ}
    (hr : 0 < r)
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)) :
    DifferentiableAt ℝ (fun z' : ℝ => Work.CoreResiduals.ssVort p lam F r z' t) z := by
  have hR : HasDerivAt (fun z' : ℝ => Work.Cyl.rhoP r z' ^ p / lam t)
      (p * (Work.Cyl.rhoP r z ^ p / lam t) * (z / Work.Cyl.rhoP r z ^ 2)) z :=
    Work.Cyl.hasDerivAt_rhoP_rpow_div_snd r p z (lam t) hr
  have hZ : HasDerivAt (fun z' : ℝ => Work.Cyl.thetaP r z') (r / Work.Cyl.rhoP r z ^ 2) z :=
    Work.Cyl.hasDerivAt_thetaP_snd r z hr
  have h := Work.Cyl.hasDerivAt_comp_two F (fun z' : ℝ => Work.Cyl.rhoP r z' ^ p / lam t)
    (fun z' : ℝ => Work.Cyl.thetaP r z') _ _ z hF hR hZ
  have h2 := h.const_mul ((lam t)⁻¹)
  show DifferentiableAt ℝ
    (fun z' : ℝ => (lam t)⁻¹ * F (Work.Cyl.rhoP r z' ^ p / lam t) (Work.Cyl.thetaP r z')) z
  exact h2.differentiableAt

/-- `s ↦ ssVort p λ F r z s` is differentiable at `t` when `λ` is differentiable at `t` with
`λ(t) ≠ 0`: the two-variable chain rule along the time slice, with the amplitude prefactor
`λ(s)⁻¹`. -/
lemma differentiableAt_ssVort_time {p κ : ℝ} {lam : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {r z t : ℝ}
    (hlam : lam t ≠ 0) (hder : HasDerivAt lam (-κ) t)
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)) :
    DifferentiableAt ℝ (fun s : ℝ => Work.CoreResiduals.ssVort p lam F r z s) t := by
  have hinv : HasDerivAt (fun s : ℝ => (lam s)⁻¹) (κ * ((lam t)^2)⁻¹) t := by
    have h := hder.inv hlam
    convert h using 1
    ring
  have hR : HasDerivAt (fun s : ℝ => Work.Cyl.rhoP r z ^ p / lam s)
      (Work.Cyl.rhoP r z ^ p * (κ * ((lam t)^2)⁻¹)) t := by
    have h : HasDerivAt (fun s : ℝ => Work.Cyl.rhoP r z ^ p * (lam s)⁻¹)
        (Work.Cyl.rhoP r z ^ p * (κ * ((lam t)^2)⁻¹)) t := hinv.const_mul _
    simpa only [div_eq_mul_inv] using h
  have hZ : HasDerivAt (fun _ : ℝ => Work.Cyl.thetaP r z) 0 t := hasDerivAt_const t _
  have hcomp := Work.Cyl.hasDerivAt_comp_two F (fun s : ℝ => Work.Cyl.rhoP r z ^ p / lam s)
    (fun _ : ℝ => Work.Cyl.thetaP r z) (Work.Cyl.rhoP r z ^ p * (κ * ((lam t)^2)⁻¹)) 0 t
    hF hR hZ
  have hprod := hinv.mul hcomp
  show DifferentiableAt ℝ
    (fun s : ℝ => (lam s)⁻¹ * F (Work.Cyl.rhoP r z ^ p / lam s) (Work.Cyl.thetaP r z)) t
  exact hprod.differentiableAt

/-! ## The residual identity for the cut self-similar pair -/

theorem meridianResid_cut_ssVort_eq {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {p κ : ℝ} (hp : 0 < p) {lam : ℝ → ℝ} {F Φ : ℝ → ℝ → ℝ}
    {r z t : ℝ} (hr : 0 < r) (hz : 0 < z) (ht : 0 < t)
    (hlam : 0 < lam t) (hder : HasDerivAt lam (-κ) t)
    (hF : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => F q.1 q.2)
      (Work.Cyl.rhoP r z ^ p / lam t, Work.Cyl.thetaP r z))
    (hΦ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2)
      (Work.Cyl.rhoP r z ^ p / lam t, Work.Cyl.thetaP r z)) :
    Work.CoreResiduals.meridianResid
        (fun r z t => Work.Stability.chi (Work.Cyl.rhoP r z / P.L)
          * Work.CoreResiduals.ssVort p lam F r z t)
        (Work.CoreResiduals.ssPsi p lam Φ) r z t
      = Work.Stability.chi (Work.Cyl.rhoP r z / P.L) *
          ((2 * (lam t) ^ 2)⁻¹ *
            (2 * κ * (F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
                + Work.Spaces.Dz F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
              + Work.Construction.UVR p F Φ (Work.Cyl.rhoP r z ^ p / lam t)
                  (Work.Cyl.thetaP r z)))
        + (deriv Work.Stability.chi (Work.Cyl.rhoP r z / P.L) / P.L)
            * (Work.Cyl.pdZ (fun r z => Work.CoreResiduals.ssPsi p lam Φ r z t) r z
                  * (r / Work.Cyl.rhoP r z)
              - (Work.CoreResiduals.ssPsi p lam Φ r z t / r
                  + Work.Cyl.pdR (fun r z => Work.CoreResiduals.ssPsi p lam Φ r z t) r z)
                  * (z / Work.Cyl.rhoP r z))
            * Work.CoreResiduals.ssVort p lam F r z t := by
  have hlam_ne : lam t ≠ 0 := ne_of_gt hlam
  have hFd : Work.Cyl.DiffAt2 F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z) :=
    hF.differentiableAt (by norm_num)
  have hWr := differentiableAt_ssVort_fst (F := F) (lam := lam) (p := p) (t := t) hr hFd
  have hWz := differentiableAt_ssVort_snd (F := F) (lam := lam) (p := p) (t := t) hr hFd
  have hWt := differentiableAt_ssVort_time (F := F) (lam := lam) (p := p) (κ := κ)
    hlam_ne hder hFd
  rw [meridianResid_cut P hr hWr hWz hWt]
  rw [meridianResid_ssVort_eq hp hr hz ht hlam hder hF hΦ]

end Work.R1G
