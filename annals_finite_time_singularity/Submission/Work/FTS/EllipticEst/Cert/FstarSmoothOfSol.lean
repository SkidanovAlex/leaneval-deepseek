import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.Defs
import Submission.Work.FTS.EllipticEst.Fstar_contDiffOn
import Submission.Work.Coercivity.slice_ibp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false

/-! ## Two independent pieces of the route

`FstarSmoothOfSol` is assembled from three ingredients, of which the first two are proved
here (they are independent of each other) and the third is the parametric-integral lemma
`Work.FTS.EllipticEst.contDiffOn_infty_integral_Itheta_Ioi_neg_one` of `Fstar_contDiffOn.lean`:

* `FstarInt_smoothNbhdOfSol`: the smooth integrand `FstarInt α Ψ` is `SmoothNbhd` whenever
  `Ψ` is — it is a sum/product of `∂_z^2Ψ`, `∂_zΨ`, `∂_θ^2Ψ`, `∂_θΨ`, `Ψ`, polynomials in `z`
  and functions of `θ` alone;
* `Fstar_eq_integral_FstarIntOfSol`: on the open quadrant `F = bslOp α Ψ`, so multiplying by
  the angular weight turns the integrand into `FstarInt α Ψ`
  (`Cert.FstarSmooth.bslOp_mul_sinCos2_eq`); at the two endpoints `θ = 0, π/2` the weight
  `sinθcos²θ` vanishes, so the two integrands agree on *all* of `Iθ` and the `θ`-integrals
  agree on the nose (no `a.e.` discussion needed). -/

/-- **The smooth integrand of the angular moment is smooth on a neighbourhood of the closed
quadrant** whenever `Ψ` is. -/
theorem FstarInt_smoothNbhdOfSol (α : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (h : Work.Spaces.SmoothNbhd Ψ) :
    Work.Spaces.SmoothNbhd (FstarInt α Ψ) := by
  have hsin : Work.Spaces.SmoothNbhd (fun _ θ : ℝ => Real.sin θ) :=
    smoothNbhd_snd_comp Real.sin Real.contDiff_sin
  have hcos : Work.Spaces.SmoothNbhd (fun _ θ : ℝ => Real.cos θ) :=
    smoothNbhd_snd_comp Real.cos Real.contDiff_cos
  have hcos2 : Work.Spaces.SmoothNbhd (fun _ θ : ℝ => Real.cos θ ^ 2) :=
    smoothNbhd_snd_comp (fun θ => Real.cos θ ^ 2) (Real.contDiff_cos.pow 2)
  have hsincos : Work.Spaces.SmoothNbhd (fun _ θ : ℝ => Real.sin θ * Real.cos θ) :=
    smoothNbhd_mul' hsin hcos
  have hpz1 : Work.Spaces.SmoothNbhd (fun z θ => Work.Spaces.pz Ψ z θ) :=
    Work.Spaces.smoothNbhd_pzIter h 1
  have hpz2 : Work.Spaces.SmoothNbhd (fun z θ => Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.Spaces.smoothNbhd_pzIter h 2
  have hpth1 : Work.Spaces.SmoothNbhd (fun z θ => Work.Spaces.pth Ψ z θ) :=
    smoothNbhd_pthIter h 1
  have hpth2 : Work.Spaces.SmoothNbhd (fun z θ => Work.Spaces.pthIter 2 Ψ z θ) :=
    smoothNbhd_pthIter h 2
  have hz2 : Work.Spaces.SmoothNbhd (fun z _ : ℝ => z ^ 2) := smoothNbhd_pow_fst 2
  have hz1 : Work.Spaces.SmoothNbhd (fun z _ : ℝ => z) := smoothNbhd_fst
  -- the `α`-bracket, written in the form produced by the closure lemmas
  have hA : Work.Spaces.SmoothNbhd
      (fun z θ => (-(α ^ 2) * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
        - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
        - Work.Spaces.pthIter 2 Ψ z θ - 6 * Ψ z θ) := by
    refine smoothNbhd_sub (smoothNbhd_sub (smoothNbhd_sub ?_ ?_) ?_) ?_
    · exact smoothNbhd_mul' (smoothNbhd_const_mul (-(α ^ 2)) hz2) hpz2
    · exact smoothNbhd_mul' (smoothNbhd_const_mul (α * (5 + α)) hz1) hpz1
    · exact hpth2
    · exact smoothNbhd_const_mul 6 h
  -- the weight-cancelled `tan`-term
  have hB : Work.Spaces.SmoothNbhd
      (fun z θ => Real.sin θ * Ψ z θ
        + Real.sin θ * (Real.sin θ * Real.cos θ) * Work.Spaces.pth Ψ z θ) := by
    refine smoothNbhd_add (smoothNbhd_mul' hsin h) ?_
    exact smoothNbhd_mul' (smoothNbhd_mul' hsin hsincos) hpth1
  -- `(α-bracket) · sinθcos²θ + (cancelled term)`, the weight split as `sin θ · cos θ ^ 2`
  have htot : Work.Spaces.SmoothNbhd
      (fun z θ => ((-(α ^ 2) * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
            - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
            - Work.Spaces.pthIter 2 Ψ z θ - 6 * Ψ z θ) * (Real.sin θ * Real.cos θ ^ 2)
          + (Real.sin θ * Ψ z θ
            + Real.sin θ * (Real.sin θ * Real.cos θ) * Work.Spaces.pth Ψ z θ)) :=
    smoothNbhd_add (smoothNbhd_mul' hA (smoothNbhd_mul' hsin hcos2)) hB
  exact SmoothNbhd_congr htot fun z θ => by
    rw [FstarInt_apply, Work.Elliptic.sinCos2]
    ring

/-- **The angular moment as an integral of the smooth integrand.**  For `z > 0` the source `F`
of a solution of (PolarBSL) agrees with `bslOp α Ψ` on the open quadrant, and on the closed
quadrant the weight `sinθcos²θ` vanishes exactly where `bslOp α Ψ` fails to be smooth (the
endpoints `θ = 0, π/2`, where also `sinθ = 0` resp. `Ψ z (π/2) = 0`), so the two integrands
agree on all of `Iθ`. -/
theorem Fstar_eq_integral_FstarIntOfSol (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z
      = ∫ θ in Work.Spaces.Iθ, FstarInt α Ψ z θ := by
  intro z hz
  rw [Work.Elliptic.Fstar]
  refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  rcases lt_or_eq_of_le hθ.1 with hθpos | hθzero
  · rcases lt_or_eq_of_le hθ.2 with hθlt | hθeq
    · -- interior of the quadrant: `F = bslOp α Ψ` and the `tan`-pole cancels
      have hcos : Real.cos θ ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθlt⟩)
      have hd : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ :=
        Work.Coercivity.smoothNbhd_slice_differentiableAt Ψ hsm hz ⟨hθpos, hθlt⟩
      rw [← hsol.1 z hz θ hθpos hθlt, bslOp_mul_sinCos2_eq α Ψ hcos hd]
    · -- the endpoint `θ = π/2`: the weight vanishes and `Ψ z (π/2) = 0`
      subst hθeq
      simp [Work.Elliptic.sinCos2, FstarInt_apply, hsol.2.2.1]
  · -- the endpoint `θ = 0`: the weight vanishes and `sin 0 = 0`
    rw [← hθzero]
    simp [Work.Elliptic.sinCos2, FstarInt_apply]

/-- **The angular moment `F_* = F_*(F)` of the source of a solution of (PolarBSL) is `C^∞`
on `(0,∞)`.**  Route: on the open quadrant `F·sinθcos²θ = FstarInt α Ψ`
(`Cert.FstarSmooth.bslOp_mul_sinCos2_eq`, proved, using `tan_weight_cancel`); the two sides agree
a.e. in `θ` so the `θ`-integrals agree (`Cert.FstarSmooth.Fstar_eq_integral_FstarInt`, which may
need to be proved inline using `Fstar_eq_integral_of_pointwise` + `bslOp_mul_sinCos2_eq`); and
`FstarInt α Ψ` is `SmoothNbhd` when `Ψ` is (`Cert.FstarSmooth.FstarInt_smoothNbhd`, needs
`SmoothNbhd_mul'`/`SmoothNbhd_add` from `Cert.FstarSmooth.Defs`), so its parametric `θ`-integral
over the compact `Iθ` is `C^∞` on `Ioi (-1)`
(`Work.FTS.EllipticEst.contDiffOn_infty_integral_Itheta_Ioi_neg_one`, proved), hence on `Ioi 0`. -/
theorem FstarSmoothOfSol (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) := by
  intro m
  -- `FstarInt α Ψ` is smooth on a neighbourhood of the closed quadrant
  have hG : Work.Spaces.SmoothNbhd (FstarInt α Ψ) := FstarInt_smoothNbhdOfSol α Ψ hsm
  -- hence its parametric `θ`-integral over the compact `Iθ` is `C^m` on `(-1,∞)`
  have hint : ContDiffOn ℝ m (fun z => ∫ θ in Work.Spaces.Iθ, FstarInt α Ψ z θ)
      (Set.Ioi 0) := by
    have h := Work.FTS.EllipticEst.contDiffOn_infty_integral_Itheta_Ioi_neg_one
      (FstarInt α Ψ) (fun _ : ℝ => (1 : ℝ)) hG continuousOn_const
    have h2 : ContDiffOn ℝ m (fun z => ∫ θ in Work.Spaces.Iθ, FstarInt α Ψ z θ)
        (Set.Ioi (-1)) := by
      simpa only [mul_one] using contDiffOn_infty.mp h m
    exact h2.mono (Set.Ioi_subset_Ioi (by norm_num))
  -- and the two functions agree on `(0,∞)`
  exact hint.congr fun z hz => Fstar_eq_integral_FstarIntOfSol α F Ψ hsm hsol z hz

end Work.FTS.EllipticEst.Cert
