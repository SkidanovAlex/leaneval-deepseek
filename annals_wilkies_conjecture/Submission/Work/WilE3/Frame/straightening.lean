import Mathlib
import Submission.Work.WilE3.Frame.Setup
import Submission.Work.WilE3.Frame.exists_analyticAt_localInverse
import Submission.Work.WilE3.Frame.straighteningDefs
import Submission.Work.WilE3.Frame.DPhiC_bijective
import Submission.Work.WilE3.Frame.hasFDerivAt_PhiC
import Submission.Work.WilE3.Frame.analyticAt_PhiC

namespace Work.WilE3.Frame

open Filter

/-- **The straightening parametrisation of `{h = 0}`** (same statement as the abandoned
`Work.WilE3.Frame.exists_param`, now with the base-point hypothesis `hxe` that the abandoned version
was missing — without it the statement is provably false, see the counterexample below).

If `h (x) = 0` and the `ι`-Jacobian of `h` is invertible at the real point `x` (viewed as the
complex point `toC x`), then the coordinate map `Φ z = (z|_ιᶜ, h(z))` (`PhiC`) is a local
biholomorphism at `toC x`: there is a complex-analytic `Ψ` with `Ψ (Φ x) = x`, `Φ (Ψ w) = w` near
`Φ x` and `Ψ (Φ z) = z` near `x`.  Consequently every point of `{h = 0}` near `x` is `Ψ (u, 0)` for a
unique `u` near `x|_ιᶜ`, i.e. the germ of `{h = 0}` at `x` is the image of the "horizontal" plane —
the starting point of the frame step.

Why `hxe` is needed: conjuncts 1 and 3 force `PhiC (toC x) = (uCoord (toC x), 0)`, i.e. `h (x) = 0`.
Counterexample without it: `k = j = 1`, `h 0 = X 0 + 1`, `x = 0` (`hd` holds, `h(x) = 1`, but
`PhiC` misses the hyperplane `{second coordinate = 0}`).

Proof ingredients: `fderiv (eaEvalC c Q) z = ∑ i, eaEvalC c (eaD c i Q) z • proj i`
(`API.eaEvalC_fderiv_analytic`), so `PhiC` has the block-triangular derivative
`[[Id, 0], [*, M]]` with `M = Matrix.of fun a b => eaEvalC c (eaD c (ι b) (h a)) (toC x)`; `hd` makes
it a `≃L[ℂ]` (`hd` also forces `ι` injective, hence equal dimensions); `PhiC` is analytic and hence
`HasStrictFDerivAt` there; then apply `exists_analyticAt_localInverse`.  Its output gives the
left-inverse `Ψ ∘ PhiC = id` near `toC x` through the source/target of the
`OpenPartialHomeomorph` (which is open, so the left-inverse property holds on a neighbourhood). -/
theorem straightening {k r j : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (h : Fin j → WilkiesDesign.E.EAPoly k r) (ι : Fin j → Fin k)
    (x : Fin k → ℝ)
    (hxe : ∀ a, Work.WilE3.eaEvalC c (h a) (Work.WilE3.Frame.toC x) = 0)
    (hd : (Matrix.of fun a b => Work.WilE3.eaEvalC c (WilkiesDesign.E.eaD c (ι b) (h a))
      (Work.WilE3.Frame.toC x)).det ≠ 0) :
    ∃ Ψ : ((Work.WilE3.Frame.U k ι → ℂ) × (Fin j → ℂ)) → (Fin k → ℂ),
      Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x), 0) = Work.WilE3.Frame.toC x ∧
      AnalyticAt ℂ Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x), 0) ∧
      (∀ᶠ w in nhds (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x), 0),
        Work.WilE3.Frame.PhiC c h ι (Ψ w) = w) ∧
      (∀ᶠ z in nhds (Work.WilE3.Frame.toC x), Ψ (Work.WilE3.Frame.PhiC c h ι z) = z) := by
  classical
  -- The derivative of `PhiC` at `toC x` is a bijective continuous linear map, hence a
  -- continuous linear equivalence `e` whose underlying map is that derivative.
  have hbij : Function.Bijective (DPhiC c h ι (toC x)) := DPhiC_bijective c h ι x hd
  have hinj : (DPhiC c h ι (toC x)).ker = ⊥ := LinearMap.ker_eq_bot.mpr hbij.1
  have hsurj : (DPhiC c h ι (toC x)).range = ⊤ := LinearMap.range_eq_top.mpr hbij.2
  let e : (Fin k → ℂ) ≃L[ℂ] ((U k ι → ℂ) × (Fin j → ℂ)) :=
    ContinuousLinearEquiv.ofBijective (DPhiC c h ι (toC x)) hinj hsurj
  have he : (e : (Fin k → ℂ) →L[ℂ] ((U k ι → ℂ) × (Fin j → ℂ))) = DPhiC c h ι (toC x) :=
    ContinuousLinearEquiv.coe_ofBijective (DPhiC c h ι (toC x)) hinj hsurj
  -- `PhiC` is analytic at `toC x`, hence strictly differentiable there with that derivative.
  have hAn : AnalyticAt ℂ (PhiC c h ι) (toC x) := analyticAt_PhiC c h ι x
  have hf : HasStrictFDerivAt (PhiC c h ι) (e : _ →L[ℂ] _) (toC x) := by
    have hFd : HasFDerivAt (PhiC c h ι) (e : _ →L[ℂ] _) (toC x) := by
      rw [he]
      exact hasFDerivAt_PhiC c h ι (toC x)
    have hthis := hAn.hasStrictFDerivAt
    rwa [hFd.fderiv] at hthis
  -- The analytic inverse function theorem.
  obtain ⟨g, hgfa, hgan, hgr, _hgd⟩ :=
    exists_analyticAt_localInverse (PhiC c h ι) e (toC x) hf hAn
  -- `hxe` says exactly that `PhiC (toC x) = (uCoord (toC x), 0)`.
  have h0 : PhiC c h ι (toC x) = (uCoord k ι (toC x), 0) := by
    refine Prod.ext rfl ?_
    funext a
    exact hxe a
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · rw [← h0]
    exact hgfa
  · rw [← h0]
    exact hgan
  · rw [← h0]
    exact hgr
  · -- left inverse of `PhiC` near `toC x`: `g` agrees near `PhiC (toC x)` with the local inverse
    -- of `hf`, which is a left inverse of `PhiC` near `toC x`.
    have hgcont : Tendsto g (nhds (PhiC c h ι (toC x))) (nhds (toC x)) := by
      have hthis : Tendsto g (nhds (PhiC c h ι (toC x)))
          (nhds (g (PhiC c h ι (toC x)))) := hgan.continuousAt
      rwa [hgfa] at hthis
    have heq : hf.localInverse (PhiC c h ι) e (toC x) =ᶠ[nhds (PhiC c h ι (toC x))] g :=
      eventuallyEq_of_left_inv_of_right_inv hf.eventually_left_inverse hgr hgcont
    have hcontPhi : Tendsto (PhiC c h ι) (nhds (toC x)) (nhds (PhiC c h ι (toC x))) :=
      hf.continuousAt
    filter_upwards [hf.eventually_left_inverse, hcontPhi.eventually heq] with z hz hz2
    rw [← hz2]
    exact hz

end Work.WilE3.Frame
