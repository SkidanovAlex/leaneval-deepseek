import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.LeafD2.hB_slab
import Submission.Work.FTS_RegExport.RXVP3.velPkgOpen_of_vopLower

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `LeafD2/hB_slab_lip.lean` — the `fderiv` conjunct of `RegDataD` along the limit curve

The `hB` conjunct of `EpsE4Thr.E4R5.RegDataD` for `F = Feps …` along the Picard limit family:
the map `p ↦ fderiv ℝ (uncurry (Feps … (slice (limFam …) p.2.2))) (p.1, p.2.1)` is continuous on
the slab `(0,∞) × (0,π/2) × [0,δ]`.

The present statement carries three hypotheses that the sibling leaf `hB_slab` (`LeafD2/hB_slab.lean`)
does *not* need — `hCpt`, `hpt` (the pointwise `EpsSq`-Lipschitz gate for `Feps` on the `X`-ball)
and `hLip` (the `τ`-`EpsSq`-Lipschitz bundle of the limit curve, *with* the `EpsMem` conjunct) —
so it follows immediately from the proved sibling

  `LeafD2.hB_slab_of_lipschitz_bundle`,

which is the same conclusion from `hlim` plus the plain `EpsSq`-Lipschitz bundle of the curve
(that bundle is `hLip`'s second conjunct).  The quantitative input is the proved gate
`LeafD2.fderivFeps_sub_le` (the spatial `fderiv` of the difference of two right-hand sides on the
`X`-ball is bounded by `C (1 + 1/sin 2θ) √(EpsSq (u - v))`), glued in the fake time by
`LeafD2.continuousOn_slab_of_lipschitz`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.LeafD2

set_option autoImplicit false
set_option linter.unusedVariables false

theorem hB_slab_lip {α C₀ Ce Cs R ε δ Cpt : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC₀ : 0 < C₀)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α (2 * C₀) Φs E)
    (hδ : 0 < δ) (hR : 0 < R) (hsm0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hlim : ∀ τ ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀)
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ))
    (hvol : ∀ z θ τ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → τ ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ z θ τ
        = h₀ z θ + ∫ s in (0 : ℝ)..τ,
            Work.FTS.EpsEngine.Feps α ρ ε Φs E
              (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) s) z θ)
    (hCpt : 0 ≤ Cpt)
    (hpt : ∀ u v : Work.FTS.Galerkin.Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ|
          ≤ Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)))
    (hLip : ∃ L' : ℝ, 0 < L' ∧ ∀ σ ∈ Set.Icc 0 δ, ∀ τ ∈ Set.Icc 0 δ,
      Work.FTS.StrongEps.EpsMem α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) σ z θ
          - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) σ z θ
          - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ z θ)
        ≤ L' * (σ - τ) ^ 2) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        fderiv ℝ (Function.uncurry
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) p.2.2)))
          (p.1, p.2.1))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ) := by
  -- the `EpsSq`-Lipschitz bundle of the limit curve is the second conjunct of `hLip`
  obtain ⟨L', hL'pos, hLipb⟩ := hLip
  exact hB_slab_of_lipschitz_bundle hα hρ hε hε1 hC₀ hEll hstar hml hδ hR hlim
    ⟨L', hL'pos, fun σ hσ τ hτ => (hLipb σ hσ τ hτ).2⟩

end Work.FTS.StrongEps.EpsE4Thr.LeafD2
