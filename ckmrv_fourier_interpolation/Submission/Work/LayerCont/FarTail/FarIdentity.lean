/-
# The far-side (`Re τ > 1`) identity of the window chart — CKMRV (5.7)

The chart `windowChart ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r` of the CKMRV layer continuation agrees with the
paper's layer `paperLayer (Gcusp ℓ d) ℓ d · r` on the `𝒟`-side of the ball, and with

  `paperLayer (Gcusp ℓ d) ℓ d τ r + sinSqC r · resCorr r τ`

on its **far side** (`1 < Re τ`).  The residue correction is *not* cancelled there: the pole
`z = τ - 1` of the kernel has positive real part, so the left detour misses it, while the
removable coincidence `ST⁻¹τ` now lies strictly inside the swept rectangle and is passed
residue-free.

The proof is the composition of the two contour identities already in the library:

* `Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_far` — the contour deformation across the two
  rectangles, giving `layerLowDouble = layerLowAt + sinSqC r · resCorr r`;
* `Work.LayerCont.layerAt_eq_paperLayer` — the split-point independence of the layer, whose two
  hypotheses are here the *far-side* cleanliness (`j τ ≠ j (i t)` for all `t > 0`, from
  `Work.LayerCont.FarTail.clean_axis_of_web_re_gt_one`) and the *far-side tail integrability*
  (`Work.LayerCont.FarTail.tail_integrableOn_of_clean`).
-/
import Mathlib
import Submission.Work.LayerCont.FarTail.Defs
import Submission.Work.LayerCont.FarTail.Clean
import Submission.Work.LayerCont.FarTail.CuspFar
import Submission.Work.LayerCont.FarTail.FarGeom
import Submission.Work.LayerCont.Coinc.All

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.FarTail

open Work.Asymptotics Work.LayerCont Work.LayerCont.Coinc

/-- **The far-side identity of the window chart.**  For `τ` in the chart ball with `1 < τ.re`,

  `windowChart ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ = paperLayer (Gcusp ℓ d) ℓ d τ r + sinSqC r · resCorr r τ`.

The geometric hypotheses are exactly those supplied on the far side by
`Work.LayerCont.FarTail.far_orbit_rects` and `Work.LayerCont.FarTail.coinc_mem_openLeftRect_far`. -/
theorem far_identity (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {s₀ A₁ ξ₁ A₂ ξ₂ p ε : ℝ} (hs₀ : 0 < s₀) (hA₁ : 0 < A₁) (hξ₁ : 0 < ξ₁) (hA₂ : 0 < A₂)
    (hξ₂ : 0 < ξ₂) (hε : 0 < ε) (hp1 : 1 ≤ p) (hlo : 0 < s₀ - A₁) (hhi : s₀ + A₁ ≤ p)
    (hsep : s₀⁻¹ + A₂ < s₀ - A₁) (hA₂inv : A₂ < s₀⁻¹)
    (hcl₁ : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀ A₁ ξ₁ z → z ≠ γ • τ)
    (hcl₂ : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀⁻¹ A₂ ξ₂ z →
          (z ≠ γ • τ ∨ z = ModularGroup.S • ((-1 : ℝ) +ᵥ τ)))
    (hcoinc : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      Work.LayerCont.Coinc.coincℂ τ ∈ Work.Asymptotics.openLeftRectℂ s₀⁻¹ A₂ ξ₂)
    (hdeg : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      Work.Residues.jprime τ ≠ 0)
    (hclean : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      ∀ (t : ℝ) (ht : 0 < t),
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    (hInt : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      ∀ r : ℝ, MeasureTheory.IntegrableOn (fun t : ℝ =>
        (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
          * Work.Asymptotics.gaussWeight r t) (Set.Ici (1 : ℝ))) :
    ∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      windowChart ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ
        = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
          + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ := by
  intro τ r hτ hτre
  have hlow : Work.LayerCont.layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ
      = Work.LayerCont.layerLowAt ℓ d p r τ
        + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ :=
    Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_far ℓ d hd hs₀ hA₁ hξ₁ hA₂ hξ₂ hε hlo hhi
      hsep hA₂inv hcl₁ hcl₂ hcoinc hdeg
      (fun σ hσ hre t ht _ => hclean σ hσ hre t ht) τ hτ hτre
  have hat : Work.LayerCont.layerAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
      = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r :=
    Work.LayerCont.layerAt_eq_paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d hd (p := p) hp1 τ
      (fun t ht _ => hclean τ hτ hτre t ht) (hInt τ hτ hτre r)
  exact windowChart_eq_paperLayer_add_resCorr ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ hlow hat


/-- **`layerAt = paperLayer` on the far side of the line `Re τ = 1`.**

The split-point independence `Work.LayerCont.layerAt_eq_paperLayer` of the layer is *not*
restricted to `𝒟`; it only requires

* cleanliness of the contour `t ↦ i t` up to the split point, and
* integrability of the cusp-subtracted integrand on `[1,∞)`.

On the far side those two are supplied by `Work.LayerCont.FarTail.farClean_of_web` (or, at a single
point, `Work.LayerCont.FarTail.clean_axis_of_web_re_gt_one`) and by
`Work.LayerCont.FarTail.tail_integrableOn_of_clean`; this lemma records the resulting statement
under the name by which the first recurrence consumes it. -/
theorem layerAt_eq_paperLayer_far (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) {p r : ℝ} (hp1 : 1 ≤ p)
    (τ : UpperHalfPlane)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) p →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    (hIntTail : MeasureTheory.IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      - Work.Asymptotics.Aexp G τ t) * Work.Asymptotics.gaussWeight r t) (Set.Ici (1 : ℝ))) :
    Work.LayerCont.layerAt G ℓ d p r τ = Work.Asymptotics.paperLayer G ℓ d τ r :=
  Work.LayerCont.layerAt_eq_paperLayer G ℓ d hd hp1 τ hclean hIntTail

end Work.LayerCont.FarTail

/-- **The first recurrence from the three agreements of a chart.**

This is the general assembly step: if a function `F` (a chart, say) agrees with the paper's layer
at `τ` and `τ+1`, and with `paperLayer + sinSqC r · resCorr r` at `τ+2` — the far side — and if the
contour is clean on `(0,1]` at the three points and the cusp-subtracted integrand is integrable on
`[1,∞)` there, then

  `T2op F τ = -T2op (gaussTerm · r) τ`.

It is `Work.LayerCont.T2op_of_far_identity` with the annihilation of the paper's layer
(`Work.LayerCont.T2op_paperLayer`) inserted, so that a caller only has to supply the agreements and
the two analytic side conditions. -/
theorem T2op_of_chart_agreements (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {r : ℝ} {τ : UpperHalfPlane} (F : UpperHalfPlane → ℂ)
    (hclean : ∀ σ ∈ ({τ, (1 : ℝ) +ᵥ τ, (2 : ℝ) +ᵥ τ} : Set UpperHalfPlane),
      ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) 1 →
        Work.Kernels.jInvariantFun σ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    (hInt : ∀ σ ∈ ({τ, (1 : ℝ) +ᵥ τ, (2 : ℝ) +ᵥ τ} : Set UpperHalfPlane),
      MeasureTheory.IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t) (Set.Ici (1 : ℝ)))
    (h2 : F ((2 : ℝ) +ᵥ τ)
      = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((2 : ℝ) +ᵥ τ) r
        + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r ((2 : ℝ) +ᵥ τ))
    (h1 : F ((1 : ℝ) +ᵥ τ)
      = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ τ) r)
    (h0 : F τ = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r) :
    Work.Kernels.T2op F τ = -Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ r) τ :=
  Work.LayerCont.T2op_of_far_identity ℓ d r τ F h2 h1 h0
    (Work.LayerCont.T2op_paperLayer ℓ d hd hclean hInt)
