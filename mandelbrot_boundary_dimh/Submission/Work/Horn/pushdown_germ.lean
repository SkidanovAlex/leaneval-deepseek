import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic
import Submission.Work.Horn.pushdown_differentiableOn_punctured
import Submission.Work.Horn.deriv_deriv_mul_piExp
import Submission.Work.Horn.analyticAt_extension_of_hasDerivAt
import Submission.Work.Horn.exists_analyticAt_piExp_factor
import Submission.Work.Repel.pushdown_deriv

/-!
# AREA HORN: the germ of the pushed-down horn map at `0`

Shishikura's normalisation (4.1.5) of the lifted horn map `Ẽ = Φ ∘ φ` reads
`Ẽ w - w → 0` at the upper end.  Its consequence for the pushed-down map
`g = pushdown Ẽ` on the cylinder is that the germ of `g` at `0` is again of the same shape
as the germ of the map one started with:

there is a germ `H` holomorphic at `0` with `H 0 = 0` and

* `g ζ = ζ · π (H ζ)` for all `ζ` near `0` (`π(w) = exp (2πi w)`), and
* `g''(0) = 4πi H'(0)`,

which is exactly the assertion that `g` (after the rescaling `ζ ↦ sζ`, `s = g''(0)/2` of
Lemma 5.4) lies in the class `𝓕₀` of parabolic germs `x + x² + O(x³)`, with the same
normalisation as `HornData.g_second`.

The mathematical input is entirely the *quadratic* normalisation `Ẽ w = w + o(1)`:
the principal lift `ζ ↦ log ζ/(2πi)` of `ζ = π w` runs to the upper end as `ζ → 0`, hence

`g ζ = π (Ẽ w) = π w · π (Ẽ w - w) = ζ · u(ζ)`, `u (ζ) = π (Ẽ w - w) → π 0 = 1`,

so `u` is a holomorphic function on a punctured neighbourhood of `0` with a removable
singularity at `0` of value `1`; `H` is then a local logarithm of `u`.  This file assembles
the four supporting lemmas:

* `Work.Horn.pushdown_differentiableOn_punctured` — `g` is holomorphic on the punctured
  disc of radius `exp (-2πη₀)` (a colleague's lemma, from `Repel.pushdown_holo`);
* `Work.Horn.pushdown_hasDerivAt_zero` (below) — `g'(0) = 1`, from `Ẽ w - w → 0` at the
  upper end (`Repel.pushdown_deriv`), and `g 0 = 0` (`pushdown_zero`);
* `Work.Horn.analyticAt_extension_of_hasDerivAt` — the removable-singularity step
  (a colleague's lemma, Riemann's theorem);
* `Work.Horn.exists_analyticAt_piExp_factor` — the local logarithm of `u`
  (a colleague's lemma);
* `Work.Horn.deriv_deriv_mul_piExp` — the second jet `(ζ π (H ζ))''(0) = 4πi H'(0)`
  (a colleague's lemma).
-/

open _root_.MandelDim Filter Topology Metric
open scoped Topology

namespace Work.Horn

noncomputable section

/-! ## The germ of the pushed-down horn map at the origin -/

/-- The pushed-down horn map has derivative `1` at `0`: this is Shishikura's normalisation
(4.1.5), expressed by the field `ParabData.E_upper` (`Ẽ w - w → 0` at the upper end of the
cylinder).  The principal lift of `ζ → 0` meets the upper end, so the asymptotic expansion of
`Ẽ` at that end controls the germ at `0`. -/
theorem pushdown_hasDerivAt_zero (f₀ : ℂ → ℂ) (D₀ : Set ℂ) (d : MandelDim.ParabData f₀ D₀) :
    HasDerivAt (MandelDim.pushdown d.E) 1 0 := by
  have hopen : IsOpen {w : ℂ | d.η₀ < |w.im|} :=
    isOpen_Ioi.preimage (continuous_abs.comp Complex.continuous_im)
  have h := Work.Repel.pushdown_deriv (E := d.E) (DR := {w : ℂ | d.η₀ < |w.im|})
    (y := d.η₀ + 1) (c := 0) hopen (isTEquivariantOn_E_abs_im_gt d)
    (differentiableOn_E_abs_im_gt d)
    (fun w hw => lt_of_lt_of_le (by linarith : d.η₀ < d.η₀ + 1) hw)
    (by simpa [MandelDim.ParabData.E] using d.E_upper)
  simpa [MandelDim.piExp] using h

/-- **Germ form of a map with a simple zero of slope `1` at `0`.**  If `g` is holomorphic on
the punctured disc of radius `R > 0`, `g 0 = 0` and `g'(0) = 1`, then near `0`

`g ζ = ζ · π (H ζ)`

for some germ `H` holomorphic at `0` with `H 0 = 0`, and `g''(0) = 4πi H'(0)`.

(The hypothesis `g 0 = 0` is essential: `g ζ / ζ` has to be bounded near `0`; it holds for the
pushed-down horn map by definition of `pushdown`.) -/
theorem germ_of_slope_one (g : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hdiff : DifferentiableOn ℂ g (Metric.ball 0 R \ {0})) (hg0 : g 0 = 0)
    (hder : HasDerivAt g 1 0) :
    ∃ H : ℂ → ℂ, H 0 = 0 ∧ DifferentiableAt ℂ H 0 ∧
      (∀ᶠ ζ in nhds (0 : ℂ), g ζ = ζ * MandelDim.piExp (H ζ)) ∧
      deriv (deriv g) 0 = 4 * (Real.pi : ℂ) * Complex.I * deriv H 0 := by
  -- Riemann's theorem: `u = g/ζ` is holomorphic at `0` with `u 0 = 1`
  obtain ⟨u, hu0, hu, hgu⟩ := analyticAt_extension_of_hasDerivAt g hR hdiff hg0 hder
  -- a local logarithm of `u`
  obtain ⟨H, hH0, hHa, hHd, hHu⟩ := exists_analyticAt_piExp_factor u hu hu0
  refine ⟨H, hH0, hHd, ?_, ?_⟩
  · filter_upwards [hgu, hHu] with ζ h1 h2
    rw [h1, h2]
  · have hFeq : g =ᶠ[𝓝 (0 : ℂ)] (fun ζ : ℂ => ζ * MandelDim.piExp (H ζ)) := by
      filter_upwards [hgu, hHu] with ζ h1 h2
      rw [h1, h2]
    rw [Filter.EventuallyEq.deriv_eq (hFeq.deriv), deriv_deriv_mul_piExp hHa hH0]

/-- **The germ of the pushed-down horn map.**  For the §4.1 data `d` of a parabolic germ, the
pushed-down horn map `pushdown d.E` has, near `0`, the form `ζ ↦ ζ · π (H ζ)` with `H`
holomorphic at `0`, `H 0 = 0`; its second jet is `4πi H'(0)`. -/
theorem pushdown_germ (f₀ : ℂ → ℂ) (D₀ : Set ℂ) (d : MandelDim.ParabData f₀ D₀) :
    ∃ H : ℂ → ℂ, H 0 = 0 ∧ DifferentiableAt ℂ H 0 ∧
      (∀ᶠ ζ in nhds (0 : ℂ), MandelDim.pushdown d.E ζ = ζ * MandelDim.piExp (H ζ)) ∧
      deriv (deriv (MandelDim.pushdown d.E)) 0 = 4 * ↑Real.pi * Complex.I * deriv H 0 := by
  exact germ_of_slope_one (MandelDim.pushdown d.E) (Real.exp_pos _)
    (pushdown_differentiableOn_punctured f₀ D₀ d) (Work.Horn.MandelDim.pushdown_zero d.E)
    (pushdown_hasDerivAt_zero f₀ D₀ d)

end

end Work.Horn
