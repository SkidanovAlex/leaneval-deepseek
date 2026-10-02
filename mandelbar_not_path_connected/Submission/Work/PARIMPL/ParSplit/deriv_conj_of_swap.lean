/-
# The multiplier relation on the swap side: `deriv (F c) z = conj (deriv (F c) w)`

If the antiholomorphic square root `g c = gtc c = (T_c)^[5]` of the second return map
`Work.EL.F c = (T_c)^[10]` swaps a two-cycle `z ↔ w`, then the two multipliers of `F c` at `z`
and `w` are **conjugate**: `deriv (F c) z = conj (deriv (F c) w)`.  This is the relation (F2) of
`Submission/Work/PARIMPL/ParSplit/NOTES.md`: on the swap side the two multipliers `ρ`, `ρ'` of
`F c` are conjugate, so `ρ' = conj ρ`, which is what forces the split direction `â` to be almost
imaginary.

The proof is the chain rule for a *conjugate*-differentiable map.  Writing

  `G := conj ∘ g`  (`G u = star (g u)`),

`G` is holomorphic, `g = conj ∘ G`, and the real Fréchet derivative of `g` at `x` is
`conjCLE ∘L mul (deriv G x)`, i.e. it sends `v ↦ deriv G x * conj v`.  Composing two of these and
using `conjCLE ∘L mul a ∘L conjCLE = mul (conj a)` gives, for `F = g ∘ g` and `g z = w`,

  `deriv (F c) z = conj (deriv G w) * deriv G z`,   `deriv (F c) w = conj (deriv G z) * deriv G w`,

and conjugating the second identity yields the first (ℂ is commutative).

For the tricorn, `G` is computed explicitly: `conj ∘ g = S ∘ (Tsq c)^[2]` with
`S u = u² + conj c`, because `(T_c)^[5] = T_c ∘ (Tsq c)^[2]` and `conj ∘ T_c = S`.
-/
import Mathlib
import Submission.Work.PARIMPL.ParSplit.Split

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **Composition of the conjugate-derivative factors.**  For `a b : ℂ` the composite of the two
real-linear maps `v ↦ a * conj v` and `v ↦ b * conj v` is the complex-linear map
`v ↦ (conj a * b) * v`. -/
theorem conjCLE_smul_comp (a b : ℂ) :
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘SL (a • (1 : ℂ →L[ℝ] ℂ))) ∘SL
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘SL (b • (1 : ℂ →L[ℝ] ℂ)))
    = (star a * b) • (1 : ℂ →L[ℝ] ℂ) := by
  ext v
  show (starRingEnd ℂ) (a * (starRingEnd ℂ) (b * v)) = (star a * b) * v
  simp only [map_mul, starRingEnd_apply, star_star]
  ring

/-- **The `swap` multiplier relation.**  If `gtc c` (the antiholomorphic square root `(T_c)^[5]`
of `Work.EL.F c = (T_c)^[10]`) exchanges `z` and `w`, then the multipliers of the holomorphic
second return map `Work.EL.F c` at the two points are conjugate. -/
theorem deriv_conj_of_swap {c z w : ℂ} (h1 : gtc c z = w) (h2 : gtc c w = z) :
    deriv (Work.EL.F c) z = star (deriv (Work.EL.F c) w) := by
  -- The holomorphic partner `G = conj ∘ g` of the antiholomorphic square root `g = gtc c`.
  set G : ℂ → ℂ := (fun u : ℂ => u^2 + star c) ∘ (Work.Landing.Tsq c)^[2] with hG
  have hg : gtc c = (starRingEnd ℂ) ∘ G := by
    rw [hG]
    show (Tantibar c)^[5] =
      (starRingEnd ℂ) ∘ ((fun u : ℂ => u^2 + star c) ∘ (Work.Landing.Tsq c)^[2])
    rw [show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ']
    rw [show (4 : ℕ) = 2 * 2 from rfl, Function.iterate_mul, ← Work.EL.Tsq_eq_comp]
    funext u
    simp only [Function.comp_apply]
    simp [LeanEval.ComplexAnalysis.Tantibar]
  have hTsq : Differentiable ℂ (Work.Landing.Tsq c) := by
    unfold Work.Landing.Tsq; fun_prop
  have hGdiff : Differentiable ℂ G := by
    rw [hG]
    exact (by fun_prop : Differentiable ℂ (fun u : ℂ => u^2 + star c)).comp (hTsq.iterate 2)
  -- The conjugate derivative of `g = gtc c` in terms of `deriv G`.
  have hgd : ∀ x : ℂ, HasFDerivAt (gtc c)
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘SL ((deriv G x) • (1 : ℂ →L[ℝ] ℂ))) x := by
    intro x
    have hGx : HasFDerivAt G ((deriv G x) • (1 : ℂ →L[ℝ] ℂ)) x :=
      (hGdiff.differentiableAt).hasDerivAt.complexToReal_fderiv
    have hstar : HasFDerivAt (starRingEnd ℂ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) (G x) := by
      have h := Complex.conjCLE.hasFDerivAt (x := G x)
      have hfun : (⇑Complex.conjCLE : ℂ → ℂ) = starRingEnd ℂ :=
        funext (fun z => Complex.conjCLE_apply z)
      rw [hfun] at h
      exact h
    have hcomp := hstar.comp x hGx
    simpa only [hg] using hcomp
  have hFdiff : Differentiable ℂ (Work.EL.F c) := by
    show Differentiable ℂ ((Work.Landing.Tsq c)^[5])
    exact hTsq.iterate 5
  -- Chain rule at `z`: `g z = w`, so `fderiv (g ∘ g) z = fderiv g w ∘ fderiv g z`.
  have hA : HasFDerivAt (gtc c)
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘SL ((deriv G w) • (1 : ℂ →L[ℝ] ℂ))) (gtc c z) := by
    rw [h1]; exact hgd w
  have hc_z := hA.comp z (hgd z)
  rw [← Ft_eq_g_comp] at hc_z
  have hFz : HasFDerivAt (Work.EL.F c) ((deriv (Work.EL.F c) z) • (1 : ℂ →L[ℝ] ℂ)) z :=
    ((hFdiff.differentiableAt).hasDerivAt).complexToReal_fderiv
  have huniq := hFz.unique hc_z
  rw [conjCLE_smul_comp (deriv G w) (deriv G z)] at huniq
  have hz : deriv (Work.EL.F c) z = star (deriv G w) * deriv G z := by
    have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) huniq
    simpa using h
  -- Chain rule at `w`: `g w = z`.
  have hB : HasFDerivAt (gtc c)
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘SL ((deriv G z) • (1 : ℂ →L[ℝ] ℂ))) (gtc c w) := by
    rw [h2]; exact hgd z
  have hc_w := hB.comp w (hgd w)
  rw [← Ft_eq_g_comp] at hc_w
  have hFw : HasFDerivAt (Work.EL.F c) ((deriv (Work.EL.F c) w) • (1 : ℂ →L[ℝ] ℂ)) w :=
    ((hFdiff.differentiableAt).hasDerivAt).complexToReal_fderiv
  have huniq_w := hFw.unique hc_w
  rw [conjCLE_smul_comp (deriv G z) (deriv G w)] at huniq_w
  have hw : deriv (Work.EL.F c) w = star (deriv G z) * deriv G w := by
    have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) huniq_w
    simpa using h
  rw [hz, hw, star_mul, star_star]

end Work.PARIMPL.ParSplit
