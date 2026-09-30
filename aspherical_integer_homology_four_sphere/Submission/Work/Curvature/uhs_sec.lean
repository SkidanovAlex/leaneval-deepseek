import Mathlib
import Submission.Work.Curvature.Basic
import Submission.Work.Curvature.Deriv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The upper half space metric has constant sectional curvature `-1`

This file proves `Work.Curvature.uhs_sec`: for the upper half space metric
`uhsMetric q = (q 3)⁻² • δ` on the half space `{q 3 > 0}`,

`uhsMetric q (R(∂_u, ∂_v) ∂_v) u = -(⟪u,u⟫ ⟪v,v⟫ - ⟪u,v⟫²)`,

i.e. the model has constant sectional curvature `-1`, matching the standard
hyperbolic space `ℍ⁴`.

The proof has three ingredients, all established here in order to be
self-contained:

* `uhs_sec_koszul` — `chrUHS` satisfies the Koszul formula for `uhsMetric`;
* `uhs_sec_koszulChr` — hence the Christoffel symbol `koszulChr uhsMetric` equals
  `chrUHS` (by the uniqueness statement `koszulChr_eq_of_forall`);
* `uhs_sec_dBmodel` — the derivative `dBmodel uhsMetric` of the Christoffel
  symbol is `(q 3)⁻¹^2 • chrUHSderiv`.

Everything is then a finite polynomial identity in the coordinates, closed by
`ring`.
-/

open scoped RealInnerProductSpace
open Filter Topology

namespace Work.Curvature

noncomputable section

/-- Coordinate expansion of the inner product on `E4 = ℝ⁴`. -/
lemma uhs_sec_inner_E4 (a b : E4) :
    ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3 := by
  rw [PiLp.inner_apply, Fin.sum_univ_four]
  simp only [Real.inner_apply]

/-- **`chrUHS` satisfies the Koszul formula** for the upper half space metric.
The needed identity `⟪chrUHSvec a b, c⟫ = -(⟪a,c⟫ b₃ + ⟪b,c⟫ a₃ - ⟪a,b⟫ c₃)`
is a consequence of the explicit coordinate formula for `chrUHSvec`. -/
theorem uhs_sec_koszul (q : E4) (hq : q 3 ≠ 0) (a b c : E4) :
    uhsMetric q (chrUHS q a b) c = koszulRHS uhsMetric q a b c := by
  rw [koszulRHS, dG_uhsMetric a c b q hq, dG_uhsMetric b c a q hq, dG_uhsMetric a b c q hq]
  simp only [uhsMetric_apply, uhs_sec_inner_E4, chrUHS, PiLp.smul_apply, chrUHSvec]
  ring_nf
  field_simp
  simp
  ring

/-- **The Christoffel symbol of `uhsMetric` is `chrUHS`** on the half space
`{q 3 ≠ 0}`. -/
theorem uhs_sec_koszulChr (q : E4) (hq : q 3 ≠ 0) (a b : E4) :
    koszulChr uhsMetric q a b = chrUHS q a b :=
  koszulChr_eq_of_forall (uhsMetric_sub_fst q) (uhsMetric_pos q hq)
    (fun c => uhs_sec_koszul q hq a b c)

/-- **The derivative of the Christoffel symbol of `uhsMetric`.**
Since `koszulChr uhsMetric q' a b = (q' 3)⁻¹ • chrUHSvec a b` near `q`, the
derivative in the direction `d` is `-((q 3)⁻¹^2 * (d 3)) • chrUHSvec a b`, which
is `(q 3)⁻¹^2 • chrUHSderiv d a b`. -/
theorem uhs_sec_dBmodel (q : E4) (hq : 0 < q 3) (d a b : E4) :
    dBmodel uhsMetric q d a b = (q 3)⁻¹ ^ 2 • chrUHSderiv d a b := by
  have hq0 : q 3 ≠ 0 := ne_of_gt hq
  have hchr : ∀ q' : E4, q' 3 ≠ 0 → koszulChr uhsMetric q' a b = chrUHS q' a b :=
    fun q' hq' => uhs_sec_koszulChr q' hq' a b
  have hev : (fun q' : E4 => koszulChr uhsMetric q' a b)
      =ᶠ[𝓝 q] (fun q' : E4 => (q' 3)⁻¹ • chrUHSvec a b) := by
    filter_upwards [(coord 3).continuous.continuousAt.eventually_ne hq0] with q' hq'
    rw [hchr q' hq']
    rfl
  have hψ : HasDerivAt (fun s : ℝ => s⁻¹ • chrUHSvec a b)
      ((-(q 3 ^ 2)⁻¹) • chrUHSvec a b) (q 3) :=
    (hasDerivAt_inv hq0).smul_const (chrUHSvec a b)
  have hF : HasFDerivAt (fun q' : E4 => (q' 3)⁻¹ • chrUHSvec a b)
      (ContinuousLinearMap.toSpanSingleton ℝ ((-(q 3 ^ 2)⁻¹) • chrUHSvec a b) ∘SL coord 3) q :=
    HasFDerivAt.comp q (g := fun y : ℝ => y⁻¹ • chrUHSvec a b) hψ.hasFDerivAt
      (hasFDerivAt_coord 3 q)
  rw [dBmodel, hev.fderiv_eq, hF.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, coord_apply,
    chrUHSderiv, smul_smul]
  congr 1
  field_simp

/-- **The upper half space metric has constant curvature `-1`.**  For
`q 3 > 0` and all `u v`,
`uhsMetric q (R(∂_u,∂_v)∂_v) u = -(⟪u,u⟫⟪v,v⟫ - ⟪u,v⟫²)`. -/
theorem uhs_sec (q : E4) (hq : 0 < q 3) (u v : E4) :
    uhsMetric q (modelCurv uhsMetric q u v v) u
      = -(uhsMetric q u u * uhsMetric q v v - uhsMetric q u v ^ 2) := by
  have hq0 : q 3 ≠ 0 := ne_of_gt hq
  have hkos : ∀ a b : E4, koszulChr uhsMetric q a b = chrUHS q a b :=
    fun a b => uhs_sec_koszulChr q hq0 a b
  have hdb : ∀ d a b : E4, dBmodel uhsMetric q d a b = (q 3)⁻¹ ^ 2 • chrUHSderiv d a b :=
    fun d a b => uhs_sec_dBmodel q hq d a b
  simp only [uhsMetric_apply, uhs_sec_inner_E4]
  rw [modelCurv, hdb u v v, hdb v v u]
  simp only [hkos, chrUHS, chrUHSderiv, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply]
  simp [chrUHSvec]
  ring_nf

end

end Work.Curvature
