import Submission.Work.Escape.GreenHarmonic
import Submission.Work.Escape.differentiable_shadowTd
import Submission.Work.Escape.norm_shadowTd
import Submission.Work.Escape.shadowTd_ratio_tendsto
import Submission.Work.Escape.poly_ratio_tendsto

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Harmonicity of the Green function of the unicritical families

The abstract theorem `Work.Escape.harmonicOnNhd_green` (in `GreenHarmonic.lean`) requires a family
of holomorphic shadows of the iterates whose "Böttcher ratios" tend to `1`.  Here we provide the
two explicit families:

* for the holomorphic polynomial `Tpoly d c = z^d + c` the iterates themselves are holomorphic
  shadows and the ratio is `1 + c / (Tpoly d c)^[k] z ^ d`;
* for the antiholomorphic antipolynomial `Td d c = z̄^d + c` the shadows are built in `Shadow.lean`
  (`shadowTd`), alternating `(Td ∘ Td)^[j]` and `fTd ∘ (Td ∘ Td)^[j]`.

Consequently the Green function of `z ↦ z^d + c` and of `z ↦ z̄^d + c` is harmonic off the filled
Julia set; specialising to `d = 2` gives the mandelbar/tricorn case.
-/

open Filter Function Metric Set InnerProductSpace
open scoped Topology

noncomputable section

namespace Work.Escape

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The holomorphic shadow family of the antipolynomial `Td d c`, built from `shadowTd`. -/
def shadowSeqTd (d : ℕ) (c : ℂ) (hd : 1 ≤ d) : ShadowSeq (Td d c) d where
  shadow := shadowTd d c
  differentiable := fun k => differentiable_shadowTd d c k
  norm_eq := fun k z => norm_shadowTd d c k z
  ratio := fun ε hε => shadowTd_ratio_tendsto d c hd ε hε

/-- `Tpoly d c` is holomorphic. -/
theorem differentiable_Tpoly (d : ℕ) (c : ℂ) : Differentiable ℂ (Tpoly d c) := by
  have h : Tpoly d c = fun z : ℂ => z ^ d + c := rfl
  rw [h]
  fun_prop

/-- The holomorphic shadow family of the polynomial `Tpoly d c`: the iterates themselves. -/
def shadowSeqTpoly (d : ℕ) (c : ℂ) (hd : 1 ≤ d) : ShadowSeq (Tpoly d c) d where
  shadow := fun k => (Tpoly d c)^[k]
  differentiable := fun k => (differentiable_Tpoly d c).iterate k
  norm_eq := fun k z => rfl
  ratio := fun ε hε => poly_ratio_tendsto d c hd ε hε

/-- The Green function of the unicritical polynomial `z ↦ z^d + c` is harmonic off the filled
Julia set. -/
theorem harmonicOnNhd_green_Tpoly (d : ℕ) (c : ℂ) (hd : 2 ≤ d) :
    HarmonicOnNhd (green (Tpoly d c) d) {z : ℂ | 0 < green (Tpoly d c) d z} :=
  harmonicOnNhd_green (Tpoly d c) d ‖c‖ (monicGrowth_Tpoly d c) hd
    (shadowSeqTpoly d c (by omega))

/-- The Green function of the unicritical antipolynomial `z ↦ z̄^d + c` is harmonic off the filled
Julia set. -/
theorem harmonicOnNhd_green_Td (d : ℕ) (c : ℂ) (hd : 2 ≤ d) :
    HarmonicOnNhd (green (Td d c) d) {z : ℂ | 0 < green (Td d c) d z} :=
  harmonicOnNhd_green (Td d c) d ‖c‖ (monicGrowth_Td d c) hd (shadowSeqTd d c (by omega))

/-- The Green function of the tricorn family `z ↦ z̄² + c` is harmonic off the filled Julia set
`K_c`. -/
theorem harmonicOnNhd_green_Tantibar (c : ℂ) :
    HarmonicOnNhd (green (Tantibar c) 2) {z : ℂ | 0 < green (Tantibar c) 2 z} :=
  harmonicOnNhd_green_Td 2 c le_rfl

/-- The Green function of the tricorn family is harmonic on the complement of the filled Julia
set: `G_c` is harmonic off `K_c`. -/
theorem harmonicOnNhd_green_compl_filledTricorn (c : ℂ) :
    HarmonicOnNhd (green (Tantibar c) 2) (filledTricorn c)ᶜ :=
  harmonicOnNhd_green_compl (Tantibar c) 2 ‖c‖ (monicGrowth_Tantibar c) le_rfl
    (shadowSeqTd 2 c (by omega))

end Work.Escape
