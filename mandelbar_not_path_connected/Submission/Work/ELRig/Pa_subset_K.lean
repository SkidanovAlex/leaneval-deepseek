/-
# The attracting petal of the parabolic flower lies in the filled Julia set

`Work.ELRig.Pa_subset_K` : the (wide) attracting petal `Pa` of the Leau–Fatou flower of the
simple parabolic point `z₁` of `F c = (T_c)^[10]` is contained in the filled Julia set
`K c = {z | BoundedOrbit c z}` of the quadratic antiholomorphic map `T_c(z) = z̄² + c`.

The mathematics is one line: by `FlowerData.tendsto_Pa` the `F c`-orbit of a point `z ∈ Pa`
converges to `z₁`, hence *some* subsequence of the `T_c`-orbit of `z` converges (namely the
subsequence of indices divisible by `10`, because `F c = (T_c)^[10]`); and a `T_c`-orbit with a
convergent subsequence cannot escape, so it is bounded.  The escape dichotomy already available
in the workspace (`Work.ParamRays.escaping_iff_not_bounded`) turns the last remark into the
elementary lemma `boundedOrbit_of_tendsto_iterate_mul` proved here.
-/
import Mathlib
import Submission.Work.ELRig.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar)

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELRig

/-- **A converging sub-orbit is bounded.**  If, for some `k ≥ 1`, the subsequence of the
`T_c`-orbit of `z` along the multiples of `k` converges to a point `w`, then the whole orbit of
`z` is bounded.

Indeed a bounded orbit is exactly a non-escaping one (`Work.ParamRays.escaping_iff_not_bounded`);
if the orbit escaped then so would the subsequence `n ↦ k * n` (`k ≥ 1`), contradicting its
convergence to `w`. -/
theorem boundedOrbit_of_tendsto_iterate_mul {c w z : ℂ} {k : ℕ} (hk : 0 < k)
    (h : Tendsto (fun n : ℕ => (Tantibar c)^[k * n] z) atTop (nhds w)) :
    Work.ParamRays.BoundedOrbit c z := by
  by_contra hb
  have hesc : Tendsto (fun n : ℕ => ‖(Tantibar c)^[n] z‖) atTop atTop :=
    (Work.ParamRays.escaping_iff_not_bounded c z).mpr hb
  -- the index map `n ↦ k * n` tends to infinity
  have hφ : Tendsto (fun n : ℕ => k * n) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun a ha => le_trans ha (Nat.le_mul_of_pos_left a hk)⟩
  -- hence the norms along the subsequence tend to `+∞`
  have hcomp : Tendsto (fun n : ℕ => ‖(Tantibar c)^[k * n] z‖) atTop atTop := hesc.comp hφ
  -- but they also converge to `‖w‖`
  have hlim : Tendsto (fun n : ℕ => ‖(Tantibar c)^[k * n] z‖) atTop (nhds ‖w‖) := h.norm
  obtain ⟨n, hn1, hn2⟩ := ((hcomp.eventually (eventually_gt_atTop (‖w‖ + 1))).and
    (hlim.eventually (eventually_lt_nhds (lt_add_one ‖w‖)))).exists
  exact absurd hn2 (not_lt.mpr (le_of_lt hn1))

theorem Pa_subset_K {c z₁ : ℂ}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) z₁) :
    fl.Pa ⊆ Work.EL.K c := by
  intro z hz
  -- `F c = (T_c)^[10]`, so the `n`-th `F c`-iterate is the `10 n`-th `T_c`-iterate
  have hF : Work.EL.F c = (Tantibar c)^[10] := Work.EL.F_eq_tantibar c
  have hiter : ∀ n : ℕ, (Work.EL.F c)^[n] z = (Tantibar c)^[10 * n] z := by
    intro n
    rw [hF, Function.iterate_mul]
  -- the `T_c`-orbit of `z` along the multiples of `10` converges to `z₁`
  have hsub : Tendsto (fun n : ℕ => (Tantibar c)^[10 * n] z) atTop (nhds z₁) :=
    Tendsto.congr' (Eventually.of_forall fun n => hiter n) (fl.tendsto_Pa z hz)
  exact boundedOrbit_of_tendsto_iterate_mul (by norm_num) hsub

end Work.ELRig
