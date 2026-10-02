import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.tantibar_family_continuous
import Submission.Work.LandLeaves.deriv_tantibar_family_continuous
import Submission.Work.LandLeaves.continuous_family_fixedpoint
import Submission.Work.LandLeaves.isRepelling_iterate_mul
import Submission.Work.LandLeaves.local_repelling_branch_family

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Uniform expansion of the family `(T_f)^{2(kq)}` at a repelling periodic point

`Work.LandLeaves.local_repelling_branch_family` produces, at a repelling periodic point `y` of
the tricorn family `T_c z = z̄² + c` of period `k`, a continuous family `f ↦ yf f` of fixed
points of `(T_f)^{2k}` near `y`, a local inverse branch `gg` of `(T_f)^{2k}` around `yf f`
(`hright`, `hleft`) contracting toward `yf f` (`hcontr`), and the *injectivity* of `(T_f)^{2k}`
on the ball `B(yf f, r')` (`hinj`).

Those four properties together say that `(T_f)^{2k}` is *expanding* on a small ball around
`yf f`: for every `u` in the ball,

  `‖u - yf f‖ ≤ κ' * ‖(T_f)^{2k} u - yf f‖`.

The argument is the standard "inverse branch + injectivity" one:

* if `h u` is still inside the ball `B(yf f, r')`, then `u' = gg f (h u)` is the inverse image of
  `h u` produced by the branch; it lies in `B(yf f, κ r') ⊆ B(yf f, r')` by the contraction
  estimate, so `u` and `u'` are two points of that ball with the same image under `h` — injectivity
  gives `u = u'`, and the contraction estimate turns into `‖u - yf f‖ ≤ κ ‖h u - yf f‖`;
* if `h u` has left the ball, then `‖u - yf f‖ ≤ r'/2 ≤ (1/2) r' < ‖h u - yf f‖`, so the
  inequality holds with the constant `1/2`.

Taking `κ' = max κ (1/2)` (written as `(1 + κ)/2`) gives a single constant `< 1`.

The statement of this file is the `q`-th iterate form: it is applied to the *multiple* period
`k * q` (a repelling periodic point of period `k` is one of period `k * q`,
`Work.LandLeaves.isRepelling_iterate_mul`), so that the map `(T_f)^{2*(k*q)}` of the conclusion
is exactly the second return map of the multiple period.

## Main result

* `Work.LandLeaves.family_repelling_expansion`.
-/

open Function Filter
open scoped Topology

namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

theorem family_repelling_expansion {c : ℂ} {k q : ℕ} {y : ℂ}
    (hrep : Work.Landing.IsRepelling c k y) (hq : 0 < q) :
    ∃ (δ ρ κ : ℝ) (yf : ℂ → ℂ),
      0 < δ ∧ 0 < ρ ∧ 0 ≤ κ ∧ κ < 1 ∧ yf c = y ∧ ContinuousAt yf c ∧
      (∀ f : ℂ, ‖f - c‖ < δ → (LeanEval.ComplexAnalysis.Tantibar f)^[2 * (k * q)] (yf f) = yf f) ∧
      (∀ f : ℂ, ‖f - c‖ < δ → ∀ u : ℂ, ‖u - yf f‖ ≤ ρ →
        ‖u - yf f‖ ≤ κ * ‖(LeanEval.ComplexAnalysis.Tantibar f)^[2 * (k * q)] u - yf f‖) := by
  -- a repelling periodic point of period `k` is one of period `k * q`
  have hrep' : Work.Landing.IsRepelling c (k * q) y := isRepelling_iterate_mul hrep hq
  -- the local repelling branch family at the multiple period
  obtain ⟨δ, r, r', κ, yf, gg, hδ, hr, hrr, hκ0, hκ1, hyfc, hyfAt, hfix, hcontr, hright,
    hleft, hinj, hcont⟩ := local_repelling_branch_family (k := k * q) hrep'
  have hr'pos : 0 < r' := lt_trans hr hrr
  -- the expansion constant `κ' = (1 + κ)/2 ∈ [1/2, 1)`
  refine ⟨δ, r' / 2, (1 + κ) / 2, yf, hδ, by linarith, by linarith, by linarith, hyfc, hyfAt,
    hfix, ?_⟩
  intro f hf u hu
  have hκ'0 : 0 ≤ (1 + κ) / 2 := by linarith
  have hκ'half : (1 : ℝ) / 2 ≤ (1 + κ) / 2 := by linarith
  have hκκ' : κ ≤ (1 + κ) / 2 := by linarith
  by_cases hcase : ‖(Tantibar f)^[2 * (k * q)] u - yf f‖ ≤ r'
  · -- inside the ball: the branch gives a point of the ball with the same image, so injectivity
    set u' : ℂ := gg f ((Tantibar f)^[2 * (k * q)] u) with hu'def
    have hfix_u' : (Tantibar f)^[2 * (k * q)] u' = (Tantibar f)^[2 * (k * q)] u := by
      rw [hu'def]
      exact hright f hf _ hcase
    have hcontr_u' : ‖u' - yf f‖ ≤ κ * ‖(Tantibar f)^[2 * (k * q)] u - yf f‖ := by
      rw [hu'def]
      exact hcontr f hf _ hcase
    have haux : κ * ‖(Tantibar f)^[2 * (k * q)] u - yf f‖ ≤ κ * r' :=
      mul_le_mul_of_nonneg_left hcase hκ0
    have hlt : ‖u' - yf f‖ < r' := by
      have h2 : κ * r' < r' := by
        have h3 := mul_lt_mul_of_pos_right hκ1 hr'pos
        simpa using h3
      linarith
    have hball_u : u ∈ Metric.ball (yf f) r' := by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith
    have hball_u' : u' ∈ Metric.ball (yf f) r' := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hlt
    have heq : u = u' := hinj f hf hball_u hball_u' hfix_u'.symm
    have hstep : ‖u' - yf f‖ ≤ (1 + κ) / 2 * ‖(Tantibar f)^[2 * (k * q)] u' - yf f‖ := by
      rw [hfix_u']
      exact le_trans hcontr_u'
        (mul_le_mul_of_nonneg_right hκκ' (norm_nonneg _))
    rw [heq]
    exact hstep
  · -- outside the ball: `‖u - yf f‖ ≤ r'/2 ≤ κ' r' < κ' ‖h u - yf f‖`
    have hgt : r' < ‖(Tantibar f)^[2 * (k * q)] u - yf f‖ := not_le.mp hcase
    calc ‖u - yf f‖ ≤ r' / 2 := hu
      _ ≤ (1 + κ) / 2 * r' := by nlinarith [hκ'half, hr'pos]
      _ ≤ (1 + κ) / 2 * ‖(Tantibar f)^[2 * (k * q)] u - yf f‖ :=
          mul_le_mul_of_nonneg_left hgt.le hκ'0

end Work.LandLeaves
