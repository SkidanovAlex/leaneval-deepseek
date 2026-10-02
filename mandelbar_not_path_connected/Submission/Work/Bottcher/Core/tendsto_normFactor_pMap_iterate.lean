/-
# The normalised factor `p_c(z)/z^4 → 1` along an escaping orbit

`normFactor c w = p_map c w / w^4 = 1 + O(w^{-2})` is the factor appearing in the
Böttcher product formula.  Along any orbit whose norms escape to infinity it tends
to `1`; this is the basic asymptotic that makes the Böttcher series summable and the
Böttcher coordinate tangent to the identity at infinity.

The hypothesis of the main theorem is stated for the *anti-holomorphic* iterator
`Tantibar c` (the tricorn map `z ↦ z̄² + c`); since `pMap c = (Tantibar c)^[2]`, the
even-indexed subsequence of the `Tantibar`-orbit is the `pMap`-orbit, so it escapes
along it as well.

Note that the `pMap`-orbit need *not* avoid `0` at every time (the critical orbit may
escape after hitting `0`), so `normFactor` is undefined-as-a-quotient (`= 0`) at those
indices; only the eventual non-vanishing is used, which is all that a limit sees.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Bottcher.Core.norm_bottcher_eq_exp_green

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Core

open LeanEval.ComplexAnalysis (Tantibar)
open Work.Bottcher

/-- If the norms of the `Tantibar c`-iterates of `z` escape to infinity, then so do
the norms of the `pMap c`-iterates, because `pMap c = (Tantibar c)^[2]`. -/
theorem tendsto_norm_pMap_iterate (c z : ℂ)
    (h : Tendsto (fun n : ℕ => ‖(Tantibar c)^[n] z‖) atTop atTop) :
    Tendsto (fun n : ℕ => ‖(pMap c)^[n] z‖) atTop atTop := by
  have h2N : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
  have hsub : Tendsto (fun N : ℕ => ‖(Tantibar c)^[2 * N] z‖) atTop atTop := h.comp h2N
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun N => ?_)) hsub
  show ‖(Tantibar c)^[2 * N] z‖ = ‖(pMap c)^[N] z‖
  rw [pMap_iterate]

/-- Along an orbit whose norms escape to infinity, the normalised factor tends to
`1`; only *eventual* non-vanishing is required (finitely many zero terms do not
affect the limit). -/
theorem normFactor_tendsto_one_of_eventually (c z : ℂ)
    (hw : ∀ᶠ n : ℕ in atTop, (pMap c)^[n] z ≠ 0)
    (hu : Tendsto (fun n : ℕ => ‖(pMap c)^[n] z‖) atTop atTop) :
    Tendsto (fun n : ℕ => normFactor c ((pMap c)^[n] z)) atTop (nhds 1) := by
  have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨max b 1, fun a ha => by
      have hb : b ≤ a := (le_max_left b 1).trans ha
      have h1 : (1 : ℝ) ≤ a := (le_max_right b 1).trans ha
      nlinarith [hb, h1]⟩)
  have h2 : Tendsto (fun n : ℕ => ‖(pMap c)^[n] z‖ ^ 2) atTop atTop := hsq.comp hu
  have h4 : Tendsto (fun n : ℕ => ‖(pMap c)^[n] z‖ ^ 4) atTop atTop := by
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun n => ?_)) (hsq.comp h2)
    show (‖(pMap c)^[n] z‖ ^ 2) ^ 2 = ‖(pMap c)^[n] z‖ ^ 4
    ring
  have hg : Tendsto (fun n : ℕ => 2 * ‖c‖ / ‖(pMap c)^[n] z‖ ^ 2
        + (‖c‖ ^ 2 + ‖c‖) / ‖(pMap c)^[n] z‖ ^ 4) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => 2 * ‖c‖ / ‖(pMap c)^[n] z‖ ^ 2) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop h2
    have h2' : Tendsto (fun n : ℕ => (‖c‖ ^ 2 + ‖c‖) / ‖(pMap c)^[n] z‖ ^ 4) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop h4
    simpa using h1.add h2'
  have hle : ∀ᶠ n : ℕ in atTop, ‖normFactor c ((pMap c)^[n] z) - 1‖
      ≤ 2 * ‖c‖ / ‖(pMap c)^[n] z‖ ^ 2 + (‖c‖ ^ 2 + ‖c‖) / ‖(pMap c)^[n] z‖ ^ 4 :=
    hw.mono (fun n hn => norm_normFactor_sub_one_le c _ hn)
  have hz0 : Tendsto (fun n : ℕ => ‖normFactor c ((pMap c)^[n] z) - 1‖) atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) hle hg
  have hz1 : Tendsto (fun n : ℕ => normFactor c ((pMap c)^[n] z) - 1) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hz0
  have hfin : Tendsto (fun n : ℕ => (normFactor c ((pMap c)^[n] z) - 1) + 1) atTop
      (nhds (0 + 1)) :=
    hz1.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1))
  simpa using hfin

theorem tendsto_normFactor_pMap_iterate (c z : ℂ)
    (h : Filter.Tendsto (fun n : ℕ => ‖(LeanEval.ComplexAnalysis.Tantibar c)^[n] z‖) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n : ℕ => Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] z))
      Filter.atTop (nhds 1) := by
  have hu : Tendsto (fun n : ℕ => ‖(pMap c)^[n] z‖) atTop atTop :=
    tendsto_norm_pMap_iterate c z h
  have hw : ∀ᶠ n : ℕ in atTop, (pMap c)^[n] z ≠ 0 := by
    filter_upwards [hu.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
    exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le zero_lt_one hn))
  exact normFactor_tendsto_one_of_eventually c z hw hu

end Work.Bottcher.Core
