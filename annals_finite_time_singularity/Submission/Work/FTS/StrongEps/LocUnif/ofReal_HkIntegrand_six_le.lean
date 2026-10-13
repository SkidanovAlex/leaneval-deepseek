/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise majorisation of the level-6 integrand by the level-5 integrand and `V6z,V6t`

This file proves the "pointwise majorisation" step of the energy bound
`HkNorm α 6 f ≤ B` of `Work.FTS.StrongEps.exists_locUnif_subseq_of_uniform_H6`
(see `LocUnif/NOTES_assembly_final.md`, items 2 and 3):

* `HkIntegrand α 6 f = HkIntegrand α 5 f + level6Z α f + level6T α f` (the level-6 slots are
  `z ∂_z` resp. `sin(2θ) ∂_θ` of level-5 slots; `level6_identities`);
* the `z`-directed level-6 slots are dominated, through `ofReal`, by the liminf over the
  *backward difference quotients* of the level-5 slots (the per-term pointwise FTC input
  `ofReal_deriv_sq_le_liminf_backwardDiffQuot`, summed with the Fatou-type inequality
  `liminf` of a finite sum `≤` finite sum of `liminf`s);
* the `θ`-directed slot is handled by a single application of the same input.

Everything is unconditional and pointwise; no smoothness or integrability hypothesis is used.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.StrongEps.LocUnif.V6Defs
import Submission.Work.FTS.StrongEps.LocUnif.tendsto_backward_diffQuot
import Submission.Work.FTS.StrongEps.LocUnif.ofReal_deriv_sq_le_liminf_backwardDiffQuot
import Submission.Work.FTS.StrongEps.LocUnif.level6_identities

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped ENNReal
open Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-! ## The Fatou-type inequality for `liminf` of a finite sum in `ℝ≥0∞`

In `ℝ≥0∞` addition preserves arbitrary suprema (`ENNReal.iSup_add`, `ENNReal.add_iSup`), so
`liminf u + liminf v ≤ liminf (u + v)` for every filter (the superadditivity direction, i.e. the
Fatou direction: the left side is *smaller*).  Finitely many summands follow by induction. -/

private lemma liminf_add_le_ennreal (u v : ℕ → ℝ≥0∞) :
    Filter.liminf u Filter.atTop + Filter.liminf v Filter.atTop
      ≤ Filter.liminf (fun n => u n + v n) Filter.atTop := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat]
  rw [ENNReal.iSup_add]
  refine iSup_le fun N => ?_
  rw [ENNReal.add_iSup]
  refine iSup_le fun M => ?_
  rw [Filter.liminf_eq_iSup_iInf_of_nat]
  refine le_iSup_of_le (max N M) ?_
  refine le_iInf fun n => le_iInf fun hn => ?_
  have hN : N ≤ n := le_trans (le_max_left _ _) hn
  have hM : M ≤ n := le_trans (le_max_right _ _) hn
  have h1 : (⨅ i, ⨅ (_ : i ≥ N), u i) ≤ u n := le_trans (iInf_le _ n) (iInf_le _ hN)
  have h2 : (⨅ i, ⨅ (_ : i ≥ M), v i) ≤ v n := le_trans (iInf_le _ n) (iInf_le _ hM)
  exact add_le_add h1 h2

/-- The Fatou-type inequality for a finite sum of `ℝ≥0∞`-valued sequences: the sum of the
`liminf`s is at most the `liminf` of the sums. -/
private theorem liminf_finset_sum_le {ι : Type*} (s : Finset ι) (u : ι → ℕ → ℝ≥0∞) :
    (∑ k ∈ s, Filter.liminf (u k) Filter.atTop)
      ≤ Filter.liminf (fun n => ∑ k ∈ s, u k n) Filter.atTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      calc Filter.liminf (u a) Filter.atTop + (∑ k ∈ s, Filter.liminf (u k) Filter.atTop)
          ≤ Filter.liminf (u a) Filter.atTop
              + Filter.liminf (fun n => ∑ k ∈ s, u k n) Filter.atTop :=
            add_le_add le_rfl ih
        _ ≤ Filter.liminf (fun n => u a n + ∑ k ∈ s, u k n) Filter.atTop :=
            liminf_add_le_ennreal _ _

/-! ## The majorisation -/

/-- The level-6 integrand is dominated, in `ℝ≥0∞`, by the level-5 integrand plus the two
measurable majorants `V6z`, `V6t` built from the backward difference quotients of the level-5
slots. -/
theorem ofReal_HkIntegrand_six_le (α : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 f p.1 p.2)
      ≤ ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 f p.1 p.2)
        + Work.FTS.StrongEps.LocUnif.V6z α f p
        + Work.FTS.StrongEps.LocUnif.V6t α f p := by
  obtain ⟨hid, hZ, hT⟩ := Work.FTS.StrongEps.LocUnif.level6_identities α
  -- The three nonnegativity facts needed to split `ofReal` of a sum.
  have h5 : 0 ≤ Work.Spaces.HkIntegrand α 5 f p.1 p.2 :=
    Work.Spaces.HkIntegrand_nonneg α 5 f p.1 p.2
  have hZnn : 0 ≤ level6Z α f p.1 p.2 := by
    rw [level6Z]
    exact Finset.sum_nonneg fun k _ => sq_nonneg _
  have hTnn : 0 ≤ level6T α f p.1 p.2 := by
    rw [level6T]
    exact sq_nonneg _
  -- Per-slot: the weighted level-6 `z`-slot is dominated by the liminf of the backward
  -- difference quotients of its level-5 parent.
  have hk : ∀ k ∈ Finset.range 6,
      ENNReal.ofReal ((deriv (fun z' => Work.Spaces.mixed (5 - k) k f z' p.2) p.1
          * (p.1 * rho6 α k p.1 p.2)) ^ 2)
        ≤ Filter.liminf (fun j : ℕ => ENNReal.ofReal
            (((Work.Spaces.mixed (5 - k) k f p.1 p.2
                - Work.Spaces.mixed (5 - k) k f (p.1 - 1 / ((j : ℝ) + 1)) p.2) * ((j : ℝ) + 1)
              * (p.1 * rho6 α k p.1 p.2)) ^ 2)) Filter.atTop :=
    fun k _ => ofReal_deriv_sq_le_liminf_backwardDiffQuot _ _ _
  -- The `z`-directed half.
  have hZle : ENNReal.ofReal (level6Z α f p.1 p.2) ≤ V6z α f p := by
    rw [hZ f p, ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    exact le_trans (Finset.sum_le_sum hk) (liminf_finset_sum_le (Finset.range 6) _)
  -- The `θ`-directed slot.
  have hTle : ENNReal.ofReal (level6T α f p.1 p.2) ≤ V6t α f p :=
    hT f p ▸ ofReal_deriv_sq_le_liminf_backwardDiffQuot
      (fun θ' => Work.Spaces.mixed 0 5 f p.1 θ') p.2
      (Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)
  calc ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 f p.1 p.2)
      = ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 f p.1 p.2
          + level6Z α f p.1 p.2 + level6T α f p.1 p.2) := by rw [hid f p.1 p.2]
    _ = ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 f p.1 p.2)
          + ENNReal.ofReal (level6Z α f p.1 p.2)
          + ENNReal.ofReal (level6T α f p.1 p.2) := by
        rw [ENNReal.ofReal_add (add_nonneg h5 hZnn) hTnn, ENNReal.ofReal_add h5 hZnn]
    _ ≤ ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 f p.1 p.2)
          + V6z α f p + V6t α f p := add_le_add (add_le_add le_rfl hZle) hTle

end Work.FTS.StrongEps.LocUnif
