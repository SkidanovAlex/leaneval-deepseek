import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxCompT_orth
import Submission.Work.BoseFixB1S.boxCompT_sum_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The finset of ordered pairs `(S,T)` of **disjoint** subsets of `Fin N`: the index set of the
three-way joint decomposition of the commuting box projections. -/
def disjPairs (N : ℕ) : Finset (Finset (Fin N) × Finset (Fin N)) :=
  (Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).filter (fun p => Disjoint p.1 p.2)

/-- Membership in `disjPairs`. -/
theorem mem_disjPairs {N : ℕ} {p : Finset (Fin N) × Finset (Fin N)} :
    p ∈ disjPairs N ↔ Disjoint p.1 p.2 := by
  simp [disjPairs]

/-- A measurable function bounded on the (finite-measure) analysis box is integrable there. -/
theorem integrableOn_abox_of_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f : X N → ℝ}
    (hm : Measurable f) {C : ℝ} (hb : ∀ x ∈ abox N ℓ, |f x| ≤ C) :
    IntegrableOn f (abox N ℓ) volume := by
  have hfin : (volume : Measure (X N)) (abox N ℓ) < ⊤ := abox_lt_top N ℓ hℓ.le
  refine IntegrableOn.of_bound hfin hm.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' (abox_measurable N ℓ)]
  exact Filter.Eventually.of_forall (fun x hx => by rw [Real.norm_eq_abs]; exact hb x hx)

/-- Products of `GoodState`s are integrable on the analysis box (both factors are measurable and
bounded on the box). -/
theorem integrableOn_mul_goodState {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {F G : X N → ℝ}
    (hF : GoodState ℓ F) (hG : GoodState ℓ G) :
    IntegrableOn (fun x => F x * G x) (abox N ℓ) volume := by
  obtain ⟨hFm, CF, hFb⟩ := hF
  obtain ⟨hGm, CG, hGb⟩ := hG
  refine integrableOn_abox_of_bound hℓ (hFm.mul hGm) (C := max CF 0 * max CG 0) (fun x hx => ?_)
  rw [abs_mul]
  have h1 : |F x| ≤ max CF 0 := le_trans (hFb x hx) (le_max_left _ _)
  have h2 : |G x| ≤ max CG 0 := le_trans (hGb x hx) (le_max_left _ _)
  exact mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)

end Work.BoseFixB1S
