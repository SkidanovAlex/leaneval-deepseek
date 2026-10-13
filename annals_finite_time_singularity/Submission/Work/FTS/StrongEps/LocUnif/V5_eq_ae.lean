import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.LocUnif.V5Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The order-5 `ℋ`-majorant `V5` agrees a.e. with `ofReal (HkIntegrand α 5 f)`

`V5 α fn p` is, by definition, the `liminf`, as `n → ∞`, of `ofReal (HkIntegrand α 5 (fn n) p)`.
Every slot of `HkIntegrand α 5` is a `mixed j i` with `i + j ≤ 5` (the `D_z^i`-terms are the slots
`(j,i) = (i,0)`, since `mixed j 0 = DzIter j`).  The slots with `i + j ≤ 4` converge everywhere on
the rectangle `[a,b] × [c,d]` (hypothesis `hconv4`) and those with `i + j = 5` converge almost
everywhere (hypothesis `hconv5`), so a.e. the whole integrand converges and its `liminf` is the
value at `f`. -/

open MeasureTheory Filter

namespace Work.FTS.StrongEps.LocUnif

/-- **Convergence of the `ℋ^5`-integrand from convergence of the slots.**  If at a point `p` every
slot `D_z^j D_θ^i (fn n)` with `j + i ≤ 5` converges to the corresponding slot of `f`, then the
value of `HkIntegrand α 5 (fn n)` at `p` converges to the value at `p` of `HkIntegrand α 5 f`
(the weights depend only on `p`, and the sum is finite). -/
private lemma tendsto_HkIntegrand_of_tendsto_mixed {α : ℝ} {fn : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    {p : ℝ × ℝ}
    (h : ∀ j i : ℕ, j + i ≤ 5 →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (fn n) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i f p.1 p.2))) :
    Filter.Tendsto (fun n => Work.Spaces.HkIntegrand α 5 (fn n) p.1 p.2) Filter.atTop
      (nhds (Work.Spaces.HkIntegrand α 5 f p.1 p.2)) := by
  -- every summand is a slot times a weight depending only on `p`, squared
  have key : ∀ (c : ℝ) (j i : ℕ), j + i ≤ 5 →
      Filter.Tendsto (fun n => (Work.Spaces.mixed j i (fn n) p.1 p.2 * c) ^ 2) Filter.atTop
        (nhds ((Work.Spaces.mixed j i f p.1 p.2 * c) ^ 2)) :=
    fun c j i hji => ((h j i hji).mul_const c).pow 2
  simp only [Work.Spaces.HkIntegrand]
  refine Tendsto.add ?_ ?_
  · -- the `D_z^i`-block: `DzIter i g = mixed i 0 g`
    refine tendsto_finsetSum (Finset.range (5 + 1)) (fun i hi => ?_)
    exact key _ i 0 (by have := Finset.mem_range.mp hi; omega)
  · -- the mixed block
    refine tendsto_finsetSum (Finset.range (5 + 1)) (fun i hi => ?_)
    refine tendsto_finsetSum (Finset.range (5 + 1)) (fun j hj => ?_)
    by_cases hc : 1 ≤ i ∧ i + j ≤ 5
    · simp only [ite_eq_left hc]
      exact key _ j i (by omega)
    · simp only [ite_eq_right hc]
      exact tendsto_const_nhds

theorem V5_eq_ae {α : ℝ} {fn : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hconv4 : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d, ∀ (j i : ℕ), j + i ≤ 4 →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (fn n) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i f p.1 p.2)))
    (hconv5 : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)),
      ∀ (j i : ℕ), j + i = 5 →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (fn n) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i f p.1 p.2))) :
    Work.FTS.StrongEps.LocUnif.V5 α fn =ᵐ[MeasureTheory.volume.restrict
        (Set.Icc a b ×ˢ Set.Icc c d)]
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 f p.1 p.2)) := by
  have hs : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d) :=
    measurableSet_Icc.prod measurableSet_Icc
  filter_upwards [hconv5, ae_restrict_mem hs] with p h5 hpmem
  rw [V5]
  -- all the slots of order `≤ 5` converge at `p`
  have hall : ∀ j i : ℕ, j + i ≤ 5 →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (fn n) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i f p.1 p.2)) := by
    intro j i hji
    rcases lt_or_eq_of_le hji with hlt | heq
    · exact hconv4 p hpmem j i (by omega)
    · exact h5 j i heq
  have ht := tendsto_HkIntegrand_of_tendsto_mixed (α := α) hall
  exact ((ENNReal.continuous_ofReal.tendsto
    (Work.Spaces.HkIntegrand α 5 f p.1 p.2)).comp ht).liminf_eq

end Work.FTS.StrongEps.LocUnif
