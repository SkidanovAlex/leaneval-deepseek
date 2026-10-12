import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.TrialState.Basic.measurePreserving_actPerm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

/-- Writing `u` into slot `i` and `v` into slot `j` of a relabelled configuration
(`i ↔ j`) gives the same configuration as doing it without relabelling: the two
updates overwrite exactly the two slots that the transposition moves. -/
private lemma upd_upd_actPerm_swap {n : ℕ} {i j : Fin n}
    (x : Submission.BoseGases.X n) (u v : EuclideanSpace ℝ (Fin 3)) :
    Function.update (Function.update (Submission.BoseGases.actPerm n (Equiv.swap i j) x) i u) j v
      = Function.update (Function.update x i u) j v := by
  funext m
  simp only [Submission.BoseGases.actPerm, Function.update_apply]
  by_cases hmj : m = j
  · simp only [if_pos hmj]
  · by_cases hmi : m = i
    · simp only [if_neg hmj, if_pos hmi]
    · simp only [if_neg hmj, if_neg hmi, Equiv.swap_apply_of_ne_of_ne hmi hmj]

/-- **The slot swap.**  If `G` is invariant under the transposition `i ↔ j` of the particle
slots, then exchanging the two *argument slots* `(q.1 i) ↔ (q.1 j)` of `F` does not change the
integral: the change of variables `x ↦ x ∘ (swap i j)` on the configuration space is
Lebesgue-measure preserving (`Work.TrialState.Basic.measurePreserving_actPerm`), it leaves the
integrand's `Θ`-factor `Θ (x[i↦q.1][j↦q.2])` unchanged (`upd_upd_actPerm_swap`), and it
exchanges `(q.1 i)` with `(q.1 j)`. -/
theorem configSlotSwap {n : ℕ} {i j : Fin n} (hij : i ≠ j) (G : Submission.BoseGases.X n → ℂ)
    (hG : ∀ x, G (Submission.BoseGases.actPerm n (Equiv.swap i j) x) = G x)
    (Θ : Submission.BoseGases.X n → ℝ) (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ) :
    (∫ q : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        G q.1 * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
          * F q.2.1 q.2.2 (q.1 i) (q.1 j))
      = ∫ q : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        G q.1 * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
          * F q.2.1 q.2.2 (q.1 j) (q.1 i) := by
  -- the slot permutation is a measurable embedding and preserves Lebesgue measure
  have hemb1 : MeasurableEmbedding (Submission.BoseGases.actPerm n (Equiv.swap i j)) := by
    rw [Work.TrialState.Basic.actPerm_eq_piCongrLeft n (Equiv.swap i j)]
    exact MeasurableEquiv.measurableEmbedding _
  have hmp1 : MeasurePreserving (Submission.BoseGases.actPerm n (Equiv.swap i j))
      (volume : Measure (Submission.BoseGases.X n)) volume :=
    Work.TrialState.Basic.measurePreserving_actPerm n (Equiv.swap i j)
  -- the same map on the product with the two momentum slots held fixed
  have hmpS : MeasurePreserving
      (fun q : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        (Submission.BoseGases.actPerm n (Equiv.swap i j) q.1, q.2))
      (volume : Measure (Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))))
      (volume : Measure (Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))) :=
    hmp1.prod (MeasurePreserving.id _)
  have hembS : MeasurableEmbedding
      (fun q : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        (Submission.BoseGases.actPerm n (Equiv.swap i j) q.1, q.2)) :=
    MeasurableEmbedding.prodMap hemb1 MeasurableEmbedding.id
  -- change variables: the integral of the "swapped" integrand is the integral after relabelling
  have key := MeasurePreserving.integral_comp hmpS hembS
    (fun q : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
      G q.1 * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
        * F q.2.1 q.2.2 (q.1 j) (q.1 i))
  rw [← key]
  apply integral_congr_ae
  filter_upwards with q
  obtain ⟨x, u, v⟩ := q
  rw [hG x, upd_upd_actPerm_swap x u v]
  have h1 : Submission.BoseGases.actPerm n (Equiv.swap i j) x i = x j := by
    simp [Submission.BoseGases.actPerm, Equiv.swap_apply_left]
  have h2 : Submission.BoseGases.actPerm n (Equiv.swap i j) x j = x i := by
    simp [Submission.BoseGases.actPerm, Equiv.swap_apply_right]
  rw [h1, h2]

end Work.BoseBoxFock.PCFU
