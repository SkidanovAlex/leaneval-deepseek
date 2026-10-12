import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Submission.Work.BoseBoxFock.PB3FibreQ
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-!
# `Work.BoseBoxFock.sum_limSlotForm_eq_q2MassChi`

The per-slot limit form `limSlotForm ℓ j Θ` is *definitionally* the `χ²`-weighted box mass of the
slot-`j` box projection `boxQ ℓ j Θ`:

    `limSlotForm ℓ j Θ = ∫_{abox n ℓ} χ_ℓ(x_j)² ‖boxQ ℓ j Θ x‖²`.

For the box restriction `boxRestrictC ℓ Φ` of a real state `Φ`, the pointwise identity

    `boxQ ℓ j (boxRestrictC ℓ Φ) x = ↑(aQ ℓ j Φ x)    (x ∈ abox n ℓ)`

holds because (i) on the box the restriction is `↑(Φ x)`, and (ii) the inner `acube ℓ`-integral of
the restricted state inserts the slot value back *into the box* (`update_mem_abox_of_mem`), so it is
the coercion of the corresponding real integral (`integral_ofReal`).  Summing in `j` gives the
requested identity with the corpus quantity `q2MassChi`.
-/

/-- Inserting a value of the one-particle cube into a configuration of the box keeps it in the
box: `update` of a slot of `x ∈ abox n ℓ` by `y ∈ acube ℓ` remains in `abox n ℓ`. -/
private lemma update_mem_abox_of_mem {n : ℕ} {ℓ : ℝ} {x : Submission.BoseGases.X n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) (j : Fin n) {y : EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ Submission.BoseGases.acube ℓ) :
    Function.update x j y ∈ Submission.BoseGases.abox n ℓ := by
  rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
  intro i
  by_cases h : i = j
  · subst h; rw [Function.update_self]; exact hy
  · rw [Function.update_of_ne h]; exact hx i

/-- **The limit slot form of a box-restricted real state is the `χ²`-weighted slot-`j` `Q`-mass.**
On the box, the slot-`j` box projection of the complex restriction `boxRestrictC ℓ Φ` is the
coercion of the corpus's real slot projection `aQ ℓ j Φ`. -/
lemma limSlotForm_boxRestrictC_eq {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ)
    (j : Fin n) :
    limSlotForm ℓ j (boxRestrictC ℓ Φ)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.aQ ℓ j Φ x) ^ 2 * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2 := by
  rw [limSlotForm]
  refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
    (fun x hx => ?_)
  have hpt : boxQ ℓ j (boxRestrictC ℓ Φ) x = ((Submission.BoseGases.aQ ℓ j Φ x : ℝ) : ℂ) := by
    have hxr : boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) := by
      simp only [boxRestrictC, Set.indicator_of_mem hx, Complex.ofReal_one, mul_one]
    have hint : (∫ y in Submission.BoseGases.acube ℓ, boxRestrictC ℓ Φ (Function.update x j y))
        = ((∫ y in Submission.BoseGases.acube ℓ, Φ (Function.update x j y) : ℝ) : ℂ) := by
      have hcongr : (∫ y in Submission.BoseGases.acube ℓ,
            boxRestrictC ℓ Φ (Function.update x j y))
          = ∫ y in Submission.BoseGases.acube ℓ, ((Φ (Function.update x j y) : ℝ) : ℂ) := by
        refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
          (fun y hy => ?_)
        simp only [boxRestrictC, Set.indicator_of_mem (update_mem_abox_of_mem hx j hy),
          Complex.ofReal_one, mul_one]
      rw [hcongr]
      exact integral_ofReal
    simp only [boxQ, hxr, hint, Submission.BoseGases.aQ, Submission.BoseGases.aP, one_div,
      Complex.ofReal_sub, Complex.ofReal_mul]
  rw [hpt]
  have hnorm : ‖((Submission.BoseGases.aQ ℓ j Φ x : ℝ) : ℂ)‖ ^ 2
      = (Submission.BoseGases.aQ ℓ j Φ x) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  rw [hnorm]
  exact mul_comm _ _

theorem sum_limSlotForm_eq_q2MassChi {n : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))} :
    (∑ j : Fin n, Work.BoseBoxFock.limSlotForm (Work.BoseBoxFock.ellH v μ) j
        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
          (Φ : Submission.BoseGases.X n → ℝ)))
      = Submission.BoseGases.q2MassChi (N := n) (Work.BoseBoxFock.ellH v μ)
          (Φ := (Φ : Submission.BoseGases.X n → ℝ)) := by
  rw [Submission.BoseGases.q2MassChi]
  exact Finset.sum_congr rfl (fun j _ => limSlotForm_boxRestrictC_eq (ellH v μ) _ j)

end Work.BoseBoxFock
