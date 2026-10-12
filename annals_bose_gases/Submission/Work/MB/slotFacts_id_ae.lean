import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.MB.slotExact_orth_ae
import Submission.Work.MB.slotFacts_dec_fibre_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MB.slotFacts_id_ae` — the `SlotFacts` instance of the identity at the weak bundle

`Work.BoseBoxFock.SlotFacts.id` proves `SlotFacts e Φc id (fun _ X => X)` for modes `e l` that are
`Continuous` with `HasCompactSupport` and a state `Φc` that is continuous with compact support.
Those regularity hypotheses are **unsatisfiable** at the honest modes of the box ↔ model bridge
(`FINDING_continuous_hypotheses_UNSATISFIABLE.md`: the condensate mode is a.e. the box indicator,
which has no continuous representative), so the bridge runs the slot calculus on the weak bundle of
`Submission/Work/MB/`:

* `hmeas : ∀ l, Measurable (e l)`, `hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C`,
  `hsupp : ∀ l, support (e l) ⊆ boxL ℓ`;
* `hΦm : Measurable Φc`, `hΦb : ∃ C, ∀ x, ‖Φc x‖ ≤ C`, `hΦsupp : support Φc ⊆ boxPow n ℓ`.

The three fields of `SlotFacts e Φc id (fun _ X => X)` are

* `good` — `RowGood.id`, no hypotheses;
* `slice` — `rfl`, no hypotheses;
* `split` — the **mass splitting** `massR Φc = ∑_S massR (slotExact e S Φc)`, i.e. the sector
  resolution of the identity `∑_S slotExact e S Φc = Φc` (`slotExact_sum_eq`) combined with the
  weak orthogonality of the sectors (`Work.MB.slotExact_orth_ae`).

The only ingredient that the strong chain supplies by *continuity + compact support* and that is
replaced here is integrability of `star Φc · slotExact e S Φc`: on the weak bundle both factors are
bounded and the second is supported in the box `boxPow n ℓ` of finite measure, so
`Work.MB.integrable_star_mul_of_support_boxPow` applies.  This is the same replacement as in
`Work.MB.slotFacts_dec_fibre_ae` and `Work.MB.AVgen_slotFacts_ae`.

Everything here is `sorry`-free.
-/

noncomputable section

namespace Work.MB

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The mass splitting of the sectors at the weak bundle.**  The sector resolution of the
identity `∑_S slotExact e S Φ = Φ` (`Work.BoseBoxFock.slotExact_sum_eq`, no hypotheses) and the weak
orthogonality of the sectors (`Work.MB.slotExact_orth_ae`) give

    (∫ star Φ · Φ).re = ∑ S, (∫ star (slotExact e S Φ) · slotExact e S Φ).re ,

the weak twin of the corresponding step of `Work.BoseBoxFock.massR_eq_sum_slotExact`.  The modes are
only measurable, everywhere bounded and supported in the corpus box `boxL ℓ`, and the state is only
measurable, everywhere bounded and supported in the `n`-particle box `boxPow n ℓ`. -/
theorem massR_eq_sum_slotExact_ae {m n : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    {Φc : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ} (hΦm : Measurable Φc)
    (hΦb : ∃ C, ∀ x, ‖Φc x‖ ≤ C) (hΦsupp : Function.support Φc ⊆ boxPow n ℓ) :
    (∫ x : Fin n → EuclideanSpace ℝ (Fin 3), star (Φc x) * Φc x).re
      = ∑ S : Finset (Fin n),
          (∫ x : Fin n → EuclideanSpace ℝ (Fin 3),
            star (Work.BoseBoxFock.slotExact e S Φc x)
              * Work.BoseBoxFock.slotExact e S Φc x).re := by
  classical
  -- the sectors are good states, supported in the box
  have hsec : ∀ S : Finset (Fin n),
      Measurable (Work.BoseBoxFock.slotExact e S Φc) ∧
      (∃ C, ∀ x, ‖Work.BoseBoxFock.slotExact e S Φc x‖ ≤ C) ∧
      Function.support (Work.BoseBoxFock.slotExact e S Φc) ⊆ boxPow n ℓ := by
    intro S
    obtain ⟨hm, hb, hs⟩ := slotExact_mb_weak hmeas hbdE hsupp S hΦm hΦb
    obtain ⟨C, -, hC⟩ := hb
    exact ⟨hm, ⟨C, hC⟩, hs hΦsupp⟩
  -- the pairing of the state with each sector is integrable
  have hintΦ : ∀ S : Finset (Fin n),
      Integrable (fun x : Fin n → EuclideanSpace ℝ (Fin 3) =>
        star (Φc x) * Work.BoseBoxFock.slotExact e S Φc x) := fun S =>
    integrable_star_mul_of_support_boxPow hΦm hΦb hΦsupp
      (hsec S).1 (hsec S).2.1 (hsec S).2.2
  -- the sectors are orthogonal, in particular each sector pairs the state only with itself
  have horthC : ∀ S : Finset (Fin n),
      (∫ x : Fin n → EuclideanSpace ℝ (Fin 3),
          star (Φc x) * Work.BoseBoxFock.slotExact e S Φc x)
        = (∫ x : Fin n → EuclideanSpace ℝ (Fin 3),
            star (Work.BoseBoxFock.slotExact e S Φc x)
              * Work.BoseBoxFock.slotExact e S Φc x) := by
    intro S
    have h := slotExact_orth_ae hmeas hbdE hsupp horth S S Φc Φc
      hΦm hΦb hΦsupp hΦm hΦb hΦsupp
    rw [if_pos rfl] at h
    exact h.symm
  -- the pointwise resolution of the identity
  have hpt : (fun x : Fin n → EuclideanSpace ℝ (Fin 3) => star (Φc x) * Φc x)
      = fun x : Fin n → EuclideanSpace ℝ (Fin 3) =>
          ∑ S : Finset (Fin n), star (Φc x) * Work.BoseBoxFock.slotExact e S Φc x := by
    funext x
    have hx : (∑ S : Finset (Fin n), Work.BoseBoxFock.slotExact e S Φc x) = Φc x := by
      simpa only [Finset.sum_apply] using congrFun (Work.BoseBoxFock.slotExact_sum_eq e Φc) x
    rw [← Finset.mul_sum, hx]
  rw [hpt, MeasureTheory.integral_finsetSum _ (fun S _ => hintΦ S),
    Finset.sum_congr rfl (fun S _ => horthC S)]
  exact Complex.re_sum _ _

theorem slotFacts_id_ae {m n : ℕ} {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    {Φc : Work.BoseDict.Xn n → ℂ} (hΦm : Measurable Φc) (hΦb : ∃ C, ∀ x, ‖Φc x‖ ≤ C)
    (hΦsupp : Function.support Φc ⊆ Work.MB.boxPow n ℓ) :
    Work.BoseBoxFock.SlotFacts e Φc (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
      (fun _ X => X) := by
  refine ⟨Work.BoseBoxFock.RowGood.id, (fun S u y => rfl), ?_⟩
  show (∫ x : Fin n → EuclideanSpace ℝ (Fin 3), star (Φc x) * Φc x).re
      = ∑ S : Finset (Fin n),
          (∫ x : Fin n → EuclideanSpace ℝ (Fin 3),
            star (Work.BoseBoxFock.slotExact e S Φc x)
              * Work.BoseBoxFock.slotExact e S Φc x).re
  exact massR_eq_sum_slotExact_ae hmeas hbdE hsupp horth hΦm hΦb hΦsupp

end Work.MB
