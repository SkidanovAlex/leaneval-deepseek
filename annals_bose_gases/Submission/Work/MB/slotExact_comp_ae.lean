import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.MB.slotSectorWeak
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MB

/-- **The composition law of the `S`-sectors, at the weak (measurable, everywhere bounded,
box-supported) mode hypotheses.**

This is the weak twin of `Work.BoseBoxFock.slotExact_comp`: the strong proof needs
`Continuous`/`HasCompactSupport` modes, hypotheses that the honest modes of the box ↔ model
bridge can never satisfy (`FINDING_continuous_hypotheses_UNSATISFIABLE.md`).  Everything here is
*pointwise*: with an everywhere bounded measurable state every Bochner integral occurring in
`slotProj` is honest.

The proof is the mirror of the strong one, with the weak sector algebra of
`Submission/Work/MB/slotSectorWeak.lean` in place of the strong one:

* `S = S'`: enter the resolution of the identity `∑_U A_U = 1`
  (`Work.BoseBoxFock.slotExact_sum_eq`, purely combinatorial) into `A_S Φ` with the weak
  linearity `Work.MB.sx_lin_exact_weak`; the cross terms vanish by
  `Work.MB.sx_zero_ne_weak`, leaving `A_S(A_S Φ) = A_S Φ`;
* `S ≠ S'`: `Work.MB.sx_zero_ne_weak` directly. -/
theorem slotExact_comp_ae {m n : ℕ} {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (S S' : Finset (Fin n)) (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    Work.BoseBoxFock.slotExact e S (Work.BoseBoxFock.slotExact e S' Φ)
      = if S = S' then Work.BoseBoxFock.slotExact e S Φ else 0 := by
  classical
  by_cases h : S = S'
  · -- `S = S'`: enter the resolution of the identity `∑_U A_U = 1` into `A_S`; the cross terms
    -- vanish by `sx_zero_ne_weak`, leaving `A_S = A_S A_S`.
    rw [if_pos h]
    subst h
    have hstep : Work.BoseBoxFock.slotExact e S Φ
        = Work.BoseBoxFock.slotExact e S (Work.BoseBoxFock.slotExact e S Φ) := by
      have hF : (fun x : Fin n → EuclideanSpace ℝ (Fin 3) =>
            ∑ U ∈ Finset.univ, (1 : ℂ) * Work.BoseBoxFock.slotExact e U Φ x) = Φ := by
        funext x
        rw [← congrFun (Work.BoseBoxFock.slotExact_sum_eq e Φ) x]
        simp only [Finset.sum_apply, one_mul]
      conv_lhs => rw [← hF]
      rw [sx_lin_exact_weak (Ψ := fun U => Work.BoseBoxFock.slotExact e U Φ)
        hmeas hbdE hsupp S Finset.univ (fun _ => (1 : ℂ))
        (fun U => (sx_exact_mb_weak hmeas hbdE hsupp U hΦm hΦb).1)
        (fun U => (sx_exact_mb_weak hmeas hbdE hsupp U hΦm hΦb).2)]
      funext x
      rw [Finset.sum_eq_single S]
      · simp
      · intro U _ hU
        rw [sx_zero_ne_weak hmeas hbdE hsupp horth S U hΦm hΦb (Ne.symm hU)]
        simp
      · intro hh
        exact absurd (Finset.mem_univ S) hh
    exact hstep.symm
  · rw [if_neg h]
    exact sx_zero_ne_weak hmeas hbdE hsupp horth S S' hΦm hΦb h

end Work.MB
