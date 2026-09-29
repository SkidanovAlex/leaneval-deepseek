import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17.logPw_setup
import Submission.Work.C17.lc_core
import Submission.Work.C17I.pw_continuation

namespace Work.C17

theorem relation_to_LC (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hlt : m < n)
    (hgap : 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n)
    (ra rb rab r0 : ℤ) (P : Fin 17 → Polynomial ℚ)
    (hrel : ∑ i : Fin 17, (P i : PowerSeries ℚ) * Submission.CDTPlan.seventeen m n ra rb rab r0 i = 0)
    (y1 : ℂ → ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : 2 * δ ≤ xsOf m n) (hδ2 : 2 * δ ≤ 1 - xsOf m n)
    (κ : ℂ) (hκ : κ ≠ 0)
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball ((xsOf m n : ℂ)) δ))
    (hy1ne : y1 ((xsOf m n : ℂ)) ≠ 0)
    (hode : ∀ z ∈ Metric.ball ((xsOf m n : ℂ)) δ,
      (P2x (aOf m) (aOf n)).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv y1) z
        + (P1x (aOf m) (aOf n)).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z
        + (P0x (aOf m) (aOf n)).eval₂ (algebraMap ℚ ℂ) z * y1 z = 0)
    (hloc : ∃ hh : ℂ → ℂ,
      DifferentiableOn ℂ hh (Metric.ball ((xsOf m n : ℂ)) δ) ∧
      ∀ z ∈ Metric.ball ((xsOf m n : ℂ)) δ ∩ Metric.ball (0 : ℂ) (xsOf m n),
        Pfun (aOf m) (aOf n) ra rb rab r0 z
          = κ * y1 z * Complex.log (((xsOf m n : ℝ) : ℂ) - z) + hh z) :
    ∃ J : Fin 6 → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (J i) (Metric.ball ((xsOf m n : ℂ)) δ)) ∧
      (∀ i, J i ((xsOf m n : ℂ)) = 0) ∧
      (∀ i, ∀ z ∈ Metric.ball ((xsOf m n : ℂ)) δ,
        HasDerivAt (J i)
          ((((yQ ^ ((i : ℤ) - 4)) * dyQ).num.eval₂ (algebraMap ℚ ℂ) z)
            / (((yQ ^ ((i : ℤ) - 4)) * dyQ).denom.eval₂ (algebraMap ℚ ℂ) z) * y1 z) z) ∧
      ∀ z ∈ Metric.ball ((xsOf m n : ℂ)) δ,
        (∑ k : Fin 4, pAtY (P ⟨5 + (k : ℕ), by omega⟩) z * DyIter (k : ℕ) y1 z)
          + (∑ i : Fin 6, pAtY (P ⟨11 + (i : ℕ), by omega⟩) z * J ⟨5 - (i : ℕ), by omega⟩ z) = 0  := by
  obtain ⟨S, hSconv, hSo, hS1, hS2, hS0, hSsub, Ψ, hΨd, hΨv⟩ :=
    Work.C17I.pw_continuation m n hm hn hlt hgap ra rb rab r0
  exact Work.C17I.relation_to_LC_core m n hm hn hlt hgap ra rb rab r0 P hrel
    hSconv hSo hS1 hS2 hS0 hSsub hΨd hΨv y1 hδ hδ1 hδ2 κ hκ hy1d hy1ne hode hloc


end Work.C17
