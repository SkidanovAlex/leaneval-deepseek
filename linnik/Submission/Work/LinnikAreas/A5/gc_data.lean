import Mathlib
import Submission.Work.LinnikAreas.A5.Weights
import Submission.Work.LinnikAreas.A5.Basic
import Submission.Work.LinnikAreas.A5.gc_elementary
import Submission.Work.LinnikAreas.A5.gc_deriv_bound

namespace Work.LinnikAreas.A5

/-
Data for the λ = 0 endpoint test function of HB Lemma 13.3 used in Area 5:
`gc K t = (K-t)/K` for `t ∈ [0,K]`, and `0` elsewhere (in particular `0` for `K ≤ t`).
It is the λ → 0 limit of the normalised family, again cut off at `t = 0` so that it is bounded
on all of ℝ.  Same list of facts as `wc_data`, with second derivative `0` on `(0,K)` and first
derivative `-1/K` there (and convention value `0` at the corners `t = 0`, `t = K`).
-/
theorem gc_data (K R : ℝ) (hK : 0 < K) (hR : 0 ≤ R) :
    Work.LinnikAreas.A5.gc K 0 = 1 ∧
    ContinuousOn (Work.LinnikAreas.A5.gc K) (Set.Ici 0) ∧
    (∀ t : ℝ, K ≤ t → Work.LinnikAreas.A5.gc K t = 0) ∧
    ContDiffOn ℝ 2 (Work.LinnikAreas.A5.gc K) (Set.Ioo 0 K) ∧
    (∀ t ∈ Set.Ioo (0:ℝ) K, ‖iteratedDeriv 2 (Work.LinnikAreas.A5.gc K) t‖ ≤ R ^ 2) ∧
    (∀ t : ℝ, ‖Work.LinnikAreas.A5.gc K t‖ ≤ 1) ∧
    (∀ t ∈ Set.Icc (0:ℝ) K, ‖deriv (Work.LinnikAreas.A5.gc K) t‖ ≤ 1 / K) ∧
    (∀ t : ℝ, 0 ≤ Work.LinnikAreas.A5.gc K t) := by
  obtain ⟨hcont, hcd, hidt, hbnd, hpos, hge⟩ := gc_elementary K hK
  have h0 : Work.LinnikAreas.A5.gc K 0 = 1 := by
    rw [gc_of_mem le_rfl hK.le, sub_zero, div_self (ne_of_gt hK)]
  refine ⟨h0, hcont, hge, hcd, ?_, hbnd, gc_deriv_bound K hK, hpos⟩
  intro t ht
  rw [hidt t ht, norm_zero, sq]
  exact mul_nonneg hR hR

end Work.LinnikAreas.A5
