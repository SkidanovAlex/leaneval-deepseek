import Mathlib
import Submission.Work.Smooth.JordanSeparation.continuum_of_compl_not_preconnected

/-!
# The complement of a compact totally disconnected plane set is connected

We prove that a compact subset `K ⊆ ℂ` whose every preconnected subset is a subsingleton
(i.e. a compact *totally disconnected* set) has preconnected complement.

This is the contrapositive of the classical plane-topology fact (Borsuk / Janiszewski) that a
compact subset of the plane separating it contains a continuum: if `Kᶜ` were disconnected, then
`K` would contain a non-degenerate continuum, contradicting total disconnectedness.
-/

open Set Metric
open scoped Topology

namespace Work.Smooth.JordanSeparation

noncomputable section

theorem isPreconnected_compl_of_totallyDisconnected {K : Set ℂ} (hK : IsCompact K)
    (h : ∀ E ⊆ K, IsPreconnected E → E.Subsingleton) : IsPreconnected Kᶜ := by
  by_contra hcon
  obtain ⟨C, hCK, hCpre, hCnt⟩ := continuum_of_compl_not_preconnected hK hcon
  exact hCnt.not_subsingleton (h C hCK hCpre)

end

end Work.Smooth.JordanSeparation
