import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.exists_enum_critical

/-!
# The critical set of a Morse function on a compact surface is finite

Target of this file: `Work.Drive.N2.finite_critical_set`.

The two ingredients live in the sibling module `Submission.Work.Drive.N2.exists_enum_critical`
(proved there):

* `Work.Drive.N2.isClosed_isCriticalSet` -- the set of critical points of a smooth function is
  closed (in a chart the condition "critical" becomes the vanishing of `fderiv ℝ g_p (e_p ·)`,
  which is continuous);
* `Work.Drive.N2.isCritical_isolated` -- a *nondegenerate* critical point is isolated in the
  critical set (the Hessian is injective, hence an antilipschitz-strict-derivative argument makes
  `y ↦ fderiv ℝ g_x y` injective near the chart point).

A closed subset of a compact space all of whose points are isolated is finite, which is
`Work.Embedding.finite_of_isClosed_forall_isolated`.  Combining these gives the statement, for a
Morse function with distinct critical values (the distinctness hypothesis is not needed for
finiteness; only smoothness and nondegeneracy of all critical points are used).

Note that the hypothesis `hmorse : MorseLemma2` is *not* needed for this lemma: the Morse normal
form is used elsewhere (the classification of the critical points), while finiteness only needs
nondegeneracy of the Hessian at each critical point.
-/

namespace Work.Drive.N2

theorem finite_critical_set {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : Work.Drive.Morse.IsMorseDistinct f) (hmorse : Work.Drive.Morse.MorseLemma2) :
    {x : M | Work.Drive.Morse.IsCritical f x}.Finite := by
  obtain ⟨hsmooth, hnd, _⟩ := hf
  exact Work.Embedding.finite_of_isClosed_forall_isolated
    (isClosed_isCriticalSet f hsmooth)
    (fun p hp => isCritical_isolated f hsmooth p hp (hnd p hp))

end Work.Drive.N2
