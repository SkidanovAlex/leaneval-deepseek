import Mathlib
import Submission.Work.RatHurewicz.SerreHurewicz
import Submission.Work.RatHurewicz.range_of_rationalHurewiczStable
import Submission.Work.RatHurewicz.torsion_of_subsingleton_ratHomology
import Submission.Work.Drive.RationalHurewicz
import Submission.Work.Stems.HurewiczNeutral
import Submission.Work.Cohomology.Chains

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The consumer-facing form of the contract

Area **RATHUREWICZ** (`Submission/Work/RatHurewicz/`).  The consumers of the drive's contract (area
THOM for the Thom space of the universal bundle, area STEMS for the stable stems) use it in the
following *vanishing* form: if `X` is `(k-1)`-connected and its **rational** homology vanishes in a
degree `n+1 ≤ 2k-2`, then `π_{n+1}(X)` is a torsion group.

This module derives that from the contract, using the change-of-coefficients input
`H_j(X;ℚ) = 0 ⟹ H_j(X;ℤ)` torsion (`Work.RatHurewicz.torsion_of_subsingleton_ratHomology`, proved
in the sibling file of the same name) to produce the torsion of the Hurewicz image.
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- **The vanishing form of the contract, from the torsion of integral homology.**  Let `X` be
`(k-1)`-connected, `n + 1 ≤ 2k-2`, and suppose that the vanishing of the rational homology in degree
`n+1` forces the integral homology in that degree to be torsion (the hypothesis `htors`).  Then every
element of `π_{n+1}(X,x₀)` has finite order: its Hurewicz image is torsion, and the contract (in the
map form `Work.RatHurewicz.HurewiczModTorsionRange`, equivalent to it by
`rationalHurewiczStable_iff_range`) concludes. -/
theorem pi_torsion_of_ratHomology_vanishing_of_torsion
    (h : Work.Drive.RationalHurewiczStable)
    (htors : ∀ (X : Type) [TopologicalSpace X] (j : ℕ),
      Subsingleton ((Work.Cohomology.singularChains ℚ (TopCat.of X)).homology j) →
        ∀ b : (Work.Cohomology.singularChains ℤ (TopCat.of X)).homology j,
          ∃ N : ℕ, 0 < N ∧ N • b = 0)
    (k : ℕ) (hk : 2 ≤ k) (X : Type) [TopologicalSpace X] (x₀ : X)
    (hconn : ∀ i < k, Subsingleton (HomotopyGroup (Fin i) X x₀))
    (n : ℕ) (hn : n + 1 ≤ 2 * k - 2)
    (hhom : Subsingleton ((Work.Cohomology.singularChains ℚ (TopCat.of X)).homology (n + 1)))
    (a : HomotopyGroup (Fin (n + 1)) X x₀) : ∃ N : ℕ, 0 < N ∧ a ^ N = 1 := by
  refine range_of_rationalHurewiczStable h k hk X x₀ hconn n hn a ?_
  obtain ⟨N, hN, hNb⟩ := htors X (n + 1) hhom
    (Work.Stems.hurewiczMapN (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x₀ a)
  refine ⟨N, hN, ?_⟩
  simpa using hNb

/-- **The vanishing form of the contract.**  Let `X` be `(k-1)`-connected and suppose that its
rational homology vanishes in degree `n + 1 ≤ 2k-2`.  Then every element of `π_{n+1}(X,x₀)` has
finite order.

This is the form in which the contract is consumed (e.g. by the area THOM: the rational homology of
the relevant spaces is known to vanish in the stable range). -/
theorem pi_torsion_of_ratHomology_vanishing
    (h : Work.Drive.RationalHurewiczStable)
    (k : ℕ) (hk : 2 ≤ k) (X : Type) [TopologicalSpace X] (x₀ : X)
    (hconn : ∀ i < k, Subsingleton (HomotopyGroup (Fin i) X x₀))
    (n : ℕ) (hn : n + 1 ≤ 2 * k - 2)
    (hhom : Subsingleton ((Work.Cohomology.singularChains ℚ (TopCat.of X)).homology (n + 1)))
    (a : HomotopyGroup (Fin (n + 1)) X x₀) : ∃ N : ℕ, 0 < N ∧ a ^ N = 1 :=
  pi_torsion_of_ratHomology_vanishing_of_torsion h
    (fun _ _ j hh => torsion_of_subsingleton_ratHomology j hh) k hk X x₀ hconn n hn hhom a

end

end Work.RatHurewicz
