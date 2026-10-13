import Mathlib
import Submission.Work.WilE2.exists_dist_ne_of_hasDerivAt_ne_zero
import Submission.Work.WilE2.finite_of_isCompact_isolated

namespace Work.WilE2

/-- A continuous real function `φ` whose every zero is a *simple* zero (i.e. at each zero the
derivative exists and is nonzero) has only finitely many zeros in any bounded interval `[a, b]`.

Proof sketch: the zero set `Z ∩ [a,b]` is closed and bounded, hence compact. At every zero the
nonzero derivative makes the value `0` an isolated value near that zero, so each point of the zero
set is relatively isolated. A compact set all of whose points are relatively isolated is finite. -/
theorem finite_zeros_of_simple {φ : ℝ → ℝ} (hcont : Continuous φ)
    (hsimple : ∀ u, φ u = 0 → ∃ c : ℝ, c ≠ 0 ∧ HasDerivAt φ c u) (a b : ℝ) :
    Set.Finite {t : ℝ | a ≤ t ∧ t ≤ b ∧ φ t = 0} := by
  -- The zero set inside `[a, b]` is compact: it is the intersection of the compact interval
  -- `[a, b]` with the closed set `φ ⁻¹' {0}`.
  have hcomp : IsCompact {t : ℝ | a ≤ t ∧ t ≤ b ∧ φ t = 0} := by
    have hEq : {t : ℝ | a ≤ t ∧ t ≤ b ∧ φ t = 0} = Set.Icc a b ∩ φ ⁻¹' {0} := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage,
        Set.mem_singleton_iff]
      tauto
    rw [hEq]
    exact (isCompact_Icc (a := a) (b := b)).of_isClosed_subset
      (isClosed_Icc.inter (isClosed_singleton.preimage hcont)) (fun t ht => ht.1)
  -- Apply the general compact/isolated-point lemma.
  apply finite_of_isCompact_isolated hcomp
  intro x hx
  -- `x` is a zero of `φ`, so its derivative there exists and is nonzero.
  obtain ⟨c, hc, hd⟩ := hsimple x hx.2.2
  -- Nonzero derivative at a zero of `φ` isolates the value `0` near `x`.
  obtain ⟨ε, hε, hε'⟩ := exists_dist_ne_of_hasDerivAt_ne_zero hd hc
  exact ⟨ε, hε, fun y hy hyS => by
    by_contra hne
    exact (hε' y hy hne) (hyS.2.2.trans hx.2.2.symm)⟩

end Work.WilE2
