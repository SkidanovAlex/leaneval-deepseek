import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.AbsData
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.uniformBoundAt_of_goodSet
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.exists_exhaustion_of_simplyConnectedSpace
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.exists_biholomorphicOn_of_isSimplyConnected_open

/-!
# The ABS input: from the exhaustion and the piece lemma to a univalent exhaustion

This module assembles the two classical inputs of the ABS proof of uniformization
(Anghel–Bruin–Stan, *Uniformization of Riemann surfaces revisited*, arXiv:2008.12189) into the
data consumed by the extraction step `Work.SimplyConnected.Parabolic.exists_injective_holomorphic_of_univalent_family`:

* the exhaustion `Ω n` of `X` by compact pieces with connected frontier (ABS step 12,
  `Work.SimplyConnected.ABS.exists_exhaustion_of_simplyConnectedSpace`);
* the piece lemma `Ω n ≅ ball (0, r n)`, normalized ([ABS step 10],
  `Work.SimplyConnected.ABS.exists_biholomorphicOn_of_isSimplyConnected_open`);
* the normal-family bound for normalised univalent maps
  (`Work.SimplyConnected.ABS.uniformBoundAt`, ABS Appendix AC);

the conclusion is `Work.SC.HasUnivalentExhaustion` — exactly the hypothesis of the extraction.

The piece data are taken with an explicit `¬ CompactSpace X` hypothesis (as in the piece lemma):
on a non-compact surface the relatively compact pieces are automatically proper subsets, whereas
without non-compactness the piece `Ω = X ∖ {p}` of a compact surface could be biholomorphic to `ℂ`
and hence admit no biholomorphism onto a disc.  This is the only point where non-compactness of the
ambient surface is used.
-/

namespace Work.SimplyConnected.ABS

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set Classical

/-- A bound for the finitely many indices `n < m` of a sequence of reals. -/
private theorem exists_bound_of_lt (r : ℕ → ℝ) (m : ℕ) : ∃ R : ℝ, ∀ n, n < m → r n ≤ R := by
  induction m with
  | zero => exact ⟨0, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  | succ k ih =>
    obtain ⟨R, hR⟩ := ih
    exact ⟨max R (r k), fun n hn => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | h
      · exact le_trans (hR n h) (le_max_left _ _)
      · subst h; exact le_max_right _ _⟩

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## The glue -/

/-- **ABS steps 12 + 10 give a univalent exhaustion.**  Given an exhaustion of the non-compact
simply connected surface `X` by open connected simply connected sets with compact closure, connected
frontier and nested closures, and, for every such piece, a normalised biholomorphism onto a disc,
the family of those biholomorphisms is a univalent exhaustion: holomorphic and injective on the
pieces, normalised at `x₀`, and uniformly bounded on compact sets by the normal-family bound. -/
theorem hasUnivalentExhaustion_of_exhaustion_and_pieceData [SimplyConnectedSpace X]
    (hX : ¬ CompactSpace X) {x₀ : X}
    (hExh : ∃ Ω : ℕ → Set X, (∀ n, IsOpen (Ω n)) ∧ (∀ n, IsConnected (Ω n)) ∧
      (∀ n, IsSimplyConnected (Ω n)) ∧ (∀ n, IsCompact (closure (Ω n))) ∧
      (∀ n, IsConnected (frontier (Ω n))) ∧ (∀ n, closure (Ω n) ⊆ Ω (n + 1)) ∧
      x₀ ∈ Ω 0 ∧ (⋃ n, Ω n) = Set.univ)
    (hPiece : ∀ {Ω : Set X}, IsOpen Ω → IsConnected Ω → IsSimplyConnected Ω → Ω ≠ Set.univ →
      IsCompact (closure Ω) → IsConnected (frontier Ω) → ∀ x₀ ∈ Ω, ∃ (r : ℝ) (χ : X → ℂ),
        0 < r ∧ (∀ x ∈ Ω, Submission.HolomorphicOnXAt χ x) ∧ Set.InjOn χ Ω ∧ χ x₀ = 0 ∧
        χ '' Ω = Metric.ball (0 : ℂ) r ∧
        deriv (χ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 1 ∧ (∀ x ∉ Ω, χ x = 0)) :
    Work.SC.HasUnivalentExhaustion (X := X) x₀ := by
  obtain ⟨Ω, hΩo, hΩc, hΩs, hcomp, hbc, hmono, hx₀, hcov⟩ := hExh
  -- a relatively compact piece of a non-compact surface is a proper subset
  have hne : ∀ n, Ω n ≠ Set.univ := by
    intro n h
    have hcl : closure (Ω n) = Set.univ := by rw [h]; exact closure_univ
    exact hX (isCompact_univ_iff.mp (hcl ▸ hcomp n))
  have hxΩ : ∀ n, x₀ ∈ Ω n := by
    intro n
    induction n with
    | zero => exact hx₀
    | succ k ih => exact hmono k (subset_closure ih)
  have hmono' : ∀ n, Ω n ⊆ Ω (n + 1) := fun n => (subset_closure).trans (hmono n)
  have hmonoM : ∀ n m : ℕ, n ≤ m → Ω n ⊆ Ω m := fun n m hn =>
    monotone_nat_of_le_succ hmono' hn
  -- the normalised biholomorphisms of the pieces
  choose r χ hr hχhol hχinj hχ0 hχimg hχder hχzero using fun n =>
    hPiece (hΩo n) (hΩc n) (hΩs n) (hne n) (hcomp n) (hbc n) x₀ (hxΩ n)
  -- the normal-family bound
  have hbnd : ∀ K : Set X, IsCompact K → ∃ B : ℝ, ∀ n, ∀ x ∈ K, ‖χ n x‖ ≤ B := by
    intro K hK
    have hsub : K ⊆ ⋃ n, Ω n := by rw [hcov]; exact subset_univ K
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover Ω hΩo hsub
    obtain ⟨m, hm⟩ : ∃ m, K ⊆ Ω m := by
      refine ⟨t.sup id, fun x hx => ?_⟩
      have hx' : x ∈ ⋃ n ∈ t, Ω n := ht hx
      obtain ⟨n, hnt, hxn⟩ : ∃ n, n ∈ t ∧ x ∈ Ω n := by
        simpa only [Set.mem_iUnion, exists_prop] using hx'
      exact hmonoM n (t.sup id) (Finset.le_sup (f := id) hnt) hxn
    -- the bound for all large indices, from the normal-family bound
    obtain ⟨B₁, hB₁⟩ := uniformBoundAt (X := X) x₀ (hΩo m) (hΩc m) (hxΩ m) K hK hm
    -- the finitely many remaining indices, from the disc radii
    obtain ⟨R, hR⟩ := exists_bound_of_lt r m
    refine ⟨max B₁ (max R 0), fun n x hxK => ?_⟩
    by_cases hn : m ≤ n
    · have hxΩn : x ∈ Ω n := hmonoM m n hn (hm hxK)
      have := hB₁ (Ω := Ω n) (hΩo n) (hΩc n) (hmonoM m n hn)
        (ψ := χ n) (hχhol n) (hχinj n) (hχ0 n) (hχder n) x hxK
      exact le_trans this (le_max_left _ _)
    · have hnlt : n < m := lt_of_not_ge hn
      by_cases hxn : x ∈ Ω n
      · have hmem : χ n x ∈ Metric.ball (0 : ℂ) (r n) := by
          rw [← hχimg n]; exact ⟨x, hxn, rfl⟩
        have hlt : ‖χ n x‖ < r n := by
          rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hmem
        exact le_trans (le_of_lt hlt)
          (le_trans (hR n hnlt) (le_trans (le_max_left _ _) (le_max_right _ _)))
      · rw [hχzero n x hxn, norm_zero]
        exact le_trans (le_max_right R 0) (le_max_right B₁ (max R 0))
  exact ⟨Ω, χ, hΩo, hxΩ, hmono', hcov, hχhol, hχinj, hχ0, hχder, hbnd⟩

/-! ## The ABS input for a space -/

end

end Work.SimplyConnected.ABS
