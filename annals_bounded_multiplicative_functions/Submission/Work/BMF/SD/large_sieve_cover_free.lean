import Mathlib
import Submission.Work.BMF.SD.large_sieve_poly_free
import Submission.Work.BMF.polyrel_basic
import Submission.Work.BMF.SD.cover_of_max_unrelated
import Submission.Work.BMF.SD.exists_pair_of_subset

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The covering form of the polynomial large sieve, clash-free

`Work.BMF.SD.large_sieve_cover` (`SD/large_sieve_cover.lean`) proves the covering corollary of
`Work.BMF.large_sieve_poly`.  It cannot be used in files that also import
`Submission.Work.BMF.SD.tk_short`, because its import closure contains `SD/weyl_inverse`
(the `Work.BMF.SD.eC_mul_nat` clash).  This file is the same proof, on top of the clash-free port
`Submission.Work.BMF.SD.large_sieve_poly_free` (`Work.BMF.SD.large_sieve_poly_free`), so that it
*can* be imported together with `SD/tk_short` -- which is what the scaling-down development
(`Work.BMF.SD.good_prime_incidence`) needs in order to use the phase-class structure.  Only the
name of the ported large sieve changed; the proof is verbatim `large_sieve_cover`'s.
-/

namespace Work.BMF.SD

open Classical Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions
open Work.BMF

/-- **Covering form of the polynomial large sieve.**

Every family of intervals `[xᵢ, xᵢ+Lᵢ]` inside a window `[x₀-C₀H, x₀+C₀H]` of length `≍ H`, whose
degree-`≤ k` phase `Pᵢ` correlates with the `1`-bounded `f` at level `η'`, can be covered by
`K = K(k,η',C₀) = O(1)` of its members: there is a subfamily `A` of size `≤ K` such that every `i`
is `PolyRel k C 1`-related (with a constant `C = C(k,η',C₀) ≥ C₀`) to some `j ∈ A`.

The proof is the standard maximal-independent-set argument on top of `large_sieve_poly`: the
relation `~` given by `PolyRel k C 1` is reflexive (`ε = γ = 0`), and `PolyRel` is symmetric up
to the explicit constant blow-up `symmConst`, so a maximal set `A` of indices that are pairwise
`~`-unrelated in *both* directions has size `< K` (otherwise the large sieve, applied to the
injective enumeration of `A`, would produce a related pair inside it) and every index is `~`-related
(with constant `symmConst k C₁`) to some member of `A`: this is `cover_of_max_unrelated`, whose
hypotheses `hmono`, `hsymm`, `hrefl` are `PolyRel.mono`, `PolyRel.symm` and reflexivity. -/
theorem large_sieve_cover_free (k : ℕ) (η' C₀ : ℝ) (hη' : 0 < η') (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, C₀ ≤ C ∧ ∃ K : ℕ,
      ∀ (N : ℕ) (f : ℕ → ℂ) (x₀ H : ℝ) (xs Ls : Fin N → ℝ) (Ps : Fin N → ℝ[X]),
        (∀ n, ‖f n‖ ≤ 1) → 1 ≤ H → (∀ i, 1 ≤ xs i) →
        (∀ i, Ls i ≤ C₀ * H ∧ H ≤ C₀ * Ls i ∧ |xs i - x₀| ≤ C₀ * H) →
        (∀ i, Ps i ∈ Polynomial.degreeLE ℝ (k : WithBot ℕ)) →
        (∀ i, η' * Ls i ≤ ‖corr f (Ps i) (xs i) (Ls i)‖) →
        ∃ A : Finset (Fin N), A.card ≤ K ∧
          ∀ i : Fin N, ∃ j ∈ A, PolyRel k C 1 (xs i) (Ls i) (Ps i) (xs j) (Ls j) (Ps j) := by
  obtain ⟨C₁, hC₁ge, K, hls⟩ := large_sieve_poly_free k η' C₀ hη' hC₀
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hC₁pos : 0 < C₁ := lt_of_lt_of_le hC₀pos hC₁ge
  have hC₁one : 1 ≤ C₁ := le_trans hC₀ hC₁ge
  have hsymm_ge : C₁ ≤ symmConst k C₁ := symmConst_ge_self hC₁pos
  refine ⟨symmConst k C₁, le_trans hC₁ge hsymm_ge, K, ?_⟩
  intro N f x₀ H xs Ls Ps hf hH hxs hgeo hdeg hcorr
  have hLpos : ∀ i, 0 < Ls i := by
    intro i
    have h := (hgeo i).2.1
    nlinarith [hH, h, hC₀pos]
  have hLnn : ∀ i, 0 ≤ Ls i := fun i => (hLpos i).le
  have hCone : 1 ≤ symmConst k C₁ := le_trans hC₁one hsymm_ge
  -- the relation of the large sieve, and its symmetric hull
  have hpair : ∀ A : Finset (Fin N), K ≤ A.card →
      ∃ i ∈ A, ∃ j ∈ A, i ≠ j ∧
        PolyRel k C₁ 1 (xs i) (Ls i) (Ps i) (xs j) (Ls j) (Ps j) := by
    intro A hA
    refine exists_pair_of_subset
      (fun i j => PolyRel k C₁ 1 (xs i) (Ls i) (Ps i) (xs j) (Ls j) (Ps j)) K ?_ A hA
    intro M e _ hKM
    exact hls M f x₀ H (fun t => xs (e t)) (fun t => Ls (e t)) (fun t => Ps (e t))
      hf hH (fun t => hxs (e t)) (fun t => hgeo (e t)) (fun t => hdeg (e t))
      (fun t => hcorr (e t)) hKM
  obtain ⟨A, hAcard, hAcov⟩ := cover_of_max_unrelated
    (fun i j => PolyRel k C₁ 1 (xs i) (Ls i) (Ps i) (xs j) (Ls j) (Ps j))
    (fun i j => PolyRel k (symmConst k C₁) 1 (xs i) (Ls i) (Ps i) (xs j) (Ls j) (Ps j))
    K
    (fun i j hij => PolyRel.mono hij hsymm_ge (hLnn i) (hLnn j))
    (fun i j hij => PolyRel.symm hij hC₁pos (hLpos j) (hLpos i))
    (fun i => by
      refine ⟨?_, ?_, ?_, 0, 0, Submodule.zero_mem _, Submodule.zero_mem _, ?_, ?_,
        IntegralOn.zero 1⟩
      · simpa using mul_le_mul_of_nonneg_right hCone (hLnn i)
      · simpa using mul_le_mul_of_nonneg_right hCone (hLnn i)
      · rw [sub_self, abs_zero]
        exact mul_nonneg (by linarith) (hLnn i)
      · show Ps i = 0 + Ps i + 0
        ring
      · intro t ht
        rw [Polynomial.eval_zero, abs_zero]
        linarith)
    hpair
  exact ⟨A, hAcard, hAcov⟩

end Work.BMF.SD
