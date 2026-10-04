import Mathlib
import Submission.Work.Diff.EXT.ConnCov.quadForm_uniform_lower_compact

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform two-sided bounds for a compact family of positive definite quadratic forms

Let `K` be a compact subset of `Fin n → ℝ` and let `A z` be a family of `n × n` matrices with
`z ∈ K`, whose entries are continuous on `K` and whose quadratic forms
`ξ ↦ ∑ p, ∑ q, A z p q * ξ p * ξ q` are strictly positive at every nonzero `ξ`.

Then there are constants `c > 0` and `C ≥ 0` such that

* `c * ∑ p, (ξ p) ^ 2 ≤ ∑ p, ∑ q, A z p q * ξ p * ξ q` for every `z ∈ K` and every `ξ`, and
* `|A z p q| ≤ C` for every `z ∈ K` and every `p q`.

The lower bound is a uniform (in `z`) positive-definiteness margin; it is obtained from the
standard compactness argument on `K × {ξ | ∑ ξᵢ² = 1}`, packaged in
`Work.Diff.EXT.ConnCov.quadForm_uniform_lower_compact` (applied to the compact subtype `↥K`,
which converts the `ContinuousOn` hypothesis into the `ContinuousAt` hypothesis of that lemma).
The upper bound is the boundedness of a continuous function on a compact set, applied to the sum
of the absolute values of the entries.
-/

namespace Work.Diff.STE.B3

/-- Entrywise sup-norm bound for a family of matrices with entries continuous on a compact set. -/
theorem exists_abs_entry_bound {n : ℕ} (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (A : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ p q, ContinuousOn (fun z => A z p q) K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ p q, |A z p q| ≤ C := by
  classical
  -- the sum of the absolute values of the entries is continuous on `K`
  have hMcont : ContinuousOn (fun z => ∑ p, ∑ q, |A z p q|) K := by
    refine continuousOn_finsetSum _ (fun p _ => ?_)
    refine continuousOn_finsetSum _ (fun q _ => ?_)
    exact (hAcont p q).abs
  -- hence it is bounded above on `K`
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z ∈ K, (∑ p, ∑ q, |A z p q|) ≤ C := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨0, by simp [hKe]⟩
    · obtain ⟨z₀, _hz₀, hmax⟩ := hK.exists_isMaxOn hKne hMcont
      exact ⟨∑ p, ∑ q, |A z₀ p q|, fun z hz => hmax hz⟩
  -- each entry is dominated by the sum of the absolute values
  have h1 : ∀ (z : Fin n → ℝ) (p q : Fin n), |A z p q| ≤ ∑ p', ∑ q', |A z p' q'| := by
    intro z p q
    have hpq : |A z p q| ≤ ∑ q' : Fin n, |A z p q'| :=
      Finset.single_le_sum (s := Finset.univ) (f := fun q' => |A z p q'|)
        (fun q' _ => abs_nonneg _) (Finset.mem_univ q)
    have hp : (∑ q' : Fin n, |A z p q'|) ≤ ∑ p' : Fin n, ∑ q' : Fin n, |A z p' q'| :=
      Finset.single_le_sum (s := Finset.univ) (f := fun p' => ∑ q' : Fin n, |A z p' q'|)
        (fun p' _ => Finset.sum_nonneg (fun q' _ => abs_nonneg _)) (Finset.mem_univ p)
    exact hpq.trans hp
  exact ⟨max C 0, le_max_right _ _, fun z hz p q =>
    (h1 z p q).trans ((hC z hz).trans (le_max_left _ _))⟩

theorem quadForm_bounds {n : ℕ} (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (A : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ p q, ContinuousOn (fun z => A z p q) K)
    (hpos : ∀ z ∈ K, ∀ ξ : Fin n → ℝ, ξ ≠ 0 →
      0 < ∑ p, ∑ q, A z p q * ξ p * ξ q) :
    ∃ (c C : ℝ), 0 < c ∧ 0 ≤ C ∧
      (∀ z ∈ K, ∀ ξ : Fin n → ℝ,
        c * ∑ p, (ξ p) ^ 2 ≤ ∑ p, ∑ q, A z p q * ξ p * ξ q) ∧
      (∀ z ∈ K, ∀ p q, |A z p q| ≤ C) := by
  classical
  -- the two ways of writing the quadratic form agree, by commutativity of multiplication
  have hswap : ∀ (z : Fin n → ℝ) (ξ : Fin n → ℝ),
      (∑ p, ∑ q, A z p q * ξ p * ξ q) = ∑ i, ∑ j, ξ i * ξ j * A z i j :=
    fun z ξ => Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => by ring))
  -- uniform positive lower bound, by compactness of the unit sphere, in the compact subtype `↥K`
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  obtain ⟨c, hcpos, hcle⟩ := Work.Diff.EXT.ConnCov.quadForm_uniform_lower_compact
    (n := n) (X := ↥K) (A := fun (z : ↥K) i j => A z.1 i j) (C := Set.univ)
    isCompact_univ
    (fun x _ i j => ((hAcont i j).domRestrict.continuousAt :
        ContinuousAt (fun y : ↥K => A y.1 i j) x))
    (fun x _ v hv => by
      have h := hpos x.1 x.2 v hv
      exact lt_of_lt_of_eq h (hswap x.1 v))
  -- entrywise bound
  obtain ⟨C, hCnonneg, hCbound⟩ := exists_abs_entry_bound K hK A hAcont
  refine ⟨c, C, hcpos, hCnonneg, ?_, hCbound⟩
  intro z hz ξ
  have h := hcle ⟨z, hz⟩ (Set.mem_univ _) ξ
  exact le_of_le_of_eq h (hswap z ξ).symm

end Work.Diff.STE.B3
