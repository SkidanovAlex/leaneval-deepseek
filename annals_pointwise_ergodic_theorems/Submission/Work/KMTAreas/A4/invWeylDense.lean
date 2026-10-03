import Mathlib
import Submission.Work.KMTAreas.A4.invWeylDefs
import Submission.Work.KMTAreas.A4.denseMultiples_engine

namespace Work.KMTAreas.A4

/-- **Green--Tao Lemma 3.1(i)** in the form `DenseStatement`: a set `T` of lattice points in
`[-N,N]` of density at least `δ₂`, all of whose multiples `β n` are within `δ₁ ≤ δ₂/4` of an
integer, forces `β` to be within `2^8/(δ₂^2 N)` of a rational with denominator at most `8/δ₂`.

This is the immediate corollary of the engine `denseMultiples_engine` (which produces the
accuracy `2^8/(δ₂^2 (2N+1))`); the passage from `2N+1` to `N` uses `N ≤ 2N+1`. -/
theorem invWeylDense : ∃ C : ℝ, 0 < C ∧ Work.KMTAreas.A4.DenseStatement C := by
  refine ⟨2 ^ 8, by norm_num, ?_⟩
  unfold DenseStatement
  intro β δ₁ δ₂ N T hN hδ₁ hδ₂ hδ₂le hδ₁le hT hcard hgood
  obtain ⟨q, hq1, hqle, a, ha⟩ :=
    denseMultiples_engine β δ₁ hδ₁ N hN T hT hgood δ₂ hδ₂ (by linarith) hcard
  refine ⟨q, hq1, hqle, a, ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  have hmono : (2 : ℝ) ^ 8 / (δ₂ ^ 2 * (2 * (N : ℝ) + 1))
      ≤ (2 : ℝ) ^ 8 / (δ₂ ^ 2 * (N : ℝ)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [hNpos]
  linarith [ha, hmono]

end Work.KMTAreas.A4
