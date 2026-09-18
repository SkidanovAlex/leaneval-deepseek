import Submission.DS.Case1
import Submission.DS.Truncate
import Submission.DS.TruncDiv
import Submission.DS.CatlinDir

open scoped Nat ENNReal NNReal
open Set MeasureTheory
open DuffinSchaefferConjecture

/-!
# Deduction of Theorem 2(b) from Theorem 1 (paper §2, Catlin's divergence theorem)

The paper's §2 proves Theorem 2(b) assuming Theorem 1 (the Duffin-Schaeffer conjecture):

* Case 1 (`ψ(q) ≥ 1/2` infinitely often): `𝒦 ψ = [0,1]`  — see `Case1.lean`.
* Case 2 (finitely many such `q`): replace `ψ` by `min ψ (1/2)` (leaves `𝒦 ψ` and the
  divergence of `∑ ψ*` unchanged — `Truncate.lean` / `TruncDiv.lean`), so WLOG `ψ ≤ 1/2`;
  then form `ξ(q)/q = sup {ψ(n)/n : q ∣ n}`, whose `∑ φ(q) ξ(q)/q` still diverges, apply
  Theorem 1 to `ξ`, and show `𝒜 ξ ∖ ℚ = 𝒦 ψ ∖ ℚ` (`CatlinDiv.lean`).

This file states the resulting dependency theorem.
-/

namespace Submission.DS

/-- **Theorem 2(b) conditional on Theorem 1** (paper §2): if the Duffin-Schaeffer
statement holds for every `ξ : ℕ+ → ℝ≥0`, then the divergence of `∑ ψ*` forces
`𝒦 ψ` to be measurable of full Lebesgue measure. -/
theorem theorem_2_b_of_theorem_1
    (hThm1 : ∀ (χ : ℕ+ → ℝ≥0),
      ¬ Summable (fun q => (χ q * φ q) / q) → MeasurableSet (𝒜 χ) ∧ volume (𝒜 χ) = 1)
    (ψ : ℕ+ → ℝ≥0) (hψ : (∑' q : ℕ+, ψ_star ψ q) = ∞) :
    MeasurableSet (𝒦 ψ) ∧ volume (𝒦 ψ) = 1 := by
  classical
  by_cases hBig : (bigQ ψ).Infinite
  · -- Case 1: ψ(q) ≥ 1/2 infinitely often ⇒ 𝒦 ψ = [0,1]
    exact theorem_2_b_case1 ψ hψ hBig
  · -- Case 2: finitely many such q; truncate at level 1/2
    have hFin : (bigQ ψ).Finite := Set.not_infinite.mp hBig
    let ψ0 : ℕ+ → ℝ≥0 := psiHalf ψ
    have hK : 𝒦 ψ = 𝒦 ψ0 := by
      dsimp [ψ0]
      exact K_eq_K_psiHalf ψ
    have hle0 : ∀ q, ψ0 q ≤ (1 / 2 : ℝ≥0) := by
      intro q
      exact psiHalf_le_half ψ q
    have hdiv0 : (∑' q : ℕ+, ψ_star ψ0 q) = ∞ := by
      simpa [ψ0] using tsum_psiStar_min_half ψ hFin hψ
    rcases catlin_div_case2 hThm1 ψ0 hle0 hdiv0 with ⟨hm0, hv0⟩
    constructor
    · rwa [hK]
    · rwa [hK]

end Submission.DS
