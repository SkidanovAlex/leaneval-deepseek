import Mathlib
import Submission.CorPerm5D
import Submission.Commons.LinearAlgebra.Net.spread_permutations

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Measure Filter unitInterval

namespace Submission.NetUniform

attribute [local instance] Classical.propDecidable

open Commons.LinearAlgebra.Net (sqNorm compressible)

/-- **Uniform special permutations**: a single family of permutations (and a
single constant `CPerm`) works for every threshold scale `T` simultaneously.
This is what the annulus decomposition of Theorem A needs (the net must be
built once and reused for all annuli). -/
theorem cor_permutations_uniform {δ ν : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2)
    (hν0 : 0 < ν) (hν1 : ν ≤ 1) :
    ∃ CPerm : ℝ, 1 ≤ CPerm ∧
      ∀ (n : ℕ), 2 ≤ n → (1 : ℝ) ≤ δ * (n : ℝ) →
        ∃ PiSet : Finset (Equiv.Perm (Fin n)),
          (PiSet.card : ℝ) ≤ CPerm ^ n ∧
          ∀ {T : ℝ}, 0 < T → T ≤ ν / 2 →
            ∀ {x : Fin n → ℝ}, sqNorm x = 1 → ¬ compressible δ ν x →
              ∀ {th : ℝ}, 0 < th → T / 2 ≤ th → th ≤ T →
                ∀ (spv : Fin n → ℤ),
                  (∀ i : Fin n, |(Real.sqrt (n : ℝ) / th) * x i - (spv i : ℝ)| ≤ 1) →
                  ∃ pi ∈ PiSet,
                    ∀ i : Fin n, spv (pi i) ∈ Submission.Section5D.Acoord n δ ν T i := by
  rcases Commons.LinearAlgebra.Net.spread_permutations with ⟨CPerm, hC1, hfam⟩
  refine ⟨CPerm, hC1, ?_⟩
  intro n hn2 hδn1
  rcases hfam n hn2 with ⟨PiSet, hCard, hProp⟩
  refine ⟨PiSet, hCard, ?_⟩
  intro T hT0 hTν x hx hinc th hth0 hthhalf hthT spv hspv
  obtain ⟨π, hπ, hlow, hup⟩ := hProp hδ0 hδ12 hν0 hν1 x hx hinc hth0 spv hspv
  refine ⟨π, hπ, ?_⟩
  exact @Submission.Section5D.reordered_spv_mem_Acoord δ ν T hδ0 hδ12 hν0 hν1 n
    (by omega) hδn1 x hx th T hth0 hT0 hTν hthhalf hthT spv hspv π hlow hup

end Submission.NetUniform
