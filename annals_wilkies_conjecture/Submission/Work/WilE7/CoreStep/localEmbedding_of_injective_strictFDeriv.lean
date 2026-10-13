import Mathlib
import Submission.Work.WilE7.CoreStep.exists_continuous_leftInverse_of_lipschitz_lowerBound

namespace Work.WilE7.CoreStep

open Filter Topology Set
open scoped Topology NNReal

/-- **A strictly differentiable map with injective derivative is a local embedding.**

Let `ζ : E → F` be strictly differentiable at `p` with derivative `ζ'`, and suppose `ζ'` admits a
continuous linear left inverse `Q` (so `ζ'` is injective). Then `ζ` restricts to a homeomorphism
onto its image on a neighbourhood `W` of `p`: there is `r : F → E`, continuous on `ζ '' W`, with
`r (ζ v) = v` for all `v ∈ W`.

The proof is elementary and avoids the inverse function theorem (in particular no completeness of
`F` is needed). Strict differentiability gives, for a suitable `c > 0` and some `W ∈ 𝓝 p`,
`‖ζ x - ζ y - ζ' (x - y)‖ ≤ c ‖x - y‖` on `W`. Combined with `‖x‖ = ‖Q (ζ' x)‖ ≤ ‖Q‖ ‖ζ' x‖`,
this yields the lower bound `‖x - y‖ ≤ C ‖ζ x - ζ y‖` on `W` with
`C = ‖Q‖ / (1 - c ‖Q‖)`. Such a lower bound makes `ζ` injective on `W` with a Lipschitz (hence
continuous) inverse on the image, which is
`exists_continuous_leftInverse_of_lipschitz_lowerBound`. -/
theorem localEmbedding_of_injective_strictFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ζ : E → F) (ζ' : E →L[ℝ] F) (p : E) (hζ : HasStrictFDerivAt ζ ζ' p)
    (Q : F →L[ℝ] E) (hQ : Q.comp ζ' = ContinuousLinearMap.id ℝ E) :
    ∃ W ∈ nhds p, ∃ r : F → E, ContinuousOn r (ζ '' W) ∧ ∀ v ∈ W, r (ζ v) = v := by
  classical
  -- `Q` is a left inverse of `ζ'`.
  have hQ' : ∀ x : E, Q (ζ' x) = x := fun x => by
    have h := congrArg (fun (L : E →L[ℝ] E) => L x) hQ
    simpa using h
  -- A constant `c > 0` with `c * ‖Q‖ < 1`.
  obtain ⟨c, hcpos, hcQ⟩ : ∃ c : NNReal, 0 < c ∧ (c : ℝ) * ‖Q‖ < 1 := by
    refine ⟨(2 * (‖Q‖₊ + 1))⁻¹, ?_, ?_⟩
    · positivity
    · have hco : (((2 * (‖Q‖₊ + 1))⁻¹ : NNReal) : ℝ) = (2 * (‖Q‖ + 1))⁻¹ := by
        push_cast; ring
      rw [hco, inv_mul_eq_div, div_lt_one (by positivity)]
      linarith [norm_nonneg Q]
  -- Strict differentiability gives `ApproximatesLinearOn` on some `W ∈ 𝓝 p`.
  obtain ⟨W, hW, happrox⟩ := hζ.approximates_deriv_on_nhds (c := c) (Or.inr hcpos)
  have hKpos : (0 : ℝ) < 1 - c * ‖Q‖ := by linarith [hcQ]
  -- The Lipschitz lower bound on `W`.
  have hbound : ∀ x ∈ W, ∀ y ∈ W,
      ‖x - y‖ ≤ (⟨‖Q‖ / (1 - c * ‖Q‖), div_nonneg (norm_nonneg _) (le_of_lt hKpos)⟩ : NNReal)
        * ‖ζ x - ζ y‖ := by
    intro x hx y hy
    have hQx : ‖x - y‖ ≤ ‖Q‖ * ‖ζ' (x - y)‖ := by
      calc ‖x - y‖ = ‖Q (ζ' (x - y))‖ := by rw [hQ' (x - y)]
        _ ≤ ‖Q‖ * ‖ζ' (x - y)‖ := Q.le_opNorm _
    have hB : ‖ζ' (x - y)‖ ≤ c * ‖x - y‖ + ‖ζ x - ζ y‖ := by
      have hsplit : ζ' (x - y) = (ζ x - ζ y) - (ζ x - ζ y - ζ' (x - y)) := by abel
      have hEq : ‖ζ' (x - y)‖ = ‖(ζ x - ζ y) - (ζ x - ζ y - ζ' (x - y))‖ :=
        congrArg (fun z => ‖z‖) hsplit
      calc ‖ζ' (x - y)‖ = ‖(ζ x - ζ y) - (ζ x - ζ y - ζ' (x - y))‖ := hEq
        _ ≤ ‖ζ x - ζ y‖ + ‖ζ x - ζ y - ζ' (x - y)‖ := norm_sub_le _ _
        _ ≤ ‖ζ x - ζ y‖ + c * ‖x - y‖ := by
            gcongr
            exact happrox x hx y hy
        _ = c * ‖x - y‖ + ‖ζ x - ζ y‖ := by ring
    have hmain : (1 - c * ‖Q‖) * ‖x - y‖ ≤ ‖Q‖ * ‖ζ x - ζ y‖ := by
      have h2 : ‖Q‖ * ‖ζ' (x - y)‖ ≤ ‖Q‖ * (c * ‖x - y‖ + ‖ζ x - ζ y‖) :=
        mul_le_mul_of_nonneg_left hB (norm_nonneg Q)
      have h3 : ‖x - y‖ ≤ ‖Q‖ * (c * ‖x - y‖ + ‖ζ x - ζ y‖) := le_trans hQx h2
      nlinarith [h3]
    rw [div_mul_eq_mul_div, le_div_iff₀ hKpos]
    nlinarith [hmain]
  -- A Lipschitz lower bound yields a continuous local left inverse.
  obtain ⟨r, hrc, hrv⟩ :=
    exists_continuous_leftInverse_of_lipschitz_lowerBound ζ W _ hbound
  exact ⟨W, hW, r, hrc, hrv⟩

end Work.WilE7.CoreStep
