/-
# `Work.KMTAreas.A4.lip2AmplifyStatement` — Green--Tao Lemma 3.1(ii) as `AmplifyStatement`

The **consumer of the amplification step** `Work.KMTAreas.A4.lip2Amplify`: the statement
`AmplifyStatement` (`Work.KMTAreas.A4.invWeylDefs`) in the exact shape in which the inverse-Weyl
cascade uses it (`Work.KMTAreas.A4.invWeylWindow.IWP_succ`, hypothesis `hAmp`).

`AmplifyStatement` asks for a *constant* `C₂` such that a `δ₂`-dense set `T ⊆ [-N,N]` on which every
`β n` is within `δ₁` of an integer — with the paper's hypotheses `δ₂ ≤ 1/2`, `16 δ₁ ≤ δ₂²`,
`2/δ₂ ≤ N` — forces a rational approximation of `β` with denominator `≤ C₂/δ₂` and error
`≤ C₂ δ₁/(δ₂³ N)`.

Note the hypothesis here is `16 δ₁ ≤ δ₂²`, i.e. *weaker* than the `50 δ₁ ≤ δ₂²` of the frozen
`lip2Amplify`: the version proved here is therefore `lip2AmplifyCore` (which only needs
`16 δ₁ ≤ δ₂`), using `δ₂ ≤ 1/2` to pass from `16 δ₁ ≤ δ₂²` to `16 δ₁ ≤ δ₂`, and `2/δ₂ ≤ N` to
supply the density hypothesis `1 ≤ δ₂(N+1)`.  The constant `C₂ = 2^20` and the passage from
`2N+1` to `N` are the only bookkeeping.

(An alternative route would be to fill the stub `Work.KMTAreas.A4.invWeylAmplify`, which states
exactly `AmplifyStatement`; that file is not mine to edit, so this module provides the statement.)
-/
import Mathlib
import Submission.Work.KMTAreas.A4.invWeylDefs
import Submission.Work.KMTAreas.A4.lip2Amplify

namespace Work.KMTAreas.A4

/-- **Green--Tao Lemma 3.1(ii)** (the amplification of the "dense multiples" estimate) in the form
consumed by the inverse-Weyl cascade: `AmplifyStatement` holds with the constant `2^20`. -/
theorem lip2AmplifyStatement : AmplifyStatement := by
  unfold AmplifyStatement
  refine ⟨(2 : ℝ) ^ 20, ?_⟩
  rintro ⟨_hC, _hDense⟩ β δ₁ δ₂ N T hN hδ₁ hδ₂ hδ₂le h16 hNd hT hcard hgood
  have hN1 : 1 ≤ N := by omega
  have hδ₂one : δ₂ ≤ 1 := by linarith
  have h16' : 16 * δ₁ ≤ δ₂ := by nlinarith [h16, hδ₂, hδ₂le]
  have hdens : 1 ≤ δ₂ * ((N : ℝ) + 1) := by
    have h2 : 2 ≤ (N : ℝ) * δ₂ := (div_le_iff₀ hδ₂).mp hNd
    nlinarith [h2, hδ₂]
  obtain ⟨q, hq1, hqle, a, ha⟩ :=
    lip2AmplifyCore β δ₁ δ₂ N T hN1 hδ₁ hδ₂ hδ₂one h16' hdens hT hcard hgood
  refine ⟨q, hq1, hqle, a, ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hmono : 2 ^ 20 * δ₁ / (δ₂ ^ 3 * (2 * (N : ℝ) + 1)) ≤
      2 ^ 20 * δ₁ / (δ₂ ^ 3 * (N : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < δ₂ ^ 3 * (2 * (N : ℝ) + 1))
      (by positivity : (0 : ℝ) < δ₂ ^ 3 * (N : ℝ))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith : (N : ℝ) ≤ 2 * (N : ℝ) + 1) (by positivity)
  exact le_trans ha hmono

end Work.KMTAreas.A4
