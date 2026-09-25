import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Commons.Analysis.Fourier.exists_dyadic_frequency_bump
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation

/-!
# The vocabulary of the Duoandikoetxea–Rubio de Francia route to `mst_theta_real`

This module fixes the objects of `Maximal/DRDF_ROUTE.md` (the project lead's CZ-free proof of
MST's input `(C2)`, i.e. of `mst_theta_real`):

* `curveSigma P N h` — the curve average `x ↦ ∫₀¹ h (x − P (N t)) dt`;
* `mstThetaOp P i M ε h` — the signed lacunary sum of curve-average differences, i.e. the operator
  of `mst_theta_real`;
* `dyadD P k` — the dyadic difference `σ_{2^k} − σ_{2^{k+1}}`;
* `dyadTheta`, `dyadPsi` — the smooth dyadic frequency bump `θ` (from
  `Commons.Analysis.Fourier.exists_dyadic_frequency_bump`) and the Littlewood–Paley symbol
  `ψ = θ − θ(2·)` (supported in `{1/2 ≤ |ξ| ≤ 2}`, with `Σ_{a∈ℤ} ψ (2^a ξ) = 1` for `ξ ≠ 0`);
* `dyadicProj ψ l h` — the Littlewood–Paley projection `𝓕⁻ (ψ (2^l ·) 𝓕 h)`.

All the objects are `sorry`-free; the lemmas about them are the ones delegated in
`Maximal/DRDF_ROUTE.md`'s split.
-/

open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

noncomputable section

/-- The curve average of `h` along `P` at scale `n`: `x ↦ ∫₀¹ h (x − P (n t)) dt`. -/
noncomputable def curveSigma (P : Polynomial ℤ) (n : ℕ) (h : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∫ t in (0:ℝ)..1, h (x - (toRealPoly P).eval ((n : ℝ) * t))

@[simp] lemma curveSigma_apply (P : Polynomial ℤ) (n : ℕ) (h : ℝ → ℂ) (x : ℝ) :
    curveSigma P n h x = ∫ t in (0:ℝ)..1, h (x - (toRealPoly P).eval ((n : ℝ) * t)) := rfl

/-- The signed lacunary sum of curve-average differences: the operator of `mst_theta_real`. -/
noncomputable def mstThetaOp (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) (h : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∑ j ∈ Finset.range M, ε j *
    ((∫ t in (0:ℝ)..1, h (x - (toRealPoly P).eval (((2:ℝ) ^ (j * 2 ^ i)) * t)))
      - (∫ t in (0:ℝ)..1, h (x - (toRealPoly P).eval (((2:ℝ) ^ ((j+1) * 2 ^ i)) * t))))

/-- The dyadic difference of curve averages: `σ_{2^k} − σ_{2^{k+1}}`. -/
noncomputable def dyadD (P : Polynomial ℤ) (k : ℕ) (h : ℝ → ℂ) : ℝ → ℂ :=
  fun x => curveSigma P (2 ^ k) h x - curveSigma P (2 ^ (k + 1)) h x

/-- The signed dyadic sum `Σ_{k<K} ε_k D_k h` (the `mstThetaOp` with `i = 0`). -/
noncomputable def dyadSum (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (h : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∑ k ∈ Finset.range K, ε k * dyadD P k h x

/-- The smooth dyadic frequency bump of `exists_dyadic_frequency_bump`: it equals `1` for
`|ξ| ≤ 1`, vanishes for `|ξ| ≥ 2`, and its dyadic telescoping gives a partition of unity. -/
noncomputable def dyadTheta : ℝ → ℝ := Classical.choose Commons.Analysis.Fourier.exists_dyadic_frequency_bump

lemma dyadTheta_spec :
    ContDiff ℝ (⊤ : ℕ∞) dyadTheta ∧ HasCompactSupport dyadTheta ∧
      (∀ ξ : ℝ, |ξ| ≤ 1 → dyadTheta ξ = 1) ∧
      (∀ ξ : ℝ, 2 ≤ |ξ| → dyadTheta ξ = 0) ∧
      (∀ ξ : ℝ, ξ ≠ 0 →
        ∑' a : ℤ, (dyadTheta ((2:ℝ)^a * ξ) - dyadTheta ((2:ℝ)^(a+1) * ξ)) = 1) :=
  Classical.choose_spec Commons.Analysis.Fourier.exists_dyadic_frequency_bump

/-- The Littlewood–Paley symbol `ψ = θ − θ(2·)`: smooth, supported in `{1/2 ≤ |ξ| ≤ 2}`. -/
noncomputable def dyadPsi (ξ : ℝ) : ℝ := dyadTheta ξ - dyadTheta (2 * ξ)

/-- The Littlewood–Paley projections: the multiplier `ξ ↦ ψ (2^l ξ)`. -/
noncomputable def dyadicProj (ψ : ℝ → ℝ) (l : ℤ) (h : ℝ → ℂ) : ℝ → ℂ :=
  fun x => FourierTransform.fourierInv (fun ξ : ℝ => (ψ ((2:ℝ)^l * ξ) : ℂ)
    * FourierTransform.fourier h ξ) x

/-- The wider bump `ψ̃ = θ(·/2)`: it equals `1` on `[−2,2]` (hence on `supp ψ`) and vanishes for
`|ξ| ≥ 4`.  It is the bump of the *outer* Littlewood–Paley projection `S̃_l` of
`Maximal/DRDF_ROUTE.md` step 2, for which `S̃_l ∘ S_l = S_l`. -/
noncomputable def dyadTilde (ξ : ℝ) : ℝ := dyadTheta (ξ / 2)

lemma dyadTilde_one {ξ : ℝ} (hξ : |ξ| ≤ 2) : dyadTilde ξ = 1 := by
  have h1 : |ξ / 2| ≤ 1 := by rw [abs_div]; norm_num; linarith
  exact dyadTheta_spec.2.2.1 _ h1

lemma dyadTilde_zero {ξ : ℝ} (hξ : 4 ≤ |ξ|) : dyadTilde ξ = 0 := by
  have h1 : 2 ≤ |ξ / 2| := by rw [abs_div]; norm_num; linarith
  exact dyadTheta_spec.2.2.2.1 _ h1

/-- The signed Littlewood–Paley block of the dyadic sum used in `DRDF_ROUTE.md` step 2. -/
noncomputable def dyadBlock (P : Polynomial ℤ) (ψ : ℝ → ℝ) (K : ℕ) (ε : ℕ → ℂ) (s : ℤ)
    (h : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∑ k ∈ Finset.range K, (dyadicProj ψ (↑(P.natDegree * k) + s)
    (fun y => ε k * dyadD P k h y)) x

end

end Work.BourgainPlan.Maximal
