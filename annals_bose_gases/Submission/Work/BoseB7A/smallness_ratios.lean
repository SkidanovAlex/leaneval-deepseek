import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7A.Statements
import Submission.Work.BoseB7A.smallness_conj1
import Submission.Work.BoseB7A.smallness_conj5
import Submission.Work.BoseB7A.smallness_conj6
import Submission.Work.BoseB7A.smallness_conj7
import Submission.Work.BoseB7A.smallness_conj8
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7A.smallness_ratios` — the smallness of every §10 ratio at FS's parameters

At FS's parameter point (`Work.BoseB7.FSParamsView E`) every scalar of the `Q3Env`
is a monomial `fsXp t c = (μa³)^{c/323}` with `t = μa³` the diluteness
(`Work.BoseB7.FSParamsVals`), so *every* combination that occurs as a smallness
hypothesis in §10 is, up to a constant, a positive power of `X = (μa³)^{1/323}`:

| quantity | value |
|---|---|
| `K_L·√(μa)·(K_H a)` | `X^{55/4}` |
| `𝓁 = E.lille` | `X^{97/2}` |
| `K_ℓ²𝓁²` | `X^{94}` |
| `K_ℓ²K_H⁻¹` | `X^{537/4}` |
| `(𝓜+1)(K_ℓK_L)³/(μℓ³)` | `≤ 2X^{193/4}` |
| `K_Ha/ℓ` | `X^{103/4}` |
| `1/(2sℓ)` vs `1/(8K_Ha)` | holds once `X ≤ 1/4` |
| `aK_H(1+log K_H)/(dsℓ)` | `≤ X^{75/4} + (549/4)X^{71/4}` |
| `K_ℓK_L` | `X^{-12} ≥ 1` |

Hence for every `c > 0` there is `t₀ > 0` (namely `τ^{323}` with
`τ = min (1/4) (c/(553/4))^{4/55}`) such that all nine ratios are `≤ c` whenever
`t ≤ t₀` — the threshold is *uniform* in `Mode` and in the whole environment `E`:
only `t` enters.  The constant `553/4` is the largest weight that occurs
(`1 + 549/4`, the weight of the log term of the eighth ratio), so `A = 553/4`
dominates every constant factor that appears (including the `2` of the fifth).

The five non-trivial conjuncts are the delegated lemmas
`smallness_conj1, smallness_conj5, smallness_conj6, smallness_conj7,
smallness_conj8` of this directory; the four monomial ones are proved here.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

open Work.BoseB7 Work.BoseBox

set_option linter.unusedVariables false

/-- **The master inequality of the threshold**: for `0 < t ≤ τ^323` and `p ≥ 0`,
`fsXp t p = (μa³)^{p/323} ≤ τ^p`. -/
lemma fsXp_le_of_le_pow {t τ p : ℝ} (ht : 0 < t) (hτ : 0 < τ) (h : t ≤ τ ^ 323)
    (hp : 0 ≤ p) : fsXp t p ≤ τ ^ p := by
  have h1 : fsXp t p ≤ fsXp (τ ^ 323) p := by
    simp only [fsXp]
    exact Real.rpow_le_rpow ht.le h (by positivity)
  have h2 : fsXp (τ ^ 323) p = τ ^ p := by
    simp only [fsXp]
    rw [← Real.rpow_natCast τ 323, ← Real.rpow_mul hτ.le]
    congr 1
    push_cast
    ring
  linarith [h1, h2]

/-- **The uniform smallness of every §10 ratio.**  For every `c > 0` there is a
diluteness threshold `t₀ > 0` such that at every parameter point `E` of FS with
`μa³ = hv.t ≤ t₀` (and every `b ≥ b₀`), the nine scalar combinations of §10 that
occur as smallness hypotheses are all `≤ c`.  The constants are absolute: `t₀`
depends only on `c`. -/
theorem smallness_ratios (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) (c : ℝ) (hc : 0 < c) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b →
        (E.KL * Real.sqrt (E.mu * E.aScat) * (E.KH * E.aScat) ≤ c) ∧
        (E.lille ≤ c) ∧
        (E.Kl ^ 2 * E.lille ^ 2 ≤ c) ∧
        (E.Kl ^ 2 * (E.KH)⁻¹ ≤ c) ∧
        ((E.bigM + 1) * (E.Kl * E.KL) ^ 3 / (E.mu * E.ell ^ 3) ≤ c) ∧
        (E.KH * E.aScat / E.ell ≤ c) ∧
        (1 / (2 * E.s * E.ell) ≤ 1 / (8 * E.KH * E.aScat)) ∧
        (E.aScat * E.KH * (1 + Real.log E.KH) / (E.d * E.s * E.ell) ≤ c) ∧
        (1 ≤ E.Kl * E.KL) := by
  have hA : 0 < (553 / 4 : ℝ) := by norm_num
  have hA1 : 1 ≤ (553 / 4 : ℝ) := by norm_num
  have hA2 : 2 ≤ (553 / 4 : ℝ) := by norm_num
  have hcA : 0 < c / (553 / 4) := div_pos hc hA
  -- the threshold, in the `X`-variable
  set τ : ℝ := min (1 / 4) ((c / (553 / 4)) ^ (4 / 55 : ℝ)) with hτdef
  have hτ4 : τ ≤ 1 / 4 := min_le_left _ _
  have hτ1 : τ ≤ 1 := le_trans hτ4 (by norm_num)
  have hτ0 : 0 < τ := lt_min (by norm_num) (Real.rpow_pos_of_pos hcA _)
  -- `τ^{55/4} ≤ c/(553/4)`: every ratio is bounded by a positive power of `τ`
  -- whose exponent is `≥ 55/4`, times a constant at most `553/4`
  have hτpow : τ ^ (55 / 4 : ℝ) ≤ c / (553 / 4) := by
    have hz : τ ≤ (c / (553 / 4)) ^ (4 / 55 : ℝ) := min_le_right _ _
    have h1 : τ ^ (55 / 4 : ℝ) ≤ ((c / (553 / 4)) ^ (4 / 55 : ℝ)) ^ (55 / 4 : ℝ) :=
      Real.rpow_le_rpow hτ0.le hz (by norm_num)
    have h2 : ((c / (553 / 4)) ^ (4 / 55 : ℝ)) ^ (55 / 4 : ℝ) = c / (553 / 4) := by
      rw [← Real.rpow_mul hcA.le, show (4 / 55) * (55 / 4) = (1 : ℝ) by norm_num,
        Real.rpow_one]
    linarith [h1, h2]
  have hcAle : c / (553 / 4) ≤ c := by
    rw [div_le_iff₀ hA]
    nlinarith [hc, hA1]
  refine ⟨τ ^ 323, by positivity, ?_⟩
  intro Mode _ _ E hv ht hb
  -- `X = (μa³)^{1/323} ≤ τ`
  have hX : fsXp hv.t 1 ≤ τ := by
    have h := fsXp_le_of_le_pow (p := 1) hv.t_pos hτ0 ht (by norm_num)
    rwa [Real.rpow_one] at h
  -- monotonicity of `p ↦ τ^p` for `p ≥ 55/4` (`τ ≤ 1`)
  have hle : ∀ p : ℝ, 55 / 4 ≤ p → τ ^ p ≤ τ ^ (55 / 4 : ℝ) := fun p hp =>
    Real.rpow_le_rpow_of_exponent_ge hτ0 hτ1 hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `K_L√(μa)·K_H a = X^{55/4} ≤ τ^{55/4} ≤ c/(553/4) ≤ c`
    have h1 := smallness_conj1 E hv hX
    linarith [h1, hτpow, hcAle]
  · -- `𝓁 = X^{97/2}`
    have h1 : E.lille = fsXp hv.t (97 / 2) := lille_val E hv
    have h2 : fsXp hv.t (97 / 2) ≤ τ ^ (97 / 2 : ℝ) :=
      fsXp_le_of_le_pow hv.t_pos hτ0 ht (by norm_num)
    have h3 : τ ^ (97 / 2 : ℝ) ≤ τ ^ (55 / 4 : ℝ) := hle _ (by norm_num)
    rw [h1]
    linarith [h2, h3, hτpow, hcAle]
  · -- `K_ℓ²𝓁² = X^{94}`
    have h1 : E.Kl ^ 2 * E.lille ^ 2 = fsXp hv.t 94 := by
      rw [Kl_val E hv, lille_val E hv, fsXp_pow hv.t_pos.le, fsXp_pow hv.t_pos.le,
        fsXp_mul hv.t_pos]
      congr 1
      norm_num
    have h2 : fsXp hv.t 94 ≤ τ ^ (94 : ℝ) := fsXp_le_of_le_pow hv.t_pos hτ0 ht (by norm_num)
    have h3 : τ ^ (94 : ℝ) ≤ τ ^ (55 / 4 : ℝ) := hle _ (by norm_num)
    rw [h1]
    linarith [h2, h3, hτpow, hcAle]
  · -- `K_ℓ²K_H⁻¹ = X^{537/4}`
    have h1 : E.Kl ^ 2 * (E.KH)⁻¹ = fsXp hv.t (537 / 4) := by
      rw [Kl_val E hv, KH_val E hv, fsXp_pow hv.t_pos.le, fsXp_inv hv.t_pos,
        fsXp_mul hv.t_pos]
      congr 1
      norm_num
    have h2 : fsXp hv.t (537 / 4) ≤ τ ^ (537 / 4 : ℝ) :=
      fsXp_le_of_le_pow hv.t_pos hτ0 ht (by norm_num)
    have h3 : τ ^ (537 / 4 : ℝ) ≤ τ ^ (55 / 4 : ℝ) := hle _ (by norm_num)
    rw [h1]
    linarith [h2, h3, hτpow, hcAle]
  · -- `(𝓜+1)(K_ℓK_L)³/(μℓ³) ≤ 2X^{193/4}`
    have h1 := smallness_conj5 E hv hX
    have h2 : τ ^ (193 / 4 : ℝ) ≤ τ ^ (55 / 4 : ℝ) := hle _ (by norm_num)
    have h3 : 2 * (c / (553 / 4)) ≤ c := by
      rw [show 2 * (c / (553 / 4)) = 2 * c / (553 / 4) by ring, div_le_iff₀ hA]
      nlinarith [hc, hA2]
    linarith [h1, h2, h3, hτpow]
  · -- `K_H a/ℓ = X^{103/4}`
    have h1 := smallness_conj6 E hv hX
    have h2 : τ ^ (103 / 4 : ℝ) ≤ τ ^ (55 / 4 : ℝ) := hle _ (by norm_num)
    linarith [h1, h2, hτpow, hcAle]
  · -- `1/(2sℓ) ≤ 1/(8K_Ha)`, which needs only `X ≤ 1/4`
    exact smallness_conj7 E hv (le_trans hX hτ4)
  · -- `aK_H(1+log K_H)/(dsℓ) ≤ X^{75/4} + (549/4)X^{71/4} ≤ (553/4)τ^{55/4} ≤ c`
    have h1 := smallness_conj8 E hv hτ1 hX
    have h5 : τ ^ (75 / 4 : ℝ) + (549 / 4) * τ ^ (71 / 4 : ℝ) ≤ c := by
      have h2 : τ ^ (75 / 4 : ℝ) ≤ τ ^ (55 / 4 : ℝ) := hle _ (by norm_num)
      have h3 : τ ^ (71 / 4 : ℝ) ≤ τ ^ (55 / 4 : ℝ) := hle _ (by norm_num)
      have h3' : (549 / 4) * τ ^ (71 / 4 : ℝ) ≤ (549 / 4) * τ ^ (55 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left h3 (by norm_num)
      have h7 : (553 / 4) * (c / (553 / 4)) = c := by field_simp
      nlinarith [h2, h3', hτpow, h7]
    linarith [h1, h5]
  · -- `K_ℓK_L = X^{-12} ≥ 1` since `t ≤ 1`
    have h1 : E.Kl * E.KL = fsXp hv.t (-12) := by
      rw [Kl_val E hv, KL_val E hv, fsXp_mul hv.t_pos]
      congr 1
      norm_num
    have h2 : (1 : ℝ) ≤ fsXp hv.t (-12) := by
      have h := fsXp_le_fsXp hv.t_pos hv.t_le_one (a := (0 : ℝ)) (b := (-12 : ℝ)) (by norm_num)
      simpa [fsXp] using h
    rw [h1]
    linarith

end Work.BoseB7A
