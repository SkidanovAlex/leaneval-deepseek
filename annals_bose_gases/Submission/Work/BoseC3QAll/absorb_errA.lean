import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseC3QAll.absz_bounds
import Submission.Work.BoseC3QAll.e23A_mul_aSq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.absorb_errA` — the absorption of the `Q₃⁽²⁾+Q₃⁽³⁾` errors

FS §10 (`lem:EstimatesOnQ3-js`, the pieces `Q₃⁽²⁾ + Q₃⁽³⁾`, i.e.
`eq:EstimateQ3Tilde2+3`) collects three error sums which must be absorbed by the
kinetic reserve `(𝓁²/2)∫_{P_H^q}𝒟_k b_k†b_k`.  This file proves the arithmetic
leg of that absorption, in the "absolute constants" form of this subproject:

> for every `K₀ ≥ 0`, `b₀ > 0` and `c > 0` there is `t₀ > 0` such that at every
> parameter point `FSParamsView E` with `t = μa³ ≤ t₀` and `b ≥ b₀`,
> ```
> 4·256·(√(ρ_zℓ³)/ℓ³)·K₀²·a·𝓁·√(𝓜+1)·(1+K₀(K_ℓK_L)³)·(128K_H²a²) ≤ c𝓁²,
> 4·256·(√(ρ_zℓ³)/ℓ³)·K₀²·a·𝓁·(64K₀²𝓁η)·K₀·(K_ℓK_L)³·(128K_H²a²) ≤ c𝓁²,
> 4·(√(ρ_zℓ³)/ℓ³)·K₀·(K_ℓK_L)³·(8ρ_zK₀aℓ³)·(64K₀²𝓁η) ≤ c·e23A.
> ```

## Why it is true

With `X = fsXp hv.t 1 = (μa³)^{1/323}` every scalar of the environment is a
monomial in `X` (and in the scattering length `a`, but the `a`'s cancel):

| quantity | value |
|---|---|
| `K_ℓ`, `K_L`, `K_H` | `X^{-3/2}`, `X^{-21/2}`, `X^{-549/4}` |
| `𝓁 = E.lille` | `X^{97/2}` |
| `η` | `X^{1236}` |
| `𝓜 = E.bigM` | `X^{-327/4}`, so `√(𝓜+1) ≤ √2·X^{-327/8}` |
| `a/ℓ` | `X^{163}` |
| `ρ_zℓ³ = z²` | `≤ (3/2)μℓ³ = (3/2)X^{-166}`, so `|z| ≤ √(3/2)X^{-83}` |
| `e23A = E₀ηK_L³K_ℓ^{3/2}(μa³)^{1/4}` | `E₀·X^{1283}`, `a²e23A = X^{1440}` |

The three left-hand sides are therefore (up to the constants written in the
statement) `X^{825/8}`, `X^{2857/2}` and `X^{2977/2}/a²` times `c`-free
constants, while the right-hand sides are `𝓁² = X^{97}` resp.
`c·e23A = cX^{1440}/a²`: the three ratios are (the constants of) `X^{49/8}`,
`X^{2663/2}` and `𝓁 = X^{97/2}`, hence tend to `0` as `t → 0⁺`
(recall `X = t^{1/323}`).  The threshold `t₀` is (hugely) non-explicit; only its
existence is needed.

## Contents

* `exists_thr` — the monomial threshold `A·fsXp t e ≤ c` for small `t`;
* `sqrt_bigM_add_one_le`, `KlKL_cube`, `KH_sq`, `lille_sq` — the monomial values
  of the error factors;
* `absorb_errA` — the three conjuncts, assembled by product comparisons.

The two genuinely analytic inputs of the assembly are *not* re-proved here: they
are the lemmas `Work.BoseC3QAll.absz_bounds` (the three bounds on
`z = √(ρ_zℓ³)`, proved in parallel in `BoseB7A/absz_bounds.lean`) and
`Work.BoseC3QAll.e23A_mul_aSq` (the monomial value of the `e23A` bracket, proved in
parallel in `BoseB7A/e23A_mul_aSq.lean`), both imported below.
-/

noncomputable section

open scoped BigOperators

set_option linter.unusedVariables false

namespace Work.BoseC3QAll

open Work.BoseB7 Work.BoseBox

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

/-! ## 1. The monomial threshold -/

/-- For every `A ≥ 0`, `e > 0` and `c > 0` there is `t₀ > 0` such that
`A·fsXp t e ≤ c` for every `0 < t ≤ t₀`. -/
lemma exists_thr (A e c : ℝ) (he : 0 < e) (hc : 0 < c) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → A * fsXp t e ≤ c := by
  by_cases hA : A ≤ 0
  · exact ⟨1, one_pos, fun t ht _ =>
      le_trans (mul_nonpos_of_nonpos_of_nonneg hA (fsXp_nonneg ht.le)) hc.le⟩
  · have hApos : 0 < A := not_le.mp hA
    obtain ⟨t₀, ht₀, h⟩ := fsXp_le_of_pos_exp he (div_pos hc hApos)
    refine ⟨t₀, ht₀, fun t ht hle => ?_⟩
    calc A * fsXp t e ≤ A * (c / A) := mul_le_mul_of_nonneg_left (h t ht hle) hApos.le
      _ = c := mul_div_cancel₀ c (ne_of_gt hApos)

/-! ## 2. The monomial values of the error factors -/

/-- `√(𝓜+1) ≤ √2·X^{-327/8}` (`𝓜 ≥ 1`, so `𝓜+1 ≤ 2𝓜`). -/
lemma sqrt_bigM_add_one_le (E : Q3Env Mode) (hv : FSParamsView E) :
    Real.sqrt (E.bigM + 1) ≤ Real.sqrt 2 * fsXp hv.t (-(327 / 8)) := by
  have hbM1 : (1 : ℝ) ≤ E.bigM := hv.one_le_bigM
  have hle : E.bigM + 1 ≤ 2 * E.bigM := by linarith
  have hsquare : (fsXp hv.t (-(327 / 8))) ^ 2 = E.bigM := by
    rw [fsXp_pow hv.t_pos.le, bigM_val E hv]
    congr 1
    norm_num
  have hnn : (0 : ℝ) ≤ Real.sqrt 2 * fsXp hv.t (-(327 / 8)) :=
    mul_nonneg (Real.sqrt_nonneg 2) (fsXp_pos hv.t_pos).le
  have hmain : Real.sqrt (2 * E.bigM) = Real.sqrt 2 * fsXp hv.t (-(327 / 8)) := by
    have h2 : (2 : ℝ) * E.bigM = (Real.sqrt 2 * fsXp hv.t (-(327 / 8))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hsquare]
    rw [h2, Real.sqrt_sq hnn]
  calc Real.sqrt (E.bigM + 1) ≤ Real.sqrt (2 * E.bigM) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt 2 * fsXp hv.t (-(327 / 8)) := hmain

/-- `(K_ℓK_L)³ = X^{-36}`. -/
lemma KlKL_cube (E : Q3Env Mode) (hv : FSParamsView E) :
    (E.Kl * E.KL) ^ 3 = fsXp hv.t (-36) := by
  rw [mul_pow, Kl_val E hv, KL_val E hv, fsXp_pow hv.t_pos.le, fsXp_pow hv.t_pos.le,
    fsXp_mul hv.t_pos]
  congr 1
  norm_num

/-- `K_H² = X^{-549/2}`. -/
lemma KH_sq (E : Q3Env Mode) (hv : FSParamsView E) :
    E.KH ^ 2 = fsXp hv.t (-(549 / 2)) := by
  rw [KH_val E hv, fsXp_pow hv.t_pos.le]
  congr 1
  norm_num

/-- `𝓁² = X^{97}`. -/
lemma lille_sq (E : Q3Env Mode) (hv : FSParamsView E) :
    E.lille ^ 2 = fsXp hv.t 97 := by
  rw [lille_val E hv, fsXp_pow hv.t_pos.le]
  congr 1
  norm_num

/-! ## 3. The three conjuncts -/

theorem absorb_errA (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) (hK₀ : 0 ≤ K₀) (c : ℝ) (hc : 0 < c) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b →
        (4 * 256 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille *
            Real.sqrt (E.bigM + 1) * (1 + K₀ * (E.Kl * E.KL) ^ 3) *
            (128 * E.KH ^ 2 * E.aScat ^ 2) ≤ c * E.lille ^ 2) ∧
        (4 * 256 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille *
            (64 * K₀ ^ 2 * E.lille * eta E) * K₀ * (E.Kl * E.KL) ^ 3 *
            (128 * E.KH ^ 2 * E.aScat ^ 2) ≤ c * E.lille ^ 2) ∧
        (4 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ * (E.Kl * E.KL) ^ 3 *
            (8 * E.rho * K₀ * E.aScat * E.ell ^ 3) * (64 * K₀ ^ 2 * E.lille * eta E)
          ≤ c * e23A E) := by
  -- the constant `K = max K₀ 1` dominates `K₀` and is `≥ 1`
  set K : ℝ := max K₀ 1 with hKdef
  have hK1 : (1 : ℝ) ≤ K := le_max_right _ _
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  have hK0K : K₀ ≤ K := le_max_left _ _
  have hK2 : K₀ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hK₀ hK0K 2
  have hK4 : K₀ ^ 4 ≤ K ^ 4 := pow_le_pow_left₀ hK₀ hK0K 4
  have hK5 : K₀ ^ 5 ≤ K ^ 5 := pow_le_pow_left₀ hK₀ hK0K 5
  -- the three monomial thresholds
  obtain ⟨t₁, ht₁, hthr₁⟩ :=
    exists_thr (131072 * (5 / 4) * Real.sqrt 2 * (1 + K) * K ^ 2) (49 / 8) c (by norm_num) hc
  obtain ⟨t₂, ht₂, hthr₂⟩ :=
    exists_thr (8388608 * (5 / 4) * K ^ 5) (2663 / 2) c (by norm_num) hc
  obtain ⟨t₃, ht₃, hthr₃⟩ :=
    exists_thr (2048 * (3 / 2) * Real.sqrt (3 / 2) * K ^ 4) (97 / 2) c (by norm_num) hc
  refine ⟨min (min t₁ t₂) (min t₃ 1),
    lt_min (lt_min ht₁ ht₂) (lt_min ht₃ one_pos), ?_⟩
  intro Mode _ _ E hv hle _
  have hleA : hv.t ≤ min t₁ t₂ := le_trans hle (min_le_left _ _)
  have hleB : hv.t ≤ min t₃ 1 := le_trans hle (min_le_right _ _)
  have ht1' : hv.t ≤ t₁ := le_trans hleA (min_le_left _ _)
  have ht2' : hv.t ≤ t₂ := le_trans hleA (min_le_right _ _)
  have ht3' : hv.t ≤ t₃ := le_trans hleB (min_le_left _ _)
  have ht1 : hv.t ≤ 1 := le_trans hleB (min_le_right _ _)
  have hX1 := hthr₁ hv.t hv.t_pos ht1'
  have hX2 := hthr₂ hv.t hv.t_pos ht2'
  have hX3 := hthr₃ hv.t hv.t_pos ht3'
  obtain ⟨_, hSa3, hW3⟩ := absz_bounds E hv
  -- positivity helpers
  have ht0 : (0 : ℝ) < hv.t := hv.t_pos
  have hℓ0 : (0 : ℝ) < E.ell := ell_pos E hv
  have ha0 : (0 : ℝ) < E.aScat := hv.a_pos
  have hρ0 : (0 : ℝ) ≤ E.rho := (rho_pos E hv).le
  have hη0 : (0 : ℝ) ≤ eta E := by rw [eta_eq E hv]; exact (fsXp_pos ht0).le
  have hbM0 : (0 : ℝ) ≤ E.bigM := bigM_nonneg E hv
  refine ⟨?_, ?_, ?_⟩
  · -- ===== conjunct 1 =====
    have hG : Real.sqrt (E.bigM + 1) ≤ Real.sqrt 2 * fsXp hv.t (-(327 / 8)) :=
      sqrt_bigM_add_one_le E hv
    have hF : 1 + K₀ * fsXp hv.t (-36) ≤ (1 + K) * fsXp hv.t (-36) := by
      have hQ1 : (1 : ℝ) ≤ fsXp hv.t (-36) := by
        have h := fsXp_le_fsXp hv.t_pos ht1 (a := (0 : ℝ)) (b := (-36 : ℝ)) (by norm_num)
        simpa [fsXp] using h
      nlinarith [hQ1, hK0K, hK₀]
    have hprod : 131072 * K₀ ^ 2 * E.KH ^ 2 *
          ((Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * E.aScat ^ 3) * E.lille *
          Real.sqrt (E.bigM + 1) * (1 + K₀ * fsXp hv.t (-36))
        ≤ 131072 * K ^ 2 * fsXp hv.t (-(549 / 2)) * ((5 / 4) * fsXp hv.t 406) *
          fsXp hv.t (97 / 2) * (Real.sqrt 2 * fsXp hv.t (-(327 / 8))) *
          ((1 + K) * fsXp hv.t (-36)) := by
      rw [KH_sq E hv, lille_val E hv]
      gcongr <;> (try simp only [fsXp]) <;> positivity
    have hcomb : 131072 * K ^ 2 * fsXp hv.t (-(549 / 2)) * ((5 / 4) * fsXp hv.t 406) *
          fsXp hv.t (97 / 2) * (Real.sqrt 2 * fsXp hv.t (-(327 / 8))) *
          ((1 + K) * fsXp hv.t (-36))
        = (131072 * (5 / 4) * Real.sqrt 2 * (1 + K) * K ^ 2) * fsXp hv.t (825 / 8) := by
      have hfs : fsXp hv.t (-(549 / 2)) * fsXp hv.t 406 * fsXp hv.t (97 / 2) *
            fsXp hv.t (-(327 / 8)) * fsXp hv.t (-36) = fsXp hv.t (825 / 8) := by
        rw [fsXp_mul hv.t_pos, fsXp_mul hv.t_pos, fsXp_mul hv.t_pos, fsXp_mul hv.t_pos]
        congr 1
        norm_num
      calc 131072 * K ^ 2 * fsXp hv.t (-(549 / 2)) * ((5 / 4) * fsXp hv.t 406) *
            fsXp hv.t (97 / 2) * (Real.sqrt 2 * fsXp hv.t (-(327 / 8))) *
            ((1 + K) * fsXp hv.t (-36))
          = (131072 * (5 / 4) * Real.sqrt 2 * (1 + K) * K ^ 2) *
            (fsXp hv.t (-(549 / 2)) * fsXp hv.t 406 * fsXp hv.t (97 / 2) *
              fsXp hv.t (-(327 / 8)) * fsXp hv.t (-36)) := by ring
        _ = (131072 * (5 / 4) * Real.sqrt 2 * (1 + K) * K ^ 2) * fsXp hv.t (825 / 8) := by
            rw [hfs]
    have hsplit : fsXp hv.t (825 / 8) = fsXp hv.t (49 / 8) * fsXp hv.t 97 := by
      rw [show (825 : ℝ) / 8 = 49 / 8 + 97 by norm_num, ← fsXp_mul hv.t_pos]
    calc 4 * 256 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille *
          Real.sqrt (E.bigM + 1) * (1 + K₀ * (E.Kl * E.KL) ^ 3) *
          (128 * E.KH ^ 2 * E.aScat ^ 2)
        = 131072 * K₀ ^ 2 * E.KH ^ 2 *
          ((Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * E.aScat ^ 3) * E.lille *
          Real.sqrt (E.bigM + 1) * (1 + K₀ * (E.Kl * E.KL) ^ 3) := by ring
      _ = 131072 * K₀ ^ 2 * E.KH ^ 2 *
          ((Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * E.aScat ^ 3) * E.lille *
          Real.sqrt (E.bigM + 1) * (1 + K₀ * fsXp hv.t (-36)) := by rw [KlKL_cube E hv]
      _ ≤ 131072 * K ^ 2 * fsXp hv.t (-(549 / 2)) * ((5 / 4) * fsXp hv.t 406) *
          fsXp hv.t (97 / 2) * (Real.sqrt 2 * fsXp hv.t (-(327 / 8))) *
          ((1 + K) * fsXp hv.t (-36)) := hprod
      _ = (131072 * (5 / 4) * Real.sqrt 2 * (1 + K) * K ^ 2) * fsXp hv.t (825 / 8) := hcomb
      _ = ((131072 * (5 / 4) * Real.sqrt 2 * (1 + K) * K ^ 2) * fsXp hv.t (49 / 8)) *
          fsXp hv.t 97 := by rw [hsplit]; ring
      _ ≤ c * fsXp hv.t 97 := mul_le_mul_of_nonneg_right hX1 (fsXp_nonneg ht0.le)
      _ = c * E.lille ^ 2 := by rw [lille_sq E hv]
  · -- ===== conjunct 2 =====
    have hη : eta E ≤ fsXp hv.t 1236 := le_of_eq (eta_eq E hv)
    have hprod : 8388608 * K₀ ^ 5 * E.KH ^ 2 * E.lille ^ 2 * (E.Kl * E.KL) ^ 3 *
          (((Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * E.aScat ^ 3) * eta E)
        ≤ 8388608 * K ^ 5 * fsXp hv.t (-(549 / 2)) * fsXp hv.t 97 * fsXp hv.t (-36) *
          (((5 / 4) * fsXp hv.t 406) * fsXp hv.t 1236) := by
      rw [KH_sq E hv, lille_sq E hv, KlKL_cube E hv]
      gcongr <;> (try simp only [fsXp]) <;> positivity
    have hcomb : 8388608 * K ^ 5 * fsXp hv.t (-(549 / 2)) * fsXp hv.t 97 * fsXp hv.t (-36) *
          (((5 / 4) * fsXp hv.t 406) * fsXp hv.t 1236)
        = (8388608 * (5 / 4) * K ^ 5) * fsXp hv.t (2857 / 2) := by
      have hfs : fsXp hv.t (-(549 / 2)) * fsXp hv.t 406 * fsXp hv.t 97 * fsXp hv.t 1236 *
            fsXp hv.t (-36) = fsXp hv.t (2857 / 2) := by
        rw [fsXp_mul hv.t_pos, fsXp_mul hv.t_pos, fsXp_mul hv.t_pos, fsXp_mul hv.t_pos]
        congr 1
        norm_num
      calc 8388608 * K ^ 5 * fsXp hv.t (-(549 / 2)) * fsXp hv.t 97 * fsXp hv.t (-36) *
            (((5 / 4) * fsXp hv.t 406) * fsXp hv.t 1236)
          = (8388608 * (5 / 4) * K ^ 5) *
            (fsXp hv.t (-(549 / 2)) * fsXp hv.t 406 * fsXp hv.t 97 * fsXp hv.t 1236 *
              fsXp hv.t (-36)) := by ring
        _ = (8388608 * (5 / 4) * K ^ 5) * fsXp hv.t (2857 / 2) := by rw [hfs]
    have hsplit : fsXp hv.t (2857 / 2) = fsXp hv.t (2663 / 2) * fsXp hv.t 97 := by
      rw [show (2857 : ℝ) / 2 = 2663 / 2 + 97 by norm_num, ← fsXp_mul hv.t_pos]
    calc 4 * 256 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille *
          (64 * K₀ ^ 2 * E.lille * eta E) * K₀ * (E.Kl * E.KL) ^ 3 *
          (128 * E.KH ^ 2 * E.aScat ^ 2)
        = 8388608 * K₀ ^ 5 * E.KH ^ 2 * E.lille ^ 2 * (E.Kl * E.KL) ^ 3 *
          (((Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * E.aScat ^ 3) * eta E) := by ring
      _ ≤ 8388608 * K ^ 5 * fsXp hv.t (-(549 / 2)) * fsXp hv.t 97 * fsXp hv.t (-36) *
          (((5 / 4) * fsXp hv.t 406) * fsXp hv.t 1236) := hprod
      _ = (8388608 * (5 / 4) * K ^ 5) * fsXp hv.t (2857 / 2) := hcomb
      _ = ((8388608 * (5 / 4) * K ^ 5) * fsXp hv.t (2663 / 2)) * fsXp hv.t 97 := by
          rw [hsplit]; ring
      _ ≤ c * fsXp hv.t 97 := mul_le_mul_of_nonneg_right hX2 (fsXp_nonneg ht0.le)
      _ = c * E.lille ^ 2 := by rw [lille_sq E hv]
  · -- ===== conjunct 3 =====
    have ha2 : (0 : ℝ) < E.aScat ^ 2 := by positivity
    have hS3 : (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * E.ell ^ 3 = |E.z| := by
      rw [div_mul_cancel₀ _ (pow_ne_zero 3 (ne_of_gt hℓ0)), ← zsq_eq E hv,
        Real.sqrt_sq_eq_abs]
    have hid : E.aScat ^ 2 *
          ((Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * E.rho * E.aScat * E.ell ^ 3)
        = E.aScat ^ 3 * E.rho * |E.z| := by
      calc E.aScat ^ 2 *
            ((Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * E.rho * E.aScat * E.ell ^ 3)
          = ((Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * E.ell ^ 3) *
            (E.aScat ^ 3 * E.rho) := by ring
        _ = |E.z| * (E.aScat ^ 3 * E.rho) := by rw [hS3]
        _ = E.aScat ^ 3 * E.rho * |E.z| := by ring
    have hkey : E.aScat ^ 2 *
          (4 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ * (E.Kl * E.KL) ^ 3 *
            (8 * E.rho * K₀ * E.aScat * E.ell ^ 3) * (64 * K₀ ^ 2 * E.lille * eta E))
        ≤ E.aScat ^ 2 * (c * e23A E) := by
      have hrearr : E.aScat ^ 2 *
            (4 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ * (E.Kl * E.KL) ^ 3 *
              (8 * E.rho * K₀ * E.aScat * E.ell ^ 3) * (64 * K₀ ^ 2 * E.lille * eta E))
          = 2048 * K₀ ^ 4 * (E.Kl * E.KL) ^ 3 * (E.aScat ^ 3 * E.rho * |E.z|) *
            E.lille * eta E := by
        rw [show E.aScat ^ 2 *
              (4 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ * (E.Kl * E.KL) ^ 3 *
                (8 * E.rho * K₀ * E.aScat * E.ell ^ 3) * (64 * K₀ ^ 2 * E.lille * eta E))
            = 2048 * K₀ ^ 4 * (E.Kl * E.KL) ^ 3 *
              (E.aScat ^ 2 *
                ((Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * E.rho * E.aScat * E.ell ^ 3)) *
              E.lille * eta E from by ring, hid]
      have hprod : 2048 * K₀ ^ 4 * (E.Kl * E.KL) ^ 3 * (E.aScat ^ 3 * E.rho * |E.z|) *
            E.lille * eta E
          ≤ 2048 * K ^ 4 * fsXp hv.t (-36) *
            ((3 / 2) * Real.sqrt (3 / 2) * fsXp hv.t 240) * fsXp hv.t (97 / 2) *
            fsXp hv.t 1236 := by
        rw [KlKL_cube E hv, lille_val E hv, eta_eq E hv]
        gcongr <;> (try simp only [fsXp]) <;> positivity
      have hcomb : 2048 * K ^ 4 * fsXp hv.t (-36) *
            ((3 / 2) * Real.sqrt (3 / 2) * fsXp hv.t 240) * fsXp hv.t (97 / 2) *
            fsXp hv.t 1236
          = (2048 * (3 / 2) * Real.sqrt (3 / 2) * K ^ 4) * fsXp hv.t (2977 / 2) := by
        have hfs : fsXp hv.t (-36) * fsXp hv.t 240 * fsXp hv.t (97 / 2) * fsXp hv.t 1236
            = fsXp hv.t (2977 / 2) := by
          rw [fsXp_mul hv.t_pos, fsXp_mul hv.t_pos, fsXp_mul hv.t_pos]
          congr 1
          norm_num
        calc 2048 * K ^ 4 * fsXp hv.t (-36) *
              ((3 / 2) * Real.sqrt (3 / 2) * fsXp hv.t 240) * fsXp hv.t (97 / 2) *
              fsXp hv.t 1236
            = (2048 * (3 / 2) * Real.sqrt (3 / 2) * K ^ 4) *
              (fsXp hv.t (-36) * fsXp hv.t 240 * fsXp hv.t (97 / 2) * fsXp hv.t 1236) := by
              ring
          _ = (2048 * (3 / 2) * Real.sqrt (3 / 2) * K ^ 4) * fsXp hv.t (2977 / 2) := by
              rw [hfs]
      have hsplit : fsXp hv.t (2977 / 2) = fsXp hv.t (97 / 2) * fsXp hv.t 1440 := by
        rw [show (2977 : ℝ) / 2 = 97 / 2 + 1440 by norm_num, ← fsXp_mul hv.t_pos]
      have hrhs : E.aScat ^ 2 * (c * e23A E) = c * fsXp hv.t 1440 := by
        calc E.aScat ^ 2 * (c * e23A E) = c * (E.aScat ^ 2 * e23A E) := by ring
          _ = c * fsXp hv.t 1440 := by rw [e23A_mul_aSq E hv]
      calc E.aScat ^ 2 *
            (4 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ * (E.Kl * E.KL) ^ 3 *
              (8 * E.rho * K₀ * E.aScat * E.ell ^ 3) * (64 * K₀ ^ 2 * E.lille * eta E))
          = 2048 * K₀ ^ 4 * (E.Kl * E.KL) ^ 3 * (E.aScat ^ 3 * E.rho * |E.z|) *
            E.lille * eta E := hrearr
        _ ≤ 2048 * K ^ 4 * fsXp hv.t (-36) *
            ((3 / 2) * Real.sqrt (3 / 2) * fsXp hv.t 240) * fsXp hv.t (97 / 2) *
            fsXp hv.t 1236 := hprod
        _ = (2048 * (3 / 2) * Real.sqrt (3 / 2) * K ^ 4) * fsXp hv.t (2977 / 2) := hcomb
        _ = ((2048 * (3 / 2) * Real.sqrt (3 / 2) * K ^ 4) * fsXp hv.t (97 / 2)) *
            fsXp hv.t 1440 := by rw [hsplit]; ring
        _ ≤ c * fsXp hv.t 1440 := mul_le_mul_of_nonneg_right hX3 (fsXp_nonneg ht0.le)
        _ = E.aScat ^ 2 * (c * e23A E) := hrhs.symm
    exact le_of_mul_le_mul_left hkey ha2

end Work.BoseC3QAll
