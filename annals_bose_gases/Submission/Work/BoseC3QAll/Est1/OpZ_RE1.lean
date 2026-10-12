import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseC3QAll.Prep
import Submission.Work.BoseC3QAll.errA_bounds
import Submission.Work.BoseC3QAll.smallness_conj8
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseC3QAll.Est1.OpZ_RE1` — the smallness of the `R1`-coefficient

At FS's parameter point (`FSParamsView E`) every scalar of the `Q3Env` is a
monomial in the diluteness `t = μa³` (`Work.BoseB7.FSParamsVals`):

| quantity | value |
|---|---|
| `K_ℓ = E.Kl` | `X^{-3/2}` |
| `K_L = E.KL` | `X^{-21/2}`, so `(K_ℓK_L)³ = X^{-36}` |
| `K_H = E.KH` | `X^{-549/4}`, so `K_H⁴ = X^{-549}` |
| `𝓜 = E.bigM` | `X^{-327/4}` |
| `a/ℓ` | `X^{163}`, so `(a/ℓ)⁶ = X^{978}` |
| `z² = ρ_zℓ³ ≤ (3/2)μℓ³` | `(3/2)X^{-166}` |
| `𝓁 = E.lille` | `X^{97/2}` |

with `X = (μa³)^{1/323} ≤ 1`.  Hence the whole left-hand side of `OpZ_RE1` is,
up to the absolute constant `393216·(2|K₀|³+|K₀|⁴)`, the single monomial

  `X^{-36}·X^{-549}·X^{812}·X^{-327/4} = X^{581/4}`,

and since `X ≤ 1` this is below `𝓁²/8 = X^{97}/8` as soon as `X^{193/4}` is small
enough — i.e. as soon as `t` is below the threshold `t₀ = τ^{323}` with
`τ = (1/(D+1))^{4/193}`, `D = 3145728·(2|K₀|³+|K₀|⁴)`.  The threshold depends only
on `K₀` (and not on `b₀`, `Mode`, `F`, `T`, `E`), which is what the callers need.

The estimate is the arithmetic input of the estimate `Est1.estT2sum_opZ` / the
`R1`-reserve bookkeeping: `𝓁²/8` is exactly the fraction of the `P_H^q`-reserve
that the summed shift `Σ_k c_k^{-1}‖Y_kΦ‖²` is allowed to consume.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll.Est1

open Work.BoseB7 Work.BoseBox

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

/-- **The master threshold inequality**: for `0 < t ≤ τ^323` and `p ≥ 0`,
`fsXp t p = (μa³)^{p/323} ≤ τ^p`. -/
lemma fsXp_le_of_pow_le {t τ p : ℝ} (ht : 0 < t) (hτ : 0 < τ) (h : t ≤ τ ^ 323)
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

/-- **The `a⁶(z/ℓ³)²` factor** at FS's parameter point:
`a⁶(z/ℓ³)² = (a/ℓ)⁶z² ≤ X^{978}·(3/2)X^{-166} = (3/2)X^{812}`. -/
lemma OpZ_RE1_aux_a (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E) :
    E.aScat ^ 6 * (E.z / E.ell ^ 3) ^ 2 ≤ (3 / 2) * fsXp hv.t 812 := by
  have ht : 0 < hv.t := hv.t_pos
  have hell : 0 < E.ell := ell_pos E hv
  have hdiv : E.aScat / E.ell = fsXp hv.t 163 := aScat_div_ell E hv
  -- `z² ≤ (3/2)μℓ³ = (3/2)X^{-166}`
  have hz2 : E.z ^ 2 ≤ (3 / 2) * fsXp hv.t (-166) := by
    have hE : 0 < E.ell ^ 3 := pow_pos hell 3
    calc E.z ^ 2 = E.rho * E.ell ^ 3 := zsq_eq E hv
      _ ≤ (3 / 2) * (E.mu * E.ell ^ 3) := by nlinarith [rho_le E hv, hE]
      _ = (3 / 2) * fsXp hv.t (-166) := by rw [mue_val E hv]
  -- `a⁶(z/ℓ³)² = (a/ℓ)⁶z²`
  have hrew : E.aScat ^ 6 * (E.z / E.ell ^ 3) ^ 2 = (E.aScat / E.ell) ^ 6 * E.z ^ 2 := by
    rw [div_pow, div_pow, show (E.ell ^ 3) ^ 2 = E.ell ^ 6 by ring]
    field_simp
  -- `(a/ℓ)⁶ = X^{978}`
  have h6 : (E.aScat / E.ell) ^ 6 = fsXp hv.t 978 := by
    rw [hdiv, fsXp_pow ht.le]
    norm_num
  calc E.aScat ^ 6 * (E.z / E.ell ^ 3) ^ 2
      = (E.aScat / E.ell) ^ 6 * E.z ^ 2 := hrew
    _ = fsXp hv.t 978 * E.z ^ 2 := by rw [h6]
    _ ≤ fsXp hv.t 978 * ((3 / 2) * fsXp hv.t (-166)) :=
        mul_le_mul_of_nonneg_left hz2 (fsXp_nonneg ht.le)
    _ = (3 / 2) * (fsXp hv.t 978 * fsXp hv.t (-166)) := by ring
    _ = (3 / 2) * fsXp hv.t 812 := by rw [fsXp_mul ht]; norm_num

/-- **The middle product** at FS's parameter point:
`K₀³(K_ℓK_L)³K_H⁴(𝓜+1+K₀(K_ℓK_L)³) ≤ (2|K₀|³+|K₀|⁴)X^{-2667/4}`. -/
lemma OpZ_RE1_aux_b (K₀ : ℝ) (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E) :
    K₀ ^ 3 * (E.Kl * E.KL) ^ 3 * E.KH ^ 4 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3)
      ≤ (2 * |K₀| ^ 3 + |K₀| ^ 4) * fsXp hv.t (-(2667 / 4)) := by
  have ht : 0 < hv.t := hv.t_pos
  have hKlKL : E.Kl * E.KL = fsXp hv.t (-12) := by
    rw [Kl_val E hv, KL_val E hv, fsXp_mul ht]
    congr 1
    norm_num
  have hP : (E.Kl * E.KL) ^ 3 = fsXp hv.t (-36) := by
    rw [hKlKL, ← Real.rpow_natCast, fsXp_rpow ht.le]
    congr 1
    norm_num
  have hQ : E.KH ^ 4 = fsXp hv.t (-549) := by
    rw [KH_val E hv, ← Real.rpow_natCast, fsXp_rpow ht.le]
    congr 1
    norm_num
  have hbigM : E.bigM = fsXp hv.t (-(327 / 4)) := bigM_val E hv
  -- monotone comparisons with `X ≤ 1`
  have h1le : (1 : ℝ) ≤ fsXp hv.t (-(327 / 4)) := by
    have h := fsXp_le_fsXp ht hv.t_le_one (a := (0 : ℝ)) (b := -(327 / 4)) (by norm_num)
    simpa [fsXp] using h
  have hPle : fsXp hv.t (-36) ≤ fsXp hv.t (-(327 / 4)) :=
    fsXp_le_fsXp ht hv.t_le_one (by norm_num)
  have hCnn : (0 : ℝ) ≤ 2 * |K₀| ^ 3 + |K₀| ^ 4 := by positivity
  -- the bracket, weighted by `K₀³`
  have hK3β : K₀ ^ 3 * (E.bigM + 1 + K₀ * fsXp hv.t (-36))
      ≤ (2 * |K₀| ^ 3 + |K₀| ^ 4) * fsXp hv.t (-(327 / 4)) := by
    have h3 : K₀ ^ 3 ≤ |K₀| ^ 3 := by
      rw [← abs_pow]
      exact le_abs_self _
    have h4 : E.bigM + 1 ≤ 2 * fsXp hv.t (-(327 / 4)) := by
      rw [hbigM]
      linarith [h1le]
    have hterm1 : K₀ ^ 3 * (E.bigM + 1) ≤ |K₀| ^ 3 * (2 * fsXp hv.t (-(327 / 4))) :=
      mul_le_mul h3 h4 (by linarith [hv.one_le_bigM]) (by positivity)
    have hterm2 : K₀ ^ 4 * fsXp hv.t (-36) ≤ |K₀| ^ 4 * fsXp hv.t (-(327 / 4)) := by
      have h5 : K₀ ^ 4 = |K₀| ^ 4 := by
        rw [← abs_pow]
        exact (abs_of_nonneg (by positivity : (0 : ℝ) ≤ K₀ ^ 4)).symm
      rw [h5]
      exact mul_le_mul_of_nonneg_left hPle (by positivity)
    have hexp : K₀ ^ 3 * (E.bigM + 1 + K₀ * fsXp hv.t (-36))
        = K₀ ^ 3 * (E.bigM + 1) + K₀ ^ 4 * fsXp hv.t (-36) := by ring
    have hsum : (2 * |K₀| ^ 3 + |K₀| ^ 4) * fsXp hv.t (-(327 / 4))
        = |K₀| ^ 3 * (2 * fsXp hv.t (-(327 / 4))) + |K₀| ^ 4 * fsXp hv.t (-(327 / 4)) := by
      ring
    linarith [hterm1, hterm2, hexp, hsum]
  have hcomb : fsXp hv.t (-(327 / 4)) * fsXp hv.t (-36) * fsXp hv.t (-549)
      = fsXp hv.t (-(2667 / 4)) := by
    rw [fsXp_mul ht, fsXp_mul ht]
    congr 1
    norm_num
  calc K₀ ^ 3 * (E.Kl * E.KL) ^ 3 * E.KH ^ 4 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3)
      = (K₀ ^ 3 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3)) * (E.Kl * E.KL) ^ 3 * E.KH ^ 4 := by
        ring
    _ ≤ ((2 * |K₀| ^ 3 + |K₀| ^ 4) * fsXp hv.t (-(327 / 4))) * fsXp hv.t (-36)
          * fsXp hv.t (-549) := by
        have h1 : (K₀ ^ 3 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3)) * (E.Kl * E.KL) ^ 3
            ≤ ((2 * |K₀| ^ 3 + |K₀| ^ 4) * fsXp hv.t (-(327 / 4))) * fsXp hv.t (-36) := by
          rw [hP]
          exact mul_le_mul_of_nonneg_right hK3β (fsXp_nonneg ht.le)
        have hn : (0 : ℝ) ≤ ((2 * |K₀| ^ 3 + |K₀| ^ 4) * fsXp hv.t (-(327 / 4)))
            * fsXp hv.t (-36) :=
          mul_nonneg (mul_nonneg hCnn (fsXp_nonneg ht.le)) (fsXp_nonneg ht.le)
        calc (K₀ ^ 3 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3)) * (E.Kl * E.KL) ^ 3
              * E.KH ^ 4
            = ((K₀ ^ 3 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3))
                * (E.Kl * E.KL) ^ 3) * E.KH ^ 4 := by ring
          _ ≤ (((2 * |K₀| ^ 3 + |K₀| ^ 4) * fsXp hv.t (-(327 / 4)))
                * fsXp hv.t (-36)) * E.KH ^ 4 :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ ≤ (((2 * |K₀| ^ 3 + |K₀| ^ 4) * fsXp hv.t (-(327 / 4)))
                * fsXp hv.t (-36)) * fsXp hv.t (-549) :=
              mul_le_mul_of_nonneg_left (le_of_eq hQ) hn
          _ = ((2 * |K₀| ^ 3 + |K₀| ^ 4) * fsXp hv.t (-(327 / 4))) * fsXp hv.t (-36)
                * fsXp hv.t (-549) := by ring
    _ = (2 * |K₀| ^ 3 + |K₀| ^ 4) * fsXp hv.t (-(2667 / 4)) := by
        rw [show ((2 * |K₀| ^ 3 + |K₀| ^ 4) * fsXp hv.t (-(327 / 4))) * fsXp hv.t (-36)
              * fsXp hv.t (-549)
            = (2 * |K₀| ^ 3 + |K₀| ^ 4)
              * (fsXp hv.t (-(327 / 4)) * fsXp hv.t (-36) * fsXp hv.t (-549)) by ring]
        rw [hcomb]

theorem OpZ_RE1 (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F)
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseC3QAll.Q3KernelFSAll K₀ F T E →
          262144 * K₀ ^ 3 * (E.Kl * E.KL) ^ 3 * E.KH ^ 4 * E.aScat ^ 6
              * (E.z / E.ell ^ 3) ^ 2 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3)
            ≤ E.lille ^ 2 / 8 := by
  set C : ℝ := 2 * |K₀| ^ 3 + |K₀| ^ 4 with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  set D : ℝ := 3145728 * C with hDdef
  have hDnn : 0 ≤ D := by rw [hDdef]; positivity
  have hD1 : 0 < D + 1 := by linarith
  set τ : ℝ := (1 / (D + 1)) ^ (4 / 193 : ℝ) with hτdef
  have hτpos : 0 < τ := by
    rw [hτdef]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hτ193 : τ ^ (193 / 4 : ℝ) = 1 / (D + 1) := by
    rw [hτdef, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / (D + 1))]
    rw [show (4 / 193 : ℝ) * (193 / 4) = 1 by norm_num, Real.rpow_one]
  refine ⟨τ ^ 323, by positivity, ?_⟩
  intro Mode _ _ _ F T E hv htle _hb _hK
  have ht : 0 < hv.t := hv.t_pos
  have hXpos : 0 < fsXp hv.t 1 := fsXp_pos ht
  have hXle : fsXp hv.t 1 ≤ τ := by
    have h := fsXp_le_of_pow_le ht hτpos htle (p := 1) (by norm_num)
    rwa [Real.rpow_one] at h
  have hX193 : fsXp hv.t (193 / 4) ≤ 1 / (D + 1) := by
    have h1 : fsXp hv.t (193 / 4) = (fsXp hv.t 1) ^ (193 / 4 : ℝ) := by
      rw [fsXp_rpow ht.le, one_mul]
    rw [h1, ← hτ193]
    exact Real.rpow_le_rpow hXpos.le hXle (by norm_num)
  have hthr : D * fsXp hv.t (193 / 4) ≤ 1 := by
    have h2 : D * fsXp hv.t (193 / 4) ≤ D * (1 / (D + 1)) :=
      mul_le_mul_of_nonneg_left hX193 hDnn
    have h3 : D * (1 / (D + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one hD1]
      linarith
    linarith [h2, h3]
  have hthreshold : 393216 * C * fsXp hv.t (581 / 4) ≤ fsXp hv.t 97 / 8 := by
    have h581 : fsXp hv.t (193 / 4) * fsXp hv.t 97 = fsXp hv.t (581 / 4) := by
      rw [fsXp_mul ht]
      congr 1
      norm_num
    have hDrel : D = 8 * (393216 * C) := by
      rw [hDdef]
      ring
    have h2 : 393216 * C * fsXp hv.t (193 / 4) ≤ 1 / 8 := by
      have h3 : 8 * (393216 * C * fsXp hv.t (193 / 4)) ≤ 1 := by
        have h4 : 8 * (393216 * C * fsXp hv.t (193 / 4)) = D * fsXp hv.t (193 / 4) := by
          rw [hDrel]
          ring
        rw [h4]
        exact hthr
      linarith [h3]
    have h5 : 0 ≤ fsXp hv.t 97 := fsXp_nonneg ht.le
    rw [← h581]
    calc 393216 * C * (fsXp hv.t (193 / 4) * fsXp hv.t 97)
        = (393216 * C * fsXp hv.t (193 / 4)) * fsXp hv.t 97 := by ring
      _ ≤ (1 / 8) * fsXp hv.t 97 := mul_le_mul_of_nonneg_right h2 h5
      _ = fsXp hv.t 97 / 8 := by ring
  have hA := OpZ_RE1_aux_a E hv
  have hB : K₀ ^ 3 * (E.Kl * E.KL) ^ 3 * E.KH ^ 4 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3)
      ≤ C * fsXp hv.t (-(2667 / 4)) := by
    rw [hCdef]
    exact OpZ_RE1_aux_b K₀ E hv
  have hSnn : 0 ≤ E.aScat ^ 6 * (E.z / E.ell ^ 3) ^ 2 := by positivity
  have hCxnn : 0 ≤ C * fsXp hv.t (-(2667 / 4)) :=
    mul_nonneg hCnn (fsXp_nonneg ht.le)
  have hcomb : fsXp hv.t (-(2667 / 4)) * fsXp hv.t 812 = fsXp hv.t (581 / 4) := by
    rw [fsXp_mul ht]
    congr 1
    norm_num
  have hlille : E.lille ^ 2 / 8 = fsXp hv.t 97 / 8 := by
    rw [lille_val E hv, fsXp_pow ht.le]
    norm_num
  calc 262144 * K₀ ^ 3 * (E.Kl * E.KL) ^ 3 * E.KH ^ 4 * E.aScat ^ 6
          * (E.z / E.ell ^ 3) ^ 2 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3)
      = 262144 * (K₀ ^ 3 * (E.Kl * E.KL) ^ 3 * E.KH ^ 4
          * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3))
          * (E.aScat ^ 6 * (E.z / E.ell ^ 3) ^ 2) := by ring
    _ ≤ 262144 * (C * fsXp hv.t (-(2667 / 4))) * ((3 / 2) * fsXp hv.t 812) := by
        have h1 : K₀ ^ 3 * (E.Kl * E.KL) ^ 3 * E.KH ^ 4
              * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3)
              * (E.aScat ^ 6 * (E.z / E.ell ^ 3) ^ 2)
            ≤ (C * fsXp hv.t (-(2667 / 4))) * ((3 / 2) * fsXp hv.t 812) :=
          mul_le_mul hB hA hSnn hCxnn
        calc 262144 * (K₀ ^ 3 * (E.Kl * E.KL) ^ 3 * E.KH ^ 4
                * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3))
                * (E.aScat ^ 6 * (E.z / E.ell ^ 3) ^ 2)
            = 262144 * (K₀ ^ 3 * (E.Kl * E.KL) ^ 3 * E.KH ^ 4
                * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3)
                * (E.aScat ^ 6 * (E.z / E.ell ^ 3) ^ 2)) := by ring
          _ ≤ 262144 * ((C * fsXp hv.t (-(2667 / 4))) * ((3 / 2) * fsXp hv.t 812)) :=
              mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 262144)
          _ = 262144 * (C * fsXp hv.t (-(2667 / 4))) * ((3 / 2) * fsXp hv.t 812) := by ring
    _ = 393216 * C * fsXp hv.t (581 / 4) := by
        rw [← hcomb]
        ring
    _ ≤ fsXp hv.t 97 / 8 := hthreshold
    _ = E.lille ^ 2 / 8 := hlille.symm

end Work.BoseC3QAll.Est1
