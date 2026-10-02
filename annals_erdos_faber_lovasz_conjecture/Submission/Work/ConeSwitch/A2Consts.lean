import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.S12Faithful.Data

/-!
# The A₂ parameters exist once the colouring parameters are given (faithful route (3))

*(`Work.ConeSwitch` copy of `Submission/Work/S12Faithful/exists_A2_given_gamma.lean`.)*
The only change is that the hypothesis `1/10^26 ≤ ρ` (which that file needs only in order to
derive `0 < ρ`) is replaced by `0 < ρ`, so that the lemma applies to the *tiny* A₂ densities
`ρ = σ/2` of §12 (where `σ ≤ 10⁻²⁴` has no lower bound).  Everything else — the private
arithmetic lemmas and the proof — is verbatim.

`Work.S12Faithful.exists_A2_given_gamma` is the "given `γ, β, r₁, r₀`" version of
`Work.S12Faithful.exists_S12A2Small`: the colouring parameters of Theorem 6.7 come
from the Large Edge Theorem and are therefore fixed by the caller *before* the
fullness parameter `ε` is chosen, so only `ε, ζ, η, ηr` can be produced here.

The proof is pure arithmetic.  With

`M := min (min (ε₀²/16) (ε₀/2·10⁶)) (min (η₀/22) (min (ρ²/20) (ρ/80)))`,

the hypothesis `hsmall₀` says `4·10⁶·√γ/ρ ≤ M`.  We take

* `ε := M`,
* `η := 22ε`,
* `ηr := max (√ε) (max (2·10⁵·ε) (4√(15√γ)))`,
* `ζ := ηr/(1 - 10⁻⁴)`.

Then `√γ ≤ ρε₀²/(64·10⁶)` follows from `ε ≤ ε₀²/16`, which gives
`4√(15√γ) ≤ ε₀(1-10⁻⁴)`; together with `√ε ≤ ε₀/4` and `2·10⁵ε ≤ ε₀/10` this
yields `ζ ≤ ε₀`.  The remaining fields of `S12A2Small` are monomial comparisons,
each of which follows from `4·10⁶√γ/ρ ≤ ε` and the five upper bounds on `ε`
coming from `ε ≤ M ≤ …`.  The only field that uses the colouring parameters is
`h8r₀ : 8 ≤ ρεr₀`: from `32 ≤ βr₁ ≤ β²(r₀-1)` and `β ≤ γ⁴/10¹²` we get
`r₀ - 1 ≥ 32·10²⁴/γ⁸`, hence `√γ·r₀ ≥ √γ·32·10²⁴/γ⁸ ≥ 32·10²⁴` (because
`γ ^ 8 ≤ γ ≤ √γ`), so `ρεr₀ ≥ 4·10⁶·√γ·r₀ ≥ 1.28·10³²`.

Every arithmetic step is factored into a small top-level `private` lemma so that
`linarith`/`nlinarith` never see the (very long) list of local hypotheses of the
main proof; each of them is invoked with the `only` modifier.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ConeSwitch

open ErdosFaberLovaszConjecture

/-! ### Elementary monotonicity facts about `√γ` -/

private lemma sqrt_gamma_le_one {γ : ℝ} (hγ1 : γ ≤ 1) : Real.sqrt γ ≤ 1 := by
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt hγ1

private lemma gamma_le_sqrt_gamma {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) : γ ≤ Real.sqrt γ := by
  have h := Real.sq_sqrt hγ0.le
  have h1 : Real.sqrt γ ≤ 1 := sqrt_gamma_le_one hγ1
  nlinarith only [h, h1, Real.sqrt_nonneg γ]

private lemma pow_eight_gamma_le {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) : γ ^ 8 ≤ γ := by
  have h := pow_le_pow_of_le_one hγ0.le hγ1 (show 1 ≤ 8 by norm_num)
  simpa using h

/-! ### The elementary lower bound for the master constant -/

private lemma div_c_ge {ρ γ : ℝ} (hρ0 : 0 < ρ) (hρ100 : ρ ≤ 1 / 100) :
    4 * 10 ^ 6 * Real.sqrt γ ≤ 4 * 10 ^ 6 * Real.sqrt γ / ρ := by
  rw [le_div_iff₀ hρ0]
  nlinarith only [Real.sqrt_nonneg γ, hρ100]

/-! ### The upper bounds on `ε` and their consequences -/

private lemma eps_le_200000 {ρ eps : ℝ} (hρ0 : 0 < ρ) (hρ100 : ρ ≤ 1 / 100)
    (h : eps ≤ ρ ^ 2 / 20) : eps ≤ 1 / 200000 := by
  have h1 : ρ ^ 2 ≤ (1 / 100) ^ 2 := pow_le_pow_left₀ hρ0.le hρ100 2
  nlinarith only [h, h1]

private lemma sqrt_eps_le_sixth {eps : ℝ} (h : eps ≤ 1 / 200000) : Real.sqrt eps ≤ 1 / 6 := by
  rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1 / 6)]
  nlinarith only [h]

/-! ### The lower bounds on `ε` -/

private lemma gamma_le_two_eps {ρ γ eps : ℝ} (hρ0 : 0 < ρ) (hρ100 : ρ ≤ 1 / 100)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (h : 4 * 10 ^ 6 * Real.sqrt γ / ρ ≤ eps) :
    γ ≤ 2 * eps := by
  have hgs : γ ≤ Real.sqrt γ := gamma_le_sqrt_gamma hγ0 hγ1
  have h2 : 2 * (4 * 10 ^ 6 * Real.sqrt γ / ρ) = 8 * 10 ^ 6 * Real.sqrt γ / ρ := by ring
  have h3 : Real.sqrt γ ≤ 8 * 10 ^ 6 * Real.sqrt γ / ρ := by
    rw [le_div_iff₀ hρ0]; nlinarith only [Real.sqrt_nonneg γ, hρ100]
  linarith only [hgs, h2, h3, h]

private lemma eight_gamma_le_eps {ρ γ eps : ℝ} (hρ0 : 0 < ρ) (hρ100 : ρ ≤ 1 / 100)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (h : 4 * 10 ^ 6 * Real.sqrt γ / ρ ≤ eps) :
    8 * γ ≤ eps := by
  have hgs : γ ≤ Real.sqrt γ := gamma_le_sqrt_gamma hγ0 hγ1
  have h3 : 8 * Real.sqrt γ ≤ 4 * 10 ^ 6 * Real.sqrt γ / ρ := by
    rw [le_div_iff₀ hρ0]; nlinarith only [Real.sqrt_nonneg γ, hρ100]
  linarith only [hgs, h3, h]

private lemma rho_abs_arith {ρ γ eps : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hρ_eps : 4 * 10 ^ 6 * Real.sqrt γ ≤ ρ * eps) :
    1000 * (3 * γ / 2) ≤ (ρ / 2) * eps := by
  have hgs : γ ≤ Real.sqrt γ := gamma_le_sqrt_gamma hγ0 hγ1
  nlinarith only [hρ_eps, hgs, Real.sqrt_nonneg γ]

private lemma sqrt_gamma_lt {ρ γ eps : ℝ} (hρ0 : 0 < ρ) (hρ100 : ρ ≤ 1 / 100) (hγ0 : 0 < γ)
    (h : 4 * 10 ^ 6 * Real.sqrt γ / ρ ≤ eps) : 10 * Real.sqrt γ < 3 * eps := by
  have hc_ge : 4 * 10 ^ 6 * Real.sqrt γ ≤ 4 * 10 ^ 6 * Real.sqrt γ / ρ :=
    div_c_ge hρ0 hρ100
  nlinarith only [hc_ge, h, Real.sqrt_pos.2 hγ0]

private lemma sqrt_gamma_small {ρ γ eps : ℝ}
    (hρ_eps : 4 * 10 ^ 6 * Real.sqrt γ ≤ ρ * eps) :
    10 ^ 4 * Real.sqrt γ ≤ (ρ / 2) * eps := by
  nlinarith only [hρ_eps, Real.sqrt_nonneg γ]

private lemma sixty_sqrt_gamma {ρ γ eps : ℝ}
    (hρ_eps : 4 * 10 ^ 6 * Real.sqrt γ ≤ ρ * eps) : 60 * Real.sqrt γ ≤ ρ * eps := by
  nlinarith only [hρ_eps, Real.sqrt_nonneg γ]

private lemma fifteen_sqrt_gamma_le {ρ γ eps : ℝ} (hρ0 : 0 < ρ) (hρ100 : ρ ≤ 1 / 100)
    (h : 4 * 10 ^ 6 * Real.sqrt γ / ρ ≤ eps) : 15 * Real.sqrt γ ≤ eps := by
  have hc_ge : 4 * 10 ^ 6 * Real.sqrt γ ≤ 4 * 10 ^ 6 * Real.sqrt γ / ρ :=
    div_c_ge hρ0 hρ100
  nlinarith only [hc_ge, h, Real.sqrt_nonneg γ]

/-! ### The three numerical fields involving `ηr`, and `hcardc` -/

private lemma hnum_alpha_arith {ρ eps etaR γ : ℝ} (hρ0 : 0 < ρ)
    (hsqrtε_le_sixth : Real.sqrt eps ≤ 1 / 6)
    (hηrbig : 4 * Real.sqrt (15 * Real.sqrt γ) ≤ etaR) :
    ρ / 2 * (1 - 2 * Real.sqrt eps) ≥
      2 * Real.sqrt (15 * Real.sqrt γ) + (ρ / 3 - etaR) := by
  have hX : 0 ≤ ρ / 6 - ρ * Real.sqrt eps := by
    nlinarith only [hρ0, hsqrtε_le_sixth]
  have hY : 0 ≤ etaR - 2 * Real.sqrt (15 * Real.sqrt γ) := by
    nlinarith only [hηrbig, Real.sqrt_nonneg (15 * Real.sqrt γ)]
  have key : ρ / 2 * (1 - 2 * Real.sqrt eps)
      - (2 * Real.sqrt (15 * Real.sqrt γ) + (ρ / 3 - etaR))
      = (ρ / 6 - ρ * Real.sqrt eps) + (etaR - 2 * Real.sqrt (15 * Real.sqrt γ)) := by ring
  linarith only [hX, hY, key]

private lemma hnum_one_arith {ρ etaR zeta : ℝ} (hρ0 : 0 < ρ)
    (hzetadef : zeta = etaR / (1 - 1 / 10 ^ 4)) :
    ρ / 4 - zeta ≤ ρ / 3 * (1 - 1 / 10 ^ 4) ^ 2 - etaR / (1 - 1 / 10 ^ 4) := by
  have hconst : (1 / 4 : ℝ) ≤ (1 / 3) * (1 - 1 / 10 ^ 4) ^ 2 := by norm_num
  have hρ4le : ρ / 4 ≤ ρ / 3 * (1 - 1 / 10 ^ 4) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hconst hρ0.le
    nlinarith only [h]
  rw [hzetadef]
  linarith only [hρ4le]

private lemma hcardc_arith {eps etaR : ℝ} (heps_pos : 0 < eps) (heps_le_200000 : eps ≤ 1 / 200000)
    (hetaR_ge_B : 2 * 10 ^ 5 * eps ≤ etaR) :
    (1 : ℝ) ≤ (1 + (1 / 10 ^ 4) * etaR) * (1 - 10 * eps) := by
  have hb2 : 0 ≤ 1 - 10 * eps := by nlinarith only [heps_le_200000]
  have hle : 1 + 20 * eps ≤ 1 + (1 / 10 ^ 4) * etaR := by
    have h : 20 * eps ≤ (1 / 10 ^ 4) * etaR := by nlinarith only [hetaR_ge_B]
    linarith only [h]
  have hmono := mul_le_mul_of_nonneg_right hle hb2
  have hbase : (1 : ℝ) ≤ (1 + 20 * eps) * (1 - 10 * eps) := by
    nlinarith only [heps_pos, heps_le_200000]
  linarith only [hmono, hbase]

/-! ### `h8r₀`: the one field that uses the colouring parameters -/

private lemma eight_le_rho_eps_r₀ {ρ γ β eps : ℝ} {r₁ r₀ : ℕ}
    (hβ0 : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hβ4 : β ≤ γ ^ 4 / 10 ^ 12)
    (hβr1 : 32 ≤ β * (r₁ : ℝ)) (hr₁β₀ : (r₁ : ℝ) ≤ β * ((r₀ : ℝ) - 1))
    (hr₀2 : 2 ≤ r₀) (hρ_eps : 4 * 10 ^ 6 * Real.sqrt γ ≤ ρ * eps) :
    (8 : ℝ) ≤ ρ * eps * (r₀ : ℝ) := by
  have hr₀ge1 : (1 : ℝ) ≤ (r₀ : ℝ) := by
    have h : (1 : ℕ) ≤ r₀ := by omega
    exact_mod_cast h
  have hγ_le_sqrtγ : γ ≤ Real.sqrt γ := gamma_le_sqrt_gamma hγ0 hγ1
  have hpowγ : γ ^ 8 ≤ γ := pow_eight_gamma_le hγ0 hγ1
  have hr₁ge : (32 : ℝ) / β ≤ (r₁ : ℝ) := by
    rw [div_le_iff₀ hβ0]; linarith only [hβr1]
  have hstep : (32 : ℝ) / β ≤ β * ((r₀ : ℝ) - 1) := le_trans hr₁ge hr₁β₀
  have h32 : (32 : ℝ) ≤ β ^ 2 * ((r₀ : ℝ) - 1) := by
    have h := (div_le_iff₀ hβ0).mp hstep
    nlinarith only [h]
  have hβ2le : β ^ 2 ≤ (γ ^ 4 / 10 ^ 12) ^ 2 := pow_le_pow_left₀ hβ0.le hβ4 2
  have hβ2le' : β ^ 2 ≤ γ ^ 8 / 10 ^ 24 := by
    have h := hβ2le
    ring_nf at h ⊢
    exact h
  have hr₀m1_nn : 0 ≤ (r₀ : ℝ) - 1 := by linarith only [hr₀ge1]
  have h32' : (32 : ℝ) ≤ (γ ^ 8 / 10 ^ 24) * ((r₀ : ℝ) - 1) := by
    have h := mul_le_mul_of_nonneg_right hβ2le' hr₀m1_nn
    linarith only [h32, h]
  have hK_le : (32 : ℝ) * 10 ^ 24 / γ ^ 8 ≤ (r₀ : ℝ) - 1 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < γ ^ 8)]
    nlinarith only [h32']
  have hr₀ge : (32 : ℝ) * 10 ^ 24 / γ ^ 8 ≤ (r₀ : ℝ) :=
    le_trans hK_le (by linarith only [hr₀ge1])
  have h1 : (1 : ℝ) ≤ Real.sqrt γ / γ ^ 8 := by
    rw [one_le_div (by positivity : (0 : ℝ) < γ ^ 8)]
    linarith only [hpowγ, hγ_le_sqrtγ]
  have hsqrt_r₀ : (32 : ℝ) * 10 ^ 24 ≤ Real.sqrt γ * (r₀ : ℝ) := by
    have h2 : Real.sqrt γ * ((32 : ℝ) * 10 ^ 24 / γ ^ 8)
        = (32 : ℝ) * 10 ^ 24 * (Real.sqrt γ / γ ^ 8) := by ring
    have h3 : (32 : ℝ) * 10 ^ 24 ≤ (32 : ℝ) * 10 ^ 24 * (Real.sqrt γ / γ ^ 8) := by
      nlinarith only [h1]
    have h4 : Real.sqrt γ * ((32 : ℝ) * 10 ^ 24 / γ ^ 8) ≤ Real.sqrt γ * (r₀ : ℝ) :=
      mul_le_mul_of_nonneg_left hr₀ge (Real.sqrt_nonneg γ)
    linarith only [h2, h3, h4]
  have hA : (4 * 10 ^ 6 : ℝ) * (32 * 10 ^ 24) ≤ 4 * 10 ^ 6 * (Real.sqrt γ * (r₀ : ℝ)) :=
    mul_le_mul_of_nonneg_left hsqrt_r₀ (by norm_num)
  have hB : (4 * 10 ^ 6 : ℝ) * (Real.sqrt γ * (r₀ : ℝ)) ≤ (ρ * eps) * (r₀ : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hρ_eps (Nat.cast_nonneg r₀)
    linarith only [h]
  nlinarith only [hA, hB]

/-! ### `ζ ≤ ε₀` -/

private lemma zeta_le_eps0 {ρ γ eps etaR zeta ε₀ : ℝ} (hρ0 : 0 < ρ) (hρ100 : ρ ≤ 1 / 100)
    (hε₀ : 0 < ε₀)
    (heps_le_1 : eps ≤ ε₀ ^ 2 / 16) (heps_le_2 : eps ≤ ε₀ / (2 * 10 ^ 6))
    (hc_le_eps : 4 * 10 ^ 6 * Real.sqrt γ / ρ ≤ eps)
    (hetaRdef : etaR = max (Real.sqrt eps)
      (max (2 * 10 ^ 5 * eps) (4 * Real.sqrt (15 * Real.sqrt γ))))
    (hzetadef : zeta = etaR / (1 - 1 / 10 ^ 4)) : zeta ≤ ε₀ := by
  have hsqrtγ_bound : Real.sqrt γ ≤ ρ * ε₀ ^ 2 / (64 * 10 ^ 6) := by
    have h2 : 4 * 10 ^ 6 * Real.sqrt γ / ρ ≤ ε₀ ^ 2 / 16 := le_trans hc_le_eps heps_le_1
    have h3 := (div_le_iff₀ hρ0).mp h2
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 64 * 10 ^ 6)]
    nlinarith only [h3]
  have h240 : 240 * Real.sqrt γ ≤ ε₀ ^ 2 * (1 - 1 / 10 ^ 4) ^ 2 := by
    have hconst : (15 : ℝ) / (4 * 10 ^ 8) ≤ (1 - 1 / 10 ^ 4) ^ 2 := by norm_num
    nlinarith only [hsqrtγ_bound, hconst, hρ0, hρ100, hε₀, sq_nonneg ε₀]
  have h240' : 4 * Real.sqrt (15 * Real.sqrt γ) ≤ ε₀ * (1 - 1 / 10 ^ 4) := by
    have heq : Real.sqrt (240 * Real.sqrt γ) = 4 * Real.sqrt (15 * Real.sqrt γ) := by
      have h16 : Real.sqrt (16 : ℝ) = 4 := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
      rw [show (240 : ℝ) * Real.sqrt γ = 16 * (15 * Real.sqrt γ) by ring,
        Real.sqrt_mul (x := 16) (by norm_num : (0 : ℝ) ≤ 16) (15 * Real.sqrt γ), h16]
    have hsq : Real.sqrt (ε₀ ^ 2 * (1 - 1 / 10 ^ 4) ^ 2) = ε₀ * (1 - 1 / 10 ^ 4) := by
      rw [show ε₀ ^ 2 * (1 - 1 / 10 ^ 4) ^ 2 = (ε₀ * (1 - 1 / 10 ^ 4)) ^ 2 by ring,
        Real.sqrt_sq (by nlinarith only [hε₀])]
    rw [← heq]
    calc Real.sqrt (240 * Real.sqrt γ) ≤ Real.sqrt (ε₀ ^ 2 * (1 - 1 / 10 ^ 4) ^ 2) :=
          Real.sqrt_le_sqrt h240
      _ = ε₀ * (1 - 1 / 10 ^ 4) := hsq
  have h1 : Real.sqrt eps ≤ ε₀ * (1 - 1 / 10 ^ 4) := by
    have h : Real.sqrt eps ≤ ε₀ / 4 := by
      rw [Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ ε₀ / 4)]
      nlinarith only [heps_le_1]
    nlinarith only [h, hε₀]
  have hetaR_le : etaR ≤ ε₀ * (1 - 1 / 10 ^ 4) := by
    rw [hetaRdef]
    refine max_le ?_ (max_le ?_ ?_)
    · exact h1
    · nlinarith only [heps_le_2, hε₀]
    · exact h240'
  rw [hzetadef, div_le_iff₀ (by norm_num : (0 : ℝ) < 1 - 1 / 10 ^ 4)]
  exact hetaR_le

/-- **The A₂ parameters `ε, ζ, η, ηr` exist once the colouring parameters are known.**  Same
role as `Work.S12Faithful.exists_S12A2Small`, but with `γ, β, r₁, r₀` *given* (they come from
the Large Edge Theorem of §12) and only `ε, ζ, η, ηr` produced.  `ε₀, η₀` are the thresholds of
the faithful Theorem 10.8 at the fixed density `p = 10⁻²⁵`; the conclusion has `ζ ≤ ε₀`,
`η ≤ η₀` and the bundle `S12A2Small`, which is the hypothesis list of
`Work.S12Faithful.exists_S12A2Data`. -/
theorem exists_A2_params {ρ γ β : ℝ} {r₁ r₀ : ℕ} {ε₀ η₀ : ℝ}
    (hρ0 : 0 < ρ) (hρ100 : ρ ≤ 1 / 100)
    (hε₀ : 0 < ε₀) (hη₀ : 0 < η₀)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hβ0 : 0 < β) (hβγ : β ≤ γ)
    (hβsq : 8 * β ≤ γ ^ 2) (hβ4 : β ≤ γ ^ 4 / 10 ^ 12)
    (hγρs : 10 ^ 6 * (2 * γ) ≤ ρ / 2) (h30 : 30 * Real.sqrt γ ≤ ρ)
    (hr₁2 : 2 ≤ r₁) (hr₀2 : 2 ≤ r₀) (hr₁r₀ : r₁ < r₀)
    (hβr1 : 32 ≤ β * (r₁ : ℝ)) (hr₁β₀ : (r₁ : ℝ) ≤ β * ((r₀ : ℝ) - 1))
    (hr₀big : (r₁ : ℝ) < γ / 4 * ((r₀ : ℝ) - 1))
    (hsmall₀ : 4 * 10 ^ 6 * Real.sqrt γ / ρ ≤
      min (min (ε₀ ^ 2 / 16) (ε₀ / (2 * 10 ^ 6)))
        (min (η₀ / 22) (min (ρ ^ 2 / 20) (ρ / 80)))) :
    ∃ ε ζ η ηr : ℝ, 0 < ε ∧ 0 < ζ ∧ 0 < η ∧ 0 < ηr ∧
      ζ ≤ ε₀ ∧ η ≤ η₀ ∧ S12A2Small β γ ρ ε ζ η ηr r₁ r₀ := by
  have hρ4 : ρ ≤ 1 / 4 := by linarith only [hρ100]
  -- the master constant `M` and the choices `ε, ηr, ζ, η`
  let M : ℝ := min (min (ε₀ ^ 2 / 16) (ε₀ / (2 * 10 ^ 6)))
    (min (η₀ / 22) (min (ρ ^ 2 / 20) (ρ / 80)))
  have hMdef : M = min (min (ε₀ ^ 2 / 16) (ε₀ / (2 * 10 ^ 6)))
      (min (η₀ / 22) (min (ρ ^ 2 / 20) (ρ / 80))) := rfl
  let eps : ℝ := M
  have hepsdef : eps = M := rfl
  have hc_le_eps : 4 * 10 ^ 6 * Real.sqrt γ / ρ ≤ eps := by
    rw [hepsdef, hMdef]; exact hsmall₀
  have hc_pos : 0 < 4 * 10 ^ 6 * Real.sqrt γ / ρ := by
    have h1 : (0 : ℝ) < 4 * 10 ^ 6 := by norm_num
    exact div_pos (mul_pos h1 (Real.sqrt_pos.2 hγ0)) hρ0
  have heps_pos : 0 < eps := lt_of_lt_of_le hc_pos hc_le_eps
  have hρ_eps : 4 * 10 ^ 6 * Real.sqrt γ ≤ ρ * eps := by
    have h := (div_le_iff₀ hρ0).mp hc_le_eps
    linarith only [h]
  have heps_le_1 : eps ≤ ε₀ ^ 2 / 16 := by
    rw [hepsdef, hMdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have heps_le_2 : eps ≤ ε₀ / (2 * 10 ^ 6) := by
    rw [hepsdef, hMdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have heps_le_3 : eps ≤ η₀ / 22 := by
    rw [hepsdef, hMdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have heps_le_4 : eps ≤ ρ ^ 2 / 20 := by
    rw [hepsdef, hMdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have heps_le_5 : eps ≤ ρ / 80 := by
    rw [hepsdef, hMdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have heps_le_200000 : eps ≤ 1 / 200000 := eps_le_200000 hρ0 hρ100 heps_le_4
  let etaR : ℝ := max (Real.sqrt eps)
    (max (2 * 10 ^ 5 * eps) (4 * Real.sqrt (15 * Real.sqrt γ)))
  have hetaRdef : etaR = max (Real.sqrt eps)
      (max (2 * 10 ^ 5 * eps) (4 * Real.sqrt (15 * Real.sqrt γ))) := rfl
  have hetaR_pos : 0 < etaR := by
    rw [hetaRdef]
    exact lt_max_iff.mpr (Or.inl (Real.sqrt_pos.2 heps_pos))
  have hetaR_ge_C : 4 * Real.sqrt (15 * Real.sqrt γ) ≤ etaR := by
    rw [hetaRdef]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hetaR_ge_B : 2 * 10 ^ 5 * eps ≤ etaR := by
    rw [hetaRdef]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hsqrtε : Real.sqrt eps ≤ etaR := by
    rw [hetaRdef]; exact le_max_left _ _
  let zeta : ℝ := etaR / (1 - 1 / 10 ^ 4)
  have hzetadef : zeta = etaR / (1 - 1 / 10 ^ 4) := rfl
  have hzeta_pos : 0 < zeta := by
    rw [hzetadef]; exact div_pos hetaR_pos (by norm_num)
  let eta : ℝ := 22 * eps
  have hetadef : eta = 22 * eps := rfl
  have heta_pos : 0 < eta := by rw [hetadef]; positivity
  -- the fields of `S12A2Small`, each from a private arithmetic lemma
  have hγ2ε : γ ≤ 2 * eps := gamma_le_two_eps hρ0 hρ100 hγ0 hγ1 hc_le_eps
  have hε1000 : 1000 * eps ≤ 1 := by linarith only [heps_le_200000]
  have hε4000 : 4000 * eps ≤ 1 := by linarith only [heps_le_200000]
  have h8γε : 8 * γ ≤ eps := eight_gamma_le_eps hρ0 hρ100 hγ0 hγ1 hc_le_eps
  have hγρabs : 1000 * (3 * γ / 2) ≤ (ρ / 2) * eps := rho_abs_arith hγ0 hγ1 hρ_eps
  have hL5in : 10 * Real.sqrt γ < 3 * eps := sqrt_gamma_lt hρ0 hρ100 hγ0 hc_le_eps
  have hsmall : 10 ^ 4 * Real.sqrt γ ≤ (ρ / 2) * eps := sqrt_gamma_small hρ_eps
  have hη22 : 22 * eps ≤ eta := by rw [hetadef]
  have h15γρε : 60 * Real.sqrt γ ≤ ρ * eps := sixty_sqrt_gamma hρ_eps
  have h15γε : 15 * Real.sqrt γ ≤ eps := fifteen_sqrt_gamma_le hρ0 hρ100 hc_le_eps
  have h20ερ : 20 * eps ≤ ρ / 4 := by linarith only [heps_le_5]
  have h20ε : 20 * eps ≤ ρ ^ 2 := by linarith only [heps_le_4]
  have h15ερ : 15 * eps ≤ ρ := by linarith only [heps_le_5, hρ0]
  have hsqrtε_le_sixth : Real.sqrt eps ≤ 1 / 6 := sqrt_eps_le_sixth heps_le_200000
  have hnumα0 : ρ / 2 * (1 - 2 * Real.sqrt eps) ≥
      2 * Real.sqrt (15 * Real.sqrt γ) + (ρ / 3 - etaR) :=
    hnum_alpha_arith hρ0 hsqrtε_le_sixth hetaR_ge_C
  have hnum1 : ρ / 4 - zeta ≤ ρ / 3 * (1 - 1 / 10 ^ 4) ^ 2 - etaR / (1 - 1 / 10 ^ 4) :=
    hnum_one_arith hρ0 hzetadef
  have hnum2 : etaR / (1 - 1 / 10 ^ 4) ≤ zeta := by rw [hzetadef]
  have hcardc : (1 : ℝ) ≤ (1 + (1 / 10 ^ 4) * etaR) * (1 - 10 * eps) :=
    hcardc_arith heps_pos heps_le_200000 hetaR_ge_B
  have h8r₀ : (8 : ℝ) ≤ ρ * eps * (r₀ : ℝ) :=
    eight_le_rho_eps_r₀ hβ0 hγ0 hγ1 hβ4 hβr1 hr₁β₀ hr₀2 hρ_eps
  have hζε₀ : zeta ≤ ε₀ :=
    zeta_le_eps0 hρ0 hρ100 hε₀ heps_le_1 heps_le_2 hc_le_eps hetaRdef hzetadef
  have hηη₀ : eta ≤ η₀ := by rw [hetadef]; linarith only [heps_le_3]
  refine ⟨eps, zeta, eta, etaR, heps_pos, hzeta_pos, heta_pos, hetaR_pos, hζε₀, hηη₀, ?_⟩
  exact
    { hβ0 := hβ0
      hγ0 := hγ0
      hρ0 := hρ0
      hε0 := heps_pos
      hζ0 := hzeta_pos
      hη0 := heta_pos
      hηr0 := hetaR_pos
      hr₁2 := hr₁2
      hr₀2 := hr₀2
      hr₁r₀ := hr₁r₀
      hρ4 := hρ4
      hρ100 := hρ100
      hγ1 := hγ1
      hβγ := hβγ
      hβsq := hβsq
      hβ4 := hβ4
      hγρs := hγρs
      hγ2ε := hγ2ε
      hε1000 := hε1000
      hε4000 := hε4000
      h8γε := h8γε
      hγρabs := hγρabs
      hβr1 := hβr1
      hr₁β₀ := hr₁β₀
      hr₀big := hr₀big
      hL5in := hL5in
      hsmall := hsmall
      hη22 := hη22
      h15γρε := h15γρε
      h15γε := h15γε
      h20ερ := h20ερ
      h30 := h30
      h8r₀ := h8r₀
      h20ε := h20ε
      h15ερ := h15ερ
      hηrbig := hetaR_ge_C
      hsqrtε := hsqrtε
      hnumα0 := hnumα0
      hnum1 := hnum1
      hnum2 := hnum2
      hcardc := hcardc }

end Work.ConeSwitch
