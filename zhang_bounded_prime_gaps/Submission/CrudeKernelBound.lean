import Mathlib
import Submission.Commons.NumberTheory.Zeta.eulerCrudeProduct_le_zeta_real

open scoped BigOperators Topology
open Filter Asymptotics

/-!
# Crude kernel bound `|K(ξ)| ≤ C·log³x` (P8 Lemma 4.1) — first layer

The ξ-truncation step (iii) needs the crude bound on the per-coordinate
kernel `K(ξ, ξ′)`: the absolute value of the divisor sum
`Σ_{d,d′} μ(d)μ(d′)/([d,d′]·d^{a}d′^{b})` (`Re a = Re b = 1/log x`) is at
most `Σ |μμ|/([d,d′]·d^{1/log x}d′^{1/log x})`, the Euler product over the
primes of the per-prime factor `1 + 2/p^{1+1/log x} + 1/p^{1+2/log x}`, and
each factor is `≤ (1 − p^{−(1+1/log x)})^{−3}`; hence the product over the
allowed primes `p ∤ q` is `≤ ζ(1 + 1/log x)³`.  This file proves the first
analytic layer of that chain:

  * `zeta_bound_near_one` — the zeta bound `‖ζ(1+η)‖ ≤ C/η` for small
    `0 < η` (`ζ(1+ε) ≪ 1/ε`, from Mathlib's
    `isBigO_riemannZeta_sub_one_div` at `𝓝 1`, i.e. `ζ(s) − 1/(s−1)` is
    bounded near `s = 1`);
  * `riemannZeta_one_add_inv_log_eventually` — its form along the sieve:
    for all large `x`, `‖ζ(1 + (1/log x : ℂ))‖ ≤ C·log x`.

Second layer (this file, below): the per-prime factor inequality
`perPrime_crude_factor_le` (`1 + 2/p^{1+ε} + 1/p^{1+2ε} ≤ ((1−p^{−(1+ε)})⁻¹)³`)
and its finite-product corollary `crudeFactors_product_le`.

Remaining layers (recorded for the next pushes): the Euler-product
comparison `∏_{p∤q}(…) ≤ ζ(1+ε)³` (monotone partial products of the Euler
product, via `riemannZeta_eulerProduct`, relating the real powers to the
complex cpow through `norm_cpow_nat_eq`), and the assembly
`|K(ξ,ξ′)| ≤ C³·log³x` (independent of L14–L16; needed to make the
ξ-integrals outside the truncation cube negligible against the rapid decay
of the Schwartz transforms in `Submission/XiTruncation.lean`).
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The Riemann zeta function is `O(1/η)` at real arguments `1 + η` just
above the pole: `∃ C > 0, δ > 0`, `∀ 0 < η ≤ δ`: `‖ζ(1+η)‖ ≤ C/η`. -/
lemma zeta_bound_near_one :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ η : ℝ, 0 < η → η ≤ δ → ‖riemannZeta (1 + (η : ℂ))‖ ≤ C / η := by
  classical
  have hO := isBigO_riemannZeta_sub_one_div (F := ℝ)
  have hO' : ∃ C : ℝ, ∀ᶠ s : ℂ in 𝓝 1,
      ‖riemannZeta s - 1 / (s - 1)‖ ≤ C * ‖(1 : ℝ)‖ := (Asymptotics.isBigO_iff).mp hO
  rcases hO' with ⟨C, hC⟩
  let C0 : ℝ := max C 0
  have hC0 : ∀ᶠ s : ℂ in 𝓝 1, ‖riemannZeta s - 1 / (s - 1)‖ ≤ C0 := by
    filter_upwards [hC] with s hs
    have hC_le : C ≤ C0 := le_max_left C 0
    have h1nn : (0 : ℝ) ≤ ‖(1 : ℝ)‖ := norm_nonneg (1 : ℝ)
    have hle : C * ‖(1 : ℝ)‖ ≤ C0 * ‖(1 : ℝ)‖ :=
      mul_le_mul_of_nonneg_right hC_le h1nn
    have : C * ‖(1 : ℝ)‖ ≤ C0 := by simpa using hle
    exact hs.trans this
  rcases (Metric.eventually_nhds_iff_ball.mp hC0) with ⟨r, hr0, hr⟩
  let δ : ℝ := min (r / 2) 1
  have hδ0 : 0 < δ := by
    dsimp [δ]
    exact lt_min (by positivity : 0 < r / 2) (by norm_num)
  have hδle1 : δ ≤ 1 := by dsimp [δ]; exact min_le_right (r / 2) 1
  have hδler : δ ≤ r / 2 := by dsimp [δ]; exact min_le_left (r / 2) 1
  refine ⟨C0 + 1, by positivity, δ, hδ0, ?_⟩
  intro η hη hηδ
  have hηr2 : η ≤ r / 2 := le_trans hηδ hδler
  have hηr : η < r := by
    have hr2pos : 0 < r / 2 := by positivity
    exact lt_of_le_of_lt hηr2 (by linarith)
  have hnormη : ‖(η : ℂ)‖ = η := by
    have : ‖(η : ℂ)‖ = |η| := by simp
    rw [this, abs_of_nonneg hη.le]
  have hsball : (1 + (η : ℂ)) ∈ Metric.ball (1 : ℂ) r := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖1 + (η : ℂ) - 1‖ = ‖(η : ℂ)‖ := by simp
      _ = η := hnormη
      _ < r := hηr
  have hb := hr (1 + (η : ℂ)) hsball
  have hmain : ‖riemannZeta (1 + (η : ℂ))‖ ≤ C0 + 1 / η := by
    calc
      ‖riemannZeta (1 + (η : ℂ))‖
          = ‖(riemannZeta (1 + (η : ℂ)) - (1 + (η : ℂ) - 1)⁻¹) + (1 + (η : ℂ) - 1)⁻¹‖ := by
              congr 1
              ring
      _ ≤ ‖riemannZeta (1 + (η : ℂ)) - (1 + (η : ℂ) - 1)⁻¹‖ + ‖(1 + (η : ℂ) - 1)⁻¹‖ :=
              norm_add_le _ _
      _ ≤ C0 + 1 / η := by
              have h1 : ‖riemannZeta (1 + (η : ℂ)) - (1 + (η : ℂ) - 1)⁻¹‖ ≤ C0 := by
                simpa using hb
              have h2 : ‖(1 + (η : ℂ) - 1)⁻¹‖ = 1 / η := by
                have hterm : (1 + (η : ℂ) - 1) = (η : ℂ) := by ring
                rw [hterm]
                have hnormη' : ‖(η : ℂ)⁻¹‖ = 1 / η := by
                  have hnorminv : ‖(η : ℂ)⁻¹‖ = ‖(η : ℂ)‖⁻¹ := by rw [norm_inv]
                  rw [hnorminv, hnormη]
                  field_simp [hη.ne']
                exact hnormη'
              nlinarith
  have hle : C0 + 1 / η ≤ (C0 + 1) / η := by
    have hηle1 : η ≤ 1 := hηδ.trans hδle1
    have hC0nn : 0 ≤ C0 := le_max_right C 0
    rw [le_div_iff₀ hη]
    have hmain' : (C0 + 1 / η) * η = C0 * η + 1 := by
      field_simp [hη.ne']
    rw [hmain']
    nlinarith [hC0nn, hηle1]
  exact le_trans hmain hle

/-- Along the sieve scale: for all large `x : ℕ`,
`‖ζ(1 + (1/log x : ℂ))‖ ≤ C·log x` (the `ζ(1+1/log x) ≪ log x` of the crude
kernel bound). -/
lemma riemannZeta_one_add_inv_log_eventually (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ)
    (hb : ∀ η : ℝ, 0 < η → η ≤ δ → ‖riemannZeta (1 + (η : ℂ))‖ ≤ C / η) :
    ∀ᶠ x : ℕ in atTop,
      ‖riemannZeta (1 + ((1 / Real.log (x : ℝ)) : ℂ))‖ ≤ C * Real.log (x : ℝ) := by
  filter_upwards [eventually_gt_atTop (Nat.ceil (Real.exp (1 / δ)) + 1)] with x hx
  have hxexp : Real.exp (1 / δ) < (x : ℝ) := by
    have h1 : Real.exp (1 / δ) < ((Nat.ceil (Real.exp (1 / δ)) + 1 : ℕ) : ℝ) := by
      have h1' : Real.exp (1 / δ) ≤ (Nat.ceil (Real.exp (1 / δ)) : ℕ) := Nat.le_ceil (Real.exp (1 / δ))
      have h2 : ((Nat.ceil (Real.exp (1 / δ)) : ℕ) : ℝ) <
          ((Nat.ceil (Real.exp (1 / δ)) + 1 : ℕ) : ℝ) := by norm_num
      exact h1'.trans_lt h2
    have hle : ((Nat.ceil (Real.exp (1 / δ)) + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast (le_of_lt hx)
    exact h1.trans_le hle
  have hlogx : 0 < Real.log (x : ℝ) := by
    have hE : (1 : ℝ) < Real.exp (1 / δ) := by
      have hinc := Real.exp_lt_exp.mpr (by positivity : 0 < 1 / δ)
      simpa using hinc
    exact Real.log_pos (by linarith)
  have hε : 0 < 1 / Real.log (x : ℝ) := by positivity
  have hlogbig : 1 / δ < Real.log (x : ℝ) := by
    have hm := Real.log_lt_log (Real.exp_pos (1 / δ)) hxexp
    simpa [Real.log_exp] using hm
  have hεδ : 1 / Real.log (x : ℝ) ≤ δ := by
    rw [div_le_iff₀ hlogx]
    have hmul : (1 / δ) * δ < Real.log (x : ℝ) * δ := mul_lt_mul_of_pos_right hlogbig hδ
    have hleft : (1 / δ) * δ = 1 := by field_simp [hδ.ne']
    have hlt : (1 : ℝ) < Real.log (x : ℝ) * δ := by
      rw [← hleft]
      exact hmul
    nlinarith
  have hb' := hb (1 / Real.log (x : ℝ)) hε hεδ
  have hval : C / (1 / Real.log (x : ℝ)) = C * Real.log (x : ℝ) := by
    field_simp [hlogx.ne']
  simpa [hval] using hb'


/-- **Per-prime factor inequality (P8 crude kernel bound).**  For a prime
`p ≥ 2` and `ε ≥ 0` (`ε = 1/log x` in the application), the per-prime
absolute contribution of the kernel factor
`1 + 2/p^{1+ε} + 1/p^{1+2ε}` is at most `(1 − p^{−(1+ε)})^{−3}`:

    1 + 2·p^{−(1+ε)} + p^{−(1+2ε)} ≤ ((1 − p^{−(1+ε)})⁻¹)³ .

Proof: with `u := p^{−(1+ε)}` and `v := p^{−(1+2ε)} ≤ u`, the LHS is
`≤ 1 + 3u ≤ (1+u)³ ≤ ((1−u)⁻¹)³` (the last since `(1+u)(1−u) = 1−u² ≤ 1`
and `0 < 1−u`). -/
lemma perPrime_crude_factor_le (p : ℕ) (hp2 : 2 ≤ p) (ε : ℝ) (hε : 0 ≤ ε) :
    1 + 2 * (p : ℝ) ^ (-(1 + ε)) + (p : ℝ) ^ (-(1 + 2 * ε)) ≤
      ((1 - (p : ℝ) ^ (-(1 + ε)))⁻¹) ^ 3 := by
  let u : ℝ := (p : ℝ) ^ (-(1 + ε))
  let v : ℝ := (p : ℝ) ^ (-(1 + 2 * ε))
  have hp1r : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hpr : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hu0 : 0 < u := by dsimp [u]; exact Real.rpow_pos_of_pos hpr _
  have hv0 : 0 < v := by dsimp [v]; exact Real.rpow_pos_of_pos hpr _
  have hle1 : -(1 + 2 * ε) ≤ -(1 + ε) := by linarith
  have hvu : v ≤ u := by
    dsimp [u, v]
    exact Real.rpow_le_rpow_of_exponent_le hp1r hle1
  have hle2 : -(1 + ε) ≤ -(1 : ℝ) := by linarith
  have hu_le_pinv : u ≤ (p : ℝ) ^ (-(1 : ℝ)) := by
    dsimp [u]
    exact Real.rpow_le_rpow_of_exponent_le hp1r hle2
  have hpinv_le : (p : ℝ) ^ (-(1 : ℝ)) ≤ 1 / 2 := by
    have hp2r : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    rw [Real.rpow_neg (by positivity : 0 ≤ (p : ℝ)) (1 : ℝ)]
    rw [Real.rpow_one]
    rw [one_div]
    exact (inv_le_inv₀ (by positivity : 0 < (p : ℝ)) (by norm_num)).mpr hp2r
  have hu12 : u ≤ 1 / 2 := hu_le_pinv.trans hpinv_le
  have hu1 : u < 1 := lt_of_le_of_lt hu12 (by norm_num)
  have hu_nonneg : 0 ≤ u := hu0.le
  have h13 : (1 : ℝ) + 3 * u ≤ (1 + u) ^ 3 := by
    nlinarith [hu_nonneg, sq_nonneg u, mul_nonneg (sq_nonneg u) hu_nonneg]
  have h1u : (1 : ℝ) + u ≤ (1 - u)⁻¹ := by
    have hpos : 0 < 1 - u := by linarith
    rw [← one_div]
    rw [le_div_iff₀ hpos]
    nlinarith [sq_nonneg u]
  have hpowmono : (1 + u) ^ 3 ≤ ((1 - u)⁻¹) ^ 3 := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ 1 + u) h1u 3
  change 1 + 2 * u + v ≤ ((1 - u)⁻¹) ^ 3
  calc
    1 + 2 * u + v ≤ 1 + 3 * u := by nlinarith [hvu]
    _ ≤ (1 + u) ^ 3 := h13
    _ ≤ ((1 - u)⁻¹) ^ 3 := hpowmono

/-- A product of cubes is the cube of the product. -/
lemma prod_pow_three (S : Finset ℕ) (f : ℕ → ℝ) :
    (∏ p ∈ S, (f p) ^ 3) = (∏ p ∈ S, f p) ^ 3 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ih]
      ring_nf

/-- **Finite-product corollary.**  Over any finite set of naturals `p ≥ 2`,
`∏_p (1 + 2/p^{1+ε} + 1/p^{1+2ε}) ≤ (∏_p (1 − p^{−(1+ε)})⁻¹)³`. -/
lemma crudeFactors_product_le (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) (ε : ℝ)
    (hε : 0 ≤ ε) :
    (∏ p ∈ S, (1 + 2 * (p : ℝ) ^ (-(1 + ε)) + (p : ℝ) ^ (-(1 + 2 * ε)))) ≤
      (∏ p ∈ S, ((1 - (p : ℝ) ^ (-(1 + ε)))⁻¹)) ^ 3 := by
  classical
  have h1 : (∏ p ∈ S, (1 + 2 * (p : ℝ) ^ (-(1 + ε)) + (p : ℝ) ^ (-(1 + 2 * ε)))) ≤
      ∏ p ∈ S, (((1 - (p : ℝ) ^ (-(1 + ε)))⁻¹) ^ 3) := by
    refine Finset.prod_le_prod₀ ?_ ?_
    · intro p hp
      positivity
    · intro p hp
      exact perPrime_crude_factor_le p (hS p hp) ε hε
  have h2 : (∏ p ∈ S, (((1 - (p : ℝ) ^ (-(1 + ε)))⁻¹) ^ 3)) =
      (∏ p ∈ S, ((1 - (p : ℝ) ^ (-(1 + ε)))⁻¹)) ^ 3 :=
    prod_pow_three S (fun p : ℕ => (1 - (p : ℝ) ^ (-(1 + ε)))⁻¹)
  rw [h2] at h1
  exact h1


/-- **Crude kernel bound in sieve (log-x) form** — the "ζ(1+ε) ≪ 1/ε"
layer of input (b) of the ξ-truncation: with `ε(x) := 1/log x`, for all
sufficiently large `x` and EVERY `n`, the finite product over the primes
`p < n` with `p ∤ q` of the per-prime absolute factor
`1 + 2/p^{1+1/log x} + 1/p^{1+2/log x}` is `≤ C·log³x`.

Assembly: specialize the commons Euler-product comparison
`Commons.NumberTheory.Zeta.eulerCrudeProduct_le_zeta_real`
(`∏_{p<n,p∤q}(1+2/p^{1+ε}+1/p^{1+2ε}) ≤ ‖ζ((1+ε:ℝ):ℂ)‖³`) to
`ε := 1/log x`, identify the zeta argument `(1+ε : ℝ) : ℂ` with
`1 + (ε : ℂ)`, and bound `‖ζ(1+ε)‖³ ≤ (C₀·log x)³` by
`zeta_bound_near_one` via `riemannZeta_one_add_inv_log_eventually`
(`ζ(1+1/log x) ≤ C₀·log x` eventually); `(C₀·log x)³ = C₀³·log³x`. -/
lemma crudeProductLogBound_eventually (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, ∀ n : ℕ,
      (∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
          (1 + 2 * (p : ℝ) ^ (-(1 + (1 / Real.log (x : ℝ)))) +
            (p : ℝ) ^ (-(1 + 2 * (1 / Real.log (x : ℝ)))))) ≤
        C * (Real.log (x : ℝ)) ^ 3 := by
  classical
  rcases zeta_bound_near_one with ⟨C0, hC0, δ, hδ, hb⟩
  have hζev := riemannZeta_one_add_inv_log_eventually C0 δ hC0 hδ hb
  have hloggt : ∀ᶠ x : ℕ in atTop, (1 : ℝ) < Real.log (x : ℝ) := by
    filter_upwards [eventually_gt_atTop (Nat.ceil (Real.exp 1) + 1)] with x hx
    have hxexp : Real.exp 1 < (x : ℝ) := by
      have h1 : Real.exp 1 < ((Nat.ceil (Real.exp 1) + 1 : ℕ) : ℝ) := by
        have h1' : Real.exp 1 ≤ (Nat.ceil (Real.exp 1) : ℕ) := Nat.le_ceil (Real.exp 1)
        have h2 : ((Nat.ceil (Real.exp 1) : ℕ) : ℝ) < ((Nat.ceil (Real.exp 1) + 1 : ℕ) : ℝ) := by norm_num
        exact h1'.trans_lt h2
      have hle : ((Nat.ceil (Real.exp 1) + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by
        exact_mod_cast (le_of_lt hx)
      exact h1.trans_le hle
    have hm := Real.log_lt_log (Real.exp_pos 1) hxexp
    simpa [Real.log_exp] using hm
  refine ⟨C0 ^ 3, pow_pos hC0 3, ?_⟩
  filter_upwards [hζev, hloggt] with x hζx hlog1
  have hlogx0 : 0 < Real.log (x : ℝ) := by linarith
  have hε : 0 < 1 / Real.log (x : ℝ) := by positivity
  intro n
  have hL := Commons.NumberTheory.Zeta.eulerCrudeProduct_le_zeta_real q (1 / Real.log (x : ℝ)) hε n
  have harg : riemannZeta ((1 + (1 / Real.log (x : ℝ)) : ℝ) : ℂ) =
      riemannZeta (1 + ((1 / Real.log (x : ℝ)) : ℂ)) := by
    congr 1
    simp
  have hnorm_eq : ‖riemannZeta ((1 + (1 / Real.log (x : ℝ)) : ℝ) : ℂ)‖ =
      ‖riemannZeta (1 + ((1 / Real.log (x : ℝ)) : ℂ))‖ := by rw [harg]
  have hcube : ‖riemannZeta (1 + ((1 / Real.log (x : ℝ)) : ℂ))‖ ^ 3 ≤
      (C0 * Real.log (x : ℝ)) ^ 3 := by
    have h01 : 0 ≤ ‖riemannZeta (1 + ((1 / Real.log (x : ℝ)) : ℂ))‖ := norm_nonneg _
    have h02 : 0 ≤ C0 * Real.log (x : ℝ) := mul_nonneg (le_of_lt hC0) (le_of_lt hlogx0)
    exact pow_le_pow_left₀ h01 hζx 3
  have hmain : (∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
        (1 + 2 * (p : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) +
          (p : ℝ) ^ (-(1 + 2 * (1 / Real.log (x : ℝ)))))) ≤
      (C0 * Real.log (x : ℝ)) ^ 3 := by
    calc
      (∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
          (1 + 2 * (p : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) +
            (p : ℝ) ^ (-(1 + 2 * (1 / Real.log (x : ℝ)))))) ≤
          ‖riemannZeta ((1 + (1 / Real.log (x : ℝ)) : ℝ) : ℂ)‖ ^ 3 := by
            simpa [harg] using hL
      _ ≤ (C0 * Real.log (x : ℝ)) ^ 3 := by
            simpa [hnorm_eq] using hcube
  have hring : (C0 * Real.log (x : ℝ)) ^ 3 = C0 ^ 3 * (Real.log (x : ℝ)) ^ 3 := by ring
  rwa [← hring]

/-- **Crude kernel bound, uniform in the excluded modulus.**  The same bound as
`crudeProductLogBound_eventually`, but with the constant independent of `q`
(this is what the family-form truncation needs: `q = W x · N x` varies with `x`).
The proof is identical, with `q` quantified inside the eventual statement. -/
lemma crudeProductLogBound_eventually_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, ∀ (q n : ℕ),
      (∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
          (1 + 2 * (p : ℝ) ^ (-(1 + (1 / Real.log (x : ℝ)))) +
            (p : ℝ) ^ (-(1 + 2 * (1 / Real.log (x : ℝ)))))) ≤
        C * (Real.log (x : ℝ)) ^ 3 := by
  classical
  rcases zeta_bound_near_one with ⟨C0, hC0, δ, hδ, hb⟩
  have hζev := riemannZeta_one_add_inv_log_eventually C0 δ hC0 hδ hb
  have hloggt : ∀ᶠ x : ℕ in atTop, (1 : ℝ) < Real.log (x : ℝ) := by
    filter_upwards [eventually_gt_atTop (Nat.ceil (Real.exp 1) + 1)] with x hx
    have hxexp : Real.exp 1 < (x : ℝ) := by
      have h1 : Real.exp 1 < ((Nat.ceil (Real.exp 1) + 1 : ℕ) : ℝ) := by
        have h1' : Real.exp 1 ≤ (Nat.ceil (Real.exp 1) : ℕ) := Nat.le_ceil (Real.exp 1)
        have h2 : ((Nat.ceil (Real.exp 1) : ℕ) : ℝ) < ((Nat.ceil (Real.exp 1) + 1 : ℕ) : ℝ) := by norm_num
        exact h1'.trans_lt h2
      have hle : ((Nat.ceil (Real.exp 1) + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by
        exact_mod_cast (le_of_lt hx)
      exact h1.trans_le hle
    have hm := Real.log_lt_log (Real.exp_pos 1) hxexp
    simpa [Real.log_exp] using hm
  refine ⟨C0 ^ 3, pow_pos hC0 3, ?_⟩
  filter_upwards [hζev, hloggt] with x hζx hlog1
  have hlogx0 : 0 < Real.log (x : ℝ) := by linarith
  have hε : 0 < 1 / Real.log (x : ℝ) := by positivity
  intro q n
  have hL := Commons.NumberTheory.Zeta.eulerCrudeProduct_le_zeta_real q (1 / Real.log (x : ℝ)) hε n
  have harg : riemannZeta ((1 + (1 / Real.log (x : ℝ)) : ℝ) : ℂ) =
      riemannZeta (1 + ((1 / Real.log (x : ℝ)) : ℂ)) := by
    congr 1
    simp
  have hnorm_eq : ‖riemannZeta ((1 + (1 / Real.log (x : ℝ)) : ℝ) : ℂ)‖ =
      ‖riemannZeta (1 + ((1 / Real.log (x : ℝ)) : ℂ))‖ := by rw [harg]
  have hcube : ‖riemannZeta (1 + ((1 / Real.log (x : ℝ)) : ℂ))‖ ^ 3 ≤
      (C0 * Real.log (x : ℝ)) ^ 3 := by
    have h01 : 0 ≤ ‖riemannZeta (1 + ((1 / Real.log (x : ℝ)) : ℂ))‖ := norm_nonneg _
    have h02 : 0 ≤ C0 * Real.log (x : ℝ) := mul_nonneg (le_of_lt hC0) (le_of_lt hlogx0)
    exact pow_le_pow_left₀ h01 hζx 3
  have hmain : (∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
        (1 + 2 * (p : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) +
          (p : ℝ) ^ (-(1 + 2 * (1 / Real.log (x : ℝ)))))) ≤
      (C0 * Real.log (x : ℝ)) ^ 3 := by
    calc
      (∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
          (1 + 2 * (p : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) +
            (p : ℝ) ^ (-(1 + 2 * (1 / Real.log (x : ℝ)))))) ≤
          ‖riemannZeta ((1 + (1 / Real.log (x : ℝ)) : ℝ) : ℂ)‖ ^ 3 := by
            simpa [harg] using hL
      _ ≤ (C0 * Real.log (x : ℝ)) ^ 3 := by
            simpa [hnorm_eq] using hcube
  have hring : (C0 * Real.log (x : ℝ)) ^ 3 = C0 ^ 3 * (Real.log (x : ℝ)) ^ 3 := by ring
  rwa [← hring]
