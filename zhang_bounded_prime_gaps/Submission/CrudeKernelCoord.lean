import Mathlib
import Submission.FiniteEuler
import Submission.CrudeKernelBound
import Submission.ZetaWNBounds

open scoped BigOperators Topology
open Filter

set_option linter.unusedVariables false

/-!
# Crude kernel bound `|K| ≤ C·log^{3k} x` (P8 Lemma 4.1, input (b) of the truncation)

The ξ-truncation step of Polymath8a's Lemma 4.1 needs the crude bound on the
`k`-coordinate kernel

    K(ξ, ξ′) = ∏_{p ∤ WN} K_p(ξ, ξ′) ,     |K| ≪ log^{3k} x ,

uniformly in all Fourier variables (P8, p. 19: "Thus `K(ξ_1, …) = O(log^{3k} x)`").
Each local factor (`coordLocal` of `Submission.FiniteEuler` at the concrete
weights `x_{jp} = p^{−a_j}`, `y_{jp} = p^{−b_j}`, `z_{jp} = p^{−1}`, and with
`Re a_j = Re b_j = 1/log x` for the sieve's points `a_j = (1+iξ_j)/log x`)

    K_p = 1 + Σ_j (−p^{−1−a_j} − p^{−1−b_j} + p^{−1−a_j−b_j})

satisfies `|K_p| ≤ 1 + 2p^{−1−1/L} + p^{−1−2/L}` with `L := log x` (P8 p. 18,
the displayed `1 + 2/p^{1+1/log x} + 1/p^{1+2/log x}`), and by the Euler-product
comparison `∏_{p∤q}(1 + 2p^{−1−1/L} + p^{−1−2/L}) ≤ ζ(1+1/L)³ ≪ log³x`
(`Submission.CrudeKernelBound`) the full product over `p ∤ q` is `≪ log^{3k}x`,
uniformly in the truncation window and in all `ξ_j, ξ'_j`.

Contents (all kernel-verified, no `sorry`):

  * `coordLocalK` — the concrete `k`-coordinate local factor of P8 (39);
  * `coordLocalK_eq` — its standard form with the merged `cpow` exponents;
  * `coordLocalK_norm_le` — the per-prime crude bound;
  * `coordProduct_norm_le` — the product bound over a finite prime window;
  * `crudeKernelCoord_eventually` — the final `≪ log^{3k}x` form.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The concrete `k`-coordinate local Euler factor `K_p` of P8 (39) at the
sieve's weights `x_{jp} = p^{−a_j}`, `y_{jp} = p^{−b_j}` and the `1/[d,d′]`
denominator weight `z_{jp} = p^{−1}`. -/
noncomputable def coordLocalK {k : ℕ} (p : ℕ) (a b : Fin k → ℂ) : ℂ :=
  coordLocal (R := ℂ) (ι := ℕ) (fun j _ => (p : ℂ) ^ (-(a j)))
    (fun j _ => (p : ℂ) ^ (-(b j))) (fun _ _ => (p : ℂ) ^ (-1 : ℂ)) p

/-- The local factor in standard form, with the `z`-weight merged into the
exponent: `K_p = 1 + Σ_j (−p^{−1−a_j} − p^{−1−b_j} + p^{−1−a_j−b_j})`. -/
lemma coordLocalK_eq {k : ℕ} (p : ℕ) (hp : p ≠ 0) (a b : Fin k → ℂ) :
    coordLocalK p a b =
      1 + ∑ j : Fin k, (-((p : ℂ) ^ (-(1 + a j))) - ((p : ℂ) ^ (-(1 + b j))) +
        ((p : ℂ) ^ (-(1 + a j + b j)))) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  unfold coordLocalK coordLocal
  dsimp only
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have ha1 : (p : ℂ) ^ (-(a j)) * (p : ℂ) ^ (-1 : ℂ) = (p : ℂ) ^ (-(1 + a j)) := by
    rw [← Complex.cpow_add _ _ hp0]
    congr 1; ring
  have hb1 : (p : ℂ) ^ (-(b j)) * (p : ℂ) ^ (-1 : ℂ) = (p : ℂ) ^ (-(1 + b j)) := by
    rw [← Complex.cpow_add _ _ hp0]
    congr 1; ring
  have hab : (p : ℂ) ^ (-(a j)) * (p : ℂ) ^ (-(b j)) * (p : ℂ) ^ (-1 : ℂ) =
      (p : ℂ) ^ (-(1 + a j + b j)) := by
    rw [mul_assoc, ← Complex.cpow_add _ _ hp0, ← Complex.cpow_add _ _ hp0]
    congr 1; ring
  rw [← ha1, ← hb1, ← hab]
  ring

/-- The modulus of the local `cpow` weight: for `p > 0`,
`‖p^{−(1+a)}‖ = p^{−(1+Re a)}`. -/
lemma norm_cpow_neg_one_add {p : ℕ} (hp : 0 < p) (a : ℂ) :
    ‖(p : ℂ) ^ (-(1 + a))‖ = (p : ℝ) ^ (-(1 + a.re)) := by
  rw [Complex.norm_natCast_cpow_of_pos hp]
  simp [Complex.neg_re, Complex.add_re]

/-- Modulus of the local weight in the sieve normalization `Re a = 1/L`. -/
lemma norm_cpow_neg_one_add_of_re {p : ℕ} (hp : 0 < p) {L : ℝ} {a : ℂ}
    (ha : a.re = 1 / L) : ‖(p : ℂ) ^ (-(1 + a))‖ = (p : ℝ) ^ (-(1 + 1 / L)) := by
  rw [norm_cpow_neg_one_add hp, ha]

/-- Elementary triangle-inequality shape used for the local factor. -/
private lemma norm_neg_sub_add_le (w1 w2 w3 : ℂ) :
    ‖-w1 - w2 + w3‖ ≤ ‖w1‖ + ‖w2‖ + ‖w3‖ := by
  have h1 : ‖-w1 - w2 + w3‖ ≤ ‖-w1 - w2‖ + ‖w3‖ := norm_add_le _ _
  have h2 : ‖-w1 - w2‖ ≤ ‖-w1‖ + ‖w2‖ := norm_sub_le _ _
  have h3 : ‖-w1‖ = ‖w1‖ := norm_neg w1
  linarith

/-- **Per-prime crude bound (P8 p. 18).**  For a prime `p ≥ 2`, `L > 0` and
weights with `Re a_j = Re b_j = 1/L`,

    |K_p| ≤ (1 + 2·p^{−1−1/L} + p^{−1−2/L})^k . -/
theorem coordLocalK_norm_le {k : ℕ} {p : ℕ} (hp2 : 2 ≤ p) {L : ℝ} (hL : 0 < L)
    (a b : Fin k → ℂ) (ha : ∀ j, (a j).re = 1 / L) (hb : ∀ j, (b j).re = 1 / L) :
    ‖coordLocalK p a b‖ ≤
      (1 + 2 * (p : ℝ) ^ (-(1 + 1 / L)) + (p : ℝ) ^ (-(1 + 2 * (1 / L)))) ^ k := by
  classical
  have hp0 : 0 < p := by omega
  have hpn : p ≠ 0 := by omega
  rw [coordLocalK_eq p hpn a b]
  -- norm bound termwise
  have hterm : ∀ j : Fin k,
      ‖-((p : ℂ) ^ (-(1 + a j))) - ((p : ℂ) ^ (-(1 + b j))) +
        ((p : ℂ) ^ (-(1 + a j + b j)))‖ ≤
      2 * (p : ℝ) ^ (-(1 + 1 / L)) + (p : ℝ) ^ (-(1 + 2 * (1 / L))) := by
    intro j
    have h1 : ‖(p : ℂ) ^ (-(1 + a j))‖ = (p : ℝ) ^ (-(1 + 1 / L)) :=
      norm_cpow_neg_one_add_of_re hp0 (ha j)
    have h2 : ‖(p : ℂ) ^ (-(1 + b j))‖ = (p : ℝ) ^ (-(1 + 1 / L)) :=
      norm_cpow_neg_one_add_of_re hp0 (hb j)
    have hab : (-(1 + a j + b j)).re = -(1 + 2 * (1 / L)) := by
      rw [Complex.neg_re, Complex.add_re, Complex.add_re, Complex.one_re, ha j, hb j]
      ring
    have h3 : ‖(p : ℂ) ^ (-(1 + a j + b j))‖ = (p : ℝ) ^ (-(1 + 2 * (1 / L))) := by
      rw [Complex.norm_natCast_cpow_of_pos hp0, hab]
    calc
      ‖-((p : ℂ) ^ (-(1 + a j))) - ((p : ℂ) ^ (-(1 + b j))) +
          ((p : ℂ) ^ (-(1 + a j + b j)))‖
          ≤ ‖(p : ℂ) ^ (-(1 + a j))‖ + ‖(p : ℂ) ^ (-(1 + b j))‖ +
            ‖(p : ℂ) ^ (-(1 + a j + b j))‖ := norm_neg_sub_add_le _ _ _
      _ = (p : ℝ) ^ (-(1 + 1 / L)) + (p : ℝ) ^ (-(1 + 1 / L)) +
            (p : ℝ) ^ (-(1 + 2 * (1 / L))) := by rw [h1, h2, h3]
      _ = 2 * (p : ℝ) ^ (-(1 + 1 / L)) + (p : ℝ) ^ (-(1 + 2 * (1 / L))) := by ring
  -- sum bound
  have hsum : ‖1 + ∑ j : Fin k, (-((p : ℂ) ^ (-(1 + a j))) - ((p : ℂ) ^ (-(1 + b j))) +
      ((p : ℂ) ^ (-(1 + a j + b j))))‖ ≤
      1 + k * (2 * (p : ℝ) ^ (-(1 + 1 / L)) + (p : ℝ) ^ (-(1 + 2 * (1 / L)))) := by
    have hsumnorm : ‖∑ j : Fin k, (-((p : ℂ) ^ (-(1 + a j))) -
        ((p : ℂ) ^ (-(1 + b j))) + ((p : ℂ) ^ (-(1 + a j + b j))))‖ ≤
        ∑ j : Fin k, (2 * (p : ℝ) ^ (-(1 + 1 / L)) +
          (p : ℝ) ^ (-(1 + 2 * (1 / L)))) := by
      refine (norm_sum_le (Finset.univ : Finset (Fin k)) _).trans ?_
      exact Finset.sum_le_sum (fun j _ => hterm j)
    calc
      ‖1 + ∑ j : Fin k, (-((p : ℂ) ^ (-(1 + a j))) - ((p : ℂ) ^ (-(1 + b j))) +
          ((p : ℂ) ^ (-(1 + a j + b j))))‖
          ≤ ‖(1 : ℂ)‖ + ‖∑ j : Fin k, (-((p : ℂ) ^ (-(1 + a j))) -
              ((p : ℂ) ^ (-(1 + b j))) + ((p : ℂ) ^ (-(1 + a j + b j))))‖ :=
            norm_add_le _ _
      _ ≤ 1 + ∑ j : Fin k, (2 * (p : ℝ) ^ (-(1 + 1 / L)) +
              (p : ℝ) ^ (-(1 + 2 * (1 / L)))) := by
            rw [norm_one]
            linarith
      _ = 1 + k * (2 * (p : ℝ) ^ (-(1 + 1 / L)) + (p : ℝ) ^ (-(1 + 2 * (1 / L)))) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Bernoulli
  have hber : 1 + k * (2 * (p : ℝ) ^ (-(1 + 1 / L)) + (p : ℝ) ^ (-(1 + 2 * (1 / L)))) ≤
      (1 + 2 * (p : ℝ) ^ (-(1 + 1 / L)) + (p : ℝ) ^ (-(1 + 2 * (1 / L)))) ^ k := by
    have hU0 : 0 ≤ (p : ℝ) ^ (-(1 + 1 / L)) := Real.rpow_nonneg (by positivity) _
    have hV0 : 0 ≤ (p : ℝ) ^ (-(1 + 2 * (1 / L))) := Real.rpow_nonneg (by positivity) _
    have h := one_add_mul_le_pow
      (a := 2 * (p : ℝ) ^ (-(1 + 1 / L)) + (p : ℝ) ^ (-(1 + 2 * (1 / L)))) (n := k)
      (by linarith)
    have h' : (1 + (2 * (p : ℝ) ^ (-(1 + 1 / L)) + (p : ℝ) ^ (-(1 + 2 * (1 / L))))) ^ k =
        (1 + 2 * (p : ℝ) ^ (-(1 + 1 / L)) + (p : ℝ) ^ (-(1 + 2 * (1 / L)))) ^ k := by
      congr 1
      ring
    rwa [h'] at h
  exact hsum.trans hber

/-- **Product bound over a finite prime window.**  For `L > 0` and weights with
`Re a_j = Re b_j = 1/L`, the finite Euler product of the `k`-coordinate local
factors over the primes below `n` (excluding those dividing `q`) is bounded by
the `k`-th power of the corresponding product of the crude factors. -/
theorem coordProduct_norm_le (q n : ℕ) {k : ℕ} {L : ℝ} (hL : 0 < L)
    (a b : Fin k → ℂ) (ha : ∀ j, (a j).re = 1 / L) (hb : ∀ j, (b j).re = 1 / L) :
    ‖∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q), coordLocalK p a b‖ ≤
      (∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
        (1 + 2 * (p : ℝ) ^ (-(1 + 1 / L)) + (p : ℝ) ^ (-(1 + 2 * (1 / L))))) ^ k := by
  rw [Complex.norm_prod, ← Finset.prod_pow]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i hi => ?_)
  exact coordLocalK_norm_le (two_le_of_mem_primesBelow (Finset.mem_of_mem_filter i hi)) hL a b ha hb

/-- **Crude kernel bound (P8 p. 19).**  There is `C > 0` such that for all large
`x`, all window bounds `n`, and all weights with `Re a_j = Re b_j = 1/log x`
(the sieve's `a_j = (1+iξ_j)/log x`), the finite Euler product of the
`k`-coordinate local factors over the primes `p ∤ q` below `n` is at most
`C·(log x)^{3k}` — uniformly in `n` and in all Fourier variables. -/
theorem crudeKernelCoord_eventually (q k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, ∀ (n : ℕ) (a b : Fin k → ℂ),
      (∀ j, (a j).re = 1 / Real.log (x : ℝ)) →
      (∀ j, (b j).re = 1 / Real.log (x : ℝ)) →
      ‖∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q), coordLocalK p a b‖ ≤
        C * (Real.log (x : ℝ)) ^ (3 * k) := by
  rcases crudeProductLogBound_eventually q with ⟨C, hC, hxC⟩
  refine ⟨C ^ k, pow_pos hC k, ?_⟩
  filter_upwards [hxC, eventually_gt_atTop 1] with x hxprod hx1
  intro n a b ha hb
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
  have hnonneg : 0 ≤ ∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
      (1 + 2 * (p : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) +
        (p : ℝ) ^ (-(1 + 2 * (1 / Real.log (x : ℝ))))) := by
    refine Finset.prod_nonneg (fun p _ => ?_)
    have h1 : 0 ≤ (p : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) :=
      Real.rpow_nonneg (by positivity) _
    have h2 : 0 ≤ (p : ℝ) ^ (-(1 + 2 * (1 / Real.log (x : ℝ)))) :=
      Real.rpow_nonneg (by positivity) _
    linarith
  calc
    ‖∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q), coordLocalK p a b‖
        ≤ (∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
            (1 + 2 * (p : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) +
              (p : ℝ) ^ (-(1 + 2 * (1 / Real.log (x : ℝ)))))) ^ k :=
          coordProduct_norm_le q n hL a b ha hb
    _ ≤ (C * (Real.log (x : ℝ)) ^ 3) ^ k := pow_le_pow_left₀ hnonneg (hxprod n) k
    _ = C ^ k * (Real.log (x : ℝ)) ^ (3 * k) := by
          rw [mul_pow, ← pow_mul]


/-- **Crude kernel bound, uniform in the excluded modulus.**  `k`-coordinate
version of `crudeProductLogBound_eventually_uniform`: the constant is
independent of `q`. -/
theorem crudeKernelCoord_eventually_uniform (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, ∀ (q n : ℕ) (a b : Fin k → ℂ),
      (∀ j, (a j).re = 1 / Real.log (x : ℝ)) →
      (∀ j, (b j).re = 1 / Real.log (x : ℝ)) →
      ‖∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q), coordLocalK p a b‖ ≤
        C * (Real.log (x : ℝ)) ^ (3 * k) := by
  rcases crudeProductLogBound_eventually_uniform with ⟨C, hC, hxC⟩
  refine ⟨C ^ k, pow_pos hC k, ?_⟩
  filter_upwards [hxC, eventually_gt_atTop 1] with x hxprod hx1
  intro q n a b ha hb
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
  have hnonneg : 0 ≤ ∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
      (1 + 2 * (p : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) +
        (p : ℝ) ^ (-(1 + 2 * (1 / Real.log (x : ℝ))))) := by
    refine Finset.prod_nonneg (fun p _ => ?_)
    have h1 : 0 ≤ (p : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) :=
      Real.rpow_nonneg (by positivity) _
    have h2 : 0 ≤ (p : ℝ) ^ (-(1 + 2 * (1 / Real.log (x : ℝ)))) :=
      Real.rpow_nonneg (by positivity) _
    linarith
  calc
    ‖∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q), coordLocalK p a b‖
        ≤ (∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
            (1 + 2 * (p : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) +
              (p : ℝ) ^ (-(1 + 2 * (1 / Real.log (x : ℝ)))))) ^ k :=
          coordProduct_norm_le q n hL a b ha hb
    _ ≤ (C * (Real.log (x : ℝ)) ^ 3) ^ k := pow_le_pow_left₀ hnonneg (hxprod q n) k
    _ = C ^ k * (Real.log (x : ℝ)) ^ (3 * k) := by
          rw [mul_pow, ← pow_mul]

end Commons.NumberTheory.MaynardSieve
