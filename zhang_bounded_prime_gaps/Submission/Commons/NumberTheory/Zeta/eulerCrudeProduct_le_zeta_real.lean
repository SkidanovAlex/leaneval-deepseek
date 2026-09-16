import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

open scoped BigOperators Topology
open Filter Finset

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- Crude real per-prime bound. -/
lemma crudePerPrimeReal (p : ℝ) (hp : 2 ≤ p) {ε : ℝ} (hε : 0 < ε) :
    1 + 2 * p ^ (-(1 + ε)) + p ^ (-(1 + 2 * ε)) ≤ ((1 - p ^ (-(1 + ε)))⁻¹) ^ 3 := by
  let u : ℝ := p ^ (-(1 + ε))
  let v : ℝ := p ^ (-(1 + 2 * ε))
  have hp1 : 1 ≤ p := by linarith
  have hp1' : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hu0 : 0 < u := by
    dsimp [u]
    exact Real.rpow_pos_of_pos hp0 _
  have hv0 : 0 < v := by
    dsimp [v]
    exact Real.rpow_pos_of_pos hp0 _
  have hneg : -(1 + 2 * ε) ≤ -(1 + ε) := by linarith
  have hvu : v ≤ u := by
    dsimp [u, v]
    exact Real.rpow_le_rpow_of_exponent_le hp1 hneg
  have hu1 : u < 1 := by
    dsimp [u]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1' (by linarith)
  have hsubpos : 0 < 1 - u := sub_pos.mpr hu1
  have h1 : 1 + 2 * u + v ≤ 1 + 3 * u := by linarith
  have h2 : 1 + 3 * u ≤ (1 + u) ^ 3 := by
    nlinarith [sq_nonneg u]
  have h3 : (1 + u) ^ 3 ≤ ((1 - u)⁻¹) ^ 3 := by
    have hA : 1 + u ≤ (1 - u)⁻¹ := by
      have hx : (1 + u) * (1 - u) ≤ 1 := by nlinarith [sq_nonneg u]
      calc
        1 + u = ((1 + u) * (1 - u)) * (1 - u)⁻¹ := by field_simp [ne_of_gt hsubpos]
        _ ≤ 1 * (1 - u)⁻¹ := by
              exact mul_le_mul_of_nonneg_right hx (le_of_lt (inv_pos.mpr hsubpos))
        _ = (1 - u)⁻¹ := by ring
    have hpos3 : 0 ≤ 1 + u := by linarith
    exact pow_le_pow_left₀ hpos3 hA 3
  have hfin : 1 + 2 * u + v ≤ ((1 - u)⁻¹) ^ 3 := le_trans (le_trans h1 h2) h3
  simpa [u, v, mul_assoc] using hfin

/-- `u_p := p^{-(1+ε)}` is nonnegative for primes. -/
lemma real_u_nonneg {p : ℕ} (hp2 : 2 ≤ p) {ε : ℝ} :
    0 ≤ (p : ℝ) ^ (-(1 + ε)) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  exact le_of_lt (Real.rpow_pos_of_pos hp0 (-(1 + ε)))

/-- `u_p := p^{-(1+ε)} < 1` for primes and ε > 0. -/
lemma real_u_lt_one {p : ℕ} (hp2 : 2 ≤ p) {ε : ℝ} (hε : 0 < ε) :
    (p : ℝ) ^ (-(1 + ε)) < 1 := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)

/-- Real Euler factor `f_p := (1 - p^{-(1+ε)})⁻¹` is positive for primes. -/
lemma realFactor_pos {p : ℕ} (hp2 : 2 ≤ p) {ε : ℝ} (hε : 0 < ε) :
    0 < (1 - (p : ℝ) ^ (-(1 + ε)))⁻¹ := by
  have hu1 : (p : ℝ) ^ (-(1 + ε)) < 1 := real_u_lt_one hp2 hε
  exact inv_pos.mpr (sub_pos.mpr hu1)

/-- Real Euler factor `f_p` is `≥ 1` for primes. -/
lemma realFactor_one_le {p : ℕ} (hp2 : 2 ≤ p) {ε : ℝ} (hε : 0 < ε) :
    1 ≤ (1 - (p : ℝ) ^ (-(1 + ε)))⁻¹ := by
  have hu1 : (p : ℝ) ^ (-(1 + ε)) < 1 := real_u_lt_one hp2 hε
  have hu0 : 0 ≤ (p : ℝ) ^ (-(1 + ε)) := real_u_nonneg hp2
  have hpos : 0 < 1 - (p : ℝ) ^ (-(1 + ε)) := sub_pos.mpr hu1
  have hle1 : 1 - (p : ℝ) ^ (-(1 + ε)) ≤ 1 := by linarith
  have hinv : (1 : ℝ)⁻¹ ≤ (1 - (p : ℝ) ^ (-(1 + ε)))⁻¹ :=
    (inv_le_inv₀ (by norm_num : 0 < (1 : ℝ)) hpos).mpr hle1
  simpa using hinv

/-- Per-prime crude bound for a natural prime `p`. -/
lemma crudePerPrime (p : ℕ) (hp : 2 ≤ p) {ε : ℝ} (hε : 0 < ε) :
    1 + 2 * (p : ℝ) ^ (-(1 + ε)) + (p : ℝ) ^ (-(1 + 2 * ε)) ≤
      ((1 - (p : ℝ) ^ (-(1 + ε)))⁻¹) ^ 3 := by
  simpa using crudePerPrimeReal (p : ℝ) (by exact_mod_cast hp) hε

/-- The per-prime crude factor is nonnegative. -/
lemma crudeFactor_nonneg (p : ℕ) (hp2 : 2 ≤ p) {ε : ℝ} (_hε : 0 < ε) :
    0 ≤ 1 + 2 * (p : ℝ) ^ (-(1 + ε)) + (p : ℝ) ^ (-(1 + 2 * ε)) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hu : 0 < (p : ℝ) ^ (-(1 + ε)) := Real.rpow_pos_of_pos hp0 _
  have hw : 0 < (p : ℝ) ^ (-(1 + 2 * ε)) := Real.rpow_pos_of_pos hp0 _
  nlinarith

/-- Complex cpow factor at real `s`: `(p:ℂ)^{-(1+ε)} = ((p:ℝ)^{-(1+ε)} : ℂ)`. -/
lemma cpow_eq_ofReal (p : ℕ) (hpos : 0 < p) (ε : ℝ) :
    (p : ℂ) ^ (-(((1 + ε : ℝ) : ℂ))) = (((p : ℝ) ^ (-(1 + ε)) : ℝ) : ℂ) := by
  rw [show -(((1 + ε : ℝ) : ℂ)) = ((-(1 + ε) : ℝ) : ℂ) by simp]
  exact (Complex.ofReal_cpow (by exact_mod_cast (le_of_lt hpos) : 0 ≤ (p : ℝ)) (-(1 + ε))).symm

/-- The complex Euler factor equals the real one, as complex numbers:
`(1 - (p:ℂ)^{-s})⁻¹ = (f_p : ℂ)`. -/
lemma complexFactor_eq_ofReal (p : ℕ) (hpos : 0 < p) (ε : ℝ) :
    (1 - (p : ℂ) ^ (-(((1 + ε : ℝ) : ℂ))))⁻¹ =
      (((1 - (p : ℝ) ^ (-(1 + ε)))⁻¹ : ℝ) : ℂ) := by
  rw [cpow_eq_ofReal p hpos ε]
  norm_num

/-- Partial real Euler products are bounded by the modulus of the zeta value.
For `ε > 0`, `∏_{p < n} (1 - p^{-(1+ε)})⁻¹ ≤ ‖ζ(1+ε)‖`. -/
lemma partialEulerReal_le_absZeta (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    (∏ p ∈ n.primesBelow, (1 - (p : ℝ) ^ (-(1 + ε)))⁻¹) ≤
      ‖riemannZeta (((1 + ε : ℝ) : ℂ))‖ := by
  classical
  let s : ℂ := (((1 + ε : ℝ) : ℂ))
  let f : ℕ → ℝ := fun p => (1 - (p : ℝ) ^ (-(1 + ε)))⁻¹
  let a : ℕ → ℝ := fun m => ∏ p ∈ m.primesBelow, f p
  have hs : 1 < s.re := by
    dsimp [s]
    simp
    linarith
  have hB : Tendsto (fun m : ℕ => ∏ p ∈ m.primesBelow, (1 - (p : ℂ) ^ (-s))⁻¹) atTop
      (𝓝 (riemannZeta s)) := riemannZeta_eulerProduct (s := s) hs
  have hper : ∀ m : ℕ, ∀ p ∈ m.primesBelow, (1 - (p : ℂ) ^ (-s))⁻¹ = (f p : ℂ) := by
    intro m p hp
    have hpP : Nat.Prime p := (Nat.mem_primesBelow.mp hp).2
    dsimp [s, f]
    exact complexFactor_eq_ofReal p (Nat.Prime.pos hpP) ε
  have hf_pos : ∀ m : ℕ, ∀ p ∈ m.primesBelow, 0 < f p := by
    intro m p hp
    have hpP : Nat.Prime p := (Nat.mem_primesBelow.mp hp).2
    have hp2 : 2 ≤ p := Nat.Prime.two_le hpP
    dsimp [f]
    exact realFactor_pos hp2 hε
  have hnonneg_a : ∀ m : ℕ, 0 ≤ a m := by
    intro m
    dsimp [a]
    exact Finset.prod_nonneg (fun p hp => le_of_lt (hf_pos m p hp))
  have hcast : ∀ m : ℕ, ∏ p ∈ m.primesBelow, (1 - (p : ℂ) ^ (-s))⁻¹ = (a m : ℂ) := by
    intro m
    have h1 : (∏ p ∈ m.primesBelow, (1 - (p : ℂ) ^ (-s))⁻¹) =
        m.primesBelow.prod (fun p => (f p : ℂ)) := by
      exact Finset.prod_congr rfl (fun p hp => hper m p hp)
    have h2 : m.primesBelow.prod (fun p => (f p : ℂ)) = ↑(m.primesBelow.prod f) := by
      exact (Complex.ofReal_prod m.primesBelow f).symm
    have h3 : ↑(m.primesBelow.prod f) = (a m : ℂ) := rfl
    exact h1.trans (h2.trans h3)
  have hnorm : Tendsto a atTop (𝓝 ‖riemannZeta s‖) := by
    refine (hB.norm).congr' (Eventually.of_forall ?_)
    intro m
    rw [hcast m]
    exact Complex.norm_of_nonneg (hnonneg_a m)
  have hmono : ∀ {m k : ℕ}, m ≤ k → a m ≤ a k := by
    intro m k hmk
    dsimp [a]
    exact Finset.prod_le_prod_of_subset_of_one_le₀
      (by intro p hp; rw [Nat.mem_primesBelow] at hp ⊢; exact ⟨lt_of_lt_of_le hp.1 hmk, hp.2⟩)
      (fun p hp => le_of_lt (hf_pos m p hp))
      (fun p hp _ => by
        have hpP : Nat.Prime p := (Nat.mem_primesBelow.mp hp).2
        have hp2 : 2 ≤ p := Nat.Prime.two_le hpP
        dsimp [f]
        exact realFactor_one_le hp2 hε)
  have hlelim : ∀ m : ℕ, a m ≤ ‖riemannZeta s‖ := by
    intro m
    exact ge_of_tendsto (b := a m) hnorm (eventually_atTop.2 ⟨m, fun k hk => hmono hk⟩)
  simpa [a, f, s] using hlelim n

/-- Crude kernel bound, Euler-product comparison (Polymath8a Lemma 4.1 proof):
for real `ε > 0` and every `n`, the finite product over the primes `p < n`
not dividing `q` of the per-prime absolute factor
`1 + 2/p^{1+ε} + 1/p^{1+2ε}` is `≤ ζ(1+ε)³` (here `ζ` is the complex
Riemann zeta at the real argument `(1+ε : ℝ) : ℂ`, modulus taken).

Suggested decomposition (all elementary real/complex analysis on top of
Mathlib, no other imports needed):

1. per-prime inequality `1 + 2u + v ≤ ((1−u)⁻¹)³` with
   `u := p^{−(1+ε)}`, `v := p^{−(1+2ε)} ≤ u` (`v ≤ u` by
   `Real.rpow_le_rpow_of_exponent_le`, base `p ≥ 2 ≥ 1`; then
   `1+2u+v ≤ 1+3u ≤ (1+u)³ ≤ ((1−u)⁻¹)³` via `(1+u)(1−u) = 1−u² ≤ 1`
   and `0 < 1−u`);
2. hence `∏_{p ∈ S}(1 + 2u + v) ≤ (∏_{p ∈ S}(1−u)⁻¹)³` over the finite set
   `S := (n.primesBelow).filter (fun p => ¬ p ∣ q)`;
3. bound `∏_{p ∈ S}(1−u_p)⁻¹ ≤ ‖ζ(1+ε)‖`: with complex
   `s := ((1+ε : ℝ) : ℂ)`, `u_p = ‖(p : ℂ)^(−s)‖` (`norm_cpow_nat_eq`-type
   fact: `‖(p:ℂ)^z‖ = (p:ℝ)^z.re`, `(−s).re = −(1+ε)`) and
   `(p : ℂ)^(−s) = (u_p : ℂ)` (`Complex.ofReal_cpow`, `Complex.cpow_neg`,
   `Complex.ofReal_inv`, `Real.rpow_neg`), so
   `‖(1 − (p:ℂ)^(−s))⁻¹‖ = (1−u_p)⁻¹`; the real product over `S` is
   `≤` the modulus of the full partial product `∏_{p ∈ n.primesBelow}
   (1 − (p:ℂ)^(−s))⁻¹` (factors `≥ 1`, `S ⊆ n.primesBelow`), which tends to
   `ζ(s)` by `riemannZeta_eulerProduct` (`1 < s.re` since `ε > 0`); partial
   products are nondecreasing in modulus, so each is `≤ |ζ(s)|`.

This is input (b) of the ξ-truncation of the bounded-gaps proof: with
`ζ(1+ε) ≪ 1/ε` (`ε = 1/log x`) it gives `|K(ξ)| ≤ C·log³x`, uniform in the
Fourier variables. -/

theorem eulerCrudeProduct_le_zeta_real (q : ℕ) (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    (∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
        (1 + 2 * (p : ℝ) ^ (-(1 + ε)) + (p : ℝ) ^ (-(1 + 2 * ε)))) ≤
      ‖riemannZeta ((1 + ε : ℝ) : ℂ)‖ ^ 3 := by
  classical
  let S : Finset ℕ := (n.primesBelow).filter (fun p => ¬ p ∣ q)
  let T : Finset ℕ := n.primesBelow
  let f : ℕ → ℝ := fun p => (1 - (p : ℝ) ^ (-(1 + ε)))⁻¹
  have hTsub : S ⊆ T := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hprime : ∀ p ∈ T, Nat.Prime p := by
    intro p hp
    exact (Nat.mem_primesBelow.mp hp).2
  have hprod_le : (∏ p ∈ S,
        ((1 + 2 * (p : ℝ) ^ (-(1 + ε)) + (p : ℝ) ^ (-(1 + 2 * ε))))) ≤
      (∏ p ∈ S, f p) ^ 3 := by
    calc
      (∏ p ∈ S, ((1 + 2 * (p : ℝ) ^ (-(1 + ε)) + (p : ℝ) ^ (-(1 + 2 * ε)))))
          ≤ ∏ p ∈ S, (f p) ^ 3 := by
              refine Finset.prod_le_prod₀ ?h0 ?h1
              · intro p hp
                have hp2 : 2 ≤ p := Nat.Prime.two_le (hprime p (hTsub hp))
                exact crudeFactor_nonneg p hp2 hε
              · intro p hp
                have hp2 : 2 ≤ p := Nat.Prime.two_le (hprime p (hTsub hp))
                dsimp [f]
                exact crudePerPrime p hp2 hε
      _ = (∏ p ∈ S, f p) ^ 3 := Finset.prod_pow S 3 f
  have hSprod_le : (∏ p ∈ S, f p) ≤ ‖riemannZeta ((1 + ε : ℝ) : ℂ)‖ := by
    calc
      (∏ p ∈ S, f p) ≤ (∏ p ∈ T, f p) := by
            refine Finset.prod_le_prod_of_subset_of_one_le₀ hTsub ?hf0 ?hf1
            · intro p hp
              have hp2 : 2 ≤ p := Nat.Prime.two_le (hprime p (hTsub hp))
              dsimp [f]
              exact le_of_lt (realFactor_pos hp2 hε)
            · intro p hp _
              have hp2 : 2 ≤ p := Nat.Prime.two_le (hprime p hp)
              dsimp [f]
              exact realFactor_one_le hp2 hε
      _ ≤ ‖riemannZeta (((1 + ε : ℝ) : ℂ))‖ := by
            dsimp [T, f]
            exact partialEulerReal_le_absZeta ε hε n
  have hnonneg : 0 ≤ ∏ p ∈ S, f p := by
    exact Finset.prod_nonneg (fun p hp => by
      have hp2 : 2 ≤ p := Nat.Prime.two_le (hprime p (hTsub hp))
      dsimp [f]
      exact le_of_lt (realFactor_pos hp2 hε))
  have hpow : (∏ p ∈ S, f p) ^ 3 ≤ ‖riemannZeta ((1 + ε : ℝ) : ℂ)‖ ^ 3 := by
    exact pow_le_pow_left₀ hnonneg hSprod_le 3
  exact le_trans hprod_le hpow

end Commons.NumberTheory.Zeta