import Mathlib
import Mathlib.NumberTheory.LSeries.RiemannZeta
set_option maxHeartbeats 2000000

open scoped BigOperators Topology
open Filter Finset

noncomputable section

/-!
# The modified zeta `ζ_WN` of Polymath8a Lemma 4.1 (part (ii))

This file (module `Submission.ZetaWN`) formalizes the *modified zeta* of
Polymath8a Lemma 4.1: for `q : ℕ` (in the paper `q = WN`, a modulus),

    ζ_q(s) := ∏_{p ∤ q} (1 − p⁻ˢ)⁻¹            (Re s > 1),

the Riemann zeta with the Euler factors of the primes dividing `q` removed
(meromorphically `ζ_q(s) = ζ(s) · ∏_{p | q} (1 − p⁻ˢ)`, valid on all of ℂ;
`zetaWN` below is this meromorphic object).

Contents (all kernel-verified, no axioms):

  * `zetaWN` — the definition;
  * `zetaWN_eulerProduct` — for `1 < s.re`, `ζ_q(s)` is the limit of the
    partial products over primes `p < n` with `p ∤ q` (Polymath8a's defining
    formula); built on the Euler product of the Riemann zeta in Mathlib
    (`riemannZeta_eulerProduct`) plus finite-product removal of the primes
    dividing `q`;
  * `zetaWN_residue_one` — the *simple pole at `s = 1` with residue
    `φ(q)/q`*: `(s − 1)·ζ_q(s) → φ(q)/q` as `s → 1, s ≠ 1` (via
    `riemannZeta_residue_one`), together with
    `totient_div_self_eq_prod_one_sub_inv` re-expressing the residue as
    `φ(q)/q`;
  * `continuousOn_zetaWN` (holomorphic off `s = 1`), `zetaWN_residue_ne_zero`
    and `zetaWN_eventually_ne_zero` (non-vanishing in a punctured
    neighbourhood of the pole).

As Polymath8a puts it (proof of Lemma 4.1): "both approaches ultimately use
the same input, namely the simple pole of the Riemann zeta function at s = 1".
Every zeta-like Euler-factor ratio in the per-coordinate evaluation of
Lemma 4.1 is `(1 + o(1))` times the pole contribution recorded here.
(Mathlib also carries this object as the L-function of the trivial Dirichlet
character mod `q`, `LFunctionTrivChar q`, whose residue it records as
`∏_{p | q}(1 − p⁻¹)`.)
-/

namespace Commons.NumberTheory.MaynardSieve

/-- `ζ_q(s) := ζ(s) · ∏_{p | q} (1 − p⁻ˢ)` for `q : ℕ`, `s : ℂ` — the Riemann
zeta with the Euler factors of the primes dividing `q` removed. -/
def zetaWN (q : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s * ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))

/-- `φ(q)/q` computed as an Euler product over the distinct prime factors of
`q` (in ℂ): `∏_{p | q} (1 − 1/p) = φ(q)/q` for `q ≠ 0`. -/
lemma totient_div_self_eq_prod_one_sub_inv (q : ℕ) (hq : q ≠ 0) :
    (q.totient : ℂ) / (q : ℂ) = ∏ p ∈ q.primeFactors, (1 - ((p : ℂ))⁻¹) := by
  classical
  let g : ℂ := ∏ p ∈ q.primeFactors, (p : ℂ)
  let A : ℂ := ∏ p ∈ q.primeFactors, (1 - ((p : ℂ))⁻¹)
  let B : ℂ := ∏ p ∈ q.primeFactors, (((p - 1 : ℕ) : ℂ))
  have hg : g ≠ 0 := by
    dsimp [g]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => by
      exact_mod_cast (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp)))
  have hB' : A * g = B := by
    dsimp [A, B, g]
    calc
      (∏ p ∈ q.primeFactors, (1 - ((p : ℂ))⁻¹)) * ∏ p ∈ q.primeFactors, (p : ℂ)
          = ∏ p ∈ q.primeFactors, ((1 - ((p : ℂ))⁻¹) * (p : ℂ)) := by
              rw [Finset.prod_mul_distrib]
      _ = ∏ p ∈ q.primeFactors, (((p - 1 : ℕ) : ℂ)) := by
              refine Finset.prod_congr rfl ?_
              intro p hp
              have hp0 : (p : ℂ) ≠ 0 := by
                exact_mod_cast (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp))
              field_simp [hp0]
              norm_num [Nat.cast_sub (by
                have h2 := Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp)
                omega : 1 ≤ p)]
  have hC : (q.totient : ℂ) * g = (q : ℂ) * B := by
    have h := congrArg (fun x : ℕ => (x : ℂ)) (Nat.totient_mul_prod_primeFactors q)
    -- h : ↑(φ q * ∏_{p|q} p) = ↑(q * ∏_{p|q} (p - 1))
    have h1 : (q.totient : ℂ) * ∏ p ∈ q.primeFactors, (p : ℂ) =
        (q : ℂ) * ∏ p ∈ q.primeFactors, (((p - 1 : ℕ) : ℂ)) := by
      simpa [Nat.cast_mul, Nat.cast_prod] using h
    dsimp [g, B]
    exact h1
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hden : (q : ℂ) * g ≠ 0 := mul_ne_zero hqC hg
  apply (mul_right_inj' hden).mp
  calc
    ((q : ℂ) * g) * ((q.totient : ℂ) / (q : ℂ))
        = (q.totient : ℂ) * g := by
            field_simp [hqC]
    _ = (q : ℂ) * B := hC
    _ = ((q : ℂ) * g) * A := by
            rw [← hB']
            ring

/-- Each factor `1 − p⁻ˢ` of the removed Euler product is continuous in `s`
(for `p ≠ 0`; in our use `p` is prime). -/
lemma continuous_one_sub_inv_pow {p : ℕ} (hp : p ≠ 0) :
    Continuous (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) := by
  have hbase : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hcpow : Continuous (fun s : ℂ => (p : ℂ) ^ (-s)) := by
    rw [continuous_iff_continuousAt]
    intro z
    have hz : Tendsto (fun s : ℂ => -s) (𝓝 z) (𝓝 (-z)) := continuousAt_id.neg.tendsto
    exact (Tendsto.const_cpow (a := (p : ℂ)) (b := -z) hz (Or.inl hbase))
  exact continuous_const.sub hcpow

/-- The finite Euler-product factor `∏_{p | q} (1 − p⁻ˢ)` tends to its value
at `s = 1`, namely `∏_{p | q} (1 − 1/p)`, as `s → 1`. -/
lemma tendsto_factor_one_sub (q : ℕ) :
    Tendsto (fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) (𝓝 1)
      (𝓝 (∏ p ∈ q.primeFactors, (1 - ((p : ℂ))⁻¹))) := by
  classical
  have hcont : Continuous (fun s : ℂ =>
      ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) := by
    refine continuous_finsetProd q.primeFactors (fun p hp => ?_)
    exact continuous_one_sub_inv_pow (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp))
  have hlim := hcont.tendsto 1
  have hval : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-(1 : ℂ)))) =
      ∏ p ∈ q.primeFactors, (1 - ((p : ℂ))⁻¹) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    congr 1
    rw [← Complex.cpow_neg_one]
  simpa [hval] using hlim

/-- `ζ_q` has a simple pole at `s = 1` with residue `φ(q)/q`:
`(s − 1) · ζ_q(s) → φ(q)/q` as `s → 1`, `s ≠ 1`. -/
lemma zetaWN_residue_one (q : ℕ) (hq : q ≠ 0) :
    Tendsto (fun s : ℂ => (s - 1) * zetaWN q s) (𝓝[≠] 1)
      (𝓝 ((q.totient : ℂ) / (q : ℂ))) := by
  have H : (fun s : ℂ => (s - 1) * zetaWN q s) =ᶠ[𝓝[≠] 1]
        fun s : ℂ => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) *
          ((s - 1) * riemannZeta s) := by
    refine Set.EqOn.eventuallyEq_nhdsWithin ?_
    intro s hs
    simp [zetaWN, mul_assoc, mul_comm, mul_left_comm]
  rw [tendsto_congr' H]
  have hpf : Tendsto (fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)))
      (𝓝[≠] 1) (𝓝 (∏ p ∈ q.primeFactors, (1 - ((p : ℂ))⁻¹))) :=
    tendsto_nhdsWithin_of_tendsto_nhds (tendsto_factor_one_sub q)
  have hprod : Tendsto (fun s : ℂ =>
      (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * ((s - 1) * riemannZeta s))
      (𝓝[≠] 1) (𝓝 ((∏ p ∈ q.primeFactors, (1 - ((p : ℂ))⁻¹)) * 1)) :=
    hpf.mul riemannZeta_residue_one
  simpa [totient_div_self_eq_prod_one_sub_inv q hq, mul_one] using hprod

/-- Away from the pole at `s = 1`, `ζ_q` has the local form
`ζ_q(s) = (s − 1)⁻¹ · ((s − 1)·ζ(s)) · ∏_{p | q}(1 − p⁻ˢ)`, which isolates
the pole. -/
lemma zetaWN_eq_inv_sub_mul (q : ℕ) {s : ℂ} (hs : s ≠ 1) :
    zetaWN q s = (s - 1)⁻¹ * (((s - 1) * riemannZeta s) * ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) := by
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp [zetaWN, hs']
  rfl

end Commons.NumberTheory.MaynardSieve

namespace Commons.NumberTheory.MaynardSieve

/-! ## Euler-product characterization (Re s > 1)

For `1 < s.re` the meromorphic definition agrees with the Euler product over
the primes not dividing `q`:

    ζ_q(s) = lim_{n→∞} ∏_{p < n, p ∤ q} (1 − p⁻ˢ)⁻¹   .

This is Polymath8a's definition of `ζ_WN`; it is what makes the per-coordinate
local factors of Lemma 4.1 (equations (39)–(41)) factor through `ζ_WN`.
-/

lemma norm_cpow_neg_lt_one {p : ℕ} {s : ℂ} (hp : 2 ≤ p) (hs : 1 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) :=
    (Complex.ofReal_log (by exact_mod_cast (by omega : 0 ≤ p))).symm
  have hmain : (p : ℂ) ^ (-s) = Complex.exp ((Real.log (p : ℝ) : ℂ) * (-s)) := by
    rw [Complex.cpow_def_of_ne_zero hp0, hlog]
  rw [hmain, Complex.norm_exp]
  have hzre : (((Real.log (p : ℝ) : ℂ) * (-s)).re) = Real.log (p : ℝ) * (-s.re) := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re]
    ring
  rw [hzre]
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
  have hneg : -s.re ≤ -1 := by linarith
  have hmul : Real.log (p : ℝ) * (-s.re) ≤ Real.log (p : ℝ) * (-1) := by
    exact mul_le_mul_of_nonneg_left hneg hlogp
  have hb : Real.exp (Real.log (p : ℝ) * (-s.re)) ≤ Real.exp (Real.log (p : ℝ) * (-1)) :=
    Real.exp_le_exp.mpr hmul
  have he1 : Real.exp (Real.log (p : ℝ) * (-1)) = (p : ℝ)⁻¹ := by
    have hring : Real.log (p : ℝ) * (-1) = -Real.log (p : ℝ) := by ring
    rw [hring, Real.exp_neg, Real.exp_log (by exact_mod_cast (by omega : 0 < p))]
  have hle12 : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
    (inv_le_inv₀ (by exact_mod_cast (by omega : 0 < p)) (by norm_num)).mpr (by exact_mod_cast hp)
  have hb2 : Real.exp (Real.log (p : ℝ) * (-s.re)) ≤ (2 : ℝ)⁻¹ := by
    exact hb.trans (by rw [he1]; exact hle12)
  exact lt_of_le_of_lt hb2 (by norm_num)

lemma one_sub_cpow_ne_zero {p : ℕ} {s : ℂ} (hp : 2 ≤ p) (hs : 1 < s.re) :
    (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
  intro hz
  have hEq : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hz).symm
  have hlt := norm_cpow_neg_lt_one (s := s) hp hs
  rw [hEq] at hlt
  norm_num at hlt

lemma zetaWN_eulerProduct (q : ℕ) (hq : q ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun n : ℕ => ∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
        (1 - (p : ℂ) ^ (-s))⁻¹) atTop (𝓝 (zetaWN q s)) := by
  let f : ℕ → ℂ := fun p => (1 - (p : ℂ) ^ (-s))⁻¹
  have hf0 : ∀ p, 2 ≤ p → f p ≠ 0 := by
    intro p hp
    dsimp [f]
    exact inv_ne_zero (one_sub_cpow_ne_zero (s := s) hp hs)
  let C : ℂ := ∏ p ∈ q.primeFactors, f p
  have hC0 : C ≠ 0 := by
    dsimp [C]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp =>
      hf0 p (Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp)))
  have hpt : ∀ n : ℕ, q < n →
      (∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q), f p) * C =
        ∏ p ∈ n.primesBelow, f p := by
    intro n hn
    let B : Finset ℕ := n.primesBelow
    have hQsub : q.primeFactors ⊆ B := by
      intro p hp
      rw [Nat.mem_primesBelow]
      have hpP : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hpq : p ∣ q := (Nat.mem_primeFactors.mp hp).2.1
      have hp_le : p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hpq
      constructor
      · omega
      · exact hpP
    have hfilter_eq : B.filter (fun p => p ∣ q) = q.primeFactors := by
      apply Finset.Subset.antisymm
      · intro p hp
        rw [Finset.mem_filter] at hp
        have hprime : Nat.Prime p := (Nat.mem_primesBelow.mp hp.1).2
        rw [Nat.mem_primeFactors]
        exact ⟨hprime, hp.2, hq⟩
      · intro p hp
        rw [Finset.mem_filter]
        constructor
        · exact hQsub hp
        · exact (Nat.mem_primeFactors.mp hp).2.1
    calc
      (∏ p ∈ B.filter (fun p => ¬ p ∣ q), f p) * (∏ p ∈ q.primeFactors, f p)
          = (∏ p ∈ B.filter (fun p => ¬ p ∣ q), f p) *
              (∏ p ∈ B.filter (fun p => p ∣ q), f p) := by
              rw [hfilter_eq]
      _ = ∏ p ∈ B, f p := by
              have hunion : B = B.filter (fun p => ¬ p ∣ q) ∪ B.filter (fun p => p ∣ q) := by
                apply Finset.Subset.antisymm
                · intro p hpB
                  by_cases hpd : p ∣ q
                  · exact Finset.mem_union.mpr (Or.inr (by simp [hpB, hpd]))
                  · exact Finset.mem_union.mpr (Or.inl (by simp [hpB, hpd]))
                · intro p hp
                  exact (Finset.mem_union.mp hp).elim
                    (fun h => (Finset.mem_filter.mp h).1)
                    (fun h => (Finset.mem_filter.mp h).1)
              have hdisj : Disjoint (B.filter (fun p => ¬ p ∣ q)) (B.filter (fun p => p ∣ q)) := by
                rw [Finset.disjoint_left]
                intro p hp1 hp2
                have h1 : ¬ p ∣ q := (Finset.mem_filter.mp hp1).2
                have h2 : p ∣ q := (Finset.mem_filter.mp hp2).2
                exact h1 h2
              rw [← Finset.prod_union hdisj, ← hunion]
  have hfull : Tendsto (fun n : ℕ => ∏ p ∈ n.primesBelow, f p) atTop
      (𝓝 (riemannZeta s)) := riemannZeta_eulerProduct (s := s) hs
  have hmain_t : Tendsto (fun n : ℕ => C⁻¹ * (∏ p ∈ n.primesBelow, f p)) atTop
      (𝓝 (C⁻¹ * riemannZeta s)) := hfull.const_mul C⁻¹
  have hmain_t2 : Tendsto (fun n : ℕ => (∏ p ∈ n.primesBelow, f p) * C⁻¹) atTop
      (𝓝 (riemannZeta s * C⁻¹)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmain_t
  -- value: riemannZeta s * C⁻¹ = zetaWN q s
  have hval : riemannZeta s * C⁻¹ = zetaWN q s := by
    dsimp [C, zetaWN]
    rw [← Finset.prod_inv_distrib]
    simp [f]
  have hmain3 : Tendsto (fun n : ℕ => (∏ p ∈ n.primesBelow, f p) * C⁻¹) atTop
      (𝓝 (zetaWN q s)) := by
    simpa [hval] using hmain_t2
  refine hmain3.congr' ?_
  filter_upwards [eventually_gt_atTop q] with n hn
  have he := hpt n hn
  have hcalc : (∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q), f p) =
      (∏ p ∈ n.primesBelow, f p) * C⁻¹ := by
    calc
      (∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q), f p)
          = (∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q), f p) * (C * C⁻¹) := by
              rw [mul_inv_cancel₀ hC0, mul_one]
      _ = ((∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q), f p) * C) * C⁻¹ := by ring
      _ = (∏ p ∈ n.primesBelow, f p) * C⁻¹ := by rw [he]
  simpa [f] using hcalc.symm



/-! ## The pole at `s = 1` is the only singularity, and `ζ_q` is non-zero near it

Recorded here (for the ξ-integral/truncation step of Lemma 4.1, where the
sieve evaluates ratios of `ζ_WN` values at points `1 + O(1/log x)`):

  * `ζ_q` is continuous (indeed holomorphic) away from `s = 1`;
  * `ζ_q` is non-zero in a punctured neighbourhood of `s = 1` (it has a
    simple pole there, so its reciprocal is non-vanishing nearby).
-/

/-- `ζ_q` is continuous away from `s = 1`. -/
lemma continuousOn_zetaWN (q : ℕ) : ContinuousOn (zetaWN q) ({1}ᶜ) := by
  have hζ : ContinuousOn riemannZeta ({1}ᶜ) := differentiableOn_riemannZeta.continuousOn
  have hprod : Continuous (fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) := by
    refine continuous_finsetProd q.primeFactors (fun p hp => ?_)
    exact continuous_one_sub_inv_pow (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp))
  change ContinuousOn (fun s : ℂ =>
      riemannZeta s * (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)))) ({1}ᶜ)
  exact hζ.mul (hprod.continuousOn.mono (Set.subset_univ _))

/-- The residue `φ(q)/q` of `ζ_q` at `s = 1` is non-zero (for `q ≠ 0`). -/
lemma zetaWN_residue_ne_zero (q : ℕ) (hq : q ≠ 0) : (q.totient : ℂ) / (q : ℂ) ≠ 0 := by
  have hφ : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)
  have hφc : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hφ)
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  exact div_ne_zero hφc hqc

/-- `ζ_q` is non-zero on a punctured neighbourhood of `s = 1` (for `q ≠ 0`). -/
lemma zetaWN_eventually_ne_zero (q : ℕ) (hq : q ≠ 0) :
    ∀ᶠ s in 𝓝[≠] 1, zetaWN q s ≠ 0 := by
  have hres := zetaWN_residue_one q hq
  have hφ := zetaWN_residue_ne_zero q hq
  have hev : ∀ᶠ s in 𝓝[≠] 1, (s - 1) * zetaWN q s ≠ 0 := hres.eventually_ne hφ
  filter_upwards [hev] with s hs
  exact (mul_ne_zero_iff.mp hs).2

end Commons.NumberTheory.MaynardSieve
