import Mathlib
import Submission.Work.A3.expSum_range_split
import Submission.Commons.Analysis.ExponentialSums.exp_eval_div_eq_exp_eval_mod

set_option autoImplicit false

namespace Work.A3

open Polynomial Finset
open scoped BigOperators

noncomputable section

/-!
# Block decomposition of a polynomial Weyl sum modulo `q`

`Work.A3.expSum Q N θ = ∑_{n ∈ [1,N]} e(-2πi θ Q(n))`.  For a phase split `θ = a/q + β` with
`q ≤ N` and `a ∈ ℤ`, `β ∈ ℝ`, the index set `{0,1,…,N}` decomposes bijectively into the blocks
`n = r + p q`, `0 ≤ r < q` (`r = n mod q`), `p ≤ (N − r)/q`; the rational part
`e(-2πi a Q(n)/q)` of the summand is `q`-periodic, so it factors out of each block, while the
archimedean part `e(-2πi β Q(n))` stays inside the block.  This is the first step of the
major-arc decomposition of Area A3 (`Work.A3.expSum_range_split` performs the phase split and
this module performs the block decomposition).

The proof is three independent auxiliary facts:

* `Work.A3.sum_range_eq_sum_blocks` — the purely combinatorial bijection
  `{(r,p) : 0 ≤ r < q, p < (N-r)/q+1} ≃ {0,…,N}`, `(r,p) ↦ r + p q` (it uses `q ≤ N` to rule out
  the blocks starting beyond `N`);
* `Work.A3.Qreal_eval_nat` — the real polynomial `Qreal Q` at a natural number is the cast of
  the integer value of `Q`;
* `Work.A3.exp_rat_phase_period_nat` — `q`-periodicity of `n ↦ e(-2πi (a/q) Q(n))`, a
  reindexing of the commons lemma
  `Commons.Analysis.ExponentialSums.exp_eval_div_eq_exp_eval_mod` (which is stated in the
  `+2πi` convention) built on `Commons.Analysis.Polynomial.dvd_eval_sub_eval_mul`.
-/

/-- **Combinatorial block decomposition.**  For `1 ≤ q ≤ N` the map
`(r,p) ↦ r + p*q` from the pairs `{0 ≤ r < q}` × `{p < (N - r)/q + 1}` to `{0,1,…,N}` is a
bijection (its inverse is `n ↦ (n % q, n / q)`), so any sum over `range (N+1)` is the sum of the
blocks.  The hypothesis `q ≤ N` guarantees that every residue class `0 ≤ r < q` occurs at least
once before `N` (i.e. `r ≤ N` for all `r < q`). -/
lemma sum_range_eq_sum_blocks (q N : ℕ) (hq : 1 ≤ q) (hqN : q ≤ N) (c : ℕ → ℂ) :
    ∑ n ∈ Finset.range (N + 1), c n
      = ∑ r ∈ Finset.range q, ∑ p ∈ Finset.range ((N - r) / q + 1), c (r + p * q) := by
  have hsig : (∑ x ∈ (Finset.range q).sigma (fun r => Finset.range ((N - r) / q + 1)),
        c (x.1 + x.2 * q))
      = ∑ r ∈ Finset.range q, ∑ p ∈ Finset.range ((N - r) / q + 1), c (r + p * q) := by
    simpa using Finset.sum_sigma (Finset.range q) (fun r => Finset.range ((N - r) / q + 1))
      (fun x : Sigma fun r : ℕ => ℕ => c (x.1 + x.2 * q))
  have hbij : (∑ x ∈ (Finset.range q).sigma (fun r => Finset.range ((N - r) / q + 1)),
        c (x.1 + x.2 * q)) = ∑ n ∈ Finset.range (N + 1), c n := by
    refine Finset.sum_bij (fun (x : Sigma fun r : ℕ => ℕ) _ => x.1 + x.2 * q) ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_sigma] at hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [Finset.mem_range] at hx1 hx2 ⊢
      have h1 : x.1 ≤ N := by omega
      have h2 : x.2 * q ≤ N - x.1 := by
        have h3 : x.2 ≤ (N - x.1) / q := by omega
        calc x.2 * q ≤ ((N - x.1) / q) * q := Nat.mul_le_mul_right _ h3
          _ ≤ N - x.1 := Nat.div_mul_le_self _ _
      omega
    · intro x hx y hy heq
      rw [Finset.mem_sigma] at hx hy
      rw [Finset.mem_range] at hx hy
      have hxq : x.1 < q := hx.1
      have hyq : y.1 < q := hy.1
      have hx1 : x.1 = y.1 := by
        have hmod : (x.1 + x.2 * q) % q = (y.1 + y.2 * q) % q := by rw [heq]
        rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt hxq, Nat.mod_eq_of_lt hyq] at hmod
        exact hmod
      have hx2 : x.2 = y.2 := by
        have : x.2 * q = y.2 * q := by omega
        exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) this
      exact Sigma.ext hx1 (heq_of_eq hx2)
    · intro b hb
      rw [Finset.mem_range] at hb
      refine ⟨⟨b % q, b / q⟩, ?_, ?_⟩
      · rw [Finset.mem_sigma]
        refine ⟨?_, ?_⟩
        · rw [Finset.mem_range]; exact Nat.mod_lt _ (by omega)
        · rw [Finset.mem_range]
          have h1 : q * (b / q) ≤ N - b % q := by
            have h2 : b % q + q * (b / q) = b := Nat.mod_add_div b q
            omega
          have h3 : b / q ≤ (N - b % q) / q := by
            calc b / q = q * (b / q) / q := (Nat.mul_div_cancel_left _ (by omega : 0 < q)).symm
              _ ≤ (N - b % q) / q := Nat.div_le_div_right h1
          show b / q < (N - b % q) / q + 1
          omega
      · show b % q + (b / q) * q = b
        rw [Nat.mul_comm]
        exact Nat.mod_add_div b q
    · intro a ha
      rfl
  exact (hsig.symm.trans hbij).symm

/-- The real polynomial `Qreal Q` evaluated at an integer: `(Qreal Q)(x) = (Q(x) : ℝ)`. -/
lemma Qreal_eval_int (Q : Polynomial ℤ) (x : ℤ) :
    (Qreal Q).eval (x : ℝ) = ((Q.eval x : ℤ) : ℝ) := by
  rw [Qreal, Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (Int.castRingHom ℝ) x

/-- The real polynomial `Qreal Q` evaluated at a natural number: `(Qreal Q)(n) = (Q(n) : ℝ)`. -/
lemma Qreal_eval_nat (Q : Polynomial ℤ) (n : ℕ) :
    (Qreal Q).eval (n : ℝ) = ((Q.eval (n : ℤ) : ℤ) : ℝ) := by
  have : (n : ℝ) = ((n : ℤ) : ℝ) := by push_cast; ring
  rw [this, Qreal_eval_int]

/-- **`q`-periodicity of the rational part of the phase** (integer form): the phase
`e(-2πi (a/q) Q(·))` is invariant under `r ↦ p q + r`.  This is
`Commons.Analysis.ExponentialSums.exp_eval_div_eq_exp_eval_mod` converted from the `+2πi`
convention (with `a` replaced by `-a`) to the `-2πi` convention of `Work.A3.expSum`. -/
lemma exp_rat_phase_period (Q : Polynomial ℤ) (q : ℕ) (hq : 0 < q) (a : ℤ) (p r : ℤ) :
    Complex.exp (-(2 * Real.pi * Complex.I *
        (((a : ℝ) / (q : ℝ)) * ((Q.eval (p * (q : ℤ) + r) : ℤ) : ℝ))))
      = Complex.exp (-(2 * Real.pi * Complex.I *
        (((a : ℝ) / (q : ℝ)) * ((Q.eval r : ℤ) : ℝ)))) := by
  have h := Commons.Analysis.ExponentialSums.exp_eval_div_eq_exp_eval_mod Q q hq (-a) p r
  have hL : -(2 * Real.pi * Complex.I * (((a : ℝ) / (q : ℝ)) * ((Q.eval (p * (q : ℤ) + r) : ℤ) : ℝ)))
      = 2 * Real.pi * Complex.I * (((-a : ℂ) * ((Q.eval (p * (q : ℤ) + r) : ℤ) : ℂ)) / (q : ℂ)) := by
    push_cast
    field_simp
  have hR : -(2 * Real.pi * Complex.I * (((a : ℝ) / (q : ℝ)) * ((Q.eval r : ℤ) : ℝ)))
      = 2 * Real.pi * Complex.I * (((-a : ℂ) * ((Q.eval r : ℤ) : ℂ)) / (q : ℂ)) := by
    push_cast
    field_simp
  rw [hL, hR]
  simpa only [Int.cast_neg] using h

/-- **`q`-periodicity of the rational part of the phase** (natural form, for `n = r + p q`). -/
lemma exp_rat_phase_period_nat (Q : Polynomial ℤ) (q : ℕ) (hq : 0 < q) (a : ℤ) (p r : ℕ) :
    Complex.exp (-(2 * Real.pi * Complex.I *
        (((a : ℝ) / (q : ℝ)) * ((Q.eval ((r + p * q : ℕ) : ℤ) : ℤ) : ℝ))))
      = Complex.exp (-(2 * Real.pi * Complex.I *
        (((a : ℝ) / (q : ℝ)) * ((Q.eval (r : ℤ) : ℤ) : ℝ)))) := by
  have h1 : ((r + p * q : ℕ) : ℤ) = (p : ℤ) * (q : ℤ) + (r : ℤ) := by push_cast; ring
  rw [h1]
  exact exp_rat_phase_period Q q hq a (p : ℤ) (r : ℤ)

/-- Block decomposition of a polynomial Weyl sum into residue classes modulo `q` (in the regime `q ≤ N`, so every residue class `0 ≤ r < q` occurs at least once before `N`): writing `n = r + p*q` with `0 ≤ r < q` and `p < (N-r)/q + 1` covers `{0,1,…,N}` exactly once; removing the single `n = 0` term turns it into `expSum` over `Icc 1 N`, and the `a/q`-part of the phase is `q`-periodic (so it factors out of each block) while the `β`-part stays inside.  For the `q`-periodicity of the `a/q`-part one can use `Commons.Analysis.Polynomial.dvd_eval_sub_eval_mul` together with `Complex.exp_int_mul_two_pi_mul_I`, and `Commons.Analysis.ExponentialSums.exp_eval_div_eq_exp_eval_mod` is the ready-made version for the `+2πi` convention. -/
lemma expSum_block_split (Q : Polynomial ℤ) (N q : ℕ) (hq : 1 ≤ q) (hqN : q ≤ N) (a : ℤ) (β : ℝ) :
    Work.A3.expSum Q N ((a : ℝ) / (q : ℝ) + β)
      = (∑ r ∈ Finset.range q,
          Complex.exp (-(2 * Real.pi * Complex.I *
              (((a : ℝ) / (q : ℝ)) * (((Q.eval (r : ℤ) : ℤ) : ℝ)))))
            * (∑ p ∈ Finset.range ((N - r) / q + 1),
                Complex.exp (-(2 * Real.pi * Complex.I *
                  (β * (Work.A3.Qreal Q).eval ((r + p * q : ℕ) : ℝ))))))
        - Complex.exp (-(2 * Real.pi * Complex.I *
              (((a : ℝ) / (q : ℝ)) * (((Q.eval (0 : ℤ) : ℤ) : ℝ)))))
            * Complex.exp (-(2 * Real.pi * Complex.I *
              (β * (Work.A3.Qreal Q).eval 0))) := by
  have hq0 : 0 < q := hq
  set G : ℕ → ℂ := fun n => Complex.exp (-(2 * Real.pi * Complex.I *
      (((a : ℝ) / (q : ℝ)) * (((Q.eval (n : ℤ) : ℤ) : ℝ))))) with hG
  set H : ℕ → ℂ := fun n => Complex.exp (-(2 * Real.pi * Complex.I *
      (β * (Work.A3.Qreal Q).eval (n : ℝ)))) with hH
  -- the `a/q`-part factors out of each block
  have hper : ∀ (p r : ℕ), r < q → G (r + p * q) = G r := by
    intro p r hr
    rw [hG]
    exact exp_rat_phase_period_nat Q q hq0 a p r
  -- the summand splits as the product of the rational and the archimedean part
  have hLHS : expSum Q N ((a : ℝ) / (q : ℝ) + β) = ∑ n ∈ Finset.Icc 1 N, G n * H n := by
    simp only [expSum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [hG, hH, ← Complex.exp_add]
    congr 1
    push_cast
    rw [Qreal_eval_nat]
    simp only [Complex.ofReal_intCast]
    ring
  have hblocks := sum_range_eq_sum_blocks q N hq hqN (fun n => G n * H n)
  -- removing the `n = 0` term from `range (N+1)` leaves the sum over `Icc 1 N`
  have hIcc : (∑ n ∈ Finset.Icc 1 N, G n * H n)
      = (∑ n ∈ Finset.range (N + 1), G n * H n) - G 0 * H 0 := by
    have h1 := Finset.sum_range_succ' (fun n => G n * H n) N
    have h2 : (∑ k ∈ Finset.range N, G (k + 1) * H (k + 1))
        = ∑ n ∈ Finset.Icc 1 N, G n * H n :=
      (sum_Icc_one_eq_sum_range_nat N (fun n => G n * H n)).symm
    rw [h2] at h1
    exact eq_sub_iff_add_eq.mpr h1.symm
  -- the `a/q`-part is constant on each block, the `β`-part is not
  have hblock2 : (∑ r ∈ Finset.range q, ∑ p ∈ Finset.range ((N - r) / q + 1),
        G (r + p * q) * H (r + p * q))
      = (∑ r ∈ Finset.range q, G r * ∑ p ∈ Finset.range ((N - r) / q + 1),
          H (r + p * q)) := by
    refine Finset.sum_congr rfl (fun r hr => ?_)
    have hrq : r < q := Finset.mem_range.mp hr
    rw [Finset.sum_congr rfl (fun p _ => by rw [hper p r hrq]), Finset.mul_sum]
  calc expSum Q N ((a : ℝ) / (q : ℝ) + β)
      = ∑ n ∈ Finset.Icc 1 N, G n * H n := hLHS
    _ = (∑ n ∈ Finset.range (N + 1), G n * H n) - G 0 * H 0 := hIcc
    _ = (∑ r ∈ Finset.range q, ∑ p ∈ Finset.range ((N - r) / q + 1),
          G (r + p * q) * H (r + p * q)) - G 0 * H 0 := by rw [hblocks]
    _ = (∑ r ∈ Finset.range q, G r * ∑ p ∈ Finset.range ((N - r) / q + 1),
          H (r + p * q)) - G 0 * H 0 := by rw [hblock2]
    _ = (∑ r ∈ Finset.range q,
          Complex.exp (-(2 * Real.pi * Complex.I *
              (((a : ℝ) / (q : ℝ)) * (((Q.eval (r : ℤ) : ℤ) : ℝ)))))
            * (∑ p ∈ Finset.range ((N - r) / q + 1),
                Complex.exp (-(2 * Real.pi * Complex.I *
                  (β * (Work.A3.Qreal Q).eval ((r + p * q : ℕ) : ℝ))))))
        - Complex.exp (-(2 * Real.pi * Complex.I *
              (((a : ℝ) / (q : ℝ)) * (((Q.eval (0 : ℤ) : ℤ) : ℝ)))))
            * Complex.exp (-(2 * Real.pi * Complex.I *
              (β * (Work.A3.Qreal Q).eval 0))) := by
      simp only [hG, hH, Nat.cast_zero]

end

end Work.A3
