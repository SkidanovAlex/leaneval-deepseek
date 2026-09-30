import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open Polynomial Finset Real MeasureTheory

open scoped BigOperators

/-!
# Summation by parts for the weight `φ(t) = 1/(t log t)`

We prove `Work.BMF.liouville.abel_step_twist`: for `2 ≤ N ≤ M` and any `a : ℕ → ℂ`,
```
∑_{n ∈ [N,M]} a_n /(n log n) = A(M)·1/(M log M) − A(N−1)·1/(N log N)
    + ∫_N^M A(t) (log t + 1)/(t log t)² dt,
```
where `A(t) = ∑_{1 ≤ j ≤ ⌊t⌋₊} a_j`.

The proof applies Mathlib's Abel summation formula (`sum_mul_eq_sub_sub_integral_mul`) with the
complexified weight `Wc t = ((1/(t log t) : ℝ) : ℂ)`, the lower limit `a = N` (so that the weight
is differentiable on the whole interval, `N ≥ 2 > 1`) and the upper limit `b = M`, together with
the sequence `cseq a` obtained from `a` by setting the `0`-th term to `0` (so that the prefix sums
`∑_{k ∈ Icc 0 m} cseq a k` are exactly `A(m)`).  The single extra term `a_N · φ(N)` produced by
using the lower limit `N` instead of `N - 1` is then absorbed by the `A(N) = A(N−1) + a_N` term.
-/

/-- The weight `φ(t) = 1/(t log t)`, as a real-valued function. -/
private noncomputable def phiW (t : ℝ) : ℝ := 1 / (t * Real.log t)

/-- The (negative of the) derivative of `phiW`, i.e. `(log t + 1)/(t log t)²`. -/
private noncomputable def dphiW (t : ℝ) : ℝ := (Real.log t + 1) / (t * Real.log t) ^ 2

/-- The complexified weight. -/
private noncomputable def Wc (t : ℝ) : ℂ := ((phiW t : ℝ) : ℂ)

/-- The prefix sums `A(n) = ∑_{1 ≤ j ≤ n} a_j`. -/
private noncomputable def AWn (a : ℕ → ℂ) (n : ℕ) : ℂ := ∑ j ∈ Finset.Icc 1 n, a j

/-- The step function `A(t) = ∑_{1 ≤ j ≤ ⌊t⌋₊} a_j`. -/
private noncomputable def AWr (a : ℕ → ℂ) (t : ℝ) : ℂ := ∑ j ∈ Finset.Icc 1 ⌊t⌋₊, a j

/-- `a` with its `0`-th term replaced by `0`; used so that prefix sums starting at `0` agree with
those starting at `1`. -/
private noncomputable def cseq (a : ℕ → ℂ) : ℕ → ℂ := fun k => if k = 0 then 0 else a k

/-- The derivative of `φ(t) = 1/(t log t)` for `t > 1`. -/
private lemma hasDerivAt_phiW (t : ℝ) (ht : 1 < t) : HasDerivAt phiW (-(dphiW t)) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have hmul : HasDerivAt (fun s : ℝ => s * Real.log s) (Real.log t + 1) t := by
    have h1 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have h2 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht0
    have h := h1.mul h2
    simp only [one_mul] at h
    convert h using 1
    field_simp
  have hinv : HasDerivAt (fun s : ℝ => (s * Real.log s)⁻¹)
      (-(Real.log t + 1) / (t * Real.log t) ^ 2) t := hmul.inv (mul_ne_zero ht0 hlt)
  have hphi : phiW = fun s : ℝ => (s * Real.log s)⁻¹ := by
    funext s; rw [phiW, one_div]
  rw [hphi]
  simpa only [dphiW, ← neg_div] using hinv

/-- The prefix sums of `cseq a` starting at `0` coincide with those of `a` starting at `1`. -/
private lemma sum0 (a : ℕ → ℂ) (m : ℕ) : ∑ k ∈ Finset.Icc 0 m, cseq a k = AWn a m := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le m), Finset.sum_cons]
  rw [show Finset.Ioc 0 m = Finset.Icc 1 m from (Finset.Icc_add_one_left_eq_Ioc 0 m).symm]
  rw [show cseq a 0 = 0 from rfl, zero_add, AWn]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mem_Icc] at hx
  simp [cseq, show x ≠ 0 by omega]

/-- Summation by parts with the weight `φ(t) = 1/(t log t)` against the step function
`A(t) = Σ_{1 ≤ j ≤ ⌊t⌋₊} a_j`: for `2 ≤ N ≤ M`,
`Σ_{n ∈ [N,M]} a_n φ(n) = A(M) φ(M) − A(N−1) φ(N) + ∫_N^M A(t) (log t + 1)/(t log t)² dt`.
Route: the discrete identity
`Σ_{n=N}^M a_n φ(n) = A(M)φ(M) − A(N−1)φ(N) + Σ_{n=N}^{M−1} A(n)(φ(n) − φ(n+1))`,
and for each `n` the term `A(n)(φ(n) − φ(n+1)) = −A(n) ∫_n^{n+1} φ'` by the fundamental FTC
identity (`φ'(t) = −(log t + 1)/(t log t)²`, valid for `t ≥ 2 > 1`), while `A` is constant on
`[n, n+1)`; summing over `n` gives the integral of the step function. -/
theorem abel_step_twist (a : ℕ → ℂ) (N M : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Icc N M, a n * ((1 / ((n : ℝ) * Real.log n) : ℝ) : ℂ)) =
      (∑ j ∈ Finset.Icc 1 M, a j) * ((1 / ((M : ℝ) * Real.log M) : ℝ) : ℂ) -
        (∑ j ∈ Finset.Icc 1 (N - 1), a j) * ((1 / ((N : ℝ) * Real.log N) : ℝ) : ℂ) +
        ∫ t in (N : ℝ)..(M : ℝ), (∑ j ∈ Finset.Icc 1 ⌊t⌋₊, a j) *
          (((Real.log t + 1) / (t * Real.log t) ^ 2 : ℝ) : ℂ) := by
  have hR2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hRNM : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
  -- The complexified weight is differentiable on `[N, M]` with derivative `-dphiW`.
  have hderiv : ∀ t ∈ Set.Icc (N : ℝ) (M : ℝ), HasDerivAt Wc ((-(dphiW t) : ℝ) : ℂ) t := by
    intro t ht
    exact (hasDerivAt_phiW t (by have := ht.1; linarith)).ofReal_comp
  have hdiff : ∀ t ∈ Set.Icc (N : ℝ) (M : ℝ), DifferentiableAt ℝ Wc t :=
    fun t ht => (hderiv t ht).differentiableAt
  -- Its derivative is integrable on `[N, M]` (it agrees there with a continuous function).
  have hint : IntegrableOn (deriv Wc) (Set.Icc (N : ℝ) (M : ℝ)) := by
    have hEq : Set.EqOn (fun t => ((-(dphiW t) : ℝ) : ℂ)) (deriv Wc) (Set.Icc (N : ℝ) (M : ℝ)) :=
      fun t ht => ((hderiv t ht).deriv).symm
    have hlog : ContinuousOn Real.log (Set.Icc (N : ℝ) (M : ℝ)) :=
      Real.continuousOn_log.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have h2t : (2 : ℝ) ≤ t := le_trans hR2 ht.1
        linarith)
    have htne : ∀ t ∈ Set.Icc (N : ℝ) (M : ℝ), (t * Real.log t) ^ 2 ≠ 0 := by
      intro t ht
      have h2t : (2 : ℝ) ≤ t := le_trans hR2 ht.1
      exact pow_ne_zero 2 (mul_ne_zero (by linarith) (ne_of_gt (Real.log_pos (by linarith))))
    have hd : ContinuousOn (fun t : ℝ => (Real.log t + 1) / (t * Real.log t) ^ 2)
        (Set.Icc (N : ℝ) (M : ℝ)) :=
      (hlog.add continuousOn_const).div ((continuousOn_id.mul hlog).pow 2) htne
    have hcont : ContinuousOn (fun t => ((-(dphiW t) : ℝ) : ℂ)) (Set.Icc (N : ℝ) (M : ℝ)) :=
      Complex.continuous_ofReal.comp_continuousOn hd.neg
    exact (hcont.integrableOn_compact isCompact_Icc).congr_fun hEq measurableSet_Icc
  -- Mathlib's Abel summation formula with lower limit `N` and upper limit `M`.
  have habel := sum_mul_eq_sub_sub_integral_mul (cseq a) (f := Wc) (a := (N : ℝ)) (b := (M : ℝ))
    (by linarith) hRNM hdiff hint
  rw [Nat.floor_natCast, Nat.floor_natCast] at habel
  have hbase : ∑ k ∈ Finset.Ioc N M, Wc (k : ℝ) * cseq a k
      = Wc (M : ℝ) * AWn a M - Wc (N : ℝ) * AWn a N
        - ∫ t in Set.Ioc (N : ℝ) (M : ℝ), deriv Wc t * AWr a t := by
    have hcongr : (∫ t in Set.Ioc (N : ℝ) (M : ℝ), deriv Wc t * ∑ k ∈ Icc 0 ⌊t⌋₊, cseq a k)
        = ∫ t in Set.Ioc (N : ℝ) (M : ℝ), deriv Wc t * AWr a t :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => by rw [sum0]; rfl)
    rw [habel, sum0, sum0, hcongr]
  -- Relate the sum over `Ioc N M` to the sum over `Icc N M`.
  have hLrel : (∑ n ∈ Finset.Icc N M, a n * Wc (n : ℝ))
      = a N * Wc (N : ℝ) + ∑ k ∈ Finset.Ioc N M, Wc (k : ℝ) * cseq a k := by
    rw [Finset.Icc_eq_cons_Ioc hNM, Finset.sum_cons]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Ioc] at hk
    have hk0 : k ≠ 0 := by omega
    rw [show cseq a k = a k from by simp [cseq, hk0]]
    ring
  -- The integral of `deriv Wc · A` is the negative of the integral appearing in the statement.
  have hintrel : ∫ t in Set.Ioc (N : ℝ) (M : ℝ), deriv Wc t * AWr a t
      = - ∫ t in (N : ℝ)..(M : ℝ), AWr a t * ((dphiW t : ℝ) : ℂ) := by
    have h1 : ∫ t in Set.Ioc (N : ℝ) (M : ℝ), deriv Wc t * AWr a t
        = ∫ t in Set.Ioc (N : ℝ) (M : ℝ), -(AWr a t * ((dphiW t : ℝ) : ℂ)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      show deriv Wc t * AWr a t = -(AWr a t * ((dphiW t : ℝ) : ℂ))
      rw [(hderiv t ⟨le_of_lt ht.1, ht.2⟩).deriv]
      push_cast
      ring
    rw [h1, MeasureTheory.integral_neg]
    congr 1
    exact (intervalIntegral.integral_of_le hRNM).symm
  have hA1N : AWn a N = AWn a (N - 1) + a N := by
    have h := Finset.sum_Icc_succ_top (a := 1) (b := N - 1) (by omega : 1 ≤ N - 1 + 1) a
    rwa [show N - 1 + 1 = N by omega] at h
  calc (∑ n ∈ Finset.Icc N M, a n * Wc (n : ℝ))
      = a N * Wc (N : ℝ) + ∑ k ∈ Finset.Ioc N M, Wc (k : ℝ) * cseq a k := hLrel
    _ = a N * Wc (N : ℝ) + (Wc (M : ℝ) * AWn a M - Wc (N : ℝ) * AWn a N
          - ∫ t in Set.Ioc (N : ℝ) (M : ℝ), deriv Wc t * AWr a t) := by rw [hbase]
    _ = Wc (M : ℝ) * AWn a M - Wc (N : ℝ) * AWn a (N - 1)
          + ∫ t in (N : ℝ)..(M : ℝ), AWr a t * ((dphiW t : ℝ) : ℂ) := by
        rw [hA1N, hintrel]; ring_nf
    _ = (∑ j ∈ Finset.Icc 1 M, a j) * ((1 / ((M : ℝ) * Real.log M) : ℝ) : ℂ) -
          (∑ j ∈ Finset.Icc 1 (N - 1), a j) * ((1 / ((N : ℝ) * Real.log N) : ℝ) : ℂ) +
          ∫ t in (N : ℝ)..(M : ℝ), (∑ j ∈ Finset.Icc 1 ⌊t⌋₊, a j) *
            (((Real.log t + 1) / (t * Real.log t) ^ 2 : ℝ) : ℂ) := by
        simp only [Wc, phiW, AWn, AWr, dphiW]
        ring

end Work.BMF.liouville
