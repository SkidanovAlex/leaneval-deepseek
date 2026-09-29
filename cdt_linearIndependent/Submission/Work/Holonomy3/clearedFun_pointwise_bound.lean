import Mathlib
import Submission.Work.Holonomy3.comp_defs

/-!
# Pointwise norm bound for the cleared composite `clearedFun`

This module proves the elementary estimate that the analytic STEP 3 of the fine holonomy bound
needs: at a point `z` with `‖z s‖ = 1` where the cleared composite does not vanish,

  `log ‖clearedFun Q ψ N P z‖ ≤ log H + log Nr + d·log m + d·log M
      + sup_{k ∈ K} ∑_s k_s · log ‖ψ_s(z_s)‖`,

with `H` a bound for the coefficients of the `Q_i`, `Nr` a bound for the sizes of their supports,
`m^d` the number of indices `i : Fin d → Fin m`, and `M` the bound on the pole-clearing factors
`N_{i,s}·∏_{i'≠i} P_{i',s}` along the unit circle.

The proof is the obvious term-by-term estimate:
`‖clearedFun‖ ≤ m^d · (H·Nr·max_{k∈K} ∏_s ‖ψ_s(z_s)‖^{k_s}) · M^d`,
followed by taking logarithms; the only subtlety is that `Real.log 0 = 0`, so one must
observe that the non-vanishing hypothesis forces the maximal monomial to be positive.
-/

namespace Work.Holonomy3

open scoped BigOperators

noncomputable section

/-- **Evaluation of a multivariable polynomial is bounded by the coefficient-wise monomial
bound.**  For `p : MvPolynomial σ ℂ` and `w : σ → ℂ`,
`‖p.eval w‖ ≤ ∑_{k ∈ support p} ‖coeff k p‖ · ∏_s ‖w s‖^{k_s}`. -/
lemma norm_eval_le_sum {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℂ) (w : σ → ℂ) :
    ‖p.eval w‖ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * ∏ s, ‖w s‖ ^ (k s) := by
  rw [MvPolynomial.eval_eq']
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun k hk => ?_
  rw [norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact Finset.prod_le_prod₀ (fun s _ => by positivity) (fun s _ => by rw [norm_pow])

/-- **The logarithm of a maximum of monomials is at most the maximum of the corresponding linear
forms.**  For a nonempty finite set `K` of exponent vectors and `a : Fin d → ℝ`, if the maximum
`Y = sup_{k∈K} ∏_s a_s^{k_s}` is positive then
`log Y ≤ sup_{k∈K} ∑_s k_s log(a_s)`.

Positivity of `Y` is essential: for `a = (0, 1/2)` and `k = (1,1)` one has
`log(∏_s a_s^{k_s}) = log 0 = 0 > log(1/2) = ∑_s k_s log a_s`; the maximum over `K` however is
attained at an index whose monomial is positive, where the identity `log(a^n) = n log a` holds
with the sum. -/
lemma log_sup'_prod_le_sup'_sum {d : ℕ} (K : Finset (Fin d →₀ ℕ)) (hKne : K.Nonempty)
    (a : Fin d → ℝ) (hYpos : 0 < K.sup' hKne (fun k => ∏ s, a s ^ (k s))) :
    Real.log (K.sup' hKne (fun k => ∏ s, a s ^ (k s))) ≤
      K.sup' hKne (fun k => ∑ s, (k s : ℝ) * Real.log (a s)) := by
  obtain ⟨k0, hk0mem, hk0⟩ := Finset.exists_mem_eq_sup' hKne (fun k => ∏ s, a s ^ (k s))
  rw [hk0]
  have hne : (∏ s, a s ^ (k0 s)) ≠ 0 := ne_of_gt (by rw [← hk0]; exact hYpos)
  rw [Real.log_prod (fun s _ => Finset.prod_ne_zero_iff.mp hne s (Finset.mem_univ s))]
  rw [Finset.sum_congr rfl (fun i _ => Real.log_pow (a i) (k0 i))]
  exact Finset.le_sup' (fun k => ∑ s, (k s : ℝ) * Real.log (a s)) hk0mem

theorem clearedFun_pointwise_bound {d m : ℕ} (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℂ)
    (ψ : Fin d → ℂ → ℂ) (N : Fin m → Fin d → ℂ → ℂ) (P : Fin m → Fin d → Polynomial ℂ)
    (H M Nr : ℝ) (hH : 1 ≤ H) (hM : 1 ≤ M) (hNr : 1 ≤ Nr) (hm : 1 ≤ m)
    (hNrc : ∀ i, ((Q i).support.card : ℝ) ≤ Nr)
    (hQc : ∀ i k, k ∈ (Q i).support → ‖(Q i).coeff k‖ ≤ H)
    (K : Finset (Fin d →₀ ℕ)) (hKne : K.Nonempty) (hK : ∀ i, (Q i).support ⊆ K)
    (hU : ∀ i s z, ‖z‖ = 1 → ‖N i s z * ∏ i' ∈ Finset.univ.erase i, (P i' s).eval z‖ ≤ M)
    (z : Fin d → ℂ) (hz : ∀ s, ‖z s‖ = 1) (hG0 : clearedFun Q ψ N P z ≠ 0) :
    Real.log ‖clearedFun Q ψ N P z‖ ≤ Real.log H + Real.log Nr + (d : ℝ) * Real.log m +
      (d : ℝ) * Real.log M +
      K.sup' hKne (fun k : Fin d →₀ ℕ => ∑ s : Fin d, (k s : ℝ) * Real.log ‖ψ s (z s)‖) := by
  -- The maximal monomial `Y = max_{k ∈ K} ∏_s ‖ψ_s(z_s)‖^{k_s}`.
  set Y : ℝ := K.sup' hKne (fun k : Fin d →₀ ℕ => ∏ s : Fin d, ‖ψ s (z s)‖ ^ (k s)) with hYdef
  have hHpos : (0:ℝ) < H := lt_of_lt_of_le zero_lt_one hH
  have hNrpos : (0:ℝ) < Nr := lt_of_lt_of_le zero_lt_one hNr
  -- `Y` is positive because some monomial of some `Q i` does not vanish at `ψ z`.
  have hYpos : 0 < Y := by
    obtain ⟨i, hi⟩ : ∃ i : Fin d → Fin m,
        (Q i).eval (fun s => ψ s (z s)) *
          ∏ s, (N (i s) s (z s) * ∏ i' ∈ Finset.univ.erase (i s), (P i' s).eval (z s)) ≠ 0 := by
      by_contra h
      apply hG0
      rw [clearedFun]
      exact Finset.sum_eq_zero (fun i _ => by_contra fun hfi => h ⟨i, hfi⟩)
    obtain ⟨hQne, -⟩ := mul_ne_zero_iff.mp hi
    rw [MvPolynomial.eval_eq'] at hQne
    obtain ⟨k, hk, hkne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQne
    have hprod : (∏ s, (ψ s (z s)) ^ (k s)) ≠ 0 := (mul_ne_zero_iff.mp hkne).2
    have hpos : 0 < ∏ s, ‖ψ s (z s)‖ ^ (k s) := by
      have h1 : (∏ s, ‖ψ s (z s)‖ ^ (k s)) = ‖∏ s, (ψ s (z s)) ^ (k s)‖ := by
        rw [norm_prod]
        exact Finset.prod_congr rfl (fun s _ => (norm_pow _ _).symm)
      rw [h1]
      exact norm_pos_iff.mpr hprod
    calc (0:ℝ) < ∏ s, ‖ψ s (z s)‖ ^ (k s) := hpos
      _ ≤ Y := by
          rw [hYdef]
          exact Finset.le_sup' (fun k => ∏ s, ‖ψ s (z s)‖ ^ (k s)) (hK i hk)
  -- Bound for a single `Q i` evaluated at `ψ z`.
  have hper : ∀ i : Fin d → Fin m, ‖(Q i).eval (fun s => ψ s (z s))‖ ≤ H * Nr * Y := by
    intro i
    refine le_trans (norm_eval_le_sum (Q i) (fun s => ψ s (z s))) ?_
    calc ∑ k ∈ (Q i).support, ‖(Q i).coeff k‖ * ∏ s, ‖ψ s (z s)‖ ^ (k s)
        ≤ ∑ _k ∈ (Q i).support, (H * Y) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have h1 := hQc i k hk
          have h2 : (∏ s, ‖ψ s (z s)‖ ^ (k s)) ≤ Y := by
            rw [hYdef]
            exact Finset.le_sup' (fun k => ∏ s, ‖ψ s (z s)‖ ^ (k s)) (hK i hk)
          exact mul_le_mul h1 h2 (by positivity) (le_trans (norm_nonneg _) h1)
      _ = ((Q i).support.card : ℝ) * (H * Y) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Nr * (H * Y) := mul_le_mul_of_nonneg_right (hNrc i) (by positivity)
      _ = H * Nr * Y := by ring
  -- Bound for the pole-clearing product, using `hU` on the unit circle.
  have hMprod : ∀ i : Fin d → Fin m,
      ‖∏ s, (N (i s) s (z s) * ∏ i' ∈ Finset.univ.erase (i s), (P i' s).eval (z s))‖ ≤ M ^ d := by
    intro i
    rw [norm_prod]
    calc ∏ s, ‖N (i s) s (z s) * ∏ i' ∈ Finset.univ.erase (i s), (P i' s).eval (z s)‖
        ≤ ∏ _s : Fin d, M :=
          Finset.prod_le_prod₀ (fun s _ => norm_nonneg _)
            (fun s _ => hU (i s) s (z s) (hz s))
      _ = M ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- The main estimate.
  have hmain : ‖clearedFun Q ψ N P z‖ ≤ (m:ℝ)^d * (H * Nr * Y) * M^d := by
    rw [clearedFun]
    refine le_trans (norm_sum_le _ _) ?_
    have hnonneg : 0 ≤ H * Nr * Y := by positivity
    calc ∑ i, ‖(Q i).eval (fun s => ψ s (z s)) *
            ∏ s, (N (i s) s (z s) * ∏ i' ∈ Finset.univ.erase (i s), (P i' s).eval (z s))‖
        ≤ ∑ _i : Fin d → Fin m, (H * Nr * Y) * M^d := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul]
          exact mul_le_mul (hper i) (hMprod i) (norm_nonneg _) hnonneg
      _ = (m:ℝ)^d * ((H * Nr * Y) * M^d) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      _ = (m:ℝ)^d * (H * Nr * Y) * M^d := by ring
  -- Expand the logarithm of the bound.
  have hexp : Real.log ((m:ℝ)^d * (H * Nr * Y) * M^d) =
      (d:ℝ) * Real.log m + (Real.log H + Real.log Nr + Real.log Y) + (d:ℝ) * Real.log M := by
    have hmne : (m:ℝ)^d ≠ 0 := by positivity
    have hMne : M^d ≠ 0 := by positivity
    have hYne : Y ≠ 0 := ne_of_gt hYpos
    rw [Real.log_mul (mul_ne_zero hmne (by positivity)) hMne, Real.log_mul hmne (by positivity),
      Real.log_mul (by positivity : H * Nr ≠ 0) hYne,
      Real.log_mul (ne_of_gt hHpos) (ne_of_gt hNrpos), Real.log_pow, Real.log_pow]
  -- Compare `log Y` with the sup of the linear forms.
  have hlsup : Real.log Y ≤ K.sup' hKne (fun k : Fin d →₀ ℕ =>
      ∑ s : Fin d, (k s : ℝ) * Real.log ‖ψ s (z s)‖) := by
    rw [hYdef]
    exact log_sup'_prod_le_sup'_sum K hKne (fun s => ‖ψ s (z s)‖)
      (by rw [← hYdef]; exact hYpos)
  have h1 : Real.log ‖clearedFun Q ψ N P z‖ ≤
      (d:ℝ) * Real.log m + (Real.log H + Real.log Nr + Real.log Y) + (d:ℝ) * Real.log M := by
    rw [← hexp]
    exact Real.log_le_log (norm_pos_iff.mpr hG0) hmain
  linarith [h1, hlsup]

end

end Work.Holonomy3
