import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.pd_seriesFun
import Submission.Work.Diff.STE.integral_seriesFun_mul_conj
import Submission.Work.Diff.STE.one_add_sum_pow_le
import Submission.Work.Diff.STE.integral_normSq_seriesFun
import Submission.Work.Diff.STE.pdVec_const_seriesFun
import Submission.Work.Diff.STE.sum_integral_pdVec_const_le_ENormSq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `CSq_le_ENormSq_seriesFun`

Layer A of the STE development: for a coefficient family `c : (ι → ℤ) → ℂ` decaying faster
than every polynomial weight, the weighted `ℓ²`-norm

`CSq k c = Σ_m ⟨m⟩^{2k} ‖c m‖²`

of the coefficients is bounded by the physical energy of the series `u = seriesFun c`,

`CSq k c ≤ C (ENormSq k u + ENormSq 0 u)`,

with a constant depending only on `k` and `ι`.  This is the direction of the
coefficient ↔ energy comparison *not* covered by the sibling `ENormSq_seriesFun_le`.

The mechanism is that the pure `k`-th derivatives `∂ᵢ^k u` supply exactly the weights needed
to dominate `⟨m⟩^{2k} = (1 + Σᵢ mᵢ²)^k ≈ 1 + Σᵢ (mᵢ²)^k`:

* `integral_normSq_seriesFun` computes `∫_{unitCube} ‖seriesFun d‖² = Σ_m ‖d m‖²`, and
* `pdVec_const_seriesFun` writes `∂ᵢ^k (seriesFun c)` as the series of the coefficient family
  `dmulPow i k c`, whose `m`-th coefficient has modulus squared `((2π)² mᵢ²)^k · ‖c m‖²`
  (`norm_dmulPow_sq` below);

hence `ENormSq k u ≥ Σᵢ ∫ ‖∂ᵢ^k u‖² = Σ_m (Σᵢ ((2π)² mᵢ²)^k) ‖c m‖²`
(`sum_integral_pdVec_const_le_ENormSq` bounds the sub-sum by the full energy), and
`ENormSq 0 u = Σ_m ‖c m‖²` (`ENormSq_zero_seriesFun`).  The pointwise weight comparison
`(wt m)^k ≤ (card ι + 1)^k (1 + Σᵢ ((2π)² mᵢ²)^k)` is `one_add_sum_pow_le`
(`wt_pow_le_Rw` below); everything else is summability bookkeeping
(`summable_w_norm_sq` and its instantiations).
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The Fourier weight of a pure derivative -/

/-- The Fourier-side weight of the `k`-fold derivative in the direction `i`: `((2π)² mᵢ²)^k`.
This is exactly the squared modulus of the multiplier `(2πi mᵢ)^k` (`norm_dmulPow_sq`). -/
private def Rw (k : ℕ) (i : ι) (m : ι → ℤ) : ℝ :=
  ((2 * Real.pi)^2 * (((m i : ℤ) : ℝ)^2))^k

/-- `(a^k)^2 = (a^2)^k`: the exponent rewriting that converts the square of a `k`-th power
into the `k`-th power of the square. -/
private lemma pow_pow_two (a : ℝ) (k : ℕ) : (a^k)^2 = (a^2)^k := by
  rw [show (a^k)^2 = a^(k*2) from (pow_mul a k 2).symm,
    show (a^2)^k = a^(2*k) from (pow_mul a 2 k).symm,
    show k * 2 = 2 * k from Nat.mul_comm k 2]

private lemma Rw_nonneg (k : ℕ) (i : ι) (m : ι → ℤ) : 0 ≤ Rw k i m := by
  simp only [Rw]; positivity

/-- The coordinate `mᵢ²` is dominated by the weight `⟨m⟩² = wt m`. -/
private lemma sq_intCast_le_wt (m : ι → ℤ) (i : ι) : (((m i : ℤ) : ℝ)^2) ≤ wt m := by
  have h := Finset.single_le_sum (f := fun j : ι => (((m j : ℤ) : ℝ)^2))
    (fun j _ => sq_nonneg (((m j : ℤ) : ℝ))) (Finset.mem_univ i)
  simp only [wt]
  linarith

/-- The weight of one pure derivative in the direction `i` is at most
`(2π)^{2k} ⟨m⟩^{2k}`. -/
private lemma Rw_le (k : ℕ) (i : ι) (m : ι → ℤ) :
    Rw k i m ≤ (2 * Real.pi)^(2*k) * (wt m)^k := by
  calc Rw k i m ≤ ((2 * Real.pi)^2 * wt m)^k := by
        simp only [Rw]
        refine pow_le_pow_left₀ (by positivity) ?_ k
        exact mul_le_mul_of_nonneg_left (sq_intCast_le_wt m i) (by positivity)
    _ = (2 * Real.pi)^(2*k) * (wt m)^k := by
        rw [show ((2 * Real.pi)^2 * wt m)^k = ((2 * Real.pi)^2)^k * (wt m)^k from
              mul_pow ((2 * Real.pi)^2) (wt m) k,
            show ((2 * Real.pi)^2)^k = (2 * Real.pi)^(2*k) from (pow_mul (2 * Real.pi) 2 k).symm]

/-- `Σᵢ Rw k i m ≤ card ι · (2π)^{2k} ⟨m⟩^{2k}`. -/
private lemma sumRw_le (k : ℕ) (m : ι → ℤ) :
    (∑ i, Rw k i m) ≤ (Fintype.card ι : ℝ) * ((2 * Real.pi)^(2*k) * (wt m)^k) := by
  calc (∑ i, Rw k i m) ≤ ∑ _i : ι, (2 * Real.pi)^(2*k) * (wt m)^k :=
        Finset.sum_le_sum (fun i _ => Rw_le k i m)
    _ = (Fintype.card ι : ℝ) * ((2 * Real.pi)^(2*k) * (wt m)^k) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## Summability -/

/-- Weighted `ℓ¹` summability implies weighted `ℓ²` summability: the family `‖c m‖` is bounded
by its sum. -/
private lemma summable_w_norm_sq (c : (ι → ℤ) → ℂ) (w : (ι → ℤ) → ℝ) (hw : ∀ m, 0 ≤ w m)
    (hc : Summable (fun m : ι → ℤ => ‖c m‖))
    (hs : Summable (fun m : ι → ℤ => w m * ‖c m‖)) :
    Summable (fun m : ι → ℤ => w m * ‖c m‖^2) := by
  have hS : ∀ m : ι → ℤ, ‖c m‖ ≤ ∑' l : ι → ℤ, ‖c l‖ :=
    fun m => hc.le_tsum m (fun l _ => norm_nonneg (c l))
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (hw m) (sq_nonneg _)) (fun m => ?_)
    (hs.mul_left (∑' l : ι → ℤ, ‖c l‖))
  calc w m * ‖c m‖^2 = (w m * ‖c m‖) * ‖c m‖ := by ring
    _ ≤ (w m * ‖c m‖) * (∑' l : ι → ℤ, ‖c l‖) :=
        mul_le_mul_of_nonneg_left (hS m) (mul_nonneg (hw m) (norm_nonneg _))
    _ = (∑' l : ι → ℤ, ‖c l‖) * (w m * ‖c m‖) := by ring

private lemma summable_norm_sq (c : (ι → ℤ) → ℂ)
    (hc : ∀ N : ℕ, Summable (fun m : ι → ℤ => (wt m)^N * ‖c m‖)) :
    Summable (fun m : ι → ℤ => ‖c m‖^2) := by
  simpa using summable_w_norm_sq c (fun _ => 1) (fun _ => zero_le_one)
    (by simpa using hc 0) (by simpa using hc 0)

private lemma summable_wt_pow_mul_norm_sq (c : (ι → ℤ) → ℂ)
    (hc : ∀ N : ℕ, Summable (fun m : ι → ℤ => (wt m)^N * ‖c m‖)) (k : ℕ) :
    Summable (fun m : ι → ℤ => (wt m)^k * ‖c m‖^2) :=
  summable_w_norm_sq c (fun m => (wt m)^k) (fun m => pow_nonneg (le_of_lt (wt_pos m)) k)
    (by simpa using hc 0) (by simpa using hc k)

private lemma summable_Rw_mul_norm (c : (ι → ℤ) → ℂ)
    (hc : ∀ N : ℕ, Summable (fun m : ι → ℤ => (wt m)^N * ‖c m‖)) (k : ℕ) (i : ι) :
    Summable (fun m : ι → ℤ => Rw k i m * ‖c m‖) := by
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (Rw_nonneg k i m) (norm_nonneg _))
    (fun m => ?_) ((hc k).mul_left ((2 * Real.pi)^(2*k)))
  calc Rw k i m * ‖c m‖ ≤ ((2 * Real.pi)^(2*k) * (wt m)^k) * ‖c m‖ :=
        mul_le_mul_of_nonneg_right (Rw_le k i m) (norm_nonneg _)
    _ = (2 * Real.pi)^(2*k) * ((wt m)^k * ‖c m‖) := by ring

private lemma summable_Rw_mul_norm_sq (c : (ι → ℤ) → ℂ)
    (hc : ∀ N : ℕ, Summable (fun m : ι → ℤ => (wt m)^N * ‖c m‖)) (k : ℕ) (i : ι) :
    Summable (fun m : ι → ℤ => Rw k i m * ‖c m‖^2) :=
  summable_w_norm_sq c (fun m => Rw k i m) (fun m => Rw_nonneg k i m)
    (by simpa using hc 0) (summable_Rw_mul_norm c hc k i)

private lemma summable_sumRw_mul_norm (c : (ι → ℤ) → ℂ)
    (hc : ∀ N : ℕ, Summable (fun m : ι → ℤ => (wt m)^N * ‖c m‖)) (k : ℕ) :
    Summable (fun m : ι → ℤ => (∑ i, Rw k i m) * ‖c m‖) := by
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (Finset.sum_nonneg (fun i _ => Rw_nonneg k i m)) (norm_nonneg _))
    (fun m => ?_) ((hc k).mul_left ((Fintype.card ι : ℝ) * (2 * Real.pi)^(2*k)))
  calc (∑ i, Rw k i m) * ‖c m‖
      ≤ ((Fintype.card ι : ℝ) * ((2 * Real.pi)^(2*k) * (wt m)^k)) * ‖c m‖ :=
        mul_le_mul_of_nonneg_right (sumRw_le k m) (norm_nonneg _)
    _ = ((Fintype.card ι : ℝ) * (2 * Real.pi)^(2*k)) * ((wt m)^k * ‖c m‖) := by ring

private lemma summable_sumRw_mul_norm_sq (c : (ι → ℤ) → ℂ)
    (hc : ∀ N : ℕ, Summable (fun m : ι → ℤ => (wt m)^N * ‖c m‖)) (k : ℕ) :
    Summable (fun m : ι → ℤ => (∑ i, Rw k i m) * ‖c m‖^2) :=
  summable_w_norm_sq c (fun m => ∑ i, Rw k i m)
    (fun m => Finset.sum_nonneg (fun i _ => Rw_nonneg k i m)) (by simpa using hc 0)
    (summable_sumRw_mul_norm c hc k)

/-! ## The pointwise weight comparison -/

/-- `⟨m⟩^{2k} = (wt m)^k ≤ (card ι + 1)^k (1 + Σᵢ Rw k i m)`. -/
private lemma wt_pow_le_Rw (k : ℕ) (m : ι → ℤ) :
    (wt m)^k ≤ (((Fintype.card ι : ℕ) : ℝ) + 1)^k * (1 + ∑ i, Rw k i m) := by
  have hbase : wt m ≤ 1 + ∑ i, (2 * Real.pi)^2 * (((m i : ℤ) : ℝ)^2) := by
    have h1 : (1 : ℝ) ≤ (2 * Real.pi)^2 := by nlinarith [Real.pi_gt_three]
    have h2 : ∀ i, (((m i : ℤ) : ℝ)^2) ≤ (2 * Real.pi)^2 * (((m i : ℤ) : ℝ)^2) := by
      intro i
      nlinarith [sq_nonneg (((m i : ℤ) : ℝ))]
    simp only [wt]
    linarith [Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h2 i)]
  have hnn : (0 : ℝ) ≤ 1 + ∑ i, (2 * Real.pi)^2 * (((m i : ℤ) : ℝ)^2) := by
    have h : (0 : ℝ) ≤ ∑ i, (2 * Real.pi)^2 * (((m i : ℤ) : ℝ)^2) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    linarith
  calc (wt m)^k ≤ (1 + ∑ i, (2 * Real.pi)^2 * (((m i : ℤ) : ℝ)^2))^k :=
        pow_le_pow_left₀ (le_of_lt (wt_pos m)) hbase k
    _ ≤ (((Fintype.card ι : ℕ) : ℝ) + 1)^k
          * (1 + ∑ i, ((2 * Real.pi)^2 * (((m i : ℤ) : ℝ)^2))^k) :=
        one_add_sum_pow_le (fun i => (2 * Real.pi)^2 * (((m i : ℤ) : ℝ)^2))
          (fun _ => by positivity) k
    _ = (((Fintype.card ι : ℕ) : ℝ) + 1)^k * (1 + ∑ i, Rw k i m) := by
        simp only [Rw]

/-! ## The norms of the pure-derivative multipliers -/

/-- The squared modulus of the multiplier `(2πi mᵢ)^k` is the weight `Rw k i m`. -/
private lemma norm_base_sq (i : ι) (m : ι → ℤ) :
    ‖2 * Real.pi * Complex.I * (m i : ℂ)‖^2 = (2 * Real.pi)^2 * (((m i : ℤ) : ℝ)^2) := by
  have hb : ‖2 * Real.pi * Complex.I * (m i : ℂ)‖ = 2 * Real.pi * |((m i : ℤ) : ℝ)| := by
    have h1 : 2 * Real.pi * Complex.I * (m i : ℂ)
        = (((2 * Real.pi * ((m i : ℤ) : ℝ)) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h1, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  rw [hb, mul_pow, sq_abs]

/-- The coefficient family of `∂ᵢ^k (seriesFun c)` has squared modulus
`Rw k i m · ‖c m‖²` at the `m`-th coefficient. -/
private lemma norm_dmulPow_sq (i : ι) (k : ℕ) (c : (ι → ℤ) → ℂ) (m : ι → ℤ) :
    ‖dmulPow i k c m‖^2 = Rw k i m * ‖c m‖^2 := by
  rw [dmulPow, norm_mul, norm_pow, mul_pow, pow_pow_two, norm_base_sq]
  simp only [Rw]

/-- **The energy of the pure derivative `∂ᵢ^k`.** -/
private lemma integral_pdVec_const_eq (k : ℕ) (i : ι) (c : (ι → ℤ) → ℂ)
    (hc : ∀ N : ℕ, Summable (fun m : ι → ℤ => (wt m)^N * ‖c m‖)) :
    (∫ x in unitCube, ‖pdVec k (fun _ : Fin k => i) (seriesFun c) x‖^2)
      = ∑' m : ι → ℤ, Rw k i m * ‖c m‖^2 := by
  have hdec : Summable (fun m : ι → ℤ => ‖dmulPow i k c m‖) := by
    simpa using summable_dmulPow i c hc k 0
  rw [show (∫ x in unitCube, ‖pdVec k (fun _ : Fin k => i) (seriesFun c) x‖^2)
      = ∫ x in unitCube, ‖seriesFun (dmulPow i k c) x‖^2 from by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        have hpt : pdVec k (fun _ : Fin k => i) (seriesFun c) x = seriesFun (dmulPow i k c) x :=
          pdVec_const_seriesFun k i c hc x
        simp only [hpt]]
  rw [integral_normSq_seriesFun (dmulPow i k c) hdec]
  exact tsum_congr (fun m => norm_dmulPow_sq i k c m)

/-! ## The `H⁰` energy of a series -/

/-- The zeroth energy of a Fourier series is the `ℓ²` norm of its coefficients. -/
theorem ENormSq_zero_seriesFun (c : (ι → ℤ) → ℂ)
    (hc : Summable (fun m : ι → ℤ => ‖c m‖)) :
    ENormSq 0 (seriesFun c) = ∑' m : ι → ℤ, ‖c m‖^2 := by
  have hsum : (∑ l : Fin 0 → ι, ∫ x in unitCube, ‖pdVec 0 l (seriesFun c) x‖^2)
      = ∫ x in unitCube, ‖seriesFun c x‖^2 := by
    have hterm : ∀ l : Fin 0 → ι,
        (∫ x in unitCube, ‖pdVec 0 l (seriesFun c) x‖^2)
          = ∫ x in unitCube, ‖seriesFun c x‖^2 := by
      intro l
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp only [show pdVec 0 l (seriesFun c) x = seriesFun c x from by simp [pdVec, pdList]]
    rw [Finset.sum_congr rfl (fun l _ => hterm l), Finset.sum_const, Finset.card_univ,
      show Fintype.card (Fin 0 → ι) = 1 from by simp, one_smul]
  rw [ENormSq, hsum, integral_normSq_seriesFun c hc]

/-! ## The target -/

theorem CSq_le_ENormSq_seriesFun {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : (ι → ℤ) → ℂ,
      (∀ N : ℕ, Summable (fun l : ι → ℤ => (Work.Diff.STE.wt l) ^ N * ‖c l‖)) →
      Work.Diff.STE.CSq k c
        ≤ C * (Work.Diff.STE.ENormSq k (Work.Diff.STE.seriesFun c)
            + Work.Diff.STE.ENormSq 0 (Work.Diff.STE.seriesFun c)) := by
  classical
  refine ⟨(((Fintype.card ι : ℕ) : ℝ) + 1)^k, by positivity, fun c hc => ?_⟩
  have hE0 : ENormSq 0 (seriesFun c) = ∑' m : ι → ℤ, ‖c m‖^2 :=
    ENormSq_zero_seriesFun c (by simpa using hc 0)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- k = 0
    subst hk
    have hCSq : CSq 0 c = ∑' m : ι → ℤ, ‖c m‖^2 :=
      tsum_congr (fun m => by rw [pow_zero, one_mul])
    have hnn : 0 ≤ ∑' m : ι → ℤ, ‖c m‖^2 := tsum_nonneg (fun m => sq_nonneg _)
    rw [hCSq, hE0, pow_zero, one_mul]
    linarith
  · -- k ≥ 1
    -- the `CSq`-side: `(wt m)^k` against `1 + Σᵢ Rw k i m`
    have hCSq_le : CSq k c ≤ (((Fintype.card ι : ℕ) : ℝ) + 1)^k
        * ((∑' m : ι → ℤ, ‖c m‖^2)
            + ∑' m : ι → ℤ, (∑ i, Rw k i m) * ‖c m‖^2) := by
      have hsumL : Summable (fun m : ι → ℤ => (wt m)^k * ‖c m‖^2) :=
        summable_wt_pow_mul_norm_sq c hc k
      have hsumR : Summable (fun m : ι → ℤ => (((Fintype.card ι : ℕ) : ℝ) + 1)^k
          * (‖c m‖^2 + (∑ i, Rw k i m) * ‖c m‖^2)) :=
        (((summable_norm_sq c hc).add (summable_sumRw_mul_norm_sq c hc k))).mul_left _
      have hpt : ∀ m : ι → ℤ, (wt m)^k * ‖c m‖^2
          ≤ (((Fintype.card ι : ℕ) : ℝ) + 1)^k
              * (‖c m‖^2 + (∑ i, Rw k i m) * ‖c m‖^2) := by
        intro m
        calc (wt m)^k * ‖c m‖^2
            ≤ (((Fintype.card ι : ℕ) : ℝ) + 1)^k * (1 + ∑ i, Rw k i m) * ‖c m‖^2 :=
              mul_le_mul_of_nonneg_right (wt_pow_le_Rw k m) (sq_nonneg _)
          _ = (((Fintype.card ι : ℕ) : ℝ) + 1)^k
                * (‖c m‖^2 + (∑ i, Rw k i m) * ‖c m‖^2) := by ring
      calc CSq k c = ∑' m : ι → ℤ, (wt m)^k * ‖c m‖^2 := rfl
        _ ≤ ∑' m : ι → ℤ, (((Fintype.card ι : ℕ) : ℝ) + 1)^k
              * (‖c m‖^2 + (∑ i, Rw k i m) * ‖c m‖^2) :=
            Summable.tsum_le_tsum hpt hsumL hsumR
        _ = (((Fintype.card ι : ℕ) : ℝ) + 1)^k
              * ((∑' m : ι → ℤ, ‖c m‖^2)
                  + ∑' m : ι → ℤ, (∑ i, Rw k i m) * ‖c m‖^2) := by
            rw [Summable.tsum_mul_left _
                (((summable_norm_sq c hc).add (summable_sumRw_mul_norm_sq c hc k))),
              Summable.tsum_add (summable_norm_sq c hc) (summable_sumRw_mul_norm_sq c hc k)]
    -- the `ENormSq`-side
    have hβ_le : (∑' m : ι → ℤ, (∑ i, Rw k i m) * ‖c m‖^2) ≤ ENormSq k (seriesFun c) := by
      have hβsum : (∑' m : ι → ℤ, (∑ i, Rw k i m) * ‖c m‖^2)
          = ∑ i : ι, ∑' m : ι → ℤ, Rw k i m * ‖c m‖^2 := by
        have h := Summable.tsum_finsetSum (s := Finset.univ)
          (f := fun i (m : ι → ℤ) => Rw k i m * ‖c m‖^2)
          (fun i _ => summable_Rw_mul_norm_sq c hc k i)
        simpa [Finset.sum_mul] using h
      rw [hβsum]
      refine le_trans (le_of_eq ?_) (sum_integral_pdVec_const_le_ENormSq k hk c)
      exact Finset.sum_congr rfl (fun i _ => (integral_pdVec_const_eq k i c hc).symm)
    calc CSq k c
        ≤ (((Fintype.card ι : ℕ) : ℝ) + 1)^k
            * ((∑' m : ι → ℤ, ‖c m‖^2)
                + ∑' m : ι → ℤ, (∑ i, Rw k i m) * ‖c m‖^2) := hCSq_le
      _ ≤ (((Fintype.card ι : ℕ) : ℝ) + 1)^k
            * ((∑' m : ι → ℤ, ‖c m‖^2) + ENormSq k (seriesFun c)) := by
          exact mul_le_mul_of_nonneg_left (by linarith [hβ_le]) (by positivity)
      _ = (((Fintype.card ι : ℕ) : ℝ) + 1)^k
            * (ENormSq k (seriesFun c) + ENormSq 0 (seriesFun c)) := by
          rw [← hE0]; ring

end Work.Diff.STE
