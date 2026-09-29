import Mathlib
import Submission.Work.Holonomy3.siegelDefs
import Submission.Work.Holonomy3.lcmUpto_log_le

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

variable {m r : ℕ} {b : Fin m → Fin r → ℕ} {e : Fin m → ℕ} {f : Fin m → PowerSeries ℚ}
  {hden : ∀ i : Fin m, Submission.CDTPlan.HasDenomType (e i) (b i) (f i)}

/-- The clearing factor `clearFac C N` is positive. -/
lemma clearFac_pos (C : DenData b e f hden) (N : ℕ) : 0 < clearFac C N := by
  unfold clearFac
  have h3 : 0 < ∏ j : Fin r, lcmUpto (C.bmax j * N + C.cmax) :=
    Finset.prod_pos (fun j _ => Nat.lcmUpto_pos _)
  have h2 : 0 < (lcmUpto N) ^ C.Emax := pow_pos (Nat.lcmUpto_pos N) _
  have h1 : 0 < C.Kmax := C.hKmax
  positivity

/-- `clearFac` is monotone in its argument. -/
lemma clearFac_mono (C : DenData b e f hden) {M N : ℕ} (h : M ≤ N) :
    clearFac C M ≤ clearFac C N := by
  unfold clearFac
  refine Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) ?_) ?_
  · exact Nat.pow_le_pow_left (Nat.le_of_dvd (Nat.lcmUpto_pos N) (lcmUpto_dvd' h)) _
  · refine Finset.prod_le_prod₀ (fun j _ => Nat.zero_le _) (fun j _ => ?_)
    exact Nat.le_of_dvd (Nat.lcmUpto_pos _)
      (lcmUpto_dvd' (Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _))

/-- The exact logarithm of the clearing factor. -/
lemma log_clearFac_eq (C : DenData b e f hden) (N : ℕ) :
    Real.log (clearFac C N) =
      Real.log (C.Kmax : ℝ) + (C.Emax : ℝ) * Real.log ((lcmUpto N : ℕ) : ℝ)
      + ∑ j : Fin r, Real.log ((lcmUpto (C.bmax j * N + C.cmax) : ℕ) : ℝ) := by
  have hKmaxpos : (0:ℝ) < (C.Kmax : ℝ) := by have := C.hKmax; positivity
  have hpowne : ((lcmUpto N : ℕ) : ℝ) ^ C.Emax ≠ 0 := by
    have : (0:ℝ) < ((lcmUpto N : ℕ) : ℝ) := by exact_mod_cast (Nat.lcmUpto_pos N)
    positivity
  have hprodne : (∏ j : Fin r, ((lcmUpto (C.bmax j * N + C.cmax) : ℕ) : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact_mod_cast (Nat.lcmUpto_pos _).ne'
  rw [clearFac]
  push_cast
  rw [Real.log_mul (by positivity) (by exact hprodne),
      Real.log_mul (ne_of_gt hKmaxpos) hpowne,
      Real.log_pow, Real.log_prod (fun j _ => by exact_mod_cast (Nat.lcmUpto_pos _).ne')]

/-- **Growth of the clearing factor.** `Nc · clearFac C N · A^N` grows at most exponentially in `N`,
uniformly in `N`: the Chebyshev/PNT input `lcmUpto_log_le` bounds `log (lcmUpto ·)`. -/
lemma clearFac_exp_growth_aux (C : DenData b e f hden) {A : ℝ} (hA : 1 ≤ A) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ N : ℕ,
      ((C.Nc : ℝ) * (clearFac C N : ℝ)) * A ^ N ≤
        Real.exp (c * ((N : ℝ) + 1)) := by
  obtain ⟨K, hK⟩ := lcmUpto_log_le 1 (by norm_num)
  set K' : ℝ := max K 0 with hK'def
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hKK' : K ≤ K' := le_max_left _ _
  have hKbound : ∀ M : ℕ, Real.log ((lcmUpto M : ℕ) : ℝ) ≤ 2 * (M : ℝ) + K' := by
    intro M; have := hK M; linarith
  have hEmax0 : 0 ≤ (C.Emax : ℝ) := Nat.cast_nonneg _
  have hcm0 : 0 ≤ (C.cmax : ℝ) := Nat.cast_nonneg _
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
  have hKmaxlog : 0 ≤ Real.log (C.Kmax : ℝ) := Real.log_nonneg (by exact_mod_cast C.hKmax)
  have hNclog : 0 ≤ Real.log (C.Nc : ℝ) := Real.log_nonneg (by exact_mod_cast C.hNc)
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA
  have hSb0 : 0 ≤ ∑ j : Fin r, (C.bmax j : ℝ) :=
    Finset.sum_nonneg (fun j _ => Nat.cast_nonneg _)
  have hC20 : 0 ≤ Real.log (C.Kmax:ℝ) + (C.Emax:ℝ)*K' + (r:ℝ)*(2*(C.cmax:ℝ) + K') := by
    have h1 : 0 ≤ (C.Emax:ℝ)*K' := mul_nonneg hEmax0 hK'0
    have h2 : 0 ≤ (r:ℝ)*(2*(C.cmax:ℝ) + K') := mul_nonneg hr0 (by linarith)
    linarith
  let c₀ : ℝ := 2*(C.Emax:ℝ) + 2*(∑ j : Fin r, (C.bmax j : ℝ))
    + (Real.log (C.Kmax:ℝ) + (C.Emax:ℝ)*K' + (r:ℝ)*(2*(C.cmax:ℝ) + K'))
    + Real.log A + Real.log (C.Nc:ℝ)
  refine ⟨c₀, ?_, ?_⟩
  · dsimp only [c₀]
    nlinarith [hEmax0, hSb0, hC20, hlogA0, hNclog]
  · intro N
    have hNcpos : (0:ℝ) < (C.Nc : ℝ) := by have := C.hNc; positivity
    have hcfpos : (0:ℝ) < (clearFac C N : ℝ) := by exact_mod_cast (clearFac_pos C N)
    have hApos : (0:ℝ) < A := by linarith
    have hN0 : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    have hsum : (∑ j : Fin r, Real.log ((lcmUpto (C.bmax j * N + C.cmax) : ℕ) : ℝ))
        ≤ 2 * (∑ j : Fin r, (C.bmax j : ℝ)) * (N:ℝ)
          + (r:ℝ) * (2*(C.cmax:ℝ) + K') := by
      have hsum_eq : (∑ j : Fin r, (2 * (((C.bmax j : ℝ) * (N:ℝ)) + (C.cmax : ℝ)) + K'))
          = 2 * (∑ j : Fin r, (C.bmax j : ℝ)) * (N:ℝ)
            + (r:ℝ) * (2*(C.cmax:ℝ) + K') := by
        have h1 : (∑ j : Fin r, (2 * (((C.bmax j : ℝ) * (N:ℝ)) + (C.cmax : ℝ)) + K'))
            = ∑ j : Fin r,
                ((2*(N:ℝ)) * (C.bmax j : ℝ) + (2*((C.cmax : ℕ):ℝ) + K')) := by
          apply Finset.sum_congr rfl; intro j _; ring
        rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      calc (∑ j : Fin r, Real.log ((lcmUpto (C.bmax j * N + C.cmax) : ℕ) : ℝ))
          ≤ ∑ j : Fin r, (2 * (((C.bmax j : ℝ) * (N:ℝ)) + (C.cmax : ℝ)) + K') := by
            apply Finset.sum_le_sum
            intro j _
            have hj := hKbound (C.bmax j * N + C.cmax)
            have hcast : (((C.bmax j * N + C.cmax : ℕ)) : ℝ)
                = (C.bmax j : ℝ) * (N:ℝ) + (C.cmax : ℝ) := by push_cast; ring
            linarith [hj]
        _ = 2 * (∑ j : Fin r, (C.bmax j : ℝ)) * (N:ℝ)
              + (r:ℝ) * (2*(C.cmax:ℝ) + K') := hsum_eq
    have hcf : Real.log (clearFac C N) ≤ 2*(C.Emax:ℝ)*(N:ℝ)
        + 2*(∑ j : Fin r, (C.bmax j : ℝ))*(N:ℝ)
        + (Real.log (C.Kmax:ℝ) + (C.Emax:ℝ)*K' + (r:ℝ)*(2*(C.cmax:ℝ) + K')) := by
      rw [log_clearFac_eq C N]
      have hN := hKbound N
      have h2 := mul_le_mul_of_nonneg_left hN hEmax0
      linarith [hsum, h2]
    have hlogLHS : Real.log (((C.Nc:ℝ) * (clearFac C N:ℝ)) * A^N)
        = Real.log (C.Nc:ℝ) + Real.log (clearFac C N : ℝ) + (N:ℝ)*Real.log A := by
      rw [Real.log_mul (mul_ne_zero (ne_of_gt hNcpos) (ne_of_gt hcfpos))
            (pow_ne_zero _ (ne_of_gt hApos)),
          Real.log_mul (ne_of_gt hNcpos) (ne_of_gt hcfpos), Real.log_pow]
    have hmain : Real.log (((C.Nc:ℝ) * (clearFac C N:ℝ)) * A^N) ≤ c₀ * ((N:ℝ) + 1) := by
      rw [hlogLHS]
      dsimp only [c₀]
      nlinarith [hcf, hC20, hKmaxlog, hEmax0, hSb0, hlogA0, hNclog, hN0, hK'0, hr0, hcm0]
    have hpos : (0:ℝ) < ((C.Nc:ℝ) * (clearFac C N : ℝ)) * A^N :=
      mul_pos (mul_pos hNcpos hcfpos) (pow_pos hApos _)
    calc ((C.Nc:ℝ) * (clearFac C N : ℝ)) * A^N
        = Real.exp (Real.log (((C.Nc:ℝ) * (clearFac C N:ℝ)) * A^N)) :=
          (Real.exp_log hpos).symm
      _ ≤ Real.exp (c₀ * ((N : ℝ) + 1)) := Real.exp_le_exp.mpr hmain

/-- **Absolute value of a cleared coefficient.** The integer `cFac C i N n` (the `n`-th coefficient
of species `i`, cleared by `Nc · clearFac C N` when `n ≤ N`) is bounded by
`Nc · clearFac C N · A^n` under the growth hypothesis. -/
lemma cFac_abs_le (C : DenData b e f hden) {A : ℝ}
    (hgr : ∀ i n, ‖((PowerSeries.coeff n (f i) : ℚ) : ℝ)‖ ≤ A ^ n) :
    ∀ (i : Fin m) (N n : ℕ), n ≤ N →
      |((cFac C i N n : ℤ) : ℝ)| ≤ (C.Nc : ℝ) * (clearFac C N : ℝ) * A ^ n := by
  intro i N n hn
  have hcast : ((cFac C i N n : ℤ) : ℝ) = ((cFac C i N n : ℚ) : ℝ) := by
    push_cast; ring
  rw [hcast, cFac_spec C i hn]
  push_cast
  have h1 : (0:ℝ) ≤ ((C.Nc : ℕ) : ℝ) * ((clearFac C N : ℕ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [abs_mul, abs_of_nonneg h1]
  have hNcfpos : (0:ℝ) < ((C.Nc : ℕ) : ℝ) * ((clearFac C N : ℕ) : ℝ) := by
    have := C.hNc
    have h := clearFac_pos C N
    positivity
  exact mul_le_mul_of_nonneg_left (hgr i n) (le_of_lt hNcfpos)

/-- **Height bound for the linear system.** The integer entries `Work.Holonomy3.matEntry C v p` of
the box-principle linear system (the row multiplier `rowFac C v` times `∏_s [x_s^{v_s-k_s}] f_{i_s}`)
grow at most like `exp (C₀ d N)` when the row index `v` is bounded coordinatewise by `N`.

Route: `|matEntry| ≤ ∏_s Nc · clearFac (v s) · A^{v s}` by `Work.Holonomy3.cFac_spec` (the rational
value of the entry is the row multiplier times `∏_s coeff`, whose absolute value is at most
`A^{Σ v s}` by the growth hypothesis `hgr`); then take logarithms and use
`Work.Holonomy3.lcmUpto_log_le` (`log (lcmUpto M) ≤ (1+η) M + K`, with e.g. `η = 1`) to bound
`log (clearFac N) = log Kmax + Emax log (lcmUpto N) + Σ_j log (lcmUpto (bmax j · N + cmax))` by
`(Emax + Σ_j bmax j) ·(2N) + const`, and `Σ_s v s ≤ d N`; the constant `C₀` collects the
data-dependent terms and the `+d` slack absorbs the additive constants. Note `clearFac` is monotone
in its argument (it is built from `lcmUpto` and products), and `cFac_spec` needs `n ≤ N` with
`n := v s - p.2 s`. -/
theorem matEntry_bound {m r : ℕ} (b : Fin m → Fin r → ℕ) (e : Fin m → ℕ)
    (f : Fin m → PowerSeries ℚ)
    (hden : ∀ i : Fin m, Submission.CDTPlan.HasDenomType (e i) (b i) (f i))
    (C : Work.Holonomy3.DenData b e f hden) {A : ℝ} (hA : 1 ≤ A)
    (hgr : ∀ i n, ‖((PowerSeries.coeff n (f i) : ℚ) : ℝ)‖ ≤ A ^ n) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (d : ℕ) (N : ℕ) (v : Fin d → ℕ), (∀ s, v s ≤ N) →
      ∀ p : (Fin d → Fin m) × (Fin d → ℕ),
      |((Work.Holonomy3.matEntry C v p : ℤ) : ℝ)| ≤
        Real.exp (C₀ * ((d : ℝ) * (N : ℝ) + (d : ℝ))) := by
  classical
  obtain ⟨c, hc0, hc⟩ := clearFac_exp_growth_aux C hA
  refine ⟨c, hc0, ?_⟩
  intro d N v hv p
  have hA0 : (0:ℝ) ≤ A := by linarith
  have hsingle : ∀ s : Fin d, (C.Nc : ℝ) * (clearFac C (v s) : ℝ) * A ^ (v s) ≤
      Real.exp (c * ((N : ℝ) + 1)) := by
    intro s
    have hcfR : (clearFac C (v s) : ℝ) ≤ (clearFac C N : ℝ) := by
      exact_mod_cast clearFac_mono C (hv s)
    have hAR : A ^ (v s) ≤ A ^ N := pow_le_pow_right₀ hA (hv s)
    have hNc0 : (0:ℝ) ≤ (C.Nc : ℝ) := Nat.cast_nonneg _
    calc (C.Nc : ℝ) * (clearFac C (v s) : ℝ) * A ^ (v s)
        ≤ (C.Nc : ℝ) * (clearFac C N : ℝ) * A ^ N := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hcfR hNc0
          · exact hAR
          · exact pow_nonneg hA0 _
          · exact mul_nonneg hNc0 (Nat.cast_nonneg _)
      _ ≤ Real.exp (c * ((N : ℝ) + 1)) := hc N
  have hprod1 : |((matEntry C v p : ℤ) : ℝ)| ≤
      ∏ s : Fin d, (C.Nc : ℝ) * (clearFac C (v s) : ℝ) * A ^ (v s) := by
    rw [matEntry, Int.cast_prod, Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun s _ => abs_nonneg _) (fun s _ => ?_)
    by_cases h : p.2 s ≤ v s
    · rw [if_pos h]
      calc |((cFac C (p.1 s) (v s) (v s - p.2 s) : ℤ) : ℝ)|
          ≤ (C.Nc : ℝ) * (clearFac C (v s) : ℝ) * A ^ (v s - p.2 s) :=
            cFac_abs_le C hgr (p.1 s) (v s) (v s - p.2 s) (Nat.sub_le _ _)
        _ ≤ (C.Nc : ℝ) * (clearFac C (v s) : ℝ) * A ^ (v s) := by
            apply mul_le_mul_of_nonneg_left
            · exact pow_le_pow_right₀ hA (Nat.sub_le _ _)
            · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · rw [if_neg h]
      simp only [Int.cast_zero, abs_zero]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg hA0 _)
  calc |((matEntry C v p : ℤ) : ℝ)|
      ≤ ∏ s : Fin d, (C.Nc : ℝ) * (clearFac C (v s) : ℝ) * A ^ (v s) := hprod1
    _ ≤ ∏ _s : Fin d, Real.exp (c * ((N : ℝ) + 1)) :=
        Finset.prod_le_prod₀
          (fun s _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg hA0 _))
          (fun s _ => hsingle s)
    _ = Real.exp (c * ((d : ℝ) * (N : ℝ) + (d : ℝ))) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
        congr 1
        ring

end Work.Holonomy3
