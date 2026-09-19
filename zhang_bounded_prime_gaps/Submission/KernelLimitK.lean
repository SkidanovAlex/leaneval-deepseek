import Mathlib
import Submission.KernelLimit
import Submission.CrudeKernelCoord
import Submission.RealExpBounds
import Submission.Commons.NumberTheory.Zeta.exists_norm_coordK_div_prod_locR_sub_one_le
import Submission.KernelFun

open scoped BigOperators Topology
open Filter

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# P8 (41) for `k` coordinates: the full kernel of Lemma 4.1

The kernel of Polymath8a's Lemma 4.1 is the Euler product of the
`k`-coordinate local factors `K_p = coordLocalK p a b` (`Submission.CrudeKernelCoord`),
compared with `∏_j R_{p,j}` by the per-prime estimate of P8 (40) — available for
all `k` as the commons lemma
`Commons.NumberTheory.Zeta.exists_norm_coordK_div_prod_locR_sub_one_le`
(proved by the fleet from the algebraic ratio bound
`Commons.Analysis.Complex.norm_ratio_sub_one_le`).

This module lifts the single-coordinate statements of
`Submission.KernelLimit` to `k` coordinates:

  * `exists_coordK_ratio_bound` — the per-prime estimate, restated for
    `coordLocalK` and `locR`;
  * `norm_prod_sub_one_le_of` / `norm_prod_exp_le_of` — products of `k`
    near-one factors;
  * `kernel_pole_asymptotic_fin` — **P8 (41) for `k` coordinates**: for fixed
    coprime moduli `W, N` and `w` with all primes `≤ w` dividing `WN`, the kernel
    limit of `∏_{p ∤ WN} K_p` satisfies

        K · ∏_j (2+iξ_j+iξ'_j)B(x)φ(N)/((1+iξ_j)(1+iξ'_j)N) → 1

    uniformly over the cube `|ξ_j|, |ξ'_j| ≤ √(log x)`, up to the tail factor
    `exp(C/w) - 1`.

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- **The per-prime comparison (40) for `k` coordinates**, in the
`coordLocalK`/`locR` normalization. -/
lemma exists_coordK_ratio_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ), 2 ≤ p → ∀ (a b : Fin k → ℂ),
      (∀ j, 0 ≤ (a j).re) → (∀ j, 0 ≤ (b j).re) →
      ‖coordLocalK p a b / ∏ j : Fin k, locR p (a j) (b j) - 1‖ ≤ C / (p : ℝ) ^ 2 := by
  obtain ⟨C, hC, h⟩ := Commons.NumberTheory.Zeta.exists_norm_coordK_div_prod_locR_sub_one_le k
  refine ⟨C, hC, fun p hp2 a b ha hb => ?_⟩
  have h1 : coordLocalK p a b = 1 + ∑ j : Fin k,
      (-((p : ℂ) ^ (-(1 + a j))) - ((p : ℂ) ^ (-(1 + b j))) +
        ((p : ℂ) ^ (-(1 + a j + b j)))) :=
    coordLocalK_eq p (by omega) a b
  have h2 : (∏ j : Fin k, locR p (a j) (b j)) = ∏ j : Fin k,
      (((1 : ℂ) - (p : ℂ) ^ (-(1 + a j))) * ((1 : ℂ) - (p : ℂ) ^ (-(1 + b j))) /
        ((1 : ℂ) - (p : ℂ) ^ (-(1 + a j + b j)))) := by
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [locR, div_eq_mul_inv]
  rw [h1, h2]
  exact h p hp2 a b ha hb

/-- Product of near-one factors: `‖∏_j a_j - 1‖ ≤ e^{kA} - 1` for
`‖a_j - 1‖ ≤ A`. -/
lemma norm_prod_sub_one_le_of {k : ℕ} {A : ℝ} {a : Fin k → ℂ}
    (ha : ∀ j, ‖a j - 1‖ ≤ A) :
    ‖(∏ j : Fin k, a j) - 1‖ ≤ Real.exp ((k : ℝ) * A) - 1 := by
  have h : (∏ j : Fin k, a j) = ∏ j : Fin k, (1 + (a j - 1)) :=
    Finset.prod_congr rfl (fun j _ => by ring)
  rw [h]
  refine (Finset.norm_prod_one_add_sub_one_le _ _).trans ?_
  have hsum : ∑ j : Fin k, ‖a j - 1‖ ≤ (k : ℝ) * A := by
    calc ∑ j : Fin k, ‖a j - 1‖ ≤ ∑ _j : Fin k, A := Finset.sum_le_sum (fun j _ => ha j)
      _ = (k : ℝ) * A := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1

/-- Norm bound for a product of near-one factors: `‖∏_j a_j‖ ≤ e^{kA}`. -/
lemma norm_prod_exp_le_of {k : ℕ} {A : ℝ} {a : Fin k → ℂ}
    (ha : ∀ j, ‖a j - 1‖ ≤ A) :
    ‖(∏ j : Fin k, a j)‖ ≤ Real.exp ((k : ℝ) * A) := by
  have h : (∏ j : Fin k, a j) = ∏ j : Fin k, (1 + (a j - 1)) :=
    Finset.prod_congr rfl (fun j _ => by ring)
  rw [h]
  have h1 : ‖∏ j : Fin k, (1 + (a j - 1))‖ ≤ ∏ j : Fin k, (1 + ‖a j - 1‖) := by
    rw [Complex.norm_prod]
    refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
    simpa using norm_add_le (1 : ℂ) (a i - 1)
  have h2 : ∏ j : Fin k, (1 + ‖a j - 1‖) ≤ Real.exp (∑ j : Fin k, ‖a j - 1‖) :=
    prod_one_add_le_exp _ _ (fun i _ => by positivity)
  have hsum : ∑ j : Fin k, ‖a j - 1‖ ≤ (k : ℝ) * A := by
    calc ∑ j : Fin k, ‖a j - 1‖ ≤ ∑ _j : Fin k, A := Finset.sum_le_sum (fun j _ => ha j)
      _ = (k : ℝ) * A := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact h1.trans (h2.trans (Real.exp_le_exp.mpr hsum))

/-- Product of a finite family of convergent sequences. -/
lemma tendsto_finset_prod_of {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℂ} {g : ι → ℂ}
    (h : ∀ i ∈ s, Tendsto (f i) atTop (𝓝 (g i))) :
    Tendsto (fun n : ℕ => ∏ i ∈ s, f i n) atTop (𝓝 (∏ i ∈ s, g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **P8 (41) for `k` coordinates.**  For fixed coprime `W, N ≠ 0`, every `k ≥ 1`
and every `w` with all primes `≤ w` dividing `WN` there is a vanishing error `ε`
such that, uniformly on the cube `|ξ_j|, |ξ'_j| ≤ √(log x)`, the limit `K` of
the `k`-coordinate kernel product satisfies

    ‖ K · ∏_j poleFactor_j − 1 ‖ ≤ ε(x) + 2·(exp(C/w) − 1) . -/
theorem kernel_pole_asymptotic_fin (k : ℕ) (hk : 1 ≤ k) (W N : ℕ) (hW : W ≠ 0)
    (hN : N ≠ 0) (hcop : W.Coprime N) (w : ℕ) (hw : 1 ≤ w)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ w → p ∣ W * N) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x → ∀ ξ ξ' : Fin k → ℝ,
        (∀ j, |ξ j| ≤ Real.sqrt (Real.log (x : ℝ))) →
        (∀ j, |ξ' j| ≤ Real.sqrt (Real.log (x : ℝ))) →
        ∃ L : ℂ, Tendsto (fun n : ℕ => ∏ p ∈ Sfilter (W * N) n,
            coordLocalK p (fun j => logZ (ξ j) x) (fun j => logZ (ξ' j) x)) atTop (𝓝 L) ∧
          ‖L * (∏ j : Fin k, poleFactor W N (ξ j) (ξ' j) x) - 1‖ ≤
            ε x + 2 * (Real.exp (C / (w : ℝ)) - 1) := by
  classical
  obtain ⟨C, hC0, hCbound⟩ := exists_coordK_ratio_bound k
  obtain ⟨x₀₁, ε₁, hε₁, hpole⟩ := zetaWN_ratio_pole_uniform W N hW hN hcop
  have hε₂ : Tendsto (fun x : ℕ => |ε₁ x|) atTop (𝓝 0) := by
    simpa using hε₁.abs
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hε₂.eventually_lt_const (by positivity : (0 : ℝ) < 1 / (2 * (k : ℝ))))
  refine ⟨C, hC0, max (max x₀₁ N₀) 2, fun x => 2 * (k : ℝ) * |ε₁ x|, ?_, ?_⟩
  · simpa using hε₂.const_mul (2 * (k : ℝ))
  · intro x hx ξ ξ' hξ hξ'
    have hx₁ : x₀₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hNx : N₀ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
    have hkx : (k : ℝ) * |ε₁ x| ≤ 1 / 2 := by
      have h1 := hN₀ x hNx
      have h2 : (k : ℝ) * |ε₁ x| < (k : ℝ) * (1 / (2 * (k : ℝ))) :=
        mul_lt_mul_of_pos_left h1 (by exact_mod_cast hk)
      have h3 : (k : ℝ) * (1 / (2 * (k : ℝ))) = 1 / 2 := by field_simp
      linarith [h2, h3.le]
    have hq : W * N ≠ 0 := mul_ne_zero hW hN
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    set a : Fin k → ℂ := fun j => logZ (ξ j) x with ha'
    set b : Fin k → ℂ := fun j => logZ (ξ' j) x with hb'
    have hare : ∀ j, 0 < (a j).re := by
      intro j
      rw [ha']
      rw [logZ_re]
      positivity
    have hbre : ∀ j, 0 < (b j).re := by
      intro j
      rw [hb']
      rw [logZ_re]
      positivity
    -- the modified-zeta ratio limits Zf
    set Zf : Fin k → ℂ := fun j => zetaWN (W * N) (1 + a j + b j) /
        (zetaWN (W * N) (1 + a j) * zetaWN (W * N) (1 + b j)) with hZf
    have hpole' : ∀ j : Fin k, ‖Zf j * poleFactor W N (ξ j) (ξ' j) x - 1‖ ≤ |ε₁ x| := by
      intro j
      have h := hpole x hx₁ (ξ j) (ξ' j) (hξ j) (hξ' j)
      rw [show (1 + (logZ (ξ j) x + logZ (ξ' j) x)) = (1 + a j + b j) from by
            simp only [ha', hb']
            ring] at h
      rw [hZf]
      exact h.trans (le_abs_self _)
    -- the ratio and R products converge
    obtain ⟨M, hM⟩ := exists_tendsto_prod_one_add_filter (W * N) (C := C) hC0.le
      (fun p hp2 => by
        simpa using hCbound p hp2 a b (fun j => (hare j).le) (fun j => (hbre j).le))
    have hratio_tend : Tendsto (fun n : ℕ => ∏ p ∈ Sfilter (W * N) n,
        coordLocalK p a b / ∏ j : Fin k, locR p (a j) (b j)) atTop (𝓝 M) := by
      refine hM.congr' ?_
      filter_upwards with n
      refine Finset.prod_congr rfl (fun p _ => ?_)
      ring
    have hRlim : Tendsto (fun n : ℕ => ∏ p ∈ Sfilter (W * N) n,
        ∏ j : Fin k, locR p (a j) (b j)) atTop (𝓝 (∏ j : Fin k, Zf j)) := by
      have hcomm : (fun n : ℕ => ∏ p ∈ Sfilter (W * N) n, ∏ j : Fin k, locR p (a j) (b j)) =
          fun n : ℕ => ∏ j : Fin k, ∏ p ∈ Sfilter (W * N) n, locR p (a j) (b j) := by
        funext n
        exact Finset.prod_comm
      rw [hcomm]
      refine tendsto_finset_prod_of _ (fun j _ => ?_)
      have hR := eulerRatioZetaWN (W * N) hq (hare j) (hbre j)
      have h1 : Tendsto (fun n : ℕ => ∏ p ∈ Sfilter (W * N) n, locR p (a j) (b j)) atTop
          (𝓝 (zetaWN (W * N) (1 + a j + b j) /
            (zetaWN (W * N) (1 + a j) * zetaWN (W * N) (1 + b j)))) := by
        refine hR.congr' ?_
        filter_upwards with n
        refine Finset.prod_congr rfl (fun p _ => ?_)
        rw [locR, div_eq_mul_inv]
      rw [hZf]
      exact h1
    -- the kernel limit is (∏ Zf) · M
    have hKlim : Tendsto (fun n : ℕ => ∏ p ∈ Sfilter (W * N) n, coordLocalK p a b) atTop
        (𝓝 ((∏ j : Fin k, Zf j) * M)) := by
      have hEq : (fun n : ℕ => ∏ p ∈ Sfilter (W * N) n, coordLocalK p a b) =
          fun n : ℕ => (∏ p ∈ Sfilter (W * N) n, ∏ j : Fin k, locR p (a j) (b j)) *
            (∏ p ∈ Sfilter (W * N) n,
              coordLocalK p a b / ∏ j : Fin k, locR p (a j) (b j)) := by
        funext n
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun p hp => ?_)
        have hp2 : 2 ≤ p := two_le_of_mem_Sfilter hp
        have hRnz : (∏ j : Fin k, locR p (a j) (b j)) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr (fun j _ => by
            intro hz
            have h := locR_norm_ge_sixth (a j) (b j) hp2 (hare j).le (hbre j).le
            rw [hz] at h
            norm_num at h)
        field_simp [hRnz]
      rw [hEq]
      exact hRlim.mul hratio_tend
    -- the tail bound on M
    have hMbound : ‖M - 1‖ ≤ Real.exp (C / (w : ℝ)) - 1 := by
      have hclosed : IsClosed {z : ℂ | ‖z - 1‖ ≤ Real.exp (C / (w : ℝ)) - 1} :=
        isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
      refine hclosed.mem_of_tendsto hM (Eventually.of_forall (fun n => ?_))
      exact tailProduct_norm_sub_one_le hC0.le hw (fun p hp => by
        by_contra hlt
        have hpn : p ∈ n.primesBelow := (Finset.mem_filter.mp hp).1
        have hnd : ¬ p ∣ W * N := (Finset.mem_filter.mp hp).2
        exact hnd (hsmall p (Nat.prime_of_mem_primesBelow hpn) (by omega)))
        (fun p hp => by
          simpa using hCbound p (two_le_of_mem_Sfilter hp) a b
            (fun j => (hare j).le) (fun j => (hbre j).le))
    refine ⟨(∏ j : Fin k, Zf j) * M, hKlim, ?_⟩
    have hexpta : 0 ≤ Real.exp (C / (w : ℝ)) - 1 := by
      have h : 0 ≤ C / (w : ℝ) := by positivity
      linarith [Real.one_le_exp h]
    have hprod_b : ‖(∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor W N (ξ j) (ξ' j) x) - 1‖ ≤
        Real.exp ((k : ℝ) * |ε₁ x|) - 1 := by
      rw [← Finset.prod_mul_distrib]
      exact norm_prod_sub_one_le_of (fun j => hpole' j)
    have hprod_n : ‖(∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor W N (ξ j) (ξ' j) x)‖ ≤
        Real.exp ((k : ℝ) * |ε₁ x|) := by
      rw [← Finset.prod_mul_distrib]
      exact norm_prod_exp_le_of (fun j => hpole' j)
    have hkabs0 : 0 ≤ (k : ℝ) * |ε₁ x| := mul_nonneg (by positivity) (abs_nonneg _)
    have hkabs1 : (k : ℝ) * |ε₁ x| ≤ 1 := by linarith [hkx]
    have hexp_le : Real.exp ((k : ℝ) * |ε₁ x|) ≤ 1 + 2 * ((k : ℝ) * |ε₁ x|) := by
      have h := exp_sub_one_le_two_mul hkabs0 hkabs1
      linarith
    have h2k1 : 2 * ((k : ℝ) * |ε₁ x|) ≤ 1 := by linarith [hkx]
    have hdecomp : ((∏ j : Fin k, Zf j) * M) * (∏ j : Fin k, poleFactor W N (ξ j) (ξ' j) x) - 1 =
        (((∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor W N (ξ j) (ξ' j) x)) * M -
          ((∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor W N (ξ j) (ξ' j) x))) +
        (((∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor W N (ξ j) (ξ' j) x)) - 1) := by ring
    rw [hdecomp]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖((∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor W N (ξ j) (ξ' j) x)) * M -
        ((∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor W N (ξ j) (ξ' j) x))‖ ≤
        (1 + 2 * ((k : ℝ) * |ε₁ x|)) * (Real.exp (C / (w : ℝ)) - 1) := by
      have hsub : ((∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor W N (ξ j) (ξ' j) x)) * M -
          ((∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor W N (ξ j) (ξ' j) x)) =
          ((∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor W N (ξ j) (ξ' j) x)) * (M - 1) := by ring
      rw [hsub, norm_mul]
      calc ‖(∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor W N (ξ j) (ξ' j) x)‖ * ‖M - 1‖
          ≤ Real.exp ((k : ℝ) * |ε₁ x|) * ‖M - 1‖ :=
            mul_le_mul_of_nonneg_right hprod_n (norm_nonneg _)
        _ ≤ (1 + 2 * ((k : ℝ) * |ε₁ x|)) * ‖M - 1‖ :=
            mul_le_mul_of_nonneg_right hexp_le (norm_nonneg _)
        _ ≤ (1 + 2 * ((k : ℝ) * |ε₁ x|)) * (Real.exp (C / (w : ℝ)) - 1) :=
            mul_le_mul_of_nonneg_left hMbound (by linarith [h2k1])
    have hexp1 : Real.exp ((k : ℝ) * |ε₁ x|) - 1 ≤ 2 * ((k : ℝ) * |ε₁ x|) :=
      exp_sub_one_le_two_mul hkabs0 hkabs1
    nlinarith [h2, hprod_b, hexp1, h2k1, hexpta]

end Commons.NumberTheory.MaynardSieve
