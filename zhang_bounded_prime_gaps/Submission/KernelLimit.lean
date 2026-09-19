import Mathlib
import Submission.KernelTail
import Submission.ZetaWNBounds
import Submission.ZetaRatio
import Submission.ZetaRatioPole

open scoped BigOperators Topology
open Filter

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# P8 (41): the kernel Euler product and its pole asymptotic

The kernel of Polymath8a's Lemma 4.1, equation (38), is the Euler product
`K = ∏_{p ∤ WN} K_p` with `K_p = (1 + O(p⁻²))·R_p` (`K_p` = `locK`, `R_p` =
`locR` of `Submission.LocalFactorComparison`).  This module assembles the three
already-proved ingredients — the per-prime comparison (P8 (40)), the tail
product estimate (`Submission.KernelTail`) and the identification of the
`R`-product with the `ζ_WN`-ratio (`eulerRatioZetaWN`,
`Submission.ZetaRatio`), together with the uniform pole ratio
(`zetaWN_ratio_pole_uniform`, `Submission.ZetaRatioPole`) — into:

  * `exists_tendsto_prod_one_add_filter` — convergence of
    `∏_{p < n, p ∤ q}(1 + z_p)` for `‖z_p‖ ≤ C/p²` (Cauchy estimate
    `e^C·(exp(C/(m-1)) - 1)`);
  * `exists_tendsto_locKratio` — convergence of `∏_{p < n, p ∤ q} K_p/R_p`;
  * `exists_tendsto_locKprod` — convergence of the kernel product `∏ K_p`:
    the kernel of Lemma 4.1 is a well-defined complex number;
  * `kernel_pole_asymptotic` — **P8 (41)**: for fixed coprime `W, N` and any `w`
    such that every prime `≤ w` divides `WN`, the kernel limit satisfies

        K·(2+iξ+iξ')·B(x)·φ(N) / ((1+iξ)(1+iξ')·N) → 1

    uniformly on the cube `|ξ|, |ξ'| ≤ √(log x)`, up to the tail factor
    `exp(48/w) - 1` of P8 (40).

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The primes below `n` that do not divide `q`. -/
noncomputable def Sfilter (q n : ℕ) : Finset ℕ :=
  (n.primesBelow).filter (fun p => ¬ p ∣ q)

lemma Sfilter_mono (q : ℕ) : Monotone (Sfilter q) := by
  intro m n hmn
  exact Finset.filter_subset_filter _
    (fun p hp => by rw [Nat.mem_primesBelow] at hp ⊢; exact ⟨lt_of_lt_of_le hp.1 hmn, hp.2⟩)

lemma Sfilter_subset_primesBelow (q n : ℕ) : Sfilter q n ⊆ n.primesBelow :=
  Finset.filter_subset _ _

lemma two_le_of_mem_Sfilter {q n p : ℕ} (hp : p ∈ Sfilter q n) : 2 ≤ p :=
  two_le_of_mem_primesBelow (Finset.mem_of_mem_filter p hp)

/-- Uniform exponential bound for the partial products. -/
lemma prod_one_add_norm_le_exp {q : ℕ} {z : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hz : ∀ p : ℕ, 2 ≤ p → ‖z p‖ ≤ C / (p : ℝ) ^ 2) (n : ℕ) :
    ‖∏ p ∈ Sfilter q n, (1 + z p)‖ ≤ Real.exp C := by
  have h1 : ‖∏ p ∈ Sfilter q n, (1 + z p)‖ ≤ ∏ p ∈ Sfilter q n, (1 + ‖z p‖) := by
    rw [Complex.norm_prod]
    refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
    simpa using norm_add_le (1 : ℂ) (z i)
  have h2 : ∏ p ∈ Sfilter q n, (1 + ‖z p‖) ≤ Real.exp (∑ p ∈ Sfilter q n, ‖z p‖) :=
    prod_one_add_le_exp _ _ (fun i _ => norm_nonneg _)
  have h3 : ∑ p ∈ Sfilter q n, ‖z p‖ ≤ C := by
    have h4 : ∑ p ∈ Sfilter q n, ‖z p‖ ≤ ∑ p ∈ Sfilter q n, C / (p : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun p hp => hz p (two_le_of_mem_Sfilter hp))
    have h5 : ∑ p ∈ Sfilter q n, C / (p : ℝ) ^ 2 = C * ∑ p ∈ Sfilter q n, ((p : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by rw [div_eq_mul_inv])
    have h6 : ∑ p ∈ Sfilter q n, ((p : ℝ) ^ 2)⁻¹ ≤ 1 := by
      have h7 : ∑ p ∈ Sfilter q n, ((p : ℝ) ^ 2)⁻¹ ≤ ((1 : ℕ) : ℝ)⁻¹ := by
        refine sum_inv_sq_le_inv (by norm_num) (fun p hp => ?_)
        have := two_le_of_mem_Sfilter hp
        exact_mod_cast (by omega : 1 < p)
      simpa using h7
    calc ∑ p ∈ Sfilter q n, ‖z p‖ ≤ ∑ p ∈ Sfilter q n, C / (p : ℝ) ^ 2 := h4
      _ = C * ∑ p ∈ Sfilter q n, ((p : ℝ) ^ 2)⁻¹ := h5
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left h6 hC
      _ = C := mul_one C
  calc ‖∏ p ∈ Sfilter q n, (1 + z p)‖ ≤ ∏ p ∈ Sfilter q n, (1 + ‖z p‖) := h1
    _ ≤ Real.exp (∑ p ∈ Sfilter q n, ‖z p‖) := h2
    _ ≤ Real.exp C := Real.exp_le_exp.mpr h3

/-- **Convergence of the filtered Euler product.**  For weights with
`‖z_p‖ ≤ C/p²` on the primes, `∏_{p < n, p ∤ q}(1 + z_p)` converges.  The proof
is the Cauchy estimate `‖P_n - P_m‖ ≤ e^C·(exp(C/(m-1)) - 1)` for `2 ≤ m ≤ n`
(the uniform product bound above and the tail estimate
`tailProduct_norm_sub_one_le`). -/
theorem exists_tendsto_prod_one_add_filter (q : ℕ) {z : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hz : ∀ p : ℕ, 2 ≤ p → ‖z p‖ ≤ C / (p : ℝ) ^ 2) :
    ∃ L : ℂ, Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n, (1 + z p)) atTop (𝓝 L) := by
  set P : ℕ → ℂ := fun n => ∏ p ∈ Sfilter q n, (1 + z p) with hP
  have hdiste : ∀ n m : ℕ, m ≤ n → 2 ≤ m →
      dist (P n) (P m) ≤ Real.exp C * (Real.exp (C / ((m : ℝ) - 1)) - 1) := by
    intro n m hmn hm2
    have hsub : Sfilter q m ⊆ Sfilter q n := Sfilter_mono q hmn
    have hfac : P n = (∏ p ∈ Sfilter q n \ Sfilter q m, (1 + z p)) * P m := by
      rw [hP]
      dsimp only
      rw [← Finset.prod_sdiff hsub]
    have hSw : ∀ p ∈ Sfilter q n \ Sfilter q m, m - 1 < p := by
      intro p hp
      rw [Finset.mem_sdiff] at hp
      obtain ⟨hpn, hpm⟩ := hp
      have hprime : p.Prime := Nat.prime_of_mem_primesBelow (Finset.mem_of_mem_filter p hpn)
      have hndvd : ¬ p ∣ q := (Finset.mem_filter.mp hpn).2
      have hle : m ≤ p := by
        by_contra hlt
        exact hpm (Finset.mem_filter.mpr
          ⟨Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩, hndvd⟩)
      omega
    have hcast : (((m - 1 : ℕ)) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m)]
      norm_num
    have htail : ‖(∏ p ∈ Sfilter q n \ Sfilter q m, (1 + z p)) - 1‖ ≤
        Real.exp (C / ((m : ℝ) - 1)) - 1 := by
      have hkey := tailProduct_norm_sub_one_le (w := m - 1)
        (S := Sfilter q n \ Sfilter q m) hC (by omega) hSw
        (fun p hp => hz p (two_le_of_mem_Sfilter (Finset.mem_sdiff.mp hp).1))
      rwa [hcast] at hkey
    have hdist : dist (P n) (P m) =
        ‖(∏ p ∈ Sfilter q n \ Sfilter q m, (1 + z p)) - 1‖ * ‖P m‖ := by
      rw [dist_eq_norm, hfac]
      have h2 : (∏ p ∈ Sfilter q n \ Sfilter q m, (1 + z p)) * P m - P m =
          ((∏ p ∈ Sfilter q n \ Sfilter q m, (1 + z p)) - 1) * P m := by ring
      rw [h2, norm_mul]
    rw [hdist]
    have hPm : ‖P m‖ ≤ Real.exp C := by rw [hP]; exact prod_one_add_norm_le_exp hC hz m
    have htail0 : 0 ≤ Real.exp (C / ((m : ℝ) - 1)) - 1 := by
      have hm1pos : 0 < (m : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
        linarith
      linarith [Real.one_le_exp (div_nonneg hC hm1pos.le)]
    calc ‖(∏ p ∈ Sfilter q n \ Sfilter q m, (1 + z p)) - 1‖ * ‖P m‖
        ≤ (Real.exp (C / ((m : ℝ) - 1)) - 1) * Real.exp C :=
          mul_le_mul htail hPm (norm_nonneg _) htail0
      _ = Real.exp C * (Real.exp (C / ((m : ℝ) - 1)) - 1) := by ring
  have hcauchy : CauchySeq P := by
    rw [cauchySeq_iff_le_tendsto_0]
    refine ⟨fun N => if N ≤ 1 then 2 * Real.exp C else
        Real.exp C * (Real.exp (C / ((N : ℝ) - 1)) - 1), ?_, ?_, ?_⟩
    · intro N
      dsimp only
      by_cases h : N ≤ 1
      · rw [if_pos h]; positivity
      · rw [if_neg h]
        have hN2 : 2 ≤ N := by omega
        have hNpos : 0 < (N : ℝ) - 1 := by
          have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
          linarith
        exact mul_nonneg (Real.exp_pos C).le
          (by linarith [Real.one_le_exp (div_nonneg hC hNpos.le)])
    · intro n m N hn hm
      dsimp only
      have hbound2 : ∀ {a b : ℕ}, 2 ≤ N → N ≤ a → N ≤ b → 2 ≤ b → b ≤ a →
          dist (P a) (P b) ≤ Real.exp C * (Real.exp (C / ((N : ℝ) - 1)) - 1) := by
        intro a b hN2 hNa hNb hb2 hba
        have h := hdiste a b hba hb2
        have hNpos : 0 < (N : ℝ) - 1 := by
          have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
          linarith
        have hmono : (N : ℝ) - 1 ≤ (b : ℝ) - 1 := by
          have : (N : ℝ) ≤ (b : ℝ) := by exact_mod_cast hNb
          linarith
        have hfrac : C / ((b : ℝ) - 1) ≤ C / ((N : ℝ) - 1) :=
          div_le_div_of_nonneg_left hC hNpos hmono
        refine h.trans ?_
        exact mul_le_mul_of_nonneg_left (by linarith [Real.exp_le_exp.mpr hfrac])
          (Real.exp_pos C).le
      by_cases hN : N ≤ 1
      · rw [if_pos hN]
        have h1 : ‖P n‖ ≤ Real.exp C := by rw [hP]; exact prod_one_add_norm_le_exp hC hz n
        have h2 : ‖P m‖ ≤ Real.exp C := by rw [hP]; exact prod_one_add_norm_le_exp hC hz m
        have h3 : dist (P n) (P m) ≤ ‖P n‖ + ‖P m‖ := by
          rw [dist_eq_norm]
          exact norm_sub_le _ _
        linarith
      · rw [if_neg hN]
        rcases le_total m n with hmn | hnm
        · have hm2 : 2 ≤ m := le_trans (by omega : 2 ≤ N) hm
          exact hbound2 (by omega) hn hm hm2 hmn
        · have hn2 : 2 ≤ n := le_trans (by omega : 2 ≤ N) hn
          rw [dist_comm]
          exact hbound2 (by omega) hm hn hn2 hnm
    · have h1 : Tendsto (fun N : ℕ => C / ((N : ℝ) - 1)) atTop (𝓝 0) := by
        have h2 : Tendsto (fun N : ℕ => (N : ℝ) - 1) atTop atTop := by
          have hbase : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
          have hc := Filter.tendsto_atTop_add_const_right atTop (-1 : ℝ) hbase
          simpa only [sub_eq_add_neg] using hc
        exact Filter.Tendsto.div_atTop tendsto_const_nhds h2
      have h3 : Tendsto (fun N : ℕ => Real.exp (C / ((N : ℝ) - 1)) - 1) atTop (𝓝 0) := by
        have h4 : Tendsto (fun N : ℕ => Real.exp (C / ((N : ℝ) - 1))) atTop (𝓝 1) := by
          have hc := (Real.continuous_exp.tendsto 0).comp h1
          simpa [Function.comp_def, Real.exp_zero] using hc
        simpa using h4.sub_const 1
      have hgood : Tendsto (fun N : ℕ => Real.exp C * (Real.exp (C / ((N : ℝ) - 1)) - 1))
          atTop (𝓝 0) := by
        simpa using h3.const_mul (Real.exp C)
      refine hgood.congr' ?_
      filter_upwards [eventually_gt_atTop 1] with N hN
      rw [if_neg (by omega)]
  rcases cauchySeq_tendsto_of_complete hcauchy with ⟨L, hL⟩
  exact ⟨L, hL⟩

/-- **P8 (40) convergence**: the ratio product `∏_{p < n, p ∤ q} K_p/R_p`
converges for `Re a, Re b ≥ 0`. -/
theorem exists_tendsto_locKratio (q : ℕ) {a b : ℂ} (ha : 0 ≤ a.re) (hb : 0 ≤ b.re) :
    ∃ M : ℂ, Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n, locK p a b / locR p a b)
      atTop (𝓝 M) := by
  have hprod : (fun n : ℕ => ∏ p ∈ Sfilter q n, locK p a b / locR p a b) =
      fun n : ℕ => ∏ p ∈ Sfilter q n, (1 + (locK p a b / locR p a b - 1)) := by
    funext n
    exact Finset.prod_congr rfl (fun p _ => by ring)
  rw [hprod]
  exact exists_tendsto_prod_one_add_filter q (C := 48) (by norm_num)
    (fun p hp2 => locK_div_locR_sub_one_bound a b hp2 ha hb)

/-- **The kernel of P8 Lemma 4.1 converges.**  For `q ≠ 0` and `Re a, Re b > 0`
the Euler product `∏_{p ∤ q} K_p` is a well-defined complex number. -/
theorem exists_tendsto_locKprod (q : ℕ) (hq : q ≠ 0) {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ∃ L : ℂ, Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n, locK p a b) atTop (𝓝 L) := by
  obtain ⟨M, hM⟩ := exists_tendsto_locKratio q (le_of_lt ha) (le_of_lt hb)
  have hR := eulerRatioZetaWN q hq ha hb
  have hR' : Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n, locR p a b) atTop
      (𝓝 (zetaWN q (1 + a + b) / (zetaWN q (1 + a) * zetaWN q (1 + b)))) := by
    refine hR.congr' ?_
    filter_upwards with n
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [locR, div_eq_mul_inv]
  have hprod : Tendsto (fun n : ℕ => (∏ p ∈ Sfilter q n, locR p a b) *
      (∏ p ∈ Sfilter q n, locK p a b / locR p a b)) atTop
      (𝓝 ((zetaWN q (1 + a + b) / (zetaWN q (1 + a) * zetaWN q (1 + b))) * M)) :=
    hR'.mul hM
  have hEq : (fun n : ℕ => ∏ p ∈ Sfilter q n, locK p a b) =
      fun n : ℕ => (∏ p ∈ Sfilter q n, locR p a b) *
        (∏ p ∈ Sfilter q n, locK p a b / locR p a b) := by
    funext n
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp2 : 2 ≤ p := two_le_of_mem_Sfilter hp
    have hRnz : locR p a b ≠ 0 := by
      intro hz
      have h := locR_norm_ge_sixth a b hp2 (le_of_lt ha) (le_of_lt hb)
      rw [hz] at h
      norm_num at h
    field_simp [hRnz]
  exact ⟨_, by rw [hEq]; exact hprod⟩

/-- The real part of the truncated point: `Re logZ ξ x = 1/log x`. -/
lemma logZ_re (ξ : ℝ) (x : ℕ) : (logZ ξ x).re = 1 / Real.log (x : ℝ) := by
  have h : logZ ξ x = ((1 / Real.log (x : ℝ) : ℝ) : ℂ) +
      ((ξ / Real.log (x : ℝ) : ℝ) : ℂ) * Complex.I := by
    dsimp [logZ]
    field_simp
    push_cast
    ring
  rw [h, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **P8 (41).**  With `q = WN` coprime and `w` such that every prime `≤ w`
divides `WN` (as in the sieve, where `W = ∏_{p ≤ w} p`), the kernel limit `K`
satisfies the pole asymptotic uniformly on the cube, up to the P8 (40) tail
factor `exp(48/w) - 1`. -/
theorem kernel_pole_asymptotic (W N : ℕ) (hW : W ≠ 0) (hN : N ≠ 0) (hcop : W.Coprime N)
    (w : ℕ) (hw : 1 ≤ w) (hsmall : ∀ p : ℕ, p.Prime → p ≤ w → p ∣ W * N) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x → ∀ ξ ξ' : ℝ,
        |ξ| ≤ Real.sqrt (Real.log (x : ℝ)) → |ξ'| ≤ Real.sqrt (Real.log (x : ℝ)) →
        ∃ L : ℂ, Tendsto (fun n : ℕ => ∏ p ∈ Sfilter (W * N) n,
            locK p (logZ ξ x) (logZ ξ' x)) atTop (𝓝 L) ∧
          ‖L * poleFactor W N ξ ξ' x - 1‖ ≤ ε x + 2 * (Real.exp (48 / (w : ℝ)) - 1) := by
  classical
  obtain ⟨x₀, ε₁, hε₁, hbound⟩ := zetaWN_ratio_pole_uniform W N hW hN hcop
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hε₁.eventually_lt_const (by norm_num : (0:ℝ) < 1))
  refine ⟨max (max x₀ N₀) 2, ε₁, hε₁, ?_⟩
  intro x hx ξ ξ' hξ hξ'
  have hx₀ : x₀ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hNx : N₀ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hε₁x : ε₁ x < 1 := hN₀ x hNx
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hq : W * N ≠ 0 := mul_ne_zero hW hN
  have ha : 0 < (logZ ξ x).re := by rw [logZ_re]; positivity
  have hb : 0 < (logZ ξ' x).re := by rw [logZ_re]; positivity
  set Z : ℂ := zetaWN (W * N) (1 + logZ ξ x + logZ ξ' x) /
      (zetaWN (W * N) (1 + logZ ξ x) * zetaWN (W * N) (1 + logZ ξ' x)) with hZdef
  obtain ⟨M, hM⟩ := exists_tendsto_locKratio (W * N) ha.le hb.le
  obtain ⟨L, hL⟩ := exists_tendsto_locKprod (W * N) hq ha hb
  have hR := eulerRatioZetaWN (W * N) hq ha hb
  have hR' : Tendsto (fun n : ℕ => ∏ p ∈ Sfilter (W * N) n,
        locR p (logZ ξ x) (logZ ξ' x)) atTop (𝓝 Z) := by
    rw [hZdef]
    refine hR.congr' ?_
    filter_upwards with n
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [locR, div_eq_mul_inv]
  have hEq : (fun n : ℕ => ∏ p ∈ Sfilter (W * N) n, locK p (logZ ξ x) (logZ ξ' x)) =
      fun n : ℕ => (∏ p ∈ Sfilter (W * N) n, locR p (logZ ξ x) (logZ ξ' x)) *
        (∏ p ∈ Sfilter (W * N) n,
          locK p (logZ ξ x) (logZ ξ' x) / locR p (logZ ξ x) (logZ ξ' x)) := by
    funext n
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp2 : 2 ≤ p := two_le_of_mem_Sfilter hp
    have hRnz : locR p (logZ ξ x) (logZ ξ' x) ≠ 0 := by
      intro hz
      have h := locR_norm_ge_sixth (logZ ξ x) (logZ ξ' x) hp2 ha.le hb.le
      rw [hz] at h
      norm_num at h
    field_simp [hRnz]
  have hLM : L = Z * M := by
    refine tendsto_nhds_unique hL ?_
    rw [hEq]
    exact hR'.mul hM
  have hMbound : ‖M - 1‖ ≤ Real.exp (48 / (w : ℝ)) - 1 := by
    have hclosed : IsClosed {z : ℂ | ‖z - 1‖ ≤ Real.exp (48 / (w : ℝ)) - 1} :=
      isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
    refine hclosed.mem_of_tendsto hM (Eventually.of_forall (fun n => ?_))
    exact locK_div_locR_tail ha.le hb.le hw (fun p hp => by
      by_contra hlt
      have hpn : p ∈ n.primesBelow := (Finset.mem_filter.mp hp).1
      have hnd : ¬ p ∣ W * N := (Finset.mem_filter.mp hp).2
      exact hnd (hsmall p (Nat.prime_of_mem_primesBelow hpn) (by omega)))
  have hZb : ‖Z * poleFactor W N ξ ξ' x - 1‖ ≤ ε₁ x := by
    have h := hbound x hx₀ ξ ξ' hξ hξ'
    rw [show (1 + (logZ ξ x + logZ ξ' x)) = (1 + logZ ξ x + logZ ξ' x) from by ring] at h
    rw [hZdef]
    exact h
  refine ⟨L, hL, ?_⟩
  rw [hLM]
  have hexpge : 0 ≤ Real.exp (48 / (w : ℝ)) - 1 := by
    have h : 0 ≤ 48 / (w : ℝ) := by positivity
    linarith [Real.one_le_exp h]
  have hZp : ‖Z * poleFactor W N ξ ξ' x‖ ≤ 1 + ε₁ x := by
    have h1 : ‖Z * poleFactor W N ξ ξ' x‖ ≤ ‖Z * poleFactor W N ξ ξ' x - 1‖ + ‖(1 : ℂ)‖ := by
      calc ‖Z * poleFactor W N ξ ξ' x‖ = ‖(Z * poleFactor W N ξ ξ' x - 1) + 1‖ := by
            congr 1
            ring
        _ ≤ ‖Z * poleFactor W N ξ ξ' x - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    rw [norm_one] at h1
    linarith
  have hstep1 : ‖(Z * M) * poleFactor W N ξ ξ' x - 1‖ ≤
      (1 + ε₁ x) * (Real.exp (48 / (w : ℝ)) - 1) + ε₁ x := by
    have hdecomp : (Z * M) * poleFactor W N ξ ξ' x - 1 =
        ((Z * poleFactor W N ξ ξ' x) * M - (Z * poleFactor W N ξ ξ' x)) +
          ((Z * poleFactor W N ξ ξ' x) - 1) := by ring
    rw [hdecomp]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖(Z * poleFactor W N ξ ξ' x) * M - (Z * poleFactor W N ξ ξ' x)‖ ≤
        (1 + ε₁ x) * (Real.exp (48 / (w : ℝ)) - 1) := by
      have hsub : (Z * poleFactor W N ξ ξ' x) * M - (Z * poleFactor W N ξ ξ' x) =
          (Z * poleFactor W N ξ ξ' x) * (M - 1) := by ring
      rw [hsub, norm_mul]
      have hnonneg : 0 ≤ 1 + ε₁ x := le_trans (norm_nonneg _) hZp
      calc ‖Z * poleFactor W N ξ ξ' x‖ * ‖M - 1‖ ≤ (1 + ε₁ x) * ‖M - 1‖ :=
            mul_le_mul_of_nonneg_right hZp (norm_nonneg _)
        _ ≤ (1 + ε₁ x) * (Real.exp (48 / (w : ℝ)) - 1) :=
            mul_le_mul_of_nonneg_left hMbound hnonneg
    linarith
  have hfinal : (1 + ε₁ x) * (Real.exp (48 / (w : ℝ)) - 1) + ε₁ x ≤
      ε₁ x + 2 * (Real.exp (48 / (w : ℝ)) - 1) := by
    nlinarith [hε₁x, hexpge]
  exact hstep1.trans hfinal

end Commons.NumberTheory.MaynardSieve
