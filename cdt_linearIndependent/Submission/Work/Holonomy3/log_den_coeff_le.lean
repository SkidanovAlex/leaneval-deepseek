import Mathlib
import Submission.Work.Holonomy3.defs
import Submission.Work.Holonomy3.log_lcm_cap_le
import Submission.Work.Holonomy3.sum_le_top_of_monotone
import Submission.Work.Holonomy3.coeff_auxSeries
import Submission.Work.Holonomy3.den_dvd_iff_mul_castInt
import Submission.Work.Holonomy3.den_finsetProd_dvd
import Submission.Work.Holonomy3.den_coeff_dvd_lcm
import Submission.Work.Holonomy3.log_absorb
import Submission.Work.Holonomy3.lcm_prod_dvd_shape
import Submission.Work.Holonomy3.log_den_defs
import Submission.Work.Holonomy3.winLcm_dvd_split
import Submission.Work.Holonomy3.log_ppFac_bound
import Submission.Work.Holonomy3.sum_Lge_le_integral
import Submission.Work.Holonomy3.pow_prod_dvd_window
import Submission.CDT.LcmGe
import Submission.Work.Holonomy3.sqrt_log_absorb

/-!
# The denominator estimate of the fine holonomy bound (`τ` denominator sum)

`Work.Holonomy3.log_den_coeff_le` bounds the denominator of a coefficient of the auxiliary series
`F = Σ_i Q_i(x)·∏_s f_{i_s}(x_s)` of the box principle:

  `log den(β_n) ≤ (m·d·D/2)·(τ♭(b) + τ♯(e,ξ) + η)`  for all large `d` (with `m ∣ d`), `D`, small `ε`.

The coefficient `β_n` is a sum over the species vectors `i` and the monomials `k` of `Q i`; the
whole sum is cleared at once by the *single* common multiple `D1`, so that no loss in the number
of terms occurs:

* `[1,…,cmax]^{r·d}` and the identity-arranged lcm cap `refProd` clear the lcm part at the
  positions `n_j - k_j ≤ n_j` (and `log refProd` is the paper's `τ♭` cap, `log_lcm_cap_le`);
* `[1,…,⌊ξD⌋]^{Σe/m}` clears the primes below `ξD`, giving the `ξ·Σe` term of `τ♯`;
* the window products `L^{≥⌊ξD⌋}_{n_j,D}` and the proper prime powers clear the `n^{e}`
  denominators, giving the `(max e)·I_ξ^m(ξ)` term of `τ♯`.
-/

set_option maxHeartbeats 8000000
set_option linter.unusedTactic false
namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

/-! ## Elementary helpers -/

/-- `τ♯(e,ξ) ≥ 0` on the paper's range `0 ≤ ξ ≤ m`: a bound with `τ♭` only may be weakened to a
bound with `τ♭ + τ♯`. -/
theorem tauSharpAt_nonneg' {m : ℕ} (hm : 0 < m) (e : Fin m → ℕ) {ξ : ℝ} (h0 : 0 ≤ ξ)
    (hm' : ξ ≤ m) : 0 ≤ tauSharpAt e ξ := by
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h1 : min ξ 1 ≤ 1 := min_le_right _ _
  have h2 : max ξ 1 ≤ (m : ℝ) := by rw [max_le_iff]; exact ⟨hm', hm1R⟩
  have hharm : ∀ t : ℝ, 0 ≤ harmonicFun ξ t := fun t =>
    Finset.sum_nonneg (fun h _ => div_nonneg zero_le_one (Nat.cast_nonneg _))
  have hcorr : ∀ t : ℝ, 0 ≤ correctionFun ξ t := fun t => le_max_right _ _
  have hI : 0 ≤ integratedLcm ξ (m : ℝ) ξ := by
    rw [integratedLcm]
    exact add_nonneg (add_nonneg
        (intervalIntegral.integral_nonneg h1 (fun u _ => le_max_right _ _))
        (intervalIntegral.integral_nonneg h2 (fun u _ => hharm u)))
      (intervalIntegral.integral_nonneg h2 (fun u _ => hcorr u))
  rw [tauSharpAt]
  refine mul_nonneg (by positivity) (add_nonneg (mul_nonneg h0 ?_) ?_)
  · exact Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  · exact mul_nonneg (Nat.cast_nonneg _) hI

/-- `lcmUpto` is monotone in its argument. -/
lemma lcmUpto_dvd_of_le' {M N : ℕ} (h : M ≤ N) : lcmUpto M ∣ lcmUpto N := by
  unfold Submission.CDTPlan.lcmUpto
  exact Finset.lcm_mono (fun a ha => by simp only [Finset.mem_Icc] at ha ⊢; omega)

/-- The value of the identity position of the pair `(i,s)`. -/
lemma val_finProdFinEquiv_cast {m d : ℕ} (hmd : m ∣ d) (i : Fin m) (s : Fin (d / m)) :
    ((Fin.cast (Nat.mul_div_cancel' hmd) (finProdFinEquiv (i, s)) : Fin d) : ℕ)
      = i.1 * (d / m) + s.1 := by
  simp only [finProdFinEquiv, Equiv.coe_fn_mk, Fin.val_cast]
  ring_nf

/-- The renormalised identity position: `m·D·(j/d) = i·D + s·m·D/d` at `j = i·(d/m) + s`. -/
lemma mul_div_pos {m d : ℕ} (hm : 0 < m) (hmd : m ∣ d) (hd : 0 < d) (D : ℕ) (i : Fin m)
    (s : Fin (d / m)) :
    (m : ℝ) * D * (((Fin.cast (Nat.mul_div_cancel' hmd) (finProdFinEquiv (i, s)) : Fin d) : ℕ) : ℝ)
        / d
      = (i : ℝ) * D + (s : ℝ) * m * D / d := by
  have hk := Nat.mul_div_cancel' hmd
  have hkpos : 0 < d / m := by
    rcases Nat.eq_zero_or_pos (d / m) with h | h
    · rw [h, mul_zero] at hk; omega
    · exact h
  rw [val_finProdFinEquiv_cast hmd]
  have hcast : ((d : ℕ) : ℝ) = (m : ℝ) * ((d / m : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, hk]
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hkR : (0 : ℝ) < ((d / m : ℕ) : ℝ) := by exact_mod_cast hkpos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  push_cast
  rw [hcast]
  field_simp

/-- For a balanced species vector the sum of the `e`-weights is `(d/m)·Σe`. -/
lemma sum_balanced_e {m d : ℕ} (hmd : m ∣ d) (e : Fin m → ℕ) (i : Fin d → Fin m)
    (hi : Balanced i) : (∑ s : Fin d, e (i s)) = (d / m) * ∑ a : Fin m, e a := by
  have h1 : ∀ s : Fin d, e (i s) = ∑ a : Fin m, (if a = i s then e a else 0) := by
    intro s
    rw [Finset.sum_ite_eq' Finset.univ (i s) e]
    simp
  calc ∑ s : Fin d, e (i s)
      = ∑ s : Fin d, ∑ a : Fin m, (if a = i s then e a else 0) :=
        Finset.sum_congr rfl (fun s _ => h1 s)
    _ = ∑ a : Fin m, ∑ s : Fin d, (if a = i s then e a else 0) := Finset.sum_comm
    _ = ∑ a : Fin m, e a * (d / m) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
        congr 1
        have hfil : (Finset.univ.filter (fun s : Fin d => a = i s)) =
            (Finset.univ.filter (fun s : Fin d => i s = a)) := by
          refine Finset.filter_congr (fun s _ => ?_)
          exact eq_comm
        rw [hfil]
        exact hi a
    _ = (d / m) * ∑ a : Fin m, e a := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun a _ => Nat.mul_comm (e a) (d / m))


/-! ## The denominator estimate -/

/-- The logarithm of a product of six positive factors in the shape produced by `D1`. -/
lemma log_mul_six {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf : 0 < f) :
    Real.log (a * (b * (c * d)) * (e * f))
      = Real.log a + Real.log b + Real.log c + Real.log d + Real.log e + Real.log f := by
  have h1 : a * (b * (c * d)) ≠ 0 := by positivity
  have h2 : e * f ≠ 0 := by positivity
  have h3 : b * (c * d) ≠ 0 := by positivity
  have h4 : c * d ≠ 0 := by positivity
  rw [Real.log_mul h1 h2, Real.log_mul ha.ne' h3, Real.log_mul hb.ne' h4,
    Real.log_mul hc.ne' hd.ne', Real.log_mul he.ne' hf.ne']
  ring

/-- **The denominator estimate of the fine holonomy bound.**  The coefficient `β_n` of the
auxiliary series `F = Σ_i Q_i(x)·∏_s f_{i_s}(x_s)` (with `Q` supported on balanced species vectors,
partial degrees `< D` and integer coefficients, and `n` a monotone exponent vector with
`n_j ≤ m·D·(j/d) + 3mεD`) has denominator at most `exp((m·d·D/2)·(τ♭(b) + τ♯(e,ξ) + η))`. -/

theorem log_den_coeff_le {m r : ℕ} (hm : 0 < m) (b : Fin m → Fin r → ℕ)
    (hb : Submission.CDTPlan.ColumnShape b) (e : Fin m → ℕ) (f : Fin m → PowerSeries ℚ)
    (hden : ∀ i, Submission.CDTPlan.HasDenomType (e i) (b i) (f i))
    (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξm : ξ ≤ m) :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → m ∣ d →
      ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ n : Fin d → ℕ, Monotone n →
      (∀ j : Fin d, (n j : ℝ) ≤ (m : ℝ) * D * ((j : ℝ) / d) + 3 * m * ε * D) →
      ∀ Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ,
      (∀ i, Q i ≠ 0 → Work.Holonomy3.Balanced i) →
      (∀ i j, (Q i).degreeOf j < D) →
      (∀ i k, ∃ a : ℤ, (Q i).coeff k = a) →
      ∀ n' : Fin d →₀ ℕ, (∀ j, n' j = n j) →
      MvPowerSeries.coeff n' (Submission.CDTPlan.auxSeries f Q) ≠ 0 →
      Real.log ((Rat.den (MvPowerSeries.coeff n' (Submission.CDTPlan.auxSeries f Q)) : ℕ) : ℝ)
        ≤ ((m : ℝ) * d * D / 2) * (Submission.CDTPlan.tauFlat b
            + Submission.CDTPlan.tauSharpAt e ξ + η) := by
  classical
  intro η hη
  -- ## 0. the clearing data of the `f_i`
  set Kmax : ℕ := ∏ i : Fin m, (hden i).choose with hKmaxdef
  set cmax : ℕ := Finset.univ.sup (fun i : Fin m => (hden i).choose_spec.choose) with hcmaxdef
  set Nc : ℕ := ∏ i : Fin m, (PowerSeries.coeff 0 (f i)).den with hNcdef
  have hK : ∀ i : Fin m, (hden i).choose ∣ Kmax := fun i => by
    rw [hKmaxdef]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hc : ∀ i : Fin m, (hden i).choose_spec.choose ≤ cmax := fun i => by
    rw [hcmaxdef]
    exact Finset.le_sup (f := fun i : Fin m => (hden i).choose_spec.choose) (Finset.mem_univ i)
  have hNc : ∀ i : Fin m, (PowerSeries.coeff 0 (f i)).den ∣ Nc := fun i => by
    rw [hNcdef]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hKpos : 0 < Kmax := by
    rw [hKmaxdef]
    exact Finset.prod_pos (fun i _ => (hden i).choose_spec.choose_spec.1)
  have hNcpos : 0 < Nc := by
    rw [hNcdef]
    exact Finset.prod_pos (fun i _ => (PowerSeries.coeff 0 (f i)).den_pos)
  have hKmax1 : 1 ≤ Kmax := hKpos
  have hNc1 : 1 ≤ Nc := hNcpos
  have hcmaxpos : 0 < Submission.CDTPlan.lcmUpto cmax := Nat.lcmUpto_pos cmax
  -- ## 1. the rate constants
  set Se : ℕ := ∑ i : Fin m, e i with hSedef
  set Emax : ℕ := Finset.univ.sup e with hEmaxdef
  have heEmax : ∀ a : Fin m, e a ≤ Emax := fun a => by
    rw [hEmaxdef]; exact Finset.le_sup (f := e) (Finset.mem_univ a)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  -- the slack in the lcm asymptotic
  set δ : ℝ := min (1 / 4) (η * (m : ℝ) ^ 2 / (16 * (ξ * (Se : ℝ) + 1))) with hδdef
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨Kδ₀, hKδ₀⟩ := lcmUpto_log_le δ hδpos
  set Kδ : ℝ := max Kδ₀ 0 with hKδdef
  have hKδnonneg : 0 ≤ Kδ := le_max_right _ _
  have hKδ : ∀ N : ℕ, Real.log ((Submission.CDTPlan.lcmUpto N : ℕ) : ℝ)
      ≤ (1 + δ) * (N : ℝ) + Kδ := fun N =>
    le_trans (hKδ₀ N) (by rw [hKδdef]; linarith [le_max_left Kδ₀ 0])
  -- the `τ♭` cap
  obtain ⟨εl, hεlpos, hεlle1, dl, hdl⟩ := log_lcm_cap_le hm b hb cmax (η / 4) (by linarith)
  -- the `τ♯` window sum
  set ηq : ℝ := η * (m : ℝ) ^ 2 / (16 * ((Emax : ℝ) + 1)) with hηqdef
  have hηqpos : 0 < ηq := by rw [hηqdef]; positivity
  obtain ⟨εL, hεLpos, DL, hDL⟩ := sum_Lge_le_integral hm hξ0 hξm ηq hηqpos
  refine ⟨min (min εl εL) (1 / 4), ?_, ?_, max dl 1, ?_⟩
  · exact lt_min (lt_min hεlpos hεLpos) (by norm_num)
  · exact le_trans (min_le_right _ _) (by norm_num)
  intro d hdbase hmd
  have hdl' : dl ≤ d := le_trans (le_max_left _ _) hdbase
  have hd1 : 1 ≤ d := le_trans (le_max_right _ _) hdbase
  have hdpos : 0 < d := hd1
  obtain ⟨Dlcm, hDlcm⟩ := hdl d hdl' hmd
  -- absorption of the constants
  obtain ⟨Dabs, hDabs⟩ := log_absorb (m := m) (d := d) hm hdpos (η := 3 * η / 8) (by linarith)
    (A := (d : ℝ) * (Real.log ((Nc : ℝ) * Kmax)
        + (r : ℝ) * Real.log ((Submission.CDTPlan.lcmUpto cmax : ℕ) : ℝ))
          + ((d : ℝ) / (m : ℝ)) * (Se : ℝ) * Kδ)
    (B := 0) (by
      have hlogNc : 0 ≤ Real.log ((Nc : ℝ) * Kmax) := by
        refine Real.log_nonneg ?_
        have h1 : (1 : ℝ) ≤ (Nc : ℝ) := by exact_mod_cast hNc1
        have h2 : (1 : ℝ) ≤ (Kmax : ℝ) := by exact_mod_cast hKmax1
        nlinarith
      have hlogL : 0 ≤ Real.log ((Submission.CDTPlan.lcmUpto cmax : ℕ) : ℝ) := by
        refine Real.log_nonneg ?_
        have h1 : (1 : ℕ) ≤ Submission.CDTPlan.lcmUpto cmax := hcmaxpos
        exact_mod_cast h1
      refine add_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg hlogNc (mul_nonneg (Nat.cast_nonneg _) hlogL))) ?_
      exact mul_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hmR.le)
        (Nat.cast_nonneg _)) hKδnonneg) le_rfl
  -- absorption of the proper prime powers
  obtain ⟨Dsqr, hDsqr⟩ := sqrt_log_absorb (m := m) hm (η := η) hη
    (B := 4 * (Emax : ℝ) * (d : ℝ)) (by positivity)
  refine ⟨max (max (max Dlcm Dabs) DL) Dsqr, ?_⟩
  intro D hD ε hε hεlt n hn hbound Q hQbal hQdeg hQint n' hn' hcoeff
  have hDlcmle : Dlcm ≤ D := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hD))
  have hDabsle : Dabs ≤ D := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hD))
  have hDLle : DL ≤ D := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hD)
  have hDsqrle : Dsqr ≤ D := le_trans (le_max_right _ _) hD
  have hεltεl : ε < εl := lt_of_lt_of_le hεlt (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεltεL : ε < εL := lt_of_lt_of_le hεlt (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεlt4 : ε < 1 / 4 := lt_of_lt_of_le hεlt (min_le_right _ _)
  have hε1 : ε < 1 := by linarith
  -- ## 2. the reference (identity-arranged) lcm product
  set E : Fin m → Fin (d / m) → ℕ :=
    fun i s => n (Fin.cast (Nat.mul_div_cancel' hmd) (finProdFinEquiv (i, s))) with hEdef
  set refProd : ℕ := ∏ i : Fin m, ∏ s : Fin (d / m), ∏ h : Fin r,
    Submission.CDTPlan.lcmUpto (b i h * E i s + cmax) with hrefProd
  have hEbound : ∀ (i : Fin m) (s : Fin (d / m)),
      (E i s : ℝ) ≤ (i.1 : ℝ) * D + (s.1 : ℝ) * m * D / d + 3 * m * ε * D := by
    intro i s
    have h := hbound (Fin.cast (Nat.mul_div_cancel' hmd) (finProdFinEquiv (i, s)))
    have hsplit : (m : ℝ) * D
          * ((((Fin.cast (Nat.mul_div_cancel' hmd) (finProdFinEquiv (i, s)) : Fin d)) : ℕ) : ℝ)
            / d
        = (m : ℝ) * D
          * (((((Fin.cast (Nat.mul_div_cancel' hmd) (finProdFinEquiv (i, s)) : Fin d)) : ℕ) : ℝ)
            / d) := by ring
    rw [← hsplit, mul_div_pos hm hmd hdpos D i s] at h
    exact h
  have hcap : Real.log ((refProd : ℕ) : ℝ)
      ≤ ((m : ℝ) * d * D / 2) * (Submission.CDTPlan.tauFlat b + η / 4) := by
    have h := hDlcm D hDlcmle ε hε hεltεl E hEbound
    have hcast : ((refProd : ℕ) : ℝ) = ∏ i : Fin m, ∏ s : Fin (d / m), ∏ h : Fin r,
        ((Submission.CDTPlan.lcmUpto (b i h * E i s + cmax) : ℕ) : ℝ) := by
      rw [hrefProd]; push_cast; rfl
    rw [hcast]
    exact h
  -- ## 3. the common denominator `D1`
  set l : ℕ := ⌊ξ * (D : ℝ)⌋₊ with hldef
  set Dex : ℕ := (d / m) * Se with hDexdef
  set LgeP : ℕ := ∏ s : Fin d, Submission.CDT.LcmGe.Lge l (n s) D with hLgePdef
  set ppP : ℕ := ∏ s : Fin d, ppFac l (n s) with hppPdef
  set D1 : ℕ := ((Nc * Kmax) ^ d * ((Submission.CDTPlan.lcmUpto l) ^ Dex
      * (LgeP ^ Emax * ppP ^ Emax))) * ((Submission.CDTPlan.lcmUpto cmax) ^ (r * d) * refProd)
    with hD1def
  have hD1den : Rat.den (MvPowerSeries.coeff n' (Submission.CDTPlan.auxSeries f Q)) ∣ D1 := by
    refine den_dvd_iff_mul_castInt.mpr ?_
    rw [coeff_auxSeries]
    have hterm : ∀ (i : Fin d → Fin m) (k : Fin d →₀ ℕ),
        ∃ z : ℤ, (D1 : ℚ) * (if k ≤ n' then ((Q i).coeff k : ℚ) *
          ∏ s : Fin d, PowerSeries.coeff (n' s - k s) (f (i s)) else 0) = (z : ℚ) := by
      intro i k
      by_cases hle : k ≤ n'
      · rw [if_pos hle]
        by_cases hsupp : k ∈ (Q i).support
        · have hQne : Q i ≠ 0 := by
            intro h0
            rw [h0, MvPolynomial.support_zero] at hsupp
            exact absurd hsupp (Finset.notMem_empty k)
          have hbal : Balanced i := hQbal i hQne
          have hpos : ∀ s : Fin d,
              (n' s - k s = 0) ∨ (n s - D ≤ n' s - k s ∧ n' s - k s ≤ n s) := by
            intro s
            by_cases h0 : n' s - k s = 0
            · exact Or.inl h0
            · have hkdeg : k s ≤ (Q i).degreeOf s := MvPolynomial.monomial_le_degreeOf s hsupp
              have hklt : k s < D := lt_of_le_of_lt hkdeg (hQdeg i s)
              have hns' : n' s = n s := hn' s
              exact Or.inr ⟨by omega, by omega⟩
          have hdiv : (∏ s : Fin d, PowerSeries.coeff (n' s - k s) (f (i s))).den ∣ D1 := by
            refine dvd_trans (den_finsetProd_dvd _ _) ?_
            refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _
              (fun s _ => den_coeff_dvd_lcm b e f hden Kmax cmax Nc hK hc hNc (i s) (n' s - k s))) ?_
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
            refine Nat.mul_dvd_mul (Nat.mul_dvd_mul ?_ ?_) ?_
            · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            · have hw := pow_prod_dvd_window l D n (fun s => n' s - k s) (fun s => e (i s))
                Emax (fun s => heEmax (i s)) hpos
              rw [sum_balanced_e hmd e i hbal] at hw
              simpa only [← hDexdef, ← hSedef, ← hLgePdef, ← hppPdef, mul_assoc] using hw
            · -- the lcm part
              have hmono : ∏ s : Fin d, ∏ h : Fin r,
                    Submission.CDTPlan.lcmUpto (b (i s) h * (n' s - k s) + cmax)
                  ∣ ∏ s : Fin d, ∏ h : Fin r,
                    Submission.CDTPlan.lcmUpto (b (i s) h * (n s) + cmax) := by
                refine Finset.prod_dvd_prod_of_dvd _ _ (fun s _ => ?_)
                refine Finset.prod_dvd_prod_of_dvd _ _ (fun h _ => ?_)
                refine lcmUpto_dvd_of_le' ?_
                have h1 : n' s - k s ≤ n' s := Nat.sub_le _ _
                rw [← hn' s]; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h1) cmax
              refine dvd_trans hmono ?_
              have hshape := lcm_prod_dvd_shape hm b hb hmd cmax i hbal n hn
              simpa only [hrefProd, hEdef, mul_assoc] using hshape
          obtain ⟨z, hz⟩ := den_dvd_iff_mul_castInt.mp hdiv
          obtain ⟨a, ha⟩ := hQint i k
          refine ⟨a * z, ?_⟩
          rw [ha]
          rw [show (D1 : ℚ) * ((a : ℚ) * ∏ s : Fin d,
                PowerSeries.coeff (n' s - k s) (f (i s)))
              = (a : ℚ) * ((D1 : ℚ) * ∏ s : Fin d,
                PowerSeries.coeff (n' s - k s) (f (i s))) from by ring, hz]
          push_cast
          ring
        · have hz0 : (Q i).coeff k = 0 := MvPolynomial.notMem_support_iff.mp hsupp
          exact ⟨0, by rw [hz0]; ring⟩
      · rw [if_neg hle]
        exact ⟨0, by ring⟩
    rw [Finset.mul_sum]
    refine ⟨∑ i : Fin d → Fin m, ∑ k ∈ (Q i).support, (hterm i k).choose, ?_⟩
    have hcast : (((∑ i : Fin d → Fin m, ∑ k ∈ (Q i).support, (hterm i k).choose) : ℤ) : ℚ)
        = ∑ i : Fin d → Fin m, ∑ k ∈ (Q i).support, (((hterm i k).choose : ℤ) : ℚ) := by
      push_cast
      rfl
    rw [hcast]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => (hterm i k).choose_spec)
  -- ## 4. the logarithm of the common denominator
  have hD1pos : 0 < D1 := by
    have h1 : 0 < (Nc * Kmax) ^ d := pow_pos (Nat.mul_pos hNcpos hKpos) d
    have h2 : 0 < (Submission.CDTPlan.lcmUpto l) ^ Dex := pow_pos (Nat.lcmUpto_pos l) Dex
    have h3 : 0 < LgeP := by
      rw [hLgePdef]
      exact Finset.prod_pos (fun s _ => lt_of_lt_of_le Nat.zero_lt_one
        (Submission.CDT.Lcm2Bound.one_le_Lge l (n s) D))
    have h4 : 0 < ppP := by
      rw [hppPdef]
      exact Finset.prod_pos (fun s _ => ppFac_pos l (n s))
    have h5 : 0 < (Submission.CDTPlan.lcmUpto cmax) ^ (r * d) := pow_pos hcmaxpos _
    have h6 : 0 < refProd := by
      rw [hrefProd]
      exact Finset.prod_pos (fun i _ => Finset.prod_pos (fun s _ => Finset.prod_pos
        (fun h _ => Nat.lcmUpto_pos _)))
    rw [hD1def]
    exact Nat.mul_pos (Nat.mul_pos h1 (Nat.mul_pos h2 (Nat.mul_pos (pow_pos h3 Emax)
      (pow_pos h4 Emax)))) (Nat.mul_pos h5 h6)

  -- ## 5. the six pieces of `log D1`
  set al : ℝ := (m : ℝ) * d * D / 2 with haldef
  have halnn : 0 ≤ al := by rw [haldef]; positivity
  set S1 : ℝ := (d : ℝ) * Real.log ((Nc : ℝ) * Kmax) with hS1def
  set S2 : ℝ := (r : ℝ) * d * Real.log ((Submission.CDTPlan.lcmUpto cmax : ℕ) : ℝ) with hS2def
  set S3 : ℝ := ((d : ℝ) / (m : ℝ)) * (Se : ℝ) * Kδ with hS3def
  set S4 : ℝ := (Dex : ℝ) * Real.log ((Submission.CDTPlan.lcmUpto l : ℕ) : ℝ) with hS4def
  set S5 : ℝ := (Emax : ℝ) * Real.log (LgeP : ℝ) with hS5def
  set S6 : ℝ := (Emax : ℝ) * Real.log (ppP : ℝ) with hS6def
  set S7 : ℝ := Real.log (refProd : ℝ) with hS7def
  set X : ℝ := al * (2 * ξ * (Se : ℝ) / (m : ℝ) ^ 2) with hXdef
  set Y : ℝ := al * (2 * ((Emax : ℝ) / ((m : ℝ) ^ 2))
    * Submission.CDTPlan.integratedLcm ξ (m : ℝ) ξ) with hYdef
  set W : ℝ := ((d : ℝ) * D / (m : ℝ)) * (Emax : ℝ) * ηq with hWdef
  set Z : ℝ := al * (Submission.CDTPlan.tauFlat b + η / 4) with hZdef
  have hδslack : δ * (2 * ξ * (Se : ℝ) / (m : ℝ) ^ 2) ≤ η / 8 := by
    rcases eq_or_ne (ξ * (Se : ℝ)) 0 with h0 | h0
    · rw [show 2 * ξ * (Se : ℝ) = 2 * (ξ * (Se : ℝ)) from by ring, h0, mul_zero]
      simp only [zero_div, mul_zero]
      have : (0:ℝ) < η / 8 := by linarith
      linarith
    · have hpos : 0 < ξ * (Se : ℝ) :=
        lt_of_le_of_ne (mul_nonneg hξ0 (Nat.cast_nonneg _)) (Ne.symm h0)
      have hδle : δ ≤ η * (m : ℝ) ^ 2 / (16 * (ξ * (Se : ℝ) + 1)) := min_le_right _ _
      have hstep : δ * (2 * ξ * (Se : ℝ) / (m : ℝ) ^ 2)
          = (δ * (2 * ξ * (Se : ℝ))) / (m : ℝ) ^ 2 := by ring
      rw [hstep]
      calc (δ * (2 * ξ * (Se : ℝ))) / (m : ℝ) ^ 2
          ≤ ((η * (m : ℝ) ^ 2 / (16 * (ξ * (Se : ℝ) + 1))) * (2 * ξ * (Se : ℝ)))
              / (m : ℝ) ^ 2 := by
            refine div_le_div_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right hδle (by positivity)
        _ = η * (ξ * (Se : ℝ)) / (8 * (ξ * (Se : ℝ) + 1)) := by
            first | (field_simp; ring) | field_simp
        _ ≤ η / 8 := by
            rw [div_le_iff₀ (by linarith : (0:ℝ) < 8 * (ξ * (Se : ℝ) + 1))]
            nlinarith [hpos.le, hη.le]
  have hXnn : 0 ≤ X := by
    rw [hXdef]
    have h1 : (0:ℝ) ≤ 2 * ξ * (Se : ℝ) := mul_nonneg (mul_nonneg (by norm_num) hξ0)
      (Nat.cast_nonneg _)
    have h2 : (0:ℝ) ≤ (m : ℝ) ^ 2 := by positivity
    exact mul_nonneg halnn (div_nonneg h1 h2)
  have hδkey : δ * X ≤ al * (η / 8) := by
    rw [hXdef]
    have hw := mul_le_mul_of_nonneg_left hδslack halnn
    calc δ * (al * (2 * ξ * (Se : ℝ) / (m : ℝ) ^ 2))
        = al * (δ * (2 * ξ * (Se : ℝ) / (m : ℝ) ^ 2)) := by ring
      _ ≤ al * (η / 8) := hw
  have hDexR : (Dex : ℝ) ≤ ((d : ℝ) / (m : ℝ)) * (Se : ℝ) := by
    have h1 : (((d / m : ℕ)) : ℝ) ≤ (d : ℝ) / (m : ℝ) := by
      rw [le_div_iff₀ hmR, ← Nat.cast_mul]
      exact_mod_cast Nat.div_mul_le_self d m
    rw [hDexdef]
    push_cast
    exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
  have hA1 : S1 + S2 + S3 ≤ al * (η / 8) := by
    rw [hS1def, hS2def, hS3def, haldef]
    have h := hDabs D hDabsle
    have hz : 0 * Real.log (4 * (m : ℝ) * (D : ℝ)) = (0 : ℝ) := by ring
    rw [hz, add_zero] at h
    have h3 : ((m : ℝ) * d * D / 2) * ((3 * η / 8) / 3) = ((m : ℝ) * d * D / 2) * (η / 8) := by
      ring
    rw [h3] at h
    have h4 : (d : ℝ) * (Real.log ((Nc : ℝ) * Kmax)
          + (r : ℝ) * Real.log ((Submission.CDTPlan.lcmUpto cmax : ℕ) : ℝ))
        = (d : ℝ) * Real.log ((Nc : ℝ) * Kmax)
          + (r : ℝ) * d * Real.log ((Submission.CDTPlan.lcmUpto cmax : ℕ) : ℝ) := by ring
    rw [h4] at h
    exact h
  have hS4 : S4 ≤ X + δ * X + S3 := by
    rw [hS4def, hXdef, hS3def, haldef]
    have hl : Real.log ((Submission.CDTPlan.lcmUpto l : ℕ) : ℝ) ≤ (1 + δ) * (l : ℝ) + Kδ := hKδ l
    have hlD : (l : ℝ) ≤ ξ * (D : ℝ) := by
      rw [hldef]
      exact Nat.floor_le (by positivity)
    have hstep : (Dex : ℝ) * Real.log ((Submission.CDTPlan.lcmUpto l : ℕ) : ℝ)
        ≤ (Dex : ℝ) * ((1 + δ) * (l : ℝ) + Kδ) :=
      mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _)
    have hsub : (Dex : ℝ) * ((1 + δ) * (l : ℝ) + Kδ)
        ≤ (1 + δ) * (((d : ℝ) / (m : ℝ)) * (Se : ℝ) * (ξ * (D : ℝ)))
          + ((d : ℝ) / (m : ℝ)) * (Se : ℝ) * Kδ := by
      have h1 : (Dex : ℝ) * ((1 + δ) * (l : ℝ)) ≤ (1 + δ) * ((Dex : ℝ) * (ξ * (D : ℝ))) := by
        have hmul : (Dex : ℝ) * ((1 + δ) * (l : ℝ)) = (1 + δ) * ((Dex : ℝ) * (l : ℝ)) := by ring
        rw [hmul]
        refine mul_le_mul_of_nonneg_left ?_ (by linarith [hδpos.le])
        exact mul_le_mul_of_nonneg_left hlD (Nat.cast_nonneg _)
      have h1' : (1 + δ) * ((Dex : ℝ) * (ξ * (D : ℝ)))
          ≤ (1 + δ) * (((d : ℝ) / (m : ℝ)) * (Se : ℝ) * (ξ * (D : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith [hδpos.le])
        exact mul_le_mul_of_nonneg_right hDexR (by positivity)
      have h2 : (Dex : ℝ) * Kδ ≤ ((d : ℝ) / (m : ℝ)) * (Se : ℝ) * Kδ :=
        mul_le_mul_of_nonneg_right hDexR hKδnonneg
      have h3 : (Dex : ℝ) * ((1 + δ) * (l : ℝ) + Kδ)
          = (Dex : ℝ) * ((1 + δ) * (l : ℝ)) + (Dex : ℝ) * Kδ := by ring
      rw [h3]
      exact add_le_add (le_trans h1 h1') h2
    have hkey : ((m : ℝ) * d * D / 2) * (2 * ξ * (Se : ℝ) / (m : ℝ) ^ 2)
        = ((d : ℝ) / (m : ℝ)) * (Se : ℝ) * (ξ * (D : ℝ)) := by
      first | (field_simp; ring) | field_simp
    have hfin : (1 + δ) * (((m : ℝ) * d * D / 2) * (2 * ξ * (Se : ℝ) / (m : ℝ) ^ 2))
        = ((m : ℝ) * d * D / 2) * (2 * ξ * (Se : ℝ) / (m : ℝ) ^ 2)
          + δ * (((m : ℝ) * d * D / 2) * (2 * ξ * (Se : ℝ) / (m : ℝ) ^ 2)) := by ring
    have h4 := hstep.trans hsub
    rw [← hkey, hfin] at h4
    exact h4
  have hLge1 : ∀ s : Fin d, 1 ≤ Submission.CDT.LcmGe.Lge l (n s) D :=
    fun s => Submission.CDT.Lcm2Bound.one_le_Lge l (n s) D
  have hS5 : S5 ≤ Y + W := by
    rw [hS5def, hYdef, hWdef, haldef]
    have hlog : Real.log (LgeP : ℝ)
        = ∑ s : Fin d, Real.log ((Submission.CDT.LcmGe.Lge l (n s) D : ℕ) : ℝ) := by
      rw [hLgePdef]
      push_cast
      rw [Real.log_prod]
      intro s _
      have h2 : (0 : ℝ) < ((Submission.CDT.LcmGe.Lge l (n s) D : ℕ) : ℝ) := by
        exact_mod_cast (hLge1 s)
      exact ne_of_gt h2
    have hsum := hDL D hDLle d hdpos ε hε hεltεL n hn hbound
    rw [hlog]
    have h2 : (Emax : ℝ) * ∑ s : Fin d, Real.log ((Submission.CDT.LcmGe.Lge l (n s) D : ℕ) : ℝ)
        ≤ (Emax : ℝ) * (((d : ℝ) * D / m)
            * (Submission.CDTPlan.integratedLcm ξ (m : ℝ) ξ + ηq)) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    have hkey : (Emax : ℝ) * (((d : ℝ) * D / m)
          * (Submission.CDTPlan.integratedLcm ξ (m : ℝ) ξ + ηq))
        = ((m : ℝ) * d * D / 2) * (2 * ((Emax : ℝ) / ((m : ℝ) ^ 2))
            * Submission.CDTPlan.integratedLcm ξ (m : ℝ) ξ)
          + ((d : ℝ) * D / (m : ℝ)) * (Emax : ℝ) * ηq := by
      first | (field_simp; ring) | field_simp
    linarith [h2, hkey.le, hkey.ge]
  have hηq : W ≤ al * (η / 8) := by
    rw [hWdef, hηqdef, haldef]
    have hkey : (d : ℝ) * D / (m : ℝ) * (Emax : ℝ) * (η * (m : ℝ) ^ 2 / (16 * ((Emax : ℝ) + 1)))
        = ((m : ℝ) * d * D / 2) * (η / 8) * ((Emax : ℝ) / ((Emax : ℝ) + 1)) := by
      first | (field_simp; ring) | field_simp
    rw [hkey]
    have hratio : (Emax : ℝ) / ((Emax : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have hnn : (0 : ℝ) ≤ ((m : ℝ) * d * D / 2) * (η / 8) := by positivity
    calc ((m : ℝ) * d * D / 2) * (η / 8) * ((Emax : ℝ) / ((Emax : ℝ) + 1))
        ≤ ((m : ℝ) * d * D / 2) * (η / 8) * 1 := mul_le_mul_of_nonneg_left hratio hnn
      _ = ((m : ℝ) * d * D / 2) * (η / 8) := by ring
  have hPPbound : Real.log (ppP : ℝ) ≤ (d : ℝ) * (4 * Real.sqrt (4 * (m : ℝ) * D + 1)
      * (1 + Real.log (4 * (m : ℝ) * D + 1))) := by
    set C : ℝ := 4 * Real.sqrt (4 * (m : ℝ) * D + 1)
      * (1 + Real.log (4 * (m : ℝ) * D + 1)) with hCdef
    have hpt : ∀ s : Fin d, Real.log ((ppFac l (n s) : ℕ) : ℝ) ≤ C := by
      intro s
      refine le_trans (log_ppFac_bound l (n s)) ?_
      have hns : (n s : ℝ) ≤ 4 * (m : ℝ) * D := by
        have h1 := hbound s
        have h2 : ((s : ℕ) : ℝ) / d ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact_mod_cast (le_of_lt s.2)
        have hstep : (m : ℝ) * D * (((s : ℕ) : ℝ) / d) ≤ (m : ℝ) * D := by
          have h0 : (0 : ℝ) ≤ (m : ℝ) * D := by positivity
          simpa using mul_le_of_le_one_right h0 h2
        have hε3 : 3 * (m : ℝ) * ε * D ≤ 3 * (m : ℝ) * D := by
          have h0 : (0 : ℝ) ≤ 3 * (m : ℝ) * D := by positivity
          have h1 : ε * D ≤ 1 * D := mul_le_mul_of_nonneg_right hε1.le (Nat.cast_nonneg _)
          have h2 : 3 * (m : ℝ) * (ε * D) ≤ 3 * (m : ℝ) * (1 * D) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
          nlinarith [h2]
        linarith [h1, hstep, hε3]
      have h1 : (n s : ℝ) + 1 ≤ 4 * (m : ℝ) * D + 1 := by linarith
      have h2 : Real.sqrt ((n s : ℝ) + 1) ≤ Real.sqrt (4 * (m : ℝ) * D + 1) :=
        Real.sqrt_le_sqrt h1
      have h3 : Real.log ((n s : ℝ) + 1) ≤ Real.log (4 * (m : ℝ) * D + 1) :=
        Real.log_le_log (by positivity) h1
      have h4 : (0 : ℝ) ≤ Real.sqrt ((n s : ℝ) + 1) := Real.sqrt_nonneg _
      have h5 : (0 : ℝ) ≤ Real.sqrt (4 * (m : ℝ) * D + 1) := Real.sqrt_nonneg _
      have h6 : (0 : ℝ) ≤ 1 + Real.log ((n s : ℝ) + 1) := by
        have h7 : (1:ℝ) ≤ (n s : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) (n s)]
        linarith [Real.log_nonneg h7]
      have h7 : (0 : ℝ) ≤ 1 + Real.log (4 * (m : ℝ) * D + 1) := by
        have h8 : (1:ℝ) ≤ 4 * (m : ℝ) * D + 1 := by linarith [Nat.cast_nonneg (α := ℝ) D, hmR]
        linarith [Real.log_nonneg h8]
      rw [hCdef]
      nlinarith [h2, h3, h4, h5, h6, h7]
    have hlog : Real.log (ppP : ℝ) = ∑ s : Fin d, Real.log ((ppFac l (n s) : ℕ) : ℝ) := by
      rw [hppPdef]
      push_cast
      rw [Real.log_prod]
      intro s _
      have h2 : (0 : ℝ) < ((ppFac l (n s) : ℕ) : ℝ) := by exact_mod_cast (ppFac_pos l (n s))
      exact ne_of_gt h2
    rw [hlog]
    calc ∑ s : Fin d, Real.log ((ppFac l (n s) : ℕ) : ℝ)
        ≤ ∑ _s : Fin d, C := Finset.sum_le_sum (fun s _ => hpt s)
      _ = (d : ℝ) * C := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (d : ℝ) * (4 * Real.sqrt (4 * (m : ℝ) * D + 1)
            * (1 + Real.log (4 * (m : ℝ) * D + 1))) := by rw [hCdef]
  have hS6 : S6 ≤ al * (η / 8) := by
    rw [hS6def, haldef]
    refine (mul_le_mul_of_nonneg_left hPPbound (Nat.cast_nonneg _)).trans ?_
    have h := hDsqr D hDsqrle
    have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    calc (Emax : ℝ) * ((d : ℝ) * (4 * Real.sqrt (4 * (m : ℝ) * D + 1)
          * (1 + Real.log (4 * (m : ℝ) * D + 1))))
        = 4 * (Emax : ℝ) * (d : ℝ) * (Real.sqrt (4 * (m : ℝ) * D + 1)
            * (1 + Real.log (4 * (m : ℝ) * D + 1))) := by ring
      _ ≤ ((m : ℝ) * D / 2) * (η / 8) := h
      _ ≤ ((m : ℝ) * d * D / 2) * (η / 8) := by
          have h0 : (0 : ℝ) ≤ η / 8 := by linarith
          have h1 : (m : ℝ) * D / 2 ≤ (m : ℝ) * d * D / 2 := by
            nlinarith [hd1R, hmR, Nat.cast_nonneg (α := ℝ) D]
          exact mul_le_mul_of_nonneg_right h1 h0
  have hlogD1 : Real.log (D1 : ℝ) = S1 + S2 + S4 + S5 + S6 + S7 := by
    have hA : (0:ℝ) < ((Nc : ℝ) * Kmax) ^ d := by
      have h1 : (0:ℝ) < (Nc : ℝ) * Kmax := by
        have h2 : (0:ℝ) < (Nc : ℝ) := by exact_mod_cast hNcpos
        have h3 : (0:ℝ) < (Kmax : ℝ) := by exact_mod_cast hKpos
        exact mul_pos h2 h3
      positivity
    have hB : (0:ℝ) < ((Submission.CDTPlan.lcmUpto l : ℕ) : ℝ) ^ Dex := by
      have h1 : (0:ℝ) < ((Submission.CDTPlan.lcmUpto l : ℕ) : ℝ) := by
        exact_mod_cast (Nat.lcmUpto_pos l)
      positivity
    have hC : (0:ℝ) < (LgeP : ℝ) ^ Emax := by
      have h1 : (0:ℝ) < (LgeP : ℝ) := by
        rw [hLgePdef]
        exact_mod_cast (Finset.prod_pos (fun s _ => lt_of_lt_of_le Nat.zero_lt_one (hLge1 s)))
      positivity
    have hD : (0:ℝ) < (ppP : ℝ) ^ Emax := by
      have h1 : (0:ℝ) < (ppP : ℝ) := by
        rw [hppPdef]
        exact_mod_cast (Finset.prod_pos (fun s _ => ppFac_pos l (n s)))
      positivity
    have hE : (0:ℝ) < ((Submission.CDTPlan.lcmUpto cmax : ℕ) : ℝ) ^ (r * d) := by
      have h1 : (0:ℝ) < ((Submission.CDTPlan.lcmUpto cmax : ℕ) : ℝ) := by
        exact_mod_cast hcmaxpos
      positivity
    have hF : (0:ℝ) < (refProd : ℝ) := by
      rw [hrefProd]
      exact_mod_cast (Finset.prod_pos (fun i _ => Finset.prod_pos (fun s _ =>
        Finset.prod_pos (fun h _ => Nat.lcmUpto_pos _))))
    rw [hD1def]
    push_cast
    rw [log_mul_six hA hB hC hD hE hF]
    rw [Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    rw [hS1def, hS2def, hS4def, hS5def, hS6def, hS7def]
    push_cast
    ring
  have hτ : X + Y = al * Submission.CDTPlan.tauSharpAt e ξ := by
    rw [hXdef, hYdef, haldef, tauSharpAt, hSedef, hEmaxdef]
    push_cast
    first | (field_simp; ring) | field_simp
  have hfinal : Real.log (D1 : ℝ) ≤ al * (Submission.CDTPlan.tauFlat b
      + Submission.CDTPlan.tauSharpAt e ξ + η) := by
    have hstep1 : Real.log (D1 : ℝ) ≤ (S1 + S2 + S3) + (X + δ * X) + (Y + W)
        + al * (η / 8) + Z := by
      rw [hlogD1]
      linarith [hA1, hS4, hS5, hS6, hcap, halnn]
    have hstep2 : (S1 + S2 + S3) + (X + δ * X) + (Y + W) + al * (η / 8) + Z
        ≤ al * (η / 8) + X + al * (η / 8) + Y + al * (η / 8) + al * (η / 8) + Z := by
      linarith [hA1, hδkey, hηq]
    have hstep3 : al * (η / 8) + X + al * (η / 8) + Y + al * (η / 8) + al * (η / 8) + Z
        ≤ al * (3 * η / 4) + X + Y + al * Submission.CDTPlan.tauFlat b := by
      rw [hZdef]
      nlinarith [halnn, hη.le]
    have hstep4 : al * (3 * η / 4) + X + Y + al * Submission.CDTPlan.tauFlat b
        ≤ al * (Submission.CDTPlan.tauFlat b + Submission.CDTPlan.tauSharpAt e ξ + η) := by
      have hXY : X + Y = al * Submission.CDTPlan.tauSharpAt e ξ := hτ
      have h3 : al * (3 * η / 4) + X + Y + al * Submission.CDTPlan.tauFlat b
          = al * (3 * η / 4) + (X + Y) + al * Submission.CDTPlan.tauFlat b := by ring
      rw [h3, hXY]
      nlinarith [halnn, hη.le]
    linarith [hstep1, hstep2, hstep3, hstep4]
  have hlogden : Real.log ((Rat.den (MvPowerSeries.coeff n'
        (Submission.CDTPlan.auxSeries f Q)) : ℕ) : ℝ) ≤ Real.log (D1 : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_of_dvd hD1pos hD1den)
  exact le_trans hlogden hfinal

end Work.Holonomy3
