import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmSetup
import Submission.Work.LinnikAreas.Density4.sum_tau_mul_rpow_neg_le
import Submission.Work.LinnikAreas.Density4.sum_filter_dvd_rpow_neg_le
import Submission.Work.LinnikAreas.Density4.lcmF_eq_sum_floor

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

/-- A single term of `lcmF`: `psi_d theta_e chi([d,e]) [d,e]^{-s}`. -/
def lcmTerm (q : ℕ) (U V W : ℝ) (χ : DirichletCharacter ℂ q) (s : ℂ) (d e : ℕ) : ℂ :=
  ((psiM U V d : ℝ) : ℂ) * ((thetaM W e : ℝ) : ℂ) * (χ ((Nat.lcm d e : ℕ) : ZMod q))
    * (((Nat.lcm d e : ℕ) : ℂ) ^ (-s))

/-- `lcmF` reindexed to the floor cut-offs: the terms with `d > V` or `e > W` vanish. -/
lemma lcmF_eq_sum_lcmTerm (q : ℕ) [NeZero q] {U V W : ℝ} (hUV : U ≤ V)
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    lcmF q U V W χ s
      = ∑ d ∈ Finset.Icc 1 (Nat.floor V), ∑ e ∈ Finset.Icc 1 (Nat.floor W),
          lcmTerm q U V W χ s d e := by
  simpa [lcmTerm] using lcmF_eq_sum_floor q hUV χ s

/-- Norm bound for a single term of `lcmF`. -/
lemma norm_lcmTerm_le (q : ℕ) [NeZero q] {U V W : ℝ} (hU : 0 < U) (χ : DirichletCharacter ℂ q)
    {s : ℂ} {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) :
    ‖lcmTerm q U V W χ s d e‖ ≤ ((Nat.lcm d e : ℕ) : ℝ) ^ (-s.re) := by
  have hlcm1 : 1 ≤ Nat.lcm d e :=
    Nat.one_le_iff_ne_zero.mpr (Nat.lcm_ne_zero (by omega) (by omega))
  have hcpow : ‖(((Nat.lcm d e : ℕ) : ℂ) ^ (-s))‖ = ((Nat.lcm d e : ℕ) : ℝ) ^ (-s.re) := by
    have h1 : (((Nat.lcm d e : ℕ) : ℂ)) = (((Nat.lcm d e : ℕ) : ℝ) : ℂ) := by simp
    rw [h1, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
  rw [lcmTerm]
  calc ‖(psiM U V d : ℂ) * (thetaM W e : ℂ) * (χ ((Nat.lcm d e : ℕ) : ZMod q))
        * (((Nat.lcm d e : ℕ) : ℂ) ^ (-s))‖
      = ‖(psiM U V d : ℂ)‖ * ‖(thetaM W e : ℂ)‖ * ‖(χ ((Nat.lcm d e : ℕ) : ZMod q))‖
          * ‖(((Nat.lcm d e : ℕ) : ℂ) ^ (-s))‖ := by simp only [norm_mul]
    _ ≤ 1 * 1 * 1 * ((Nat.lcm d e : ℕ) : ℝ) ^ (-s.re) := by
        have h1 : ‖(psiM U V d : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_psiM_le_one hU d
        have h2 : ‖(thetaM W e : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_thetaM_le_one W e
        have h3 : ‖(χ ((Nat.lcm d e : ℕ) : ZMod q) : ℂ)‖ ≤ 1 := norm_le_one χ _
        have h4 : (0:ℝ) ≤ ((Nat.lcm d e : ℕ) : ℝ) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
        rw [hcpow]
        exact mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)) h3
          (norm_nonneg _) (by norm_num)) le_rfl h4 (by positivity)
    _ = ((Nat.lcm d e : ℕ) : ℝ) ^ (-s.re) := by ring

/-- The lcm/gcd identity: `lcm(d,e) = d*e/gcd(d,e)`, hence
`lcm(d,e)^{-sigma} = d^{-sigma} e^{-sigma} gcd(d,e)^sigma`. -/
lemma lcm_rpow_neg_eq {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) (σ : ℝ) :
    ((Nat.lcm d e : ℕ) : ℝ) ^ (-σ)
      = (d : ℝ) ^ (-σ) * (e : ℝ) ^ (-σ) * ((Nat.gcd d e : ℕ) : ℝ) ^ σ := by
  have hLg : ((Nat.lcm d e : ℕ) : ℝ) * ((Nat.gcd d e : ℕ) : ℝ) = (d : ℝ) * (e : ℝ) := by
    exact_mod_cast Nat.lcm_mul_gcd d e
  have hg0 : ((Nat.gcd d e : ℕ) : ℝ) ≠ 0 := by
    have : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left e (by omega)
    positivity
  have hL : ((Nat.lcm d e : ℕ) : ℝ) = (d : ℝ) * (e : ℝ) / ((Nat.gcd d e : ℕ) : ℝ) := by
    rw [eq_div_iff hg0]; exact hLg
  rw [hL, Real.div_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ ((Nat.gcd d e : ℕ) : ℝ)), div_inv_eq_mul]

/-- The gcd is at most the sum of `h^sigma` over the common divisors `h` of `d` and `e`. -/
lemma gcd_rpow_le_sum_common_divisors {d e : ℕ} (hd : 1 ≤ d) {σ : ℝ} :
    ((Nat.gcd d e : ℕ) : ℝ) ^ σ ≤ ∑ h ∈ d.divisors with h ∣ e, (h : ℝ) ^ σ := by
  refine Finset.single_le_sum (fun h _ => Real.rpow_nonneg (by positivity) _) ?_
  rw [Finset.mem_filter, Nat.mem_divisors]
  exact ⟨⟨Nat.gcd_dvd_left d e, by omega⟩, Nat.gcd_dvd_right d e⟩

/-- Termwise: `lcm(d,e)^{-sigma} <= d^{-sigma} e^{-sigma} sum_{h | d, h | e} h^sigma`. -/
lemma lcm_rpow_neg_le_sum {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) {σ : ℝ} :
    ((Nat.lcm d e : ℕ) : ℝ) ^ (-σ)
      ≤ (d : ℝ) ^ (-σ) * (e : ℝ) ^ (-σ) * (∑ h ∈ d.divisors with h ∣ e, (h : ℝ) ^ σ) := by
  rw [lcm_rpow_neg_eq hd he σ]
  exact mul_le_mul_of_nonneg_left (gcd_rpow_le_sum_common_divisors hd)
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _))

/-- Inner estimate: for fixed `d`, the sum over `e <= B` of `lcm(d,e)^{-sigma}` is at most
`d^{-sigma} tau(d) B^{1-sigma}(1 + log B)`. -/
lemma sum_lcm_inner_le {B d : ℕ} (hd : 1 ≤ d) (hB : 1 ≤ B) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) :
    ∑ e ∈ Finset.Icc 1 B, (d : ℝ) ^ (-σ) * (e : ℝ) ^ (-σ)
        * (∑ h ∈ d.divisors with h ∣ e, (h : ℝ) ^ σ)
      ≤ (d : ℝ) ^ (-σ) * ((d.divisors.card : ℕ) : ℝ)
          * ((B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ))) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hlogB : 0 ≤ 1 + Real.log (B : ℝ) := by
    have : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
    linarith only [this]
  have hXnn : 0 ≤ (B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hB0.le _) hlogB
  have hkey : ∑ e ∈ Finset.Icc 1 B, (d : ℝ) ^ (-σ) * (e : ℝ) ^ (-σ)
        * (∑ h ∈ d.divisors with h ∣ e, (h : ℝ) ^ σ)
      = ∑ h ∈ d.divisors, ∑ e ∈ Finset.Icc 1 B with h ∣ e,
          (d : ℝ) ^ (-σ) * (h : ℝ) ^ σ * (e : ℝ) ^ (-σ) := by
    have h1 : ∑ e ∈ Finset.Icc 1 B, (d : ℝ) ^ (-σ) * (e : ℝ) ^ (-σ)
        * (∑ h ∈ d.divisors with h ∣ e, (h : ℝ) ^ σ)
        = ∑ e ∈ Finset.Icc 1 B, ∑ h ∈ d.divisors,
            (if h ∣ e then (d : ℝ) ^ (-σ) * (e : ℝ) ^ (-σ) * (h : ℝ) ^ σ else 0) := by
      simp only [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro h hh
      by_cases hc : h ∣ e <;> simp [hc]
    have h2 : (∑ e ∈ Finset.Icc 1 B, ∑ h ∈ d.divisors,
            (if h ∣ e then (d : ℝ) ^ (-σ) * (e : ℝ) ^ (-σ) * (h : ℝ) ^ σ else 0))
        = ∑ h ∈ d.divisors, ∑ e ∈ Finset.Icc 1 B,
            (if h ∣ e then (d : ℝ) ^ (-σ) * (e : ℝ) ^ (-σ) * (h : ℝ) ^ σ else 0) :=
      Finset.sum_comm
    have h3 : (∑ h ∈ d.divisors, ∑ e ∈ Finset.Icc 1 B,
            (if h ∣ e then (d : ℝ) ^ (-σ) * (e : ℝ) ^ (-σ) * (h : ℝ) ^ σ else 0))
        = ∑ h ∈ d.divisors, ∑ e ∈ Finset.Icc 1 B with h ∣ e,
            (d : ℝ) ^ (-σ) * (h : ℝ) ^ σ * (e : ℝ) ^ (-σ) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hc : h ∣ e <;> simp only [hc, ↓reduceIte]
      ring
    rw [h1, h2, h3]
  rw [hkey]
  calc ∑ h ∈ d.divisors, ∑ e ∈ Finset.Icc 1 B with h ∣ e,
          (d : ℝ) ^ (-σ) * (h : ℝ) ^ σ * (e : ℝ) ^ (-σ)
      = ∑ h ∈ d.divisors, (d : ℝ) ^ (-σ) * (h : ℝ) ^ σ
          * (∑ e ∈ Finset.Icc 1 B with h ∣ e, (e : ℝ) ^ (-σ)) := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [Finset.mul_sum]
    _ ≤ ∑ h ∈ d.divisors,
          (d : ℝ) ^ (-σ) * ((B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ))) := by
        apply Finset.sum_le_sum
        intro h hh
        have hh1 : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr (Nat.pos_of_mem_divisors hh).ne'
        have hh0 : (0 : ℝ) < h := by positivity
        have hbd := sum_filter_dvd_rpow_neg_le hh1 hB hσ0 hσ1
        have hle1 : (h : ℝ) ^ σ * (∑ e ∈ Finset.Icc 1 B with h ∣ e, (e : ℝ) ^ (-σ))
            ≤ (h : ℝ) ^ σ
              * (((B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ))) / (h : ℝ)) :=
          mul_le_mul_of_nonneg_left hbd (Real.rpow_nonneg hh0.le _)
        have hcollapse : (h : ℝ) ^ σ
                * (((B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ))) / (h : ℝ))
            ≤ (B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ)) := by
          have hpow : (h : ℝ) ^ σ / (h : ℝ) = (h : ℝ) ^ (σ - 1) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hh0,
              show σ + (-1) = σ - 1 by ring]
          have hle1' : (h : ℝ) ^ (σ - 1) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hh1) (by linarith only [hσ1])
          calc (h : ℝ) ^ σ * (((B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ))) / (h : ℝ))
              = ((B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ))) * ((h : ℝ) ^ σ / (h : ℝ)) := by
                ring
            _ = ((B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ))) * (h : ℝ) ^ (σ - 1) := by rw [hpow]
            _ ≤ ((B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ))) * 1 :=
                mul_le_mul_of_nonneg_left hle1' hXnn
            _ = (B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ)) := by ring
        calc (d : ℝ) ^ (-σ) * (h : ℝ) ^ σ * (∑ e ∈ Finset.Icc 1 B with h ∣ e, (e : ℝ) ^ (-σ))
            = (d : ℝ) ^ (-σ) * ((h : ℝ) ^ σ
                * (∑ e ∈ Finset.Icc 1 B with h ∣ e, (e : ℝ) ^ (-σ))) := by ring
          _ ≤ (d : ℝ) ^ (-σ) * ((h : ℝ) ^ σ
                * (((B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ))) / (h : ℝ))) :=
              mul_le_mul_of_nonneg_left hle1 (Real.rpow_nonneg hd0.le _)
          _ ≤ (d : ℝ) ^ (-σ) * ((B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ))) :=
              mul_le_mul_of_nonneg_left hcollapse (Real.rpow_nonneg hd0.le _)
    _ = (d : ℝ) ^ (-σ) * ((d.divisors.card : ℕ) : ℝ)
          * ((B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- The double sum over `lcm`. -/
lemma sum_lcm_rpow_neg_le {A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) :
    ∑ d ∈ Finset.Icc 1 A, ∑ e ∈ Finset.Icc 1 B, ((Nat.lcm d e : ℕ) : ℝ) ^ (-σ)
      ≤ (A : ℝ) ^ (1 - σ) * (B : ℝ) ^ (1 - σ) * (1 + Real.log (A : ℝ)) ^ 2
          * (1 + Real.log (B : ℝ)) := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hlogB : 0 ≤ 1 + Real.log (B : ℝ) := by
    have : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
    linarith only [this]
  have hXnn : 0 ≤ (B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hB0.le _) hlogB
  calc ∑ d ∈ Finset.Icc 1 A, ∑ e ∈ Finset.Icc 1 B, ((Nat.lcm d e : ℕ) : ℝ) ^ (-σ)
      ≤ ∑ d ∈ Finset.Icc 1 A, ∑ e ∈ Finset.Icc 1 B,
          (d : ℝ) ^ (-σ) * (e : ℝ) ^ (-σ) * (∑ h ∈ d.divisors with h ∣ e, (h : ℝ) ^ σ) := by
        apply Finset.sum_le_sum; intro d hd
        apply Finset.sum_le_sum; intro e he
        exact lcm_rpow_neg_le_sum (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
    _ ≤ ∑ d ∈ Finset.Icc 1 A, (d : ℝ) ^ (-σ) * ((d.divisors.card : ℕ) : ℝ)
          * ((B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ))) := by
        apply Finset.sum_le_sum; intro d hd
        exact sum_lcm_inner_le (Finset.mem_Icc.mp hd).1 hB hσ0 hσ1
    _ = ((B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ)))
          * ∑ d ∈ Finset.Icc 1 A, (d : ℝ) ^ (-σ) * ((d.divisors.card : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro d hd; ring
    _ ≤ ((B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ)))
          * ((A : ℝ) ^ (1 - σ) * (1 + Real.log (A : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_tau_mul_rpow_neg_le hA hσ1) hXnn
    _ = (A : ℝ) ^ (1 - σ) * (B : ℝ) ^ (1 - σ) * (1 + Real.log (A : ℝ)) ^ 2
          * (1 + Real.log (B : ℝ)) := by ring

theorem norm_lcmF_le (q : ℕ) [NeZero q] {U V W : ℝ} (hU : 0 < U) (hUV : U ≤ V) (hV : 1 ≤ V)
    (hW : 1 ≤ W) (χ : DirichletCharacter ℂ q) {k : ℕ} (hk : 1 ≤ k) {s : ℂ}
    (hs : s.re = 1 - (k : ℝ)⁻¹) :
    ‖lcmF q U V W χ s‖ ≤ (V * W) ^ (1 / (k : ℝ)) * (1 + Real.log (V * W)) ^ 3 := by
  set A : ℕ := Nat.floor V with hAdef
  set B : ℕ := Nat.floor W with hBdef
  set σ : ℝ := 1 - (k : ℝ)⁻¹ with hσdef
  have hA1 : 1 ≤ A := by rw [hAdef]; exact Nat.le_floor (by exact_mod_cast hV)
  have hB1 : 1 ≤ B := by rw [hBdef]; exact Nat.le_floor (by exact_mod_cast hW)
  have hAV : (A:ℝ) ≤ V := by rw [hAdef]; exact Nat.floor_le (by linarith only [hU, hUV])
  have hBW : (B:ℝ) ≤ W := by rw [hBdef]; exact Nat.floor_le (by linarith only [hW])
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkinv1 : (k:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hk)
  have hkinv0 : 0 ≤ (k:ℝ)⁻¹ := inv_nonneg.mpr hkpos.le
  have hσ0 : 0 ≤ σ := by rw [hσdef]; linarith only [hkinv1]
  have hσ1 : σ ≤ 1 := by rw [hσdef]; linarith only [hkinv0]
  have hsre : s.re = σ := by rw [hs, hσdef]
  have hV0 : (0:ℝ) < V := lt_of_lt_of_le one_pos hV
  have hW0 : (0:ℝ) < W := lt_of_lt_of_le one_pos hW
  have hnorm : ‖lcmF q U V W χ s‖
      ≤ ∑ d ∈ Finset.Icc 1 A, ∑ e ∈ Finset.Icc 1 B, ((Nat.lcm d e : ℕ) : ℝ) ^ (-σ) := by
    rw [lcmF_eq_sum_lcmTerm q hUV χ s, ← hAdef, ← hBdef]
    calc ‖∑ d ∈ Finset.Icc 1 A, ∑ e ∈ Finset.Icc 1 B, lcmTerm q U V W χ s d e‖
        ≤ ∑ d ∈ Finset.Icc 1 A, ‖∑ e ∈ Finset.Icc 1 B, lcmTerm q U V W χ s d e‖ :=
          norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 A, ∑ e ∈ Finset.Icc 1 B, ‖lcmTerm q U V W χ s d e‖ :=
          Finset.sum_le_sum (fun d _ => norm_sum_le _ _)
      _ ≤ ∑ d ∈ Finset.Icc 1 A, ∑ e ∈ Finset.Icc 1 B, ((Nat.lcm d e : ℕ) : ℝ) ^ (-σ) := by
          apply Finset.sum_le_sum; intro d hd
          apply Finset.sum_le_sum; intro e he
          calc ‖lcmTerm q U V W χ s d e‖ ≤ ((Nat.lcm d e : ℕ) : ℝ) ^ (-s.re) :=
                norm_lcmTerm_le q hU χ (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
            _ = ((Nat.lcm d e : ℕ) : ℝ) ^ (-σ) := by rw [hsre]
  have hsum := sum_lcm_rpow_neg_le hA1 hB1 hσ0 hσ1
  refine hnorm.trans (hsum.trans ?_)
  have hAle : (A:ℝ) ^ (1 - σ) ≤ V ^ (1 - σ) :=
    Real.rpow_le_rpow (by positivity) hAV (by linarith only [hkinv0])
  have hBle : (B:ℝ) ^ (1 - σ) ≤ W ^ (1 - σ) :=
    Real.rpow_le_rpow (by positivity) hBW (by linarith only [hkinv0])
  have hlogA : 1 + Real.log (A:ℝ) ≤ 1 + Real.log (V * W) := by
    have h1 : Real.log (A:ℝ) ≤ Real.log (V * W) :=
      Real.log_le_log (by positivity) (by nlinarith only [hAV, hW0.le, hV0.le, hU, hW, hUV])
    linarith only [h1]
  have hlogB : 1 + Real.log (B:ℝ) ≤ 1 + Real.log (V * W) := by
    have h1 : Real.log (B:ℝ) ≤ Real.log (V * W) :=
      Real.log_le_log (by positivity) (by nlinarith only [hBW, hV0.le, hW0.le, hV, hU, hUV])
    linarith only [h1]
  have hlogA0 : 0 ≤ 1 + Real.log (A:ℝ) := by
    have : (1:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA1
    linarith only [Real.log_nonneg this, this]
  have hlogB0 : 0 ≤ 1 + Real.log (B:ℝ) := by
    have : (1:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB1
    linarith only [Real.log_nonneg this, this]
  have hlogle : (1 + Real.log (A:ℝ)) ^ 2 * (1 + Real.log (B:ℝ))
      ≤ (1 + Real.log (V * W)) ^ 3 := by
    have h2 : (1 + Real.log (A:ℝ)) ^ 2 ≤ (1 + Real.log (V * W)) ^ 2 :=
      pow_le_pow_left₀ hlogA0 hlogA 2
    have h3 : (1 + Real.log (V * W)) ^ 2 * (1 + Real.log (B:ℝ))
        ≤ (1 + Real.log (V * W)) ^ 2 * (1 + Real.log (V * W)) :=
      mul_le_mul_of_nonneg_left hlogB (by positivity)
    calc (1 + Real.log (A:ℝ)) ^ 2 * (1 + Real.log (B:ℝ))
        ≤ (1 + Real.log (V * W)) ^ 2 * (1 + Real.log (B:ℝ)) :=
          mul_le_mul_of_nonneg_right h2 hlogB0
      _ ≤ (1 + Real.log (V * W)) ^ 2 * (1 + Real.log (V * W)) := h3
      _ = (1 + Real.log (V * W)) ^ 3 := by ring
  have hprod : (A:ℝ) ^ (1 - σ) * (B:ℝ) ^ (1 - σ) ≤ (V * W) ^ (1 - σ) := by
    have h4 : (A:ℝ) ^ (1 - σ) * (B:ℝ) ^ (1 - σ) ≤ V ^ (1 - σ) * W ^ (1 - σ) :=
      mul_le_mul hAle hBle (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hV0.le _)
    simpa [← Real.mul_rpow hV0.le hW0.le] using h4
  have hexp : 1 - σ = 1 / (k : ℝ) := by
    rw [hσdef]; simp [one_div]
  calc (A : ℝ) ^ (1 - σ) * (B : ℝ) ^ (1 - σ) * (1 + Real.log (A : ℝ)) ^ 2
        * (1 + Real.log (B : ℝ))
      = ((A:ℝ) ^ (1 - σ) * (B:ℝ) ^ (1 - σ))
          * ((1 + Real.log (A:ℝ)) ^ 2 * (1 + Real.log (B:ℝ))) := by ring
    _ ≤ (V * W) ^ (1 - σ) * (1 + Real.log (V * W)) ^ 3 :=
        mul_le_mul hprod hlogle (by positivity) (Real.rpow_nonneg (by positivity) _)
    _ = (V * W) ^ (1 / (k : ℝ)) * (1 + Real.log (V * W)) ^ 3 := by rw [hexp]

end Work.LinnikAreas.Density4
