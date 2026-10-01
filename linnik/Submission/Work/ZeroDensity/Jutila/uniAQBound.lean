import Mathlib
import Submission.Work.ZeroDensity.Jutila.sieveSymbolDefs

/-!
# The weight `1/(d·rad d)` has bounded reciprocal sum

This file proves `Work.ZeroDensity.Jutila.uniAQBound`: there is an absolute constant `K > 0`
with `Σ_{d ≤ V} 1/(d·rad d) ≤ K` for every `V : ℕ`, where `rad d = ∏_{p ∣ d} p`
(`Submission.Work.ZeroDensity.Jutila.sieveSymbolDefs`).

The route implemented here is the squarefree decomposition `d = b²·a` (`Nat.sq_mul_squarefree`):

* `a = sqfreePart d` is squarefree, `b = sqRoot d` is a square root, and `b²·a = d`;
* hence `a ∣ rad d` (a squarefree divisor of `d` only uses each prime once), so `a ≤ rad d`;
* consequently `(a·b)² ≤ d·rad d`, i.e. `1/(d·rad d) ≤ 1/(a²b²)`;
* `d ↦ (a,b)` is injective on `{1,…,V}` (as `d = a·b²` and `a,b ≤ d ≤ V`), so
  `Σ_{d ≤ V} 1/(d·rad d) ≤ (Σ_{a ≤ V} 1/a²)·(Σ_{b ≤ V} 1/b²)`;
* `Σ_{a ∈ Icc 1 V} 1/a² ≤ Σ_{n ≥ 1} 1/n² = π²/6 < 2`, giving the absolute constant `K = 4`.
-/

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-! ### The squarefree decomposition `d = b²·a` -/

/-- The squarefree part `a` of the decomposition `d = b²·a` of a natural number
(`Nat.sq_mul_squarefree`).  For `d = 0` it is the value supplied by that existence statement,
which is never used. -/
def sqfreePart (d : ℕ) : ℕ := (Nat.sq_mul_squarefree d).choose

/-- The `b` of the decomposition `d = b²·a`; for `d ≠ 0` it is positive. -/
def sqRoot (d : ℕ) : ℕ := (Nat.sq_mul_squarefree d).choose_spec.choose

lemma sqRoot_sq_mul_sqfreePart (d : ℕ) : sqRoot d ^ 2 * sqfreePart d = d :=
  ((Nat.sq_mul_squarefree d).choose_spec.choose_spec).1

lemma sqfreePart_squarefree (d : ℕ) : Squarefree (sqfreePart d) :=
  ((Nat.sq_mul_squarefree d).choose_spec.choose_spec).2

lemma one_le_sqfreePart {d : ℕ} (hd : d ≠ 0) : 1 ≤ sqfreePart d := by
  have h := sqRoot_sq_mul_sqfreePart d
  have hne : sqfreePart d ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    exact hd h.symm
  omega

lemma one_le_sqRoot {d : ℕ} (hd : d ≠ 0) : 1 ≤ sqRoot d := by
  have h := sqRoot_sq_mul_sqfreePart d
  have hne : sqRoot d ≠ 0 := by
    intro h0
    rw [h0] at h
    simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_mul] at h
    exact hd h.symm
  omega

/-! ### A squarefree divisor of `d` divides `rad d` -/

/-- The prime factors of a divisor of a nonzero number are prime factors of that number. -/
lemma primeFactors_subset_of_dvd {a d : ℕ} (hd : d ≠ 0) (had : a ∣ d) :
    a.primeFactors ⊆ d.primeFactors := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp ⊢
  exact ⟨hp.1, hp.2.1.trans had, hd⟩

/-- **A squarefree divisor of a nonzero number divides its radical.**  Indeed, if `a` is
squarefree and `a ∣ d`, then `a = ∏_{p ∣ a} p` and every `p ∣ a` divides `d`, so
`a ∣ ∏_{p ∣ d} p = rad d`.  The hypothesis `d ≠ 0` is needed: `2 ∣ 0` but `2 ∤ rad 0 = 1`. -/
theorem squarefreeDvdRad {a d : ℕ} (ha : Squarefree a) (hd : d ≠ 0) (had : a ∣ d) :
    a ∣ rad d := by
  rw [rad, ← Nat.prod_primeFactors_of_squarefree ha]
  refine ⟨∏ p ∈ d.primeFactors \ a.primeFactors, p, ?_⟩
  calc (∏ p ∈ d.primeFactors, p)
      = (∏ p ∈ d.primeFactors \ a.primeFactors, p) * (∏ p ∈ a.primeFactors, p) :=
        (Finset.prod_sdiff (primeFactors_subset_of_dvd hd had)).symm
    _ = (∏ p ∈ a.primeFactors, p) * (∏ p ∈ d.primeFactors \ a.primeFactors, p) := by
        rw [mul_comm]

lemma sqfreePart_dvd_rad (d : ℕ) (hd : d ≠ 0) : sqfreePart d ∣ rad d :=
  squarefreeDvdRad (sqfreePart_squarefree d) hd
    ⟨sqRoot d ^ 2, by rw [mul_comm, sqRoot_sq_mul_sqfreePart]⟩

/-! ### The termwise comparison `1/(d·rad d) ≤ 1/(a²b²)` -/

/-- If `d = b²·a` with `a, b ≥ 1` and `a ∣ rad d`, then `a ≤ rad d`, so
`(a·b)² = a²b² ≤ d·rad d` and therefore `1/(d·rad d) ≤ 1/(a²b²)`. -/
theorem invMulRad_le_inv_sq_mul_sq {a b d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hd : b ^ 2 * a = d) (had : a ∣ rad d) :
    1 / ((d : ℝ) * (rad d : ℝ)) ≤ 1 / ((a : ℝ) ^ 2 * (b : ℝ) ^ 2) := by
  have hrad1 : 1 ≤ rad d := by
    rw [rad]
    exact Finset.one_le_prod₀ (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_lt.le)
  have hle : a ≤ rad d := Nat.le_of_dvd (by omega) had
  have hale : (a : ℝ) ≤ (rad d : ℝ) := by exact_mod_cast hle
  have hcast : (d : ℝ) = (b : ℝ) ^ 2 * (a : ℝ) := by
    rw [← hd]; push_cast; ring
  have haR : (0 : ℝ) ≤ (a : ℝ) := by positivity
  have hbR : (0 : ℝ) ≤ (b : ℝ) ^ 2 := by positivity
  have hprod : ((a : ℝ) ^ 2 * (b : ℝ) ^ 2) ≤ (d : ℝ) * (rad d : ℝ) := by
    have h1 : (a : ℝ) * (a : ℝ) ≤ (a : ℝ) * (rad d : ℝ) :=
      mul_le_mul_of_nonneg_left hale haR
    calc (a : ℝ) ^ 2 * (b : ℝ) ^ 2 = ((a : ℝ) * (a : ℝ)) * ((b : ℝ) ^ 2) := by ring
      _ ≤ ((a : ℝ) * (rad d : ℝ)) * ((b : ℝ) ^ 2) := mul_le_mul_of_nonneg_right h1 hbR
      _ = (b : ℝ) ^ 2 * (a : ℝ) * (rad d : ℝ) := by ring
      _ = (d : ℝ) * (rad d : ℝ) := by rw [← hcast]
  have hden : (0 : ℝ) < (a : ℝ) ^ 2 * (b : ℝ) ^ 2 := by
    have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
    have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
    positivity
  exact one_div_le_one_div_of_le hden hprod

/-! ### The partial sums of `Σ 1/n²` -/

/-- `Σ_{a ∈ Icc 1 V} 1/a² ≤ 2`: the partial sums are bounded by `Σ_{n ≥ 1} 1/n² = π²/6 < 2`
(using `π < 3.15`, so `π²/6 < 9.93/6 < 2`). -/
theorem uniAQInvSqSum (V : ℕ) :
    (∑ a ∈ Finset.Icc 1 V, 1 / ((a : ℝ) ^ 2)) ≤ 2 := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := hasSum_zeta_two.summable
  have h1 : (∑ a ∈ Finset.Icc 1 V, 1 / (a : ℝ) ^ 2) ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 :=
    hs.sum_le_tsum (Finset.Icc 1 V) (fun n _ => by positivity)
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
  calc (∑ a ∈ Finset.Icc 1 V, 1 / (a : ℝ) ^ 2) ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := h1
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
    _ ≤ 2 := hpi

/-! ### The uniform bound -/

/-- **The weight `1/(d·rad d)` has bounded reciprocal sum.**  There is an absolute `K > 0` with
`Σ_{d ≤ V} 1/(d·rad d) ≤ K` for every `V : ℕ`, where `rad d = ∏_{p ∣ d} p`.

Proof route: `d = a·b²` with `a` squarefree gives `rad d = a·rad b` and `d·rad d ≥ a²b²`; hence
`Σ_{d ≤ V} 1/(d·rad d) ≤ (Σ_{a} 1/a²)·(Σ_b 1/b²) ≤ 2·2 = 4` using `Σ_{n ≥ 1} 1/n² ≤ 1 + ∫_1^∞ dx/x² = 2`.
Do not change the statement (any absolute constant is fine; the numerical value is `≤ 1.7`). -/
theorem uniAQBound : ∃ K : ℝ, 0 < K ∧ ∀ V : ℕ,
    (∑ d ∈ Finset.Icc 1 V, 1 / ((d : ℝ) * (rad d : ℝ))) ≤ K := by
  refine ⟨4, by norm_num, fun V => ?_⟩
  set φ : ℕ → ℕ × ℕ := fun d => (sqfreePart d, sqRoot d) with hφ
  set F : ℕ × ℕ → ℝ := fun p => 1 / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2) with hF
  -- termwise comparison `1/(d·rad d) ≤ 1/(a²b²)`
  have hterm : ∀ d ∈ Finset.Icc 1 V, 1 / ((d : ℝ) * (rad d : ℝ)) ≤ F (φ d) := by
    intro d hd
    have hd0 : d ≠ 0 := by
      have := (Finset.mem_Icc.mp hd).1
      omega
    have h := invMulRad_le_inv_sq_mul_sq (one_le_sqfreePart hd0) (one_le_sqRoot hd0)
      (sqRoot_sq_mul_sqfreePart d) (sqfreePart_dvd_rad d hd0)
    simpa only [hF, hφ] using h
  -- the decomposition map is injective on `{1,…,V}`
  have hinj : Set.InjOn φ ↑(Finset.Icc 1 V) := by
    intro d _ d' _ heq
    have hfa : sqfreePart d = sqfreePart d' := by
      have := congrArg Prod.fst heq
      simpa only [hφ] using this
    have hfb : sqRoot d = sqRoot d' := by
      have := congrArg Prod.snd heq
      simpa only [hφ] using this
    calc d = sqRoot d ^ 2 * sqfreePart d := (sqRoot_sq_mul_sqfreePart d).symm
      _ = sqRoot d' ^ 2 * sqfreePart d' := by rw [hfa, hfb]
      _ = d' := sqRoot_sq_mul_sqfreePart d'
  -- its image lies in `{1,…,V} × {1,…,V}`
  have hsub : (Finset.Icc 1 V).image φ ⊆ (Finset.Icc 1 V) ×ˢ (Finset.Icc 1 V) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    have hdV : d ≤ V := (Finset.mem_Icc.mp hd).2
    have hd0 : d ≠ 0 := by
      have := (Finset.mem_Icc.mp hd).1
      omega
    have ha1 := one_le_sqfreePart hd0
    have hb1 := one_le_sqRoot hd0
    have hspec := sqRoot_sq_mul_sqfreePart d
    have ha_le : sqfreePart d ≤ d := by
      have h : sqfreePart d ≤ sqRoot d ^ 2 * sqfreePart d :=
        Nat.le_mul_of_pos_left _ (pow_pos (by omega : 0 < sqRoot d) 2)
      rwa [hspec] at h
    have hb_le : sqRoot d ≤ d := by
      have h1 : sqRoot d ≤ sqRoot d * sqRoot d :=
        Nat.le_mul_of_pos_left _ (by omega : 0 < sqRoot d)
      have h2 : sqRoot d * sqRoot d ≤ sqRoot d * sqRoot d * sqfreePart d :=
        Nat.le_mul_of_pos_right _ (by omega : 0 < sqfreePart d)
      have h3 : sqRoot d * sqRoot d * sqfreePart d = sqRoot d ^ 2 * sqfreePart d := by ring
      rw [h3] at h2
      exact (h1.trans h2).trans_eq hspec
    rw [(by rfl : φ d = (sqfreePart d, sqRoot d)), Finset.mem_product]
    exact ⟨Finset.mem_Icc.mpr ⟨ha1, ha_le.trans hdV⟩,
      Finset.mem_Icc.mpr ⟨hb1, hb_le.trans hdV⟩⟩
  -- the double sum factorises
  have hprod : (∑ a ∈ Finset.Icc 1 V, ∑ b ∈ Finset.Icc 1 V, F (a, b))
      = (∑ a ∈ Finset.Icc 1 V, 1 / (a : ℝ) ^ 2) * (∑ b ∈ Finset.Icc 1 V, 1 / (b : ℝ) ^ 2) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hF, div_mul_div_comm, one_mul]
  calc (∑ d ∈ Finset.Icc 1 V, 1 / ((d : ℝ) * (rad d : ℝ)))
      ≤ ∑ d ∈ Finset.Icc 1 V, F (φ d) := Finset.sum_le_sum hterm
    _ = ∑ x ∈ (Finset.Icc 1 V).image φ, F x := (Finset.sum_image hinj).symm
    _ ≤ ∑ x ∈ (Finset.Icc 1 V) ×ˢ (Finset.Icc 1 V), F x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => by rw [hF]; positivity)
    _ = (∑ a ∈ Finset.Icc 1 V, 1 / (a : ℝ) ^ 2) * (∑ b ∈ Finset.Icc 1 V, 1 / (b : ℝ) ^ 2) := by
        rw [Finset.sum_product]
        exact hprod
    _ ≤ 4 := by
        have h1 := uniAQInvSqSum V
        have hnn : 0 ≤ ∑ a ∈ Finset.Icc 1 V, 1 / (a : ℝ) ^ 2 :=
          Finset.sum_nonneg (fun a _ => by positivity)
        nlinarith [h1, hnn]

end

end Work.ZeroDensity.Jutila
