import Mathlib
set_option linter.unusedVariables false

namespace Work.ChenPlan.LinearSieve.Selberg

open Finset

/-- The total logarithmic mass of a finite set of primes with weights `ν` is the logarithm of the
corresponding product of `(1 - ν p)⁻¹`. -/
private lemma sum_neg_log_eq_log_prod_inv {F : Finset ℕ} {ν : ℕ → ℝ}
    (hν1 : ∀ p ∈ F, ν p < 1) :
    (∑ p ∈ F, -Real.log (1 - ν p)) = Real.log (∏ p ∈ F, (1 - ν p)⁻¹) := by
  have key : (∑ p ∈ F, -Real.log (1 - ν p)) = ∑ p ∈ F, Real.log ((1 - ν p)⁻¹) :=
    Finset.sum_congr rfl (fun p _ => by rw [Real.log_inv])
  rw [key, Real.log_prod (f := fun p => (1 - ν p)⁻¹) (fun p hp => by
    have h1 : (1 : ℝ) - ν p ≠ 0 := by have := hν1 p hp; linarith
    exact inv_ne_zero h1)]

/-- Antitonicity of `w ↦ log (log Z / log w) + log (1 + K / log w)` on `(1, 2]`. -/
private lemma phi_anti {Z : ℕ} (hZ : 2 ≤ Z) {K : ℝ} (hK : 0 ≤ K) {v : ℝ}
    (hv1 : 1 < v) (hv2 : v ≤ 2) :
    Real.log (Real.log (Z : ℝ) / Real.log 2) + Real.log (1 + K / Real.log 2)
      ≤ Real.log (Real.log (Z : ℝ) / Real.log v) + Real.log (1 + K / Real.log v) := by
  have hlogZ : 0 < Real.log (Z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogv : 0 < Real.log v := Real.log_pos hv1
  have hlv : Real.log v ≤ Real.log 2 := Real.log_le_log (by linarith) hv2
  have h1 : Real.log (Real.log (Z : ℝ) / Real.log 2)
      ≤ Real.log (Real.log (Z : ℝ) / Real.log v) := by
    apply Real.log_le_log (div_pos hlogZ hlog2)
    exact div_le_div_of_nonneg_left (le_of_lt hlogZ) hlogv hlv
  have h2 : Real.log (1 + K / Real.log 2) ≤ Real.log (1 + K / Real.log v) := by
    apply Real.log_le_log (add_pos_of_pos_of_nonneg one_pos (div_nonneg hK (le_of_lt hlog2)))
    have hdiv : K / Real.log 2 ≤ K / Real.log v := div_le_div_of_nonneg_left hK hlogv hlv
    linarith
  linarith

/-- Conversion of a product bound on the tail above `w` into a bound on the logarithmic mass of
that tail. -/
private lemma tail_bound_of_prod {S : Finset ℕ} (ν : ℕ → ℝ)
    (hν1 : ∀ p ∈ S, ν p < 1) {Z : ℕ} (hlogZ : 0 < Real.log (Z : ℝ)) {K : ℝ} (hK : 0 ≤ K)
    {w : ℝ} (hw : 2 ≤ w)
    (hcon : (∏ p ∈ S.filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - ν p)⁻¹)
        ≤ (Real.log (Z : ℝ) / Real.log w) * (1 + K / Real.log w)) :
    (∑ p ∈ S.filter (fun p : ℕ => w ≤ (p : ℝ)), -Real.log (1 - ν p))
        ≤ Real.log (Real.log (Z : ℝ) / Real.log w) + Real.log (1 + K / Real.log w) := by
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have ha : Real.log (Z : ℝ) / Real.log w ≠ 0 := div_ne_zero hlogZ.ne' hlogw.ne'
  have hb : 1 + K / Real.log w ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg one_pos (div_nonneg hK (le_of_lt hlogw)))
  have hPpos : 0 < ∏ p ∈ S.filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - ν p)⁻¹ := by
    apply Finset.prod_pos
    intro p hp
    rw [inv_pos]
    have := hν1 p (Finset.mem_of_mem_filter p hp)
    linarith
  calc (∑ p ∈ S.filter (fun p : ℕ => w ≤ (p : ℝ)), -Real.log (1 - ν p))
      = Real.log (∏ p ∈ S.filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - ν p)⁻¹) :=
        sum_neg_log_eq_log_prod_inv (fun p hp => hν1 p (Finset.mem_of_mem_filter p hp))
    _ ≤ Real.log ((Real.log (Z : ℝ) / Real.log w) * (1 + K / Real.log w)) :=
        Real.log_le_log hPpos hcon
    _ = Real.log (Real.log (Z : ℝ) / Real.log w) + Real.log (1 + K / Real.log w) :=
        Real.log_mul ha hb

theorem tail_mass_constraint_of_product_bound {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (ν : ℕ → ℝ)
    (hν0 : ∀ p ∈ S, 0 ≤ ν p) (hν1 : ∀ p ∈ S, ν p < 1) {Z : ℕ} (hZ : 2 ≤ Z)
    (hSZ : ∀ p ∈ S, p < Z) {K : ℝ} (hK : 0 ≤ K)
    (hcon : ∀ w : ℝ, 2 ≤ w → w < (Z : ℝ) →
      (∏ p ∈ S.filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - ν p)⁻¹)
        ≤ (Real.log (Z : ℝ) / Real.log w) * (1 + K / Real.log w)) :
    ∀ u : ℝ, 0 < u → u ≤ 1 →
      (∑ p ∈ S.filter (fun p : ℕ => u ≤ Real.log (p : ℝ) / Real.log (Z : ℝ)), -Real.log (1 - ν p))
        ≤ Real.log (1 / u) + Real.log (1 + K / (u * Real.log (Z : ℝ))) := by
  intro u hu0 hu1
  have hZ1 : (1 : ℝ) < (Z : ℝ) := by exact_mod_cast (by omega : 1 < Z)
  have hZpos : (0 : ℝ) < (Z : ℝ) := by linarith
  have hlogZ : 0 < Real.log (Z : ℝ) := Real.log_pos hZ1
  have hRHS : 0 ≤ Real.log (1 / u) + Real.log (1 + K / (u * Real.log (Z : ℝ))) := by
    apply add_nonneg
    · apply Real.log_nonneg
      rw [one_le_div hu0]; exact hu1
    · apply Real.log_nonneg
      have h : 0 ≤ K / (u * Real.log (Z : ℝ)) :=
        div_nonneg hK (mul_nonneg (le_of_lt hu0) (le_of_lt hlogZ))
      linarith
  have hiff : ∀ p ∈ S, (u ≤ Real.log (p : ℝ) / Real.log (Z : ℝ)) ↔ ((Z : ℝ) ^ u ≤ (p : ℝ)) := by
    intro p hp
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hS p hp).pos
    rw [le_div_iff₀ hlogZ, ← Real.log_rpow hZpos u]
    exact Real.log_le_log_iff (Real.rpow_pos_of_pos hZpos u) hppos
  have hfilter : S.filter (fun p : ℕ => u ≤ Real.log (p : ℝ) / Real.log (Z : ℝ))
      = S.filter (fun p : ℕ => (Z : ℝ) ^ u ≤ (p : ℝ)) :=
    Finset.filter_congr (fun p hp => hiff p hp)
  have hphiZ : Real.log (Real.log (Z : ℝ) / Real.log ((Z : ℝ) ^ u))
        + Real.log (1 + K / Real.log ((Z : ℝ) ^ u))
      = Real.log (1 / u) + Real.log (1 + K / (u * Real.log (Z : ℝ))) := by
    rw [Real.log_rpow hZpos u]
    congr 1
    · congr 1
      field_simp
  rw [hfilter]
  by_cases hcase : (2 : ℝ) ≤ (Z : ℝ) ^ u
  · by_cases hu_eq : u = 1
    · have hpow : (Z : ℝ) ^ u = (Z : ℝ) := by rw [hu_eq, Real.rpow_one]
      rw [hpow]
      have hempty : S.filter (fun p : ℕ => (Z : ℝ) ≤ (p : ℝ)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro p hp hle
        have hlt : (p : ℝ) < (Z : ℝ) := by exact_mod_cast hSZ p hp
        linarith
      rw [hempty, Finset.sum_empty]
      exact hRHS
    · have hu_lt : u < 1 := lt_of_le_of_ne hu1 hu_eq
      have hpow_lt : (Z : ℝ) ^ u < (Z : ℝ) := by
        have h := Real.rpow_lt_rpow_of_exponent_lt hZ1 hu_lt
        rwa [Real.rpow_one] at h
      have htb := tail_bound_of_prod ν hν1 hlogZ hK hcase (hcon ((Z : ℝ) ^ u) hcase hpow_lt)
      exact le_trans htb (le_of_eq hphiZ)
  · push Not at hcase
    by_cases hSne : S = ∅
    · rw [hSne, Finset.filter_empty, Finset.sum_empty]
      exact hRHS
    · obtain ⟨p0, hp0S⟩ := Finset.nonempty_iff_ne_empty.mpr hSne
      have h2ltZ : 2 < Z := by
        have h1 := (hS p0 hp0S).two_le
        have h2 := hSZ p0 hp0S
        omega
      have h2ltZr : (2 : ℝ) < (Z : ℝ) := by exact_mod_cast h2ltZ
      have hfilter2 : S.filter (fun p : ℕ => (Z : ℝ) ^ u ≤ (p : ℝ))
          = S.filter (fun p : ℕ => (2 : ℝ) ≤ (p : ℝ)) := by
        apply Finset.filter_congr
        intro p hp
        constructor
        · intro _; exact_mod_cast (hS p hp).two_le
        · intro h2; exact le_trans (le_of_lt hcase) h2
      rw [hfilter2]
      have htb := tail_bound_of_prod ν hν1 hlogZ hK (le_refl (2 : ℝ)) (hcon 2 (le_refl 2) h2ltZr)
      have hv1 : (1 : ℝ) < (Z : ℝ) ^ u := Real.one_lt_rpow hZ1 hu0
      have hphi2 := phi_anti hZ hK hv1 (le_of_lt hcase)
      exact le_trans (le_trans htb hphi2) (le_of_eq hphiZ)

end Work.ChenPlan.LinearSieve.Selberg
