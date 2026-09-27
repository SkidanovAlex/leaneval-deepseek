import Mathlib
import Submission.Work.EKLC6Core.box_facts
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.contraction_rate_uminus

namespace Work.EKLC6Core

open Filter Topology
open Work.EKLContract

/-- The identity of `SL₃(ℝ)`, viewed as a matrix. -/
private theorem coe_one_SL3 :
    ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by simp

/-- The scalar multiple `k • t` scaled entrywise. -/
private theorem smul_t_sub (t : Fin 3 → ℝ) (k : ℕ) (i j : Fin 3) :
    ((k : ℝ) • t) i - ((k : ℝ) • t) j = (k : ℝ) * (t i - t j) := by
  simp only [Pi.smul_apply]; ring

/-- **Contraction shrinks the box into `V r`.**  If the exponent vector `t` contracts all of `U`
and the gaps satisfy `-log r < k (t j - t i)` for every pair with `t i < t j`, then
`conjBox U (k • t) ⊆ V r ∩ U`. -/
theorem conjBox_subset_V_inter_U {U : Subgroup SL3} (hU : IsHoro U) {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (nhds 1))
    {r : ℝ} (hr : 0 < r) {k : ℕ}
    (hgap : ∀ i j : Fin 3, i ≠ j → t i < t j → -Real.log r < (k : ℝ) * (t j - t i)) :
    conjBox U ((k : ℝ) • t) ⊆ V r ∩ (U : Set SL3) := by
  rintro g ⟨h, hh, rfl⟩
  refine ⟨fun i j => ?_, hU.2.1 ((k : ℝ) • t) h hh.1⟩
  rw [boxi_conj_apply, smul_t_sub]
  rcases eq_or_ne i j with rfl | hij
  · have h1 : (h : Matrix (Fin 3) (Fin 3) ℝ) i i = 1 := by
      simpa [coe_one_SL3, Matrix.one_apply_eq] using
        box_facts_entry_eq_one hcontr hh.1 (le_refl (t i))
    rw [sub_self, mul_zero, Real.exp_zero, one_mul, h1, Matrix.one_apply_eq, sub_self, abs_zero]
    exact hr
  · rw [Matrix.one_apply_ne hij, sub_zero]
    by_cases hlt : t i < t j
    · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have hhij : |(h : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
        have hb := hh.2 i j
        rwa [Matrix.one_apply_ne hij, sub_zero] at hb
      calc Real.exp ((k : ℝ) * (t i - t j)) * |(h : Matrix (Fin 3) (Fin 3) ℝ) i j|
          ≤ Real.exp ((k : ℝ) * (t i - t j)) * 1 := by gcongr
        _ = Real.exp ((k : ℝ) * (t i - t j)) := mul_one _
        _ < Real.exp (Real.log r) := by
              rw [Real.exp_lt_exp]
              have hkey : (k : ℝ) * (t i - t j) = -((k : ℝ) * (t j - t i)) := by ring
              rw [hkey]
              have hg := hgap i j hij hlt
              linarith
        _ = r := Real.exp_log hr
    · have hle : t j ≤ t i := not_lt.mp hlt
      have h0 : (h : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := by
        simpa [coe_one_SL3, Matrix.one_apply_ne hij] using
          box_facts_entry_eq_one hcontr hh.1 hle
      rw [h0, mul_zero, abs_zero]
      exact hr

/-- **Expansion enlarges the box.**  If the exponent vector `t` contracts all of `U` and the gaps
satisfy `log r ≤ k (t j - t i)` for every pair with `t i < t j`, then
`V r ∩ U ⊆ conjBox U (-(k • t))`. -/
theorem V_inter_U_subset_conjBox_neg {U : Subgroup SL3} (hU : IsHoro U) {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (nhds 1))
    {r : ℝ} (hr : 0 < r) {k : ℕ}
    (hgap : ∀ i j : Fin 3, i ≠ j → t i < t j → Real.log r ≤ (k : ℝ) * (t j - t i)) :
    V r ∩ (U : Set SL3) ⊆ conjBox U (-((k : ℝ) • t)) := by
  intro h hh
  obtain ⟨hhV, hhU⟩ := hh
  rw [conjBox, conjBy, Set.mem_image]
  refine ⟨aDiag ((k : ℝ) • t) * h * (aDiag ((k : ℝ) • t))⁻¹, ?_, ?_⟩
  · -- the conjugate lies in the normalising box `B₁^U`
    refine ⟨hU.2.1 ((k : ℝ) • t) h hhU, fun i j => ?_⟩
    rw [boxi_conj_apply, smul_t_sub]
    rcases eq_or_ne i j with rfl | hij
    · have h1 : (h : Matrix (Fin 3) (Fin 3) ℝ) i i = 1 := by
        simpa [coe_one_SL3, Matrix.one_apply_eq] using
          box_facts_entry_eq_one hcontr hhU (le_refl (t i))
      rw [sub_self, mul_zero, Real.exp_zero, one_mul, h1, Matrix.one_apply_eq, sub_self, abs_zero]
      norm_num
    · rw [Matrix.one_apply_ne hij, sub_zero]
      by_cases hlt : t i < t j
      · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        have hhij : |(h : Matrix (Fin 3) (Fin 3) ℝ) i j| < r := by
          have hb := hhV i j
          rwa [Matrix.one_apply_ne hij, sub_zero] at hb
        have hbound : Real.exp ((k : ℝ) * (t i - t j)) * r ≤ 1 := by
          have hkey : (k : ℝ) * (t i - t j) ≤ -Real.log r := by
            have hg := hgap i j hij hlt
            have hsub : (k : ℝ) * (t i - t j) = -((k : ℝ) * (t j - t i)) := by ring
            rw [hsub]; linarith
          calc Real.exp ((k : ℝ) * (t i - t j)) * r
              ≤ Real.exp (-Real.log r) * r :=
                mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hkey) hr.le
            _ = 1 := by rw [Real.exp_neg, Real.exp_log hr, inv_mul_cancel₀ hr.ne']
        calc Real.exp ((k : ℝ) * (t i - t j)) * |(h : Matrix (Fin 3) (Fin 3) ℝ) i j|
            ≤ Real.exp ((k : ℝ) * (t i - t j)) * r :=
              (mul_lt_mul_of_pos_left hhij (Real.exp_pos _)).le
          _ ≤ 1 := hbound
      · have hle : t j ≤ t i := not_lt.mp hlt
        have h0 : (h : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := by
          simpa [coe_one_SL3, Matrix.one_apply_ne hij] using
            box_facts_entry_eq_one hcontr hhU hle
        rw [h0, mul_zero, abs_zero]
        norm_num
  · -- conjugating back recovers `h`
    have h1 : (aDiag ((k : ℝ) • t))⁻¹ = aDiag (-((k : ℝ) • t)) := aDiag_inv_eq_neg _
    rw [h1]
    calc aDiag (-((k : ℝ) • t)) * (aDiag ((k : ℝ) • t) * h * aDiag (-((k : ℝ) • t)))
          * (aDiag (-((k : ℝ) • t)))⁻¹
        = (aDiag (-((k : ℝ) • t)) * aDiag ((k : ℝ) • t)) * h
            * (aDiag (-((k : ℝ) • t)) * (aDiag (-((k : ℝ) • t)))⁻¹) := by group
      _ = h := by rw [aDiag_neg_mul]; group

theorem box_sandwich {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U)
    {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1))
    {r : ℝ} (hr : 0 < r) :
    ∃ k : ℕ, 0 < k ∧
      Work.EKLC6Core.conjBox U ((k : ℝ) • t) ⊆
        Work.EKLContract.V r ∩ (U : Set Work.EKLContract.SL3) ∧
      Work.EKLContract.V r ∩ (U : Set Work.EKLContract.SL3) ⊆
        Work.EKLC6Core.conjBox U (-((k : ℝ) • t)) := by
  let c : ℝ := (gapSet t).min' (gapSet_nonempty t)
  have hcpos : 0 < c := gapSet_pos t (Finset.min'_mem _ _)
  have hcle : ∀ i j : Fin 3, i ≠ j → t i < t j → c ≤ t j - t i :=
    fun i j hij hlt => gapSet_min_le t hij hlt
  let A : ℝ := max (-Real.log r) (Real.log r)
  obtain ⟨N, hN⟩ := exists_nat_gt (A / c)
  have hNc : A < (N : ℝ) * c := (div_lt_iff₀ hcpos).mp hN
  have hAk : A < ((N + 1 : ℕ) : ℝ) * c := by
    have h2 : ((N + 1 : ℕ) : ℝ) * c = (N : ℝ) * c + c := by push_cast; ring
    rw [h2]; linarith
  have hgap1 : ∀ i j : Fin 3, i ≠ j → t i < t j →
      -Real.log r < ((N + 1 : ℕ) : ℝ) * (t j - t i) := by
    intro i j hij hlt
    have h1 : ((N + 1 : ℕ) : ℝ) * c ≤ ((N + 1 : ℕ) : ℝ) * (t j - t i) :=
      mul_le_mul_of_nonneg_left (hcle i j hij hlt) (Nat.cast_nonneg _)
    have h2 : -Real.log r ≤ A := le_max_left _ _
    linarith
  have hgap2 : ∀ i j : Fin 3, i ≠ j → t i < t j →
      Real.log r ≤ ((N + 1 : ℕ) : ℝ) * (t j - t i) := by
    intro i j hij hlt
    have h1 : ((N + 1 : ℕ) : ℝ) * c ≤ ((N + 1 : ℕ) : ℝ) * (t j - t i) :=
      mul_le_mul_of_nonneg_left (hcle i j hij hlt) (Nat.cast_nonneg _)
    have h2 : Real.log r ≤ A := le_max_right _ _
    linarith
  exact ⟨N + 1, Nat.succ_pos N,
    conjBox_subset_V_inter_U hU hcontr hr hgap1,
    V_inter_U_subset_conjBox_neg hU hcontr hr hgap2⟩

end Work.EKLC6Core
