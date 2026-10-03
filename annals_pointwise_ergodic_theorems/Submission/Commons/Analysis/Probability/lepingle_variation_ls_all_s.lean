import Mathlib
import Submission.Commons.Analysis.Probability.lepingle_variation_ls

/-! Lépingle's inequality for the `s`-variation, for ALL `s > 2` (the commons version
`Commons.Analysis.Probability.lepingle_variation_ls` requires `s ≤ 3`, which is only a
limitation of the constant bookkeeping: the analytic core `bdg_sm_sq` is valid for all `s > 2`).

The change is confined to the two constant lemmas `geom_bound`/`bdgZZ_bound`: the geometric sum
`∑_{m=2}^{M} (1/2)^{(m-2)(s-2)}` is bounded by `lepG s = (1 + (s-2) log 2)/((s-2) log 2)`, valid for
every `s > 2`. -/

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace Commons.Analysis.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

/-- For `x > 0`: `x log 2/(1 + x log 2) ≤ 1 - 2^{-x}`. -/
lemma one_sub_half_rpow_ge_gen {x : ℝ} (hx : 0 < x) :
    x * Real.log 2 / (1 + x * Real.log 2) ≤ 1 - (1/2:ℝ)^x := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h2x : 1 + x * Real.log 2 ≤ (2:ℝ)^x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    have := Real.add_one_le_exp (Real.log 2 * x)
    linarith
  have hpos : 0 < (2:ℝ)^x := Real.rpow_pos_of_pos (by norm_num) x
  have hhalf : (1/2:ℝ)^x = ((2:ℝ)^x)⁻¹ := by
    rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2)]
  rw [hhalf]
  rw [show (1:ℝ) - ((2:ℝ)^x)⁻¹ = ((2:ℝ)^x - 1) / (2:ℝ)^x by field_simp]
  rw [div_le_div_iff₀ (by positivity) hpos]
  nlinarith [h2x, hlog, hx]

/-- The constant replacing `2/((s-2) log 2)` for general `s > 2`. -/
noncomputable def lepG (s : ℝ) : ℝ := (1 + (s-2) * Real.log 2) / ((s-2) * Real.log 2)

lemma lepG_pos {s : ℝ} (hs : 2 < s) : 0 < lepG s := by
  have h1 : 0 < (s-2) * Real.log 2 := by
    have := Real.log_pos one_lt_two; nlinarith
  exact div_pos (by linarith) h1

/-- The geometric-sum bound, valid for all `s > 2`. -/
lemma geom_bound_gen {s : ℝ} (hs2 : 2 < s) (M : ℕ) :
    ∑ m ∈ Finset.Icc 2 M, (1/2:ℝ)^((m-2)*(s-2)) ≤ lepG s := by
  have hs0 : 0 < s - 2 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hspos : 0 < (s-2) * Real.log 2 := mul_pos hs0 hlog2
  set c : ℝ := (1/2:ℝ)^(s-2) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hpos1 : 0 < 1 + (s-2) * Real.log 2 := by linarith
  have hbase : (s-2) * Real.log 2 / (1 + (s-2) * Real.log 2) ≤ 1 - c := by
    rw [hc]; exact one_sub_half_rpow_ge_gen hs0
  have hlt : c < 1 := by
    have h2 : 0 < (s-2) * Real.log 2 / (1 + (s-2) * Real.log 2) := div_pos hspos hpos1
    linarith
  have hpow : ∀ m ∈ Finset.Icc 2 M, (1/2:ℝ)^((m-2)*(s-2)) = c^(m-2) := by
    intro m hm
    have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2)]
    congr 1
    rw [Nat.cast_sub hm2]; ring
  have hkey : (s-2) * Real.log 2 ≤ (1 + (s-2) * Real.log 2) * (1 - c) := by
    have h := mul_le_mul_of_nonneg_right hbase hpos1.le
    rw [div_mul_cancel₀ _ (ne_of_gt hpos1)] at h
    linarith [h]
  calc ∑ m ∈ Finset.Icc 2 M, (1/2:ℝ)^((m-2)*(s-2))
      = ∑ m ∈ Finset.Icc 2 M, c^(m-2) := Finset.sum_congr rfl hpow
    _ = ∑ k ∈ (Finset.Icc 2 M).image (fun m => m-2), c^k :=
        (Finset.sum_image (f := fun k : ℕ => c^k) (g := fun m : ℕ => m - 2)
          (fun a ha b hb hab => by
            obtain ⟨ha1, -⟩ := Finset.mem_Icc.mp (by simpa using ha)
            obtain ⟨hb1, -⟩ := Finset.mem_Icc.mp (by simpa using hb)
            beta_reduce at hab
            omega)).symm
    _ ≤ ∑ k ∈ Finset.range (M+1), c^k := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => pow_nonneg hc0 i)
        intro k hk
        rw [Finset.mem_image] at hk
        obtain ⟨m, hm, rfl⟩ := hk
        rw [Finset.mem_Icc] at hm
        exact Finset.mem_range.mpr (by omega)
    _ ≤ 1/(1-c) := Commons.Analysis.Asymptotics.geom_finset_le hc0 hlt _
    _ ≤ lepG s := by
        rw [lepG, div_le_div_iff₀ (by linarith : (0:ℝ) < 1 - c) hspos]
        linarith [hkey]


section LepingleGeneral

open Commons.Analysis.Probability

lemma bdgZZ_pos {s : ℝ} (hs : 2 < s) : 0 < bdgZZ s := by
  have h1 : 0 < s/2 - 1 := by linarith
  have h2 : (0:ℝ) < 2^(s/2-1) := Real.rpow_pos_of_pos (by norm_num) _
  have h3 : 0 < s/2 := by linarith
  have hA : 0 < bdgA s := by
    rw [bdgA]; exact mul_pos h3 (mul_pos (by norm_num) (div_pos h2 h1))
  have hB : (0:ℝ) < bdgB s := by
    rw [bdgB]; exact div_pos (by linarith) (by linarith)
  rw [bdgZZ]; exact mul_pos hA (pow_pos hB 2)

end LepingleGeneral

end Commons.Analysis.Probability
