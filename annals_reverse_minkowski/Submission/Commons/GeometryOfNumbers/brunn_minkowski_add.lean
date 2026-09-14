import Mathlib
import Submission.Commons.Analysis.Convex.prekopa_leindler_inequality

namespace Commons.GeometryOfNumbers

open MeasureTheory Set Metric Filter
open scoped ENNReal Pointwise

variable {n : ℕ}

/-- Scaling of the real Lebesgue measure by a nonnegative scalar. -/
lemma volume_real_smul (c : ℝ) (hc : 0 ≤ c)
    (s : Set (EuclideanSpace ℝ (Fin n))) :
    volume.real (c • s) = c ^ n * volume.real s := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    rw [finrank_euclideanSpace]; simp
  have h := Measure.addHaar_smul (volume : Measure (EuclideanSpace ℝ (Fin n))) c s
  rw [hfr] at h
  rw [measureReal_def, h, abs_of_nonneg (pow_nonneg hc n), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hc n), measureReal_def]

/-- `c • (A + B) = c • A + c • B` for sets. -/
lemma smul_add_eq_smul_add_smul (c : ℝ) (A B : Set (EuclideanSpace ℝ (Fin n))) :
    c • (A + B) = c • A + c • B := by
  ext x
  rw [Set.mem_smul_set, Set.mem_add]
  constructor
  · rintro ⟨y, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨c • a, ⟨a, ha, rfl⟩, c • b, ⟨b, hb, rfl⟩, (smul_add c a b).symm⟩
  · rintro ⟨u, ⟨a, ha, rfl⟩, v, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, smul_add c a b⟩

/-- Indicator functions of finite-measure sets are integrable. -/
lemma integrable_indicator_one' (s : Set (EuclideanSpace ℝ (Fin n)))
    (hs : MeasurableSet s) (hsf : volume s ≠ ∞) :
    Integrable (s.indicator (fun _ => (1:ℝ))) volume := by
  rw [integrable_indicator_iff hs]
  exact integrableOn_const hsf (by simp)

/-- Indicator functions are nonnegative. -/
lemma indicator_one_nonneg (s : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ s.indicator (fun _ => (1:ℝ)) x := by
  by_cases h : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

/-- Prékopa–Leindler log-concavity of Lebesgue measure on compact sets. -/
lemma volume_real_log_concave_compact
    (A B : Set (EuclideanSpace ℝ (Fin n))) (hA : IsCompact A) (hB : IsCompact B)
    (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1) :
    (volume.real A) ^ (1 - lam) * (volume.real B) ^ lam
      ≤ volume.real ((1 - lam) • A + lam • B) := by
  have hAmeas : MeasurableSet A := hA.isClosed.measurableSet
  have hBmeas : MeasurableSet B := hB.isClosed.measurableSet
  have hKA : IsCompact ((1 - lam) • A) := hA.smul (1 - lam)
  have hKB : IsCompact (lam • B) := hB.smul lam
  have hK : IsCompact ((1 - lam) • A + lam • B) := hKA.add hKB
  have hKmeas : MeasurableSet ((1 - lam) • A + lam • B) := hK.isClosed.measurableSet
  have hhyp : ∀ x y, ((1 - lam) • A + lam • B).indicator (fun _ => (1:ℝ))
        ((1 - lam) • x + lam • y)
      ≥ (A.indicator (fun _ => (1:ℝ))) x ^ (1 - lam)
        * (B.indicator (fun _ => (1:ℝ))) y ^ lam := by
    intro x y
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ B
      · have hmem : (1 - lam) • x + lam • y ∈ (1 - lam) • A + lam • B :=
          ⟨_, Set.smul_mem_smul_set hx, _, Set.smul_mem_smul_set hy, rfl⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hx, Set.indicator_of_mem hy,
            Real.one_rpow, Real.one_rpow, mul_one]
      · have hy' : (B.indicator (fun _ => (1:ℝ))) y = 0 := Set.indicator_of_notMem hy _
        rw [hy', Real.zero_rpow (ne_of_gt hl0), mul_zero]
        exact indicator_one_nonneg _ _
    · have hx' : (A.indicator (fun _ => (1:ℝ))) x = 0 := Set.indicator_of_notMem hx _
      rw [hx', Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < 1 - lam)), zero_mul]
      exact indicator_one_nonneg _ _
  have hPL := Commons.Analysis.Convex.prekopa_leindler_inequality
      (A.indicator (fun _ => (1:ℝ))) (B.indicator (fun _ => (1:ℝ)))
      (((1 - lam) • A + lam • B).indicator (fun _ => (1:ℝ)))
      lam hl0.le hl1.le
      (fun x => indicator_one_nonneg _ x) (fun x => indicator_one_nonneg _ x)
      (fun x => indicator_one_nonneg _ x)
      (integrable_indicator_one' A hAmeas hA.measure_ne_top)
      (integrable_indicator_one' B hBmeas hB.measure_ne_top)
      (integrable_indicator_one' _ hKmeas hK.measure_ne_top)
      hhyp
  have keyA : ∫ x, A.indicator (fun _ => (1:ℝ)) x = volume.real A := by
    rw [show (fun _ => (1:ℝ)) = (1 : EuclideanSpace ℝ (Fin n) → ℝ) from rfl]
    exact integral_indicator_one hAmeas
  have keyB : ∫ x, B.indicator (fun _ => (1:ℝ)) x = volume.real B := by
    rw [show (fun _ => (1:ℝ)) = (1 : EuclideanSpace ℝ (Fin n) → ℝ) from rfl]
    exact integral_indicator_one hBmeas
  have keyK : ∫ x, ((1 - lam) • A + lam • B).indicator (fun _ => (1:ℝ)) x
      = volume.real ((1 - lam) • A + lam • B) := by
    rw [show (fun _ => (1:ℝ)) = (1 : EuclideanSpace ℝ (Fin n) → ℝ) from rfl]
    exact integral_indicator_one hKmeas
  rw [keyA, keyB, keyK] at hPL
  exact hPL

/-- Brunn–Minkowski for compact sets with positive volume. -/
lemma brunn_minkowski_compact (hn : 0 < n)
    (A B : Set (EuclideanSpace ℝ (Fin n))) (hA : IsCompact A) (hB : IsCompact B)
    (hApos : 0 < volume.real A) (hBpos : 0 < volume.real B) :
    volume.real A ^ (1 / (n : ℝ)) + volume.real B ^ (1 / (n : ℝ))
      ≤ volume.real (A + B) ^ (1 / (n : ℝ)) := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  set α : ℝ := volume.real A ^ (1 / (n : ℝ)) with hα
  set β : ℝ := volume.real B ^ (1 / (n : ℝ)) with hβ
  have hαpos : 0 < α := by rw [hα]; exact Real.rpow_pos_of_pos hApos _
  have hβpos : 0 < β := by rw [hβ]; exact Real.rpow_pos_of_pos hBpos _
  have hαn : α ^ n = volume.real A := by
    rw [hα, one_div]
    exact Real.rpow_inv_natCast_pow hApos.le (by omega)
  have hβn : β ^ n = volume.real B := by
    rw [hβ, one_div]
    exact Real.rpow_inv_natCast_pow hBpos.le (by omega)
  set lam : ℝ := β / (α + β) with hlam
  have hlam0 : 0 < lam := by rw [hlam]; exact div_pos hβpos (by linarith)
  have hlam1 : lam < 1 := by rw [hlam, div_lt_one (by linarith)]; linarith
  have hscale1 : (1 - lam) * α⁻¹ = 1 / (α + β) := by
    rw [hlam]; field_simp; try ring
  have hscale2 : lam * β⁻¹ = 1 / (α + β) := by
    rw [hlam]; field_simp; try ring
  have hset : (1 - lam) • (α⁻¹ • A) + lam • (β⁻¹ • B) = (1 / (α + β)) • (A + B) := by
    rw [smul_smul, smul_smul, hscale1, hscale2, ← smul_add_eq_smul_add_smul]
  have hvolA' : volume.real (α⁻¹ • A) = 1 := by
    rw [volume_real_smul _ (by positivity), ← hαn, ← mul_pow, inv_mul_cancel₀ hαpos.ne',
      one_pow]
  have hvolB' : volume.real (β⁻¹ • B) = 1 := by
    rw [volume_real_smul _ (by positivity), ← hβn, ← mul_pow, inv_mul_cancel₀ hβpos.ne',
      one_pow]
  have hPL := volume_real_log_concave_compact (α⁻¹ • A) (β⁻¹ • B)
      (hA.smul _) (hB.smul _) lam hlam0 hlam1
  rw [hvolA', hvolB', Real.one_rpow, Real.one_rpow, one_mul, hset, volume_real_smul _ (by positivity),
      one_div] at hPL
  -- hPL : 1 ≤ ((α+β)⁻¹)^n * volume.real (A+B)
  have hpowinv : ((α + β)⁻¹) ^ n = ((α + β) ^ n)⁻¹ := inv_pow _ _
  rw [hpowinv] at hPL
  have hpown : 0 < (α + β) ^ n := pow_pos (by linarith) n
  have hAB : (α + β) ^ n ≤ volume.real (A + B) := by
    have h := mul_le_mul_of_nonneg_left hPL hpown.le
    rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hpown.ne', one_mul] at h
    exact h
  have key := Real.rpow_le_rpow (x := (α + β) ^ n) (y := volume.real (A + B))
      (z := 1 / (n : ℝ)) (pow_nonneg (by linarith) n) hAB
      (by rw [one_div]; exact inv_nonneg.mpr hn'.le)
  rw [one_div, Real.pow_rpow_inv_natCast (by linarith : (0:ℝ) ≤ α + β) (by omega)] at key
  simpa only [one_div] using key

/-- Inner approximation of a finite-measure set by compact subsets, in real measure. -/
lemma exists_isCompact_subset_measureReal_lt
    (A : Set (EuclideanSpace ℝ (Fin n))) (hA : MeasurableSet A) (hAf : volume A ≠ ∞)
    (hApos : 0 < volume.real A) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ volume.real A - ε < volume.real K := by
  by_cases hεA : ε ≤ volume.real A
  · have hεlt : ENNReal.ofReal (volume.real A - ε) < volume A := by
      rw [← ofReal_measureReal hAf, ENNReal.ofReal_lt_ofReal_iff hApos]
      linarith
    obtain ⟨K, hKA, hKc, hK⟩ := hA.exists_lt_isCompact_of_ne_top hAf hεlt
    refine ⟨K, hKA, hKc, ?_⟩
    have h1 : (ENNReal.ofReal (volume.real A - ε)).toReal < (volume K).toReal :=
      (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hKc.measure_ne_top).mpr hK
    rwa [ENNReal.toReal_ofReal (by linarith), measureReal_def] at h1
  · refine ⟨∅, empty_subset _, isCompact_empty, ?_⟩
    rw [measureReal_empty]
    linarith [not_le.mp hεA]

/-- The reverse-Minkowski (Brunn–Minkowski) inequality for measurable bounded sets. -/
theorem brunn_minkowski_add {n : ℕ} (hn : 0 < n)
    (A B : Set (EuclideanSpace ℝ (Fin n)))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAb : Bornology.IsBounded A) (hBb : Bornology.IsBounded B)
    (hApos : 0 < MeasureTheory.volume.real A) (hBpos : 0 < MeasureTheory.volume.real B) :
    MeasureTheory.volume.real A ^ ((1 : ℝ) / (n : ℝ))
        + MeasureTheory.volume.real B ^ ((1 : ℝ) / (n : ℝ))
      ≤ MeasureTheory.volume.real (A + B) ^ ((1 : ℝ) / (n : ℝ)) := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hz : 0 ≤ (1 : ℝ) / (n : ℝ) := by rw [one_div]; exact inv_nonneg.mpr hn'.le
  have hAf : volume A ≠ ∞ := hAb.measure_lt_top.ne
  have hBf : volume B ≠ ∞ := hBb.measure_lt_top.ne
  have hABf : volume (A + B) ≠ ∞ := (hAb.add hBb).measure_lt_top.ne
  have hKq : ∀ m : ℕ, ∃ K : Set (EuclideanSpace ℝ (Fin n)), K ⊆ A ∧ IsCompact K ∧
      volume.real A - 1 / ((m : ℝ) + 1) < volume.real K :=
    fun m => exists_isCompact_subset_measureReal_lt A hA hAf hApos (by positivity)
  choose K hKsub hKcpt hKapprox using hKq
  have hLq : ∀ m : ℕ, ∃ L : Set (EuclideanSpace ℝ (Fin n)), L ⊆ B ∧ IsCompact L ∧
      volume.real B - 1 / ((m : ℝ) + 1) < volume.real L :=
    fun m => exists_isCompact_subset_measureReal_lt B hB hBf hBpos (by positivity)
  choose L hLsub hLcpt hLapprox using hLq
  have hlinA : Tendsto (fun m : ℕ => volume.real A - 1 / ((m : ℝ) + 1)) atTop
      (nhds (volume.real A)) := by
    have h' := (tendsto_const_nhds (x := volume.real A) (f := atTop)).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using h'
  have hlinB : Tendsto (fun m : ℕ => volume.real B - 1 / ((m : ℝ) + 1)) atTop
      (nhds (volume.real B)) := by
    have h' := (tendsto_const_nhds (x := volume.real B) (f := atTop)).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using h'
  have hKtend : Tendsto (fun m : ℕ => volume.real (K m)) atTop (nhds (volume.real A)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (h := fun _ : ℕ => volume.real A) hlinA ?_ ?_ ?_
    · exact tendsto_const_nhds
    · intro m; exact (hKapprox m).le
    · intro m; exact measureReal_mono (hKsub m) hAf
  have hLtend : Tendsto (fun m : ℕ => volume.real (L m)) atTop (nhds (volume.real B)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (h := fun _ : ℕ => volume.real B) hlinB ?_ ?_ ?_
    · exact tendsto_const_nhds
    · intro m; exact (hLapprox m).le
    · intro m; exact measureReal_mono (hLsub m) hBf
  have hu : Tendsto (fun m : ℕ => volume.real (K m) ^ ((1:ℝ)/(n:ℝ))
      + volume.real (L m) ^ ((1:ℝ)/(n:ℝ))) atTop
      (nhds (volume.real A ^ ((1:ℝ)/(n:ℝ)) + volume.real B ^ ((1:ℝ)/(n:ℝ)))) :=
    (hKtend.rpow_const (Or.inr hz)).add (hLtend.rpow_const (Or.inr hz))
  have hle : ∀ᶠ m in atTop, volume.real (K m) ^ ((1:ℝ)/(n:ℝ))
      + volume.real (L m) ^ ((1:ℝ)/(n:ℝ)) ≤ volume.real (A + B) ^ ((1:ℝ)/(n:ℝ)) := by
    filter_upwards [hKtend.eventually (isOpen_Ioi.mem_nhds hApos),
      hLtend.eventually (isOpen_Ioi.mem_nhds hBpos)] with m hmK hmL
    have h1 := brunn_minkowski_compact hn (K m) (L m) (hKcpt m) (hLcpt m) hmK hmL
    have h2 : volume.real (K m + L m) ≤ volume.real (A + B) :=
      measureReal_mono (Set.add_subset_add (hKsub m) (hLsub m)) hABf
    have h3 : volume.real (K m + L m) ^ ((1:ℝ)/(n:ℝ))
        ≤ volume.real (A + B) ^ ((1:ℝ)/(n:ℝ)) :=
      Real.rpow_le_rpow measureReal_nonneg h2 hz
    linarith
  exact le_of_tendsto hu hle

end Commons.GeometryOfNumbers
