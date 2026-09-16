import Mathlib
import Submission.Commons.Analysis.TensorApprox.exists_tensor_partition_unity
import Submission.Commons.Analysis.Calculus.exists_contDiff_partition_unity

namespace Commons.Analysis.TensorApprox

open scoped BigOperators
open Finset

/-- A box sum of a one-dimensional partition of unity is at most `1`. -/
lemma sum_Icc_partition_le_one {ψ : ℤ → ℝ → ℝ}
    (hsum : ∀ y, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), ψ m y) = 1)
    (hnn : ∀ m x, 0 ≤ ψ m x) (n : ℕ) (y : ℝ) :
    (∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), ψ m y) ≤ 1 := by
  obtain ⟨N, hN⟩ := hsum y
  have hn : n ≤ max n N := le_max_left n N
  have hn' : (n : ℤ) ≤ ((max n N : ℕ) : ℤ) := by exact_mod_cast hn
  have hsub : Finset.Icc (-(n : ℤ)) (n : ℤ) ⊆
      Finset.Icc (-(((max n N : ℕ)) : ℤ)) (((max n N : ℕ)) : ℤ) := by
    intro m hm
    simp only [Finset.mem_Icc] at hm ⊢
    constructor <;> omega
  calc (∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), ψ m y)
      ≤ ∑ m ∈ Finset.Icc (-(((max n N : ℕ)) : ℤ)) (((max n N : ℕ)) : ℤ), ψ m y :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnn i y)
    _ = 1 := hN (max n N) (le_max_right n N)

/-- The `k`-fold tensor box sum of a one-dimensional partition of unity is at most `1`. -/
lemma tensor_box_le_one {ψ : ℤ → ℝ → ℝ} {k : ℕ}
    (hsum : ∀ y, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), ψ m y) = 1)
    (hnn : ∀ m x, 0 ≤ ψ m x) (n : ℕ) (t : Fin k → ℝ) :
    (∑ m ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(n : ℤ)) (n : ℤ)),
      ∏ i, ψ (m i) (t i)) ≤ 1 := by
  rw [Finset.sum_prod_piFinset (Finset.Icc (-(n : ℤ)) (n : ℤ))
    (fun (i : Fin k) (j : ℤ) => ψ j (t i))]
  exact Finset.prod_le_one (fun i _ => Finset.sum_nonneg (fun j _ => hnn j (t i)))
    (fun i _ => sum_Icc_partition_le_one hsum hnn n (t i))

/-- The `k`-fold tensor box sum of a rescaled one-dimensional partition of unity equals
`1`, provided the box is large enough relative to the point. -/
lemma tensor_box_eq_one {ψ : ℤ → ℝ → ℝ} {k : ℕ}
    (hsupp : ∀ m, Function.support (ψ m) ⊆ Set.Icc ((m : ℝ) - 1) ((m : ℝ) + 1))
    (hsum : ∀ y, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), ψ m y) = 1)
    {σ : ℝ} (hσ : 0 < σ) {N : ℕ} {t : Fin k → ℝ} (hN : ∀ i, |t i| / σ + 2 ≤ (N : ℝ)) :
    (∑ m ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(N : ℤ)) (N : ℤ)),
      ∏ i, ψ (m i) (t i / σ)) = 1 := by
  rw [Finset.sum_prod_piFinset (Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun (i : Fin k) (j : ℤ) => ψ j (t i / σ))]
  refine Finset.prod_eq_one (fun i _ => ?_)
  exact sum_partition_unity_eq_one hsupp hsum (by rw [abs_div, abs_of_pos hσ]; exact hN i)

/-- A nonzero tensor weight pins the point within `σ` of the corresponding grid point. -/
lemma abs_sub_mul_le_of_prod_ne_zero {ψ : ℤ → ℝ → ℝ} {k : ℕ}
    (hsupp : ∀ m, Function.support (ψ m) ⊆ Set.Icc ((m : ℝ) - 1) ((m : ℝ) + 1))
    {σ : ℝ} (hσ : 0 < σ) {m : Fin k → ℤ} {t : Fin k → ℝ}
    (h : (∏ i, ψ (m i) (t i / σ)) ≠ 0) :
    ∀ i, |t i - (m i : ℝ) * σ| ≤ σ := by
  intro i
  have hi : ψ (m i) (t i / σ) ≠ 0 := fun hzero =>
    h (by simpa using Finset.prod_eq_zero (Finset.mem_univ i) hzero)
  have hmem := hsupp (m i) hi
  rw [Set.mem_Icc] at hmem
  have h1 : t i / σ - (m i : ℝ) ≤ 1 := by linarith [hmem.2]
  have h2 : -1 ≤ t i / σ - (m i : ℝ) := by linarith [hmem.1]
  have h3 : t i - (m i : ℝ) * σ = (t i / σ - (m i : ℝ)) * σ := by
    field_simp
  have h4 : |t i / σ - (m i : ℝ)| ≤ 1 := by
    rw [abs_le]
    exact ⟨h2, h1⟩
  rw [h3, abs_mul, abs_of_pos hσ]
  calc |t i / σ - (m i : ℝ)| * σ ≤ 1 * σ := mul_le_mul_of_nonneg_right h4 hσ.le
    _ = σ := one_mul σ

/-- A weighted sum identity: if the weights sum to `1`, the deviation from `x` is the
weighted sum of the deviations. -/
lemma sub_sum_eq_sum_sub {ι : Type*} [Fintype ι] {P G : ι → ℝ} {x : ℝ}
    (hP : ∑ m, P m = 1) :
    x - ∑ m, G m * P m = ∑ m, (x - G m) * P m := by
  rw [Finset.sum_congr rfl (fun m _ => by ring : ∀ m ∈ (Finset.univ : Finset ι),
      (x - G m) * P m = x * P m - G m * P m)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hP, mul_one]

/-- Localised tensor approximation: a continuous compactly supported `g` on `Fin k → ℝ`
whose support lies in `{t | ∑ i, t i ≤ R}` is uniformly approximated by a finite tensor sum
`∑ j, c j * ∏ i, h j i (t i)` whose one-variable components `h j i` are smooth, compactly
supported, and supported in `(-∞, β j i]`, with `∑ i, β j i ≤ R + 6 * k * η`. -/
theorem exists_tensor_localization {k : ℕ} {g : (Fin k → ℝ) → ℝ} (hg : Continuous g)
    (hcs : HasCompactSupport g) {R : ℝ} (hR : ∀ t, g t ≠ 0 → ∑ i, t i ≤ R)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℝ) (β : ι → Fin k → ℝ) (h : ι → Fin k → ℝ → ℝ),
      (∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (h j i)) ∧
      (∀ j i, HasCompactSupport (h j i)) ∧
      (∀ j i u, β j i < u → h j i u = 0) ∧
      (∀ j, ∑ i, β j i ≤ R + 6 * (k : ℝ) * η) ∧
      (∀ t, |g t - ∑ j, c j * ∏ i, h j i (t i)| < ε) := by
  classical
  have hε2 : 0 < ε / 2 := by linarith
  -- Uniform continuity of `g`.
  have hu : UniformContinuous g :=
    hg.uniformContinuous_of_tendsto_cocompact hcs.is_zero_at_infty
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuous_iff.mp hu (ε / 2) hε2
  -- The support of `g` is bounded.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, Function.support g ⊆ Metric.closedBall (0 : Fin k → ℝ) C := by
    have hbdd : Bornology.IsBounded (tsupport g) :=
      (show IsCompact (tsupport g) from hcs).isBounded
    obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin k → ℝ)).1 hbdd
    exact ⟨C, Set.Subset.trans (subset_tsupport g) hC⟩
  -- Choose a step size `σ` small compared with `η` and with the continuity modulus.
  set σ : ℝ := min (min η 1) δ / 2 with hσdef
  have hσinner : 0 < min (min η 1) δ := lt_min (lt_min hη one_pos) hδpos
  have hσpos : 0 < σ := by rw [hσdef]; exact div_pos hσinner two_pos
  have hσleη : σ ≤ η := by
    rw [hσdef]
    have h2 : min (min η 1) δ ≤ η := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hσltδ : σ < δ := by
    rw [hσdef]
    have h2 : min (min η 1) δ ≤ δ := min_le_right _ _
    linarith
  -- The one-dimensional partition of unity.
  obtain ⟨ψ₀, hψsm, hψsupp, hψnn, hψsum⟩ :=
    Commons.Analysis.Calculus.exists_contDiff_partition_unity
  have hψnn' : ∀ (m : Fin k → ℤ) (t : Fin k → ℝ), 0 ≤ (∏ i, ψ₀ (m i) (t i / σ)) :=
    fun m t => Finset.prod_nonneg (fun i _ => hψnn _ _)
  -- Box size.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, C / σ + 2 ≤ (N : ℝ) := exists_nat_ge (C / σ + 2)
  have hNle : ∀ t ∈ Function.support g, ∀ i, |t i| / σ + 2 ≤ (N : ℝ) := by
    intro t ht i
    have h1 : t ∈ Metric.closedBall (0 : Fin k → ℝ) C := hC ht
    rw [Metric.mem_closedBall] at h1
    have h2 : dist (t i) (0 : ℝ) ≤ C :=
      (dist_pi_le_iff (le_trans dist_nonneg h1)).mp h1 i
    rw [Real.dist_eq] at h2
    have h2' : |t i| ≤ C := by simpa using h2
    have h3 : |t i| / σ ≤ C / σ := div_le_div_of_nonneg_right h2' hσpos.le
    linarith
  -- The box and the localisation constraint.
  set B : Finset (Fin k → ℤ) :=
    Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(N : ℤ)) (N : ℤ)) with hB
  set Cb : ℝ := R / σ + 6 * (k : ℝ) * η / σ - (k : ℝ) with hCbdef
  set S : Finset (Fin k → ℤ) := B.filter (fun m => (∑ i, ((m i : ℤ) : ℝ)) ≤ Cb) with hSdef
  -- Key estimates.
  have hgrid : ∀ (m : Fin k → ℤ) (t : Fin k → ℝ),
      (∏ i, ψ₀ (m i) (t i / σ)) ≠ 0 → ∀ i, |t i - (m i : ℝ) * σ| ≤ σ :=
    fun m t h => abs_sub_mul_le_of_prod_ne_zero hψsupp hσpos h
  have hvanish : ∀ (m : Fin k → ℤ) (t : Fin k → ℝ), t ∈ Function.support g → m ∈ B →
      m ∉ S → (∏ i, ψ₀ (m i) (t i / σ)) = 0 := by
    intro m t ht hmB hmS
    by_contra hne
    have hnot : ¬ ((∑ i, ((m i : ℤ) : ℝ)) ≤ Cb) := by
      intro hle
      exact hmS (by rw [hSdef]; exact Finset.mem_filter.mpr ⟨hmB, hle⟩)
    have hlt : Cb < ∑ i, ((m i : ℤ) : ℝ) := not_le.mp hnot
    have hd := hgrid m t hne
    have hsum_le : (∑ i, ((m i : ℤ) : ℝ)) * σ ≤ ∑ i, t i + (k : ℝ) * σ := by
      calc (∑ i, ((m i : ℤ) : ℝ)) * σ = ∑ i, ((m i : ℤ) : ℝ) * σ := Finset.sum_mul _ _ _
        _ ≤ ∑ i, (t i + σ) := Finset.sum_le_sum (fun i _ => by
              have := (abs_le.mp (hd i)).1
              linarith)
        _ = ∑ i, t i + (k : ℝ) * σ := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
              simp [nsmul_eq_mul]
    have htR : ∑ i, t i ≤ R := hR t ht
    have h1 : (∑ i, ((m i : ℤ) : ℝ)) ≤ R / σ + (k : ℝ) := by
      apply le_of_mul_le_mul_right _ hσpos
      calc (∑ i, ((m i : ℤ) : ℝ)) * σ ≤ ∑ i, t i + (k : ℝ) * σ := hsum_le
        _ ≤ R + (k : ℝ) * σ := by linarith
        _ = (R / σ + (k : ℝ)) * σ := by rw [add_mul, div_mul_cancel₀ _ hσpos.ne']
    have h2 : R / σ + (k : ℝ) ≤ Cb := by
      rw [hCbdef]
      have hησ : 1 ≤ η / σ := (one_le_div hσpos).mpr hσleη
      have h6 : 6 * (k : ℝ) * 1 ≤ 6 * (k : ℝ) * (η / σ) :=
        mul_le_mul_of_nonneg_left hησ (by positivity)
      have heq : 6 * (k : ℝ) * η / σ = 6 * (k : ℝ) * (η / σ) := by ring
      rw [heq]
      nlinarith
    linarith
  have hWle : ∀ t : Fin k → ℝ, (∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ))) ≤ 1 := by
    intro t
    obtain ⟨N', hN'le, hN'⟩ : ∃ N' : ℕ, N ≤ N' ∧ ∀ i, |t i| / σ + 2 ≤ (N' : ℝ) := by
      obtain ⟨M', hM'⟩ := exists_nat_ge ((∑ i, |t i|) / σ + 2)
      refine ⟨max N M', le_max_left N M', fun i => ?_⟩
      have h1 : |t i| ≤ ∑ j, |t j| :=
        Finset.single_le_sum (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i)
      have h2 : |t i| / σ ≤ (∑ j, |t j|) / σ := div_le_div_of_nonneg_right h1 hσpos.le
      have h3 : (M' : ℝ) ≤ ((max N M' : ℕ) : ℝ) := by
        exact_mod_cast le_max_right N M'
      linarith
    have hsub : S ⊆ Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(N' : ℤ)) (N' : ℤ)) := by
      intro m hm
      have hmB : m ∈ B := by
        have h' := hm
        rw [hSdef] at h'
        exact (Finset.mem_filter.mp h').1
      have hmB' : ∀ a, m a ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
        rw [hB, Fintype.mem_piFinset] at hmB
        exact hmB
      rw [Fintype.mem_piFinset]
      intro i
      have h2 := hmB' i
      rw [Finset.mem_Icc] at h2 ⊢
      have hle : (N : ℤ) ≤ (N' : ℤ) := by exact_mod_cast hN'le
      constructor <;> omega
    calc (∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ)))
        = ∑ m ∈ S, (∏ i, ψ₀ (m i) (t i / σ)) :=
          Finset.sum_coe_sort S (fun m => ∏ i, ψ₀ (m i) (t i / σ))
      _ ≤ ∑ m ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(N' : ℤ)) (N' : ℤ)),
            (∏ i, ψ₀ (m i) (t i / σ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun m _ _ => Finset.prod_nonneg (fun i _ => hψnn _ _))
      _ = 1 := tensor_box_eq_one hψsupp hψsum hσpos hN'
  have hW1 : ∀ t : Fin k → ℝ, g t ≠ 0 →
      (∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ))) = 1 := by
    intro t ht
    have htK : t ∈ Function.support g := ht
    calc (∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ)))
        = ∑ m ∈ S, (∏ i, ψ₀ (m i) (t i / σ)) :=
          Finset.sum_coe_sort S (fun m => ∏ i, ψ₀ (m i) (t i / σ))
      _ = ∑ m ∈ B, (∏ i, ψ₀ (m i) (t i / σ)) := by
          refine Finset.sum_subset ?_ ?_
          · intro m hm
            have h' := hm
            rw [hSdef] at h'
            exact (Finset.mem_filter.mp h').1
          · intro m hmB hmS
            exact hvanish m t htK hmB hmS
      _ = 1 := by
          rw [hB]
          exact tensor_box_eq_one hψsupp hψsum hσpos (hNle t htK)
  refine ⟨↥S, inferInstance, fun (m : ↥S) => g (fun i => ((m.1 i : ℤ) : ℝ) * σ),
    fun (m : ↥S) (i : Fin k) => ((m.1 i : ℤ) : ℝ) * σ + σ,
    fun (m : ↥S) (i : Fin k) => fun u : ℝ => ψ₀ (m.1 i) (u / σ), ?_, ?_, ?_, ?_, ?_⟩
  · intro m i
    exact (hψsm (m.1 i)).comp (by fun_prop)
  · intro m i
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (((m.1 i : ℤ) : ℝ) * σ - σ) (((m.1 i : ℤ) : ℝ) * σ + σ))
      isCompact_Icc ?_
    intro u hu
    have h := hψsupp (m.1 i) hu
    rw [Set.mem_Icc] at h ⊢
    constructor
    · have := mul_le_mul_of_nonneg_right h.1 hσpos.le
      rw [div_mul_cancel₀ u hσpos.ne'] at this
      linarith
    · have := mul_le_mul_of_nonneg_right h.2 hσpos.le
      rw [div_mul_cancel₀ u hσpos.ne'] at this
      linarith
  · intro m i u hu
    have h1 : u / σ ∉ Function.support (ψ₀ (m.1 i)) := by
      intro hmem
      have h2 := hψsupp (m.1 i) hmem
      rw [Set.mem_Icc] at h2
      have h3 : ((m.1 i : ℤ) : ℝ) + 1 < u / σ := by
        rw [lt_div_iff₀ hσpos]
        linarith
      linarith [h2.2]
    exact Function.notMem_support.mp h1
  · intro m
    have hle : (∑ i, ((m.1 i : ℤ) : ℝ)) ≤ Cb := (Finset.mem_filter.mp m.2).2
    have hsumβ : (∑ i, (((m.1 i : ℤ) : ℝ) * σ + σ)) =
        (∑ i, ((m.1 i : ℤ) : ℝ)) * σ + (k : ℝ) * σ := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin]
      simp [nsmul_eq_mul]
    rw [hsumβ]
    have hCb' : Cb * σ + (k : ℝ) * σ = R + 6 * (k : ℝ) * η := by
      rw [hCbdef]
      field_simp
      ring
    calc (∑ i, ((m.1 i : ℤ) : ℝ)) * σ + (k : ℝ) * σ
        ≤ Cb * σ + (k : ℝ) * σ := by
          have := mul_le_mul_of_nonneg_right hle hσpos.le
          linarith
      _ = R + 6 * (k : ℝ) * η := hCb'
  · intro t
    by_cases ht : g t = 0
    · have hb : ∀ m : ↥S,
          (∏ i, ψ₀ (m.1 i) (t i / σ)) * |g (fun i => ((m.1 i : ℤ) : ℝ) * σ)| ≤
            (∏ i, ψ₀ (m.1 i) (t i / σ)) * (ε / 2) := by
        intro m
        by_cases hP : (∏ i, ψ₀ (m.1 i) (t i / σ)) = 0
        · rw [hP, zero_mul, zero_mul]
        · have hd := hgrid m.1 t hP
          have hdist : dist t (fun i => ((m.1 i : ℤ) : ℝ) * σ) ≤ σ := by
            rw [dist_pi_le_iff hσpos.le]
            intro i
            simpa [Real.dist_eq, abs_sub_comm] using hd i
          have hcont := hδ (a := t) (b := fun i => ((m.1 i : ℤ) : ℝ) * σ)
            (lt_of_le_of_lt hdist hσltδ)
          rw [Real.dist_eq, ht, zero_sub, abs_neg] at hcont
          exact mul_le_mul_of_nonneg_left hcont.le (hψnn' m.1 t)
      calc |g t - ∑ m : ↥S, g (fun i => ((m.1 i : ℤ) : ℝ) * σ) *
              (∏ i, ψ₀ (m.1 i) (t i / σ))|
          = |∑ m : ↥S, g (fun i => ((m.1 i : ℤ) : ℝ) * σ) *
              (∏ i, ψ₀ (m.1 i) (t i / σ))| := by rw [ht, zero_sub, abs_neg]
        _ ≤ ∑ m : ↥S, |g (fun i => ((m.1 i : ℤ) : ℝ) * σ) *
              (∏ i, ψ₀ (m.1 i) (t i / σ))| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ)) *
              |g (fun i => ((m.1 i : ℤ) : ℝ) * σ)| := by
            refine Finset.sum_congr rfl (fun m _ => ?_)
            rw [abs_mul, abs_of_nonneg (hψnn' m.1 t), mul_comm]
        _ ≤ ∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ)) * (ε / 2) :=
            Finset.sum_le_sum (fun m _ => hb m)
        _ = (∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ))) * (ε / 2) :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ 1 * (ε / 2) := mul_le_mul_of_nonneg_right (hWle t) hε2.le
        _ < ε := by linarith
    · have hW1t := hW1 t ht
      rw [sub_sum_eq_sum_sub (P := fun m : ↥S => ∏ i, ψ₀ (m.1 i) (t i / σ))
        (G := fun m : ↥S => g (fun i => ((m.1 i : ℤ) : ℝ) * σ)) (x := g t) hW1t]
      have hb : ∀ m : ↥S,
          (∏ i, ψ₀ (m.1 i) (t i / σ)) *
              |g t - g (fun i => ((m.1 i : ℤ) : ℝ) * σ)| ≤
            (∏ i, ψ₀ (m.1 i) (t i / σ)) * (ε / 2) := by
        intro m
        by_cases hP : (∏ i, ψ₀ (m.1 i) (t i / σ)) = 0
        · rw [hP, zero_mul, zero_mul]
        · have hd := hgrid m.1 t hP
          have hdist : dist t (fun i => ((m.1 i : ℤ) : ℝ) * σ) ≤ σ := by
            rw [dist_pi_le_iff hσpos.le]
            intro i
            simpa [Real.dist_eq, abs_sub_comm] using hd i
          have hcont := hδ (a := t) (b := fun i => ((m.1 i : ℤ) : ℝ) * σ)
            (lt_of_le_of_lt hdist hσltδ)
          rw [Real.dist_eq] at hcont
          exact mul_le_mul_of_nonneg_left hcont.le (hψnn' m.1 t)
      calc |∑ m : ↥S, (g t - g (fun i => ((m.1 i : ℤ) : ℝ) * σ)) *
              (∏ i, ψ₀ (m.1 i) (t i / σ))|
          ≤ ∑ m : ↥S, |(g t - g (fun i => ((m.1 i : ℤ) : ℝ) * σ)) *
              (∏ i, ψ₀ (m.1 i) (t i / σ))| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ)) *
              |g t - g (fun i => ((m.1 i : ℤ) : ℝ) * σ)| := by
            refine Finset.sum_congr rfl (fun m _ => ?_)
            rw [abs_mul, abs_of_nonneg (hψnn' m.1 t), mul_comm]
        _ ≤ ∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ)) * (ε / 2) :=
            Finset.sum_le_sum (fun m _ => hb m)
        _ = (∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ))) * (ε / 2) :=
            (Finset.sum_mul _ _ _).symm
        _ = ε / 2 := by rw [hW1t, one_mul]
        _ < ε := by linarith

end Commons.Analysis.TensorApprox
