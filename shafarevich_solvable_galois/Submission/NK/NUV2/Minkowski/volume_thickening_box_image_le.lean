import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.Minkowski

open MeasureTheory MeasureTheory.Measure

/-- Covering of a box by the cubes of a grid of mesh `δ`: if `N i` is a natural number with
`(b i - a i) / δ ≤ N i` for every `i`, then `∏ i, [a i, b i]` is contained in the union of the
cubes `∏ i, [a i + m i * δ, a i + (m i + 1) * δ]` over all multi-indices `m` with `m i ≤ N i`. -/
lemma box_subset_iUnion_cube {ι : Type*} [Fintype ι] (a b : ι → ℝ) (N : ι → ℕ)
    {δ : ℝ} (hδ : 0 < δ) (hN : ∀ i, (b i - a i) / δ ≤ (N i : ℝ)) :
    Set.univ.pi (fun i => Set.Icc (a i) (b i)) ⊆
      ⋃ m : (i : ι) → Fin (N i + 1),
        Set.univ.pi (fun i => Set.Icc (a i + (m i : ℕ) * δ) (a i + ((m i : ℕ) + 1) * δ)) := by
  intro x hx
  rw [Set.mem_iUnion]
  refine ⟨fun i => ⟨⌊(x i - a i) / δ⌋₊, ?_⟩, ?_⟩
  · have hxi : x i ∈ Set.Icc (a i) (b i) := Set.mem_univ_pi.mp hx i
    have h1 : (x i - a i) / δ ≤ (N i : ℝ) :=
      le_trans (div_le_div_of_nonneg_right (by linarith [hxi.2]) hδ.le) (hN i)
    have h2 : ⌊(x i - a i) / δ⌋₊ ≤ N i := by
      have := Nat.floor_mono h1
      rwa [Nat.floor_natCast] at this
    omega
  · rw [Set.mem_univ_pi]
    intro i
    have hxi : x i ∈ Set.Icc (a i) (b i) := Set.mem_univ_pi.mp hx i
    have hxA : 0 ≤ x i - a i := by linarith [hxi.1]
    have h1 : ((⌊(x i - a i) / δ⌋₊ : ℕ) : ℝ) * δ ≤ x i - a i := by
      have h := Nat.floor_le (show 0 ≤ (x i - a i) / δ from div_nonneg hxA hδ.le)
      rwa [le_div_iff₀ hδ] at h
    have h2 : x i - a i < (((⌊(x i - a i) / δ⌋₊ : ℕ) : ℝ) + 1) * δ := by
      have h := Nat.lt_floor_add_one ((x i - a i) / δ)
      rwa [div_lt_iff₀ hδ] at h
    constructor
    · push_cast; linarith
    · push_cast; linarith

/-- **Minkowski content of a Lipschitz image of a box.** If `g` is `L`-Lipschitz on the box
`∏ i, [a i, b i] ⊆ ι → ℝ` (nondegenerate, `Fintype.card ι ≤ finrank ℝ E`), then the
`ε`-neighbourhood of the image `g '' box` has volume `≤ C ε ^ (finrank ℝ E - card ι)`
for `0 < ε ≤ 1`. The intended proof: cover the box by `≍ ε^(-card ι)` cubes of side `ε/(L+1)`;
the image of each cube lies in a ball of radius `≲ ε`, and the union of their `ε`-neighbourhoods
has volume `≲ ε^(card ι) · ε^(finrank ℝ E - card ι)`. -/
theorem volume_thickening_box_image_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) (hab : ∀ i, a i < b i)
    (hk : Fintype.card ι ≤ Module.finrank ℝ E)
    (g : (ι → ℝ) → E) (L : NNReal)
    (hL : LipschitzOnWith L g (Set.univ.pi fun i => Set.Icc (a i) (b i))) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (volume {x : E | ∃ q ∈ (Set.univ.pi fun i => Set.Icc (a i) (b i)), ‖x - g q‖ ≤ ε}).toReal
        ≤ C * ε ^ ((Module.finrank ℝ E : ℝ) - (Fintype.card ι : ℝ)) := by
  classical
  have _ := hk
  set B : Set (ι → ℝ) := Set.univ.pi (fun i => Set.Icc (a i) (b i)) with hB
  set K : ℝ := ∏ i, (b i - a i + 2) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact Finset.prod_nonneg (fun i _ => by linarith [hab i])
  set V : ℝ := (volume (Metric.closedBall (0:E) 1)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set A : ℝ := K * ((L:ℝ)+1) ^ (Fintype.card ι) * (2:ℝ) ^ (Module.finrank ℝ E) * V with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (mul_nonneg (mul_nonneg hK0 (by positivity)) (by positivity)) hV0
  refine ⟨A + 1, by linarith, ?_⟩
  intro ε hε0 hε1
  set δ : ℝ := ε / ((L:ℝ) + 1) with hδdef
  have hL1 : (0:ℝ) < (L:ℝ) + 1 := by positivity
  have hδ0 : 0 < δ := by rw [hδdef]; exact div_pos hε0 hL1
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one hL1]
    linarith [L.coe_nonneg, hε1]
  have hLδ : (L:ℝ) * δ ≤ ε := by
    have hle : (L:ℝ) / ((L:ℝ) + 1) ≤ 1 := (div_le_one hL1).mpr (by linarith)
    have heq : (L:ℝ) * δ = ε * ((L:ℝ) / ((L:ℝ) + 1)) := by
      rw [hδdef]; field_simp
    rw [heq]
    simpa using mul_le_of_le_one_right hε0.le hle
  set N : ι → ℕ := fun i => ⌈(b i - a i) / δ⌉₊ with hN
  have hNbound : ∀ i, (b i - a i) / δ ≤ (N i : ℝ) := by
    intro i; simp only [hN]; exact Nat.le_ceil _
  let cube : ((i : ι) → Fin (N i + 1)) → Set (ι → ℝ) := fun m =>
    Set.univ.pi (fun i => Set.Icc (a i + (m i : ℕ) * δ) (a i + ((m i : ℕ) + 1) * δ))
  have hcover : B ⊆ ⋃ m, cube m := by
    intro x hx
    rw [Set.mem_iUnion]
    have hx' : x ∈ Set.univ.pi (fun i => Set.Icc (a i) (b i)) := by rwa [hB] at hx
    have h := box_subset_iUnion_cube a b N hδ0 hNbound hx'
    rwa [Set.mem_iUnion] at h
  let q : ((i : ι) → Fin (N i + 1)) → (ι → ℝ) :=
    fun m => if h : (B ∩ cube m).Nonempty then h.some else 0
  have hq_mem : ∀ m, (B ∩ cube m).Nonempty → q m ∈ B ∩ cube m := by
    intro m h
    simp only [q]
    rw [dif_pos h]
    exact h.some_mem
  have hsub : {x : E | ∃ p ∈ B, ‖x - g p‖ ≤ ε} ⊆
      ⋃ m, Metric.closedBall (g (q m)) (2 * ε) := by
    intro x hx
    obtain ⟨p, hpB, hpx⟩ := hx
    rw [Set.mem_iUnion]
    have hp_cov : p ∈ ⋃ m, cube m := hcover hpB
    rw [Set.mem_iUnion] at hp_cov
    obtain ⟨m, hm⟩ := hp_cov
    refine ⟨m, ?_⟩
    have hne : (B ∩ cube m).Nonempty := ⟨p, hpB, hm⟩
    have hqmem := hq_mem m hne
    have hqB : q m ∈ B := hqmem.1
    have hqm : q m ∈ cube m := hqmem.2
    have hp' : p ∈ Set.univ.pi
        (fun i => Set.Icc (a i + (m i : ℕ) * δ) (a i + ((m i : ℕ) + 1) * δ)) := by
      simpa only [cube] using hm
    have hq' : q m ∈ Set.univ.pi
        (fun i => Set.Icc (a i + (m i : ℕ) * δ) (a i + ((m i : ℕ) + 1) * δ)) := by
      simpa only [cube] using hqm
    have hdist : dist p (q m) ≤ δ := by
      rw [dist_pi_le_iff hδ0.le]
      intro i
      have h1 := Set.mem_univ_pi.mp hp' i
      have h2 := Set.mem_univ_pi.mp hq' i
      rw [Real.dist_eq, abs_sub_le_iff]
      exact ⟨by linarith [h1.2, h2.1], by linarith [h1.1, h2.2]⟩
    have hlip : dist (g p) (g (q m)) ≤ (L:ℝ) * δ :=
      (hL.dist_le_mul p hpB (q m) hqB).trans (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)
    have hpx' : dist x (g p) ≤ ε := by simpa only [dist_eq_norm] using hpx
    rw [Metric.mem_closedBall]
    calc dist x (g (q m)) ≤ dist x (g p) + dist (g p) (g (q m)) := dist_triangle _ _ _
      _ ≤ ε + (L:ℝ) * δ := add_le_add hpx' hlip
      _ ≤ ε + ε := by linarith
      _ = 2 * ε := by ring
  have hVfin : volume (Metric.closedBall (0:E) 1) ≠ ⊤ :=
    (isCompact_closedBall (0:E) (1:ℝ)).measure_lt_top.ne
  have hball : ∀ m, volume (Metric.closedBall (g (q m)) (2*ε))
      = ENNReal.ofReal ((2*ε) ^ Module.finrank ℝ E) * volume (Metric.closedBall (0:E) 1) := by
    intro m
    exact MeasureTheory.Measure.addHaar_closedBall' volume (g (q m)) (by positivity)
  have hsum : (∑ m, volume (Metric.closedBall (g (q m)) (2*ε)))
      = (Fintype.card ((i : ι) → Fin (N i + 1)) : ENNReal)
          * (ENNReal.ofReal ((2*ε) ^ Module.finrank ℝ E)
              * volume (Metric.closedBall (0:E) 1)) := by
    simp only [hball, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsum_ne_top : (∑ m, volume (Metric.closedBall (g (q m)) (2*ε))) ≠ ⊤ := by
    rw [hsum]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin)
  have htoReal_sum : (∑ m, volume (Metric.closedBall (g (q m)) (2*ε))).toReal
      = (Fintype.card ((i : ι) → Fin (N i + 1)) : ℝ) * ((2*ε) ^ Module.finrank ℝ E * V) := by
    rw [hsum, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity), ← hV]
  have hvol : volume {x : E | ∃ p ∈ B, ‖x - g p‖ ≤ ε} ≤
      ∑ m, volume (Metric.closedBall (g (q m)) (2*ε)) :=
    (measure_mono hsub).trans (measure_iUnion_fintype_le volume _)
  have hNcard : (Fintype.card ((i : ι) → Fin (N i + 1)) : ℝ) ≤ K / δ ^ (Fintype.card ι) := by
    rw [hK]
    simp only [Fintype.card_pi, Fintype.card_fin]
    rw [Nat.cast_prod]
    have hfac : ∀ i ∈ (Finset.univ : Finset ι), (((N i + 1 : ℕ) : ℝ)) ≤ (b i - a i + 2)/δ := by
      intro i _
      have hyi : (0:ℝ) ≤ (b i - a i)/δ := div_nonneg (by linarith [hab i]) hδ0.le
      have hc : (N i : ℝ) ≤ (b i - a i)/δ + 1 := by
        simp only [hN]
        exact (Nat.ceil_lt_add_one hyi).le
      have h2 : (2:ℝ) ≤ 2/δ := by rw [le_div_iff₀ hδ0]; linarith [hδ1]
      rw [Nat.cast_add, Nat.cast_one, add_div]
      linarith
    have h1 : ∏ i, ((N i + 1 : ℕ) : ℝ) ≤ ∏ i, ((b i - a i + 2)/δ) :=
      Finset.prod_le_prod₀ (fun i _ => by positivity) hfac
    have h2 : ∏ i, ((b i - a i + 2)/δ) = (∏ i, (b i - a i + 2)) / δ ^ (Fintype.card ι) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
    exact h1.trans h2.le
  have hAexpr : K / δ ^ (Fintype.card ι) * ((2*ε) ^ Module.finrank ℝ E * V)
      = A * ε ^ ((Module.finrank ℝ E : ℝ) - (Fintype.card ι : ℝ)) := by
    have key : ε ^ Module.finrank ℝ E * (ε ^ Fintype.card ι)⁻¹
        = ε ^ ((Module.finrank ℝ E : ℝ) - (Fintype.card ι : ℝ)) := by
      rw [← Real.rpow_natCast ε (Module.finrank ℝ E),
          ← Real.rpow_natCast ε (Fintype.card ι),
          ← Real.rpow_neg hε0.le (Fintype.card ι : ℝ), ← Real.rpow_add hε0]
      congr 1
    have hsplit : K / δ ^ (Fintype.card ι) * ((2*ε) ^ Module.finrank ℝ E * V)
        = (K * ((L:ℝ)+1) ^ (Fintype.card ι) * (2:ℝ) ^ (Module.finrank ℝ E) * V)
          * (ε ^ Module.finrank ℝ E * (ε ^ Fintype.card ι)⁻¹) := by
      rw [hδdef, div_pow, div_div_eq_mul_div, div_eq_mul_inv, mul_pow]
      ring
    rw [hA, hsplit, key]
  have h1 : (volume {x : E | ∃ p ∈ B, ‖x - g p‖ ≤ ε}).toReal
      ≤ (Fintype.card ((i : ι) → Fin (N i + 1)) : ℝ) * ((2*ε) ^ Module.finrank ℝ E * V) :=
    (ENNReal.toReal_mono hsum_ne_top hvol).trans_eq htoReal_sum
  have h2 : (Fintype.card ((i : ι) → Fin (N i + 1)) : ℝ) * ((2*ε) ^ Module.finrank ℝ E * V)
      ≤ K / δ ^ (Fintype.card ι) * ((2*ε) ^ Module.finrank ℝ E * V) :=
    mul_le_mul_of_nonneg_right hNcard (mul_nonneg (by positivity) hV0)
  have h3 : K / δ ^ (Fintype.card ι) * ((2*ε) ^ Module.finrank ℝ E * V)
      ≤ (A + 1) * ε ^ ((Module.finrank ℝ E : ℝ) - (Fintype.card ι : ℝ)) := by
    rw [hAexpr, add_mul, one_mul]
    exact le_add_of_nonneg_right (Real.rpow_nonneg hε0.le _)
  exact h1.trans (h2.trans h3)

end NK.NUV2.Minkowski
