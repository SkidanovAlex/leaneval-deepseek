import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.PiSetup

/-!
# Splitting identities for the product measure on `ℝ^ℕ`

* `mkSeq_map`: the cons map `(u,z) ↦ (u, z₀, z₁, …)` pushes `μ ⊗ μ^ℕ` to `μ^ℕ`.
* `splitSeq_map`: splitting off the first `k` coordinates is measure preserving.
* `ae_divergence`: the partial sums diverge a.s.
-/

open MeasureTheory
open scoped ENNReal

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

theorem mkSeq_map {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    ((μ.prod (Measure.infinitePi (fun _ : ℕ => μ))).map mkSeq)
      = Measure.infinitePi (fun _ : ℕ => μ) := by
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply measurable_mkSeq
    (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have hset : mkSeq ⁻¹' Set.pi s t =
      (if 0 ∈ s then t 0 else Set.univ) ×ˢ
        (Set.pi ((s.erase 0).image (fun m => m - 1)) (fun j => t (j + 1))) := by
    ext p
    rw [Set.mem_preimage, Set.mem_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · by_cases h0 : 0 ∈ s
        · rw [if_pos h0]; exact h 0 h0
        · rw [if_neg h0]; exact Set.mem_univ _
      · rw [Set.mem_pi]
        intro j hj
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hj
        rw [Finset.mem_erase] at hm
        have hm0 : m ≠ 0 := hm.1
        have hmem : m ∈ s := hm.2
        have := h m hmem
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)]
        simpa only [mkSeq, if_neg hm0] using this
    · intro h
      rw [Set.mem_pi] at h
      obtain ⟨h1, h2⟩ := h
      intro n hn
      by_cases hn0 : n = 0
      · subst hn0
        by_cases h0 : 0 ∈ s
        · rw [if_pos h0] at h1; simpa [mkSeq] using h1
        · exact absurd hn h0
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have hmem : n - 1 ∈ (s.erase 0).image (fun m => m - 1) := by
          rw [Finset.mem_image]
          exact ⟨n, Finset.mem_erase.mpr ⟨hn0, hn⟩,
            Nat.sub_add_cancel hn1 ▸ rfl⟩
        have := h2 (n - 1) hmem
        rw [show n - 1 + 1 = n from Nat.sub_add_cancel hn1] at this
        simpa only [mkSeq, if_neg hn0] using this
  rw [hset, Measure.prod_prod]
  have hν : (Measure.infinitePi (fun _ : ℕ => μ))
      (Set.pi ((s.erase 0).image (fun m => m - 1)) (fun j => t (j + 1)))
      = ∏ m ∈ s.erase 0, μ (t m) := by
    rw [Measure.infinitePi_pi _ (fun j _ => ht (j + 1))]
    rw [Finset.prod_image ?_]
    · refine Finset.prod_congr rfl fun m hm => ?_
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Finset.mem_erase.mp hm).1)]
    · intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_erase] at hx hy
      have hx0 : x ≠ 0 := hx.1
      have hy0 : y ≠ 0 := hy.1
      have h' : x - 1 + 1 = y - 1 + 1 := congrArg (· + 1) hxy
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hx0),
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hy0)] at h'
      exact h'
  rw [hν]
  by_cases h0 : 0 ∈ s
  · rw [if_pos h0]
    exact Finset.mul_prod_erase s (fun i => μ (t i)) h0
  · rw [if_neg h0, Finset.erase_eq_of_notMem h0, measure_univ, one_mul]


theorem splitSeq_map {μ : Measure ℝ} [IsProbabilityMeasure μ] (k : ℕ) :
    ((Measure.pi (fun _ : Fin k => μ)).prod (Measure.infinitePi (fun _ : ℕ => μ))).map
        (splitSeq k)
      = Measure.infinitePi (fun _ : ℕ => μ) := by
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply (measurable_splitSeq k)
    (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  set s1 : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => (i : ℕ) ∈ s) with hs1
  set s2 : Finset ℕ := (s.filter (fun n => ¬ n < k)).image (fun n => n - k) with hs2
  have hset : splitSeq k ⁻¹' Set.pi s t
      = Set.pi (↑s1) (fun i : Fin k => t i) ×ˢ Set.pi (↑s2) (fun j : ℕ => t (j + k)) := by
    ext p
    rw [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Set.mem_pi, Set.mem_pi]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro i hi
        rw [Finset.mem_coe] at hi
        have hi' : (i : ℕ) ∈ s := by rw [hs1, Finset.mem_filter] at hi; exact hi.2
        have := h (i : ℕ) hi'
        rwa [splitSeq_apply_lt i.isLt] at this
      · intro j hj
        rw [Finset.mem_coe, hs2, Finset.mem_image] at hj
        obtain ⟨n, hn, rfl⟩ := hj
        rw [Finset.mem_filter] at hn
        have := h n hn.1
        rw [splitSeq_apply_ge hn.2] at this
        rw [Nat.sub_add_cancel (not_lt.mp hn.2)]
        exact this
    · rintro ⟨h1, h2⟩ n hn
      by_cases hnk : n < k
      · rw [splitSeq_apply_lt hnk]
        refine h1 ⟨n, hnk⟩ ?_
        rw [Finset.mem_coe, hs1, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hn⟩
      · rw [splitSeq_apply_ge hnk]
        have hm : n - k ∈ (↑s2 : Set ℕ) := by
          rw [Finset.mem_coe, hs2, Finset.mem_image]
          exact ⟨n, by rw [Finset.mem_filter]; exact ⟨hn, hnk⟩,
            Nat.sub_add_cancel (not_lt.mp hnk) ▸ rfl⟩
        have h2' := h2 (n - k) hm
        rwa [Nat.sub_add_cancel (not_lt.mp hnk)] at h2'
  rw [hset, Measure.prod_prod, Measure.pi_pi_finset,
    Measure.infinitePi_pi _ (fun j _ => ht (j + k))]
  have hAB : s1.image (fun i : Fin k => (i : ℕ)) = s.filter (fun n => n < k) := by
    ext n
    rw [Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [hs1, Finset.mem_filter] at hi
      exact Finset.mem_filter.mpr ⟨hi.2, i.isLt⟩
    · intro hn
      rw [Finset.mem_filter] at hn
      exact ⟨⟨n, hn.2⟩, by rw [hs1, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hn.1⟩, rfl⟩
  have h1 : ∏ i ∈ s1, μ (t i) = ∏ n ∈ s.filter (fun n => n < k), μ (t n) := by
    rw [← Finset.prod_image (s := s1) (f := fun n : ℕ => μ (t n)) ?_]
    · rw [hAB]
    · intro x _ y _ hxy
      exact Fin.ext hxy
  have hinj2 : Set.InjOn (fun n : ℕ => n - k) ↑(s.filter (fun n => ¬ n < k)) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    have hx1 : k ≤ x := not_lt.mp hx.2
    have hy1 : k ≤ y := not_lt.mp hy.2
    have h' : x - k + k = y - k + k := congrArg (· + k) hxy
    rwa [Nat.sub_add_cancel hx1, Nat.sub_add_cancel hy1] at h'
  have h2 : ∏ j ∈ s2, μ (t (j + k)) = ∏ n ∈ s.filter (fun n => ¬ n < k), μ (t n) := by
    rw [hs2, Finset.prod_image (s := s.filter (fun n => ¬ n < k))
      (f := fun n : ℕ => μ (t (n + k))) hinj2]
    refine Finset.prod_congr rfl fun n hn => ?_
    rw [Nat.sub_add_cancel (not_lt.mp (Finset.mem_filter.mp hn).2)]
  rw [h1, h2, Finset.prod_filter_mul_prod_filter_not s (fun n => n < k) (fun n => μ (t n))]


/-- Measure of the image of a set under the cons map. -/
lemma mkSeq_image_measure {μ : Measure ℝ} [IsProbabilityMeasure μ] (S : Set (ℝ × (ℕ → ℝ)))
    (hS : MeasurableSet S) :
    Measure.infinitePi (fun _ : ℕ => μ) (mkSeq '' S)
      = (μ.prod (Measure.infinitePi (fun _ : ℕ => μ))) S := by
  have himg : mkSeq '' S = unSeq ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      simpa only [Set.mem_preimage, unSeq_mkSeq] using hp
    · intro hx; exact ⟨unSeq x, hx, mkSeq_unSeq x⟩
  have hmap : Measure.infinitePi (fun _ : ℕ => μ)
      = (μ.prod (Measure.infinitePi (fun _ : ℕ => μ))).map mkSeq :=
    (mkSeq_map (μ := μ)).symm
  have hpre : mkSeq ⁻¹' (unSeq ⁻¹' S) = S := by
    ext p
    simp only [Set.mem_preimage, unSeq_mkSeq]
  conv_lhs => rw [hmap]
  rw [himg, Measure.map_apply measurable_mkSeq (hS.preimage measurable_unSeq), hpre]

theorem ae_divergence {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : HasExpLaw μ) (t : ℝ) :
    Measure.infinitePi (fun _ : ℕ => μ) {x : ℕ → ℝ | ∀ k, Tf k x ≤ t} = 0 := by
  have hIci : μ (Set.Ici 0) = 1 := by
    have hset : Set.Ici (0:ℝ) = Set.Ioi 0 ∪ {0} := by
      ext x
      simp only [Set.mem_Ici, Set.mem_union, Set.mem_Ioi, Set.mem_singleton_iff]
      constructor
      · intro hx
        rcases eq_or_lt_of_le hx with h | h
        · exact Or.inr h.symm
        · exact Or.inl h
      · rintro (h | h)
        · exact le_of_lt h
        · rw [h]
    rw [hset, measure_union ?_ (measurableSet_singleton 0), hμ.Ioi_zero, hμ.singleton_zero,
      add_zero]
    rw [Set.disjoint_left]
    rintro x hx hy
    simp only [Set.mem_Ioi] at hx
    simp only [Set.mem_singleton_iff] at hy
    linarith
  -- The event that all coordinates are `≤ t` has measure zero.
  have hC : Measure.infinitePi (fun _ : ℕ => μ) {x : ℕ → ℝ | ∀ k, x k ≤ t} = 0 := by
    set C : Set (ℕ → ℝ) := {x : ℕ → ℝ | ∀ k, x k ≤ t} with hCdef
    have hfix : C = mkSeq '' (Set.Iic t ×ˢ C) := by
      rw [hCdef]
      ext x
      constructor
      · intro hx
        refine ⟨unSeq x, ⟨?_, ?_⟩, mkSeq_unSeq x⟩
        · simpa [unSeq] using hx 0
        · intro k
          simpa [unSeq] using hx (k+1)
      · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
        intro k
        cases k with
        | zero => simpa using hp1
        | succ k => simpa using hp2 k
    have hmeasC : MeasurableSet C := by
      rw [hCdef]
      rw [show {x : ℕ → ℝ | ∀ k, x k ≤ t} = ⋂ k, {x : ℕ → ℝ | x k ≤ t} from by ext; simp]
      exact MeasurableSet.iInter fun k => measurableSet_Iic.preimage (measurable_pi_apply k)
    have hval : Measure.infinitePi (fun _ : ℕ => μ) C
        = μ (Set.Iic t) * Measure.infinitePi (fun _ : ℕ => μ) C := by
      conv_lhs => rw [hfix]
      rw [mkSeq_image_measure _ ((measurableSet_Iic).prod hmeasC), Measure.prod_prod]
    have hne_top : Measure.infinitePi (fun _ : ℕ => μ) C ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
    have hrt : (Measure.infinitePi (fun _ : ℕ => μ) C).toReal
        = (μ (Set.Iic t)).toReal * (Measure.infinitePi (fun _ : ℕ => μ) C).toReal := by
      conv_lhs => rw [hval]
      rw [ENNReal.toReal_mul]
    have ha_lt : (μ (Set.Iic t)).toReal < 1 := by
      rw [hμ t]
      rcases le_or_gt 0 t with ht | ht
      · rw [ENNReal.toReal_ofReal (by
          have : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
          linarith)]
        linarith [Real.exp_pos (-t)]
      · have hneg : 1 - Real.exp (-t) ≤ 0 := by
          have : 1 < Real.exp (-t) := by rw [Real.one_lt_exp_iff]; linarith
          linarith
        rw [ENNReal.ofReal_of_nonpos hneg, ENNReal.toReal_zero]
        norm_num
    have hx0 : (Measure.infinitePi (fun _ : ℕ => μ) C).toReal = 0 := by
      have h1 : (1 - (μ (Set.Iic t)).toReal)
          * (Measure.infinitePi (fun _ : ℕ => μ) C).toReal = 0 := by
        rw [sub_mul, one_mul, ← hrt, sub_self]
      have h2 : (1 : ℝ) - (μ (Set.Iic t)).toReal ≠ 0 := by linarith
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h h2
      · exact h
    rw [ENNReal.toReal_eq_zero_iff] at hx0
    rcases hx0 with h | h
    · exact h
    · exact absurd h hne_top
  -- Reduce the `Tf` event to `C` on the a.e. set of nonnegative sequences.
  have hBmeas : MeasurableSet {x : ℕ → ℝ | ∀ i, 0 ≤ x i} := by
    rw [show {x : ℕ → ℝ | ∀ i, 0 ≤ x i} = Set.univ.pi (fun _ : ℕ => Set.Ici (0:ℝ)) from by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ici]]
    exact MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ici
  have hB : Measure.infinitePi (fun _ : ℕ => μ) {x : ℕ → ℝ | ∀ i, 0 ≤ x i} = 1 := by
    have hset : {x : ℕ → ℝ | ∀ i, 0 ≤ x i} = Set.univ.pi (fun _ : ℕ => Set.Ici (0:ℝ)) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ici]
    rw [hset, Measure.infinitePi_pi_univ (fun _ : ℕ => μ) (fun _ => measurableSet_Ici)]
    simp only [hIci]
    exact tprod_one
  have hBc : Measure.infinitePi (fun _ : ℕ => μ) {x : ℕ → ℝ | ∀ i, 0 ≤ x i}ᶜ = 0 := by
    rw [measure_compl hBmeas (by rw [hB]; exact ENNReal.one_ne_top), measure_univ, hB,
      tsub_self]
  refine le_antisymm ?_ (by simp)
  calc Measure.infinitePi (fun _ : ℕ => μ) {x : ℕ → ℝ | ∀ k, Tf k x ≤ t}
      ≤ Measure.infinitePi (fun _ : ℕ => μ)
          ({x : ℕ → ℝ | ∀ i, 0 ≤ x i}ᶜ ∪ {x : ℕ → ℝ | ∀ k, x k ≤ t}) := by
        refine measure_mono fun x hx => ?_
        by_cases hxn : ∀ i, 0 ≤ x i
        · refine Or.inr fun k => ?_
          have h1 := hx (k+1)
          have h2 : 0 ≤ Tf k x := Finset.sum_nonneg fun i _ => hxn i
          rw [Tf_succ] at h1
          linarith
        · exact Or.inl hxn
    _ ≤ Measure.infinitePi (fun _ : ℕ => μ) {x : ℕ → ℝ | ∀ i, 0 ≤ x i}ᶜ
          + Measure.infinitePi (fun _ : ℕ => μ) {x : ℕ → ℝ | ∀ k, x k ≤ t} :=
        measure_union_le _ _
    _ = 0 := by rw [hBc, hC, add_zero]

