import Mathlib
import Submission.Commons.Analysis.TensorApprox.exists_tensor_localization
import Submission.Commons.Analysis.Calculus.exists_contDiff_partition_unity

namespace Commons.Analysis.TensorApprox

open scoped BigOperators
open Finset

/-- Strengthened localised tensor approximation.  A continuous compactly supported `g` on
`Fin k → ℝ` whose support lies in the orthant and in `{∑ i, t i ≤ R}` is uniformly
approximated by a finite tensor sum `∑ j, c j * ∏ i, h j i (t i)` whose one-variable
components `h j i` are smooth, compactly supported, vanish for `u > β j i`, with every
individual `β j i ≤ R + 12 * k * η` and `∑ i, β j i ≤ R + 12 * k * η`. -/
theorem exists_tensor_localization_box {k : ℕ} {g : (Fin k → ℝ) → ℝ} (hg : Continuous g)
    (hcs : HasCompactSupport g) {R : ℝ}
    (hR : ∀ t, g t ≠ 0 → (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ R)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℝ) (β : ι → Fin k → ℝ) (h : ι → Fin k → ℝ → ℝ),
      (∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (h j i)) ∧
      (∀ j i, HasCompactSupport (h j i)) ∧
      (∀ j i u, β j i < u → h j i u = 0) ∧
      (∀ j i u, u < -(12 * η) → h j i u = 0) ∧
      (∀ j i, β j i ≤ R + 12 * (k : ℝ) * η) ∧
      (∀ j, ∑ i, β j i ≤ R + 12 * (k : ℝ) * η) ∧
      (∀ t, |g t - ∑ j, c j * ∏ i, h j i (t i)| < ε) := by
  classical
  by_cases hgzero : ∀ t, g t = 0
  · -- The zero function: use the empty index.
    refine ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, PEmpty.elim,
      fun j => j.elim, fun j => j.elim, fun j => j.elim, fun j => j.elim,
      fun j => j.elim, fun j => j.elim, ?_⟩
    intro t
    rw [hgzero t]
    have hsum0 : (∑ j : PEmpty, (PEmpty.elim : PEmpty → ℝ) j *
        ∏ i, (PEmpty.elim : PEmpty → Fin k → ℝ → ℝ) j i (t i)) = 0 := by simp
    rw [hsum0]
    simp only [sub_zero, abs_zero]
    exact hε
  · push Not at hgzero
    obtain ⟨t₀, ht₀⟩ := hgzero
    have hR0 : 0 ≤ R := by
      obtain ⟨h1, h2⟩ := hR t₀ ht₀
      have h3 : 0 ≤ ∑ i, t₀ i := Finset.sum_nonneg (fun i _ => h1 i)
      linarith
    have hε2 : 0 < ε / 2 := by linarith
    have hu : UniformContinuous g :=
      hg.uniformContinuous_of_tendsto_cocompact hcs.is_zero_at_infty
    obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuous_iff.mp hu (ε / 2) hε2
    obtain ⟨C, hC⟩ : ∃ C : ℝ, Function.support g ⊆ Metric.closedBall (0 : Fin k → ℝ) C := by
      have hbdd : Bornology.IsBounded (tsupport g) :=
        (show IsCompact (tsupport g) from hcs).isBounded
      obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin k → ℝ)).1 hbdd
      exact ⟨C, Set.Subset.trans (subset_tsupport g) hC⟩
    have hC0 : 0 ≤ C := by
      have h1 : t₀ ∈ Metric.closedBall (0 : Fin k → ℝ) C := hC ht₀
      rw [Metric.mem_closedBall] at h1
      have h2 : (0 : ℝ) ≤ dist t₀ (0 : Fin k → ℝ) := dist_nonneg
      linarith
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
    -- A vanishing helper for `ψ₀`.
    have hvanψ : ∀ (a : ℤ) (y : ℝ), (a : ℝ) + 1 < y → ψ₀ a y = 0 := by
      intro a y hy
      by_contra h
      have := hψsupp a h
      rw [Set.mem_Icc] at this
      linarith [this.2]
    -- Box size.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, C / σ + 2 ≤ (N : ℝ) := exists_nat_ge (C / σ + 2)
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
      have : 0 ≤ C / σ := div_nonneg hC0 hσpos.le
      linarith
    have hNi : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN1
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
    -- The one-sided box and the localisation constraint.
    set B : Finset (Fin k → ℤ) :=
      Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(1 : ℤ)) (N : ℤ)) with hB
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
      have htR : ∑ i, t i ≤ R := (hR t ht).2
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
    -- The full one-sided box sum equals `1` on the support.
    have hsum_eq_one : ∀ t ∈ Function.support g,
        (∑ m ∈ B, (∏ i, ψ₀ (m i) (t i / σ))) = 1 := by
      intro t ht
      have hor : ∀ i, 0 ≤ t i := (hR t ht).1
      have hsub : B ⊆ Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
        intro m hm
        rw [hB, Fintype.mem_piFinset] at hm
        rw [Fintype.mem_piFinset]
        intro i
        have h2 := hm i
        rw [Finset.mem_Icc] at h2 ⊢
        constructor <;> omega
      have hzero : ∀ m ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(N : ℤ)) (N : ℤ)),
          m ∉ B → (∏ i, ψ₀ (m i) (t i / σ)) = 0 := by
        intro m hmBig hmB
        have hex : ∃ i, m i ∉ Finset.Icc (-(1 : ℤ)) (N : ℤ) := by
          by_contra h
          push Not at h
          exact hmB (by rw [hB, Fintype.mem_piFinset]; exact h)
        obtain ⟨i, hi⟩ := hex
        have hmiBig : m i ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
          rw [Fintype.mem_piFinset] at hmBig; exact hmBig i
        have hnot : ¬ ((-(1 : ℤ)) ≤ m i) := by
          intro h'
          exact hi (Finset.mem_Icc.mpr ⟨h', (Finset.mem_Icc.mp hmiBig).2⟩)
        have hle2 : (m i : ℤ) ≤ -2 := by omega
        have hcast : (m i : ℝ) + 1 < t i / σ := by
          have hti : (0 : ℝ) ≤ t i := hor i
          have hc : (m i : ℝ) ≤ -2 := by exact_mod_cast hle2
          have : (0 : ℝ) ≤ t i / σ := div_nonneg hti hσpos.le
          linarith
        exact Finset.prod_eq_zero (Finset.mem_univ i) (hvanψ (m i) (t i / σ) hcast)
      calc (∑ m ∈ B, (∏ i, ψ₀ (m i) (t i / σ)))
          = ∑ m ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(N : ℤ)) (N : ℤ)),
              (∏ i, ψ₀ (m i) (t i / σ)) := Finset.sum_subset hsub hzero
        _ = 1 := tensor_box_eq_one hψsupp hψsum hσpos (hNle t ht)
    -- The restricted sum is at most `1` everywhere.
    have hWle : ∀ t : Fin k → ℝ, (∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ))) ≤ 1 := by
      intro t
      calc (∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ)))
          = ∑ m ∈ S, (∏ i, ψ₀ (m i) (t i / σ)) :=
            Finset.sum_coe_sort S (fun m => ∏ i, ψ₀ (m i) (t i / σ))
        _ ≤ ∑ m ∈ B, (∏ i, ψ₀ (m i) (t i / σ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun m _ _ => Finset.prod_nonneg (fun i _ => hψnn _ _))
        _ = ∏ i, ∑ m ∈ Finset.Icc (-(1 : ℤ)) (N : ℤ), ψ₀ m (t i / σ) := by
            rw [hB, Finset.sum_prod_piFinset (Finset.Icc (-(1 : ℤ)) (N : ℤ))
              (g := fun (i : Fin k) (j : ℤ) => ψ₀ j (t i / σ))]
        _ ≤ ∏ i, (1 : ℝ) := by
            refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg (fun m _ => hψnn _ _))
              (fun i _ => ?_)
            have hsub2 : Finset.Icc (-(1 : ℤ)) (N : ℤ) ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
              intro m hm
              rw [Finset.mem_Icc] at hm ⊢
              constructor <;> omega
            exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub2
                (fun m _ _ => hψnn m _))
              (sum_Icc_partition_le_one hψsum hψnn N (t i / σ))
        _ = 1 := Finset.prod_const_one
    -- The restricted sum equals `1` on the support.
    have hW1 : ∀ t ∈ Function.support g,
        (∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ))) = 1 := by
      intro t ht
      calc (∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ)))
          = ∑ m ∈ S, (∏ i, ψ₀ (m i) (t i / σ)) :=
            Finset.sum_coe_sort S (fun m => ∏ i, ψ₀ (m i) (t i / σ))
        _ = ∑ m ∈ B, (∏ i, ψ₀ (m i) (t i / σ)) := by
            refine Finset.sum_subset (Finset.filter_subset _ _) ?_
            intro m hmB hmS
            exact hvanish m t ht hmB hmS
        _ = 1 := hsum_eq_one t ht
    -- The `β`-sum bound and nonnegativity.
    have hβnonneg : ∀ (m : ↥S) (i : Fin k), 0 ≤ ((m.1 i : ℤ) : ℝ) * σ + σ := by
      intro m i
      have hmB : m.1 ∈ B := (Finset.mem_filter.mp m.2).1
      rw [hB, Fintype.mem_piFinset] at hmB
      have hmi := Finset.mem_Icc.mp (hmB i)
      have hcast : (-1 : ℝ) ≤ ((m.1 i : ℤ) : ℝ) := by exact_mod_cast hmi.1
      nlinarith [hσpos]
    have hβsum : ∀ (m : ↥S), (∑ i, (((m.1 i : ℤ) : ℝ) * σ + σ)) ≤ R + 6 * (k : ℝ) * η := by
      intro m
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
    -- Assembly.
    refine ⟨↥S, inferInstance, fun (m : ↥S) => g (fun i => ((m.1 i : ℤ) : ℝ) * σ),
      fun (m : ↥S) (i : Fin k) => ((m.1 i : ℤ) : ℝ) * σ + σ,
      fun (m : ↥S) (i : Fin k) => fun u : ℝ => ψ₀ (m.1 i) (u / σ), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · intro m i u hu
      have hmB : m.1 ∈ B := (Finset.mem_filter.mp m.2).1
      rw [hB, Fintype.mem_piFinset] at hmB
      have hmi := Finset.mem_Icc.mp (hmB i)
      have hmi' : (-1 : ℝ) ≤ ((m.1 i : ℤ) : ℝ) := by exact_mod_cast hmi.1
      have h1 : u / σ ∉ Function.support (ψ₀ (m.1 i)) := by
        intro hmem
        have h2 := hψsupp (m.1 i) hmem
        rw [Set.mem_Icc] at h2
        have hlt : u / σ < -12 := by
          rw [div_lt_iff₀ hσpos]
          linarith [hu, hσleη]
        linarith [h2.1, hmi', hlt]
      exact Function.notMem_support.mp h1
    · intro m i
      have h1 : ((m.1 i : ℤ) : ℝ) * σ + σ ≤ ∑ i', (((m.1 i' : ℤ) : ℝ) * σ + σ) :=
        Finset.single_le_sum (fun i' _ => hβnonneg m i') (Finset.mem_univ i)
      have h2 := hβsum m
      have h3 : 6 * (k : ℝ) * η ≤ 12 * (k : ℝ) * η := by
        have : (0 : ℝ) ≤ 6 * (k : ℝ) * η := by positivity
        linarith
      linarith
    · intro m
      have h2 := hβsum m
      have h3 : 6 * (k : ℝ) * η ≤ 12 * (k : ℝ) * η := by
        have : (0 : ℝ) ≤ 6 * (k : ℝ) * η := by positivity
        linarith
      linarith
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
            exact mul_le_mul_of_nonneg_left hcont.le (Finset.prod_nonneg (fun i _ => hψnn _ _))
        calc |g t - ∑ m : ↥S, g (fun i => ((m.1 i : ℤ) : ℝ) * σ) *
                (∏ i, ψ₀ (m.1 i) (t i / σ))|
            = |∑ m : ↥S, g (fun i => ((m.1 i : ℤ) : ℝ) * σ) *
                (∏ i, ψ₀ (m.1 i) (t i / σ))| := by rw [ht, zero_sub, abs_neg]
          _ ≤ ∑ m : ↥S, |g (fun i => ((m.1 i : ℤ) : ℝ) * σ) *
                (∏ i, ψ₀ (m.1 i) (t i / σ))| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ)) *
                |g (fun i => ((m.1 i : ℤ) : ℝ) * σ)| := by
              refine Finset.sum_congr rfl (fun m _ => ?_)
              rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg (fun i _ => hψnn _ _)), mul_comm]
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
            exact mul_le_mul_of_nonneg_left hcont.le (Finset.prod_nonneg (fun i _ => hψnn _ _))
        calc |∑ m : ↥S, (g t - g (fun i => ((m.1 i : ℤ) : ℝ) * σ)) *
                (∏ i, ψ₀ (m.1 i) (t i / σ))|
            ≤ ∑ m : ↥S, |(g t - g (fun i => ((m.1 i : ℤ) : ℝ) * σ)) *
                (∏ i, ψ₀ (m.1 i) (t i / σ))| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ)) *
                |g t - g (fun i => ((m.1 i : ℤ) : ℝ) * σ)| := by
              refine Finset.sum_congr rfl (fun m _ => ?_)
              rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg (fun i _ => hψnn _ _)), mul_comm]
          _ ≤ ∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ)) * (ε / 2) :=
              Finset.sum_le_sum (fun m _ => hb m)
          _ = (∑ m : ↥S, (∏ i, ψ₀ (m.1 i) (t i / σ))) * (ε / 2) :=
              (Finset.sum_mul _ _ _).symm
          _ = ε / 2 := by rw [hW1t, one_mul]
          _ < ε := by linarith

end Commons.Analysis.TensorApprox
