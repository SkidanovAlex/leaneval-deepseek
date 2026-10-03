import Mathlib
import Submission.Work.Parab.coordData.card_filter_abs_lt
import Submission.Work.Parab.coordData.tail_log_sum_bound

namespace Work.Parab.coordData

/-- The summand of `sum_log_inv_bound`, as a function of `t = x + j`. -/
private noncomputable def term (η : ℝ) (t : ℝ) : ℝ := (1 + Real.log (2 + |t|)) / (t ^ 2 + η ^ 2)

private lemma term_nonneg {η : ℝ} (t : ℝ) : 0 ≤ term η t := by
  rw [term]
  apply div_nonneg
  · have h : (1 : ℝ) ≤ 2 + |t| := by have := abs_nonneg t; linarith
    linarith [Real.log_nonneg h]
  · positivity

private lemma term_neg (η : ℝ) (t : ℝ) : term η (-t) = term η t := by
  rw [term, term, abs_neg, neg_sq]

/-- Elementary comparison of `(1 + log (3 + t))/t` with `2 (1 + log (2 + s))/s` for `1 ≤ s ≤ t`. -/
private lemma log_ratio_le {t s : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) :
    (1 + Real.log (3 + t)) / t ≤ 2 * (1 + Real.log (2 + s)) / s := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hs3 : 0 < 3 + s := by linarith
  have hlog3s : 0 ≤ Real.log (3 + s) := Real.log_nonneg (by linarith)
  have step1 : (1 + Real.log (3 + t)) / t ≤ (1 + Real.log (3 + s)) / s := by
    rw [div_le_div_iff₀ ht0 hs0]
    have hts : 0 ≤ t - s := by linarith
    have hlog : Real.log ((3 + t) / (3 + s)) ≤ (t - s) / (3 + s) := by
      have h := Real.log_le_sub_one_of_pos (show 0 < (3 + t) / (3 + s) by positivity)
      have he : (3 + t) / (3 + s) - 1 = (t - s) / (3 + s) := by field_simp; ring
      linarith [he]
    have h1 : s * Real.log ((3 + t) / (3 + s)) ≤ s * ((t - s) / (3 + s)) :=
      mul_le_mul_of_nonneg_left hlog (le_of_lt hs0)
    have h2 : s * ((t - s) / (3 + s)) ≤ (t - s) * (1 + Real.log (3 + s)) := by
      have h3 : s / (3 + s) ≤ 1 := by rw [div_le_one hs3]; linarith
      have h4 : s * ((t - s) / (3 + s)) = (t - s) * (s / (3 + s)) := by field_simp
      rw [h4]
      have h5 : (t - s) * (s / (3 + s)) ≤ (t - s) * 1 := mul_le_mul_of_nonneg_left h3 hts
      have h6 : (t - s) * 1 ≤ (t - s) * (1 + Real.log (3 + s)) :=
        mul_le_mul_of_nonneg_left (by linarith) hts
      linarith
    have hkey : s * Real.log ((3 + t) / (3 + s)) ≤ (t - s) * (1 + Real.log (3 + s)) :=
      le_trans h1 h2
    have hsplit : s * Real.log (3 + t) - t * Real.log (3 + s)
        = s * Real.log ((3 + t) / (3 + s)) - (t - s) * Real.log (3 + s) := by
      rw [Real.log_div (by linarith) (by linarith)]
      ring
    have h7 : s * Real.log (3 + t) - t * Real.log (3 + s) ≤ t - s := by
      rw [hsplit]; linarith [hkey]
    linarith [h7]
  have hlog3t : 1 + Real.log (3 + s) ≤ 2 * (1 + Real.log (2 + s)) := by
    have hlog2s' : 0 ≤ Real.log (2 + s) := Real.log_nonneg (by linarith)
    have h1 : 3 + s ≤ 2 * (2 + s) := by linarith
    have h2 := Real.log_le_log (by linarith : (0 : ℝ) < 3 + s) h1
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : 2 + s ≠ 0)] at h2
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    linarith
  calc (1 + Real.log (3 + t)) / t ≤ (1 + Real.log (3 + s)) / s := step1
    _ = (1 + Real.log (3 + s)) * (1 / s) := by ring
    _ ≤ (2 * (1 + Real.log (2 + s))) * (1 / s) :=
        mul_le_mul_of_nonneg_right hlog3t (by positivity)
    _ = 2 * (1 + Real.log (2 + s)) / s := by ring

theorem sum_log_inv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x η : ℝ, 1 ≤ η → ∀ k : ℕ,
      ∑ j ∈ Finset.range k,
          (1 + Real.log (2 + |x + (j : ℝ)|)) / ((x + (j : ℝ)) ^ 2 + η ^ 2)
        ≤ C * (1 + Real.log (2 + η)) / η := by
  refine ⟨22, by norm_num, ?_⟩
  intro x η hη k
  have hηpos : 0 < η := by linarith
  have hlog0 : 0 ≤ Real.log (2 + η) := Real.log_nonneg (by linarith)
  have hL0 : 0 ≤ 1 + Real.log (2 + η) := by linarith
  have hA0 : 0 ≤ 1 + Real.log (3 + η) := by
    have h : (1 : ℝ) ≤ 3 + η := by linarith
    linarith [Real.log_nonneg h]
  set r : ℝ := η + 1 with hr
  have hr1 : 1 ≤ r := by rw [hr]; linarith
  have hrpos : 0 < r := by linarith
  set M : Finset ℕ := (Finset.range k).filter (fun j : ℕ => |x + (j : ℝ)| < r) with hM
  set U : Finset ℕ := (Finset.range k).filter (fun j : ℕ => r ≤ x + (j : ℝ)) with hU
  set L : Finset ℕ := (Finset.range k).filter (fun j : ℕ => x + (j : ℝ) ≤ -r) with hL
  have hSdef : ∑ j ∈ Finset.range k,
        (1 + Real.log (2 + |x + (j : ℝ)|)) / ((x + (j : ℝ)) ^ 2 + η ^ 2)
      = ∑ j ∈ Finset.range k, term η (x + (j : ℝ)) :=
    Finset.sum_congr rfl (fun j _ => by rw [term])
  have hcover : Finset.range k = M ∪ (U ∪ L) := by
    rw [hM, hU, hL]
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hj
      by_cases h1 : |x + (j : ℝ)| < r
      · exact Or.inl ⟨hj, h1⟩
      · simp only [not_lt] at h1
        by_cases h2 : r ≤ x + (j : ℝ)
        · exact Or.inr (Or.inl ⟨hj, h2⟩)
        · simp only [not_le] at h2
          refine Or.inr (Or.inr ⟨hj, ?_⟩)
          rcases le_or_gt 0 (x + (j : ℝ)) with h3 | h3
          · rw [abs_of_nonneg h3] at h1; linarith
          · rw [abs_of_neg h3] at h1; linarith
    · rintro (⟨hj, _⟩ | ⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
  have hdisj1 : Disjoint M (U ∪ L) := by
    rw [Finset.disjoint_left]
    intro j hj hju
    rw [Finset.mem_union] at hju
    rcases hju with hju | hju
    · rw [hM] at hj; rw [hU] at hju
      have h1 := (Finset.mem_filter.mp hj).2
      have h2 := (Finset.mem_filter.mp hju).2
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x + (j : ℝ))] at h1
      linarith
    · rw [hM] at hj; rw [hL] at hju
      have h1 := (Finset.mem_filter.mp hj).2
      have h2 := (Finset.mem_filter.mp hju).2
      rw [abs_of_neg (by linarith : x + (j : ℝ) < 0)] at h1
      linarith
  have hdisj2 : Disjoint U L := by
    rw [Finset.disjoint_left]
    intro j hu hl
    rw [hU] at hu; rw [hL] at hl
    have h1 := (Finset.mem_filter.mp hu).2
    have h2 := (Finset.mem_filter.mp hl).2
    linarith
  have hsplit : ∑ j ∈ Finset.range k, term η (x + (j : ℝ))
      = ∑ j ∈ M, term η (x + (j : ℝ))
        + (∑ j ∈ U, term η (x + (j : ℝ)) + ∑ j ∈ L, term η (x + (j : ℝ))) := by
    rw [hcover, Finset.sum_union hdisj1, Finset.sum_union hdisj2]
  -- middle block
  have hMbound : ∑ j ∈ M, term η (x + (j : ℝ)) ≤ 10 * (1 + Real.log (2 + η)) / η := by
    have hterm : ∀ j ∈ M, term η (x + (j : ℝ)) ≤ (1 + Real.log (3 + η)) / η ^ 2 := by
      intro j hj
      have hj2 : |x + (j : ℝ)| < r := by
        rw [hM] at hj
        exact (Finset.mem_filter.mp hj).2
      have hnum : 1 + Real.log (2 + |x + (j : ℝ)|) ≤ 1 + Real.log (3 + η) := by
        have harg : 2 + |x + (j : ℝ)| ≤ 3 + η := by
          have h := hj2
          rw [hr] at h
          linarith [le_abs_self (x + (j : ℝ))]
        have hpos : 0 < 2 + |x + (j : ℝ)| := by positivity
        linarith [Real.log_le_log hpos harg]
      have hdenle : η ^ 2 ≤ (x + (j : ℝ)) ^ 2 + η ^ 2 := by
        have := sq_nonneg (x + (j : ℝ)); linarith
      have hdenpos : 0 < (x + (j : ℝ)) ^ 2 + η ^ 2 := by positivity
      rw [term]
      calc (1 + Real.log (2 + |x + (j : ℝ)|)) / ((x + (j : ℝ)) ^ 2 + η ^ 2)
          ≤ (1 + Real.log (3 + η)) / ((x + (j : ℝ)) ^ 2 + η ^ 2) :=
            div_le_div_of_nonneg_right hnum (le_of_lt hdenpos)
        _ ≤ (1 + Real.log (3 + η)) / η ^ 2 :=
            div_le_div_of_nonneg_left hA0 (by positivity) hdenle
    calc ∑ j ∈ M, term η (x + (j : ℝ))
        ≤ ∑ j ∈ M, (1 + Real.log (3 + η)) / η ^ 2 := Finset.sum_le_sum hterm
      _ = (M.card : ℝ) * ((1 + Real.log (3 + η)) / η ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * η + 3) * ((1 + Real.log (3 + η)) / η ^ 2) := by
            have hcard : (M.card : ℝ) ≤ 2 * η + 3 := by
              have h := card_filter_abs_lt x r hrpos k
              rw [hr] at h
              linarith
            exact mul_le_mul_of_nonneg_right hcard (div_nonneg hA0 (by positivity))
      _ ≤ 10 * (1 + Real.log (2 + η)) / η := by
            have hA : 1 + Real.log (3 + η) ≤ 2 * (1 + Real.log (2 + η)) := by
              have h1 : 3 + η ≤ 2 * (2 + η) := by linarith
              have h2 := Real.log_le_log (by linarith : (0 : ℝ) < 3 + η) h1
              rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : 2 + η ≠ 0)] at h2
              have h3 : Real.log 2 ≤ 1 := by
                have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
              linarith
            have hstep1 : (2 * η + 3) * ((1 + Real.log (3 + η)) / η ^ 2)
                ≤ (2 * η + 3) * (2 * (1 + Real.log (2 + η)) / η ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ (by linarith)
              exact div_le_div_of_nonneg_right hA (by positivity)
            have hstep2 : 2 * (2 * η + 3) * (1 + Real.log (2 + η)) / η ^ 2
                ≤ 10 * (1 + Real.log (2 + η)) / η := by
              rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < η ^ 2) hηpos]
              have hfac : 2 * (2 * η + 3) ≤ 10 * η := by linarith
              have hXn : 0 ≤ (1 + Real.log (2 + η)) * η := mul_nonneg hL0 (le_of_lt hηpos)
              calc 2 * (2 * η + 3) * (1 + Real.log (2 + η)) * η
                  = (2 * (2 * η + 3)) * ((1 + Real.log (2 + η)) * η) := by ring
                _ ≤ (10 * η) * ((1 + Real.log (2 + η)) * η) :=
                    mul_le_mul_of_nonneg_right hfac hXn
                _ = 10 * (1 + Real.log (2 + η)) * η ^ 2 := by ring
            calc (2 * η + 3) * ((1 + Real.log (3 + η)) / η ^ 2)
                ≤ (2 * η + 3) * (2 * (1 + Real.log (2 + η)) / η ^ 2) := hstep1
              _ = 2 * (2 * η + 3) * (1 + Real.log (2 + η)) / η ^ 2 := by ring
              _ ≤ 10 * (1 + Real.log (2 + η)) / η := hstep2
  -- upper block
  have hUbound : ∑ j ∈ U, term η (x + (j : ℝ)) ≤ 6 * (1 + Real.log (2 + η)) / η := by
    rcases Finset.eq_empty_or_nonempty U with hUe | hUne
    · rw [hUe, Finset.sum_empty]
      exact div_nonneg (by linarith [hL0]) (le_of_lt hηpos)
    · set j0 : ℕ := U.min' hUne with hj0
      have hmin : j0 ∈ U := by rw [hj0]; exact Finset.min'_mem U hUne
      have hminle : ∀ j ∈ U, j0 ≤ j := by
        intro j hj
        rw [hj0]
        exact Finset.min'_le U j hj
      have ha_ge : r ≤ x + (j0 : ℝ) := by
        rw [hU] at hmin
        exact (Finset.mem_filter.mp hmin).2
      have hle : η ≤ x + (j0 : ℝ) := by rw [hr] at ha_ge; linarith
      have ha1 : 1 ≤ x + (j0 : ℝ) := by linarith
      have hinj : Set.InjOn (fun j : ℕ => j - j0) ↑U := by
        intro j hj j' hj' heq
        have h1 : j0 ≤ j := hminle j hj
        have h2 : j0 ≤ j' := hminle j' hj'
        have hsubeq : j - j0 = j' - j0 := heq
        have key : j0 + (j - j0) = j0 + (j' - j0) := by rw [hsubeq]
        rwa [Nat.add_sub_cancel' h1, Nat.add_sub_cancel' h2] at key
      have hstep : ∑ j ∈ U, term η (x + (j : ℝ))
          = ∑ i ∈ U.image (fun j : ℕ => j - j0), term η ((x + (j0 : ℝ)) + (i : ℝ)) := by
        rw [Finset.sum_image hinj]
        exact Finset.sum_congr rfl (fun j hj => by
          have h1 : j0 ≤ j := hminle j hj
          have hcast : ((j - j0 : ℕ) : ℝ) = (j : ℝ) - (j0 : ℝ) := Nat.cast_sub h1
          congr 1
          rw [hcast]; ring)
      have hsub : U.image (fun j : ℕ => j - j0) ⊆ Finset.range k := by
        intro i hi
        rw [Finset.mem_image] at hi
        obtain ⟨j, hj, rfl⟩ := hi
        rw [Finset.mem_range]
        rw [hU] at hj
        exact lt_of_le_of_lt (Nat.sub_le j j0) (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
      have htail := tail_log_sum_bound (a := x + (j0 : ℝ)) (η := η) (N := k) ha1
      have htail' : ∑ i ∈ Finset.range k, term η ((x + (j0 : ℝ)) + (i : ℝ))
          ≤ 3 * (1 + Real.log (3 + (x + (j0 : ℝ)))) / (x + (j0 : ℝ)) := by
        have heq : ∀ i : ℕ, term η ((x + (j0 : ℝ)) + (i : ℝ))
            = (1 + Real.log (2 + ((x + (j0 : ℝ)) + (i : ℝ))))
                / (((x + (j0 : ℝ)) + (i : ℝ)) ^ 2 + η ^ 2) := by
          intro i
          rw [term, abs_of_nonneg (by have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i; linarith)]
        rw [Finset.sum_congr rfl (fun i _ => heq i)]
        exact htail
      have hcmp : 3 * (1 + Real.log (3 + (x + (j0 : ℝ)))) / (x + (j0 : ℝ))
          ≤ 6 * (1 + Real.log (2 + η)) / η := by
        have h1 := log_ratio_le (s := η) (t := x + (j0 : ℝ)) hη hle
        calc 3 * (1 + Real.log (3 + (x + (j0 : ℝ)))) / (x + (j0 : ℝ))
            = 3 * ((1 + Real.log (3 + (x + (j0 : ℝ)))) / (x + (j0 : ℝ))) := by ring
          _ ≤ 3 * (2 * (1 + Real.log (2 + η)) / η) := mul_le_mul_of_nonneg_left h1 (by norm_num)
          _ = 6 * (1 + Real.log (2 + η)) / η := by ring
      calc ∑ j ∈ U, term η (x + (j : ℝ))
          = ∑ i ∈ U.image (fun j : ℕ => j - j0), term η ((x + (j0 : ℝ)) + (i : ℝ)) := hstep
        _ ≤ ∑ i ∈ Finset.range k, term η ((x + (j0 : ℝ)) + (i : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => term_nonneg _)
        _ ≤ 3 * (1 + Real.log (3 + (x + (j0 : ℝ)))) / (x + (j0 : ℝ)) := htail'
        _ ≤ 6 * (1 + Real.log (2 + η)) / η := hcmp
  -- lower block
  have hLbound : ∑ j ∈ L, term η (x + (j : ℝ)) ≤ 6 * (1 + Real.log (2 + η)) / η := by
    rcases Finset.eq_empty_or_nonempty L with hLe | hLne
    · rw [hLe, Finset.sum_empty]
      exact div_nonneg (by linarith [hL0]) (le_of_lt hηpos)
    · set j1 : ℕ := L.max' hLne with hj1
      have hmax : j1 ∈ L := by rw [hj1]; exact Finset.max'_mem L hLne
      have hmaxge : ∀ j ∈ L, j ≤ j1 := by
        intro j hj
        rw [hj1]
        exact Finset.le_max' L j hj
      have hb_ge : r ≤ -(x + (j1 : ℝ)) := by
        rw [hL] at hmax
        have h := (Finset.mem_filter.mp hmax).2
        linarith
      have hle : η ≤ -(x + (j1 : ℝ)) := by rw [hr] at hb_ge; linarith
      have hb1 : 1 ≤ -(x + (j1 : ℝ)) := by linarith
      have hinj : Set.InjOn (fun j : ℕ => j1 - j) ↑L := by
        intro j hj j' hj' heq
        have h1 : j ≤ j1 := hmaxge j hj
        have h2 : j' ≤ j1 := hmaxge j' hj'
        have hsubeq : j1 - j = j1 - j' := heq
        have e1 : j + (j1 - j') = j + (j1 - j) := by rw [hsubeq]
        have e2 : j + (j1 - j) = j1 := Nat.add_sub_cancel' h1
        have e3 : j' + (j1 - j') = j1 := Nat.add_sub_cancel' h2
        have h' : j + (j1 - j') = j' + (j1 - j') := e1.trans (e2.trans e3.symm)
        exact Nat.add_right_cancel h'
      have hstep : ∑ j ∈ L, term η (x + (j : ℝ))
          = ∑ i ∈ L.image (fun j : ℕ => j1 - j), term η ((-(x + (j1 : ℝ))) + (i : ℝ)) := by
        rw [Finset.sum_image hinj]
        exact Finset.sum_congr rfl (fun j hj => by
          have h1 : j ≤ j1 := hmaxge j hj
          have hcast : ((j1 - j : ℕ) : ℝ) = (j1 : ℝ) - (j : ℝ) := Nat.cast_sub h1
          rw [← term_neg η (x + (j : ℝ))]
          congr 1
          rw [hcast]; ring)
      have hsub : L.image (fun j : ℕ => j1 - j) ⊆ Finset.range k := by
        intro i hi
        rw [Finset.mem_image] at hi
        obtain ⟨j, hj, rfl⟩ := hi
        rw [Finset.mem_range]
        rw [hL] at hmax
        exact lt_of_le_of_lt (Nat.sub_le j1 j) (Finset.mem_range.mp (Finset.mem_filter.mp hmax).1)
      have htail := tail_log_sum_bound (a := -(x + (j1 : ℝ))) (η := η) (N := k) hb1
      have htail' : ∑ i ∈ Finset.range k, term η ((-(x + (j1 : ℝ))) + (i : ℝ))
          ≤ 3 * (1 + Real.log (3 + (-(x + (j1 : ℝ))))) / (-(x + (j1 : ℝ))) := by
        have heq : ∀ i : ℕ, term η ((-(x + (j1 : ℝ))) + (i : ℝ))
            = (1 + Real.log (2 + ((-(x + (j1 : ℝ))) + (i : ℝ))))
                / (((-(x + (j1 : ℝ))) + (i : ℝ)) ^ 2 + η ^ 2) := by
          intro i
          rw [term, abs_of_nonneg (by have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i; linarith)]
        rw [Finset.sum_congr rfl (fun i _ => heq i)]
        exact htail
      have hcmp : 3 * (1 + Real.log (3 + (-(x + (j1 : ℝ))))) / (-(x + (j1 : ℝ)))
          ≤ 6 * (1 + Real.log (2 + η)) / η := by
        have h1 := log_ratio_le (s := η) (t := -(x + (j1 : ℝ))) hη hle
        calc 3 * (1 + Real.log (3 + (-(x + (j1 : ℝ))))) / (-(x + (j1 : ℝ)))
            = 3 * ((1 + Real.log (3 + (-(x + (j1 : ℝ))))) / (-(x + (j1 : ℝ)))) := by ring
          _ ≤ 3 * (2 * (1 + Real.log (2 + η)) / η) := mul_le_mul_of_nonneg_left h1 (by norm_num)
          _ = 6 * (1 + Real.log (2 + η)) / η := by ring
      calc ∑ j ∈ L, term η (x + (j : ℝ))
          = ∑ i ∈ L.image (fun j : ℕ => j1 - j), term η ((-(x + (j1 : ℝ))) + (i : ℝ)) := hstep
        _ ≤ ∑ i ∈ Finset.range k, term η ((-(x + (j1 : ℝ))) + (i : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => term_nonneg _)
        _ ≤ 3 * (1 + Real.log (3 + (-(x + (j1 : ℝ))))) / (-(x + (j1 : ℝ))) := htail'
        _ ≤ 6 * (1 + Real.log (2 + η)) / η := hcmp
  rw [hSdef, hsplit]
  calc ∑ j ∈ M, term η (x + (j : ℝ))
        + (∑ j ∈ U, term η (x + (j : ℝ)) + ∑ j ∈ L, term η (x + (j : ℝ)))
      ≤ 10 * (1 + Real.log (2 + η)) / η
        + (6 * (1 + Real.log (2 + η)) / η + 6 * (1 + Real.log (2 + η)) / η) := by
        linarith [hMbound, hUbound, hLbound]
    _ = 22 * (1 + Real.log (2 + η)) / η := by ring

end Work.Parab.coordData
