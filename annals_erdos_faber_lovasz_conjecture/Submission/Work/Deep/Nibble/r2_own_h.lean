import Submission.Work.Deep.Nibble.r2_own_g

set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The tail bound for the number of uncovered vertices, from `bj_talagrand`. -/
theorem r2_Y_tail (𝓖 : Set (Set V)) {r : ℕ} (hr : 2 ≤ r) (huni : HUnif 𝓖 r) {θ : ℝ}
    (hθ0 : 0 < θ) {D : ℕ} (hD : 1 ≤ D) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) < 1) {t : ℝ}
    (ht : 50 * (r : ℝ) * Real.sqrt (Fintype.card V : ℝ) < t) :
    (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).prob
        {ω : 𝓖 → Bool | t ≤ |((uncovF 𝓖 ω).card : ℝ)
          - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).exp (fun ω => ((uncovF 𝓖 ω).card : ℝ))|}
      ≤ 4 * Real.exp (-t ^ 2 / (16 * (r : ℝ) ^ 2 * (Fintype.card V : ℝ))) := by
  classical
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
  have htpos : 0 < t := by
    have h1 : (0:ℝ) ≤ Real.sqrt (Fintype.card V : ℝ) := Real.sqrt_nonneg _
    nlinarith [ht, h1]
  have hfull : ∀ (i : 𝓖) (x : Bool), 0 < (boolProb (θ / (D : ℝ)) hp0 hp1.le).wt x := by
    intro i x
    cases x with
    | true => simpa using (div_pos hθ0 hDpos)
    | false =>
        simp only [boolProb_wt_false]
        rw [sub_pos]
        exact hp1
  have hle : ∀ ω : 𝓖 → Bool, ((uncovF 𝓖 ω).card : ℝ) ≤ (Fintype.card V : ℝ) := by
    intro ω
    calc ((uncovF 𝓖 ω).card : ℝ) ≤ ((Finset.univ : Finset V).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ = (Fintype.card V : ℝ) := by simp
  have hcert : ∀ u : ℝ, 0 < u → ∀ ω : 𝓖 → Bool, ω ∉ (∅ : Set (𝓖 → Bool)) →
      ∃ I : Finset 𝓖, I.card ≤ Fintype.card V ∧
        ∀ ω' : 𝓖 → Bool, ω' ∉ (∅ : Set (𝓖 → Bool)) →
          ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / (r : ℝ) →
            ((uncovF 𝓖 ω').card : ℝ) < ((uncovF 𝓖 ω).card : ℝ) + u := by
    intro u hu ω _
    by_cases hne : 𝓖.Nonempty
    · obtain ⟨e₀, he₀⟩ := hne
      haveI : Nonempty 𝓖 := ⟨⟨e₀, he₀⟩⟩
      let f : V → 𝓖 := fun v =>
        if h : v ∈ covX 𝓖 ω then Classical.choose ((mem_covX_iff 𝓖 ω v).mp h)
        else Classical.arbitrary 𝓖
      let I : Finset 𝓖 := (Finset.univ.filter (fun v : V => v ∈ covX 𝓖 ω)).image f
      have hf_kept : ∀ (v : V) (hv : v ∈ covX 𝓖 ω), ω (f v) = true := by
        intro v hv
        have h1 : f v = Classical.choose ((mem_covX_iff 𝓖 ω v).mp hv) := by
          simp only [f, dif_pos hv]
        rw [h1]
        exact (Classical.choose_spec ((mem_covX_iff 𝓖 ω v).mp hv)).1
      have hf_through : ∀ (v : V) (hv : v ∈ covX 𝓖 ω), v ∈ (f v : Set V) := by
        intro v hv
        have h1 : f v = Classical.choose ((mem_covX_iff 𝓖 ω v).mp hv) := by
          simp only [f, dif_pos hv]
        rw [h1]
        exact (Classical.choose_spec ((mem_covX_iff 𝓖 ω v).mp hv)).2
      have hf_mem : ∀ (v : V) (hv : v ∈ covX 𝓖 ω), f v ∈ I := by
        intro v hv
        refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hv⟩
      refine ⟨I, ?_, fun ω' _ hdis => ?_⟩
      · calc I.card ≤ (Finset.univ.filter (fun v : V => v ∈ covX 𝓖 ω)).card :=
            Finset.card_image_le
          _ ≤ (Finset.univ : Finset V).card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = Fintype.card V := Finset.card_univ
      · have hnew : ∀ v : V, v ∈ covX 𝓖 ω → v ∉ covX 𝓖 ω' →
            f v ∈ (I.filter (fun i => ω i ≠ ω' i)) := by
          intro v hv hv'
          refine Finset.mem_filter.mpr ⟨hf_mem v hv, ?_⟩
          have h1 : ω (f v) = true := hf_kept v hv
          have h2 : ω' (f v) = false := by
            by_contra hc
            exact hv' ((mem_covX_iff 𝓖 ω' v).mpr ⟨f v, by simpa using hc, hf_through v hv⟩)
          rw [h1, h2]
          simp
        have hmaps : ∀ v ∈ Finset.univ.filter (fun v : V => v ∈ covX 𝓖 ω ∧ v ∉ covX 𝓖 ω'),
            f v ∈ (I.filter (fun i => ω i ≠ ω' i)) := by
          intro v hv
          obtain ⟨-, hv1, hv2⟩ := Finset.mem_filter.mp hv
          exact hnew v hv1 hv2
        have hfib : ∀ i ∈ (I.filter (fun i => ω i ≠ ω' i)),
            ((Finset.univ.filter (fun v : V => v ∈ covX 𝓖 ω ∧ v ∉ covX 𝓖 ω')).filter
              (fun v => f v = i)).card ≤ r := by
          intro i hi
          calc ((Finset.univ.filter (fun v : V => v ∈ covX 𝓖 ω ∧ v ∉ covX 𝓖 ω')).filter
                (fun v => f v = i)).card
              ≤ (Finset.univ.filter (fun v : V => v ∈ (i : Set V))).card := by
                refine Finset.card_le_card ?_
                intro v hv
                rw [Finset.mem_filter] at hv
                obtain ⟨hv1, hv2⟩ := hv
                obtain ⟨-, hv3, -⟩ := Finset.mem_filter.mp hv1
                rw [Finset.mem_filter]
                refine ⟨Finset.mem_univ _, ?_⟩
                have h1 : v ∈ (f v : Set V) := hf_through v hv3
                rwa [hv2] at h1
            _ = r := by
                have hc : (Finset.univ.filter (fun v : V => v ∈ (i : Set V))).card = r := by
                  rw [← natCard_subtype_eq_filter_card (fun x : V => x ∈ (i : Set V))]
                  exact huni i i.2
                exact hc
        have hbound : ((Finset.univ.filter (fun v : V => v ∈ covX 𝓖 ω ∧ v ∉ covX 𝓖 ω')).card : ℝ)
            ≤ ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) * (r : ℝ) := by
          rw [Finset.card_eq_sum_card_fiberwise (f := f)
            (s := Finset.univ.filter (fun v : V => v ∈ covX 𝓖 ω ∧ v ∉ covX 𝓖 ω'))
            (t := I.filter (fun i => ω i ≠ ω' i)) hmaps]
          calc (((∑ i ∈ I.filter (fun i => ω i ≠ ω' i),
              ((Finset.univ.filter (fun v : V => v ∈ covX 𝓖 ω ∧ v ∉ covX 𝓖 ω')).filter
                (fun v => f v = i)).card : ℕ)) : ℝ)
              ≤ (((∑ _i ∈ I.filter (fun i => ω i ≠ ω' i), r : ℕ)) : ℝ) := by
                exact_mod_cast Finset.sum_le_sum (fun i hi => hfib i hi)
            _ = ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) * (r : ℝ) := by
                rw [Finset.sum_const, smul_eq_mul]
                push_cast
                ring
        have huncov : ((uncovF 𝓖 ω').card : ℝ)
            ≤ ((uncovF 𝓖 ω).card : ℝ)
              + ((Finset.univ.filter (fun v : V => v ∈ covX 𝓖 ω ∧ v ∉ covX 𝓖 ω')).card : ℝ) := by
          have hset : uncovF 𝓖 ω'
              = (uncovF 𝓖 ω ∩ uncovF 𝓖 ω')
                ∪ (Finset.univ.filter (fun v : V => v ∈ covX 𝓖 ω ∧ v ∉ covX 𝓖 ω')) := by
            ext v
            simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
              true_and, uncovF_mem_iff]
            constructor
            · intro hv
              by_cases h : v ∈ covX 𝓖 ω
              · exact Or.inr ⟨h, hv⟩
              · exact Or.inl ⟨h, hv⟩
            · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · exact h2
              · exact h2
          rw [hset]
          calc (((uncovF 𝓖 ω ∩ uncovF 𝓖 ω')
                ∪ (Finset.univ.filter (fun v : V => v ∈ covX 𝓖 ω ∧ v ∉ covX 𝓖 ω'))).card : ℝ)
              ≤ ((uncovF 𝓖 ω ∩ uncovF 𝓖 ω').card : ℝ)
                + ((Finset.univ.filter (fun v : V => v ∈ covX 𝓖 ω ∧ v ∉ covX 𝓖 ω')).card : ℝ) := by
                exact_mod_cast Finset.card_union_le _ _
            _ ≤ ((uncovF 𝓖 ω).card : ℝ)
                + ((Finset.univ.filter (fun v : V => v ∈ covX 𝓖 ω ∧ v ∉ covX 𝓖 ω')).card : ℝ) := by
                have h1 : (uncovF 𝓖 ω ∩ uncovF 𝓖 ω').card ≤ (uncovF 𝓖 ω).card :=
                  Finset.card_le_card Finset.inter_subset_left
                have h1' : (((uncovF 𝓖 ω ∩ uncovF 𝓖 ω').card : ℕ) : ℝ)
                    ≤ (((uncovF 𝓖 ω).card : ℕ) : ℝ) := by exact_mod_cast h1
                linarith
        have hlt : ((Finset.univ.filter (fun v : V => v ∈ covX 𝓖 ω ∧ v ∉ covX 𝓖 ω')).card : ℝ) < u := by
          calc _ ≤ ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) * (r : ℝ) := hbound
            _ < (u / (r : ℝ)) * (r : ℝ) := mul_lt_mul_of_pos_right hdis hrpos
            _ = u := by field_simp
        linarith
    · -- 𝓖 is empty: the uncovered set is everything in both outcomes
      have hcov : ∀ ω : 𝓖 → Bool, covX 𝓖 ω = ∅ := by
        intro ω
        ext v
        rw [mem_covX_iff]
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨e, -, -⟩
        exact absurd ⟨e, e.2⟩ hne
      refine ⟨∅, by simp, fun ω' _ hdis => ?_⟩
      have h1 : uncovF 𝓖 ω = Finset.univ := by
        ext v
        rw [uncovF_mem_iff]
        simp only [Finset.mem_univ, iff_true]
        rw [hcov ω]
        simp
      have h2 : uncovF 𝓖 ω' = Finset.univ := by
        ext v
        rw [uncovF_mem_iff]
        simp only [Finset.mem_univ, iff_true]
        rw [hcov ω']
        simp
      rw [h1, h2]
      simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero, Finset.card_univ] at hdis
      linarith
  by_cases hV : Nonempty V
  · haveI : Nonempty V := hV
    have hcardpos : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have hmain := bj_talagrand (μ := fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le) hfull
      (fun ω => ((uncovF 𝓖 ω).card : ℝ)) ((Fintype.card V : ℝ)) hcardpos
      (fun ω => by rw [abs_of_nonneg (by positivity)]; exact hle ω)
      (r : ℝ) (by exact_mod_cast (by omega : 1 ≤ r)) (Fintype.card V)
      (by exact_mod_cast Fintype.card_pos)
      (∅ : Set (𝓖 → Bool)) (by rw [FinProb.prob_empty]; positivity) hcert t ht
    rw [FinProb.prob_empty, mul_zero, add_zero] at hmain
    exact hmain
  · -- `V` is empty: the variable is identically zero and the event is empty
    have hempty : ∀ ω : 𝓖 → Bool, uncovF 𝓖 ω = ∅ := by
      intro ω
      ext v
      exact absurd ⟨v⟩ hV
    have hzero : ∀ ω : 𝓖 → Bool, ((uncovF 𝓖 ω).card : ℝ) = 0 := by
      intro ω
      rw [hempty ω]
      simp
    have hset : {ω : 𝓖 → Bool | t ≤ |((uncovF 𝓖 ω).card : ℝ)
          - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).exp (fun ω => ((uncovF 𝓖 ω).card : ℝ))|}
        = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rw [hzero ω]
      have hexp0 : (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).exp
          (fun ω => ((uncovF 𝓖 ω).card : ℝ)) = 0 := by
        rw [show (fun ω : 𝓖 → Bool => ((uncovF 𝓖 ω).card : ℝ)) = (fun _ => (0:ℝ)) from
          funext (fun ω => hzero ω)]
        exact FinProb.exp_const _ 0
      rw [hexp0]
      simp only [sub_zero, abs_zero]
      exact not_le.mpr htpos
    rw [hset, FinProb.prob_empty]
    exact mul_nonneg (by norm_num) (Real.exp_nonneg _)

end Work.Deep.Nibble
