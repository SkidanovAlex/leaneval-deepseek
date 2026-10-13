import Mathlib

namespace Work.WilE4.CAD

/-- If a polynomial has no zero on the closed interval `[a,b]` (with `a ≤ b`), then it takes the
same sign at `a` and at `b`.  Indeed a sign change would produce a zero by the intermediate value
theorem. -/
private lemma sign_eq_of_no_root_Icc {p : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b)
    (hne : ∀ x ∈ Set.Icc a b, p.eval x ≠ 0) :
    SignType.sign (p.eval a) = SignType.sign (p.eval b) := by
  have hcont : ContinuousOn (fun x : ℝ => p.eval x) (Set.Icc a b) :=
    (Polynomial.continuous p).continuousOn
  rcases lt_trichotomy (p.eval a) 0 with ha | ha | ha
  · have hb : p.eval b < 0 := by
      by_contra hb
      push_neg at hb
      rcases lt_or_eq_of_le hb with hb' | hb'
      · have h0 : (0 : ℝ) ∈ Set.Icc (p.eval a) (p.eval b) := ⟨le_of_lt ha, le_of_lt hb'⟩
        obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc hab hcont h0
        exact hne c hc hcv
      · exact hne b ⟨hab, le_refl b⟩ hb'.symm
    rw [sign_neg ha, sign_neg hb]
  · exact absurd ha (hne a ⟨le_refl a, hab⟩)
  · have hb : 0 < p.eval b := by
      by_contra hb
      push_neg at hb
      have h0 : (0 : ℝ) ∈ Set.Icc (p.eval b) (p.eval a) := ⟨hb, le_of_lt ha⟩
      obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc' hab hcont h0
      exact hne c hc hcv
    rw [sign_pos ha, sign_pos hb]

/-- If two points outside `R` have the same number of elements of `R` below them, then no element
of `R` lies strictly between them.  Hence, if `R` contains all the real roots of the members of the
family `f` (excluding the identically zero members, which have no roots), the sign vector of `f` is
the same at the two points. -/
private lemma signVec_of_card_eq {k : ℕ} (f : Fin k → Polynomial ℝ) (R : Finset ℝ)
    (hroot : ∀ i (x : ℝ), (f i).eval x = 0 → f i ≠ 0 → x ∈ R)
    {t₁ t₂ : ℝ} (h₁ : t₁ ∉ R) (h₂ : t₂ ∉ R)
    (hcard : (R.filter (fun r => r < t₁)).card = (R.filter (fun r => r < t₂)).card) :
    (fun i => SignType.sign ((f i).eval t₁)) = (fun i => SignType.sign ((f i).eval t₂)) := by
  have key₁ : ∀ r ∈ R, ¬ (t₁ < r ∧ r < t₂) := by
    rintro r hr ⟨hr1, hr2⟩
    have hsub : R.filter (fun r => r < t₁) ⊆ R.filter (fun r => r < t₂) := by
      intro r hr'
      rw [Finset.mem_filter] at hr' ⊢
      exact ⟨hr'.1, lt_trans hr'.2 (lt_trans hr1 hr2)⟩
    have hssub : R.filter (fun r => r < t₁) ⊂ R.filter (fun r => r < t₂) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => ?_⟩
      have hmem : r ∈ R.filter (fun r => r < t₁) := by
        rw [heq]; exact Finset.mem_filter.mpr ⟨hr, hr2⟩
      exact absurd (Finset.mem_filter.mp hmem).2 (not_lt.mpr (le_of_lt hr1))
    have hlt := Finset.card_lt_card hssub
    omega
  have key₂ : ∀ r ∈ R, ¬ (t₂ < r ∧ r < t₁) := by
    rintro r hr ⟨hr1, hr2⟩
    have hsub : R.filter (fun r => r < t₂) ⊆ R.filter (fun r => r < t₁) := by
      intro r hr'
      rw [Finset.mem_filter] at hr' ⊢
      exact ⟨hr'.1, lt_trans hr'.2 (lt_trans hr1 hr2)⟩
    have hssub : R.filter (fun r => r < t₂) ⊂ R.filter (fun r => r < t₁) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => ?_⟩
      have hmem : r ∈ R.filter (fun r => r < t₂) := by
        rw [heq]; exact Finset.mem_filter.mpr ⟨hr, hr2⟩
      exact absurd (Finset.mem_filter.mp hmem).2 (not_lt.mpr (le_of_lt hr1))
    have hlt := Finset.card_lt_card hssub
    omega
  funext i
  by_cases hf : f i = 0
  · rw [hf]; simp
  · rcases le_total t₁ t₂ with hle | hle
    · refine sign_eq_of_no_root_Icc hle fun x hx => ?_
      by_contra hx0
      have hxR : x ∈ R := hroot i x hx0 hf
      rcases lt_trichotomy x t₁ with hlt | heq | hgt
      · exact absurd hx.1 (not_le.mpr hlt)
      · exact h₁ (heq ▸ hxR)
      · rcases lt_trichotomy x t₂ with hlt2 | heq2 | hgt2
        · exact key₁ x hxR ⟨hgt, hlt2⟩
        · exact h₂ (heq2 ▸ hxR)
        · exact absurd hx.2 (not_le.mpr hgt2)
    · refine (sign_eq_of_no_root_Icc hle fun x hx => ?_).symm
      by_contra hx0
      have hxR : x ∈ R := hroot i x hx0 hf
      rcases lt_trichotomy x t₂ with hlt | heq | hgt
      · exact absurd hx.1 (not_le.mpr hlt)
      · exact h₂ (heq ▸ hxR)
      · rcases lt_trichotomy x t₁ with hlt2 | heq2 | hgt2
        · exact key₂ x hxR ⟨hgt, hlt2⟩
        · exact h₁ (heq2 ▸ hxR)
        · exact absurd hx.2 (not_le.mpr hgt2)

theorem realized_signvec_card {k d : ℕ} (f : Fin k → Polynomial ℝ)
    (hd : ∀ i : Fin k, (f i).natDegree ≤ d) :
    ∃ S : Finset (Fin k → SignType), S.card ≤ 2 * (k * d + 1) + 1 ∧
      ∀ v : Fin k → SignType, (∃ t : ℝ, ∀ i, SignType.sign ((f i).eval t) = v i) → v ∈ S := by
  classical
  -- `R` is the set of all real roots of the members of the family.
  set R : Finset ℝ := Finset.univ.biUnion (fun i : Fin k => (f i).roots.toFinset) with hRdef
  have hroot : ∀ i (x : ℝ), (f i).eval x = 0 → f i ≠ 0 → x ∈ R := by
    intro i x hx hf
    rw [hRdef]
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
    exact hx
  -- `R` has at most `k * d` elements.
  have hRcard : R.card ≤ k * d := by
    rw [hRdef]
    calc (Finset.univ.biUnion (fun i : Fin k => (f i).roots.toFinset)).card
        ≤ ∑ i : Fin k, ((f i).roots.toFinset).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin k, d := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            exact le_trans (le_trans (Multiset.toFinset_card_le _)
              (Polynomial.card_roots' _)) (hd i)
      _ = k * d := by simp [Finset.sum_const, Finset.card_univ]
  let W : ℝ → (Fin k → SignType) := fun t i => SignType.sign ((f i).eval t)
  -- Off the roots, the sign vector only depends on the number of roots below the point.
  have hWconst : ∀ {t₁ t₂ : ℝ}, t₁ ∉ R → t₂ ∉ R →
      (R.filter (fun r => r < t₁)).card = (R.filter (fun r => r < t₂)).card → W t₁ = W t₂ := by
    intro t₁ t₂ h₁ h₂ hcard
    exact signVec_of_card_eq f R hroot h₁ h₂ hcard
  -- A representative of every possible "off the roots" position, chosen by `Classical.epsilon`.
  let g : Fin (R.card + 1) → (Fin k → SignType) :=
    fun n => W (Classical.epsilon fun s : ℝ =>
      s ∉ R ∧ (R.filter (fun r => r < s)).card = (n : ℕ))
  refine ⟨(R.image W) ∪ (Finset.univ.image g), ?_, ?_⟩
  · -- Cardinality bound.
    have h1 : (R.image W).card ≤ R.card := Finset.card_image_le
    have h2 : (Finset.univ.image g).card ≤ R.card + 1 := by
      calc (Finset.univ.image g).card
          ≤ (Finset.univ : Finset (Fin (R.card + 1))).card := Finset.card_image_le
        _ = R.card + 1 := by simp
    have h3 := Finset.card_union_le (R.image W) (Finset.univ.image g)
    omega
  · -- Every realised sign vector lies in the set.
    intro v hv
    obtain ⟨t, ht⟩ := hv
    have hvt : v = W t := by
      funext i
      exact (ht i).symm
    rw [hvt]
    by_cases htR : t ∈ R
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨t, htR, rfl⟩))
    · have hn : (R.filter (fun r => r < t)).card < R.card + 1 :=
        Nat.lt_succ_of_le (Finset.card_filter_le R (fun r => r < t))
      let n : Fin (R.card + 1) := ⟨(R.filter (fun r => r < t)).card, hn⟩
      have hex : ∃ s : ℝ, s ∉ R ∧ (R.filter (fun r => r < s)).card = (n : ℕ) := ⟨t, htR, rfl⟩
      have hgv : g n = W t := by
        show W (Classical.epsilon fun s : ℝ =>
          s ∉ R ∧ (R.filter (fun r => r < s)).card = (n : ℕ)) = W t
        have he := Classical.epsilon_spec hex
        exact hWconst he.1 htR he.2
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨n, Finset.mem_univ n, hgv⟩))

end Work.WilE4.CAD
