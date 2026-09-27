import Mathlib

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Drive

open Set

namespace ENPC

/-! ## Auxiliary lemmas for `even_ncard_of_periodic_changes` -/

/-- A `1`-periodic set is invariant under all integer translations. -/
theorem mem_add_intCast_iff {Z : Set ℝ} (hZper : ∀ t : ℝ, t ∈ Z ↔ t + 1 ∈ Z) (t : ℝ) :
    ∀ k : ℤ, t + (k : ℝ) ∈ Z ↔ t ∈ Z := by
  have hZper_sub : ∀ s : ℝ, s - 1 ∈ Z ↔ s ∈ Z := by
    intro s
    have h := hZper (s - 1)
    rwa [sub_add_cancel] at h
  intro k
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have h : t + (((n : ℤ) + 1 : ℤ) : ℝ) = (t + (n : ℝ)) + 1 := by push_cast; ring
      rw [h, ← hZper (t + (n : ℝ))]
      exact ih
  | pred n ih =>
      have h : t + ((-(n : ℤ) - 1 : ℤ) : ℝ) = (t + ((-(n : ℤ) : ℤ) : ℝ)) - 1 := by
        push_cast; ring
      rw [h, hZper_sub]
      exact ih

/-- **A function that is locally constant away from `Z` is constant on any closed interval
which avoids `Z`.** -/
theorem zfree_const {Z : Set ℝ} {f : ℝ → ℤ}
    (hloc : ∀ t : ℝ, t ∉ Z → ∃ ε > 0, ∀ s : ℝ, |s - t| < ε → s ∉ Z → f s = f t)
    (u v : ℝ) (huv : u ≤ v)
    (hZfree : ∀ t : ℝ, u ≤ t → t ≤ v → t ∉ Z) :
    f u = f v := by
  have hLC : IsLocallyConstant (fun x : Set.Icc u v => f x.1) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro t
    obtain ⟨ε, hεpos, hε⟩ := hloc t.1 (hZfree t.1 t.2.1 t.2.2)
    refine ⟨Subtype.val ⁻¹' Metric.ball t.1 ε, ?_, ?_, ?_⟩
    · exact Metric.isOpen_ball.preimage continuous_subtype_val
    · simp only [Set.mem_preimage, Metric.mem_ball, dist_self]
      exact hεpos
    · intro x hx
      simp only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hx
      exact hε x.1 hx (hZfree x.1 x.2.1 x.2.2)
  have hpre : IsPreconnected (Set.Icc u v) := isPreconnected_Icc
  haveI : PreconnectedSpace (Set.Icc u v) := (isPreconnected_iff_preconnectedSpace).mp hpre
  exact hLC.apply_eq_of_preconnectedSpace ⟨u, ⟨le_refl u, huv⟩⟩ ⟨v, ⟨huv, le_refl v⟩⟩

/-- `Int.fract` of a point of `Z` still lies in `Z`. -/
theorem fract_mem {Z : Set ℝ} (hZper : ∀ t : ℝ, t ∈ Z ↔ t + 1 ∈ Z)
    {a : ℝ} (ha : a ∈ Z) : Int.fract a ∈ Z := by
  have h : Int.fract a = a + ((-⌊a⌋ : ℤ) : ℝ) := by
    rw [← Int.self_sub_floor a]; push_cast; ring
  rw [h]
  exact (mem_add_intCast_iff hZper a (-⌊a⌋)).mpr ha

/-- **A `1`-periodic set with finite fundamental domain meets every bounded interval finitely.** -/
theorem finite_inter_Ioo_periodic (Z : Set ℝ)
    (hZper : ∀ t : ℝ, t ∈ Z ↔ t + 1 ∈ Z)
    (hZfin : (Z ∩ Set.Ico (0:ℝ) 1).Finite) (a b : ℝ) :
    (Z ∩ Set.Ioo a b).Finite := by
  by_cases hab : a < b
  swap
  · rw [Set.Ioo_eq_empty (not_lt.mpr (not_lt.mp hab)), Set.inter_empty]
    exact Set.finite_empty
  have hUfin : (⋃ z ∈ (Z ∩ Set.Ico (0:ℝ) 1),
      ((fun k : ℤ => z + (k : ℝ)) '' {k : ℤ | a < z + k ∧ z + k < b})).Finite := by
    refine Set.Finite.biUnion hZfin (fun z hz => ?_)
    refine Set.Finite.image (fun k : ℤ => z + (k : ℝ)) ?_
    refine Set.Finite.subset (Set.finite_Icc ⌊a - z⌋ ⌊b - z⌋) ?_
    intro k hk
    simp only [Set.mem_setOf_eq] at hk
    simp only [Set.mem_Icc]
    constructor
    · rw [Int.floor_le_iff]
      linarith [hk.1]
    · rw [Int.le_floor]
      push_cast
      linarith [hk.2]
  refine hUfin.subset ?_
  · rintro t ⟨htZ, htIoo⟩
    have ht1 : a < t := htIoo.1
    have ht2 : t < b := htIoo.2
    have hfrac : Int.fract t + (⌊t⌋ : ℝ) = t := Int.fract_add_floor t
    refine Set.mem_iUnion₂.mpr ⟨Int.fract t,
      ⟨fract_mem hZper htZ, Int.fract_nonneg t, Int.fract_lt_one t⟩, ?_⟩
    rw [Set.mem_image]
    exact ⟨⌊t⌋, ⟨by linarith, by linarith⟩, by linarith⟩

/-- The number of points of a `1`-periodic set in a window of length `1` does not depend on
the window, as long as the window is placed with generic endpoints. -/
theorem ncard_shift_periodic {Z : Set ℝ} (hZper : ∀ t : ℝ, t ∈ Z ↔ t + 1 ∈ Z)
    (hZfin : (Z ∩ Set.Ico (0:ℝ) 1).Finite) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 0)
    (hxZ : x ∉ Z) (hx1Z : x + 1 ∉ Z) :
    (Z ∩ Set.Ioo x (x + 1)).ncard = (Z ∩ Set.Ico (0:ℝ) 1).ncard := by
  have hfract_eq : ∀ a : ℝ, Int.fract a = a - (⌊a⌋ : ℝ) := fun a => (Int.self_sub_floor a).symm
  refine Set.ncard_congr (fun a (_ : a ∈ Z ∩ Set.Ioo x (x + 1)) => Int.fract a) ?_ ?_ ?_
  · intro a ha
    exact ⟨fract_mem hZper ha.1, Int.fract_nonneg a, Int.fract_lt_one a⟩
  · intro a b ha hb hab
    have hdiff : a - b = ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) := by
      have h := hab
      rw [hfract_eq a, hfract_eq b] at h
      push_cast
      linarith
    by_contra hne
    have habs : |a - b| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2]
    have hne' : (⌊a⌋ - ⌊b⌋ : ℤ) ≠ 0 := by
      intro h
      apply hne
      have hz : a - b = 0 := by rw [hdiff, h]; norm_num
      linarith
    have hge : (1 : ℝ) ≤ |a - b| := by
      have h1 : |a - b| = ((|⌊a⌋ - ⌊b⌋| : ℤ) : ℝ) := by
        rw [hdiff, ← Int.cast_abs]
      rw [h1]
      have h2 : (1 : ℤ) ≤ |⌊a⌋ - ⌊b⌋| := Int.one_le_abs hne'
      exact_mod_cast h2
    linarith
  · intro z hz
    have hzZ : z ∈ Z := hz.1
    have hz0 : 0 ≤ z := hz.2.1
    have hz1 : z < 1 := hz.2.2
    have hzx : z ≠ x + 1 := fun h => hx1Z (h ▸ hzZ)
    rcases lt_trichotomy z (x + 1) with hlt | heq | hgt
    · refine ⟨z, ⟨hzZ, by linarith [hx.2, hz0], hlt⟩, ?_⟩
      have hfl : ⌊z⌋ = (0:ℤ) := by
        rw [Int.floor_eq_iff]
        exact ⟨by simpa using hz0, by simpa using hz1⟩
      rw [← Int.self_sub_floor z, hfl]
      ring
    · exact absurd heq hzx
    · refine ⟨z - 1, ⟨?_, by linarith, by linarith [hx.1, hz1]⟩, ?_⟩
      · rw [show z - 1 = z + ((-1 : ℤ) : ℝ) by push_cast; ring]
        exact (mem_add_intCast_iff hZper z (-1)).mpr hzZ
      · have hfl : ⌊z - 1⌋ = (-1 : ℤ) := by
          rw [Int.floor_eq_iff]
          refine ⟨?_, ?_⟩ <;> push_cast <;> linarith
        rw [← Int.self_sub_floor (z - 1), hfl]
        push_cast
        ring

/-- A non-negative integer which is even as an integer is even. -/
lemma even_nat_of_even_int {n : ℕ} (h : Even (n : ℤ)) : Even n := by
  obtain ⟨k, hk⟩ := h
  have hk0 : 0 ≤ k := by
    have h1 : (0 : ℤ) ≤ k + k := by rw [← hk]; exact Int.natCast_nonneg n
    linarith
  refine ⟨k.toNat, ?_⟩
  have h2 : ((k.toNat : ℕ) : ℤ) + ((k.toNat : ℕ) : ℤ) = (n : ℤ) := by
    rw [Int.toNat_of_nonneg hk0, hk]
  exact_mod_cast h2.symm

/-- A finite sum of `±1`'s which vanishes has an even number of terms. -/
theorem even_card_of_sum_eq_zero {α : Type*} (s : Finset α) (g : α → ℤ)
    (h1 : ∀ x ∈ s, g x = 1 ∨ g x = -1) (hsum : ∑ x ∈ s, g x = 0) : Even s.card := by
  have hg : ∀ x ∈ s, g x = 2 * (if g x = 1 then (1 : ℤ) else 0) - 1 := by
    intro x hx
    rcases h1 x hx with h | h <;> simp [h]
  have hsum2 : ∑ x ∈ s, (2 * (if g x = 1 then (1 : ℤ) else 0) - 1) = 0 :=
    (Finset.sum_congr rfl (fun x hx => (hg x hx).symm)).trans hsum
  have hkey : (s.card : ℤ) = 2 * ∑ x ∈ s, (if g x = 1 then (1 : ℤ) else 0) := by
    have h := hsum2
    rw [Finset.sum_sub_distrib] at h
    rw [← Finset.mul_sum] at h
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
    linarith
  exact even_nat_of_even_int ⟨_, by rw [hkey]; ring⟩

/-- A finite sum of `±2`'s which vanishes has an even number of terms. -/
theorem even_card_of_sum_eq_zero_two {α : Type*} (s : Finset α) (g : α → ℤ)
    (h1 : ∀ x ∈ s, g x = 2 ∨ g x = -2) (hsum : ∑ x ∈ s, g x = 0) : Even s.card := by
  have hsumσ : ∑ x ∈ s, (if g x = 2 then (1 : ℤ) else -1) = 0 := by
    have h2 : (2 : ℤ) * ∑ x ∈ s, (if g x = 2 then (1 : ℤ) else -1) = ∑ x ∈ s, g x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x hx => by rcases h1 x hx with h | h <;> simp [h])
    have h3 : (2 : ℤ) * ∑ x ∈ s, (if g x = 2 then (1 : ℤ) else -1) = 0 := by rw [h2, hsum]
    omega
  exact even_card_of_sum_eq_zero s _ (fun x hx => by
    rcases h1 x hx with h | h
    · left; simp [h]
    · right; simp [h]) hsumσ

end ENPC

open ENPC

theorem even_ncard_of_periodic_changes (Z : Set ℝ)
    (hZper : ∀ t : ℝ, t ∈ Z ↔ t + 1 ∈ Z)
    (hZfin : (Z ∩ Set.Ico (0:ℝ) 1).Finite)
    (f : ℝ → ℤ)
    (hloc : ∀ t : ℝ, t ∉ Z → ∃ ε > 0, ∀ s : ℝ, |s - t| < ε → s ∉ Z → f s = f t)
    (hper : ∀ t : ℝ, f (t + 1) = f t)
    (hchange : ∀ τ ∈ Z, ∃ t₁ t₂ : ℝ, t₁ ∉ Z ∧ t₂ ∉ Z ∧ t₁ < τ ∧ τ < t₂ ∧
      (∀ s : ℝ, t₁ < s → s < t₂ → s ∈ Z → s = τ) ∧
      (f t₂ - f t₁ = 2 ∨ f t₂ - f t₁ = -2)) :
    Even (Z ∩ Set.Ico (0:ℝ) 1).ncard := by
  classical
  -- ## Step 1: a generic window of length `1` with endpoints off `Z`.
  have hBfin : ((Z ∩ Set.Ioo (-1:ℝ) 0) ∪
      ((fun s : ℝ => s - 1) '' (Z ∩ Set.Ioo (0:ℝ) 1))).Finite :=
    (finite_inter_Ioo_periodic Z hZper hZfin (-1) 0).union
      ((finite_inter_Ioo_periodic Z hZper hZfin 0 1).image (fun s : ℝ => s - 1))
  obtain ⟨x, hx_mem, hx_notB⟩ :=
    (Set.Ioo_infinite (show (-1:ℝ) < 0 by norm_num)).exists_notMem_finite hBfin
  have hxZ : x ∉ Z := fun h => hx_notB (Or.inl ⟨h, hx_mem⟩)
  have hx1Z : x + 1 ∉ Z := by
    intro h
    refine hx_notB (Or.inr ?_)
    exact ⟨x + 1, ⟨h, by linarith [hx_mem.1], by linarith [hx_mem.2]⟩, by ring⟩
  have hxlt : x < x + 1 := by linarith
  -- ## Step 2: the jump function at the points of `Z`.
  have hchange' : ∀ τ ∈ Z, ∃ p : ℝ × ℝ,
      p.1 ∉ Z ∧ p.2 ∉ Z ∧ p.1 < τ ∧ τ < p.2 ∧
      (∀ s : ℝ, p.1 < s → s < p.2 → s ∈ Z → s = τ) ∧
      (f p.2 - f p.1 = 2 ∨ f p.2 - f p.1 = -2) := by
    intro τ hτ
    obtain ⟨t₁, t₂, h1, h2, h3, h4, h5, h6⟩ := hchange τ hτ
    exact ⟨(t₁, t₂), h1, h2, h3, h4, h5, h6⟩
  let W : ℝ → ℝ × ℝ := fun τ => if h : τ ∈ Z then Classical.choose (hchange' τ h) else (τ, τ)
  have hWspec : ∀ τ (hτ : τ ∈ Z), W τ = Classical.choose (hchange' τ hτ) := fun τ hτ => by
    show (if h : τ ∈ Z then Classical.choose (hchange' τ h) else (τ, τ)) = _
    exact dif_pos hτ
  have hW : ∀ τ (hτ : τ ∈ Z),
      (W τ).1 ∉ Z ∧ (W τ).2 ∉ Z ∧ (W τ).1 < τ ∧ τ < (W τ).2 ∧
      (∀ s : ℝ, (W τ).1 < s → s < (W τ).2 → s ∈ Z → s = τ) ∧
      (f (W τ).2 - f (W τ).1 = 2 ∨ f (W τ).2 - f (W τ).1 = -2) := by
    intro τ hτ
    rw [hWspec τ hτ]
    exact Classical.choose_spec (hchange' τ hτ)
  let J : ℝ → ℤ := fun τ => if h : τ ∈ Z then f (W τ).2 - f (W τ).1 else 0
  have hJ : ∀ τ (hτ : τ ∈ Z), J τ = f (W τ).2 - f (W τ).1 := fun τ hτ => by
    show (if h : τ ∈ Z then f (W τ).2 - f (W τ).1 else (0 : ℤ)) = _
    exact dif_pos hτ
  -- ## Step 3: telescoping over the points of `Z` in a window.
  have telescope : ∀ (a b : ℝ) (ha : a ∉ Z) (hb : b ∉ Z) (hab : a < b),
      f b - f a = ∑ τ ∈ (finite_inter_Ioo_periodic Z hZper hZfin a b).toFinset, J τ := by
    have main : ∀ (n : ℕ) (a b : ℝ) (ha : a ∉ Z) (hb : b ∉ Z) (hab : a < b),
        (Z ∩ Set.Ioo a b).ncard = n →
        f b - f a = ∑ τ ∈ (finite_inter_Ioo_periodic Z hZper hZfin a b).toFinset, J τ := by
      intro n
      refine Nat.strong_induction_on n ?_
      intro n ih a b ha hb hab hn
      have hfin_a : (Z ∩ Set.Ioo a b).Finite := finite_inter_Ioo_periodic Z hZper hZfin a b
      by_cases hne : (Z ∩ Set.Ioo a b).Nonempty
      · -- there is at least one point of `Z` in the window
        have hneF : hfin_a.toFinset.Nonempty := by
          obtain ⟨y, hy⟩ := hne
          exact ⟨y, by rwa [Set.Finite.mem_toFinset]⟩
        obtain ⟨τs, hτs_mem, hτs_min⟩ :
            ∃ τs ∈ hfin_a.toFinset, ∀ y ∈ hfin_a.toFinset, τs ≤ y :=
          ⟨hfin_a.toFinset.min' hneF, Finset.min'_mem _ _,
            fun y hy => Finset.min'_le _ y hy⟩
        have hτs_E : τs ∈ Z ∩ Set.Ioo a b := by
          rw [← Set.Finite.mem_toFinset hfin_a]; exact hτs_mem
        have hτsZ : τs ∈ Z := hτs_E.1
        have haτs : a < τs := hτs_E.2.1
        have hτsb : τs < b := hτs_E.2.2
        have hWs := hW τs hτsZ
        let t₁ : ℝ := (W τs).1
        let t₂ : ℝ := (W τs).2
        have ht1Z : t₁ ∉ Z := hWs.1
        have ht2Z : t₂ ∉ Z := hWs.2.1
        have ht1lt : t₁ < τs := hWs.2.2.1
        have htlt2 : τs < t₂ := hWs.2.2.2.1
        have hgap : ∀ s : ℝ, t₁ < s → s < t₂ → s ∈ Z → s = τs := hWs.2.2.2.2.1
        have hJt : J τs = f t₂ - f t₁ := hJ τs hτsZ
        have haτs_free : ∀ s : ℝ, a < s → s < τs → s ∉ Z := by
          intro s has hsts hsZ
          have hsE : s ∈ hfin_a.toFinset := by
            rw [Set.Finite.mem_toFinset]
            exact ⟨hsZ, has, lt_trans hsts hτsb⟩
          exact absurd (hτs_min s hsE) (not_le.mpr hsts)
        -- `f t₁ = f a`
        have hft1 : f t₁ = f a := by
          rcases le_total a t₁ with hle | hle
          · have h := zfree_const hloc a t₁ hle ?_
            · exact h.symm
            · intro t h1 h2
              rcases eq_or_lt_of_le h1 with h | h
              · rw [← h]; exact ha
              · rcases eq_or_lt_of_le h2 with h' | h'
                · rw [h']; exact ht1Z
                · exact haτs_free t h (lt_trans h' ht1lt)
          · have h := zfree_const hloc t₁ a hle ?_
            · exact h
            · intro t h1 h2
              rcases eq_or_lt_of_le h1 with h | h
              · rw [← h]; exact ht1Z
              · rcases eq_or_lt_of_le h2 with h' | h'
                · rw [h']; exact ha
                · intro htZ
                  have hg : t = τs := hgap t h (by linarith) htZ
                  linarith
        -- `f b - f t₂` is the sum over the remaining points
        have hfin_b : (Z ∩ Set.Ioo t₂ b).Finite := finite_inter_Ioo_periodic Z hZper hZfin t₂ b
        have hstep : f b - f t₂ = ∑ τ ∈ hfin_b.toFinset, J τ := by
          rcases lt_or_ge t₂ b with hlt | hge
          · have hE' : Z ∩ Set.Ioo t₂ b = (Z ∩ Set.Ioo a b) \ {τs} := by
              ext y; constructor
              · rintro ⟨hyZ, hy1, hy2⟩
                exact ⟨⟨hyZ, by linarith, hy2⟩,
                  fun hcon => absurd (hcon ▸ hy1) (not_lt.mpr (le_of_lt htlt2))⟩
              · rintro ⟨⟨hyZ, hy1, hy2⟩, hyne⟩
                have hyE : y ∈ hfin_a.toFinset := by
                  rw [Set.Finite.mem_toFinset]; exact ⟨hyZ, hy1, hy2⟩
                have hτsy : τs < y := lt_of_le_of_ne (hτs_min y hyE) (Ne.symm hyne)
                have hlt2 : t₂ < y := by
                  by_contra hcon
                  rcases eq_or_lt_of_le (not_lt.mp hcon) with h | h
                  · exact ht2Z (h ▸ hyZ)
                  · exact absurd (hgap y (by linarith) (by linarith) hyZ) (by linarith)
                exact ⟨hyZ, hlt2, hy2⟩
            have hcardlt : (Z ∩ Set.Ioo t₂ b).ncard < n := by
              have h1 : (Z ∩ Set.Ioo t₂ b).ncard + 1 = n := by
                rw [hE', Set.ncard_sdiff_singleton_add_one hτs_E hfin_a]
                exact hn
              omega
            exact ih (Z ∩ Set.Ioo t₂ b).ncard hcardlt t₂ b ht2Z hb hlt rfl
          · have hsum0 : ∑ τ ∈ hfin_b.toFinset, J τ = 0 := by
              apply Finset.sum_eq_zero
              intro τ hτ
              rw [Set.Finite.mem_toFinset] at hτ
              exfalso
              linarith [hτ.2.1, hτ.2.2, hge]
            rw [hsum0]
            have hfbt2 : f b = f t₂ := by
              have h := zfree_const hloc b t₂ hge ?_
              · exact h
              · intro t h1 h2
                rcases eq_or_lt_of_le h1 with h | h
                · rw [← h]; exact hb
                · rcases eq_or_lt_of_le h2 with h' | h'
                  · rw [h']; exact ht2Z
                  · intro htZ
                    have hg : t = τs := hgap t (by linarith) h' htZ
                    linarith
            rw [hfbt2]; ring
        -- split the sum at `τs`
        have hnotmem : τs ∉ hfin_b.toFinset := by
          rw [Set.Finite.mem_toFinset]
          exact fun h => absurd h.2.1 (not_lt.mpr (le_of_lt htlt2))
        have hFset : (finite_inter_Ioo_periodic Z hZper hZfin a b).toFinset
            = insert τs hfin_b.toFinset := by
          ext y
          rw [Set.Finite.mem_toFinset, Finset.mem_insert, Set.Finite.mem_toFinset]
          constructor
          · intro hy
            by_cases hyτ : y = τs
            · exact Or.inl hyτ
            · refine Or.inr ⟨hy.1, ?_, hy.2.2⟩
              by_contra hcon
              have hyE : y ∈ hfin_a.toFinset := by
                rw [Set.Finite.mem_toFinset]; exact hy
              have hτsy : τs < y :=
                lt_of_le_of_ne (hτs_min y hyE) (Ne.symm hyτ)
              rcases eq_or_lt_of_le (not_lt.mp hcon) with h | h
              · exact ht2Z (h ▸ hy.1)
              · exact absurd (hgap y (by linarith) (by linarith) hy.1) hyτ
          · rintro (rfl | hy)
            · exact hτs_E
            · exact ⟨hy.1, lt_trans (lt_trans haτs htlt2) hy.2.1, hy.2.2⟩
        have hsumA : ∑ τ ∈ (finite_inter_Ioo_periodic Z hZper hZfin a b).toFinset, J τ
            = J τs + ∑ τ ∈ hfin_b.toFinset, J τ := by
          rw [hFset, Finset.sum_insert hnotmem]
        have hmain : f b - f a = J τs + ∑ τ ∈ hfin_b.toFinset, J τ := by
          calc f b - f a = (f t₁ - f a) + (f t₂ - f t₁) + (f b - f t₂) := by ring
            _ = J τs + ∑ τ ∈ hfin_b.toFinset, J τ := by
                  linarith [hft1, hJt.symm, hstep]
        rw [hmain, ← hsumA]
      · -- the window contains no point of `Z`
        have hEempty : Z ∩ Set.Ioo a b = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        have hfa : f b = f a := by
          have h := zfree_const hloc a b (le_of_lt hab) ?_
          · exact h.symm
          · intro t h1 h2 htZ
            rcases eq_or_lt_of_le h1 with h | h
            · exact ha (h.symm ▸ htZ)
            · rcases eq_or_lt_of_le h2 with h' | h'
              · exact hb (h'.symm ▸ htZ)
              · exact absurd (show t ∈ Z ∩ Set.Ioo a b from ⟨htZ, h, h'⟩) (by simp [hEempty])
        have hsum0 : ∑ τ ∈ (finite_inter_Ioo_periodic Z hZper hZfin a b).toFinset, J τ = 0 := by
          apply Finset.sum_eq_zero
          intro τ hτ
          rw [Set.Finite.mem_toFinset] at hτ
          exact absurd hτ (by simp [hEempty])
        rw [hfa, hsum0]
        ring
    intro a b ha hb hab
    exact main (Z ∩ Set.Ioo a b).ncard a b ha hb hab rfl
  -- ## Step 4: conclude the parity.
  have htel := telescope x (x + 1) hxZ hx1Z hxlt
  have hperx : f (x + 1) = f x := hper x
  have hsum0 : ∑ τ ∈ (finite_inter_Ioo_periodic Z hZper hZfin x (x + 1)).toFinset, J τ = 0 := by
    rw [← htel, hperx]; ring
  have hJpm : ∀ τ ∈ (finite_inter_Ioo_periodic Z hZper hZfin x (x + 1)).toFinset,
      J τ = 2 ∨ J τ = -2 := by
    intro τ hτ
    rw [Set.Finite.mem_toFinset] at hτ
    rw [hJ τ hτ.1]
    exact (hW τ hτ.1).2.2.2.2.2
  have heven : Even (finite_inter_Ioo_periodic Z hZper hZfin x (x + 1)).toFinset.card :=
    even_card_of_sum_eq_zero_two _ J hJpm hsum0
  have hcard : (finite_inter_Ioo_periodic Z hZper hZfin x (x + 1)).toFinset.card
      = (Z ∩ Set.Ioo x (x + 1)).ncard :=
    (Set.ncard_eq_toFinset_card (Z ∩ Set.Ioo x (x + 1))
      (finite_inter_Ioo_periodic Z hZper hZfin x (x + 1))).symm
  rw [hcard] at heven
  rwa [ncard_shift_periodic hZper hZfin hx_mem hxZ hx1Z] at heven

end Work.Drive
