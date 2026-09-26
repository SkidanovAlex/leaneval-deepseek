import Mathlib

namespace Work.Drive.Final

open Set

/-- Convexity of a half space cut out by a combination of the two coordinates of `T ξ`. -/
private lemma convex_pos_comb (T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (c₁ c₂ : ℝ) :
    Convex ℝ {ξ : ℝ × ℝ | 0 < c₁ * (T ξ).1 + c₂ * (T ξ).2} := by
  intro ξ hξ η hη a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hξ hη ⊢
  have key : c₁ * (T (a • ξ + b • η)).1 + c₂ * (T (a • ξ + b • η)).2
      = a * (c₁ * (T ξ).1 + c₂ * (T ξ).2) + b * (c₁ * (T η).1 + c₂ * (T η).2) := by
    rw [map_add, map_smul, map_smul]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [key]
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have hb1 : b = 1 := by linarith
    rw [← ha0, zero_mul, zero_add, hb1, one_mul]
    exact hη
  · exact lt_of_lt_of_le (mul_pos ha0 hξ) (le_add_of_nonneg_right (mul_nonneg hb hη.le))

/-- A convex set is either empty or path connected. -/
private lemma eq_empty_or_isPathConnected_of_convex {U : Set (ℝ × ℝ)} (hU : Convex ℝ U) :
    U = ∅ ∨ IsPathConnected U := by
  rcases U.eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · exact Or.inr (hU.isPathConnected h)

/-- The union of two convex sets meeting in a point is path connected. -/
private lemma isPathConnected_union_of_convex {U W : Set (ℝ × ℝ)} (hU : Convex ℝ U)
    (hW : Convex ℝ W) (h : (U ∩ W).Nonempty) : IsPathConnected (U ∪ W) :=
  IsPathConnected.union (hU.isPathConnected (h.mono Set.inter_subset_left))
    (hW.isPathConnected (h.mono Set.inter_subset_right)) h

/-- Two convex pieces meeting a path connected piece cover a set of the form `B ∩ (P ∪ (C₁ ∪ C₂))`
by two pieces which are empty or path connected. -/
private lemma cover_of_convex_pair {B P C₁ C₂ : Set (ℝ × ℝ)} (hB : Convex ℝ B)
    (hP : IsPathConnected (B ∩ P)) (hC₁ : Convex ℝ C₁) (hC₂ : Convex ℝ C₂)
    (hpt : ∃ ξ, ξ ∈ B ∧ ξ ∈ P ∧ ξ ∈ C₁) :
    ∃ S₁ S₂ : Set (ℝ × ℝ), (S₁ = ∅ ∨ IsPathConnected S₁) ∧ (S₂ = ∅ ∨ IsPathConnected S₂) ∧
      S₁ ∪ S₂ = B ∩ (P ∪ (C₁ ∪ C₂)) := by
  obtain ⟨ξ₀, hB₀, hP₀, hC₀⟩ := hpt
  refine ⟨(B ∩ P) ∪ (B ∩ C₁), B ∩ C₂, Or.inr ?_,
    eq_empty_or_isPathConnected_of_convex (hB.inter hC₂), ?_⟩
  · exact IsPathConnected.union hP ((hB.inter hC₁).isPathConnected ⟨ξ₀, hB₀, hC₀⟩)
      ⟨ξ₀, ⟨hB₀, hP₀⟩, ⟨hB₀, hC₀⟩⟩
  · rw [Set.inter_union_distrib_left, Set.inter_union_distrib_left, Set.union_assoc]

/-- The set of points of the open square at which `V` is positive is path connected: the positive
set of `V` is a union of rows which are upwards closed in the first variable and each row contains
the vertical line over `xstar`. -/
private lemma row_pathConnected {δ : ℝ} (hδ : 0 < δ) {xstar : ℝ}
    (hxstar : xstar ∈ Set.Ioo (-δ) δ) {V : ℝ × ℝ → ℝ}
    (hmono : ∀ x x' y : ℝ, x ∈ Set.Ioo (-δ) δ → x' ∈ Set.Ioo x δ → y ∈ Set.Ioo (-δ) δ →
      0 < V (x, y) → 0 < V (x', y))
    (htall : ∀ y ∈ Set.Ioo (-δ) δ, 0 < V (xstar, y)) :
    IsPathConnected
      ((Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ) ∩ {ξ : ℝ × ℝ | 0 < V ξ}) := by
  have h0 : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hrow_all : ∀ y ∈ Set.Ioo (-δ) δ, ∀ b ∈ Set.Ioo (-δ) δ,
      xstar ≤ b → 0 < V (b, y) := by
    intro y hy b hb hxb
    rcases eq_or_lt_of_le hxb with h | h
    · rw [← h]; exact htall y hy
    · exact hmono xstar b y hxstar ⟨h, hb.2⟩ hy (htall y hy)
  have hrow_right : ∀ y ∈ Set.Ioo (-δ) δ, ∀ a ∈ Set.Ioo (-δ) δ, 0 < V (a, y) →
      ∀ b ∈ Set.Ioo (-δ) δ, a ≤ b → 0 < V (b, y) := by
    intro y hy a ha hVa b hb hab
    rcases eq_or_lt_of_le hab with h | h
    · rw [← h]; exact hVa
    · exact hmono a b y ha ⟨h, hb.2⟩ hy hVa
  refine ⟨(xstar, 0), ⟨⟨hxstar, h0⟩, htall 0 h0⟩, ?_⟩
  rintro ⟨x, y⟩ ⟨⟨hx, hy⟩, hVxy⟩
  have h1 : JoinedIn ((Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ) ∩ {ξ : ℝ × ℝ | 0 < V ξ})
      (x, y) (xstar, y) := by
    refine ⟨Path.segment (x, y) (xstar, y), ?_⟩
    intro t
    rw [Path.segment_apply, AffineMap.lineMap_apply_module]
    have hpt : (1 - (t : ℝ)) • ((x, y) : ℝ × ℝ) + (t : ℝ) • ((xstar, y) : ℝ × ℝ)
        = ((1 - (t : ℝ)) * x + (t : ℝ) * xstar, y) := by
      simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
      ext <;> ring
    rw [hpt]
    have hwI : (1 - (t : ℝ)) * x + (t : ℝ) * xstar ∈ Set.Ioo (-δ) δ := by
      have hconv := (convex_Ioo (-δ) δ) hx hxstar
        (show (0:ℝ) ≤ 1 - (t:ℝ) by linarith [unitInterval.le_one t])
        (show (0:ℝ) ≤ (t:ℝ) by exact unitInterval.nonneg t)
        (show (1 - (t:ℝ)) + (t:ℝ) = 1 by ring)
      simpa [smul_eq_mul] using hconv
    have hVw : 0 < V ((1 - (t : ℝ)) * x + (t : ℝ) * xstar, y) := by
      rcases lt_trichotomy x xstar with hlt | heq | hgt
      · have hle : x ≤ (1 - (t : ℝ)) * x + (t : ℝ) * xstar := by
          have h1 : (0:ℝ) ≤ (t:ℝ) := unitInterval.nonneg t
          have h2 : (0:ℝ) ≤ xstar - x := by linarith [hlt.le]
          nlinarith [mul_nonneg h1 h2]
        exact hrow_right y hy x hx hVxy _ hwI hle
      · rw [heq]
        rw [show (1 - (t:ℝ)) * xstar + (t:ℝ) * xstar = xstar by ring]
        exact htall y hy
      · have hle : xstar ≤ (1 - (t : ℝ)) * x + (t : ℝ) * xstar := by
          have h1 : (0:ℝ) ≤ 1 - (t:ℝ) := by linarith [unitInterval.le_one t]
          have h2 : (0:ℝ) ≤ x - xstar := by linarith [hgt.le]
          nlinarith [mul_nonneg h1 h2]
        exact hrow_all y hy _ hwI hle
    exact ⟨⟨hwI, hy⟩, hVw⟩
  have h2 : JoinedIn ((Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ) ∩ {ξ : ℝ × ℝ | 0 < V ξ})
      (xstar, y) (xstar, 0) := by
    refine ⟨Path.segment (xstar, y) (xstar, 0), ?_⟩
    intro t
    rw [Path.segment_apply, AffineMap.lineMap_apply_module]
    have hpt : (1 - (t : ℝ)) • ((xstar, y) : ℝ × ℝ) + (t : ℝ) • ((xstar, 0) : ℝ × ℝ)
        = (xstar, (1 - (t : ℝ)) * y) := by
      simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
      ext <;> ring
    rw [hpt]
    have hyI : (1 - (t : ℝ)) * y ∈ Set.Ioo (-δ) δ := by
      have hconv := (convex_Ioo (-δ) δ) hy h0
        (show (0:ℝ) ≤ 1 - (t:ℝ) by linarith [unitInterval.le_one t])
        (show (0:ℝ) ≤ (t:ℝ) by exact unitInterval.nonneg t)
        (show (1 - (t:ℝ)) + (t:ℝ) = 1 by ring)
      simpa [smul_eq_mul] using hconv
    exact ⟨⟨hxstar, hyI⟩, htall _ hyI⟩
  exact (h1.trans h2).symm

/-- The point `(δ/2, δ/2)` is in the first quadrant pieces and in the square. -/
private lemma mid_hi_mem (δ : ℝ) (hδ : 0 < δ) :
    ((δ/2, δ/2) : ℝ × ℝ) ∈ (Set.Ioi (0:ℝ) ×ˢ (Set.univ : Set ℝ)) ∧
    ((δ/2, δ/2) : ℝ × ℝ) ∈ ((Set.univ : Set ℝ) ×ˢ Set.Ioi (0:ℝ)) ∧
    ((δ/2, δ/2) : ℝ × ℝ) ∈ (Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true]; linarith
  · simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and]; linarith
  · simp only [Set.mem_prod, Set.mem_Ioo]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The point `(-δ/2, -δ/2)` is in the third quadrant pieces and in the square. -/
private lemma mid_lo_mem (δ : ℝ) (hδ : 0 < δ) :
    ((-δ/2, -δ/2) : ℝ × ℝ) ∈ (Set.Iio (0:ℝ) ×ˢ (Set.univ : Set ℝ)) ∧
    ((-δ/2, -δ/2) : ℝ × ℝ) ∈ ((Set.univ : Set ℝ) ×ˢ Set.Iio (0:ℝ)) ∧
    ((-δ/2, -δ/2) : ℝ × ℝ) ∈ (Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Set.mem_prod, Set.mem_Iio, Set.mem_univ, and_true]; linarith
  · simp only [Set.mem_prod, Set.mem_univ, Set.mem_Iio, true_and]; linarith
  · simp only [Set.mem_prod, Set.mem_Ioo]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem gateFace (δ : ℝ) (hδ : 0 < δ) (xstar : ℝ) (hxstar : xstar ∈ Set.Ioo (-δ) δ)
    (V : ℝ × ℝ → ℝ) (hV0 : V 0 = 0)
    (hmono : ∀ x x' y : ℝ, x ∈ Set.Ioo (-δ) δ → x' ∈ Set.Ioo x δ → y ∈ Set.Ioo (-δ) δ →
      0 < V (x, y) → 0 < V (x', y))
    (htall : ∀ y ∈ Set.Ioo (-δ) δ, 0 < V (xstar, y))
    (T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (hTinj : Function.Injective T)
    (s₁ s₂ : ℝ) (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (hmeet1 : s₁ = 1 → s₂ = -1 → ∃ ξ ∈ Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ,
      0 < V ξ ∧ |(T ξ).2| < |(T ξ).1|)
    (hmeet2 : s₁ = -1 → s₂ = 1 → ∃ ξ ∈ Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ,
      0 < V ξ ∧ |(T ξ).1| < |(T ξ).2|) :
    ∃ S₁ S₂ : Set (ℝ × ℝ), (S₁ = ∅ ∨ IsPathConnected S₁) ∧ (S₂ = ∅ ∨ IsPathConnected S₂) ∧
      S₁ ∪ S₂ = (Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ) ∩
        ({ξ | 0 < V ξ} ∪ {ξ | 0 < s₁ * (T ξ).1 ^ 2 + s₂ * (T ξ).2 ^ 2}) := by
  have hBc : Convex ℝ (Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ) :=
    (convex_Ioo (-δ) δ).prod (convex_Ioo (-δ) δ)
  have hPpc : IsPathConnected
      ((Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ) ∩ {ξ : ℝ × ℝ | 0 < V ξ}) :=
    row_pathConnected hδ hxstar hmono htall
  have hPsub : {ξ : ℝ × ℝ | 0 < V ξ} ⊆ ({0}ᶜ : Set (ℝ × ℝ)) := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    rw [hV0] at hp
    exact absurd hp (lt_irrefl 0)
  rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl
  · -- s₁ = 1, s₂ = 1
    refine ⟨(Set.Ioi (0:ℝ) ×ˢ (Set.univ : Set ℝ) ∪ (Set.univ : Set ℝ) ×ˢ Set.Ioi (0:ℝ)) ∩
              (Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ),
            (Set.Iio (0:ℝ) ×ˢ (Set.univ : Set ℝ) ∪ (Set.univ : Set ℝ) ×ˢ Set.Iio (0:ℝ)) ∩
              (Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ), ?_, ?_, ?_⟩
    · refine Or.inr ?_
      rw [Set.union_inter_distrib_right]
      refine isPathConnected_union_of_convex ?_ ?_ ?_
      · exact ((convex_Ioi (0:ℝ)).prod convex_univ).inter hBc
      · exact (convex_univ.prod (convex_Ioi (0:ℝ))).inter hBc
      · obtain ⟨h1, h2, h3⟩ := mid_hi_mem δ hδ
        exact ⟨(δ/2, δ/2), ⟨h1, h3⟩, ⟨h2, h3⟩⟩
    · refine Or.inr ?_
      rw [Set.union_inter_distrib_right]
      refine isPathConnected_union_of_convex ?_ ?_ ?_
      · exact ((convex_Iio (0:ℝ)).prod convex_univ).inter hBc
      · exact (convex_univ.prod (convex_Iio (0:ℝ))).inter hBc
      · obtain ⟨h1, h2, h3⟩ := mid_lo_mem δ hδ
        exact ⟨(-δ/2, -δ/2), ⟨h1, h3⟩, ⟨h2, h3⟩⟩
    · have hQ11 : ({ξ : ℝ × ℝ | 0 < (1:ℝ) * (T ξ).1 ^ 2 + (1:ℝ) * (T ξ).2 ^ 2} : Set (ℝ × ℝ))
          = {0}ᶜ := by
        ext ξ
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
        have hsq : (1:ℝ) * (T ξ).1 ^ 2 + (1:ℝ) * (T ξ).2 ^ 2
            = (T ξ).1 ^ 2 + (T ξ).2 ^ 2 := by ring
        rw [hsq]
        constructor
        · rintro h rfl
          simp at h
        · intro hne
          have hT : T ξ ≠ 0 := fun h => hne (hTinj (by rw [h, map_zero]))
          by_cases h1 : (T ξ).1 = 0
          · have h2 : (T ξ).2 ≠ 0 := fun h2 => hT (Prod.ext h1 h2)
            have := sq_pos_of_ne_zero h2
            nlinarith [sq_nonneg (T ξ).1]
          · have := sq_pos_of_ne_zero h1
            nlinarith [sq_nonneg (T ξ).2]
      have hbig11 : (((Set.Ioi (0:ℝ) ×ˢ (Set.univ : Set ℝ) ∪
            (Set.univ : Set ℝ) ×ˢ Set.Ioi (0:ℝ)) ∪
          (Set.Iio (0:ℝ) ×ˢ (Set.univ : Set ℝ) ∪
            (Set.univ : Set ℝ) ×ˢ Set.Iio (0:ℝ))) : Set (ℝ × ℝ)) = {0}ᶜ := by
        ext p
        simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, true_and,
          Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_Ioi, Set.mem_Iio]
        constructor
        · rintro h hp0
          rw [hp0] at h
          simp at h
        · intro hp
          rcases lt_trichotomy p.1 0 with h | h | h
          · exact Or.inr (Or.inl h)
          · have h2 : p.2 ≠ 0 := fun h2 => hp (Prod.ext h h2)
            rcases lt_trichotomy p.2 0 with h3 | h3 | h3
            · exact Or.inr (Or.inr h3)
            · exact absurd h3 h2
            · exact Or.inl (Or.inr h3)
          · exact Or.inl (Or.inl h)
      have hsub : (Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ) ∩ {ξ : ℝ × ℝ | 0 < V ξ} ⊆
          (Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ) ∩ ({0}ᶜ : Set (ℝ × ℝ)) :=
        fun x hx => ⟨hx.1, hPsub hx.2⟩
      rw [← Set.union_inter_distrib_right, hbig11, hQ11, Set.inter_union_distrib_left,
        Set.union_eq_right.mpr hsub]
      exact Set.inter_comm _ _
  · -- s₁ = 1, s₂ = -1
    obtain ⟨ξ₀, hξ₀B, hξ₀V, hξ₀abs⟩ := hmeet1 rfl rfl
    have hQ : ({ξ : ℝ × ℝ | 0 < (1:ℝ) * (T ξ).1 ^ 2 + (-1:ℝ) * (T ξ).2 ^ 2} : Set (ℝ × ℝ))
        = ({ξ : ℝ × ℝ | 0 < (1:ℝ) * (T ξ).1 + (1:ℝ) * (T ξ).2} ∩
           {ξ : ℝ × ℝ | 0 < (1:ℝ) * (T ξ).1 + (-1:ℝ) * (T ξ).2}) ∪
          ({ξ : ℝ × ℝ | 0 < (-1:ℝ) * (T ξ).1 + (-1:ℝ) * (T ξ).2} ∩
           {ξ : ℝ × ℝ | 0 < (-1:ℝ) * (T ξ).1 + (1:ℝ) * (T ξ).2}) := by
      ext ξ
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff]
      have key : (1:ℝ) * (T ξ).1 ^ 2 + (-1:ℝ) * (T ξ).2 ^ 2
          = ((1:ℝ) * (T ξ).1 + (1:ℝ) * (T ξ).2) *
            ((1:ℝ) * (T ξ).1 + (-1:ℝ) * (T ξ).2) := by ring
      rw [key, mul_pos_iff]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨by linarith, by linarith⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨by linarith, by linarith⟩
    have hξ₀Q : (0:ℝ) < (1:ℝ) * (T ξ₀).1 ^ 2 + (-1:ℝ) * (T ξ₀).2 ^ 2 := by
      have h := sq_lt_sq.mpr hξ₀abs
      nlinarith [h]
    have hξ₀C : ξ₀ ∈ ({ξ : ℝ × ℝ | 0 < (1:ℝ) * (T ξ).1 + (1:ℝ) * (T ξ).2} ∩
           {ξ : ℝ × ℝ | 0 < (1:ℝ) * (T ξ).1 + (-1:ℝ) * (T ξ).2}) ∪
          ({ξ : ℝ × ℝ | 0 < (-1:ℝ) * (T ξ).1 + (-1:ℝ) * (T ξ).2} ∩
           {ξ : ℝ × ℝ | 0 < (-1:ℝ) * (T ξ).1 + (1:ℝ) * (T ξ).2}) := by
      rw [← hQ]
      exact hξ₀Q
    rcases hξ₀C with hC | hC
    · obtain ⟨S₁, S₂, hS₁, hS₂, hun⟩ := cover_of_convex_pair hBc hPpc
        ((convex_pos_comb T 1 1).inter (convex_pos_comb T 1 (-1)))
        ((convex_pos_comb T (-1) (-1)).inter (convex_pos_comb T (-1) 1))
        ⟨ξ₀, hξ₀B, hξ₀V, hC⟩
      exact ⟨S₁, S₂, hS₁, hS₂, by rw [hQ]; exact hun⟩
    · have hQ' : ({ξ : ℝ × ℝ | 0 < (1:ℝ) * (T ξ).1 ^ 2 + (-1:ℝ) * (T ξ).2 ^ 2} : Set (ℝ × ℝ))
          = ({ξ : ℝ × ℝ | 0 < (-1:ℝ) * (T ξ).1 + (-1:ℝ) * (T ξ).2} ∩
             {ξ : ℝ × ℝ | 0 < (-1:ℝ) * (T ξ).1 + (1:ℝ) * (T ξ).2}) ∪
            ({ξ : ℝ × ℝ | 0 < (1:ℝ) * (T ξ).1 + (1:ℝ) * (T ξ).2} ∩
             {ξ : ℝ × ℝ | 0 < (1:ℝ) * (T ξ).1 + (-1:ℝ) * (T ξ).2}) :=
        hQ.trans (Set.union_comm _ _)
      obtain ⟨S₁, S₂, hS₁, hS₂, hun⟩ := cover_of_convex_pair hBc hPpc
        ((convex_pos_comb T (-1) (-1)).inter (convex_pos_comb T (-1) 1))
        ((convex_pos_comb T 1 1).inter (convex_pos_comb T 1 (-1)))
        ⟨ξ₀, hξ₀B, hξ₀V, hC⟩
      exact ⟨S₁, S₂, hS₁, hS₂, by rw [hQ']; exact hun⟩
  · -- s₁ = -1, s₂ = 1
    obtain ⟨ξ₀, hξ₀B, hξ₀V, hξ₀abs⟩ := hmeet2 rfl rfl
    have hQ : ({ξ : ℝ × ℝ | 0 < (-1:ℝ) * (T ξ).1 ^ 2 + (1:ℝ) * (T ξ).2 ^ 2} : Set (ℝ × ℝ))
        = ({ξ : ℝ × ℝ | 0 < (1:ℝ) * (T ξ).1 + (1:ℝ) * (T ξ).2} ∩
           {ξ : ℝ × ℝ | 0 < (-1:ℝ) * (T ξ).1 + (1:ℝ) * (T ξ).2}) ∪
          ({ξ : ℝ × ℝ | 0 < (-1:ℝ) * (T ξ).1 + (-1:ℝ) * (T ξ).2} ∩
           {ξ : ℝ × ℝ | 0 < (1:ℝ) * (T ξ).1 + (-1:ℝ) * (T ξ).2}) := by
      ext ξ
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff]
      have key : (-1:ℝ) * (T ξ).1 ^ 2 + (1:ℝ) * (T ξ).2 ^ 2
          = ((1:ℝ) * (T ξ).1 + (1:ℝ) * (T ξ).2) *
            ((-1:ℝ) * (T ξ).1 + (1:ℝ) * (T ξ).2) := by ring
      rw [key, mul_pos_iff]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨by linarith, by linarith⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨by linarith, by linarith⟩
    have hξ₀Q : (0:ℝ) < (-1:ℝ) * (T ξ₀).1 ^ 2 + (1:ℝ) * (T ξ₀).2 ^ 2 := by
      have h := sq_lt_sq.mpr hξ₀abs
      nlinarith [h]
    have hξ₀C : ξ₀ ∈ ({ξ : ℝ × ℝ | 0 < (1:ℝ) * (T ξ).1 + (1:ℝ) * (T ξ).2} ∩
           {ξ : ℝ × ℝ | 0 < (-1:ℝ) * (T ξ).1 + (1:ℝ) * (T ξ).2}) ∪
          ({ξ : ℝ × ℝ | 0 < (-1:ℝ) * (T ξ).1 + (-1:ℝ) * (T ξ).2} ∩
           {ξ : ℝ × ℝ | 0 < (1:ℝ) * (T ξ).1 + (-1:ℝ) * (T ξ).2}) := by
      rw [← hQ]
      exact hξ₀Q
    rcases hξ₀C with hC | hC
    · obtain ⟨S₁, S₂, hS₁, hS₂, hun⟩ := cover_of_convex_pair hBc hPpc
        ((convex_pos_comb T 1 1).inter (convex_pos_comb T (-1) 1))
        ((convex_pos_comb T (-1) (-1)).inter (convex_pos_comb T 1 (-1)))
        ⟨ξ₀, hξ₀B, hξ₀V, hC⟩
      exact ⟨S₁, S₂, hS₁, hS₂, by rw [hQ]; exact hun⟩
    · have hQ' : ({ξ : ℝ × ℝ | 0 < (-1:ℝ) * (T ξ).1 ^ 2 + (1:ℝ) * (T ξ).2 ^ 2} : Set (ℝ × ℝ))
          = ({ξ : ℝ × ℝ | 0 < (-1:ℝ) * (T ξ).1 + (-1:ℝ) * (T ξ).2} ∩
             {ξ : ℝ × ℝ | 0 < (1:ℝ) * (T ξ).1 + (-1:ℝ) * (T ξ).2}) ∪
            ({ξ : ℝ × ℝ | 0 < (1:ℝ) * (T ξ).1 + (1:ℝ) * (T ξ).2} ∩
             {ξ : ℝ × ℝ | 0 < (-1:ℝ) * (T ξ).1 + (1:ℝ) * (T ξ).2}) :=
        hQ.trans (Set.union_comm _ _)
      obtain ⟨S₁, S₂, hS₁, hS₂, hun⟩ := cover_of_convex_pair hBc hPpc
        ((convex_pos_comb T (-1) (-1)).inter (convex_pos_comb T 1 (-1)))
        ((convex_pos_comb T 1 1).inter (convex_pos_comb T (-1) 1))
        ⟨ξ₀, hξ₀B, hξ₀V, hC⟩
      exact ⟨S₁, S₂, hS₁, hS₂, by rw [hQ']; exact hun⟩
  · -- s₁ = -1, s₂ = -1
    have hQe : ({ξ : ℝ × ℝ | 0 < (-1:ℝ) * (T ξ).1 ^ 2 + (-1:ℝ) * (T ξ).2 ^ 2} : Set (ℝ × ℝ))
        = ∅ := by
      ext ξ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      nlinarith [sq_nonneg (T ξ).1, sq_nonneg (T ξ).2]
    exact ⟨(Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ) ∩ {ξ : ℝ × ℝ | 0 < V ξ}, ∅,
      Or.inr hPpc, Or.inl rfl, by rw [hQe, Set.union_empty, Set.union_empty]⟩

end Work.Drive.Final
