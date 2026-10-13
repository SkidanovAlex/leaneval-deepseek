import Mathlib

namespace Work.WilC4

/-- The left germ of `T` at `a` contains a full left-neighbourhood of `a`. -/
def LeftCovers (T : Set ℝ) (a : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ Set.Ioo (a - ε) a ⊆ T

/-- The left germ of `T` at `a` avoids a full left-neighbourhood of `a`. -/
def LeftAvoids (T : Set ℝ) (a : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioo (a - ε) a, z ∉ T

/-- The right germ of `T` at `a` contains a full right-neighbourhood of `a`. -/
def RightCovers (T : Set ℝ) (a : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ Set.Ioo a (a + ε) ⊆ T

/-- The right germ of `T` at `a` avoids a full right-neighbourhood of `a`. -/
def RightAvoids (T : Set ℝ) (a : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioo a (a + ε), z ∉ T

lemma LeftCovers.mono {T U : Set ℝ} {a : ℝ} (hc : LeftCovers T a) (h : T ⊆ U) :
    LeftCovers U a := by
  obtain ⟨ε, hε, hsub⟩ := hc
  exact ⟨ε, hε, hsub.trans h⟩

lemma RightCovers.mono {T U : Set ℝ} {a : ℝ} (hc : RightCovers T a) (h : T ⊆ U) :
    RightCovers U a := by
  obtain ⟨ε, hε, hsub⟩ := hc
  exact ⟨ε, hε, hsub.trans h⟩

/-- An ord-connected (i.e. interval) set has the left-germ dichotomy at every point. -/
lemma ordConnected_left_germ {T : Set ℝ} (hT : T.OrdConnected) (a : ℝ) :
    LeftCovers T a ∨ LeftAvoids T a := by
  by_cases h : ∃ x : ℝ, x < a ∧ Set.Ioo x a ⊆ T
  · obtain ⟨x, hx, hsub⟩ := h
    refine Or.inl ⟨a - x, by linarith, ?_⟩
    rwa [show a - (a - x) = x from by ring]
  · by_cases hz : ∃ z : ℝ, z < a ∧ z ∈ T
    · obtain ⟨z, hza, hzT⟩ := hz
      have hsub : ¬ (Set.Ioo z a ⊆ T) := fun hs => h ⟨z, hza, hs⟩
      rw [Set.not_subset] at hsub
      obtain ⟨w, hwa, hwT⟩ := hsub
      -- `z < w < a`, `w ∉ T`; convexity gives that `(w, a)` avoids `T`.
      refine Or.inr ⟨a - w, by linarith [hwa.2], ?_⟩
      intro u hu huT
      rw [show a - (a - w) = w from by ring] at hu
      exact hwT (hT.out' hzT huT ⟨le_of_lt hwa.1, le_of_lt hu.1⟩)
    · refine Or.inr ⟨1, by norm_num, ?_⟩
      intro y hy hyT
      exact hz ⟨y, hy.2, hyT⟩

/-- An ord-connected (i.e. interval) set has the right-germ dichotomy at every point. -/
lemma ordConnected_right_germ {T : Set ℝ} (hT : T.OrdConnected) (a : ℝ) :
    RightCovers T a ∨ RightAvoids T a := by
  by_cases h : ∃ x : ℝ, a < x ∧ Set.Ioo a x ⊆ T
  · obtain ⟨x, hx, hsub⟩ := h
    refine Or.inl ⟨x - a, by linarith, ?_⟩
    rwa [show a + (x - a) = x from by ring]
  · by_cases hz : ∃ z : ℝ, a < z ∧ z ∈ T
    · obtain ⟨z, haz, hzT⟩ := hz
      have hsub : ¬ (Set.Ioo a z ⊆ T) := fun hs => h ⟨z, haz, hs⟩
      rw [Set.not_subset] at hsub
      obtain ⟨w, hwa, hwT⟩ := hsub
      -- `a < w < z`, `w ∉ T`; convexity gives that `(a, w)` avoids `T`.
      refine Or.inr ⟨w - a, by linarith [hwa.1], ?_⟩
      intro u hu huT
      rw [show a + (w - a) = w from by ring] at hu
      exact hwT (hT.out' huT hzT ⟨le_of_lt hu.2, le_of_lt hwa.2⟩)
    · refine Or.inr ⟨1, by norm_num, ?_⟩
      intro y hy hyT
      exact hz ⟨y, hy.1, hyT⟩

lemma finUnion_left_germ (s : Finset (Set ℝ)) (a : ℝ) :
    (∀ I ∈ s, I.OrdConnected) →
      LeftCovers (⋃₀ (s : Set (Set ℝ))) a ∨ LeftAvoids (⋃₀ (s : Set (Set ℝ))) a := by
  induction s using Finset.induction_on with
  | empty =>
      intro _
      refine Or.inr ⟨1, by norm_num, ?_⟩
      intro z hz
      simp
  | insert I t hIt ih =>
      intro hconn
      have hI : I.OrdConnected := hconn I (Finset.mem_insert_self I t)
      have ht : ∀ J ∈ t, J.OrdConnected :=
        fun J hJ => hconn J (Finset.mem_insert_of_mem hJ)
      have hUnion : ⋃₀ ((insert I t : Finset (Set ℝ)) : Set (Set ℝ))
          = I ∪ ⋃₀ (t : Set (Set ℝ)) := by
        rw [Finset.coe_insert, Set.sUnion_insert]
      rcases ordConnected_left_germ hI a with hc | ha
      · refine Or.inl ?_
        rw [hUnion]
        exact hc.mono (Set.subset_union_left)
      · rcases ih ht with hct | hat
        · refine Or.inl ?_
          rw [hUnion]
          exact hct.mono (Set.subset_union_right)
        · refine Or.inr ?_
          rw [hUnion]
          obtain ⟨ε₁, hε₁, ha₁⟩ := ha
          obtain ⟨ε₂, hε₂, ha₂⟩ := hat
          refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
          intro z hz hmem
          have hz₁ : z ∈ Set.Ioo (a - ε₁) a :=
            ⟨by linarith [min_le_left ε₁ ε₂, hz.1], hz.2⟩
          have hz₂ : z ∈ Set.Ioo (a - ε₂) a :=
            ⟨by linarith [min_le_right ε₁ ε₂, hz.1], hz.2⟩
          rcases hmem with hmem | hmem
          · exact ha₁ z hz₁ hmem
          · exact ha₂ z hz₂ hmem

lemma finUnion_right_germ (s : Finset (Set ℝ)) (a : ℝ) :
    (∀ I ∈ s, I.OrdConnected) →
      RightCovers (⋃₀ (s : Set (Set ℝ))) a ∨ RightAvoids (⋃₀ (s : Set (Set ℝ))) a := by
  induction s using Finset.induction_on with
  | empty =>
      intro _
      refine Or.inr ⟨1, by norm_num, ?_⟩
      intro z hz
      simp
  | insert I t hIt ih =>
      intro hconn
      have hI : I.OrdConnected := hconn I (Finset.mem_insert_self I t)
      have ht : ∀ J ∈ t, J.OrdConnected :=
        fun J hJ => hconn J (Finset.mem_insert_of_mem hJ)
      have hUnion : ⋃₀ ((insert I t : Finset (Set ℝ)) : Set (Set ℝ))
          = I ∪ ⋃₀ (t : Set (Set ℝ)) := by
        rw [Finset.coe_insert, Set.sUnion_insert]
      rcases ordConnected_right_germ hI a with hc | ha
      · refine Or.inl ?_
        rw [hUnion]
        exact hc.mono (Set.subset_union_left)
      · rcases ih ht with hct | hat
        · refine Or.inl ?_
          rw [hUnion]
          exact hct.mono (Set.subset_union_right)
        · refine Or.inr ?_
          rw [hUnion]
          obtain ⟨ε₁, hε₁, ha₁⟩ := ha
          obtain ⟨ε₂, hε₂, ha₂⟩ := hat
          refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
          intro z hz hmem
          have hz₁ : z ∈ Set.Ioo a (a + ε₁) :=
            ⟨hz.1, by linarith [min_le_left ε₁ ε₂, hz.2]⟩
          have hz₂ : z ∈ Set.Ioo a (a + ε₂) :=
            ⟨hz.1, by linarith [min_le_right ε₁ ε₂, hz.2]⟩
          rcases hmem with hmem | hmem
          · exact ha₁ z hz₁ hmem
          · exact ha₂ z hz₂ hmem

theorem finUnionOrd_germ {S : Set ℝ}
    (hS : ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧ S = ⋃₀ (s : Set (Set ℝ)))
    (a : ℝ) :
    ((∃ ε : ℝ, 0 < ε ∧ Set.Ioo (a - ε) a ⊆ S) ∨
        (∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioo (a - ε) a, z ∉ S)) ∧
      ((∃ ε : ℝ, 0 < ε ∧ Set.Ioo a (a + ε) ⊆ S) ∨
        (∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioo a (a + ε), z ∉ S)) := by
  rcases hS with ⟨s, hconn, rfl⟩
  exact ⟨by simpa only [LeftCovers, LeftAvoids] using finUnion_left_germ s a hconn,
    by simpa only [RightCovers, RightAvoids] using finUnion_right_germ s a hconn⟩

end Work.WilC4
