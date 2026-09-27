import Mathlib
import Submission.Work.Whitney.PathTools.exists_arc_of_isPathConnected
import Submission.Work.Whitney.PathTools.isPathConnected_compl_finite
import Submission.Work.Whitney.PathTools.isPathConnected_compl_arc_union_finite

/-!
# Two disjoint arcs avoiding a finite set in a compact connected manifold

Main statement: `Work.Whitney.exists_disjoint_arcs_avoiding_finite`.

Proof strategy. Put `F := D \ {p₁,p₂,q₁,q₂}`.

* `W₁ := (F ∪ {p₂,q₂})ᶜ` is open (complement of a finite set) and path connected
  (`PathTools.isPathConnected_compl_finite`), so `PathTools.exists_arc_of_isPathConnected`
  gives an injective arc `γ₁ : p₁ → q₁` with image in `W₁`.
* By `PathTools.isPathConnected_compl_arc_union_finite`, `M \ (γ₁ '' [0,1] ∪ F)` is path
  connected, so the same lemma gives an injective arc `γ₂ : p₂ → q₂` avoiding
  `γ₁ '' [0,1] ∪ F`.
* The two images are disjoint; `γ₁` can only meet `D` at `p₁` or `q₁` (parameters `0`,`1`), and
  `γ₂` only at `p₂` or `q₂`.
-/

namespace Work.Whitney

open Set Topology

theorem exists_disjoint_arcs_avoiding_finite {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (D : Set M) (hD : D.Finite)
    (p₁ p₂ q₁ q₂ : M) (h₁ : p₁ ≠ p₂) (h₂ : q₁ ≠ q₂) (h₃ : p₁ ≠ q₁) (h₄ : p₁ ≠ q₂)
    (h₅ : p₂ ≠ q₁) (h₆ : p₂ ≠ q₂) :
    ∃ γ₁ γ₂ : ℝ → M,
      Continuous γ₁ ∧ Continuous γ₂ ∧ γ₁ 0 = p₁ ∧ γ₁ 1 = q₁ ∧ γ₂ 0 = p₂ ∧ γ₂ 1 = q₂ ∧
      Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1) ∧ Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ D → t = 0 ∨ t = 1) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ D → t = 0 ∨ t = 1) ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) := by
  -- The finite set of points of `D` other than the four given points.
  set F : Set M := D \ ({p₁, p₂, q₁, q₂} : Set M) with hFdef
  have hFfin : F.Finite := hD.sdiff
  have hfour : ({p₁, p₂, q₁, q₂} : Set M).Finite :=
    (((Set.finite_singleton q₂).insert q₁).insert p₂).insert p₁
  have hpair : ({p₂, q₂} : Set M).Finite := (Set.finite_singleton q₂).insert p₂
  -- `γ₁` will be built inside `W₁`.
  set W₁ : Set M := (F ∪ {p₂, q₂})ᶜ with hW₁def
  have hW₁open : IsOpen W₁ := by
    rw [hW₁def]
    exact (hFfin.union hpair).isClosed.isOpen_compl
  have hW₁conn : IsPathConnected W₁ := by
    rw [hW₁def]
    exact PathTools.isPathConnected_compl_finite (n := n) (by omega) (F ∪ {p₂, q₂}) (hFfin.union hpair)
  have hmemW₁ : ∀ z : M, z ∈ W₁ ↔ z ∉ F ∧ z ≠ p₂ ∧ z ≠ q₂ := by
    intro z
    rw [hW₁def]
    constructor
    · intro h
      exact ⟨fun hc => h (Or.inl hc), fun hc => h (Or.inr (by simp [hc])),
        fun hc => h (Or.inr (by simp [hc]))⟩
    · rintro ⟨h1, h2, h3⟩ (h | h)
      · exact h1 h
      · rcases (by simpa using h : z = p₂ ∨ z = q₂) with h' | h'
        · exact h2 h'
        · exact h3 h'
  have hp₁W₁ : p₁ ∈ W₁ := by
    rw [hmemW₁]; exact ⟨by rw [hFdef]; simp, h₁, h₄⟩
  have hq₁W₁ : q₁ ∈ W₁ := by
    rw [hmemW₁]; exact ⟨by rw [hFdef]; simp, fun h => h₅ h.symm, h₂⟩
  obtain ⟨γ₁, hγ₁c, hγ₁inj, hγ₁0, hγ₁1, hγ₁W⟩ :=
    PathTools.exists_arc_of_isPathConnected (n := n) (M := M) hW₁open hW₁conn hp₁W₁ hq₁W₁ h₃
  have hγ₁not : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₁ t ∉ F ∧ γ₁ t ≠ p₂ ∧ γ₁ t ≠ q₂ :=
    fun t ht => (hmemW₁ (γ₁ t)).mp (hγ₁W t ht)
  -- `γ₂` will be built inside `W₂`.
  set W₂ : Set M := (γ₁ '' Set.Icc (0 : ℝ) 1 ∪ F)ᶜ with hW₂def
  have hmemW₂ : ∀ z : M, z ∈ W₂ ↔ z ∉ γ₁ '' Set.Icc (0 : ℝ) 1 ∧ z ∉ F := by
    intro z
    rw [hW₂def]
    constructor
    · intro h
      exact ⟨fun hc => h (Or.inl hc), fun hc => h (Or.inr hc)⟩
    · rintro ⟨h1, h2⟩ (h | h)
      · exact h1 h
      · exact h2 h
  have hp₂W₂ : p₂ ∈ W₂ := by
    rw [hmemW₂]
    exact ⟨fun hc => (hγ₁not _ hc.choose_spec.1).2.1 hc.choose_spec.2, by rw [hFdef]; simp⟩
  have hq₂W₂ : q₂ ∈ W₂ := by
    rw [hmemW₂]
    exact ⟨fun hc => (hγ₁not _ hc.choose_spec.1).2.2 hc.choose_spec.2, by rw [hFdef]; simp⟩
  have hW₂conn : IsPathConnected W₂ := by
    rw [hW₂def]
    exact PathTools.isPathConnected_compl_arc_union_finite (n := n) hn hγ₁c hγ₁inj F hFfin
  have hW₂open : IsOpen W₂ := by
    rw [hW₂def]
    exact ((isCompact_Icc.image hγ₁c).isClosed.union hFfin.isClosed).isOpen_compl
  obtain ⟨γ₂, hγ₂c, hγ₂inj, hγ₂0, hγ₂1, hγ₂W⟩ :=
    PathTools.exists_arc_of_isPathConnected (n := n) (M := M) hW₂open hW₂conn hp₂W₂ hq₂W₂ h₆
  have hγ₂not : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₂ t ∉ γ₁ '' Set.Icc (0 : ℝ) 1 ∧ γ₂ t ∉ F :=
    fun t ht => (hmemW₂ (γ₂ t)).mp (hγ₂W t ht)
  -- Membership in the four-point set, given membership in `D` but not in `F`.
  have hfour_of : ∀ z ∈ D, z ∉ F → z ∈ ({p₁, p₂, q₁, q₂} : Set M) := by
    intro z hzD hzF
    by_contra hcon
    exact hzF (by rw [hFdef]; exact ⟨hzD, hcon⟩)
  refine ⟨γ₁, γ₂, hγ₁c, hγ₂c, hγ₁0, hγ₁1, hγ₂0, hγ₂1, hγ₁inj, hγ₂inj, ?_, ?_, ?_⟩
  · intro t ht htD
    obtain ⟨hnotF, hnotp₂, hnotq₂⟩ := hγ₁not t ht
    have hmem := hfour_of (γ₁ t) htD hnotF
    simp only [mem_insert_iff, mem_singleton_iff] at hmem
    rcases hmem with h | h | h | h
    · exact Or.inl (hγ₁inj ht (by norm_num) (by rw [hγ₁0, h]))
    · exact absurd h hnotp₂
    · exact Or.inr (hγ₁inj ht (by norm_num) (by rw [hγ₁1, h]))
    · exact absurd h hnotq₂
  · intro t ht htD
    obtain ⟨hnotact, hnotF⟩ := hγ₂not t ht
    have hmem := hfour_of (γ₂ t) htD hnotF
    simp only [mem_insert_iff, mem_singleton_iff] at hmem
    rcases hmem with h | h | h | h
    · exact absurd (⟨0, by norm_num, by rw [hγ₁0]; exact h.symm⟩ : γ₂ t ∈ γ₁ '' Set.Icc (0 : ℝ) 1) hnotact
    · exact Or.inl (hγ₂inj ht (by norm_num) (by rw [hγ₂0, h]))
    · exact absurd (⟨1, by norm_num, by rw [hγ₁1]; exact h.symm⟩ : γ₂ t ∈ γ₁ '' Set.Icc (0 : ℝ) 1) hnotact
    · exact Or.inr (hγ₂inj ht (by norm_num) (by rw [hγ₂1, h]))
  · intro s hs t ht hst
    exact absurd (hst ▸ ⟨s, hs, rfl⟩ : γ₂ t ∈ γ₁ '' Set.Icc (0 : ℝ) 1) (hγ₂not t ht).1

end Work.Whitney
