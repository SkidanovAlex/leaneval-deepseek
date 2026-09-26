import Mathlib.Analysis.Normed.Order.Lattice

open Set

namespace Commons.Topology.Order

/-- If `s` is preconnected and `x < y` are points of `s`, then `f` is strictly monotone (in one
of the two directions) on the closed interval spanned by `x`, `a` and `y`, `b`, where `a < b`
are two given points of `s`. -/
private lemma mono_antiOn_on_Icc_of_anchor {s : Set ℝ} (hs : IsPreconnected s) {f : ℝ → ℝ}
    (hcont : ContinuousOn f s) (hinj : InjOn f s) {a b x y : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) :
    StrictMonoOn f (Icc (min x a) (max y b)) ∨ StrictAntiOn f (Icc (min x a) (max y b)) := by
  have hmin : min x a ∈ s := by
    rcases le_total x a with hxa | hax
    · simpa [min_eq_left hxa] using hx
    · simpa [min_eq_right hax] using ha
  have hmax : max y b ∈ s := by
    rcases le_total y b with hyb | hby
    · simpa [max_eq_right hyb] using hb
    · simpa [max_eq_left hby] using hy
  have hsub : Icc (min x a) (max y b) ⊆ s := hs.Icc_subset hmin hmax
  have hmn : min x a ≤ max y b :=
    le_trans (min_le_left x a) (le_trans (le_of_lt hxy) (le_max_left y b))
  exact ContinuousOn.strictMonoOn_of_injOn_Icc' (a := min x a) (b := max y b) hmn
    (hcont.mono hsub) (hinj.mono hsub)

/-- Given two points `a < b` of a preconnected set `s` with `f a < f b`, a continuous injective
`f` is strictly increasing on `s`. -/
private lemma strictMonoOn_of_anchor {s : Set ℝ} (hs : IsPreconnected s) {f : ℝ → ℝ}
    (hcont : ContinuousOn f s) (hinj : InjOn f s) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a < b) (hfab : f a < f b) : StrictMonoOn f s := by
  intro x hx y hy hxy
  have hdich : StrictMonoOn f (Icc (min x a) (max y b)) ∨
      StrictAntiOn f (Icc (min x a) (max y b)) :=
    mono_antiOn_on_Icc_of_anchor hs hcont hinj ha hb hx hy hxy
  rcases hdich with hmono | hanti
  · exact hmono
      (mem_Icc.mpr ⟨min_le_left x a, le_trans (le_of_lt hxy) (le_max_left y b)⟩)
      (mem_Icc.mpr ⟨le_trans (min_le_left x a) (le_of_lt hxy), le_max_left y b⟩)
      hxy
  · exfalso
    have hba : f b < f a := hanti
      (mem_Icc.mpr ⟨min_le_right x a, le_trans (le_of_lt hab) (le_max_right y b)⟩)
      (mem_Icc.mpr ⟨le_trans (min_le_right x a) (le_of_lt hab), le_max_right y b⟩)
      hab
    exact (lt_asymm hfab) hba

/-- Given two points `a < b` of a preconnected set `s` with `f b < f a`, a continuous injective
`f` is strictly decreasing on `s`. -/
private lemma strictAntiOn_of_anchor {s : Set ℝ} (hs : IsPreconnected s) {f : ℝ → ℝ}
    (hcont : ContinuousOn f s) (hinj : InjOn f s) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a < b) (hba : f b < f a) : StrictAntiOn f s := by
  intro x hx y hy hxy
  have hdich : StrictMonoOn f (Icc (min x a) (max y b)) ∨
      StrictAntiOn f (Icc (min x a) (max y b)) :=
    mono_antiOn_on_Icc_of_anchor hs hcont hinj ha hb hx hy hxy
  rcases hdich with hmono | hanti
  · exfalso
    have habf : f a < f b := hmono
      (mem_Icc.mpr ⟨min_le_right x a, le_trans (le_of_lt hab) (le_max_right y b)⟩)
      (mem_Icc.mpr ⟨le_trans (min_le_right x a) (le_of_lt hab), le_max_right y b⟩)
      hab
    exact (lt_asymm hba) habf
  · exact hanti
      (mem_Icc.mpr ⟨min_le_left x a, le_trans (le_of_lt hxy) (le_max_left y b)⟩)
      (mem_Icc.mpr ⟨le_trans (min_le_left x a) (le_of_lt hxy), le_max_left y b⟩)
      hxy

theorem strictMonoOn_or_strictAntiOn_of_continuousOn_injOn {s : Set ℝ}
    (hs : IsPreconnected s) {f : ℝ → ℝ} (hcont : ContinuousOn f s)
    (hinj : InjOn f s) : StrictMonoOn f s ∨ StrictAntiOn f s := by
  by_cases h : ∃ a ∈ s, ∃ b ∈ s, a < b
  · rcases h with ⟨a, ha, b, hb, hab⟩
    have hne : f a ≠ f b := by
      intro hfab
      exact (ne_of_lt hab) (hinj ha hb hfab)
    rcases lt_or_gt_of_ne hne with habf | hbaf
    · exact Or.inl (strictMonoOn_of_anchor hs hcont hinj ha hb hab habf)
    · exact Or.inr (strictAntiOn_of_anchor hs hcont hinj ha hb hab hbaf)
  · exact Or.inl (by
      intro x hx y hy hxy
      exact False.elim (h ⟨x, hx, y, hy, hxy⟩))

end Commons.Topology.Order