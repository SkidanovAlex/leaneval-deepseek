import Mathlib

open scoped ContDiff Topology
open Filter Set

namespace Work.RPB.B5

private lemma hmemS₁ {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (a x₀ : ℝ) {z : ℝ × P} (haz : a < z.1) (hzx : z.1 < x₀) :
    (Set.Ioc a x₀ ×ˢ (Set.univ : Set P)) ∈ 𝓝 z :=
  Filter.mem_of_superset
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨haz, hzx⟩, mem_univ z.2⟩)
    (fun y hy => ⟨Set.mem_Ioc.mpr ⟨hy.1.1, le_of_lt hy.1.2⟩, Set.mem_univ y.2⟩)

private lemma hmemS₂ {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (x₀ b : ℝ) {z : ℝ × P} (hxz : x₀ < z.1) (hzb : z.1 < b) :
    (Set.Icc x₀ b ×ˢ (Set.univ : Set P)) ∈ 𝓝 z :=
  Filter.mem_of_superset
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨hxz, hzb⟩, mem_univ z.2⟩)
    (fun y hy => ⟨Set.mem_Icc.mpr ⟨le_of_lt hy.1.1, le_of_lt hy.1.2⟩, Set.mem_univ y.2⟩)

theorem seamContinuousFderivAux {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : ℝ × P → E) (a b x₀ : ℝ) (ha : a < x₀) (hb : x₀ < b)
    (hu : ContDiffOn ℝ 1 u (Set.Ioc a x₀ ×ˢ (Set.univ : Set P)))
    (hv : ContDiffOn ℝ 1 v (Set.Icc x₀ b ×ˢ (Set.univ : Set P)))
    (hmatch : ∀ p, fderivWithin ℝ u (Set.Ioc a x₀ ×ˢ (Set.univ : Set P)) (x₀, p)
        = fderivWithin ℝ v (Set.Icc x₀ b ×ˢ (Set.univ : Set P)) (x₀, p))
    (hglue : ∀ p, HasFDerivAt (fun z : ℝ × P => if z.1 ≤ x₀ then u z else v z)
        (fderivWithin ℝ u (Set.Ioc a x₀ ×ˢ (Set.univ : Set P)) (x₀, p)) (x₀, p)) :
    ∀ p, ContinuousWithinAt
      (fun y => fderiv ℝ (fun z : ℝ × P => if z.1 ≤ x₀ then u z else v z) y)
      (Set.Ioo a b ×ˢ (Set.univ : Set P)) (x₀, p) := by
  intro p
  set S₁ : Set (ℝ × P) := Set.Ioc a x₀ ×ˢ (Set.univ : Set P) with hS₁
  set S₂ : Set (ℝ × P) := Set.Icc x₀ b ×ˢ (Set.univ : Set P) with hS₂
  set T : Set (ℝ × P) := Set.Ioo a b ×ˢ (Set.univ : Set P) with hT
  set f : ℝ × P → E := (fun z : ℝ × P => if z.1 ≤ x₀ then u z else v z) with hf
  have huS₁ : ContDiffOn ℝ 1 u S₁ := by rw [hS₁]; exact hu
  have hvS₂ : ContDiffOn ℝ 1 v S₂ := by rw [hS₂]; exact hv
  have hud₁ : UniqueDiffOn ℝ S₁ := by
    rw [hS₁]; exact (uniqueDiffOn_Ioc a x₀).prod uniqueDiffOn_univ
  have hud₂ : UniqueDiffOn ℝ S₂ := by
    rw [hS₂]; exact (uniqueDiffOn_Icc hb).prod uniqueDiffOn_univ
  have hxS₁ : (x₀, p) ∈ S₁ := by rw [hS₁]; exact ⟨Set.mem_Ioc.mpr ⟨ha, le_rfl⟩, mem_univ p⟩
  have hxS₂ : (x₀, p) ∈ S₂ := by rw [hS₂]; exact ⟨Set.mem_Icc.mpr ⟨le_rfl, le_of_lt hb⟩, mem_univ p⟩
  set g : ℝ × P → (ℝ × P →L[ℝ] E) :=
    (fun y : ℝ × P => if y.1 ≤ x₀ then fderivWithin ℝ u S₁ y else fderivWithin ℝ v S₂ y) with hg
  -- `g` computes the derivative of the glued function on `T`
  have hfg : Set.EqOn (fun y => fderiv ℝ f y) g T := by
    rintro ⟨y1, y2⟩ hy
    rw [hT] at hy
    change fderiv ℝ f (y1, y2)
      = (if y1 ≤ x₀ then fderivWithin ℝ u S₁ (y1, y2)
         else fderivWithin ℝ v S₂ (y1, y2))
    rcases lt_trichotomy y1 x₀ with hlt | heq | hgt
    · have hev : f =ᶠ[𝓝 (y1, y2)] u := by
        filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hlt] with w hw
        change (if w.1 ≤ x₀ then u w else v w) = u w
        exact ite_eq_left (le_of_lt hw)
      rw [hev.fderiv_eq, ← fderivWithin_of_mem_nhds (hmemS₁ a x₀ hy.1.1 hlt)]
      exact (ite_eq_left (le_of_lt hlt)).symm
    · subst heq
      rw [(hglue y2).fderiv]
      exact (ite_eq_left le_rfl).symm
    · have hev : f =ᶠ[𝓝 (y1, y2)] v := by
        filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hgt] with w hw
        change (if w.1 ≤ x₀ then u w else v w) = v w
        exact ite_eq_right (not_le.mpr hw)
      rw [hev.fderiv_eq, ← fderivWithin_of_mem_nhds (hmemS₂ x₀ b hgt hy.1.2)]
      exact (ite_eq_right (not_le.mpr hgt)).symm
  have hc₁ : ContinuousWithinAt (fderivWithin ℝ u S₁) S₁ (x₀, p) :=
    (huS₁.continuousOn_fderivWithin hud₁ le_rfl) (x₀, p) hxS₁
  have h1g : ContinuousWithinAt g S₁ (x₀, p) := by
    refine hc₁.congr (fun y hy => ?_) ?_
    · rw [hS₁] at hy
      change (if y.1 ≤ x₀ then fderivWithin ℝ u S₁ y else fderivWithin ℝ v S₂ y)
        = fderivWithin ℝ u S₁ y
      exact ite_eq_left hy.1.2
    · change (if (x₀, p).1 ≤ x₀ then fderivWithin ℝ u S₁ (x₀, p)
        else fderivWithin ℝ v S₂ (x₀, p)) = fderivWithin ℝ u S₁ (x₀, p)
      exact ite_eq_left le_rfl
  have hc₂ : ContinuousWithinAt (fderivWithin ℝ v S₂) S₂ (x₀, p) :=
    (hvS₂.continuousOn_fderivWithin hud₂ le_rfl) (x₀, p) hxS₂
  have h2g : ContinuousWithinAt g S₂ (x₀, p) := by
    refine hc₂.congr (fun y hy => ?_) ?_
    · rw [hS₂] at hy
      change (if y.1 ≤ x₀ then fderivWithin ℝ u S₁ y else fderivWithin ℝ v S₂ y)
        = fderivWithin ℝ v S₂ y
      rcases lt_or_eq_of_le hy.1.1 with hlt | heq
      · exact ite_eq_right (not_le.mpr hlt)
      · rw [ite_eq_left (le_of_eq heq.symm)]
        rw [show y = (x₀, y.2) from by ext <;> simp [heq]]
        exact hmatch y.2
    · change (if (x₀, p).1 ≤ x₀ then fderivWithin ℝ u S₁ (x₀, p)
        else fderivWithin ℝ v S₂ (x₀, p)) = fderivWithin ℝ v S₂ (x₀, p)
      rw [ite_eq_left le_rfl]
      exact hmatch p
  have hunion : ContinuousWithinAt g (S₁ ∪ S₂) (x₀, p) := h1g.union h2g
  have hg_cont : ContinuousWithinAt g T (x₀, p) := by
    refine hunion.mono ?_
    rintro y hy
    rw [hT] at hy
    rw [hS₁, hS₂]
    rcases le_total y.1 x₀ with h | h
    · exact Or.inl ⟨Set.mem_Ioc.mpr ⟨hy.1.1, h⟩, hy.2⟩
    · exact Or.inr ⟨Set.mem_Icc.mpr ⟨h, le_of_lt hy.1.2⟩, hy.2⟩
  have hxT : (x₀, p) ∈ T := by rw [hT]; exact ⟨⟨ha, hb⟩, mem_univ p⟩
  exact hg_cont.congr (fun y hy => hfg hy) (hfg hxT)

end Work.RPB.B5
