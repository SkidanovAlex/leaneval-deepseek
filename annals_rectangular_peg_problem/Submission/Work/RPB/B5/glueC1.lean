import Mathlib
import Submission.Work.RPB.B5.withinFderivMatching
import Submission.Work.RPB.B5.glueC1SeamAux

open scoped ContDiff Topology
open Filter Set

namespace Work.RPB.B5

/-- Helper: the half box `Ioc a x₀ × univ` is a neighbourhood of any point lying in its
interior (first coordinate `< x₀`). -/
private lemma memS₁_of_lt {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (a x₀ : ℝ) {z : ℝ × P} (haz : a < z.1) (hzx : z.1 < x₀) :
    (Set.Ioc a x₀ ×ˢ (Set.univ : Set P)) ∈ 𝓝 z :=
  Filter.mem_of_superset
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨haz, hzx⟩, mem_univ z.2⟩)
    (fun y hy => ⟨Set.mem_Ioc.mpr ⟨hy.1.1, le_of_lt hy.1.2⟩, Set.mem_univ y.2⟩)

/-- Helper: the half box `Icc x₀ b × univ` is a neighbourhood of any point lying in its
interior (first coordinate `> x₀`). -/
private lemma memS₂_of_gt {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (x₀ b : ℝ) {z : ℝ × P} (hxz : x₀ < z.1) (hzb : z.1 < b) :
    (Set.Icc x₀ b ×ˢ (Set.univ : Set P)) ∈ 𝓝 z :=
  Filter.mem_of_superset
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨hxz, hzb⟩, mem_univ z.2⟩)
    (fun y hy => ⟨Set.mem_Icc.mpr ⟨le_of_lt hy.1.1, le_of_lt hy.1.2⟩, Set.mem_univ y.2⟩)

/-- `Ioc a x₀ × univ ∪ Icc x₀ b × univ = Ioc a b × univ` for `a < x₀ < b`. -/
private lemma halfBoxes_union {P : Type*} (a b x₀ : ℝ) (ha : a < x₀) (hb : x₀ < b) :
    (Set.Ioc a x₀ ×ˢ (Set.univ : Set P)) ∪ (Set.Icc x₀ b ×ˢ (Set.univ : Set P))
      = Set.Ioc a b ×ˢ (Set.univ : Set P) := by
  ext y
  simp only [Set.mem_union, Set.mem_prod, Set.mem_Ioc, Set.mem_Icc, Set.mem_univ, and_true]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, le_trans h2 (le_of_lt hb)⟩
    · exact ⟨lt_of_lt_of_le ha h1, h2⟩
  · rintro ⟨h1, h2⟩
    rcases le_total y.1 x₀ with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨h, h2⟩

theorem glueC1 {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : ℝ × P → E) (a b x₀ : ℝ) (ha : a < x₀) (hb : x₀ < b)
    (hu : ContDiffOn ℝ 1 u (Set.Ioc a x₀ ×ˢ Set.univ))
    (hv : ContDiffOn ℝ 1 v (Set.Icc x₀ b ×ˢ Set.univ))
    (hval : ∀ p, u (x₀, p) = v (x₀, p))
    (hder : ∀ p, derivWithin (fun x : ℝ => u (x, p)) (Set.Iic x₀) x₀
              = derivWithin (fun x : ℝ => v (x, p)) (Set.Ici x₀) x₀) :
    ContDiffOn ℝ 1 (fun z : ℝ × P => if z.1 ≤ x₀ then u z else v z) (Set.Ioo a b ×ˢ Set.univ) := by
  set S₁ : Set (ℝ × P) := Set.Ioc a x₀ ×ˢ (Set.univ : Set P) with hS₁
  set S₂ : Set (ℝ × P) := Set.Icc x₀ b ×ˢ (Set.univ : Set P) with hS₂
  set T : Set (ℝ × P) := Set.Ioo a b ×ˢ (Set.univ : Set P) with hT
  set f : ℝ × P → E := (fun z : ℝ × P => if z.1 ≤ x₀ then u z else v z) with hf
  have huS₁ : ContDiffOn ℝ 1 u S₁ := by rw [hS₁]; exact hu
  have hvS₂ : ContDiffOn ℝ 1 v S₂ := by rw [hS₂]; exact hv
  have hxS₁ : ∀ p, (x₀, p) ∈ S₁ := fun p => by
    rw [hS₁]; exact ⟨Set.mem_Ioc.mpr ⟨ha, le_rfl⟩, mem_univ p⟩
  have hxS₂ : ∀ p, (x₀, p) ∈ S₂ := fun p => by
    rw [hS₂]; exact ⟨Set.mem_Icc.mpr ⟨le_rfl, le_of_lt hb⟩, mem_univ p⟩
  -- the glued function agrees with `u` on `S₁` and with `v` on `S₂`
  have hfS₁ : Set.EqOn f u S₁ := by
    intro y hy
    rw [hS₁] at hy
    change (if y.1 ≤ x₀ then u y else v y) = u y
    exact ite_eq_left hy.1.2
  have hfS₂ : Set.EqOn f v S₂ := by
    intro y hy
    rw [hS₂] at hy
    change (if y.1 ≤ x₀ then u y else v y) = v y
    rcases lt_or_eq_of_le hy.1.1 with hlt | heq
    · exact ite_eq_right (not_le.mpr hlt)
    · rw [ite_eq_left (le_of_eq heq.symm)]
      rw [show y = (x₀, y.2) from by ext <;> simp [heq]]
      exact hval y.2
  -- matching of the two within-derivatives at the seam
  have hmatch : ∀ p, fderivWithin ℝ u S₁ (x₀, p) = fderivWithin ℝ v S₂ (x₀, p) := by
    intro p
    refine withinFderivMatching u v a b x₀ ha hb hval hder p _ _ ?_ ?_
    · exact ((huS₁.differentiableOn one_ne_zero) (x₀, p) (hxS₁ p)).hasFDerivWithinAt
    · exact ((hvS₂.differentiableOn one_ne_zero) (x₀, p) (hxS₂ p)).hasFDerivWithinAt
  -- the glued function is differentiable at the seam with the common value
  have hglue : ∀ p, HasFDerivAt f (fderivWithin ℝ u S₁ (x₀, p)) (x₀, p) := by
    intro p
    have h1 : HasFDerivWithinAt u (fderivWithin ℝ u S₁ (x₀, p)) S₁ (x₀, p) :=
      ((huS₁.differentiableOn one_ne_zero) (x₀, p) (hxS₁ p)).hasFDerivWithinAt
    have h1f : HasFDerivWithinAt f (fderivWithin ℝ u S₁ (x₀, p)) S₁ (x₀, p) :=
      h1.congr hfS₁ (by
        change (if (x₀, p).1 ≤ x₀ then u (x₀, p) else v (x₀, p)) = u (x₀, p)
        exact ite_eq_left le_rfl)
    have h2 : HasFDerivWithinAt v (fderivWithin ℝ v S₂ (x₀, p)) S₂ (x₀, p) :=
      ((hvS₂.differentiableOn one_ne_zero) (x₀, p) (hxS₂ p)).hasFDerivWithinAt
    have h2f : HasFDerivWithinAt f (fderivWithin ℝ u S₁ (x₀, p)) S₂ (x₀, p) := by
      have h2f' : HasFDerivWithinAt f (fderivWithin ℝ v S₂ (x₀, p)) S₂ (x₀, p) :=
        h2.congr hfS₂ (by
          change (if (x₀, p).1 ≤ x₀ then u (x₀, p) else v (x₀, p)) = v (x₀, p)
          exact (ite_eq_left le_rfl).trans (hval p))
      simpa only [hmatch p] using h2f'
    have hmem : (S₁ ∪ S₂) ∈ 𝓝 (x₀, p) := by
      have hsub : (Set.Ioo a b ×ˢ (Set.univ : Set P)) ⊆ (S₁ ∪ S₂) := by
        intro y hy
        rw [show S₁ ∪ S₂ = Set.Ioc a b ×ˢ (Set.univ : Set P) from by
          rw [hS₁, hS₂]; exact halfBoxes_union a b x₀ ha hb]
        exact ⟨Set.mem_Ioc.mpr ⟨hy.1.1, le_of_lt hy.1.2⟩, hy.2⟩
      exact Filter.mem_of_superset
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨ha, hb⟩, mem_univ p⟩) hsub
    exact (h1f.union h2f).hasFDerivAt hmem
  -- differentiability of the glued function on the open set
  have hdiff : DifferentiableOn ℝ f T := by
    intro z hz
    rw [hT] at hz
    rcases lt_trichotomy z.1 x₀ with hlt | heq | hgt
    · have hzu : ContDiffAt ℝ 1 u z :=
        ContDiffOn.contDiffAt huS₁ (memS₁_of_lt a x₀ hz.1.1 hlt)
      have hcf : DifferentiableAt ℝ f z :=
        hzu.differentiableAt one_ne_zero |>.congr_of_eventuallyEq (by
          filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hlt] with y hy
          change (if y.1 ≤ x₀ then u y else v y) = u y
          exact ite_eq_left (le_of_lt hy))
      exact hcf.differentiableWithinAt
    · have hz_eq : z = (x₀, z.2) := by ext <;> simp [heq]
      rw [hz_eq]
      exact (hglue z.2).differentiableAt.differentiableWithinAt
    · have hzv : ContDiffAt ℝ 1 v z :=
        ContDiffOn.contDiffAt hvS₂ (memS₂_of_gt x₀ b hgt hz.1.2)
      have hcf : DifferentiableAt ℝ f z :=
        hzv.differentiableAt one_ne_zero |>.congr_of_eventuallyEq (by
          filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hgt] with y hy
          change (if y.1 ≤ x₀ then u y else v y) = v y
          exact ite_eq_right (not_le.mpr hy))
      exact hcf.differentiableWithinAt
  -- continuity of the derivative of the glued function
  have hcont : ContinuousOn (fun y => fderiv ℝ f y) T := by
    intro z hz
    rw [hT] at hz
    rcases lt_trichotomy z.1 x₀ with hlt | heq | hgt
    · have hzu : ContDiffAt ℝ 1 u z :=
        ContDiffOn.contDiffAt huS₁ (memS₁_of_lt a x₀ hz.1.1 hlt)
      have hcf : ContDiffAt ℝ 1 f z := hzu.congr_of_eventuallyEq (by
        filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hlt] with y hy
        change (if y.1 ≤ x₀ then u y else v y) = u y
        exact ite_eq_left (le_of_lt hy))
      exact (hcf.continuousAt_fderiv one_ne_zero).continuousWithinAt
    · have hz_eq : z = (x₀, z.2) := by ext <;> simp [heq]
      have hthis := seamContinuousFderivAux u v a b x₀ ha hb hu hv hmatch hglue z.2
      rw [hz_eq]
      simpa only [hf, hT] using hthis
    · have hzv : ContDiffAt ℝ 1 v z :=
        ContDiffOn.contDiffAt hvS₂ (memS₂_of_gt x₀ b hgt hz.1.2)
      have hcf : ContDiffAt ℝ 1 f z := hzv.congr_of_eventuallyEq (by
        filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hgt] with y hy
        change (if y.1 ≤ x₀ then u y else v y) = v y
        exact ite_eq_right (not_le.mpr hy))
      exact (hcf.continuousAt_fderiv one_ne_zero).continuousWithinAt
  have hTopen : IsOpen T := by rw [hT]; exact isOpen_Ioo.prod isOpen_univ
  have hmain : ContDiffOn ℝ (0 + 1 : ℕ∞ω) f T :=
    (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := (0 : ℕ∞ω)) (f := f) (s := T) hTopen).mpr
      ⟨hdiff, (fun h => by simp at h), contDiffOn_zero.mpr hcont⟩
  rw [show (0 : ℕ∞ω) + 1 = 1 from by simp] at hmain
  simpa only [hf, hT] using hmain

end Work.RPB.B5
