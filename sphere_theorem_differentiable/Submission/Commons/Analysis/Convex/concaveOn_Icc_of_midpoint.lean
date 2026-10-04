import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Convex

/-- A continuous function on `[0,1]` which is midpoint-concave and vanishes at the endpoints is
nonnegative on `[0,1]`. -/
theorem midpointConcave_nonneg {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Icc (0:ℝ) 1))
    (hmid : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      (φ x + φ y) / 2 ≤ φ ((x + y) / 2))
    (h0 : φ 0 = 0) (h1 : φ 1 = 0) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ φ t := by
  intro t ht
  obtain ⟨x0, hx0mem, hx0min⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr zero_le_one) hcont
  have hx0min' : ∀ y ∈ Set.Icc (0:ℝ) 1, φ x0 ≤ φ y := fun y hy => hx0min hy
  have hx0ge : 0 ≤ x0 := hx0mem.1
  have hx0le : x0 ≤ 1 := hx0mem.2
  have hgoal : 0 ≤ φ x0 := by
    rcases le_or_gt x0 (1 / 2) with hx | hx
    · have h2 : (2 * x0) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
      have hm := hmid 0 (by constructor <;> norm_num) (2 * x0) h2
      have e : (0 + 2 * x0) / 2 = x0 := by ring
      rw [e, h0, zero_add] at hm
      have hmin2 := hx0min' (2 * x0) h2
      linarith
    · have h2 : (2 * x0 - 1) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
      have hm := hmid (2 * x0 - 1) h2 1 (by constructor <;> norm_num)
      have e : (2 * x0 - 1 + 1) / 2 = x0 := by ring
      rw [e, h1, add_zero] at hm
      have hmin2 := hx0min' (2 * x0 - 1) h2
      linarith
  exact hgoal.trans (hx0min' t ht)

/-- The midpoint concavity condition on `[0,T]` upgrades to full concavity of the combination
`a f x + b f y ≤ f (a x + b y)`. -/
theorem concave_combo {f : ℝ → ℝ} {T : ℝ}
    (hcont : ContinuousOn f (Set.Icc (0:ℝ) T))
    (hmid : ∀ x ∈ Set.Icc (0:ℝ) T, ∀ y ∈ Set.Icc (0:ℝ) T,
      (f x + f y) / 2 ≤ f ((x + y) / 2))
    {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) T) (hy : y ∈ Set.Icc (0:ℝ) T)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * f x + b * f y ≤ f (a * x + b * y) := by
  have hb1 : b ≤ 1 := by linarith
  have hba : a = 1 - b := by linarith
  rw [hba]
  let φ : ℝ → ℝ := fun t => f ((1 - t) * x + t * y) - ((1 - t) * f x + t * f y)
  have hφcont : ContinuousOn φ (Set.Icc (0:ℝ) 1) := by
    have hzcont : Continuous fun t : ℝ => (1 - t) * x + t * y := by continuity
    have hmaps : Set.MapsTo (fun t : ℝ => (1 - t) * x + t * y)
        (Set.Icc (0:ℝ) 1) (Set.Icc (0:ℝ) T) := by
      intro t ht
      constructor <;> nlinarith [ht.1, ht.2, hx.1, hx.2, hy.1, hy.2]
    have h1 : ContinuousOn (fun t : ℝ => f ((1 - t) * x + t * y)) (Set.Icc (0:ℝ) 1) :=
      hcont.comp' hzcont.continuousOn hmaps
    have h2 : ContinuousOn (fun t : ℝ => (1 - t) * f x + t * f y) (Set.Icc (0:ℝ) 1) := by
      fun_prop
    exact h1.sub h2
  have hφmid : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ u ∈ Set.Icc (0:ℝ) 1,
      (φ s + φ u) / 2 ≤ φ ((s + u) / 2) := by
    intro s hs u hu
    have hzs : (1 - s) * x + s * y ∈ Set.Icc (0:ℝ) T := by
      constructor <;> nlinarith [hs.1, hs.2, hx.1, hx.2, hy.1, hy.2]
    have hzu : (1 - u) * x + u * y ∈ Set.Icc (0:ℝ) T := by
      constructor <;> nlinarith [hu.1, hu.2, hx.1, hx.2, hy.1, hy.2]
    have hm := hmid ((1 - s) * x + s * y) hzs ((1 - u) * x + u * y) hzu
    have he : ((1 - s) * x + s * y + ((1 - u) * x + u * y)) / 2
        = (1 - (s + u) / 2) * x + (s + u) / 2 * y := by ring
    rw [he] at hm
    have h1 : (φ s + φ u) / 2
        = (f ((1 - s) * x + s * y) + f ((1 - u) * x + u * y)) / 2
          - ((1 - (s + u) / 2) * f x + (s + u) / 2 * f y) := by
      simp only [φ]; ring
    have h2 : φ ((s + u) / 2)
        = f ((1 - (s + u) / 2) * x + (s + u) / 2 * y)
          - ((1 - (s + u) / 2) * f x + (s + u) / 2 * f y) := by
      simp only [φ]
    rw [h1, h2]
    linarith
  have hφ0 : φ 0 = 0 := by simp only [φ]; ring
  have hφ1 : φ 1 = 0 := by simp only [φ]; ring
  have hb01 : b ∈ Set.Icc (0:ℝ) 1 := ⟨hb, hb1⟩
  have hfin := midpointConcave_nonneg hφcont hφmid hφ0 hφ1 b hb01
  simp only [φ] at hfin
  linarith

theorem concaveOn_Icc_of_midpoint {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hcont : ContinuousOn f (Set.Icc 0 T))
    (hmid : ∀ x ∈ Set.Icc (0:ℝ) T, ∀ y ∈ Set.Icc (0:ℝ) T,
      (f x + f y) / 2 ≤ f ((x + y) / 2)) :
    ConcaveOn ℝ (Set.Icc (0:ℝ) T) f := by
  refine ⟨convex_Icc 0 T, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  exact concave_combo hcont hmid hx hy ha hb hab

end Commons.Analysis.Convex