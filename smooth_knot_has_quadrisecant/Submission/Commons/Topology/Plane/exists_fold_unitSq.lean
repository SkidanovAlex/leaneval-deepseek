import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice

namespace Commons.Topology.Plane

open Set

open Classical

noncomputable section

/-- The closed unit square in `ℂ`. -/
def foldUnitSq : Set ℂ := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1}

/-- The union of the left, bottom and right edges of the unit square (a "U"-shaped set). -/
def foldUnitSqU : Set ℂ :=
  {z : ℂ | (z.re = 0 ∧ 0 ≤ z.im ∧ z.im ≤ 1) ∨ (z.re = 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1) ∨
           (z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1)}

/-- A parametrization of the `U`-shaped boundary: for `t ∈ [0,3]` it runs from `(0,1)` down the
left edge to `(0,0)`, then along the bottom edge to `(1,0)`, then up the right edge to `(1,1)`. -/
def foldCurve (t : ℝ) : ℂ :=
  ((max 0 (min 1 (t - 1)) : ℝ) : ℂ) + ((max 0 (1 - t) + max 0 (t - 2) : ℝ) : ℂ) * Complex.I

lemma continuous_foldCurve : Continuous foldCurve := by
  unfold foldCurve
  fun_prop

lemma foldCurve_re (t : ℝ) : (foldCurve t).re = max 0 (min 1 (t - 1)) := by simp [foldCurve]

lemma foldCurve_im (t : ℝ) : (foldCurve t).im = max 0 (1 - t) + max 0 (t - 2) := by
  simp [foldCurve]

/-- The parametrized curve lies in the `U`. -/
lemma foldCurve_mem (t : ℝ) (h0 : 0 ≤ t) (h3 : t ≤ 3) : foldCurve t ∈ foldUnitSqU := by
  simp only [foldUnitSqU, Set.mem_ofPred_eq, foldCurve_re, foldCurve_im]
  rcases le_total t 1 with h | h
  · left
    have h1 : t - 1 ≤ (1 : ℝ) := by linarith
    have h2 : t - 1 ≤ (0 : ℝ) := by linarith
    have h4 : t - 2 ≤ (0 : ℝ) := by linarith
    have h5 : (0 : ℝ) ≤ 1 - t := by linarith
    rw [min_eq_right h1, max_eq_left h2, max_eq_right h5, max_eq_left h4]
    exact ⟨by norm_num, by linarith, by linarith⟩
  · rcases le_total t 2 with h' | h'
    · right; right
      have h1 : t - 1 ≤ (1 : ℝ) := by linarith
      have h4 : t - 2 ≤ (0 : ℝ) := by linarith
      have h6 : (0 : ℝ) ≤ t - 1 := by linarith
      have h9 : (1 : ℝ) - t ≤ 0 := by linarith
      rw [min_eq_right h1, max_eq_right h6, max_eq_left h9, max_eq_left h4]
      exact ⟨by norm_num, by linarith, by linarith⟩
    · right; left
      have h7 : (0 : ℝ) ≤ t - 2 := by linarith
      have h8 : (1 : ℝ) ≤ t - 1 := by linarith
      have h9 : (1 : ℝ) - t ≤ 0 := by linarith
      rw [min_eq_left h8, max_eq_right (show (0 : ℝ) ≤ 1 by norm_num), max_eq_left h9,
        max_eq_right h7]
      exact ⟨by norm_num, by linarith, by linarith⟩

/-- `foldCurve (1 - y)` is the point `(0, y)` of the left edge, for `y ≥ 0`. -/
lemma foldCurve_one_sub (y : ℝ) (h0 : 0 ≤ y) : foldCurve (1 - y) = Complex.mk 0 y := by
  have h2 : (1 - y) - 1 ≤ (1 : ℝ) := by linarith
  have h3 : (1 - y) - 1 ≤ (0 : ℝ) := by linarith
  have h4 : (0 : ℝ) ≤ 1 - (1 - y) := by linarith
  have h5 : (1 - y) - 2 ≤ (0 : ℝ) := by linarith
  apply Complex.ext
  · rw [foldCurve_re, min_eq_right h2, max_eq_left h3]
  · rw [foldCurve_im, max_eq_right h4, max_eq_left h5]; ring

/-- `foldCurve (1 + x)` is the point `(x, 0)` of the bottom edge, for `x ∈ [0,1]`. -/
lemma foldCurve_add_one (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    foldCurve (1 + x) = Complex.mk x 0 := by
  have h2 : (1 + x) - 1 ≤ (1 : ℝ) := by linarith
  have h3 : (0 : ℝ) ≤ (1 + x) - 1 := by linarith
  have h4 : 1 - (1 + x) ≤ (0 : ℝ) := by linarith
  have h5 : (1 + x) - 2 ≤ (0 : ℝ) := by linarith
  apply Complex.ext
  · rw [foldCurve_re, min_eq_right h2, max_eq_right h3]; ring
  · rw [foldCurve_im, max_eq_left h4, max_eq_left h5]; simp

/-- `foldCurve (2 + y)` is the point `(1, y)` of the right edge, for `y ≥ 0`. -/
lemma foldCurve_add_two (y : ℝ) (h0 : 0 ≤ y) : foldCurve (2 + y) = Complex.mk 1 y := by
  have h2 : (1 : ℝ) ≤ (2 + y) - 1 := by linarith
  have h3 : 1 - (2 + y) ≤ (0 : ℝ) := by linarith
  have h4 : (0 : ℝ) ≤ (2 + y) - 2 := by linarith
  apply Complex.ext
  · rw [foldCurve_re, min_eq_left h2, max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]
  · rw [foldCurve_im, max_eq_left h3, max_eq_right h4]; ring

/-- A reparametrization of the square: on the left edge it is `1 - y`, on the bottom edge `1 + x`
and on the right edge `2 + y`, so that `foldCurve ∘ foldParam` fixes the whole `U`. -/
def foldParam (z : ℂ) : ℝ := 1 + z.re + z.im * (2 * z.re - 1)

lemma continuous_foldParam : Continuous foldParam := by
  unfold foldParam
  fun_prop

lemma foldParam_mem_Icc (z : ℂ) (hz : z ∈ foldUnitSq) : foldParam z ∈ Set.Icc 0 3 := by
  have h1 : 0 ≤ z.re := hz.1
  have h2 : z.re ≤ 1 := hz.2.1
  have h3 : 0 ≤ z.im := hz.2.2.1
  have h4 : z.im ≤ 1 := hz.2.2.2
  rw [foldParam, Set.mem_Icc]
  rcases le_total z.re (1 / 2) with h | h
  · have hb : 2 * z.re - 1 ≤ 0 := by linarith
    have hm : 1 * (2 * z.re - 1) ≤ z.im * (2 * z.re - 1) := mul_le_mul_of_nonpos_right h4 hb
    have hu : z.im * (2 * z.re - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h3 hb
    constructor <;> nlinarith
  · have hb : (0 : ℝ) ≤ 2 * z.re - 1 := by linarith
    have hm : z.im * (2 * z.re - 1) ≤ 1 * (2 * z.re - 1) := mul_le_mul_of_nonneg_right h4 hb
    have hu : (0 : ℝ) ≤ z.im * (2 * z.re - 1) := mul_nonneg h3 hb
    constructor <;> nlinarith

/-- The fold map: on the square it follows `foldCurve ∘ foldParam`, outside it is the identity. -/
def foldMapUnitSq (z : ℂ) : ℂ := if z ∈ foldUnitSq then foldCurve (foldParam z) else z

lemma foldMapUnitSq_of_mem (z : ℂ) (hz : z ∈ foldUnitSq) :
    foldMapUnitSq z = foldCurve (foldParam z) := by
  simp only [foldMapUnitSq, if_pos hz]

lemma foldMapUnitSq_of_not_mem (z : ℂ) (hz : z ∉ foldUnitSq) : foldMapUnitSq z = z := by
  simp only [foldMapUnitSq, if_neg hz]

lemma continuousOn_foldMapUnitSq : ContinuousOn foldMapUnitSq foldUnitSq := by
  refine (continuous_foldCurve.comp continuous_foldParam).continuousOn.congr ?_
  intro z hz
  exact foldMapUnitSq_of_mem z hz

lemma foldMapUnitSq_mem_unitSqU (z : ℂ) (hz : z ∈ foldUnitSq) :
    foldMapUnitSq z ∈ foldUnitSqU := by
  rw [foldMapUnitSq_of_mem z hz]
  exact foldCurve_mem (foldParam z) (foldParam_mem_Icc z hz).1 (foldParam_mem_Icc z hz).2

lemma foldUnitSqU_subset_foldUnitSq : foldUnitSqU ⊆ foldUnitSq := by
  intro z hz
  rcases hz with ⟨h, h2, h3⟩ | ⟨h, h2, h3⟩ | ⟨h, h2, h3⟩
  · exact ⟨h.ge, by linarith [h], h2, h3⟩
  · exact ⟨by linarith [h], h.le, h2, h3⟩
  · exact ⟨h2, h3, h.ge, by linarith [h]⟩

lemma foldMapUnitSq_fixes (z : ℂ) (hz : z ∈ foldUnitSqU) : foldMapUnitSq z = z := by
  rw [foldMapUnitSq_of_mem z (foldUnitSqU_subset_foldUnitSq hz)]
  rcases hz with ⟨hre, hlo, hhi⟩ | ⟨hre, hlo, hhi⟩ | ⟨him, hlo, hhi⟩
  · have hτ : foldParam z = 1 - z.im := by simp only [foldParam, hre]; ring
    rw [hτ, foldCurve_one_sub z.im hlo]
    exact Complex.ext (by simp [hre]) (by simp)
  · have hτ : foldParam z = 2 + z.im := by simp only [foldParam, hre]; ring
    rw [hτ, foldCurve_add_two z.im hlo]
    exact Complex.ext (by simp [hre]) (by simp)
  · have hτ : foldParam z = 1 + z.re := by simp only [foldParam, him]; ring
    rw [hτ, foldCurve_add_one z.re hlo hhi]
    exact Complex.ext (by simp) (by simp [him])

lemma convex_foldUnitSq : Convex ℝ foldUnitSq := by
  intro x hx y hy a b ha hb hab
  obtain ⟨h1, h2, h3, h4⟩ := hx
  obtain ⟨g1, g2, g3, g4⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> nlinarith

/-- The straight line homotopy from the identity to the fold map. -/
def foldHomUnitSq (p : ℂ × unitInterval) : ℂ :=
  (1 - (p.2 : ℝ)) • p.1 + (p.2 : ℝ) • foldMapUnitSq p.1

lemma continuousOn_foldHomUnitSq : ContinuousOn foldHomUnitSq (foldUnitSq ×ˢ Set.univ) := by
  have hG : Continuous fun p : ℂ × unitInterval =>
      (1 - (p.2 : ℝ)) • p.1 + (p.2 : ℝ) • foldCurve (foldParam p.1) := by
    have hc : Continuous fun p : ℂ × unitInterval => (p.2 : ℝ) :=
      continuous_subtype_val.comp continuous_snd
    have hf : Continuous fun p : ℂ × unitInterval => p.1 := continuous_fst
    exact ((continuous_const.sub hc).smul hf).add
      (hc.smul (continuous_foldCurve.comp (continuous_foldParam.comp hf)))
  refine hG.continuousOn.congr ?_
  intro p hp
  obtain ⟨hp1, -⟩ := hp
  simp only [foldHomUnitSq, foldMapUnitSq_of_mem p.1 hp1]

lemma foldHomUnitSq_mem (z : ℂ) (t : unitInterval) (hz : z ∈ foldUnitSq) :
    foldHomUnitSq (z, t) ∈ foldUnitSq := by
  have hφ : foldMapUnitSq z ∈ foldUnitSq :=
    foldUnitSqU_subset_foldUnitSq (foldMapUnitSq_mem_unitSqU z hz)
  have h1 : (0 : ℝ) ≤ 1 - (t : ℝ) := by have := t.2.2; linarith
  have h2 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have h3 : (1 - (t : ℝ)) + (t : ℝ) = 1 := by ring
  exact convex_foldUnitSq hz hφ h1 h2 h3

lemma foldHomUnitSq_zero (z : ℂ) : foldHomUnitSq (z, (0 : unitInterval)) = z := by
  simp [foldHomUnitSq]

lemma foldHomUnitSq_one (z : ℂ) : foldHomUnitSq (z, (1 : unitInterval)) = foldMapUnitSq z := by
  simp [foldHomUnitSq]

lemma foldHomUnitSq_fixes (z : ℂ) (t : unitInterval) (hz : foldMapUnitSq z = z) :
    foldHomUnitSq (z, t) = z := by
  simp only [foldHomUnitSq, hz]
  rw [sub_smul, one_smul]
  abel

/-- The closed unit square together with a strong deformation retraction onto the union of its
left, bottom and right edges, which is the identity outside the square and off the (relatively)
open top edge.  Concretely: there are `φ : ℂ → ℂ` and a homotopy `H` such that `φ` fixes the
"U" (left ∪ bottom ∪ right edges), maps the square into the U, is the identity outside the square,
and `H` deforms the identity to `φ` while staying in the square and fixing the U.

The intended construction is the radial projection of the square from the point `(1/2, 3/2)`
(the midpoint of the top edge, raised by half a side): every point of the square is pushed away
from that point until it meets the boundary, which is always the left, bottom or right edge. -/
theorem exists_fold_unitSq :
    let unitSq : Set ℂ := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1}
    let unitSqU : Set ℂ :=
      {z : ℂ | (z.re = 0 ∧ 0 ≤ z.im ∧ z.im ≤ 1) ∨ (z.re = 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1) ∨
               (z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1)}
    ∃ (φ : ℂ → ℂ) (H : ℂ × unitInterval → ℂ),
      ContinuousOn φ unitSq ∧
      ContinuousOn H (unitSq ×ˢ Set.univ) ∧
      (∀ z ∈ unitSq, ∀ t : unitInterval, H (z, t) ∈ unitSq) ∧
      (∀ z ∈ unitSq, H (z, (0:unitInterval)) = z) ∧
      (∀ z ∈ unitSq, H (z, (1:unitInterval)) = φ z) ∧
      (∀ z ∈ unitSq, φ z ∈ unitSqU) ∧
      (∀ z ∈ unitSqU, φ z = z) ∧
      (∀ z, z ∉ unitSq → φ z = z) ∧
      (∀ z ∈ unitSqU, ∀ t : unitInterval, H (z, t) = z) ∧
      (∀ z, z ∉ unitSq → ∀ t : unitInterval, H (z, t) = z) := by
  change ∃ (φ : ℂ → ℂ) (H : ℂ × unitInterval → ℂ),
      ContinuousOn φ foldUnitSq ∧
      ContinuousOn H (foldUnitSq ×ˢ Set.univ) ∧
      (∀ z ∈ foldUnitSq, ∀ t : unitInterval, H (z, t) ∈ foldUnitSq) ∧
      (∀ z ∈ foldUnitSq, H (z, (0:unitInterval)) = z) ∧
      (∀ z ∈ foldUnitSq, H (z, (1:unitInterval)) = φ z) ∧
      (∀ z ∈ foldUnitSq, φ z ∈ foldUnitSqU) ∧
      (∀ z ∈ foldUnitSqU, φ z = z) ∧
      (∀ z, z ∉ foldUnitSq → φ z = z) ∧
      (∀ z ∈ foldUnitSqU, ∀ t : unitInterval, H (z, t) = z) ∧
      (∀ z, z ∉ foldUnitSq → ∀ t : unitInterval, H (z, t) = z)
  exact ⟨foldMapUnitSq, foldHomUnitSq, continuousOn_foldMapUnitSq, continuousOn_foldHomUnitSq,
    fun z hz t => foldHomUnitSq_mem z t hz, fun z _ => foldHomUnitSq_zero z,
    fun z _ => foldHomUnitSq_one z, fun z hz => foldMapUnitSq_mem_unitSqU z hz,
    fun z hz => foldMapUnitSq_fixes z hz, fun z hz => foldMapUnitSq_of_not_mem z hz,
    fun z hz t => foldHomUnitSq_fixes z t (foldMapUnitSq_fixes z hz),
    fun z hz t => foldHomUnitSq_fixes z t (foldMapUnitSq_of_not_mem z hz)⟩

end

end Commons.Topology.Plane