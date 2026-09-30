import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.Zeta

private lemma convex_re_gt (θ : ℝ) : Convex ℝ {z : ℂ | θ < z.re} := by
  have hre : IsLinearMap ℝ (fun z : ℂ => z.re) := by
    refine ⟨?_, ?_⟩ <;> simp
  exact (convex_Ioi θ).is_linear_preimage hre

private lemma convex_re_lt (θ : ℝ) : Convex ℝ {z : ℂ | z.re < θ} := by
  have hre : IsLinearMap ℝ (fun z : ℂ => z.re) := by
    refine ⟨?_, ?_⟩ <;> simp
  exact (convex_Iio θ).is_linear_preimage hre

private lemma convex_im_gt (θ : ℝ) : Convex ℝ {z : ℂ | θ < z.im} := by
  have him : IsLinearMap ℝ (fun z : ℂ => z.im) := by
    refine ⟨?_, ?_⟩ <;> simp
  exact (convex_Ioi θ).is_linear_preimage him

private lemma convex_im_lt (θ : ℝ) : Convex ℝ {z : ℂ | z.im < θ} := by
  have him : IsLinearMap ℝ (fun z : ℂ => z.im) := by
    refine ⟨?_, ?_⟩ <;> simp
  exact (convex_Iio θ).is_linear_preimage him

private lemma ne_one_of_re_lt {z : ℂ} (h : z.re < 1) : z ≠ 1 := by
  intro hz
  rw [hz] at h
  norm_num at h

private lemma ne_one_of_one_lt_re {z : ℂ} (h : 1 < z.re) : z ≠ 1 := by
  intro hz
  rw [hz] at h
  norm_num at h

private lemma ne_one_of_pos_im {z : ℂ} (h : 0 < z.im) : z ≠ 1 := by
  intro hz
  rw [hz] at h
  norm_num at h

private lemma ne_one_of_im_neg {z : ℂ} (h : z.im < 0) : z ≠ 1 := by
  intro hz
  rw [hz] at h
  norm_num at h

lemma isPreconnected_re_gt_sdiff {θ : ℝ} (hθ : θ < 1) :
    IsPreconnected {z : ℂ | θ < z.re ∧ z ≠ 1} := by
  let U : Set ℂ := {z : ℂ | θ < z.re ∧ 0 < z.im}
  let L : Set ℂ := {z : ℂ | θ < z.re ∧ z.im < 0}
  let R : Set ℂ := {z : ℂ | 1 < z.re}
  let M : Set ℂ := {z : ℂ | θ < z.re ∧ z.re < 1}
  have hUconv : Convex ℝ U := by
    dsimp [U]
    convert (convex_re_gt θ).inter (convex_im_gt 0) using 1
    ext z
    simp
  have hLconv : Convex ℝ L := by
    dsimp [L]
    convert (convex_re_gt θ).inter (convex_im_lt 0) using 1
    ext z
    simp
  have hRconv : Convex ℝ R := by
    dsimp [R]
    simpa using convex_re_gt 1
  have hMconv : Convex ℝ M := by
    dsimp [M]
    convert (convex_re_gt θ).inter (convex_re_lt 1) using 1
    ext z
    simp
  -- nonemptiness of the pieces
  have hUn : U.Nonempty := by
    refine ⟨(1 : ℂ) + Complex.I, ?_⟩
    dsimp [U]
    constructor <;> simp [hθ]
  have hLn : L.Nonempty := by
    refine ⟨(1 : ℂ) - Complex.I, ?_⟩
    dsimp [L]
    constructor <;> simp [hθ]
  have hRn : R.Nonempty := by
    refine ⟨(2 : ℂ), ?_⟩
    dsimp [R]
    norm_num
  have hMn : M.Nonempty := by
    refine ⟨(((1 + θ) / 2 : ℝ) : ℂ), ?_⟩
    dsimp [M]
    constructor <;> linarith
  -- path connectedness of pieces
  have hU : IsPathConnected U := hUconv.isPathConnected hUn
  have hL : IsPathConnected L := hLconv.isPathConnected hLn
  have hR : IsPathConnected R := hRconv.isPathConnected hRn
  have hM : IsPathConnected M := hMconv.isPathConnected hMn
  -- overlaps
  have hURn : (U ∩ R).Nonempty := by
    refine ⟨(2 : ℂ) + Complex.I, ?_⟩
    dsimp [U, R]
    constructor
    · constructor
      · simp; linarith
      · norm_num
    · norm_num
  have hURLn : ((U ∪ R) ∩ L).Nonempty := by
    refine ⟨(2 : ℂ) - Complex.I, ?_⟩
    dsimp [U, R, L]
    constructor
    · right
      norm_num
    · constructor
      · simp; linarith
      · norm_num
  have hURLMn : (((U ∪ R) ∪ L) ∩ M).Nonempty := by
    refine ⟨(((1 + θ) / 2 : ℝ) : ℂ) + Complex.I, ?_⟩
    dsimp [U, R, L, M]
    constructor
    · left
      left
      constructor
      · simp; linarith
      · norm_num
    · constructor
      · simp; linarith
      · simp; linarith
  -- chain of unions is path connected
  have hUR : IsPathConnected (U ∪ R) := hU.union hR hURn
  have hURL : IsPathConnected ((U ∪ R) ∪ L) := hUR.union hL hURLn
  have hURLM : IsPathConnected (((U ∪ R) ∪ L) ∪ M) := hURL.union hM hURLMn
  -- the union equals the target set
  have h_eq : (((U ∪ R) ∪ L) ∪ M) = {z : ℂ | θ < z.re ∧ z ≠ 1} := by
    ext z
    constructor
    · intro hz
      rcases hz with hz | hzM
      · rcases hz with hz | hzL
        · rcases hz with hzU | hzR
          · rcases hzU with ⟨hzθ, hzim⟩
            exact ⟨hzθ, ne_one_of_pos_im hzim⟩
          · have hz1gt : 1 < z.re := by simpa [R] using hzR
            exact ⟨by linarith, ne_one_of_one_lt_re hz1gt⟩
        · rcases hzL with ⟨hzθ, hzim⟩
          exact ⟨hzθ, ne_one_of_im_neg hzim⟩
      · rcases hzM with ⟨hzθ, hzr⟩
        exact ⟨hzθ, ne_one_of_re_lt hzr⟩
    · intro hz
      rcases hz with ⟨hzθ, hz1⟩
      by_cases hzn : z.im ≠ 0
      · rcases lt_or_gt_of_ne hzn with hzneg | hzpos
        · left
          right
          exact ⟨hzθ, hzneg⟩
        · left
          left
          left
          exact ⟨hzθ, hzpos⟩
      · have hz0 : z.im = 0 := by simpa using hzn
        have hzreal : z = (z.re : ℂ) := by
          apply Complex.ext
          · simp
          · simp [hz0]
        have hre1 : z.re ≠ 1 := by
          intro h
          apply hz1
          rw [hzreal, h]
          norm_num
        rcases lt_or_gt_of_ne hre1 with hzlt | hzgt
        · right
          exact ⟨hzθ, hzlt⟩
        · left
          left
          right
          exact hzgt
  rw [← h_eq]
  exact hURLM.isConnected.isPreconnected

end Commons.NumberTheory.Zeta