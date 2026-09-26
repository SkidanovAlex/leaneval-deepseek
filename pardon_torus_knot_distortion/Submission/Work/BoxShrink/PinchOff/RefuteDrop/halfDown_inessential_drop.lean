import Mathlib
import Submission.Work.BoxShrink.Pinch.Plane
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.Config

/-!
# The lower half-region of the `RefuteDrop` configuration is inessential

This module proves `Work.BoxShrink.PinchOff.RefuteDrop.halfDown_inessential_drop`: at the
counterexample's configuration (`RefuteDrop/Config.lean`: the linear diffeomorphism `dropDiffeo`,
`dropS = 7/5`, `dropC = 0`, `dropCyc = swap 0 2`, `dropU = 0`, so that the cutting plane is
`{x = 0}`), the **lower** half-region

  `Ω₋ = F ∩ PBox (7/5) 0 (swap 0 2) ∩ {y 0 < 0}`

of the torus `F = dropDiffeo(T²)` carries no essential loop of `F`, i.e. its winding span
vanishes.

The proof is the parameter-plane window criterion of `Work.BoxShrink.Pinch.Plane`, in the same
shape as the sibling counterexamples (`Work.BoxShrink.Pinch.BubbleHalfRefuted`,
`RefuteNC/halfDown_inessential`).  Writing `q = (θ, φ)` for a point of the parameter plane, the
image of `q` in the box has coordinates

  `x' = -(2/25) r cos θ - (39/100) r sin θ + (97/100) sin φ`
  `y' =  (49/100) r cos θ + (31/25)  r sin θ + (59/100)  sin φ`      (`r = 2 + cos φ`),

and membership of `q` in the preimage of `Ω₋` gives `x' < 0` and `|y'| < 7/5`.  From these two
inequalities we extract two **windows** of the parameter plane:

* **the `φ`-window.**  `x' < 0` is `(97/100) sin φ < r · (8/100 cos θ + 39/100 sin θ)`, and the
  bracket is at most `4/10` by Cauchy–Schwarz, so `φ` satisfies `97 sin φ < 40 (2 + cos φ)`.
  The set of `φ ∈ [9/5, 11/5] (mod 2π)` is contained in the *complement* of that inequality —
  `sin φ ≥ 4/5` and `cos φ ≤ -11/50` there, whence `97 sin φ - 40 cos φ - 80 ≥ 64/10 > 0`.
* **the `θ`-window.**  `x' < 0` and `y' > -7/5` say `-r A + (97/100) sin φ < 0` and
  `r B + (59/100) sin φ + 7/5 > 0` with `A = 8/100 cos θ + 39/100 sin θ`,
  `B = 49/100 cos θ + 124/100 sin θ`; the combination
  `(59/100)·(first) - (97/100)·(second)` cancels `sin φ` and gives
  `(2 + cos φ) (59 A + 97 B) > -1358/1000`, whence `5225 cos θ + 14329 sin θ > -13580`.  On
  `θ ∈ [4.2, 4.4] (mod 2π)` one has `cos θ ≤ -3/10` and `sin θ ≤ -17/20`, so the form is at most
  `-274943/20 < -13580`.

Both forbidden sets are intervals of the circle, and the complementary windows
`(4.4 + 2πk, 4.2 + 2π + 2πk) × (2.2 + 2πl, 1.8 + 2π + 2πl)` are pairwise disjoint and have side
lengths `2π - 1/5` and `2π - 2/5`, so the window criterion applies.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff.RefuteDrop

noncomputable section

/-! The auxiliary lemmas of this module live in a namespace of their own, so that they cannot
clash with the helpers of the sibling modules of this directory. -/
namespace HalfDown

/-! ## The configuration in coordinates -/

/-- The first row of the matrix of `dropDiffeo`, read off from `dropVec_apply`. -/
theorem dropVec_coord_zero (x : R3) :
    (dropVec x).ofLp 0 =
      (-2 / 25 : ℝ) * x.ofLp 0 + (-39 / 100 : ℝ) * x.ofLp 1 + (97 / 100 : ℝ) * x.ofLp 2 := by
  rw [dropVec_apply, Fin.sum_univ_three]
  simp [dropA]

/-- The third row of the matrix of `dropDiffeo`. -/
theorem dropVec_coord_two (x : R3) :
    (dropVec x).ofLp 2 =
      (49 / 100 : ℝ) * x.ofLp 0 + (31 / 25 : ℝ) * x.ofLp 1 + (59 / 100 : ℝ) * x.ofLp 2 := by
  rw [dropVec_apply, Fin.sum_univ_three]
  simp [dropA]

@[simp] theorem dropCyc_apply_zero : dropCyc (0 : Fin 3) = 2 := by decide

@[simp] theorem dropCyc_apply_two : dropCyc (2 : Fin 3) = 0 := by decide

@[simp] theorem dropC_apply_zero : dropC.ofLp 0 = 0 := by simp [dropC]

@[simp] theorem dropC_apply_two : dropC.ofLp 2 = 0 := by simp [dropC]

theorem boxSide_zero : Submission.boxSide 0 = 1 := by simp [Submission.boxSide]

theorem dropS_eq : dropS = 7 / 5 := rfl

theorem dropU_eq : dropU = 0 := rfl

/-- The parametrisation of the counterexample's surface. -/
theorem torus_psi_drop (θ φ : ℝ) :
    (Work.Smooth.Morse.torus dropDiffeo).psi θ φ = dropVec (Work.Core.torusMap θ φ) := by
  rw [Work.Smooth.Morse.torus_psi, Work.Smooth.Morse.param_apply, dropDiffeo_apply]

/-- The `x`-coordinate of the parametrisation, in terms of `θ` and `φ`. -/
theorem dropVec_torusMap_zero (θ φ : ℝ) :
    (dropVec (Work.Core.torusMap θ φ)).ofLp 0 =
      (-2 / 25 : ℝ) * ((2 + Real.cos φ) * Real.cos θ)
        + (-39 / 100 : ℝ) * ((2 + Real.cos φ) * Real.sin θ) + (97 / 100 : ℝ) * Real.sin φ := by
  rw [dropVec_coord_zero, Work.CoreTopology.torusMap_apply_zero,
    Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two]

/-- The `z`-coordinate of the parametrisation, in terms of `θ` and `φ`. -/
theorem dropVec_torusMap_two (θ φ : ℝ) :
    (dropVec (Work.Core.torusMap θ φ)).ofLp 2 =
      (49 / 100 : ℝ) * ((2 + Real.cos φ) * Real.cos θ)
        + (31 / 25 : ℝ) * ((2 + Real.cos φ) * Real.sin θ) + (59 / 100 : ℝ) * Real.sin φ := by
  rw [dropVec_coord_two, Work.CoreTopology.torusMap_apply_zero,
    Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two]

/-! ## Elementary trigonometric bounds -/

/-- `c ≤ sin y` from rational bounds on `y` and on the Taylor polynomial `y - y³/6`. -/
theorem sin_ge_of_bounds {y a b c : ℝ} (h1 : a ≤ y) (h2 : y ≤ b) (ha : 0 ≤ a)
    (h : c ≤ a - b ^ 3 / 6) : c ≤ Real.sin y := by
  have hy : 0 ≤ y := le_trans ha h1
  have hcube : y ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ hy h2 3
  have hsin := Real.sin_ge_sub_cube hy
  linarith

/-- `c ≤ cos y` from rational bounds on `y` and on `1 - y²/2`. -/
theorem cos_ge_of_bounds {y a b c : ℝ} (h1 : a ≤ y) (h2 : y ≤ b) (ha : 0 ≤ a)
    (h : c ≤ 1 - b ^ 2 / 2) : c ≤ Real.cos y := by
  have hy : 0 ≤ y := le_trans ha h1
  have hsq : y ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hy h2 2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := y)
  linarith

/-! ### The `θ`-gap -/

/-- On `[4.2, 4.4]` the cosine is at most `-3/10`. -/
theorem cos_le_neg_three_tenths {θ : ℝ} (h1 : 21 / 5 ≤ θ) (h2 : θ ≤ 22 / 5) :
    Real.cos θ ≤ -(3 / 10 : ℝ) := by
  have hπ1 := Real.pi_lt_d6
  have hπ2 := Real.pi_gt_d6
  rw [show θ = (θ - Real.pi) + Real.pi by ring, Real.cos_add_pi]
  have hy2 : θ - Real.pi ≤ 1.258408 := by linarith
  have hmono : Real.cos (1.258408) ≤ Real.cos (θ - Real.pi) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hy2
  have h30 : (3 / 10 : ℝ) ≤ Real.cos (1.258408) := by
    rw [← Real.sin_pi_div_two_sub 1.258408]
    refine sin_ge_of_bounds (y := Real.pi / 2 - 1.258408) (a := 0.312388) (b := 0.3123885)
      (c := 3 / 10) ?_ ?_ (by norm_num) (by norm_num)
    · linarith
    · linarith
  linarith

/-- On `[4.2, 4.4]` the sine is at most `-17/20`. -/
theorem sin_le_neg_17_20 {θ : ℝ} (h1 : 21 / 5 ≤ θ) (h2 : θ ≤ 22 / 5) :
    Real.sin θ ≤ -(17 / 20 : ℝ) := by
  have hπ1 := Real.pi_lt_d6
  have hπ2 := Real.pi_gt_d6
  rw [show θ = (θ - Real.pi) + Real.pi by ring, Real.sin_add_pi]
  have hy1 : (1.058407 : ℝ) < θ - Real.pi := by linarith
  have hyπ : θ - Real.pi ≤ Real.pi / 2 := by linarith
  have hmono : Real.sin (1.058407) ≤ Real.sin (θ - Real.pi) :=
    (Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hyπ hy1).le
  have h85 : (17 / 20 : ℝ) ≤ Real.sin (1.058407) := by
    rw [← Real.cos_pi_div_two_sub (1.058407)]
    refine cos_ge_of_bounds (y := Real.pi / 2 - 1.058407) (a := 0.512388) (b := 0.5123895)
      (c := 17 / 20) ?_ ?_ (by norm_num) (by norm_num)
    · linarith
    · linarith
  linarith

/-- **The `θ`-inequality on the gap.**  On `θ ∈ [21/5, 22/5]` the linear form of the `θ`-window
criterion is at most `-274943/20 < -13580`. -/
theorem gap_theta {θ : ℝ} (h1 : 21 / 5 ≤ θ) (h2 : θ ≤ 22 / 5) :
    5225 * Real.cos θ + 14329 * Real.sin θ ≤ -13580 := by
  have hc := cos_le_neg_three_tenths h1 h2
  have hs := sin_le_neg_17_20 h1 h2
  nlinarith

/-! ### The `φ`-gap -/

/-- On `[9/5, 11/5]` the sine is at least `4/5`. -/
theorem sin_ge_four_fifths {φ : ℝ} (h1 : 9 / 5 ≤ φ) (h2 : φ ≤ 11 / 5) :
    (4 / 5 : ℝ) ≤ Real.sin φ := by
  have hπ1 := Real.pi_lt_d6
  have hπ2 := Real.pi_gt_d6
  rcases le_or_gt φ (Real.pi / 2) with hcase | hcase
  · have hmono : Real.sin (9 / 5) ≤ Real.sin φ :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hcase h1
    have h9 : (4 / 5 : ℝ) ≤ Real.sin (9 / 5) := by
      have := Real.sin_ge_sub_cube (show (0 : ℝ) ≤ 9 / 5 by norm_num)
      linarith
    linarith
  · have hφπ : φ ≤ Real.pi := by linarith
    have h11 : (4 / 5 : ℝ) ≤ Real.sin (11 / 5) := by
      rw [← Real.sin_pi_sub (11 / 5)]
      refine sin_ge_of_bounds (y := Real.pi - 11 / 5) (a := 0.941592) (b := 0.941593)
        (c := 4 / 5) ?_ ?_ (by norm_num) (by norm_num)
      · linarith
      · linarith
    have hmono : Real.sin (11 / 5) ≤ Real.sin φ := by
      rw [← Real.sin_pi_sub (11 / 5), ← Real.sin_pi_sub φ]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
    linarith

/-- On `[9/5, 11/5]` the cosine is at most `-11/50`. -/
theorem cos_le_neg_11_50 {φ : ℝ} (h1 : 9 / 5 ≤ φ) (h2 : φ ≤ 11 / 5) :
    Real.cos φ ≤ -(11 / 50 : ℝ) := by
  have hπ1 := Real.pi_lt_d6
  have hπ2 := Real.pi_gt_d6
  have hmono : Real.cos φ ≤ Real.cos (9 / 5) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith) h1
  have h9 : Real.cos (9 / 5) ≤ -(11 / 50 : ℝ) := by
    have hid : Real.cos (Real.pi - 9 / 5) = -Real.cos (9 / 5) := Real.cos_pi_sub (9 / 5)
    have hmono2 : Real.cos (1.341593) ≤ Real.cos (Real.pi - 9 / 5) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
    have h22 : (11 / 50 : ℝ) ≤ Real.cos (1.341593) := by
      rw [← Real.sin_pi_div_two_sub 1.341593]
      refine sin_ge_of_bounds (y := Real.pi / 2 - 1.341593) (a := 0.229203) (b := 0.229204)
        (c := 11 / 50) ?_ ?_ (by norm_num) (by norm_num)
      · linarith
      · linarith
    linarith
  linarith

/-- **The `φ`-inequality on the gap.**  On `φ ∈ [9/5, 11/5]` the inequality `97 sin φ < 40
(2 + cos φ)` fails, with margin `64/10`. -/
theorem gap_phi {φ : ℝ} (h1 : 9 / 5 ≤ φ) (h2 : φ ≤ 11 / 5) :
    ¬ (97 * Real.sin φ < 40 * (2 + Real.cos φ)) := by
  have hs : (4 / 5 : ℝ) ≤ Real.sin φ := sin_ge_four_fifths h1 h2
  have hc : Real.cos φ ≤ -(11 / 50 : ℝ) := cos_le_neg_11_50 h1 h2
  intro hcon
  nlinarith [hcon, hs, hc]

/-! ## The two windows -/

/-- **The `θ`-window.**  If the linear form `5225 cos θ + 14329 sin θ` exceeds `-13580` then `θ`
lies in one of the intervals `(4.4 + 2πk, 4.2 + 2π + 2πk)`. -/
theorem theta_window {θ : ℝ} (h : -13580 < 5225 * Real.cos θ + 14329 * Real.sin θ) :
    ∃ k : ℤ, 22 / 5 + k * (2 * Real.pi) < θ ∧ θ < 21 / 5 + 2 * Real.pi + k * (2 * Real.pi) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  set k : ℤ := ⌊(θ - 22 / 5) / (2 * Real.pi)⌋
  have hfl : ((k : ℤ) : ℝ) ≤ (θ - 22 / 5) / (2 * Real.pi) := Int.floor_le _
  have hlow : ((k : ℤ) : ℝ) * (2 * Real.pi) ≤ θ - 22 / 5 := by
    rw [le_div_iff₀ hπ] at hfl; linarith
  have hlt : (θ - 22 / 5) / (2 * Real.pi) < ((k : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hhigh : θ - 22 / 5 < (((k : ℤ) : ℝ) + 1) * (2 * Real.pi) := by
    rw [div_lt_iff₀ hπ] at hlt; linarith
  refine ⟨k, ?_, ?_⟩
  · rcases lt_or_eq_of_le hlow with hlt' | heq
    · linarith
    · exfalso
      have hgap := gap_theta (show (21 / 5 : ℝ) ≤ 22 / 5 by norm_num) (le_refl (22 / 5 : ℝ))
      have hθ : θ = 22 / 5 + (k : ℝ) * (2 * Real.pi) := by linarith
      have : 5225 * Real.cos θ + 14329 * Real.sin θ ≤ -13580 := by
        rw [hθ, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
        exact hgap
      linarith
  · by_contra hcon
    have hcon' : 21 / 5 + 2 * Real.pi + (k : ℝ) * (2 * Real.pi) ≤ θ := not_lt.mp hcon
    have hcast : (((k + 1 : ℤ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have h1' : (21 / 5 : ℝ) ≤ θ - (((k + 1 : ℤ)) : ℝ) * (2 * Real.pi) := by
      rw [hcast]; linarith
    have h2' : θ - (((k + 1 : ℤ)) : ℝ) * (2 * Real.pi) ≤ 22 / 5 := by
      rw [hcast]; linarith
    have hgap := gap_theta h1' h2'
    rw [Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi] at hgap
    linarith

/-- **The `φ`-window.**  If `97 sin φ < 40 (2 + cos φ)` then `φ` lies in one of the intervals
`(2.2 + 2πl, 1.8 + 2π + 2πl)`. -/
theorem phi_window {φ : ℝ} (h : 97 * Real.sin φ < 40 * (2 + Real.cos φ)) :
    ∃ l : ℤ, 11 / 5 + l * (2 * Real.pi) < φ ∧ φ < 9 / 5 + 2 * Real.pi + l * (2 * Real.pi) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  set l : ℤ := ⌊(φ - 11 / 5) / (2 * Real.pi)⌋
  have hfl : ((l : ℤ) : ℝ) ≤ (φ - 11 / 5) / (2 * Real.pi) := Int.floor_le _
  have hlow : ((l : ℤ) : ℝ) * (2 * Real.pi) ≤ φ - 11 / 5 := by
    rw [le_div_iff₀ hπ] at hfl; linarith
  have hlt : (φ - 11 / 5) / (2 * Real.pi) < ((l : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hhigh : φ - 11 / 5 < (((l : ℤ) : ℝ) + 1) * (2 * Real.pi) := by
    rw [div_lt_iff₀ hπ] at hlt; linarith
  refine ⟨l, ?_, ?_⟩
  · rcases lt_or_eq_of_le hlow with hlt' | heq
    · linarith
    · exfalso
      have hφ : φ = 11 / 5 + (l : ℝ) * (2 * Real.pi) := by linarith
      have hc := Real.cos_add_int_mul_two_pi (11 / 5) l
      have hs := Real.sin_add_int_mul_two_pi (11 / 5) l
      rw [hφ, hc, hs] at h
      exact gap_phi (show (9 / 5 : ℝ) ≤ 11 / 5 by norm_num) (le_refl (11 / 5 : ℝ)) h
  · by_contra hcon
    have hcon' : 9 / 5 + 2 * Real.pi + (l : ℝ) * (2 * Real.pi) ≤ φ := not_lt.mp hcon
    have hcast : (((l + 1 : ℤ)) : ℝ) = (l : ℝ) + 1 := by push_cast; ring
    have h1' : (9 / 5 : ℝ) ≤ φ - (((l + 1 : ℤ)) : ℝ) * (2 * Real.pi) := by
      rw [hcast]; linarith
    have h2' : φ - (((l + 1 : ℤ)) : ℝ) * (2 * Real.pi) ≤ 11 / 5 := by
      rw [hcast]; linarith
    have hc := Real.cos_sub_int_mul_two_pi φ (l + 1)
    have hs := Real.sin_sub_int_mul_two_pi φ (l + 1)
    rw [← hc, ← hs] at h
    exact gap_phi h1' h2' h

/-! ## The windows of the parameter plane -/

/-- The windows `(4.4 + 2πk, 4.2 + 2π + 2πk) × (2.2 + 2πl, 1.8 + 2π + 2πl)`. -/
def dropWindows : Set (Set (ℝ × ℝ)) :=
  {W | ∃ k l : ℤ,
    W = Set.Ioo ((22 / 5 : ℝ) + k * (2 * Real.pi))
          ((21 / 5 : ℝ) + 2 * Real.pi + k * (2 * Real.pi)) ×ˢ
        Set.Ioo ((11 / 5 : ℝ) + l * (2 * Real.pi))
          ((9 / 5 : ℝ) + 2 * Real.pi + l * (2 * Real.pi))}

theorem mem_dropWindows {W : Set (ℝ × ℝ)} :
    W ∈ dropWindows ↔ ∃ k l : ℤ,
      W = Set.Ioo ((22 / 5 : ℝ) + k * (2 * Real.pi))
            ((21 / 5 : ℝ) + 2 * Real.pi + k * (2 * Real.pi)) ×ˢ
          Set.Ioo ((11 / 5 : ℝ) + l * (2 * Real.pi))
            ((9 / 5 : ℝ) + 2 * Real.pi + l * (2 * Real.pi)) := Iff.rfl

theorem isWindow_dropWindows (W : Set (ℝ × ℝ)) (hW : W ∈ dropWindows) :
    Work.BoxShrink.Pinch.IsWindow W := by
  obtain ⟨k, l, rfl⟩ := mem_dropWindows.mp hW
  refine Work.BoxShrink.Pinch.isWindow_Ioo ?_ ?_
  · have := Real.pi_pos
    linarith
  · have := Real.pi_pos
    linarith

theorem isOpen_dropWindows (W : Set (ℝ × ℝ)) (hW : W ∈ dropWindows) : IsOpen W := by
  obtain ⟨k, l, rfl⟩ := mem_dropWindows.mp hW
  exact isOpen_Ioo.prod isOpen_Ioo

theorem pairwiseDisjoint_dropWindows : dropWindows.Pairwise Disjoint := by
  rintro W hW W' hW' hne
  obtain ⟨k, l, rfl⟩ := mem_dropWindows.mp hW
  obtain ⟨k', l', rfl⟩ := mem_dropWindows.mp hW'
  rcases eq_or_ne k k' with rfl | hk
  · rcases eq_or_ne l l' with rfl | hl
    · exact absurd rfl hne
    · rw [Set.disjoint_left]
      intro q hq hq'
      obtain ⟨-, hq2⟩ := hq
      obtain ⟨-, hq2'⟩ := hq'
      rcases lt_or_gt_of_ne hl with h | h
      · have hcast : (l : ℝ) + 1 ≤ (l' : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h
        nlinarith [Real.pi_pos, hq2.2, hq2'.1]
      · have hcast : (l' : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h
        nlinarith [Real.pi_pos, hq2'.2, hq2.1]
  · rw [Set.disjoint_left]
    intro q hq hq'
    obtain ⟨hq1, -⟩ := hq
    obtain ⟨hq1', -⟩ := hq'
    rcases lt_or_gt_of_ne hk with h | h
    · have hcast : (k : ℝ) + 1 ≤ (k' : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h
      nlinarith [Real.pi_pos, hq1.2, hq1'.1]
    · have hcast : (k' : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h
      nlinarith [Real.pi_pos, hq1'.2, hq1.1]

/-! ## The two necessary conditions -/

/-- **The `φ`-inequality from the box.**  If the plane coordinate is negative then
`97 sin φ < 40 (2 + cos φ)`. -/
theorem phi_necessary {θ φ : ℝ}
    (h1 : (-2 / 25 : ℝ) * ((2 + Real.cos φ) * Real.cos θ)
        + (-39 / 100 : ℝ) * ((2 + Real.cos φ) * Real.sin θ) + (97 / 100 : ℝ) * Real.sin φ < 0) :
    97 * Real.sin φ < 40 * (2 + Real.cos φ) := by
  have hcs : ((8 / 100 : ℝ) * Real.cos θ + (39 / 100 : ℝ) * Real.sin θ) ^ 2 ≤ (4 / 10) ^ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq θ, sq_nonneg ((8 / 100 : ℝ) * Real.sin θ
      - (39 / 100 : ℝ) * Real.cos θ)]
  have hA : (8 / 100 : ℝ) * Real.cos θ + (39 / 100 : ℝ) * Real.sin θ ≤ 4 / 10 := by
    nlinarith [hcs]
  have hr : (0 : ℝ) < 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]
  have h2 : (97 / 100 : ℝ) * Real.sin φ
      < (2 + Real.cos φ) * ((8 / 100 : ℝ) * Real.cos θ + (39 / 100 : ℝ) * Real.sin θ) := by
    nlinarith [h1]
  have h3 : (97 / 100 : ℝ) * Real.sin φ < (2 + Real.cos φ) * (4 / 10) := by
    nlinarith [h2, hA, hr]
  linarith

/-- **The `θ`-inequality from the box.**  If the plane coordinate is negative and the `z`-box
coordinate is `> -7/5`, then `5225 cos θ + 14329 sin θ > -13580`. -/
theorem theta_necessary {θ φ : ℝ}
    (h1 : (-2 / 25 : ℝ) * ((2 + Real.cos φ) * Real.cos θ)
        + (-39 / 100 : ℝ) * ((2 + Real.cos φ) * Real.sin θ) + (97 / 100 : ℝ) * Real.sin φ < 0)
    (h2 : -(7 / 5 : ℝ) < (49 / 100 : ℝ) * ((2 + Real.cos φ) * Real.cos θ)
        + (31 / 25 : ℝ) * ((2 + Real.cos φ) * Real.sin θ) + (59 / 100 : ℝ) * Real.sin φ) :
    -13580 < 5225 * Real.cos θ + 14329 * Real.sin θ := by
  set A : ℝ := (8 / 100 : ℝ) * Real.cos θ + (39 / 100 : ℝ) * Real.sin θ with hA
  set B : ℝ := (49 / 100 : ℝ) * Real.cos θ + (124 / 100 : ℝ) * Real.sin θ with hB
  have h1' : -((2 + Real.cos φ) * A) + (97 / 100 : ℝ) * Real.sin φ < 0 := by
    rw [hA]; nlinarith [h1]
  have h2' : -(7 / 5 : ℝ) < (2 + Real.cos φ) * B + (59 / 100 : ℝ) * Real.sin φ := by
    rw [hB]; nlinarith [h2]
  have hr : (1 : ℝ) ≤ 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]
  have hcomb : -((2 + Real.cos φ) * ((59 / 100 : ℝ) * A + (97 / 100 : ℝ) * B)) - 1358 / 1000 < 0 := by
    nlinarith [h1', h2']
  have hP : -(1358 / 1000 : ℝ) < (59 / 100 : ℝ) * A + (97 / 100 : ℝ) * B := by
    by_cases hX : (0 : ℝ) ≤ (59 / 100 : ℝ) * A + (97 / 100 : ℝ) * B
    · linarith
    · have hX' : (2 + Real.cos φ) * ((59 / 100 : ℝ) * A + (97 / 100 : ℝ) * B)
          ≤ (59 / 100 : ℝ) * A + (97 / 100 : ℝ) * B := by nlinarith
      linarith
  have hexp : (59 / 100 : ℝ) * A + (97 / 100 : ℝ) * B
      = (5225 / 10000 : ℝ) * Real.cos θ + (14329 / 10000 : ℝ) * Real.sin θ := by
    rw [hA, hB]; ring
  rw [hexp] at hP
  linarith

/-! ## The preimage of the lower half-region is covered by the windows -/

theorem drop_preimage_subset :
    Work.BoxShrink.Pinch.planePreimage (Work.Smooth.Morse.torus dropDiffeo)
      (Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus dropDiffeo) dropS dropC dropCyc
        dropU)
      ⊆ ⋃₀ dropWindows := by
  intro q hq
  rw [Work.BoxShrink.Pinch.mem_planePreimage] at hq
  rw [torus_psi_drop] at hq
  obtain ⟨-, hPBox, hneg⟩ := (Work.BoxShrink.Core.mem_lowerRegion).mp hq
  rw [dropCyc_apply_two, dropC_apply_zero, dropU_eq, zero_add] at hneg
  have hz := (Submission.mem_PBox.mp hPBox) 0
  rw [dropCyc_apply_zero, dropC_apply_two, boxSide_zero, dropS_eq, one_mul, abs_lt] at hz
  rw [dropVec_torusMap_zero] at hneg
  rw [dropVec_torusMap_two] at hz
  simp only [sub_zero] at hz
  have hphi : 97 * Real.sin q.2 < 40 * (2 + Real.cos q.2) := phi_necessary hneg
  have htheta : -13580 < 5225 * Real.cos q.1 + 14329 * Real.sin q.1 :=
    theta_necessary hneg hz.1
  obtain ⟨k, hk1, hk2⟩ := theta_window htheta
  obtain ⟨l, hl1, hl2⟩ := phi_window hphi
  exact mem_sUnion.mpr ⟨_, ⟨k, l, rfl⟩, ⟨hk1, hk2⟩, ⟨hl1, hl2⟩⟩

theorem not_containsEssentialLoop_lowerRegion_drop :
    ¬ (Work.Smooth.Morse.torus dropDiffeo).ContainsEssentialLoop
      (Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus dropDiffeo) dropS dropC dropCyc
        dropU) :=
  Work.BoxShrink.Pinch.not_containsEssentialLoop_of_disjoint_windows _ dropWindows
    isWindow_dropWindows isOpen_dropWindows pairwiseDisjoint_dropWindows drop_preimage_subset

end HalfDown

theorem halfDown_inessential_drop :
    Work.SurgeryInvariance.WindingSpan
      (Work.Smooth.Morse.torus Work.BoxShrink.PinchOff.RefuteDrop.dropDiffeo)
      (Work.BoxShrink.Core.lowerRegion
        (Work.Smooth.Morse.torus Work.BoxShrink.PinchOff.RefuteDrop.dropDiffeo)
        Work.BoxShrink.PinchOff.RefuteDrop.dropS
        Work.BoxShrink.PinchOff.RefuteDrop.dropC
        Work.BoxShrink.PinchOff.RefuteDrop.dropCyc
        Work.BoxShrink.PinchOff.RefuteDrop.dropU) = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  exact HalfDown.not_containsEssentialLoop_lowerRegion_drop

end

end Work.BoxShrink.PinchOff.RefuteDrop
