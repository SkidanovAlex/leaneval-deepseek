import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.win_membership
import Submission.Work.HP.fiber_bound

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

open Finset

namespace Work.HP

theorem window_sum_ge3 (n r : ℕ) (hn : 2 ≤ n) (hr : 3 ≤ r) (hrn : r ≤ n + 1)
    (Knum : ℝ) (hKnum : 0 < Knum)
    (hnum : ∀ (s : Fin r → ℝ) (F : Finset (Submodule ℤ (Fin (n + 1) → ℤ))), (∀ j, 1 ≤ s j) →
      (∀ L ∈ F, IsPrimLat L ∧ rk L = r ∧ ∀ j : Fin r, lam L (j.1 + 1) ≤ s j) →
      ((F.card : ℝ) ≤ Knum * ∏ j : Fin r, s j ^ (n + 1 + r + 1 - 2 * (j.1 + 1))))
    (Kmink : ℝ) (hKmink : 1 ≤ Kmink)
    (hmink : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ Kmink * detL L)
    (hwin : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)), rk L = r →
      (∀ j : Fin r, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin r L j)) ∧
      (∀ j : Fin r, (2 : ℝ) ^ (kwin r L j) ≤ 2 * lam L (j.1 + 1)) ∧
      Monotone (kwin r L) ∧
      (∀ M : ℝ, 1 ≤ M → (∏ j : Fin r, (2 : ℝ) ^ (kwin r L j)) ≤ M →
        (∑ j : Fin r, kwin r L j) ≤ ⌈Real.logb 2 M⌉₊))
    (Ksmall : ℝ) (hKsmall : 0 < Ksmall)
    (hsmallX : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (X : ℝ), 1 ≤ X → lam L 1 ≤ X →
      (ballCount L X : ℝ) ≤ Ksmall * X ^ rk L / lam L 1 ^ rk L)
    (hsmallY : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (Y : ℝ), 1 ≤ Y → 2 ≤ rk L → lam L 2 ≤ Y →
      (ballCount L Y : ℝ) ≤ Ksmall * Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)))
    (hbp : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (k : Fin r → ℕ) (X Y : ℝ), rk L = r →
      (∀ j : Fin r, (2 : ℝ) ^ (k j) ≤ 2 * lam L (j.1 + 1)) → 1 ≤ X → 1 ≤ Y →
      lam L 1 ≤ X → lam L 2 ≤ Y →
      (ballCount L X : ℝ) * (ballCount L Y : ℝ) ≤
        Ksmall ^ 2 * (2 : ℝ) ^ (2 * r) * X ^ r * Y ^ r /
          ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
            (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩)))
    (Karith : ℝ) (hKarith : 0 < Karith)
    (harith : ∀ (Δ : ℝ), 1 ≤ Δ →
      (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊ + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ ⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊ then
          (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) /
            ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
              (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))
        else 0))
      ≤ Karith * Δ ^ (n - 1) * Real.log (2 * Δ) ^ (2 * min (r - 2) 1))
    (X Y Δ : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hΔ : 1 ≤ Δ) (hXY : X ≤ Y)
    (T : Finset (Submodule ℤ (Fin (n + 1) → ℤ)))
    (hT : ∀ L ∈ T, IsPrimLat L ∧ rk L = r ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ X ∧ lam L 2 ≤ Y) :
    (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ)) ≤
      (Knum * Ksmall ^ 2 * (2 : ℝ) ^ (2 * r) * Karith) * X ^ r * Y ^ r * Δ ^ (n - 1) *
        Real.log (2 * Δ) ^ (2 * min (r - 2) 1) := by
  set N : ℕ := ⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊ with hN
  have hwin1 : ∀ L ∈ T, ∀ j : Fin r, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin r L j) :=
    fun L hL => (hwin L (hT L hL).2.1).1
  have hwin2 : ∀ L ∈ T, ∀ j : Fin r, (2 : ℝ) ^ (kwin r L j) ≤ 2 * lam L (j.1 + 1) :=
    fun L hL => (hwin L (hT L hL).2.1).2.1
  have hwinL : ∀ L ∈ T, Monotone (kwin r L) ∧ (∑ j : Fin r, kwin r L j) ≤ N ∧
      (∀ j : Fin r, kwin r L j ≤ N) := by
    intro L hL
    obtain ⟨h1, h2, h3, h4, h5⟩ := hT L hL
    rw [hN]
    exact win_membership n r hr Kmink Δ hKmink hΔ L h2 h3 (hmink L) (hwin L h2)
  have hcond : ∀ k ∈ T.image (fun L => kwin r L), Monotone k ∧ (∑ j : Fin r, k j) ≤ N := by
    intro k hk
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨(hwinL L hL).1, (hwinL L hL).2.1⟩
  have himg_sub : T.image (fun L => kwin r L) ⊆
      (Fintype.piFinset (fun _ : Fin r => Finset.range (N + 1)) : Finset (Fin r → ℕ)) := by
    intro k hk
    rw [Fintype.mem_piFinset]
    intro j
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((hwinL L hL).2.2 j)
  have hfib : (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ))
      = ∑ k ∈ T.image (fun L => kwin r L),
          ∑ L ∈ T.filter (fun L => kwin r L = k), (ballCount L X : ℝ) * (ballCount L Y : ℝ) :=
    (Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image (fun L => kwin r L))
      (g := fun L => kwin r L) (fun i hi => Finset.mem_image_of_mem _ hi)
      (fun L => (ballCount L X : ℝ) * (ballCount L Y : ℝ))).symm
  have hinner : ∀ k ∈ T.image (fun L => kwin r L),
      (∑ L ∈ T.filter (fun L => kwin r L = k), (ballCount L X : ℝ) * (ballCount L Y : ℝ))
      ≤ Knum * (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) *
        (Ksmall ^ 2 * (2 : ℝ) ^ (2 * r) * X ^ r * Y ^ r /
          ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
            (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))) := by
    intro k hk
    have hTf : ∀ L ∈ T.filter (fun L => kwin r L = k),
        IsPrimLat L ∧ rk L = r ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ X ∧ lam L 2 ≤ Y :=
      fun L hL => hT L (Finset.mem_of_mem_filter L hL)
    have hw1 : ∀ L ∈ T.filter (fun L => kwin r L = k), ∀ j : Fin r,
        lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin r L j) :=
      fun L hL => hwin1 L (Finset.mem_of_mem_filter L hL)
    have hw2 : ∀ L ∈ T.filter (fun L => kwin r L = k), ∀ j : Fin r,
        (2 : ℝ) ^ (kwin r L j) ≤ 2 * lam L (j.1 + 1) :=
      fun L hL => hwin2 L (Finset.mem_of_mem_filter L hL)
    have hkk : ∀ L ∈ T.filter (fun L => kwin r L = k), kwin r L = k :=
      fun L hL => (Finset.mem_filter.mp hL).2
    exact fiber_bound n r hn hr hrn Knum hKnum hnum Ksmall hKsmall hbp X Y Δ hX hY
      (T.filter (fun L => kwin r L = k)) k hTf hw1 hw2 hkk
  have hstep2 := Finset.sum_le_sum hinner
  have hC0 : (0 : ℝ) ≤ Knum * Ksmall ^ 2 * (2 : ℝ) ^ (2 * r) * X ^ r * Y ^ r := by
    have h1 : (0 : ℝ) ≤ Knum := le_of_lt hKnum
    have h2 : (0 : ℝ) ≤ Ksmall ^ 2 := sq_nonneg Ksmall
    have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * r) := by positivity
    have h4 : (0 : ℝ) ≤ X ^ r := pow_nonneg (by linarith) r
    have h5 : (0 : ℝ) ≤ Y ^ r := pow_nonneg (by linarith) r
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4) h5
  have hstep3 : (∑ k ∈ T.image (fun L => kwin r L),
        Knum * (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) *
          (Ksmall ^ 2 * (2 : ℝ) ^ (2 * r) * X ^ r * Y ^ r /
            ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
              (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))))
      ≤ (Knum * Ksmall ^ 2 * (2 : ℝ) ^ (2 * r) * X ^ r * Y ^ r) *
        (∑ k ∈ (Fintype.piFinset (fun _ : Fin r => Finset.range (N + 1)) : Finset (Fin r → ℕ)),
          (if Monotone k ∧ (∑ j : Fin r, k j) ≤ N then
            (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) /
              ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
                (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))
          else 0)) := by
    rw [Finset.mul_sum]
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg himg_sub ?_)
    · apply Finset.sum_congr rfl
      intro k hk
      rw [if_pos (hcond k hk)]
      ring
    · intro k _ _
      by_cases hc : Monotone k ∧ (∑ j : Fin r, k j) ≤ N
      · rw [if_pos hc]
        exact mul_nonneg hC0 (div_nonneg (by positivity) (by positivity))
      · rw [if_neg hc]
        exact mul_nonneg hC0 le_rfl
  have hmain : (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ))
      ≤ (Knum * Ksmall ^ 2 * (2 : ℝ) ^ (2 * r) * X ^ r * Y ^ r) *
        (∑ k ∈ (Fintype.piFinset (fun _ : Fin r => Finset.range (N + 1)) : Finset (Fin r → ℕ)),
          (if Monotone k ∧ (∑ j : Fin r, k j) ≤ N then
            (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) /
              ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
                (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))
          else 0)) := by
    rw [hfib]
    exact le_trans hstep2 hstep3
  calc (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ))
      ≤ (Knum * Ksmall ^ 2 * (2 : ℝ) ^ (2 * r) * X ^ r * Y ^ r) *
        (∑ k ∈ (Fintype.piFinset (fun _ : Fin r => Finset.range (N + 1)) : Finset (Fin r → ℕ)),
          (if Monotone k ∧ (∑ j : Fin r, k j) ≤ N then
            (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) /
              ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
                (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))
          else 0)) := hmain
    _ ≤ (Knum * Ksmall ^ 2 * (2 : ℝ) ^ (2 * r) * X ^ r * Y ^ r) *
        (Karith * Δ ^ (n - 1) * Real.log (2 * Δ) ^ (2 * min (r - 2) 1)) :=
        mul_le_mul_of_nonneg_left (harith Δ hΔ) hC0
    _ = (Knum * Ksmall ^ 2 * (2 : ℝ) ^ (2 * r) * Karith) * X ^ r * Y ^ r * Δ ^ (n - 1) *
        Real.log (2 * Δ) ^ (2 * min (r - 2) 1) := by ring


end Work.HP
