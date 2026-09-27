import Mathlib
import Submission.Work.EQ.SymDefs

/-!
# Coordinates and the trap estimate for `LocalModel`

`LocalModel T A lam C ε` (see `Submission/Work/EQ/SymDefs.lean`) describes a map `T` near a real
point `A` in the coordinates `P = A + ξ + η i`:

`T (A + ξ + η i) = A + (ξ + F ξ η) + (η * G ξ η) i`   for `|ξ|, |η| ≤ 4 ε`,

where `F = O(η²)`, `|G - lam| ≤ C (|ξ| + |η|)`, `0 < lam < 1`, `C ε ≤ (1 - lam)/4`, and `T` fixes
the real segment `|ξ| ≤ 4 ε` pointwise.

This file provides

* `dynXi A P = (P - A).re`, `dynEta A P = (P - A).im`, so that `P = A + (dynXi A P) + (dynEta A P) i`;
* `dynStep`, the one-step formula `(ξ, η) ↦ (ξ + F ξ η, η * G ξ η)`;
* `dynTrap`: every orbit starting in the ball `‖P - A‖ ≤ ε` stays in the ball of radius `2 ε`
  (`|ξ_n| + |η_n| ≤ 2 ε` in fact), and the imaginary coordinate decays geometrically with rate
  `(1 + lam)/2 = lam + (1 - lam)/2 < 1`.
-/

namespace Work.EQ

open Complex Filter

/-- Real coordinate of `P` relative to `A`: `P = A + dynXi A P + dynEta A P * I`. -/
def dynXi (A P : ℂ) : ℝ := (P - A).re

/-- Imaginary coordinate of `P` relative to `A`. -/
def dynEta (A P : ℂ) : ℝ := (P - A).im

lemma dynXi_le_norm (A P : ℂ) : |dynXi A P| ≤ ‖P - A‖ := by
  simpa [dynXi] using Complex.abs_re_le_norm (P - A)

lemma dynEta_le_norm (A P : ℂ) : |dynEta A P| ≤ ‖P - A‖ := by
  simpa [dynEta] using Complex.abs_im_le_norm (P - A)

lemma dyn_norm_le (A P : ℂ) : ‖P - A‖ ≤ |dynXi A P| + |dynEta A P| := by
  have h : P - A = ((dynXi A P : ℝ) : ℂ) + ((dynEta A P : ℝ) : ℂ) * I := by
    rw [dynXi, dynEta, Complex.re_add_im]
  rw [h]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  simp

lemma dyn_point_eq (A P : ℂ) :
    A + ((dynXi A P : ℝ) : ℂ) + ((dynEta A P : ℝ) : ℂ) * I = P := by
  rw [dynXi, dynEta, add_assoc, Complex.re_add_im]
  ring

/-- The `F`, `G` data of a local model, with their properties. -/
lemma dyn_exists_FG {T : ℂ → ℂ} {A : ℂ} {lam C ε : ℝ} (h : LocalModel T A lam C ε) :
    ∃ F G : ℝ → ℝ → ℝ,
      (∀ ξ η : ℝ, |ξ| ≤ 4 * ε → |η| ≤ 4 * ε →
        T (A + (ξ : ℂ) + (η : ℂ) * I) =
          A + ((ξ + F ξ η : ℝ) : ℂ) + ((η * G ξ η : ℝ) : ℂ) * I) ∧
      (∀ ξ η : ℝ, |ξ| ≤ 4 * ε → |η| ≤ 4 * ε → |F ξ η| ≤ C * η ^ 2) ∧
      (∀ ξ η : ℝ, |ξ| ≤ 4 * ε → |η| ≤ 4 * ε → |G ξ η - lam| ≤ C * (|ξ| + |η|)) ∧
      (∀ ξ η ξ' η' : ℝ, |ξ| ≤ 4 * ε → |η| ≤ 4 * ε → |ξ'| ≤ 4 * ε → |η'| ≤ 4 * ε →
        |F ξ η - F ξ' η'| ≤ C * (η ^ 2 * |ξ - ξ'| + (|η| + |η'|) * |η - η'|)) ∧
      (∀ ξ η ξ' η' : ℝ, |ξ| ≤ 4 * ε → |η| ≤ 4 * ε → |ξ'| ≤ 4 * ε → |η'| ≤ 4 * ε →
        |G ξ η - G ξ' η'| ≤ C * (|ξ - ξ'| + |η - η'|)) := h.2.2.2.2.2.2.2

/-- One step of `T` in the coordinates `ξ = dynXi A P`, `η = dynEta A P`. -/
theorem dynStep {T : ℂ → ℂ} {A : ℂ} {F G : ℝ → ℝ → ℝ} {ε : ℝ}
    (hrep : ∀ ξ η : ℝ, |ξ| ≤ 4 * ε → |η| ≤ 4 * ε →
      T (A + (ξ : ℂ) + (η : ℂ) * I) =
        A + ((ξ + F ξ η : ℝ) : ℂ) + ((η * G ξ η : ℝ) : ℂ) * I)
    {P : ℂ} (hξ : |dynXi A P| ≤ 4 * ε) (hη : |dynEta A P| ≤ 4 * ε) :
    dynXi A (T P) = dynXi A P + F (dynXi A P) (dynEta A P) ∧
      dynEta A (T P) = dynEta A P * G (dynXi A P) (dynEta A P) := by
  have key := hrep (dynXi A P) (dynEta A P) hξ hη
  rw [dyn_point_eq A P] at key
  refine ⟨?_, ?_⟩
  · have hre := congrArg Complex.re key
    simp only [dynXi] at hre ⊢
    rw [Complex.sub_re, hre]
    simp
  · have him := congrArg Complex.im key
    simp only [dynEta] at him ⊢
    rw [Complex.sub_im, him]
    simp

/-- On the invariant ball `|ξ| + |η| ≤ 2 ε` the vertical multiplier is at most `(1 + lam)/2`. -/
lemma dyn_G_le {G : ℝ → ℝ → ℝ} {C lam ε ξ η : ℝ} (hC0 : 0 < C) (hlam0 : 0 < lam)
    (hCε : C * ε ≤ (1 - lam) / 4)
    (h : |G ξ η - lam| ≤ C * (|ξ| + |η|)) (habs : |ξ| + |η| ≤ 2 * ε) :
    |G ξ η| ≤ (1 + lam) / 2 := by
  have h1 : |G ξ η| ≤ |G ξ η - lam| + lam := by
    have := abs_add_le (G ξ η - lam) lam
    rwa [sub_add_cancel, abs_of_pos hlam0] at this
  have h2 : C * (|ξ| + |η|) ≤ C * (2 * ε) := mul_le_mul_of_nonneg_left habs (le_of_lt hC0)
  have h3 : C * (2 * ε) ≤ (1 - lam) / 2 := by linarith
  linarith

/-- On the invariant ball the horizontal displacement is at most `2 C ε |η|`. -/
lemma dyn_F_le {F : ℝ → ℝ → ℝ} {C ε ξ η : ℝ} (hC0 : 0 < C) (h : |F ξ η| ≤ C * η ^ 2)
    (habs : |ξ| + |η| ≤ 2 * ε) : |F ξ η| ≤ 2 * C * ε * |η| := by
  have hη : |η| ≤ 2 * ε := by linarith [abs_nonneg ξ]
  have hsq : η ^ 2 ≤ 2 * ε * |η| := by
    rw [← sq_abs]
    nlinarith [abs_nonneg η]
  have hC2 : C * η ^ 2 ≤ C * (2 * ε * |η|) := mul_le_mul_of_nonneg_left hsq (le_of_lt hC0)
  linarith [h, hC2]

/-- **Trap estimate.**  If `‖P - A‖ ≤ ε` then along the orbit the coordinates satisfy
`|ξ_n| + |η_n| ≤ 2 ε`, the Euclidean distance to `A` is at most `2 ε`, and the imaginary
coordinate decays geometrically with rate `(1 + lam)/2 < 1`. -/
theorem dynTrap {T : ℂ → ℂ} {A : ℂ} {lam C ε : ℝ} (h : LocalModel T A lam C ε) :
    ∀ P : ℂ, ‖P - A‖ ≤ ε →
      (∀ n : ℕ, |dynXi A ((T^[n]) P)| + |dynEta A ((T^[n]) P)| ≤ 2 * ε) ∧
      (∀ n : ℕ, ‖(T^[n]) P - A‖ ≤ 2 * ε) ∧
      (∀ n : ℕ, |dynEta A ((T^[n]) P)| ≤ ((1 + lam) / 2) ^ n * ε) := by
  intro P hP
  obtain ⟨hA, hε0, hC0, hlam0, hlam1, hCε, haxis, F, G, hrep, hFb, hGb, hFl, hGl⟩ := h
  have hCε' : 2 * C * ε ≤ (1 - lam) / 2 := by linarith
  have key : ∀ n : ℕ,
      |dynXi A ((T^[n]) P)| + |dynEta A ((T^[n]) P)| ≤ 2 * ε ∧
      |dynEta A ((T^[n]) P)| ≤ ((1 + lam) / 2) ^ n * ε := by
    intro n
    induction n with
    | zero =>
        have h1 : |dynXi A ((T^[0]) P)| ≤ ε := by
          simpa using (dynXi_le_norm A P).trans hP
        have h2 : |dynEta A ((T^[0]) P)| ≤ ε := by
          simpa using (dynEta_le_norm A P).trans hP
        exact ⟨by linarith, by simpa using h2⟩
    | succ n ih =>
        obtain ⟨ih1, ih2⟩ := ih
        have hξ4 : |dynXi A ((T^[n]) P)| ≤ 4 * ε := by
          linarith [abs_nonneg (dynEta A ((T^[n]) P))]
        have hη4 : |dynEta A ((T^[n]) P)| ≤ 4 * ε := by
          linarith [abs_nonneg (dynXi A ((T^[n]) P))]
        have hs := dynStep hrep hξ4 hη4
        have hFabs : |F (dynXi A ((T^[n]) P)) (dynEta A ((T^[n]) P))| ≤
            2 * C * ε * |dynEta A ((T^[n]) P)| := dyn_F_le hC0 (hFb _ _ hξ4 hη4) ih1
        have hGabs : |G (dynXi A ((T^[n]) P)) (dynEta A ((T^[n]) P))| ≤ (1 + lam) / 2 :=
          dyn_G_le hC0 hlam0 hCε (hGb _ _ hξ4 hη4) ih1
        have hcoef : 2 * C * ε + (1 + lam) / 2 ≤ 1 := by linarith
        rw [Function.iterate_succ_apply', hs.1, hs.2]
        refine ⟨?_, ?_⟩
        · have ha : |dynXi A ((T^[n]) P) +
                F (dynXi A ((T^[n]) P)) (dynEta A ((T^[n]) P))| ≤
              |dynXi A ((T^[n]) P)| + 2 * C * ε * |dynEta A ((T^[n]) P)| :=
            (abs_add_le _ _).trans (add_le_add (le_refl _) hFabs)
          have hb : |dynEta A ((T^[n]) P) * G (dynXi A ((T^[n]) P)) (dynEta A ((T^[n]) P))| ≤
              |dynEta A ((T^[n]) P)| * ((1 + lam) / 2) := by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left hGabs (abs_nonneg _)
          have hfin : 2 * C * ε * |dynEta A ((T^[n]) P)| +
              |dynEta A ((T^[n]) P)| * ((1 + lam) / 2) ≤ |dynEta A ((T^[n]) P)| := by
            have hmul := mul_le_mul_of_nonneg_left hcoef (abs_nonneg (dynEta A ((T^[n]) P)))
            nlinarith [hmul]
          linarith [ha, hb, ih1]
        · rw [abs_mul]
          have hmul := mul_le_mul ih2 hGabs (abs_nonneg _)
            (by positivity : (0 : ℝ) ≤ ((1 + lam) / 2) ^ n * ε)
          calc |dynEta A ((T^[n]) P)| * |G (dynXi A ((T^[n]) P)) (dynEta A ((T^[n]) P))|
              ≤ ((1 + lam) / 2) ^ n * ε * ((1 + lam) / 2) := hmul
            _ = ((1 + lam) / 2) ^ (n + 1) * ε := by ring
  refine ⟨fun n => (key n).1, fun n => ?_, fun n => (key n).2⟩
  exact (dyn_norm_le A _).trans (key n).1

end Work.EQ
