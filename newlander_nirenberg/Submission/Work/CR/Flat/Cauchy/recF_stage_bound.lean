import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolRec
import Submission.Work.CR.Flat.Cauchy.dbarTransform_basic

namespace Work.CR.Flat.Cauchy

/-- Auxiliary: the constant `K = max 1 (4 * trRho * C₀) + 1` dominates `1`,
`2 * trRho * C₀` and `4 * trRho * C₀`. -/
private lemma recF_stage_K_props {C₀ : ℝ} (hC₀ : 0 < C₀) :
    1 ≤ max 1 (4 * trRho * C₀) + 1 ∧
    2 * trRho * C₀ ≤ max 1 (4 * trRho * C₀) + 1 ∧
    4 * trRho * C₀ ≤ max 1 (4 * trRho * C₀) + 1 ∧
    0 ≤ max 1 (4 * trRho * C₀) + 1 := by
  have htrC : 0 ≤ trRho * C₀ := mul_nonneg (le_of_lt trRho_pos) (le_of_lt hC₀)
  have h1 : (1 : ℝ) ≤ max 1 (4 * trRho * C₀) + 1 := by
    linarith [le_max_left (1 : ℝ) (4 * trRho * C₀)]
  have h2 : 2 * trRho * C₀ ≤ max 1 (4 * trRho * C₀) + 1 := by
    nlinarith [le_max_right (1 : ℝ) (4 * trRho * C₀), htrC]
  have h4 : 4 * trRho * C₀ ≤ max 1 (4 * trRho * C₀) + 1 := by
    linarith [le_max_right (1 : ℝ) (4 * trRho * C₀)]
  exact ⟨h1, h2, h4, le_trans zero_le_one h1⟩

theorem recF_stage_bound {n : ℕ} {α : ℝ} {C₀ S : ℝ} (hC₀ : 0 < C₀)
    (hC₀prop : ∀ (j : Fin n) {F : (Fin n → ℂ) → ℂ} {A H : ℝ}, 0 ≤ A → 0 ≤ H →
      (∀ z : Fin n → ℂ, z ∈ trackSet → ‖F z‖ ≤ A) →
      (∀ x y : Fin n → ℂ, x ∈ trackSet → y ∈ trackSet → ‖F x - F y‖ ≤ H * ‖x - y‖ ^ α) →
      (∀ z : Fin n → ℂ, (∀ l, l ≠ j → ‖z l‖ < trTrack) → ‖z j‖ ≤ cutOut →
        ‖dbarC openCut (z j) * F z‖ ≤ C₀ * A) ∧
      (∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → ‖a l‖ < trTrack) →
        (∀ l, l ≠ j → ‖a' l‖ < trTrack) →
        ‖dbarC openCut (a j) * F a - dbarC openCut (a' j) * F a'‖ ≤ C₀ * (A + H) * ‖a - a'‖ ^ α))
    {f : Fin n → (Fin n → ℂ) → ℂ} (hS0 : 0 ≤ S)
    (hA : ∀ j z, z ∈ trackSet → ‖f j z‖ ≤ S)
    (hH : ∀ j x y, x ∈ trackSet → y ∈ trackSet → ‖f j x - f j y‖ ≤ S * ‖x - y‖ ^ α)
    (hcont : ∀ m, m ≤ n → ∀ k : Fin n, Continuous (recF f m k)) :
    ∀ m, m ≤ n → ∀ k : Fin n,
      (∀ z, z ∈ trackSet → ‖recF f m k z‖ ≤ (max 1 (4 * trRho * C₀) + 1) ^ m * S) ∧
      (∀ x y, x ∈ trackSet → y ∈ trackSet →
        ‖recF f m k x - recF f m k y‖
          ≤ (max 1 (4 * trRho * C₀) + 1) ^ m * S * ‖x - y‖ ^ α) := by
  obtain ⟨hK1, hK2, hK4, hKpos⟩ := recF_stage_K_props hC₀
  have hcutOut_nn : 0 ≤ cutOut := le_of_lt cutOut_pos
  intro m
  induction m with
  | zero =>
      intro _ k
      exact ⟨fun z hz => by simpa using hA k z hz,
        fun x y hx hy => by simpa using hH k x y hx hy⟩
  | succ m ih =>
      intro hm1 k
      have hm : m ≤ n := Nat.le_of_succ_le hm1
      have hmlt : m < n := Nat.lt_of_succ_le hm1
      obtain ⟨hAm, hHm⟩ := ih hm k
      have hA0 : 0 ≤ (max 1 (4 * trRho * C₀) + 1) ^ m * S :=
        mul_nonneg (pow_nonneg hKpos m) hS0
      obtain ⟨hC1, hC2⟩ := hC₀prop (⟨m, hmlt⟩ : Fin n) (F := recF f m k)
        (A := (max 1 (4 * trRho * C₀) + 1) ^ m * S)
        (H := (max 1 (4 * trRho * C₀) + 1) ^ m * S) hA0 hA0 hAm hHm
      have hFcont : Continuous (recF f m k) := hcont m hm k
      have hgcont : Continuous
          (fun y : Fin n → ℂ => cutFbar (⟨m, hmlt⟩ : Fin n) y * recF f m k y) :=
        (contDiff_cutFbar (⟨m, hmlt⟩ : Fin n)).continuous.mul hFcont
      have hsupp : ∀ y : Fin n → ℂ, cutOut ≤ ‖y (⟨m, hmlt⟩ : Fin n)‖ →
          cutFbar (⟨m, hmlt⟩ : Fin n) y * recF f m k y = 0 :=
        fun y hy => by rw [cutFbar_eq_zero_of_ge hy, zero_mul]
      have hrec : recF f (m + 1) = stepData (⟨m, hmlt⟩ : Fin n) (recF f m) :=
        recF_succ_of_lt f hmlt
      have hstep : recF f (m + 1) k = dbarTransform trRho (⟨m, hmlt⟩ : Fin n)
          (fun y => cutFbar (⟨m, hmlt⟩ : Fin n) y * recF f m k y) := by
        rw [hrec]; rfl
      constructor
      · intro z hz
        have hbd : ∀ y : Fin n → ℂ, (∀ l, l ≠ (⟨m, hmlt⟩ : Fin n) → y l = z l) →
            ‖y (⟨m, hmlt⟩ : Fin n)‖ ≤ cutOut →
            ‖cutFbar (⟨m, hmlt⟩ : Fin n) y * recF f m k y‖
              ≤ C₀ * ((max 1 (4 * trRho * C₀) + 1) ^ m * S) := by
          intro y hy hyj
          have hyt : ∀ l, l ≠ (⟨m, hmlt⟩ : Fin n) → ‖y l‖ < trTrack := by
            intro l hl; rw [hy l hl]; exact hz l
          simpa using hC1 y hyt hyj
        have hb := (dbarTransform_basic (n := n) (ρ := trRho) (b := cutOut) trRho_pos
            hcutOut_nn (j := (⟨m, hmlt⟩ : Fin n))).1 hgcont hsupp
            (C₀ * ((max 1 (4 * trRho * C₀) + 1) ^ m * S)) z hbd
        rw [hstep]
        calc ‖dbarTransform trRho (⟨m, hmlt⟩ : Fin n)
              (fun y => cutFbar (⟨m, hmlt⟩ : Fin n) y * recF f m k y) z‖
            ≤ 2 * trRho * (C₀ * ((max 1 (4 * trRho * C₀) + 1) ^ m * S)) := hb
          _ = (2 * trRho * C₀) * ((max 1 (4 * trRho * C₀) + 1) ^ m * S) := by ring
          _ ≤ (max 1 (4 * trRho * C₀) + 1) * ((max 1 (4 * trRho * C₀) + 1) ^ m * S) :=
              mul_le_mul_of_nonneg_right hK2 hA0
          _ = (max 1 (4 * trRho * C₀) + 1) ^ (m + 1) * S := by rw [pow_succ]; ring
      · intro x y hx hy
        have hhold : ∀ a a' : Fin n → ℂ,
            (∀ l, l ≠ (⟨m, hmlt⟩ : Fin n) → a l = x l) →
            (∀ l, l ≠ (⟨m, hmlt⟩ : Fin n) → a' l = y l) →
            ‖cutFbar (⟨m, hmlt⟩ : Fin n) a * recF f m k a
              - cutFbar (⟨m, hmlt⟩ : Fin n) a' * recF f m k a'‖
              ≤ (C₀ * ((max 1 (4 * trRho * C₀) + 1) ^ m * S
                  + (max 1 (4 * trRho * C₀) + 1) ^ m * S)) * ‖a - a'‖ ^ α := by
          intro a a' ha ha'
          have hat : ∀ l, l ≠ (⟨m, hmlt⟩ : Fin n) → ‖a l‖ < trTrack := by
            intro l hl; rw [ha l hl]; exact hx l
          have ha't : ∀ l, l ≠ (⟨m, hmlt⟩ : Fin n) → ‖a' l‖ < trTrack := by
            intro l hl; rw [ha' l hl]; exact hy l
          simpa using hC2 a a' hat ha't
        have hb := (dbarTransform_basic (n := n) (ρ := trRho) (b := cutOut) trRho_pos
            hcutOut_nn (j := (⟨m, hmlt⟩ : Fin n))).2.1 hgcont hsupp α
            (C₀ * ((max 1 (4 * trRho * C₀) + 1) ^ m * S
              + (max 1 (4 * trRho * C₀) + 1) ^ m * S)) x y hhold
        rw [hstep]
        calc ‖dbarTransform trRho (⟨m, hmlt⟩ : Fin n)
              (fun y => cutFbar (⟨m, hmlt⟩ : Fin n) y * recF f m k y) x
              - dbarTransform trRho (⟨m, hmlt⟩ : Fin n)
              (fun y => cutFbar (⟨m, hmlt⟩ : Fin n) y * recF f m k y) y‖
            ≤ 2 * trRho * (C₀ * ((max 1 (4 * trRho * C₀) + 1) ^ m * S
                + (max 1 (4 * trRho * C₀) + 1) ^ m * S)) * ‖x - y‖ ^ α := hb
          _ = (4 * trRho * C₀) * ((max 1 (4 * trRho * C₀) + 1) ^ m * S)
              * ‖x - y‖ ^ α := by ring
          _ ≤ (max 1 (4 * trRho * C₀) + 1) * ((max 1 (4 * trRho * C₀) + 1) ^ m * S)
              * ‖x - y‖ ^ α := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hK4 hA0) (Real.rpow_nonneg (norm_nonneg _) α)
          _ = (max 1 (4 * trRho * C₀) + 1) ^ (m + 1) * S * ‖x - y‖ ^ α := by
              rw [pow_succ]; ring

end Work.CR.Flat.Cauchy
