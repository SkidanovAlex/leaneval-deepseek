import ChallengeDeps
import Submission.FUP.Metric

open FractalUncertainty
open MeasureTheory FourierTransform Metric
open scoped ENNReal

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-- Porosity is monotone: smaller `ν` and a narrower scale range make the statement easier. -/
lemma PorousOnLines.mono {ν ν' α₀ α₁ α₀' α₁' : ℝ} {X : Set ℝᵈ}
    (hX : PorousOnLines ν α₀ α₁ X) (hν : ν' ≤ ν)
    (ha₀ : α₀ ≤ α₀') (ha₁ : α₁' ≤ α₁) (hα₀' : 0 < α₀') :
    PorousOnLines ν' α₀' α₁' X := by
  intro R hR y₁ y₂ hd
  have hRge0 : 0 ≤ R := le_of_lt (lt_trans hα₀' (Set.mem_Ioo.mp hR).1)
  have hR' : R ∈ Set.Ioo α₀ α₁ := by
    exact ⟨lt_of_le_of_lt ha₀ (Set.mem_Ioo.mp hR).1, lt_of_lt_of_le (Set.mem_Ioo.mp hR).2 ha₁⟩
  rcases hX R hR' y₁ y₂ hd with ⟨x, hx, hball⟩
  refine ⟨x, hx, ?_⟩
  apply Set.subset_empty_iff.mp
  intro z hz
  have hzX : z ∈ closedBall x (ν * R) ∩ X :=
    ⟨closedBall_subset_closedBall (mul_le_mul_of_nonneg_right hν hRge0) hz.1, hz.2⟩
  simpa [hball] using hzX

/-- A subset of a porous set is porous (same scales). -/
lemma PorousOnLines.mono_set {ν α₀ α₁ : ℝ} {X Y : Set ℝᵈ}
    (hX : PorousOnLines ν α₀ α₁ X) (hYX : Y ⊆ X) :
    PorousOnLines ν α₀ α₁ Y := by
  intro R hR y₁ y₂ hd
  rcases hX R hR y₁ y₂ hd with ⟨x, hx, hball⟩
  refine ⟨x, hx, ?_⟩
  apply Set.subset_empty_iff.mp
  intro z hz
  have hzX : z ∈ closedBall x (ν * R) ∩ X := ⟨hz.1, hYX hz.2⟩
  simpa [hball] using hzX

/-- PorousOnBalls is monotone: smaller `ν` and narrower range. -/
lemma PorousOnBalls.mono {ν ν' α₀ α₁ α₀' α₁' : ℝ} {X : Set ℝᵈ}
    (hX : PorousOnBalls ν α₀ α₁ X) (hν : ν' ≤ ν)
    (ha₀ : α₀ ≤ α₀') (ha₁ : α₁' ≤ α₁) (hα₀' : 0 < α₀') :
    PorousOnBalls ν' α₀' α₁' X := by
  intro y R hR
  have hRge0 : 0 ≤ R := le_of_lt (lt_trans hα₀' (Set.mem_Ioo.mp hR).1)
  have hR' : R ∈ Set.Ioo α₀ α₁ := by
    exact ⟨lt_of_le_of_lt ha₀ (Set.mem_Ioo.mp hR).1, lt_of_lt_of_le (Set.mem_Ioo.mp hR).2 ha₁⟩
  rcases hX y R hR' with ⟨x, hx, hball⟩
  refine ⟨x, hx, ?_⟩
  apply Set.subset_empty_iff.mp
  intro z hz
  have hzX : z ∈ closedBall x (ν * R) ∩ X :=
    ⟨closedBall_subset_closedBall (mul_le_mul_of_nonneg_right hν hRge0) hz.1, hz.2⟩
  simpa [hball] using hzX

/-- Dilating a `ν`-porous set by `s > 0` gives a `ν`-porous set with scaled scale range. -/
lemma PorousOnLines_smul {ν α₀ α₁ s : ℝ} {Y : Set ℝᵈ} (hs : 0 < s)
    (hY : PorousOnLines ν α₀ α₁ Y) :
    PorousOnLines ν (s * α₀) (s * α₁) ((fun y : ℝᵈ => s • y) '' Y) := by
  intro R hR y₁ y₂ hd
  let u₁ : ℝᵈ := s⁻¹ • y₁
  let u₂ : ℝᵈ := s⁻¹ • y₂
  have hR₀ : R / s ∈ Set.Ioo α₀ α₁ := by
    constructor
    · rw [lt_div_iff₀ hs]
      simpa [mul_comm] using (Set.mem_Ioo.mp hR).1
    · rw [div_lt_iff₀ hs]
      simpa [mul_comm, mul_left_comm, mul_assoc] using (Set.mem_Ioo.mp hR).2
  have hd₀ : dist u₁ u₂ = R / s := by
    dsimp [u₁, u₂]
    rw [dist_smul₀']
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hs))]
    rw [hd]
    field_simp [ne_of_gt hs]
  rcases hY (R / s) hR₀ u₁ u₂ hd₀ with ⟨x, hx, hball⟩
  have hsu₁ : s • u₁ = y₁ := by
    dsimp [u₁]
    simp [smul_smul, ne_of_gt hs]
  have hsu₂ : s • u₂ = y₂ := by
    dsimp [u₂]
    simp [smul_smul, ne_of_gt hs]
  refine ⟨s • x, ?_, ?_⟩
  · simpa [hsu₁, hsu₂] using smul_mem_segment s hx
  apply Set.subset_empty_iff.mp
  intro z hz
  rcases hz.2 with ⟨w, hwY, rfl⟩
  have hzX : w ∈ closedBall x (ν * (R / s)) ∩ Y := by
    constructor
    · rw [Metric.mem_closedBall]
      have hz1 : dist (s • w) (s • x) ≤ ν * R := Metric.mem_closedBall.mp hz.1
      have hdist : s * dist w x ≤ ν * R := by
        simpa [dist_smul_of_nonneg s (le_of_lt hs) w x] using hz1
      have hle : dist w x ≤ (ν * R) / s := by
        rw [le_div_iff₀ hs]
        simpa [mul_comm] using hdist
      calc
        dist w x ≤ (ν * R) / s := hle
        _ = ν * (R / s) := by ring
    · exact hwY
  simpa [hball] using hzX

/-- Translating a porous set preserves porosity (same scales). -/
lemma PorousOnLines_add_const {ν α₀ α₁ : ℝ} {Y : Set ℝᵈ} (a : ℝᵈ)
    (hY : PorousOnLines ν α₀ α₁ Y) :
    PorousOnLines ν α₀ α₁ ((fun y : ℝᵈ => a + y) '' Y) := by
  intro R hR y₁ y₂ hd
  have hd₀ : dist (-a + y₁) (-a + y₂) = R := by
    calc
      dist (-a + y₁) (-a + y₂) = ‖(-a + y₁) - (-a + y₂)‖ := by rw [dist_eq_norm]
      _ = ‖y₁ - y₂‖ := by congr 1; abel
      _ = R := by
        simpa [dist_eq_norm] using hd
  rcases hY R hR (-a + y₁) (-a + y₂) hd₀ with ⟨x, hx, hball⟩
  refine ⟨a + x, ?_, ?_⟩
  · have hx' : a + x ∈ segment ℝ (a + (-a + y₁)) (a + (-a + y₂)) :=
      image_add_subset_segment hx
    simpa using hx'
  · apply Set.subset_empty_iff.mp
    intro z hz
    rcases hz.2 with ⟨w, hwY, rfl⟩
    have hzX : w ∈ closedBall x (ν * R) ∩ Y := by
      constructor
      · rw [Metric.mem_closedBall]
        have hz1 : dist (a + w) (a + x) ≤ ν * R := Metric.mem_closedBall.mp hz.1
        have hiso : dist (a + w) (a + x) = dist w x := by
          rw [dist_eq_norm, dist_eq_norm]
          congr 1
          abel
        simpa [hiso] using hz1
      · exact hwY
    simpa [hball] using hzX

/-- Adding a ball-neighbourhood keeps line porosity, with a worsened porosity parameter
`ν' < ν` and a raised lower scale `r / (ν - ν')`.  (Lemma (a) in the appendix of Cohen's paper.) -/
lemma PorousOnLines_add_ball {ν ν' α₀ α₁ r : ℝ} {Y : Set ℝᵈ}
    (hν' : 0 < ν') (hν'lt : ν' < ν)
    (hlo : α₀ ≤ r / (ν - ν'))
    (hY : PorousOnLines ν α₀ α₁ Y) :
    PorousOnLines ν' (r / (ν - ν')) α₁ (addSet Y (closedBall 0 r)) := by
  have hνν' : 0 < ν - ν' := sub_pos.mpr hν'lt
  intro R hR y₁ y₂ hd
  have hR' : R ∈ Set.Ioo α₀ α₁ := by
    constructor
    · exact lt_of_le_of_lt hlo (Set.mem_Ioo.mp hR).1
    · exact (Set.mem_Ioo.mp hR).2
  rcases hY R hR' y₁ y₂ hd with ⟨x, hx, hball⟩
  refine ⟨x, hx, ?_⟩
  apply Set.subset_empty_iff.mp
  intro z hz
  rcases hz.2 with ⟨y, hyY, w, hw, rfl⟩
  have hz1 : dist (y + w) x ≤ ν' * R := Metric.mem_closedBall.mp hz.1
  have hwr : dist w 0 ≤ r := Metric.mem_closedBall.mp hw
  have hdist_le : dist y x ≤ r + ν' * R := by
    have hd1 : dist y (y + w) ≤ r := by
      have hd1' : dist y (y + w) = dist w 0 := by
        rw [dist_eq_norm, dist_eq_norm]
        calc
          ‖y - (y + w)‖ = ‖-w‖ := by congr 1; abel
          _ = ‖w‖ := by rw [norm_neg]
          _ = ‖w - 0‖ := by simp
      rw [hd1']
      exact hwr
    calc
      dist y x ≤ dist y (y + w) + dist (y + w) x := dist_triangle y (y + w) x
      _ ≤ r + ν' * R := add_le_add hd1 hz1
  have hmain : r < (ν - ν') * R := by
    simpa [mul_comm] using (div_lt_iff₀ hνν').mp (Set.mem_Ioo.mp hR).1
  have hdist_lt : dist y x < ν * R := by
    nlinarith [hdist_le, hmain]
  have hy : y ∈ closedBall x (ν * R) := by
    rw [Metric.mem_closedBall]
    exact le_of_lt hdist_lt
  have hc : y ∈ closedBall x (ν * R) ∩ Y := ⟨hy, hyY⟩
  simpa [hball] using hc

/-- Dilating a set porous on balls. -/
lemma PorousOnBalls_smul {ν α₀ α₁ s : ℝ} {Y : Set ℝᵈ} (hs : 0 < s)
    (hY : PorousOnBalls ν α₀ α₁ Y) :
    PorousOnBalls ν (s * α₀) (s * α₁) ((fun y : ℝᵈ => s • y) '' Y) := by
  intro y R hR
  have hRlo : α₀ < R / s := by
    rw [lt_div_iff₀ hs]
    simpa [mul_comm] using (Set.mem_Ioo.mp hR).1
  have hRhi : R / s < α₁ := by
    rw [div_lt_iff₀ hs]
    simpa [mul_comm, mul_left_comm, mul_assoc] using (Set.mem_Ioo.mp hR).2
  rcases hY (s⁻¹ • y) (R / s) ⟨hRlo, hRhi⟩ with ⟨w, hw, hball⟩
  refine ⟨s • w, ?_, ?_⟩
  · rw [Metric.mem_closedBall] at hw ⊢
    calc
      dist (s • w) y = s * dist w (s⁻¹ • y) := by
        have hy : y = s • (s⁻¹ • y) := by
          simp [smul_smul, mul_inv_cancel₀ (ne_of_gt hs)]
        calc
          dist (s • w) y = dist (s • w) (s • (s⁻¹ • y)) := by rw [← hy]
          _ = s * dist w (s⁻¹ • y) := by
            rw [dist_smul_of_nonneg s (le_of_lt hs) w (s⁻¹ • y)]
      _ ≤ R / 2 := by
        have h1 : s * dist w (s⁻¹ • y) ≤ s * ((R / s) / 2) :=
          mul_le_mul_of_nonneg_left hw (le_of_lt hs)
        calc
          s * dist w (s⁻¹ • y) ≤ s * ((R / s) / 2) := h1
          _ = R / 2 := by field_simp [ne_of_gt hs]
  · apply Set.subset_empty_iff.mp
    intro z hz
    rcases hz.2 with ⟨w', hw'Y, rfl⟩
    have hw' : w' ∈ closedBall w (ν * (R / s)) ∩ Y := by
      constructor
      · rw [Metric.mem_closedBall]
        have hz1 : dist (s • w') (s • w) ≤ ν * R := Metric.mem_closedBall.mp hz.1
        have hscaled : s * dist w' w ≤ ν * R := by
          simpa [dist_smul_of_nonneg s (le_of_lt hs) w' w] using hz1
        have hle : dist w' w ≤ (ν * R) / s := by
          rw [le_div_iff₀ hs]
          simpa [mul_comm] using hscaled
        calc
          dist w' w ≤ (ν * R) / s := hle
          _ = ν * (R / s) := by ring
      · exact hw'Y
    simpa [hball] using hw'

/-- Translating a set porous on balls. -/
lemma PorousOnBalls_add_const {ν α₀ α₁ : ℝ} {Y : Set ℝᵈ} (a : ℝᵈ)
    (hY : PorousOnBalls ν α₀ α₁ Y) :
    PorousOnBalls ν α₀ α₁ ((fun y : ℝᵈ => a + y) '' Y) := by
  intro y R hR
  rcases hY (-a + y) R hR with ⟨x, hx, hball⟩
  refine ⟨a + x, ?_, ?_⟩
  · rw [Metric.mem_closedBall] at hx ⊢
    have hiso : dist (a + x) (a + (-a + y)) = dist x (-a + y) := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    have hy : a + (-a + y) = y := by abel
    rw [hy] at hiso
    rwa [hiso]
  · apply Set.subset_empty_iff.mp
    intro z hz
    rcases hz.2 with ⟨w, hwY, rfl⟩
    have hw' : w ∈ closedBall x (ν * R) ∩ Y := by
      constructor
      · rw [Metric.mem_closedBall]
        have hz1 : dist (a + w) (a + x) ≤ ν * R := Metric.mem_closedBall.mp hz.1
        have hiso : dist (a + w) (a + x) = dist w x := by
          rw [dist_eq_norm, dist_eq_norm]
          congr 1
          abel
        simpa [hiso] using hz1
      · exact hwY
    simpa [hball] using hw'

end Submission.FUP
