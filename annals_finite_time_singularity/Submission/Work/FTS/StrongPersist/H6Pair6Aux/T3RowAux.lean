import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Small `θ`-slice facts -/

/-- A single slot of `f` is dominated by the level-six integrand. -/
theorem slotW_slot_le6 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {a b : ℕ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hab : a + b ≤ 6) :
    Work.FTS.TransportS.slotW α a z θ * (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    rw [Work.FTS.TransportS.slotW_zero_eq α hθ]
    have h := sq_le_HkIntegrand_pure6 (f := f) (z := z) (θ := θ) α
      (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) b (by omega)
    simpa only [Work.Spaces.mixed_zero_right] using h
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    rw [Work.FTS.TransportS.slotW_of_pos_eq α ha1 hθ]
    exact sq_le_HkIntegrand_mixed6 α hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ b a ha1 hab

/-- The `ρ`-weighted product of two slots of `f` is dominated by the level-six integrand. -/
theorem leaf_slice_le6 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {a b k : ℕ}
    {ρ : ℝ → ℝ → ℝ} (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hab : a + b ≤ 6)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  obtain ⟨hρnn, hρle⟩ := Work.FTS.TransportS.IsLeafW_le α hα hleaf
  have hρ0 : 0 ≤ ρ z θ := hρnn z θ hz hθ.1 hθ.2
  have h1 : ρ z θ * (Work.Spaces.mixed (b - k) a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    (mul_le_mul_of_nonneg_right (hρle z θ hz hθ.1 hθ.2) (sq_nonneg _)).trans
      (slotW_slot_le6 hα hθ (by omega))
  have h2 : ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    (mul_le_mul_of_nonneg_right (hρle z θ hz hθ.1 hθ.2) (sq_nonneg _)).trans
      (slotW_slot_le6 hα hθ hab)
  have h3 : |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|
      ≤ (1 / 2) * (Work.Spaces.mixed (b - k) a f z θ) ^ 2
        + (1 / 2) * (Work.Spaces.mixed b a f z θ) ^ 2 := by
    rw [← abs_mul]
    exact abs_mul_le_half _ _
  calc ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|
      = ρ z θ * (|Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|) := by
        ring
    _ ≤ ρ z θ * ((1 / 2) * (Work.Spaces.mixed (b - k) a f z θ) ^ 2
          + (1 / 2) * (Work.Spaces.mixed b a f z θ) ^ 2) :=
        mul_le_mul_of_nonneg_left h3 hρ0
    _ = (1 / 2) * (ρ z θ * (Work.Spaces.mixed (b - k) a f z θ) ^ 2)
          + (1 / 2) * (ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) := by ring
    _ ≤ Work.Spaces.HkIntegrand α 6 f z θ := by linarith

/-- The three leaf weights are continuous on the open quadrant. -/
theorem continuousOn_leaf {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  rcases hleaf with rfl | rfl | ⟨-, rfl⟩
  · exact (continuousOn_w_sq_Q0.mul (continuousOn_sin_rpow_Q0 Work.Spaces.eta)).congr
      (fun p _ => rfl)
  · exact continuousOn_w_sq_Q0.congr (fun p _ => rfl)
  · exact (continuousOn_w_sq_Q0.mul (continuousOn_sin_rpow_Q0 (Work.Spaces.gam α))).congr
      (fun p _ => rfl)

/-- A `θ`-slice sum of `ρ`-weighted slot products, with coefficients bounded by `64`, is
dominated by `448` times the level-six integrand. -/
theorem group_sum_le {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hab : a + b ≤ 6) (P : ℕ → Prop)
    [DecidablePred P] {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (∑ k ∈ Finset.range (b + 1), (if P k then (b.choose k : ℝ)
        * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
        else 0))
      ≤ 448 * Work.Spaces.HkIntegrand α 6 f z θ := by
  have hchoose : ∀ k ∈ Finset.range (b + 1), (b.choose k : ℝ) ≤ 64 := by
    intro k hk
    have h1 : b.choose k ≤ 2 ^ b := Nat.choose_le_two_pow b k
    have h2 : 2 ^ b ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast (le_trans h1 h2 : b.choose k ≤ 64)
  have hstep : ∀ k ∈ Finset.range (b + 1),
      (if P k then (b.choose k : ℝ)
        * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
        else 0)
        ≤ 64 * Work.Spaces.HkIntegrand α 6 f z θ := by
    intro k hk
    by_cases hP : P k
    · rw [if_pos hP]
      have hle := leaf_slice_le6 (f := f) (k := k) (ρ := ρ) hα hleaf hab hz hθ
      have hc := hchoose k hk
      have hρnn : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα hleaf).1 z θ hz hθ.1 hθ.2
      exact mul_le_mul hc hle
        (mul_nonneg (mul_nonneg hρnn (abs_nonneg _)) (abs_nonneg _)) (by norm_num)
    · rw [if_neg hP]
      exact mul_nonneg (by norm_num) (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)
  have hcard : (Finset.range (b + 1)).card = b + 1 := Finset.card_range _
  have hle7 : ((b + 1 : ℕ) : ℝ) ≤ 7 := by
    have hb : b ≤ 6 := by omega
    exact_mod_cast (by omega : b + 1 ≤ 7)
  have hnn := Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  calc (∑ k ∈ Finset.range (b + 1), (if P k then (b.choose k : ℝ)
        * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
        else 0))
      ≤ ∑ _k ∈ Finset.range (b + 1), 64 * Work.Spaces.HkIntegrand α 6 f z θ :=
        Finset.sum_le_sum hstep
    _ = 64 * ((b + 1 : ℕ) : ℝ) * Work.Spaces.HkIntegrand α 6 f z θ := by
        rw [Finset.sum_const, hcard]
        simp only [nsmul_eq_mul]
        ring
    _ ≤ 448 * Work.Spaces.HkIntegrand α 6 f z θ := by
        have : (64 : ℝ) * ((b + 1 : ℕ) : ℝ) ≤ 448 := by nlinarith [hle7]
        exact mul_le_mul_of_nonneg_right this hnn

/-- A property holding for every `z > 0` holds a.e. for the measure restricted to `Iz`. -/
theorem ae_restrict_Iz_of_pos {p : ℝ → Prop} (h : ∀ z : ℝ, 0 < z → p z) :
    ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), p z := by
  rw [Work.Spaces.Iz]
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => h z hz)

/-- The first group of slots (those with at most four derivatives on the coefficient). -/
def B1f (a b : ℕ) (ρ : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (b + 1), (if k ≤ 4 then (b.choose k : ℝ)
    * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|) else 0)

/-- The second group of slots (those with at least five derivatives on the coefficient). -/
def B2f (a b : ℕ) (ρ : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (b + 1), (if 5 ≤ k then (b.choose k : ℝ)
    * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|) else 0)

theorem B2f_continuousOn {α : ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => B2f a b ρ f p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  simp only [B2f]
  refine continuousOn_finsetSum _ fun k _ => ?_
  by_cases h5 : 5 ≤ k
  · simp only [if_pos h5]
    exact continuousOn_const.mul
      (((continuousOn_leaf hleaf).mul ((hso.mixed (b - k) a).continuousOn).abs).mul
        ((hso.mixed b a).continuousOn).abs)
  · simp only [if_neg h5]; exact continuousOn_const

end Work.FTS.StrongPersist.H6Pair6Aux
