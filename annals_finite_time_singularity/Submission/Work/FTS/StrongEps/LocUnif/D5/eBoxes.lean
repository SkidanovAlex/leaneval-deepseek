import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The exhaustion boxes for the level-5 extraction
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif.D5

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Inner lower `z`-bound. -/
def ea (m : ℕ) : ℝ := 1 / ((m : ℝ) + 2)
/-- Inner upper `z`-bound. -/
def eb (m : ℕ) : ℝ := (m : ℝ) + 2
/-- Inner lower `θ`-bound. -/
def ec (m : ℕ) : ℝ := 1 / ((m : ℝ) + 2)
/-- Inner upper `θ`-bound. -/
def ed (m : ℕ) : ℝ := π / 2 - 1 / ((m : ℝ) + 2)
/-- Outer lower `z`-bound. -/
def ea₀ (m : ℕ) : ℝ := 1 / (2 * ((m : ℝ) + 2))
/-- Outer upper `z`-bound. -/
def eb₀ (m : ℕ) : ℝ := 2 * ((m : ℝ) + 2)
/-- Outer lower `θ`-bound. -/
def ec₀ (m : ℕ) : ℝ := 1 / (2 * ((m : ℝ) + 2))
/-- Outer upper `θ`-bound. -/
def ed₀ (m : ℕ) : ℝ := π / 2 - 1 / (2 * ((m : ℝ) + 2))

/-- The inner box of the exhaustion. -/
def eBox (m : ℕ) : Set (ℝ × ℝ) := Set.Icc (ea m) (eb m) ×ˢ Set.Icc (ec m) (ed m)

/-- The data box for the `z`-engine at stage `m`. -/
def eBoxZ (m : ℕ) : Set (ℝ × ℝ) := Set.Icc (ea₀ m) (eb₀ m) ×ˢ Set.Icc (ec m) (ed m)

/-- The data box for the `θ`-engine at stage `m`. -/
def eBoxT (m : ℕ) : Set (ℝ × ℝ) := Set.Icc (ea m) (eb m) ×ˢ Set.Icc (ec₀ m) (ed₀ m)

theorem ea_pos (m : ℕ) : 0 < ea m := by
  simp only [ea]; positivity

theorem eb_pos (m : ℕ) : 0 < eb m := by
  simp only [eb]; positivity

theorem ec_pos (m : ℕ) : 0 < ec m := by
  simp only [ec]; positivity

theorem ea₀_pos (m : ℕ) : 0 < ea₀ m := by
  simp only [ea₀]; positivity

theorem ec₀_pos (m : ℕ) : 0 < ec₀ m := by
  simp only [ec₀]; positivity

theorem ea₀_lt_ea (m : ℕ) : ea₀ m < ea m := by
  have h : 0 < (m : ℝ) + 2 := by positivity
  simp only [ea, ea₀]
  rw [div_lt_div_iff₀ (by positivity) h] <;> ring_nf <;> linarith

theorem two_le_natCast_add_two (m : ℕ) : (2 : ℝ) ≤ (m : ℝ) + 2 := by
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem ea_lt_eb (m : ℕ) : ea m < eb m := by
  have h : 0 < (m : ℝ) + 2 := by positivity
  have h2 : (2 : ℝ) ≤ (m : ℝ) + 2 := two_le_natCast_add_two m
  simp only [ea, eb]
  rw [div_lt_iff₀ h]
  nlinarith [h2, h]

theorem eb_lt_eb₀ (m : ℕ) : eb m < eb₀ m := by
  simp only [eb, eb₀]; linarith

theorem ec₀_lt_ec (m : ℕ) : ec₀ m < ec m := by
  have h : 0 < (m : ℝ) + 2 := by positivity
  simp only [ec, ec₀]
  rw [div_lt_div_iff₀ (by positivity) h] <;> ring_nf <;> linarith

theorem ec_lt_ed (m : ℕ) : ec m < ed m := by
  have h : 0 < (m : ℝ) + 2 := by positivity
  have h2 : (2 : ℝ) ≤ (m : ℝ) + 2 := two_le_natCast_add_two m
  have hp : 2 < π := by linarith [Real.pi_gt_three]
  have hb : 2 * (1 / ((m : ℝ) + 2)) ≤ 1 := by
    rw [mul_one_div, div_le_iff₀ h]; linarith [h2]
  have hc : (1 : ℝ) < π / 2 := by linarith [hp]
  simp only [ec, ed]
  linarith

theorem ed_lt_ed₀ (m : ℕ) : ed m < ed₀ m := by
  have h : 0 < (m : ℝ) + 2 := by positivity
  simp only [ed, ed₀]
  have h1 : 1 / (2 * ((m : ℝ) + 2)) < 1 / ((m : ℝ) + 2) := by
    rw [div_lt_div_iff₀ (by positivity) h] <;> ring_nf <;> linarith
  linarith

theorem ed₀_lt_pi (m : ℕ) : ed₀ m < π / 2 := by
  have h : 0 < 1 / (2 * ((m : ℝ) + 2)) := by positivity
  simp only [ed₀]; linarith

theorem ed_lt_pi (m : ℕ) : ed m < π / 2 :=
  lt_trans (ed_lt_ed₀ m) (ed₀_lt_pi m)

theorem eBox_subset_Q0 (m : ℕ) : eBox m ⊆ Work.FTS.EllipticEst.Q0 := by
  intro p hp
  have h1 : 0 < p.1 := lt_of_lt_of_le (ea_pos m) hp.1.1
  have h2 : 0 < p.2 := lt_of_lt_of_le (ec_pos m) hp.2.1
  have h3 : p.2 < π / 2 := lt_of_le_of_lt hp.2.2 (ed_lt_pi m)
  exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨h1, h2, h3⟩

theorem eBoxZ_subset_Q0 (m : ℕ) : eBoxZ m ⊆ Work.FTS.EllipticEst.Q0 := by
  intro p hp
  have h1 : 0 < p.1 := lt_of_lt_of_le (ea₀_pos m) hp.1.1
  have h2 : 0 < p.2 := lt_of_lt_of_le (ec_pos m) hp.2.1
  have h3 : p.2 < π / 2 := lt_of_le_of_lt hp.2.2 (ed_lt_pi m)
  exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨h1, h2, h3⟩

theorem eBoxT_subset_Q0 (m : ℕ) : eBoxT m ⊆ Work.FTS.EllipticEst.Q0 := by
  intro p hp
  have h1 : 0 < p.1 := lt_of_lt_of_le (ea_pos m) hp.1.1
  have h2 : 0 < p.2 := lt_of_lt_of_le (ec₀_pos m) hp.2.1
  have h3 : p.2 < π / 2 := lt_of_le_of_lt hp.2.2 (ed₀_lt_pi m)
  exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨h1, h2, h3⟩

theorem iUnion_eBox : (⋃ m : ℕ, eBox m) = Work.FTS.EllipticEst.Q0 := by
  ext p
  constructor
  · intro hp
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hp
    exact eBox_subset_Q0 m hm
  · intro hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    obtain ⟨N, hN⟩ := exists_nat_gt (max (max (1 / p.1) (1 / p.2))
      (max p.1 (1 / (π / 2 - p.2))))
    have hN1 : 1 / p.1 < (N : ℝ) := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hN2 : 1 / p.2 < (N : ℝ) := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hN3 : p.1 < (N : ℝ) := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
    have hN4 : 1 / (π / 2 - p.2) < (N : ℝ) :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    have hpos : 0 < π / 2 - p.2 := by linarith
    have hNpos : (0 : ℝ) < (N : ℝ) + 2 := by positivity
    refine Set.mem_iUnion.mpr ⟨N, ?_⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [ea, div_le_iff₀ hNpos]
      have hkey : 1 / p.1 * p.1 < (N : ℝ) * p.1 := mul_lt_mul_of_pos_right hN1 hz
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hz)] at hkey
      nlinarith [hkey]
    · rw [eb]; linarith
    · rw [ec, div_le_iff₀ hNpos]
      have hkey : 1 / p.2 * p.2 < (N : ℝ) * p.2 := mul_lt_mul_of_pos_right hN2 hθ0
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hθ0)] at hkey
      nlinarith [hkey]
    · rw [ed, le_sub_iff_add_le]
      have hkey : 1 / (π / 2 - p.2) * (π / 2 - p.2) < (N : ℝ) * (π / 2 - p.2) :=
        mul_lt_mul_of_pos_right hN4 hpos
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hpos)] at hkey
      have : 1 / ((N : ℝ) + 2) ≤ π / 2 - p.2 := by
        rw [div_le_iff₀ hNpos]
        have : (1 : ℝ) ≤ (π / 2 - p.2) * ((N : ℝ) + 2) := by nlinarith [hkey, hpos]
        linarith [this]
      linarith [this]

end Work.FTS.StrongEps.LocUnif.D5
