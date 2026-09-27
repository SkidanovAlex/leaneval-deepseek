/-
# L2b — sub-windows: every chart extends to a window

`Submission/Work/EKLC6Route/exists_window.lean`

Statement `L2b — sub-windows` of `Submission/Work/EKLComp/C6GEOM_ROUTE_LEAD.md` §3.1:

Given a chart `c : Chart μ t` for a probability measure `μ` on `X₃`, there is a `Window μ t`
with `w.toChart = c`.

The construction (route lead §2.3) is: start from `C 0 = VtSet t ∩ V ρ`, and, while the window-mass
`μ (chartW c ∩ θ ⁻¹' C m)` is positive, refine by a level-`(m+1)` grid cell of positive window-mass
(this is possible because the level-`(m+1)` cells partition `SL3`).  This produces a decreasing
sequence `winCfam c` of Borel sets, all of positive window-mass, whose members are contained in
finer and finer grid cells; two elements of a level-`ℓ` cell inside `V ρ` differ by at most
`ρ / 2^ℓ` entrywise, whence their ratio lies in `V (3 (ρ/2^ℓ) (1 + 10ρ))`.

The remaining `hCtail` (and `hCsmall`) requirement is met by passing to a sub-sequence `φ` with
`φ 0 = 0` along which the masses decrease dyadically fast, which is `subseq_tail_le`.

Auxiliary definitions (`chartW`, `gridCell`, `winSel`, `winCfam`, …) live in
`Submission/Work/EKLC6Route/window_defs.lean`.
-/
import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Route.exists_chart
import Submission.Work.EKLC6Route.window_defs
import Submission.Work.EKLC6Route.subseq_tail_le
import Submission.Work.EKLC6Route.grid_cell_entry_close
import Submission.Work.EKLC6Route.mul_inv_mem_V_of_entry_close

noncomputable section
namespace Work.EKLC6Route
open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract Work.EKLComp
open Classical

variable {μ : MeasureTheory.Measure X3} {t : Fin 3 → ℝ}


/-! ## Elementary numerical bounds -/

/-- The bound used at `j = 0`, where no grid cell is available: two elements of `V ρ` have ratio in
`V (3 (2ρ) (1 + 10ρ)) ⊆ V (δ/100)` when `4000 ρ ≤ δ`. -/
theorem three_mul_two_rho_le {ρ δ : ℝ} (hρ : 0 < ρ) (hρδ : 4000 * ρ ≤ δ) (hρ10 : ρ ≤ 1 / 10) :
    3 * (2 * ρ) * (1 + 10 * ρ) ≤ δ / 100 := by
  nlinarith [hρ, hρδ, hρ10]

/-- The bound used for `j ≥ 1`: two elements of one level-`ℓ` cell inside `V ρ` have ratio in
`V (3 (ρ/2^ℓ) (1 + 10ρ)) ⊆ V ((1/2)^j δ / 100)` when `j ≤ ℓ` and `4000 ρ ≤ δ`. -/
theorem cell_bound_le {ρ δ : ℝ} (hρ : 0 < ρ) (hρδ : 4000 * ρ ≤ δ) (hρ10 : ρ ≤ 1 / 10)
    {j ℓ : ℕ} (hjl : j ≤ ℓ) :
    3 * (ρ / 2 ^ ℓ) * (1 + 10 * ρ) ≤ (1 / 2 : ℝ) ^ j * δ / 100 := by
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have h2l : (0 : ℝ) < 2 ^ ℓ := by positivity
  have h2 : (2 : ℝ) ^ j ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hjl
  have hratio : ρ / 2 ^ ℓ * 2 ^ j ≤ ρ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ h2l]
    exact mul_le_mul_of_nonneg_left h2 hρ.le
  have h11 : (0 : ℝ) < 1 + 10 * ρ := by linarith
  rw [show (1 / 2 : ℝ) ^ j * δ / 100 = δ / (100 * 2 ^ j) by
        rw [div_pow, one_pow]; ring]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 100 * 2 ^ j)]
  calc 3 * (ρ / 2 ^ ℓ) * (1 + 10 * ρ) * (100 * 2 ^ j)
      = 300 * (ρ / 2 ^ ℓ * 2 ^ j) * (1 + 10 * ρ) := by ring
    _ ≤ 300 * ρ * (1 + 10 * ρ) := by
        apply mul_le_mul_of_nonneg_right _ h11.le
        exact mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ ≤ δ := by nlinarith [hρ, hρ10, hρδ]

/-- Elementary bound: `|a - b| ≤ |a - c| + |b - c|`. -/
theorem abs_sub_le_abs_sub_add (a b c : ℝ) : |a - b| ≤ |a - c| + |b - c| := by
  have h : a - b = (a - c) - (b - c) := by ring
  rw [h]
  have h' := abs_sub_le (a - c) (0 : ℝ) (b - c)
  rw [sub_zero, zero_sub, abs_neg] at h'
  exact h'

/-! ## The window -/

theorem exists_window {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (c : Work.EKLC6Route.Chart μ t) :
    ∃ w : Work.EKLC6Route.Window μ t, w.toChart = c := by
  -- the raw decreasing sequence of cells has positive window-mass at every step
  have hanti : Antitone (fun j : ℕ => chartW c ∩ c.θ ⁻¹' winCfam c j) := by
    intro i j hij x hx
    exact ⟨hx.1, winCfam_antitone c hij hx.2⟩
  have hmeas : ∀ j : ℕ, NullMeasurableSet (chartW c ∩ c.θ ⁻¹' winCfam c j) μ := fun j =>
    ((measurableSet_chartW c).inter (c.hθ (measurableSet_winCfam c j))).nullMeasurableSet
  obtain ⟨φ, hφmono, hφ0, hφtail⟩ := subseq_tail_le μ hanti hmeas
  have hρ10 : c.ρ ≤ 1 / 10 := by linarith [c.hρδ, c.hδ1]
  refine ⟨{ toChart := c, C := fun j => winCfam c (φ j), lev := fun j => φ j,
            hC0 := ?_, hCmeas := ?_, hCanti := ?_, hCsmall := ?_, hCpos := ?_, hCtail := ?_ },
          rfl⟩
  · rw [hφ0, winCfam_zero]
  · intro j; exact measurableSet_winCfam c (φ j)
  · intro i j hij; exact winCfam_antitone c (hφmono.monotone hij)
  · intro j k hk k' hk'
    change k ∈ winCfam c (φ j) at hk
    change k' ∈ winCfam c (φ j) at hk'
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      -- no cell is imposed at the initial index; only `k, k' ∈ V ρ`
      have hkρ : k ∈ V c.ρ := winCfam_subset_V c (φ 0) hk
      have hk'ρ : k' ∈ V c.ρ := winCfam_subset_V c (φ 0) hk'
      have hK : (0 : ℝ) < 2 * c.ρ := by linarith [c.hρ]
      have hclose : ∀ p q : Fin 3,
          |(k' : Matrix (Fin 3) (Fin 3) ℝ) p q - (k : Matrix (Fin 3) (Fin 3) ℝ) p q|
            ≤ 2 * c.ρ := by
        intro p q
        have h1 : |(k' : Matrix (Fin 3) (Fin 3) ℝ) p q
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| < c.ρ := hk'ρ p q
        have h2 : |(k : Matrix (Fin 3) (Fin 3) ℝ) p q
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| < c.ρ := hkρ p q
        calc |(k' : Matrix (Fin 3) (Fin 3) ℝ) p q - (k : Matrix (Fin 3) (Fin 3) ℝ) p q|
            ≤ |(k' : Matrix (Fin 3) (Fin 3) ℝ) p q - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q|
              + |(k : Matrix (Fin 3) (Fin 3) ℝ) p q - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| :=
              abs_sub_le_abs_sub_add _ _ _
          _ ≤ 2 * c.ρ := by linarith
      have hmem := mul_inv_mem_V_of_entry_close c.hρ hρ10 hK hkρ hclose
      have hbound : 3 * (2 * c.ρ) * (1 + 10 * c.ρ) ≤ (1 / 2 : ℝ) ^ 0 * c.δ / 100 := by
        rw [pow_zero, one_mul]
        exact three_mul_two_rho_le c.hρ c.hρδ hρ10
      exact V_subset_V hbound hmem
    · have hjφ : j ≤ φ j := hφmono.id_le j
      have hφj1 : 1 ≤ φ j := le_trans hj hjφ
      have hkρ : k ∈ V c.ρ := winCfam_subset_V c (φ j) hk
      have hgrid : gridIdx c.ρ (φ j) k = gridIdx c.ρ (φ j) k' :=
        (winCfam_subset_gridCell c hφj1 hk).trans (winCfam_subset_gridCell c hφj1 hk').symm
      have hclose : ∀ p q : Fin 3,
          |(k' : Matrix (Fin 3) (Fin 3) ℝ) p q - (k : Matrix (Fin 3) (Fin 3) ℝ) p q|
            ≤ c.ρ / 2 ^ (φ j) :=
        fun p q => le_of_lt (grid_cell_entry_close c.hρ hgrid p q)
      have hK : (0 : ℝ) < c.ρ / 2 ^ (φ j) := div_pos c.hρ (by positivity)
      have hmem := mul_inv_mem_V_of_entry_close c.hρ hρ10 hK hkρ hclose
      exact V_subset_V (cell_bound_le c.hρ c.hρδ hρ10 hjφ) hmem
  · intro j; exact winCfam_pos c (φ j)
  · intro j; exact hφtail j

end Work.EKLC6Route
