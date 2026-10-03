import Submission.Work.Interfaces.Basic
import Submission.Work.Interfaces.Parabolic

/-!
# Wiring: the challenge from the area statements

`main_of_parts` composes the areas: MSET gives `dimH ∂M ≤ 2`; for the lower bound, DYN gives an IFS
at the parameter `cOfAlpha (alphaOf a₁ a₂ (1/2))`, PARAM puts that parameter (a real rotation
number, main-cardioid boundary) in `∂M`, and TRANSFER turns the IFS into a dimension bound.
-/

open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter Topology

noncomputable section

namespace MandelDim

theorem alphaOf_half_eq (a₁ a₂ : ℕ) :
    alphaOf a₁ a₂ (1 / 2 : ℂ) = ((1 / ((a₁ : ℝ) - 1 / ((a₂ : ℝ) + 1 / 2)) : ℝ) : ℂ) := by
  unfold alphaOf; push_cast; ring

theorem alpha_half_mem (a₁ a₂ : ℕ) (h₁ : 2 ≤ a₁) (h₂ : 1 ≤ a₂) :
    0 < 1 / ((a₁ : ℝ) - 1 / ((a₂ : ℝ) + 1 / 2)) ∧ 1 / ((a₁ : ℝ) - 1 / ((a₂ : ℝ) + 1 / 2)) < 1 := by
  have ha₁ : (2 : ℝ) ≤ a₁ := by exact_mod_cast h₁
  have ha₂ : (1 : ℝ) ≤ a₂ := by exact_mod_cast h₂
  have hq : 1 / ((a₂ : ℝ) + 1 / 2) < 1 := by
    rw [div_lt_iff₀ (by linarith)]; linarith
  have hd : 1 < (a₁ : ℝ) - 1 / ((a₂ : ℝ) + 1 / 2) := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one (by linarith)]; exact hd

/-- Lower bound below any `x < 2`. -/
theorem lower_of_parts (hD : DynStatement) (hP : ParamStatement) (hT : TransferStatement)
    (x : ℝ) (hx : x < 2) : ENNReal.ofReal x ≤ dimH (frontier Mandelbrot) := by
  rcases le_or_gt x 0 with h0 | h0
  · rw [ENNReal.ofReal_of_nonpos h0]; exact zero_le
  set δ : ℝ := 2 - x with hδ
  have hδpos : 0 < δ := by linarith
  obtain ⟨N₁, N₂, hN⟩ := hD (δ / 4) (by linarith) 1 one_pos
  set a₁ : ℕ := max N₁ 2
  set a₂ : ℕ := max N₂ 1
  obtain ⟨N, K, hN2, hK, hlog, hifs⟩ :=
    hN a₁ a₂ (le_max_left _ _) (le_max_left _ _) (1 / 2 : ℂ) (by norm_num) (by norm_num)
      (by norm_num)
  have hmem := alpha_half_mem a₁ a₂ (le_max_right _ _) (le_max_right _ _)
  have hc₀ := hP _ hmem.1 hmem.2
  rw [← alphaOf_half_eq] at hc₀
  set a : ℝ := (x + δ / 2) / (x + 3 * δ / 4) with ha
  have hden : 0 < x + 3 * δ / 4 := by linarith
  have ha0 : 0 < a := by positivity
  have ha1 : a < 1 := by rw [ha, div_lt_one hden]; linarith
  have hT' := hT _ hc₀ N K hN2 hifs a ha0 ha1
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hT'
  have h1 : x + δ / 2 = a * (x + 3 * δ / 4) := by rw [ha]; field_simp
  have h2 : x + 3 * δ / 4 = 2 - δ / 4 := by rw [hδ]; ring
  calc x ≤ x + δ / 2 := by linarith
    _ = a * (2 - δ / 4) := by rw [h1, h2]
    _ ≤ a * (Real.log N / Real.log K) := mul_le_mul_of_nonneg_left hlog ha0.le

theorem main_of_parts (hM : MsetStatement) (hD : DynStatement) (hP : ParamStatement)
    (hT : TransferStatement) : dimH (frontier Mandelbrot) = 2 := by
  apply le_antisymm hM.2.2.2.2
  refine le_of_forall_lt_imp_le_of_dense fun y hy => ?_
  have hy' : y ≠ ⊤ := ne_top_of_lt hy
  have hyr : y.toReal < 2 := by
    have := (ENNReal.toReal_lt_toReal hy' (by norm_num)).2 hy
    simpa using this
  have := lower_of_parts hD hP hT y.toReal hyr
  rwa [ENNReal.ofReal_toReal hy'] at this

/-- The parabolic core from its areas (FATOU enters only through PERT). -/
theorem dyn_of_parts (hF : FatouStatement) (hPa : ParabStatement)
    (hPe : FatouStatement → PertStatement) (hH : HornStatement) (h61 : L61Statement)
    (h62 : L62Statement) (hF0 : F0FactsStatement) (hR : RepelStatement) : DynStatement :=
  hR hPa (hPe hF) hH h61 h62 hF0

/-- The challenge from ALL area statements. -/
theorem main_of_all (hM : MsetStatement) (hP : ParamStatement) (hT : TransferStatement)
    (hF : FatouStatement) (hPa : ParabStatement) (hPe : FatouStatement → PertStatement)
    (hH : HornStatement) (h61 : L61Statement) (h62 : L62Statement) (hF0 : F0FactsStatement)
    (hR : RepelStatement) : dimH (frontier Mandelbrot) = 2 :=
  main_of_parts hM (dyn_of_parts hF hPa hPe hH h61 h62 hF0 hR) hP hT

end MandelDim
