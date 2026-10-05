import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPCore.GenFun.Basic

namespace Work.RPCore.GenFun

theorem add_bijective_of_lipschitzWith_lt_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : E → E} {K : NNReal} (hf : LipschitzWith K f) (hK : K < 1) :
    Function.Bijective (fun x : E => x + f x) := by
  have hKreal : (K : ℝ) < 1 := by exact_mod_cast hK
  refine ⟨?_, ?_⟩
  · -- injectivity: `x + f x = y + f y` forces `x = y` since `K < 1`
    intro x y h
    have h2 : x + f x = y + f y := h
    have hxy : x - y = f y - f x := by
      have h' : x - y = (x + f x) - (y + f y) + (f y - f x) := by abel
      rw [h', h2]; abel
    have hnorm : ‖x - y‖ = ‖f x - f y‖ := by rw [hxy, norm_sub_rev]
    have h1 : ‖f x - f y‖ ≤ (K : ℝ) * ‖x - y‖ := by
      simpa [dist_eq_norm] using hf.dist_le_mul x y
    have hd : ‖x - y‖ ≤ (K : ℝ) * ‖x - y‖ := by
      calc ‖x - y‖ = ‖f x - f y‖ := hnorm
        _ ≤ (K : ℝ) * ‖x - y‖ := h1
    have hzero : ‖x - y‖ = 0 := by nlinarith [hd, norm_nonneg (x - y), hKreal]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  · -- surjectivity: for each `y`, the map `x ↦ y - f x` is a contraction on the
    -- complete space `E`, so Banach's fixed point theorem gives `x = y - f x`.
    intro y
    have hg : LipschitzWith K (fun x : E => y - f x) := by
      have h := (LipschitzWith.const (y : E)).sub hf
      simpa using h
    have hc : ContractingWith K (fun x : E => y - f x) := ⟨hK, hg⟩
    obtain ⟨x, hx, -⟩ := hc.exists_fixedPoint y (edist_ne_top y _)
    exact ⟨x, (sub_eq_iff_eq_add.mp hx).symm⟩

end Work.RPCore.GenFun
