import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.half_log_discr_le
import Submission.Work.BW.logHeight_one_intermediate
import Submission.Work.BW.sigma_sum_le
import Submission.Work.BW.D_ge
import Submission.Work.BW.discr_term_le_weak
import Submission.Work.BW.slack_ge_dK_dF2_sum_tiny
import Submission.Work.BW.slack_ge_log_factorial_tiny

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Height

/-- **Discriminant-term estimate with a small slack constant `0.001`.**

This is `Work.BW.discr_term_le_weak` re-proved with the slack constant `0.1` replaced by
`0.001`; the two quantities that the arithmetic core `discr_weak_arith` must absorb,
`4·[K:ℚ]·[F:ℚ]²·∑σⱼ` and `2·[K:ℚ]·log(([F:ℚ])!)`, are dominated by `0.001·S·D` by the
`_tiny` slack estimates (with a large numerical margin), using
`∑σ ≤ r·dK^{r-1}·∏σ` (`sigma_sum_le`), `dF ≤ dK`, `h ≥ 19` (`ph_ge_nineteen`) and
`∏σ ≥ (1/dK)^r`. -/
theorem discr_term_le_tiny {K : Type*} [Field K] [NumberField K] {n r : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (c : ℝ) (hst : Standing φ α b k c)
    (v : ℕ) (L : Fin r → Fin n → ℤ) (α' : Fin r → K) (σ : Fin r → ℝ)
    (hBH : BH φ α b v c r L α' σ) (hr : 2 ≤ r) :
    (Module.finrank ↥(auxField α') K : ℝ) *
        ((1 / 2) * Real.log |((NumberField.discr ↥(auxField α') : ℤ) : ℝ)|)
      ≤ (Module.finrank ℚ K : ℝ) ^ 2 * ((∑ j, σ j) + (1 / 2) * r * Real.log 2)
        + 0.001 * ((pS r (Module.finrank ℚ K) (ph (hL b (Module.finrank ℚ K)) v) : ℝ) *
            pD r (Module.finrank ℚ K) σ) := by
  have hσpos : ∀ j, 0 < σ j := fun j => hBH.2.2.2.2.1 j
  have hhmod : ∀ j, hmod (α' j) (lamP φ α v L j) ≤ σ j := fun j => hBH.2.2.2.2.2.1 j
  have hgen : IntermediateField.adjoin ℚ (Set.range (alphaF α')) = ⊤ := by
    apply IntermediateField.lift_injective (auxField α')
    rw [IntermediateField.lift_adjoin (F := ℚ) (K := auxField α'), IntermediateField.lift_top]
    congr 1
    ext x
    simp [alphaF_coe]
  -- height hypothesis measured in `F = ℚ(α')`
  have hh : ∀ j : Fin r,
      Height.logHeight₁ (alphaF α' j) ≤ (Module.finrank ℚ ↥(auxField α') : ℝ) * σ j := by
    intro j
    have hK : Height.logHeight₁ ((alphaF α' j : ↥(auxField α')) : K)
        ≤ (Module.finrank ℚ K : ℝ) * σ j := by
      have h1 : Height.logHeight₁ (α' j) / (Module.finrank ℚ K : ℝ)
          ≤ hmod (α' j) (lamP φ α v L j) := le_max_left _ _
      have h2 : Height.logHeight₁ (α' j) / (Module.finrank ℚ K : ℝ) ≤ σ j :=
        le_trans h1 (hhmod j)
      have hpos : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
        exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
      rw [mul_comm]
      exact (div_le_iff₀ hpos).mp h2
    have hm : (Module.finrank ↥(auxField α') K : ℝ)
        * Height.logHeight₁ (alphaF α' j) ≤ (Module.finrank ℚ K : ℝ) * σ j := by
      rw [← logHeight_one_intermediate (auxField α') (alphaF α' j)]
      exact hK
    have htower : (Module.finrank ℚ K : ℝ)
        = (Module.finrank ↥(auxField α') K : ℝ) * (Module.finrank ℚ ↥(auxField α') : ℝ) := by
      rw [← Nat.cast_mul, mul_comm,
        Module.finrank_mul_finrank (F := ℚ) (K := ↥(auxField α')) (A := K)]
    have hmpos : (0 : ℝ) < (Module.finrank ↥(auxField α') K : ℝ) := by
      exact_mod_cast Module.finrank_pos (R := ↥(auxField α')) (M := K)
    rw [htower, mul_assoc] at hm
    exact le_of_mul_le_mul_left hm hmpos
  have hmain := half_log_discr_le (F := ↥(auxField α')) hr (alphaF α') hgen σ hσpos hh
  have hslA := slack_ge_dK_dF2_sum_tiny φ α b k c hst v L α' σ hBH hr
  have hslB := slack_ge_log_factorial_tiny φ α b k c hst v L α' σ hBH hr
  have htower : (Module.finrank ↥(auxField α') K : ℝ)
      * (Module.finrank ℚ ↥(auxField α') : ℝ) = (Module.finrank ℚ K : ℝ) := by
    rw [← Nat.cast_mul, mul_comm,
      Module.finrank_mul_finrank (F := ℚ) (K := ↥(auxField α')) (A := K)]
  have hm1 : (1 : ℝ) ≤ (Module.finrank ↥(auxField α') K : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ↥(auxField α')) (M := K)
  have hdF1 : (1 : ℝ) ≤ (Module.finrank ℚ ↥(auxField α') : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := ↥(auxField α'))
  have hX0 : (0 : ℝ) ≤ Finset.univ.sum fun j => σ j :=
    Finset.sum_nonneg (fun j _ => le_of_lt (hσpos j))
  exact discr_weak_arith (df := Module.finrank ℚ ↥(auxField α')) hr rfl htower hm1 hdF1 hX0
    hmain hslA hslB

end Work.BW
