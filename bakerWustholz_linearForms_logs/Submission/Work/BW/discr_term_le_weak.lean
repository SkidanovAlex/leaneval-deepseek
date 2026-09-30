import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.logHeight_one_intermediate
import Submission.Work.BW.ph_ge_nineteen
import Submission.Work.BW.half_log_discr_le
import Submission.Work.BW.slack_ge_dK_dF2_sum
import Submission.Work.BW.slack_ge_log_factorial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Height

/-- Arithmetic core of the discriminant-term estimate. -/
lemma discr_weak_arith {df : ℕ} {m dF dK X B L : ℝ} {r : ℕ} (hr : 2 ≤ r)
    (hdF : (df : ℝ) = dF) (hmul : m * dF = dK) (hm1 : 1 ≤ m) (hdF1 : 1 ≤ dF) (hX : 0 ≤ X)
    (hmain : (1 / 2) * L ≤ Real.log (df.factorial : ℝ) + 2 * dF ^ 3 * X)
    (hslA : 4 * dK * dF ^ 2 * X ≤ B)
    (hslB : 2 * dK * Real.log (df.factorial : ℝ) ≤ B) :
    m * ((1 / 2) * L) ≤ dK ^ 2 * (X + (1 / 2) * r * Real.log 2) + B := by
  have hm0 : (0 : ℝ) ≤ m := le_trans zero_le_one hm1
  have hdF0 : (0 : ℝ) ≤ dF := le_trans zero_le_one hdF1
  have hlog0 : (0 : ℝ) ≤ Real.log (df.factorial : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero df))
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hdK0 : (0 : ℝ) ≤ dK := by nlinarith [hmul, hm0, hdF0]
  have hX0 : (0 : ℝ) ≤ dK ^ 2 * X := mul_nonneg (sq_nonneg _) hX
  have h1 : m * ((1 / 2) * L) ≤ m * (Real.log (df.factorial : ℝ) + 2 * dF ^ 3 * X) :=
    mul_le_mul_of_nonneg_left hmain hm0
  have hmle : m ≤ dK := by nlinarith [hmul, hdF1]
  have h2 : m * Real.log (df.factorial : ℝ) ≤ B / 2 := by
    have h : m * Real.log (df.factorial : ℝ) ≤ dK * Real.log (df.factorial : ℝ) :=
      mul_le_mul_of_nonneg_right hmle hlog0
    linarith
  have h3 : m * (2 * dF ^ 3 * X) ≤ dK ^ 2 * X + B / 2 := by
    have hid : m * (2 * dF ^ 3 * X) = 2 * dK * dF ^ 2 * X := by
      have : m * dF ^ 3 = dK * dF ^ 2 := by nlinarith [hmul]
      nlinarith [this]
    linarith [hslA]
  have h4 : m * (Real.log (df.factorial : ℝ) + 2 * dF ^ 3 * X)
      = m * Real.log (df.factorial : ℝ) + m * (2 * dF ^ 3 * X) := by ring
  have h5 : B / 2 + (dK ^ 2 * X + B / 2) ≤ dK ^ 2 * (X + (1 / 2) * r * Real.log 2) + B := by
    have : (0 : ℝ) ≤ dK ^ 2 * ((1 / 2) * (r : ℝ) * Real.log 2) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    linarith
  calc m * ((1 / 2) * L) ≤ m * (Real.log (df.factorial : ℝ) + 2 * dF ^ 3 * X) := h1
    _ = m * Real.log (df.factorial : ℝ) + m * (2 * dF ^ 3 * X) := h4
    _ ≤ B / 2 + (dK ^ 2 * X + B / 2) := add_le_add h2 h3
    _ ≤ dK ^ 2 * (X + (1 / 2) * r * Real.log 2) + B := h5

theorem discr_term_le_weak {K : Type*} [Field K] [NumberField K] {n r : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (c : ℝ) (hst : Standing φ α b k c)
    (v : ℕ) (L : Fin r → Fin n → ℤ) (α' : Fin r → K) (σ : Fin r → ℝ)
    (hBH : BH φ α b v c r L α' σ) (hr : 2 ≤ r) :
    (Module.finrank ↥(auxField α') K : ℝ) *
        ((1 / 2) * Real.log |((NumberField.discr ↥(auxField α') : ℤ) : ℝ)|)
      ≤ (Module.finrank ℚ K : ℝ) ^ 2 * ((∑ j, σ j) + (1 / 2) * r * Real.log 2)
        + 0.1 * ((pS r (Module.finrank ℚ K) (ph (hL b (Module.finrank ℚ K)) v) : ℝ) *
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
  have hslA := slack_ge_dK_dF2_sum φ α b k c hst v L α' σ hBH hr
  have hslB := slack_ge_log_factorial φ α b k c hst v L α' σ hBH hr
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
