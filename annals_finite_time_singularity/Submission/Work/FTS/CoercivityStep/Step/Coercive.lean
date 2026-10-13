/-
# The coercivity half of the induction step (tex 686–700)

Given one level of the induction `StepInputs α n IP cc CC κ`, the paper's recursion

  `HkIPStep 1 1 IP (𝓛_Γ^T f) f = (𝓛_Γ^T f, f)_{ℋ^n} + (D_θ𝓛_Γ^T f, D_θ f)_{ℋ^n}
                                  + (D_z𝓛_Γ^T f, D_z f)_{ℋ^n}`

dominates `(cc/4)|f|²_{ℋ^{n+1}}` for every `f ∈ HkAdm α (n+1)`.

The proof is the paper's, with the constants made explicit:

* splitting `D_θ𝓛_Γ^T f = 𝓛_Γ^T(D_θ f) + E₁` and `D_z𝓛_Γ^T f = 𝓛_Γ^T(D_z f) + E₂`
  (additivity of the pairing, using `StepReg α n`), coercivity at level `n` applied to
  `f`, `D_θ f`, `D_z f` (`HkAdm_dth`), and Cauchy–Schwarz plus `CommutBounds` for the two
  defects;
* the two defect pairings are then bounded by
  `CC√(κ X₀)√X₁ ≤ (cc/2)√(X₀X₁) ≤ (cc/4)(X₀+X₁)` and
  `CC√(κ(X₀+X₁))√X₂ ≤ (cc/2)√((X₀+X₁)X₂) ≤ (cc/4)(X₀+X₁+X₂)`,
  where the balance `CC√κ ≤ cc/2` of `StepInputs` is exactly what is needed;
* adding up, `cc X₀ + cc X₁ + cc X₂ - (cc/4)(X₀+X₁) - (cc/4)(X₀+X₁+X₂)
  = (cc/2)(X₀+X₁) + (3cc/4)X₂ ≥ (cc/4)(X₀+X₁+X₂) ≥ (cc/4)|f|²_{ℋ^{n+1}}`.
-/
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.HkAdm_dth
import Submission.Work.Coercivity.HkSq_succ_le
import Submission.Work.FTS.CoercivityStep.Defs
import Submission.Work.FTS.CoercivityStep.Norm.HkAdm_mono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.CoercivityStep.Norm (HkAdm_mono)

namespace Work.FTS.CoercivityStep

set_option autoImplicit false

/-- `HkAdm` is contained in the linearity class `HkReg`. -/
theorem HkAdm.hkReg {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.Coercivity.HkAdm α k f) : HkReg α k f :=
  ⟨h.1, by simpa using h.2.1 0 0 (by omega)⟩

/-- The AM–GM inequality `2√a√b ≤ a + b` in the form used by the defect bounds. -/
theorem two_mul_sqrt_mul_sqrt_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * (Real.sqrt a * Real.sqrt b) ≤ a + b := by
  have h := sq_nonneg (Real.sqrt a - Real.sqrt b)
  rw [sub_sq, Real.sq_sqrt ha, Real.sq_sqrt hb] at h
  linarith

/-- The AM–GM inequality in the form `√a√b ≤ (a+b)/2`. -/
theorem sqrt_mul_sqrt_le_half_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a * Real.sqrt b ≤ (a + b) / 2 := by
  have h := two_mul_sqrt_mul_sqrt_le a b ha hb
  linarith

/-- **The coercivity half of the induction step.**  With the level-`n` input package
`StepInputs α n IP cc CC κ`, the paper's recursion with `c₁ = c₂ = 1` dominates
`(cc/4)|f|²_{ℋ^{n+1}}` on the admissible class `HkAdm α (n+1)`. -/
theorem HkIPStep_coercive (α : ℝ) (hα : 0 < α) (n : ℕ) (hn : 1 ≤ n)
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} {cc CC κ : ℝ}
    (h : StepInputs α n IP cc CC κ) :
    ∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α (n + 1) f →
      (cc / 4) * Work.Spaces.HkSq α (n + 1) f
        ≤ Work.Coercivity.HkIPStep 1 1 IP (Work.Coercivity.LGammaT α f) f := by
  obtain ⟨hcc0, hCC0, hIPc, hcs, hreg, hcom, hbal⟩ := h
  obtain ⟨hκ0, hE1, hE2⟩ := hcom
  intro f hf
  -- level-`n` coercivity is applied to `f`, `D_θ f`, `D_z f`
  have hf0 : Work.Coercivity.HkAdm α n f := HkAdm_mono α (Nat.le_succ n) hf
  obtain ⟨hf1, hf2⟩ := Work.Coercivity.HkAdm_dth α n hf
  have hR1 : HkReg α n (Work.Spaces.Dth f) := HkAdm.hkReg hf1
  have hR2 : HkReg α n (Work.Spaces.Dz f) := HkAdm.hkReg hf2
  -- the regularity package
  obtain ⟨hA, hEA, hB, hEB, hLA, hLB⟩ := hreg f hf
  -- the two splittings
  have hfun1 : Work.Spaces.Dth (Work.Coercivity.LGammaT α f)
      = Work.Coercivity.LGammaT α (Work.Spaces.Dth f) + E₁ α f := by
    simp only [E₁]; abel
  have hfun2 : Work.Spaces.Dz (Work.Coercivity.LGammaT α f)
      = Work.Coercivity.LGammaT α (Work.Spaces.Dz f) + E₂ α f := by
    simp only [E₂]; abel
  have hsplit1 : IP (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f)
      = IP (Work.Coercivity.LGammaT α (Work.Spaces.Dth f)) (Work.Spaces.Dth f)
        + IP (E₁ α f) (Work.Spaces.Dth f) := by
    rw [hfun1]
    exact hIPc.prop.core.add_fst _ _ _ hA hEA hR1 (hfun1 ▸ hLA)
  have hsplit2 : IP (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f)
      = IP (Work.Coercivity.LGammaT α (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
        + IP (E₂ α f) (Work.Spaces.Dz f) := by
    rw [hfun2]
    exact hIPc.prop.core.add_fst _ _ _ hB hEB hR2 (hfun2 ▸ hLB)
  -- coercivity at level `n`
  have hc0 := hIPc.coercive f hf0
  have hc1 := hIPc.coercive (Work.Spaces.Dth f) hf1
  have hc2 := hIPc.coercive (Work.Spaces.Dz f) hf2
  set X0 : ℝ := Work.Spaces.HkSq α n f with hX0def
  set X1 : ℝ := Work.Spaces.HkSq α n (Work.Spaces.Dth f) with hX1def
  set X2 : ℝ := Work.Spaces.HkSq α n (Work.Spaces.Dz f) with hX2def
  have hX0 : 0 ≤ X0 := by rw [hX0def]; exact Work.Spaces.HkSq_nonneg α n f
  have hX1 : 0 ≤ X1 := by rw [hX1def]; exact Work.Spaces.HkSq_nonneg α n (Work.Spaces.Dth f)
  have hX2 : 0 ≤ X2 := by rw [hX2def]; exact Work.Spaces.HkSq_nonneg α n (Work.Spaces.Dz f)
  have hcc4 : 0 < cc / 4 := by linarith
  -- the two defect bounds
  have hb1 : |IP (E₁ α f) (Work.Spaces.Dth f)| ≤ (cc / 4) * (X0 + X1) := by
    have h1 := hcs (E₁ α f) (Work.Spaces.Dth f) hEA hR1
    have hN1 : Work.Spaces.HkNorm α n (E₁ α f) ≤ Real.sqrt (κ * X0) := by
      rw [Work.Spaces.HkNorm, hX0def]
      exact Real.sqrt_le_sqrt (hE1 f hf)
    have hN1' : 0 ≤ Work.Spaces.HkNorm α n (E₁ α f) := Work.Spaces.HkNorm_nonneg α n _
    have hN2 : Work.Spaces.HkNorm α n (Work.Spaces.Dth f) = Real.sqrt X1 := by
      rw [Work.Spaces.HkNorm, hX1def]
    have hs1 : 0 ≤ Real.sqrt X1 := Real.sqrt_nonneg _
    have hs2 : 0 ≤ Real.sqrt (κ * X0) := Real.sqrt_nonneg _
    have hs3 : 0 ≤ CC := le_of_lt hCC0
    have hstep1 : CC * Work.Spaces.HkNorm α n (E₁ α f)
        * Work.Spaces.HkNorm α n (Work.Spaces.Dth f)
        ≤ CC * Real.sqrt (κ * X0) * Real.sqrt X1 := by
      rw [hN2]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hN1 hs3) le_rfl hs1 (mul_nonneg hs3 hs2)
    have hstep2 : CC * Real.sqrt (κ * X0) * Real.sqrt X1 ≤ (cc / 4) * (X0 + X1) := by
      rw [Real.sqrt_mul (le_of_lt hκ0) X0]
      have hprod : Real.sqrt X0 * Real.sqrt X1 ≤ (X0 + X1) / 2 :=
        sqrt_mul_sqrt_le_half_add X0 X1 hX0 hX1
      have hcchalf : (0:ℝ) ≤ cc / 2 := by linarith
      calc CC * (Real.sqrt κ * Real.sqrt X0) * Real.sqrt X1
          = (CC * Real.sqrt κ) * (Real.sqrt X0 * Real.sqrt X1) := by ring
        _ ≤ (cc / 2) * ((X0 + X1) / 2) :=
            mul_le_mul hbal hprod (by positivity) hcchalf
        _ = (cc / 4) * (X0 + X1) := by ring
    exact le_trans h1 (le_trans hstep1 hstep2)
  have hb2 : |IP (E₂ α f) (Work.Spaces.Dz f)| ≤ (cc / 4) * ((X0 + X1) + X2) := by
    have h1 := hcs (E₂ α f) (Work.Spaces.Dz f) hEB hR2
    have hN1 : Work.Spaces.HkNorm α n (E₂ α f) ≤ Real.sqrt (κ * (X0 + X1)) := by
      rw [Work.Spaces.HkNorm, hX0def, hX1def]
      exact Real.sqrt_le_sqrt (hE2 f hf)
    have hN2 : Work.Spaces.HkNorm α n (Work.Spaces.Dz f) = Real.sqrt X2 := by
      rw [Work.Spaces.HkNorm, hX2def]
    have hs1 : 0 ≤ Real.sqrt X2 := Real.sqrt_nonneg _
    have hs2 : 0 ≤ Real.sqrt (κ * (X0 + X1)) := Real.sqrt_nonneg _
    have hs3 : 0 ≤ CC := le_of_lt hCC0
    have hstep1 : CC * Work.Spaces.HkNorm α n (E₂ α f)
        * Work.Spaces.HkNorm α n (Work.Spaces.Dz f)
        ≤ CC * Real.sqrt (κ * (X0 + X1)) * Real.sqrt X2 := by
      rw [hN2]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hN1 hs3) le_rfl hs1 (mul_nonneg hs3 hs2)
    have hstep2 : CC * Real.sqrt (κ * (X0 + X1)) * Real.sqrt X2
        ≤ (cc / 4) * ((X0 + X1) + X2) := by
      rw [Real.sqrt_mul (le_of_lt hκ0) (X0 + X1)]
      have hS : 0 ≤ X0 + X1 := by linarith
      have hprod : Real.sqrt (X0 + X1) * Real.sqrt X2 ≤ ((X0 + X1) + X2) / 2 :=
        sqrt_mul_sqrt_le_half_add (X0 + X1) X2 hS hX2
      have hcchalf : (0:ℝ) ≤ cc / 2 := by linarith
      calc CC * (Real.sqrt κ * Real.sqrt (X0 + X1)) * Real.sqrt X2
          = (CC * Real.sqrt κ) * (Real.sqrt (X0 + X1) * Real.sqrt X2) := by ring
        _ ≤ (cc / 2) * (((X0 + X1) + X2) / 2) :=
            mul_le_mul hbal hprod (by positivity) hcchalf
        _ = (cc / 4) * ((X0 + X1) + X2) := by ring
    exact le_trans h1 (le_trans hstep1 hstep2)
  -- the level-`n+1` norm is dominated by the three level-`n` norms
  have hY : Work.Spaces.HkSq α (n + 1) f ≤ X0 + X1 + X2 := by
    rw [hX0def, hX1def, hX2def]
    exact Work.Coercivity.HkSq_succ_le α hα n hn hf.1 (by simpa using hf.2.1 0 0 (by omega))
  -- assemble
  have hlow : cc * X0 + (cc * X1 + -((cc / 4) * (X0 + X1)))
      + (cc * X2 + -((cc / 4) * ((X0 + X1) + X2)))
      ≤ IP (Work.Coercivity.LGammaT α f) f
        + IP (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f)
        + IP (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f) := by
    have h2 : -(IP (E₁ α f) (Work.Spaces.Dth f)) ≤ (cc / 4) * (X0 + X1) := by
      linarith [neg_le_abs (IP (E₁ α f) (Work.Spaces.Dth f)), hb1]
    have h3 : -(IP (E₂ α f) (Work.Spaces.Dz f)) ≤ (cc / 4) * ((X0 + X1) + X2) := by
      linarith [neg_le_abs (IP (E₂ α f) (Work.Spaces.Dz f)), hb2]
    rw [hsplit1, hsplit2]
    linarith [hc0, hc1, hc2, h2, h3]
  have hccX0 : 0 ≤ cc * X0 := mul_nonneg (le_of_lt (by linarith : (0:ℝ) < cc)) hX0
  have hccX1 : 0 ≤ cc * X1 := mul_nonneg (le_of_lt (by linarith : (0:ℝ) < cc)) hX1
  have hccX2 : 0 ≤ cc * X2 := mul_nonneg (le_of_lt (by linarith : (0:ℝ) < cc)) hX2
  have hmid : (cc / 4) * (X0 + X1 + X2)
      ≤ cc * X0 + (cc * X1 + -((cc / 4) * (X0 + X1)))
        + (cc * X2 + -((cc / 4) * ((X0 + X1) + X2))) := by
    linarith [hccX0, hccX1, hccX2]
  have hfinal : (cc / 4) * (X0 + X1 + X2)
      ≤ IP (Work.Coercivity.LGammaT α f) f
        + IP (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f)
        + IP (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f) :=
    le_trans hmid hlow
  have hgoal : (cc / 4) * Work.Spaces.HkSq α (n + 1) f
      ≤ IP (Work.Coercivity.LGammaT α f) f
        + IP (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f)
        + IP (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f) := by
    calc (cc / 4) * Work.Spaces.HkSq α (n + 1) f ≤ (cc / 4) * (X0 + X1 + X2) :=
          mul_le_mul_of_nonneg_left hY (le_of_lt hcc4)
      _ ≤ _ := hfinal
  rw [Work.Coercivity.HkIPStep]
  simpa using hgoal

end Work.FTS.CoercivityStep
