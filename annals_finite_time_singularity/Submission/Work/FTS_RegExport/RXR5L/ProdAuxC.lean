import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXR5L.ProdAuxB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- The `Jet` clause of the product lemma. -/
theorem prod_jet {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (h : ProdData α S A B Q R) :
    Work.FTS.Regularity.Jet α S (8 * A * B) (fun z θ τ => Q z θ τ * R z θ τ) := by
  have hAB : 0 ≤ A * B := mul_nonneg h.A_nonneg h.B_nonneg
  have hp2 : 0 ≤ 2 * A * B := by linarith [hAB]
  have hp3 : 0 ≤ 3 * A * B := by linarith [hAB]
  have hp8 : 0 ≤ 8 * A * B := by linarith [hAB]
  refine ⟨hp8, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    have h1 := prod_abs_le hα h hz hθ hτ
    nlinarith [h1, hAB]
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    change |Q z θ τ * R z θ τ - Q z' θ' τ' * R z' θ' τ'|
      ≤ 8 * A * B * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α
    set D := |z - z'| + |θ - θ'| + |τ - τ'| with hD
    have hD0 : 0 ≤ D := by positivity
    have hDα : 0 ≤ D ^ α := Real.rpow_nonneg hD0 α
    have hDge : |θ - θ'| ≤ D := by rw [hD]; linarith [abs_nonneg (z - z'), abs_nonneg (τ - τ')]
    by_cases hθe : θ = 0 ∨ θ = π / 2
    · have hR0 : R z θ τ = 0 := by
        have hb := h.RGam z θ τ hz hθ hτ
        rw [Gmp_eq_zero_of_endpoint hα hθe, mul_zero] at hb
        exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
      have hP0 : Q z θ τ * R z θ τ = 0 := by rw [hR0, mul_zero]
      rw [hP0, zero_sub, abs_neg]
      by_cases hθe' : θ' = 0 ∨ θ' = π / 2
      · have hR0' : R z' θ' τ' = 0 := by
          have hb := h.RGam z' θ' τ' hz' hθ' hτ'
          rw [Gmp_eq_zero_of_endpoint hα hθe', mul_zero] at hb
          exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
        rw [hR0', mul_zero, abs_zero]
        positivity
      · push Not at hθe'
        have hθI' : θ' ∈ Set.Ioo 0 (π / 2) :=
          ⟨lt_of_le_of_ne hθ'.1 (fun hc => hθe'.1 hc.symm), lt_of_le_of_ne hθ'.2 hθe'.2⟩
        have hθ'I : θ' ∈ Work.Spaces.Iθ := ⟨hθ'.1, hθ'.2⟩
        rw [abs_mul]
        have hQb := abs_Q_le_min h hz' hθI' hτ'
        have hRb := h.RGam z' θ' τ' hz' hθ'I hτ'
        have h1 : |Q z' θ' τ'| * |R z' θ' τ'| ≤ (A * min z' 1) * (B * Gmp α θ') :=
          mul_le_mul hQb hRb (abs_nonneg _)
            (mul_nonneg h.A_nonneg (le_min hz' zero_le_one))
        have h2 : (A * min z' 1) * (B * Gmp α θ') ≤ A * B * dang θ' ^ α := by
          have hmin : min z' 1 ≤ 1 := min_le_right _ _
          have hG : Gmp α θ' ≤ dang θ' ^ α := Gmp_le_dang_rpow hα hθ'I
          have h3 : A * min z' 1 ≤ A := by
            simpa using mul_le_mul_of_nonneg_left hmin h.A_nonneg
          have h4 : B * Gmp α θ' ≤ B * dang θ' ^ α :=
            mul_le_mul_of_nonneg_left hG h.B_nonneg
          have h5 : 0 ≤ B * Gmp α θ' := mul_nonneg h.B_nonneg (Gmp_nonneg hθ'I)
          calc (A * min z' 1) * (B * Gmp α θ') ≤ A * (B * Gmp α θ') :=
                mul_le_mul_of_nonneg_right h3 h5
            _ ≤ A * (B * dang θ' ^ α) := mul_le_mul_of_nonneg_left h4 h.A_nonneg
            _ = A * B * dang θ' ^ α := by ring
        have h6 : dang θ' ≤ |θ - θ'| := by
          rcases hθe with h0 | h2p
          · rw [h0, zero_sub, abs_neg, abs_of_pos hθI'.1]
            exact dang_le_self θ'
          · rw [h2p]
            rw [abs_of_pos (by linarith [hθI'.2])]
            exact dang_le_half θ'
        have h7 : dang θ' ^ α ≤ |θ - θ'| ^ α :=
          Real.rpow_le_rpow (dang_nonneg_of_mem hθ'I) h6 hα.le
        have h8 : |θ - θ'| ^ α ≤ D ^ α := Real.rpow_le_rpow (abs_nonneg _) hDge hα.le
        calc |Q z' θ' τ'| * |R z' θ' τ'| ≤ A * B * dang θ' ^ α := le_trans h1 h2
          _ ≤ A * B * |θ - θ'| ^ α := mul_le_mul_of_nonneg_left h7 hAB
          _ ≤ A * B * D ^ α := mul_le_mul_of_nonneg_left h8 hAB
          _ ≤ 8 * A * B * D ^ α := by nlinarith [hAB, hDα]
    · push Not at hθe
      have hθI : θ ∈ Set.Ioo 0 (π / 2) :=
        ⟨lt_of_le_of_ne hθ.1 (fun hc => hθe.1 hc.symm), lt_of_le_of_ne hθ.2 hθe.2⟩
      have hθIt : θ ∈ Work.Spaces.Iθ := ⟨hθ.1, hθ.2⟩
      by_cases hθe' : θ' = 0 ∨ θ' = π / 2
      · have hR0 : R z' θ' τ' = 0 := by
          have hb := h.RGam z' θ' τ' hz' hθ' hτ'
          rw [Gmp_eq_zero_of_endpoint hα hθe', mul_zero] at hb
          exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
        have hP0 : Q z' θ' τ' * R z' θ' τ' = 0 := by rw [hR0, mul_zero]
        rw [hP0, sub_zero]
        rw [abs_mul]
        have hQb := abs_Q_le_min h hz hθI hτ
        have hRb := h.RGam z θ τ hz hθIt hτ
        have h1 : |Q z θ τ| * |R z θ τ| ≤ (A * min z 1) * (B * Gmp α θ) :=
          mul_le_mul hQb hRb (abs_nonneg _)
            (mul_nonneg h.A_nonneg (le_min hz zero_le_one))
        have h2 : (A * min z 1) * (B * Gmp α θ) ≤ A * B * dang θ ^ α := by
          have hmin : min z 1 ≤ 1 := min_le_right _ _
          have hG : Gmp α θ ≤ dang θ ^ α := Gmp_le_dang_rpow hα hθIt
          have h3 : A * min z 1 ≤ A := by
            simpa using mul_le_mul_of_nonneg_left hmin h.A_nonneg
          have h4 : B * Gmp α θ ≤ B * dang θ ^ α :=
            mul_le_mul_of_nonneg_left hG h.B_nonneg
          have h5 : 0 ≤ B * Gmp α θ := mul_nonneg h.B_nonneg (Gmp_nonneg hθIt)
          calc (A * min z 1) * (B * Gmp α θ) ≤ A * (B * Gmp α θ) :=
                mul_le_mul_of_nonneg_right h3 h5
            _ ≤ A * (B * dang θ ^ α) := mul_le_mul_of_nonneg_left h4 h.A_nonneg
            _ = A * B * dang θ ^ α := by ring
        have h6 : dang θ ≤ |θ - θ'| := by
          rcases hθe' with h0 | h2p
          · rw [h0, sub_zero, abs_of_pos hθI.1]
            exact dang_le_self θ
          · rw [h2p, abs_of_nonpos (by linarith [hθI.2])]
            have : -(θ - π / 2) = π / 2 - θ := by ring
            rw [this]
            exact dang_le_half θ
        have h7 : dang θ ^ α ≤ |θ - θ'| ^ α :=
          Real.rpow_le_rpow (dang_nonneg_of_mem hθIt) h6 hα.le
        have h8 : |θ - θ'| ^ α ≤ D ^ α := Real.rpow_le_rpow (abs_nonneg _) hDge hα.le
        calc |Q z θ τ| * |R z θ τ| ≤ A * B * dang θ ^ α := le_trans h1 h2
          _ ≤ A * B * |θ - θ'| ^ α := mul_le_mul_of_nonneg_left h7 hAB
          _ ≤ A * B * D ^ α := mul_le_mul_of_nonneg_left h8 hAB
          _ ≤ 8 * A * B * D ^ α := by nlinarith [hAB, hDα]
      · push Not at hθe'
        have hθI' : θ' ∈ Set.Ioo 0 (π / 2) :=
          ⟨lt_of_le_of_ne hθ'.1 (fun hc => hθe'.1 hc.symm), lt_of_le_of_ne hθ'.2 hθe'.2⟩
        have e1 := prod_zmod hα hα1 h hz hz' hθI hτ
        have e2 := prod_thmod hα hα1 h hz' hθI hθI' hτ
        have e3 := prod_taumod hα hα1 h hz' hθI' hτ hτ'
        have h4 := Paux_abs_sub_le_three (Q z θ τ * R z θ τ) (Q z' θ τ * R z' θ τ)
          (Q z' θ' τ * R z' θ' τ) (Q z' θ' τ' * R z' θ' τ')
        have h5 : |z - z'| ^ α ≤ D ^ α :=
          Real.rpow_le_rpow (abs_nonneg _) (by rw [hD]; linarith [abs_nonneg (θ - θ'), abs_nonneg (τ - τ')]) hα.le
        have h6 : |θ - θ'| ^ α ≤ D ^ α := Real.rpow_le_rpow (abs_nonneg _) hDge hα.le
        have h7 : |τ - τ'| ^ α ≤ D ^ α :=
          Real.rpow_le_rpow (abs_nonneg _) (by rw [hD]; linarith [abs_nonneg (z - z'), abs_nonneg (θ - θ')]) hα.le
        have i1 : 2 * A * B * |z - z'| ^ α ≤ 2 * A * B * D ^ α :=
          mul_le_mul_of_nonneg_left h5 hp2
        have i2 : 3 * A * B * |θ - θ'| ^ α ≤ 3 * A * B * D ^ α :=
          mul_le_mul_of_nonneg_left h6 hp3
        have i3 : 2 * A * B * |τ - τ'| ^ α ≤ 2 * A * B * D ^ α :=
          mul_le_mul_of_nonneg_left h7 hp2
        have i4 : 2 * A * B * D ^ α + 3 * A * B * D ^ α + 2 * A * B * D ^ α
            ≤ 8 * A * B * D ^ α := by nlinarith [hAB, hDα]
        linarith [h4, e1, e2, e3, i1, i2, i3, i4]

/-- The `z`-derivative clause of the product lemma. -/
theorem prod_zderiv {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α)
    (h : ProdData α S A B Q R) :
    ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Q z' θ τ * R z' θ τ) d z ∧ |d| ≤ 2 * A * B := by
  have hAB : 0 ≤ A * B := mul_nonneg h.A_nonneg h.B_nonneg
  intro τ hτ θ hθ z hz
  by_cases hθe : θ = 0 ∨ θ = π / 2
  · have hv : (fun z' => Q z' θ τ * R z' θ τ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      have hb := h.RGam z' θ τ hz'.le hθ hτ
      rw [Gmp_eq_zero_of_endpoint hα hθe, mul_zero] at hb
      have hR0 : R z' θ τ = 0 := abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
      rw [hR0, mul_zero]
    exact ⟨0, (hasDerivAt_const z 0).congr_of_eventuallyEq hv, by rw [abs_zero]; linarith [hAB]⟩
  · push Not at hθe
    have hθI : θ ∈ Set.Ioo 0 (π / 2) :=
      ⟨lt_of_le_of_ne hθ.1 (fun hc => hθe.1 hc.symm), lt_of_le_of_ne hθ.2 hθe.2⟩
    have hdQ := h.Qdz z θ τ hz hθI.1 hθI.2 hτ
    obtain ⟨dR, hdR, hdRb⟩ := h.Rjet.2 τ hτ θ hθ z hz
    refine ⟨Work.Spaces.pz (fun z θ => Q z θ τ) z θ * R z θ τ + Q z θ τ * dR, ?_, ?_⟩
    · exact hdQ.hasDerivAt.mul hdR
    · have h1 : |Work.Spaces.pz (fun z θ => Q z θ τ) z θ| ≤ A := pz_abs_le h hz hθI hτ
      have h2 : |R z θ τ| ≤ B := abs_R_le hα h hz.le hθ hτ
      have h3 : |Q z θ τ| ≤ A := abs_Q_le h hz.le hθI hτ
      calc |Work.Spaces.pz (fun z θ => Q z θ τ) z θ * R z θ τ + Q z θ τ * dR|
          ≤ |Work.Spaces.pz (fun z θ => Q z θ τ) z θ * R z θ τ| + |Q z θ τ * dR| :=
            abs_add_le _ _
        _ = |Work.Spaces.pz (fun z θ => Q z θ τ) z θ| * |R z θ τ| + |Q z θ τ| * |dR| := by
            rw [abs_mul, abs_mul]
        _ ≤ A * B + A * B :=
            add_le_add (mul_le_mul h1 h2 (abs_nonneg _) h.A_nonneg)
              (mul_le_mul h3 hdRb (abs_nonneg _) h.A_nonneg)
        _ = 2 * A * B := by ring

/-- **The product lemma of `EllProd_C1JetFull`.** -/
theorem prod_C1Jet_of_vanish {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (h : ProdData α S A B Q R) :
    ∃ N : ℝ, 0 ≤ N ∧
      Work.FTS.RegPkgGal.C1Jet α S N (fun z θ τ => Q z θ τ * R z θ τ) := by
  have hAB : 0 ≤ A * B := mul_nonneg h.A_nonneg h.B_nonneg
  have hp8 : 0 ≤ 8 * A * B := by linarith [hAB]
  refine ⟨8 * A * B, hp8, prod_jet hα hα1 h, ?_⟩
  intro τ hτ θ hθ z hz
  obtain ⟨d, hd, hdb⟩ := prod_zderiv hα h τ hτ θ hθ z hz
  exact ⟨d, hd, le_trans hdb (by linarith [hAB])⟩

end Work.FTS_RegExport.RXR5L
