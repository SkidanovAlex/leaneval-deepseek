import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop
import Submission.Work.FTS_RegExport.RXT.SysAux.Theta_ops
import Submission.Work.FTS_RegExport.RXT.SysAux.PieceCalc
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.Inputs

noncomputable section

open MeasureTheory Set Filter

/-- **The `Θ`-slots of the profile `F`.**  Given the uniform bounds and the differentiability of
the `D_z`-jets of `L₁₂ F` (order `≤ 2`) and of `𝔽K F` (`≤ 1`), together with the level-one
identity `z ∂_z(L₁₂ F) = -𝔽K F` on `(0,∞)`, the three `Θ`-slots

* `Uop α (Theta α F)/sin(2θ)`,
* `L₁₂ F · c2m`,
* `Vop (Theta α F)`

have uniformly bounded mixed jets of order `≤ 2` on the open quadrant. -/
theorem theta_part_theta {α CL : ℝ} (hαG : 0 < α) (hCL0 : 0 < CL) {F : ℝ → ℝ → ℝ}
    (hL12jet : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 F z) z| ≤ CL)
    (hFKjet : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.FK F z) z| ≤ CL)
    (hL12diff : ∀ c : ℕ, c ≤ 2 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c (fun z => Work.Construction.L12 F z)) z)
    (hFKdiff : ∀ b : ℕ, b ≤ 1 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (fun z => Work.Construction.FK F z)) z)
    (hL12d : ∀ z : ℝ, 0 < z →
      z * deriv (fun z' => Work.Construction.L12 F z') z = -Work.Construction.FK F z) :
    ∃ C : ℝ, 0 < C ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop α (Work.Construction.Theta α F)
          z θ / Real.sin (2 * θ)) z θ| ≤ C) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (fun z θ => Work.Construction.L12 F z
          * Work.Construction.c2m θ) z θ| ≤ C) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Work.Construction.Vop (Work.Construction.Theta α F)) z θ| ≤ C) := by
  set C2 : ℝ := (3 / (4 * α)) * CL + (1 / 4) * CL with hC2
  set C3 : ℝ := 1000 * CL with hC3
  set C4 : ℝ := 1000 * ((1 / (2 * α)) * CL) with hC4
  have hC2pos : 0 < C2 := by
    rw [hC2]
    have := mul_pos (by positivity : (0:ℝ) < 3 / (4 * α)) hCL0
    linarith
  have hC4pos : 0 < C4 := by rw [hC4]; positivity
  have hConj3 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => Work.Construction.L12 F z
        * Work.Construction.c2m θ) z θ| ≤ C3 := by
    intro j i hji z θ hz hθ0 hθ1
    have hcomm : (fun z θ => Work.Construction.L12 F z * Work.Construction.c2m θ)
        = fun z θ => Work.Construction.c2m θ * Work.Construction.L12 F z := by
      funext z θ; ring
    rw [hcomm, Work.FTS.Nonlinear.Pieces.mixed_ang_rad (fun θ => Work.Construction.c2m θ)
      (fun z => Work.Construction.L12 F z) j i z θ]
    rw [abs_mul]
    have hang : |Work.Spaces.DthIter i (fun x θ' => Work.Construction.c2m θ') 0 θ| ≤ 1000 := by
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi
        rw [Work.Spaces.DthIter_zero, Work.Construction.c2m]
        have h1 : |Real.cos (2 * θ)| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
        have h2 : Real.sin θ ^ 2 ≤ 1 := by
          have hs : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
          nlinarith [sq_abs (Real.sin θ), abs_nonneg (Real.sin θ)]
        calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
            ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := by
              rw [sub_eq_add_neg]
              exact le_trans (abs_add_le _ _) (le_of_eq (by rw [abs_neg]))
          _ = |Real.cos (2 * θ)| + Real.sin θ ^ 2 := by
              rw [abs_of_nonneg (sq_nonneg (Real.sin θ))]
          _ ≤ 1 + 1 := add_le_add h1 h2
          _ = 2 := by norm_num
          _ ≤ 1000 := by norm_num
      · have h := Work.FTS.Nonlinear.Pieces.DthIter_c2m_le i hi (by omega) θ
        have hsin2 : Real.sin (2 * θ) ^ (2 : ℝ) ≤ 1 :=
          Real.rpow_le_one (Real.sin_pos_of_pos_of_lt_pi (by linarith)
            (by linarith [Real.pi_pos])).le (Real.sin_le_one _) (by norm_num)
        linarith [h, mul_le_mul_of_nonneg_left hsin2 (by norm_num : (0:ℝ) ≤ 1000)]
    rw [hC3]
    linarith [abs_nonneg (Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 F z) z),
      hL12jet j (by omega) z hz,
      mul_le_mul hang (hL12jet j (by omega) z hz) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1000)]
  have hConj4 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.Construction.Vop (Work.Construction.Theta α F)) z θ| ≤ C4 := by
    intro j i hji z θ hz hθ0 hθ1
    have hEqOn : Set.EqOn (Function.uncurry (fun z θ => Work.Construction.Vop
          (Work.Construction.Theta α F) z θ))
        (Function.uncurry (fun z θ => Work.Construction.c2m θ
          * ((1 / (2 * α)) * Work.Construction.L12 F z)))
        Work.Construction.Qd := by
      intro p hp
      obtain ⟨hz', hθ0', hθ1'⟩ := hp
      have hOp := Work.FTS_RegExport.RXT.SysAux.Theta_ops hαG (F := F) hL12d p.1 p.2 hz' hθ0' hθ1'
      show Work.Construction.Vop (Work.Construction.Theta α F) p.1 p.2
        = Work.Construction.c2m p.2 * ((1 / (2 * α)) * Work.Construction.L12 F p.1)
      have h2α : (2 : ℝ) * α ≠ 0 := by positivity
      have hU' : Work.Construction.Vop (Work.Construction.Theta α F) p.1 p.2 * (2 * α)
          = Work.Construction.c2m p.2 * Work.Construction.L12 F p.1 := by
        linarith [hOp.1]
      rw [show Work.Construction.c2m p.2 * ((1 / (2 * α)) * Work.Construction.L12 F p.1)
          = Work.Construction.c2m p.2 * Work.Construction.L12 F p.1 / (2 * α) from by ring,
        eq_div_iff h2α]
      linarith [hU']
    have hmix := Work.FTS_RegExport.RXT.SysAux.mixed_congr_of_isOpen isOpen_Qd hEqOn j i z θ
      ⟨hz, hθ0, hθ1⟩
    rw [hmix, Work.FTS.Nonlinear.Pieces.mixed_ang_rad (fun θ => Work.Construction.c2m θ)
      (fun z => (1 / (2 * α)) * Work.Construction.L12 F z) j i z θ]
    rw [abs_mul]
    have hval' : Work.Elliptic.DzdIter j (fun z => (1 / (2 * α)) * Work.Construction.L12 F z) z
        = (1 / (2 * α)) * Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 F z) z :=
      congrFun (DzdIter_const_mul j (1 / (2 * α)) (fun z => Work.Construction.L12 F z)) z
    rw [hval', abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * α))]
    have hang : |Work.Spaces.DthIter i (fun x θ' => Work.Construction.c2m θ') 0 θ| ≤ 1000 := by
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi
        rw [Work.Spaces.DthIter_zero, Work.Construction.c2m]
        have h1 : |Real.cos (2 * θ)| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
        have h2 : Real.sin θ ^ 2 ≤ 1 := by
          have hs : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
          nlinarith [sq_abs (Real.sin θ), abs_nonneg (Real.sin θ)]
        calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
            ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := by
              rw [sub_eq_add_neg]
              exact le_trans (abs_add_le _ _) (le_of_eq (by rw [abs_neg]))
          _ = |Real.cos (2 * θ)| + Real.sin θ ^ 2 := by
              rw [abs_of_nonneg (sq_nonneg (Real.sin θ))]
          _ ≤ 1 + 1 := add_le_add h1 h2
          _ = 2 := by norm_num
          _ ≤ 1000 := by norm_num
      · have h := Work.FTS.Nonlinear.Pieces.DthIter_c2m_le i hi (by omega) θ
        have hsin2 : Real.sin (2 * θ) ^ (2 : ℝ) ≤ 1 :=
          Real.rpow_le_one (Real.sin_pos_of_pos_of_lt_pi (by linarith)
            (by linarith [Real.pi_pos])).le (Real.sin_le_one _) (by norm_num)
        linarith [h, mul_le_mul_of_nonneg_left hsin2 (by norm_num : (0:ℝ) ≤ 1000)]
    rw [hC4]
    calc |Work.Spaces.DthIter i (fun x θ' => Work.Construction.c2m θ') 0 θ|
          * ((1 / (2 * α)) * |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 F z) z|)
        = (1 / (2 * α)) * (|Work.Spaces.DthIter i (fun x θ' => Work.Construction.c2m θ') 0 θ|
            * |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 F z) z|) := by ring
      _ ≤ (1 / (2 * α)) * (1000 * CL) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hang (hL12jet j (by omega) z hz) (abs_nonneg _)
            (by norm_num : (0:ℝ) ≤ 1000)) (by positivity)
      _ = 1000 * ((1 / (2 * α)) * CL) := by ring
  have hConj2 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop α (Work.Construction.Theta α F)
        z θ / Real.sin (2 * θ)) z θ| ≤ C2 := by
    intro j i hji z θ hz hθ0 hθ1
    have hEqOn : Set.EqOn (Function.uncurry (fun z θ => Work.Construction.Uop α
          (Work.Construction.Theta α F) z θ / Real.sin (2 * θ)))
        (Function.uncurry (fun z _ => -(3 / (4 * α)) * Work.Construction.L12 F z
          + (1 / 4) * Work.Construction.FK F z)) Work.Construction.Qd := by
      intro p hp
      obtain ⟨hz', hθ0', hθ1'⟩ := hp
      have hsin : Real.sin (2 * p.2) ≠ 0 := ne_of_gt
        (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
      have hOp := Work.FTS_RegExport.RXT.SysAux.Theta_ops hαG (F := F) hL12d p.1 p.2 hz' hθ0' hθ1'
      show Work.Construction.Uop α (Work.Construction.Theta α F) p.1 p.2 / Real.sin (2 * p.2)
        = -(3 / (4 * α)) * Work.Construction.L12 F p.1 + (1 / 4) * Work.Construction.FK F p.1
      have h2α : (2 : ℝ) * α ≠ 0 := by positivity
      have hU : Work.Construction.Uop α (Work.Construction.Theta α F) p.1 p.2
          = (1 / 2) * (-(3 / (2 * α)) * Real.sin (2 * p.2) * Work.Construction.L12 F p.1
            + (1 / 2) * Real.sin (2 * p.2) * Work.Construction.FK F p.1) := by
        have hU' : Work.Construction.Uop α (Work.Construction.Theta α F) p.1 p.2 * 2
            = -(3 / (2 * α)) * Real.sin (2 * p.2) * Work.Construction.L12 F p.1
              + (1 / 2) * Real.sin (2 * p.2) * Work.Construction.FK F p.1 := by
          linarith [hOp.2.1]
        rw [show (1 / 2) * (-(3 / (2 * α)) * Real.sin (2 * p.2)
              * Work.Construction.L12 F p.1
            + (1 / 2) * Real.sin (2 * p.2) * Work.Construction.FK F p.1)
            = (-(3 / (2 * α)) * Real.sin (2 * p.2) * Work.Construction.L12 F p.1
              + (1 / 2) * Real.sin (2 * p.2) * Work.Construction.FK F p.1) / 2 from by ring,
          eq_div_iff (by norm_num : (2:ℝ) ≠ 0)]
        linarith [hU']
      rw [hU, div_eq_iff hsin]
      have hαne : α ≠ 0 := ne_of_gt hαG
      field_simp
      ring
    have hmix := Work.FTS_RegExport.RXT.SysAux.mixed_congr_of_isOpen isOpen_Qd hEqOn j i z θ
      ⟨hz, hθ0, hθ1⟩
    rw [hmix]
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      rw [Work.Spaces.mixed_zero_right]
      show |Work.Spaces.DzIter j (fun z _ => -(3 / (4 * α)) * Work.Construction.L12 F z
        + (1 / 4) * Work.Construction.FK F z) z θ| ≤ C2
      rw [show Work.Spaces.DzIter j (fun z _ => -(3 / (4 * α)) * Work.Construction.L12 F z
          + (1 / 4) * Work.Construction.FK F z) z θ
          = Work.Elliptic.DzdIter j (fun z => -(3 / (4 * α)) * Work.Construction.L12 F z
            + (1 / 4) * Work.Construction.FK F z) z from
        Work.Elliptic.DzIter_rad _ j z θ]
      have hDr := DzdIter_const_mul_add (c := -(3 / (4 * α))) (d := (1 / 4))
        (u := fun z => Work.Construction.L12 F z)
        (v := fun z => Work.Construction.FK F z) (j := j)
        (fun b hb z' hz' => hL12diff b (by omega) z' hz')
        (fun b hb z' hz' => hFKdiff b (by omega) z' hz') hz
      rw [hDr]
      rw [hC2]
      calc |-(3 / (4 * α)) * Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 F z) z
            + (1 / 4) * Work.Elliptic.DzdIter j (fun z => Work.Construction.FK F z) z|
          ≤ |-(3 / (4 * α)) * Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 F z) z|
            + |(1 / 4) * Work.Elliptic.DzdIter j (fun z => Work.Construction.FK F z) z| :=
            abs_add_le _ _
        _ = (3 / (4 * α)) * |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 F z) z|
            + (1 / 4) * |Work.Elliptic.DzdIter j (fun z => Work.Construction.FK F z) z| := by
            rw [abs_mul, abs_mul, abs_neg,
              abs_of_nonneg (by positivity : (0:ℝ) ≤ 3 / (4 * α)),
              abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 4)]
        _ ≤ (3 / (4 * α)) * CL + (1 / 4) * CL :=
            add_le_add (mul_le_mul_of_nonneg_left (hL12jet j (by omega) z hz) (by positivity))
              (mul_le_mul_of_nonneg_left (hFKjet j (by omega) z hz) (by norm_num))
    · have hz0 : Work.Spaces.DthIter i (fun z _ => -(3 / (4 * α)) * Work.Construction.L12 F z
          + (1 / 4) * Work.Construction.FK F z) = 0 :=
        DthIter_radial_eq_zero (fun z => -(3 / (4 * α)) * Work.Construction.L12 F z
          + (1 / 4) * Work.Construction.FK F z) i hi
      rw [Work.Spaces.mixed, hz0, DzIter_zero_fun]
      simpa using le_of_lt hC2pos
  refine ⟨max (max C3 C4) C2 + 1, ?_, ?_, ?_, ?_⟩
  · have h2 : 0 < C2 := hC2pos
    have h4 : 0 < C4 := hC4pos
    have h3 : 0 < C3 := by rw [hC3]; linarith
    nlinarith [le_max_left C3 C4, le_max_right C3 C4, le_max_left (max C3 C4) C2,
      le_max_right (max C3 C4) C2, h2, h3, h4]
  · intro j i hji z θ hz hθ0 hθ1
    have hle : C2 ≤ max (max C3 C4) C2 + 1 := by
      have h : C2 ≤ max (max C3 C4) C2 := le_max_right _ _
      linarith
    exact le_trans (hConj2 j i hji z θ hz hθ0 hθ1) hle
  · intro j i hji z θ hz hθ0 hθ1
    have hle : C3 ≤ max (max C3 C4) C2 + 1 := by
      have h : C3 ≤ max (max C3 C4) C2 := le_trans (le_max_left C3 C4) (le_max_left _ _)
      linarith
    exact le_trans (hConj3 j i hji z θ hz hθ0 hθ1) hle
  · intro j i hji z θ hz hθ0 hθ1
    have hle : C4 ≤ max (max C3 C4) C2 + 1 := by
      have h : C4 ≤ max (max C3 C4) C2 := le_trans (le_max_right C3 C4) (le_max_left _ _)
      linarith
    exact le_trans (hConj4 j i hji z θ hz hθ0 hθ1) hle

end

end Work.FTS_StreamBdry.Inputs
