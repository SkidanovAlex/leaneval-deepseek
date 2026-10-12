import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Submission.Work.BoseBoxFock.aPCPairAlg
import Submission.Work.BoseBoxFock.chiRowDict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.thMode_measurable_bounded` — regularity of the pinned `χ²`-row mode

The pinned `χ²`-row (`θ`-row) mode of the FS `Q₁` row is

    `thMode ℓ N = χ_Λ² − θ_Λ − thetaTail ℓ N`,

the complexified localisation function `χ_Λ` minus the sharp box indicator `θ_Λ` minus the
lattice-truncation tail.  This module proves the two regularity facts about it:

* `Measurable (thMode ℓ N)` — from the measurability of `χ_Λ` (continuous), of `θ_Λ` (the
  indicator of the box `Λ(ℓ) = ℓ • cell`, which is compact and hence measurable) and of
  `thetaTail ℓ N` (a finite sum of `θ`-modes `e^{i⟪s,·⟫}θ_Λ`, each a continuous phase times the
  measurable box indicator);
* a global bound `∃ C, 0 ≤ C ∧ ∀ z, ‖thMode ℓ N z‖ ≤ C`, with `C` allowed to depend on `ℓ` and
  `N` (the statement carries no positivity hypothesis on `ℓ`).

The bound is obtained from the **finite-sum identity**

    `thMode ℓ N z = ∑_{s ≠ 0, s : Lab N} (χ̂²(ℓ • kmomLab ℓ N s) : ℂ) · θExp ℓ (kmomLab ℓ N s) z`

— the two leading terms cancel exactly, so the mode is the *truncated lattice sum itself* — and
the two elementary bounds `‖(r : ℂ)‖ = ‖r‖` and `‖θExp ℓ s z‖ ≤ 1` (the phase `e^{i⟪s,z⟫}` has
modulus `1`, the box indicator has modulus at most `1`).  Taking `C` to be the sum of the moduli
of the finitely many coefficients gives the result for **every** real `ℓ` and every `N`,
including the degenerate values `ℓ ≤ 0`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option maxHeartbeats 800000

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-! ## Measurability of the three summands -/

/-- The sharp box indicator `θ_Λ` is the indicator of the box `Λ(ℓ) = ℓ • cell`, which is
compact (an image of the compact cell under a continuous map) and therefore measurable. -/
private lemma thetaFun_measurable_aux (ℓ : ℝ) :
    Measurable (Work.BoseK15.corpusBox.thetaFun ℓ) := by
  have h : Work.BoseK15.corpusBox.thetaFun ℓ
      = Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : Sp => (1 : ℂ)) := by
    funext z
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ <;> simp [hz]
  rw [h]
  exact measurable_const.indicator (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)

/-- The complexified localisation function `χ_Λ` is measurable (it is continuous). -/
private lemma chiLamC_measurable_aux (ℓ : ℝ) :
    Measurable (fun z : Sp => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.measurable.comp
    ((Work.BoseB4.BoxData.chiLam_cont (B := Work.BoseK15.corpusBox) ℓ).measurable)

/-- The `θ`-mode `e^{i⟪s,·⟫}θ_Λ` is measurable: a continuous phase times the measurable box
indicator. -/
private lemma thetaExp_measurable_aux (ℓ : ℝ) (s : Sp) :
    Measurable (Work.BoseK15.corpusBox.thetaExp ℓ s) := by
  have h1 : Continuous (fun z : Sp =>
      Complex.exp (Complex.I * ((inner ℝ s z : ℝ) : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (Continuous.inner continuous_const continuous_id)))
  rw [show Work.BoseK15.corpusBox.thetaExp ℓ s
      = fun z : Sp => Complex.exp (Complex.I * ((inner ℝ s z : ℝ) : ℂ)) *
          Work.BoseK15.corpusBox.thetaFun ℓ z from
    funext fun z => Work.BoseB4.BoxData.thetaExp_apply _ _ _ _]
  exact h1.measurable.mul (thetaFun_measurable_aux ℓ)

/-- The `χ²`-row truncation tail is measurable: it is the difference of the measurable
`χ_Λ² − θ_Λ` and a finite sum of measurable `θ`-modes. -/
private lemma thetaTail_measurable_aux (ℓ : ℝ) (N : ℕ) : Measurable (thetaTail ℓ N) := by
  unfold thetaTail
  refine (((chiLamC_measurable_aux ℓ).pow_const 2).sub (thetaFun_measurable_aux ℓ)).sub ?_
  exact Finset.measurable_sum (Finset.univ.filter (fun s : Lab N => s ≠ 0))
    (fun s _ => measurable_const.mul (thetaExp_measurable_aux ℓ (kmomLab ℓ N s)))

/-- The pinned `χ²`-row (`θ`-row) mode is measurable. -/
private lemma thMode_measurable_aux (ℓ : ℝ) (N : ℕ) : Measurable (thMode ℓ N) :=
  (((chiLamC_measurable_aux ℓ).pow_const 2).sub (thetaFun_measurable_aux ℓ)).sub
    (thetaTail_measurable_aux ℓ N)

/-! ## Bounds on the summands, and the finite-sum identity -/

/-- The sharp box indicator has modulus at most `1`. -/
private lemma thetaFun_norm_le_one_aux (ℓ : ℝ) (z : Sp) :
    ‖Work.BoseK15.corpusBox.thetaFun ℓ z‖ ≤ 1 := by
  rw [Work.BoseB4.BoxData.thetaFun_apply]
  split <;> simp

/-- The `θ`-mode `e^{i⟪s,·⟫}θ_Λ` has modulus at most `1`. -/
private lemma thetaExp_norm_le_one_aux (ℓ : ℝ) (s : Sp) (z : Sp) :
    ‖Work.BoseK15.corpusBox.thetaExp ℓ s z‖ ≤ 1 := by
  rw [Work.BoseB4.BoxData.thetaExp_apply, norm_mul]
  have h1 : ‖Complex.exp (Complex.I * ((inner ℝ s z : ℝ) : ℂ))‖ = 1 := by
    rw [mul_comm Complex.I _, Complex.norm_exp_ofReal_mul_I]
  rw [h1, one_mul]
  exact thetaFun_norm_le_one_aux ℓ z

/-- A single summand of the truncated lattice sum is bounded by the modulus of its coefficient. -/
private lemma summand_norm_le_aux (ℓ : ℝ) (N : ℕ) (s : Lab N) (z : Sp) :
    ‖((Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s) : ℝ) : ℂ) *
        Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s) z‖
      ≤ ‖((Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s) : ℝ) : ℂ)‖ := by
  rw [norm_mul]
  calc ‖((Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s) : ℝ) : ℂ)‖ *
          ‖Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s) z‖
      ≤ ‖((Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s) : ℝ) : ℂ)‖ * 1 :=
        mul_le_mul_of_nonneg_left (thetaExp_norm_le_one_aux ℓ (kmomLab ℓ N s) z) (norm_nonneg _)
    _ = ‖((Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s) : ℝ) : ℂ)‖ := mul_one _

/-- **The truncated lattice sum identity.**  The two leading terms `χ_Λ² − θ_Λ` of `thMode` are
exactly the same as the subtracted leading part of `thetaTail`, so the mode *is* the truncated
lattice sum `∑_{s ≠ 0} χ̂²(ℓs) θExp(ℓs)`. -/
private lemma thMode_eq_sum (ℓ : ℝ) (N : ℕ) :
    thMode ℓ N = fun z : Sp => ∑ s ∈ (Finset.univ.filter (fun s : Lab N => s ≠ 0)),
      ((Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s) : ℝ) : ℂ) *
        Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s) z := by
  funext z
  unfold thMode thetaTail
  ring

/-- **A global bound on the pinned `χ²`-row mode**, with the constant allowed to depend on
`ℓ` and `N` (so no positivity of `ℓ` is needed): the modulus of the mode is at most the sum of
the moduli of the finitely many lattice coefficients. -/
private lemma thMode_norm_bound_aux (ℓ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Sp, ‖thMode ℓ N z‖ ≤ C := by
  refine ⟨∑ s ∈ (Finset.univ.filter (fun s : Lab N => s ≠ 0)),
    ‖((Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s) : ℝ) : ℂ)‖, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun s _ => norm_nonneg _)
  · intro z
    rw [thMode_eq_sum]
    calc ‖∑ s ∈ (Finset.univ.filter (fun s : Lab N => s ≠ 0)),
            ((Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s) : ℝ) : ℂ) *
              Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s) z‖
        ≤ ∑ s ∈ (Finset.univ.filter (fun s : Lab N => s ≠ 0)),
            ‖((Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s) : ℝ) : ℂ) *
              Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s) z‖ :=
          norm_sum_le _ _
      _ ≤ ∑ s ∈ (Finset.univ.filter (fun s : Lab N => s ≠ 0)),
            ‖((Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s) : ℝ) : ℂ)‖ :=
          Finset.sum_le_sum (fun s _ => summand_norm_le_aux ℓ N s z)

/-- **The pinned `χ²`-row mode is measurable and globally bounded.**  The bound may depend on
`ℓ` and `N`; in particular no positivity hypothesis on the box side `ℓ` is required (the
mode is the truncated lattice sum for every real `ℓ`). -/
theorem thMode_measurable_bounded (ℓ : ℝ) (N : ℕ) :
    Measurable (Work.BoseBoxFock.thMode ℓ N) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z : EuclideanSpace ℝ (Fin 3), ‖Work.BoseBoxFock.thMode ℓ N z‖ ≤ C :=
  ⟨thMode_measurable_aux ℓ N, thMode_norm_bound_aux ℓ N⟩

end Work.BoseBoxFock
