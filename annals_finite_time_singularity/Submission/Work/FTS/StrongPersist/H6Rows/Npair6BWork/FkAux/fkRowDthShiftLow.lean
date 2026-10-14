import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingSup
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowsAux
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS_MuLamOK.Rows.Rl1Open
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

variable {α : ℝ} {ρ : ℝ → ℝ → ℝ}

/-- **A leaf weight of the angular slot `0` is a leaf weight of every slot.**  The two
weights `leafEta`, `leafOne` qualify for every angular index (`IsLeafW` has no guard on
them), while `leafGam α` needs `1 ≤ a` and is *excluded* at `a = 0` by definition. -/
theorem fkRowDthShiftLow_leafW_slot_mono {a : ℕ}
    (h : Work.FTS.TransportS.IsLeafW α 0 ρ) : Work.FTS.TransportS.IsLeafW α a ρ := by
  rcases h with h | h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨le_trans h1 (Nat.zero_le a), h2⟩)

/-- **The a.e.-in-`z` bound on the low radial jets of the angular moment.**  For a level-six
datum (`DatData α f M`) and `b₁ ≤ 3`, the `b₁`-th `D_z`-iterate of `FK f` is bounded almost
everywhere by `C·M`, with the universal constant of `fkDzdIterSharp`. -/
theorem fkRowDthShiftLow_moment_le {α : ℝ} {f : ℝ → ℝ → ℝ} {M : ℝ} {b₁ : ℕ} {C₁ : ℝ}
    (hC₁ : ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f → ∀ b : ℕ, b ≤ 5 → ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
        |Work.Elliptic.DzdIter b (fun z => Work.Construction.FK f z) z|
          ≤ C₁ * Real.sqrt (Work.Spaces.HkSq α (b + 1) f))
    (hC₁pos : 0 < C₁)
    (hD : Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M)
    (hαI : α ∈ Set.Ioc 0 1) (hb₁ : b₁ ≤ 3) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      |Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z| ≤ C₁ * M := by
  obtain ⟨hsm, h6, h7, -, -, hbdd⟩ := hD
  have hM0 : 0 ≤ M := by
    have h0 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α f := by
      show (0 : ℝ) ≤ Work.Spaces.HkNorm α 4 f
      exact Real.sqrt_nonneg _
    linarith
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) h6
  refine (hC₁ α hαI f hsm h6 h7 b₁ (by omega)).mono ?_
  intro z hz
  have hroot : Real.sqrt (Work.Spaces.HkSq α (b₁ + 1) f) ≤ M := by
    rw [← Real.sqrt_sq hM0]
    exact Real.sqrt_le_sqrt (HkSq_le_Msq hbdd hmem4 (by omega))
  exact hz.trans (mul_le_mul_of_nonneg_left hroot hC₁pos.le)

/-- **The level-six shifted `D_θ`-row of the angular moment `FK f`.**

For `0 < α ≤ 1`, a level-six datum `f` (`DatData α f M`), a leaf weight `ρ` of the angular
slot `0` and `1 ≤ b₁ ≤ 3`, the product-measure integrand

  `(z,θ) ↦ D_z^{b₁}(FK f) z · (ρ z θ · (D_z^{6-b₁}D_θ f) z θ · (D_z^6 f) z θ)`

is integrable and its integral is bounded by `C·(1+M)²·(1 + HkSq α 6 f)`, with a universal
`C`. -/
theorem fkRowDthShiftLow : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (ρ : ℝ → ℝ → ℝ) (b₁ : ℕ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      1 ≤ b₁ → b₁ ≤ 3 → Work.FTS.TransportS.IsLeafW α 0 ρ →
      MeasureTheory.Integrable (fun p : ℝ × ℝ =>
          Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
            * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                * Work.Spaces.mixed 6 0 f p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
            * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                * Work.Spaces.mixed 6 0 f p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
  refine ⟨C₁, hC₁pos, ?_⟩
  intro α hαI f M ρ b₁ hD hb₁1 hb₁3 hρ
  obtain ⟨hα0, hα1⟩ := hαI
  obtain ⟨hsm, h6, h7, hvan, haxis, hbdd⟩ := hD
  have hM0 : 0 ≤ M := by
    have h0 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α f := by
      show (0 : ℝ) ≤ Work.Spaces.HkNorm α 4 f
      exact Real.sqrt_nonneg _
    linarith
  have hS0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hρ1 : Work.FTS.TransportS.IsLeafW α 1 ρ := fkRowDthShiftLow_leafW_slot_mono hρ
  have hK0 : 0 ≤ C₁ * M := mul_nonneg hC₁pos.le hM0
  -- ## the a.e. bound on the radial multiplier
  have hA := fkRowDthShiftLow_moment_le (α := α) (f := f) (M := M) (b₁ := b₁) (C₁ := C₁)
    hC₁ hC₁pos ⟨hsm, h6, h7, hvan, haxis, hbdd⟩ ⟨hα0, hα1⟩ hb₁3
  -- ## the two slot squares
  obtain ⟨hXint, hXle⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkSlotSqInt (α := α) (f := f)
      (a := 1) (j := 6 - b₁) (ρ := ρ) hα0 (by omega) hρ1 hsm h6
  obtain ⟨hYint, hYle⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkSlotSqInt (α := α) (f := f)
      (a := 0) (j := 6) (ρ := ρ) hα0 (by omega) hρ hsm h6
  -- ## measurability of the radial multiplier
  have hA_aesm : MeasureTheory.AEStronglyMeasurable
      (fun z => Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.aesm_Qang hsm b₁).congr
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkQangAe hsm h6 b₁ (by omega)).symm
  have hAc : AEMeasurable
      (fun p : ℝ × ℝ => Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hA_aesm.aemeasurable.comp_fst
  have hAprod : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      |Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1| ≤ C₁ * M :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.ae_fst_prod hA
  have hXYaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2 * Work.Spaces.mixed 6 0 f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (((Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_leaf hρ).mul
        (hsm.mixed (6 - b₁) 1).continuousOn).mul (hsm.mixed 6 0).continuousOn)
  have hF_aesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
        * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
          * Work.Spaces.mixed 6 0 f p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (hAc.aestronglyMeasurable.mul hXYaesm).congr
      (Eventually.of_forall (fun p => by simp only [Pi.mul_apply]))
  -- ## the pointwise AM–GM bound
  have hpt : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      ‖Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
        * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
          * Work.Spaces.mixed 6 0 f p.1 p.2)‖
      ≤ (C₁ * M) * (ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
          + ρ p.1 p.2 * (Work.Spaces.mixed 6 0 f p.1 p.2) ^ 2) := by
    filter_upwards [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.ae_mem_Q0, hAprod]
      with p hp hAp
    obtain ⟨hpz, hpθ0, hpθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hρ0 : 0 ≤ ρ p.1 p.2 :=
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.leaf_nonneg hρ p.1
        (le_of_lt hpz) p.2 ⟨le_of_lt hpθ0, le_of_lt hpθ1⟩
    have hkey : ‖Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
        * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
          * Work.Spaces.mixed 6 0 f p.1 p.2)‖
        = ρ p.1 p.2 * |Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1|
          * |Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2|
          * |Work.Spaces.mixed 6 0 f p.1 p.2| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hρ0]
      ring
    rw [hkey]
    have h3 : |Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2| * |Work.Spaces.mixed 6 0 f p.1 p.2|
        ≤ (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
          + (Work.Spaces.mixed 6 0 f p.1 p.2) ^ 2 := by
      have h := two_mul_le_add_sq |Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2|
        |Work.Spaces.mixed 6 0 f p.1 p.2|
      rw [sq_abs, sq_abs] at h
      nlinarith [h, abs_nonneg (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2),
        abs_nonneg (Work.Spaces.mixed 6 0 f p.1 p.2)]
    have hstep1 : ρ p.1 p.2
          * |Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1|
          * |Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2| * |Work.Spaces.mixed 6 0 f p.1 p.2|
        ≤ ρ p.1 p.2 * (C₁ * M) * |Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2|
          * |Work.Spaces.mixed 6 0 f p.1 p.2| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAp hρ0) (abs_nonneg _))
        (abs_nonneg _)
    have hstep2 : ρ p.1 p.2 * (C₁ * M) * |Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2|
          * |Work.Spaces.mixed 6 0 f p.1 p.2|
        ≤ (C₁ * M) * (ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
            + ρ p.1 p.2 * (Work.Spaces.mixed 6 0 f p.1 p.2) ^ 2) := by
      calc ρ p.1 p.2 * (C₁ * M) * |Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2|
            * |Work.Spaces.mixed 6 0 f p.1 p.2|
          = ρ p.1 p.2 * (C₁ * M) * (|Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2|
              * |Work.Spaces.mixed 6 0 f p.1 p.2|) := by ring
        _ ≤ ρ p.1 p.2 * (C₁ * M) * ((Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
              + (Work.Spaces.mixed 6 0 f p.1 p.2) ^ 2) :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg hρ0 hK0)
        _ = (C₁ * M) * (ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
              + ρ p.1 p.2 * (Work.Spaces.mixed 6 0 f p.1 p.2) ^ 2) := by ring
    exact hstep1.trans hstep2
  -- ## integrability of the pairing
  have hmaj : MeasureTheory.Integrable (fun p : ℝ × ℝ => (C₁ * M)
      * (ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
        + ρ p.1 p.2 * (Work.Spaces.mixed 6 0 f p.1 p.2) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (hXint.add hYint).const_mul (C₁ * M)
  have hFint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
        * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
          * Work.Spaces.mixed 6 0 f p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Integrable.mono' hmaj hF_aesm hpt
  refine ⟨hFint, ?_⟩
  -- ## the value bound
  have h1 : |∫ p, Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
        * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
          * Work.Spaces.mixed 6 0 f p.1 p.2)
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
      ≤ ∫ p, ‖Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
        * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
          * Work.Spaces.mixed 6 0 f p.1 p.2)‖
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (fun p : ℝ × ℝ => Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
        * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
          * Work.Spaces.mixed 6 0 f p.1 p.2))
  have h2 : (∫ p, ‖Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
        * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
          * Work.Spaces.mixed 6 0 f p.1 p.2)‖
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ≤ ∫ p, (C₁ * M) * (ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
          + ρ p.1 p.2 * (Work.Spaces.mixed 6 0 f p.1 p.2) ^ 2)
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    integral_mono_of_nonneg (Eventually.of_forall (fun p => norm_nonneg _)) hmaj hpt
  have h3 : (∫ p, (C₁ * M) * (ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
          + ρ p.1 p.2 * (Work.Spaces.mixed 6 0 f p.1 p.2) ^ 2)
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = (C₁ * M) * ((∫ p, ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
          + (∫ p, ρ p.1 p.2 * (Work.Spaces.mixed 6 0 f p.1 p.2) ^ 2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)))) := by
    rw [integral_const_mul, integral_add hXint hYint]
  calc |∫ p, Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
        * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
          * Work.Spaces.mixed 6 0 f p.1 p.2)
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))| ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := h3
    _ ≤ (C₁ * M) * (Work.Spaces.HkSq α 6 f + Work.Spaces.HkSq α 6 f) :=
        mul_le_mul_of_nonneg_left (add_le_add hXle hYle) hK0
    _ = C₁ * (2 * M) * Work.Spaces.HkSq α 6 f := by ring
    _ ≤ C₁ * ((1 + M) * (1 + M)) * Work.Spaces.HkSq α 6 f := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC₁pos.le) hS0
        nlinarith [sq_nonneg M]
    _ ≤ C₁ * ((1 + M) * (1 + M)) * (1 + Work.Spaces.HkSq α 6 f) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = C₁ * (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
