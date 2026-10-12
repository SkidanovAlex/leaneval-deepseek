import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.AbsorbClose
import Submission.Work.BoseFixR.AbsorbFar
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/Assembly.lean` — the `R`-assembly (FS §11, `R-B8`)

This is the **assembly**: from the three residual obligations of `Defs.lean` —
the bridge `RB4box` (R-B4box), the far-away bound `RB5` (R-B5) and the close
bound `RB67` (R-B6/7) — to the frozen node conclusion
`Work.BoseBoxFix.NodeRestrictedB`.

## The chain (FS §11)

Fix the realisation `D : KzDatum` and a state `Φ` that is low and
`n₊`-restricted (`RB4box`'s class).  Then

1. (`RB4box`) `(⨅_{ρ≥0} D.val ρ)·‖Φ‖² ≤ wordB Φ + errKafz·‖Φ‖²`.
2. (`RB5`, `RB67`, `le_ciInf`) for **every** `ρ ≥ 0`,
   `ℓ³Λ(a v, C, η₀, μ) + errKafz ≤ D.val ρ`:
   `ρ` is either in `CloseCond` — then `D.val ρ ≥ CloseBoundR` (`RB67`) and
   `AbsorbCloseFix` gives `ℓ³Λ + errAbs ≤ CloseBoundR` — or in the complement, which
   is `FarCond` — then `D.val ρ ≥ FarBound` (`RB5`) and `AbsorbFar` gives
   `ℓ³Λ + errAbs ≤ FarBound`.  (`errKafz = errAbs` at the box parameters,
   `Arith.errKafz_eq_errAbs`.)
3. Multiplying 2 by `‖Φ‖² ≥ 0` and applying `le_ciInf` gives
   `(ℓ³Λ + errKafz)·‖Φ‖² ≤ ⨅_{ρ≥0} D.val ρ·‖Φ‖² ≤ wordB + errKafz·‖Φ‖²`,
   hence `ℓ³Λ·‖Φ‖² ≤ wordB`, i.e. `Work.BoseBoxFix.BoxBoundB`.

Two points of care, both handled below:

* the assembly never divides by `‖Φ‖²` (a `BoxState` need not be supported in the
  box, so `normB` may vanish); everything is kept homogeneous, which is why the
  bridge of `Defs.lean` is stated with `D.val ρ · ‖Φ‖²` and `errKafz · ‖Φ‖²`.
* the target's constant is `C := bigK (a v) R C₄ C₆`, i.e. `K ≥ bigK` is the
  hypothesis of `AbsorbFar`/`AbsorbCloseFix`; hence the node's `C` is *pinned* by the
  two residual constants (`C₄` from `RB4box`, `C₆` from `RB67`), exactly as
  `Work.BoseB7.ErrDominated_fsParams` pins its constant.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. `Adm` is monotone in the diluteness threshold, and `‖Φ‖² ≥ 0` -/

lemma adm_mono {v : ℝ³ → ℝ} {ε₀ ε₀' μ : ℝ} (h : ε₀ ≤ ε₀') (hA : Adm v ε₀ μ) :
    Adm v ε₀' μ :=
  ⟨hA.1, le_trans hA.2.1 h, hA.2.2⟩

lemma adm_pos {v : ℝ³ → ℝ} {ε₀ μ : ℝ} (h : Adm v ε₀ μ) : 0 < μ := h.1

lemma adm_dil {v : ℝ³ → ℝ} {ε₀ μ : ℝ} (h : Adm v ε₀ μ) : dil v μ ≤ ε₀ := h.2.1

lemma normB_nonneg (v : ℝ³ → ℝ) (μ : ℝ) (n : ℕ) (Φ : X n → ℝ) :
    0 ≤ normB v μ n Φ := by
  rw [normB, Work.BoseKinLoc.sqNormB]
  exact integral_nonneg fun x => sq_nonneg _

lemma ell_pos' (v : ℝ³ → ℝ) {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) : 0 < ell v μ := by
  have hd : 0 < dil v μ := by rw [dil]; positivity
  rw [ell, sideAt, boxSide]
  exact mul_pos (by rw [paramsAt, fsParams]; exact fsXp_pos hd)
    (Real.rpow_pos_of_pos (by positivity) _)

/-- `CloseCond v μ ρ` bounds `ρ` from below by `μ(1 − (μa³)^{3/323})`, the form
`AbsorbClose` consumes (`K_ℓ^{-2} = (μa³)^{3/323}`, `Arith.Kl_inv_sq`). -/
lemma closeCond_lower {v : ℝ³ → ℝ} {μ ρ : ℝ} (hμ : 0 < μ) (hav : 0 < a v)
    (hc : CloseCond v μ ρ) : μ * (1 - (dil v μ) ^ (3 / 323 : ℝ)) ≤ ρ := by
  have hthr : closeThreshold v μ = μ * (dil v μ) ^ (3 / 323 : ℝ) := by
    rw [closeThreshold, Kl_inv_sq v hμ hav]
  have h2 : |ρ - μ| ≤ μ * (dil v μ) ^ (3 / 323 : ℝ) := by rw [← hthr]; exact hc
  have h4 : -(ρ - μ) ≤ |ρ - μ| := neg_le_abs _
  have h5 : -(ρ - μ) ≤ μ * (dil v μ) ^ (3 / 323 : ℝ) := le_trans h4 h2
  linarith

/-- `CloseCond` fails only on `FarCond` (the two regions cover `[0,∞)`). -/
lemma farCond_of_not_close {v : ℝ³ → ℝ} {μ ρ : ℝ} (hc : ¬ CloseCond v μ ρ) :
    FarCond v μ ρ := by
  rw [CloseCond] at hc
  exact le_of_lt (not_le.mp hc)

/-! ## 1. The assembly -/

/-- **The `R`-assembly (FS §11)**: the three residual obligations at the fixed
realisation `D` imply the frozen node conclusion `NodeRestrictedB`, with the
error constant `C := bigK (a v) R C₄ C₆` pinned by `RB4box`'s and `RB67`'s
constants. -/
theorem nodeRestrictedB_of_residuals {v : ℝ³ → ℝ} {h : ScatSol v} {R J η₀ : ℝ}
    {D : ℝ → KzDatum} (hav : 0 < a v) (hR : 0 ≤ R) (hη₀ : 0 ≤ η₀)
    (hη₂ : η₀ < 2 / 323) (hη₃ : η₀ ≤ 1 / 1615)
    (h4 : RB4box v h R J D) (h5 : RB5 v h R D) (h67 : RB67 v h R D) :
    ∃ C : ℝ, 0 ≤ C ∧ NodeRestrictedB v h J η₀ C := by
  obtain ⟨ε₄, C₄, hε₄, hC₄, hview₄, hred⟩ := h4
  obtain ⟨ε₅, hε₅, hfar⟩ := h5
  obtain ⟨ε₆, C₆, hε₆, hC₆, hclose⟩ := h67
  refine ⟨bigK (a v) R C₄ C₆, bigK_nonneg hav hR hC₄ hC₆, ?_⟩
  refine ⟨min (min ε₄ ε₅) (min ε₆ 1), ?_, ?_⟩
  · have h6 : (0 : ℝ) < min ε₆ 1 := lt_min hε₆ one_pos
    exact lt_min (lt_min hε₄ hε₅) h6
  intro μ hAdm hJKB n Φ hlow hspec
  have hε₀₄ : min (min ε₄ ε₅) (min ε₆ 1) ≤ ε₄ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε₀₅ : min (min ε₄ ε₅) (min ε₆ 1) ≤ ε₅ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε₀₆ : min (min ε₄ ε₅) (min ε₆ 1) ≤ ε₆ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε₀₁ : min (min ε₄ ε₅) (min ε₆ 1) ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hAdm₄ : Adm v ε₄ μ := adm_mono hε₀₄ hAdm
  have hAdm₅ : Adm v ε₅ μ := adm_mono hε₀₅ hAdm
  have hAdm₆ : Adm v ε₆ μ := adm_mono hε₀₆ hAdm
  have hμ : 0 < μ := adm_pos hAdm₄
  have hdil0 : 0 < dil v μ := by rw [dil]; positivity
  have hdil1 : dil v μ ≤ 1 := le_trans (adm_dil hAdm) hε₀₁
  have hℓ : 0 < ell v μ := ell_pos' v hμ hav
  have hview : (D μ).view v h μ := hview₄ μ hAdm₄
  obtain ⟨⟨f₀, hf₀spec, hf₀ne⟩, hbridge⟩ := hred μ hAdm₄ hJKB n Φ hlow hspec
  have hne : Nonempty {f : (D μ).F.H // (D μ).T.NWindow (D μ).E.bigM f ∧ f ≠ 0} :=
    ⟨⟨f₀, hf₀spec, hf₀ne⟩⟩
  have hpoint : ∀ ρ : {ρ : ℝ // 0 ≤ ρ},
      (ell3 v μ * Lambda (a v) (bigK (a v) R C₄ C₆) η₀ μ + errKafz v R μ C₄)
        * normB v μ n Φ ≤ (D μ).val ρ.1 * normB v μ n Φ := by
    intro ρ
    have hN := normB_nonneg v μ n Φ
    by_cases hc : CloseCond v μ ρ.1
    · have hCb : CloseBoundR v R μ C₆ ρ.1 ≤ (D μ).val ρ.1 :=
        KzVal_le_of_bound (D μ).F (D μ).T (D μ).E (D μ).gHat0 ρ.1 hne
          (fun f hf _ => hclose μ hAdm₆ hview ρ.1 ρ.2 hc f hf)
      have hAbs := AbsorbClose (a := a v) (ℓ := ell v μ) (t := dil v μ) (μ := μ) (R := R)
        (C₄ := C₄) (C₆ := C₆) (K := bigK (a v) R C₄ C₆) (η₀ := η₀) (ρ := ρ.1)
        hav hℓ hμ hR hC₄ hC₆ hη₀ hη₂ hη₃ hdil0 hdil1 le_rfl ρ.2
        (le_of_eq (by rw [dil])) (closeCond_lower hμ hav hc)
      rw [← errKafz_eq_errAbs v hμ hav, ← Lambda_ell3' v,
        ← fsX_sq v hμ hav, ← errExp_eq] at hAbs
      exact mul_le_mul_of_nonneg_right (le_trans hAbs hCb) hN
    · have hfc : FarCond v μ ρ.1 := farCond_of_not_close hc
      have hFb : FarBound v μ ≤ (D μ).val ρ.1 :=
        KzVal_le_of_bound (D μ).F (D μ).T (D μ).E (D μ).gHat0 ρ.1 hne
          (fun f hf _ => hfar μ hAdm₅ hview ρ.1 ρ.2 hfc f hf)
      have hAbs := AbsorbFar (a := a v) (ℓ := ell v μ) (t := dil v μ) (μ := μ) (R := R)
        (C₄ := C₄) (C₆ := C₆) (K := bigK (a v) R C₄ C₆) (η₀ := η₀)
        hav hℓ hμ hR hC₄ hC₆ hη₀ hη₂ hη₃ hdil0 hdil1 le_rfl
      rw [← errKafz_eq_errAbs v hμ hav, ← Lambda_ell3' v, ← FarBound_eq' v μ] at hAbs
      exact mul_le_mul_of_nonneg_right (le_trans hAbs hFb) hN
  have hci : (ell3 v μ * Lambda (a v) (bigK (a v) R C₄ C₆) η₀ μ + errKafz v R μ C₄)
      * normB v μ n Φ
      ≤ ⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (D μ).val ρ.1 * normB v μ n Φ := by
    haveI := nonemptyDensity
    exact le_ciInf (fun ρ => hpoint ρ)
  have hmain : (ell3 v μ * Lambda (a v) (bigK (a v) R C₄ C₆) η₀ μ) * normB v μ n Φ
      ≤ wordB v h μ n Φ := by
    have h1 : (ell3 v μ * Lambda (a v) (bigK (a v) R C₄ C₆) η₀ μ) * normB v μ n Φ
        + errKafz v R μ C₄ * normB v μ n Φ
        ≤ wordB v h μ n Φ + errKafz v R μ C₄ * normB v μ n Φ := by
      calc (ell3 v μ * Lambda (a v) (bigK (a v) R C₄ C₆) η₀ μ) * normB v μ n Φ
            + errKafz v R μ C₄ * normB v μ n Φ
          = (ell3 v μ * Lambda (a v) (bigK (a v) R C₄ C₆) η₀ μ + errKafz v R μ C₄)
            * normB v μ n Φ := by ring
        _ ≤ ⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (D μ).val ρ.1 * normB v μ n Φ := hci
        _ ≤ wordB v h μ n Φ + errKafz v R μ C₄ * normB v μ n Φ := hbridge
    linarith
  exact hmain

/-- **The node, conditionally on the three residuals at the fixed realisation
`D`** (the form a caller combines with `RB4boxExists`): the existence of `η₀` in
FS's range and of the error constant `C` of `Work.BoseBoxFix.NodeRestrictedB`. -/
theorem nodeRestrictedB_holds_of_residuals {v : ℝ³ → ℝ} {h : ScatSol v} {R : ℝ}
    {D : ℝ → KzDatum} (hav : 0 < a v) (hR : 0 ≤ R) {J' : ℝ} (hJ' : lhyC < J')
    (h4 : RB4box v h R J' D) (h5 : RB5 v h R D) (h67 : RB67 v h R D) :
    ∃ η₀ : ℝ, 1 / 2000 < η₀ ∧ η₀ < 2 / 323 ∧
      ∃ C : ℝ, 0 ≤ C ∧ NodeRestrictedB v h J' η₀ C := by
  refine ⟨1 / 1800, by norm_num, by norm_num, ?_⟩
  exact nodeRestrictedB_of_residuals hav hR (by norm_num) (by norm_num) (by norm_num)
    h4 h5 h67

/-- **The node from the three residuals *bundled as one existence*** (the shape a
single prover produces, cf. `Work.BoseFixR.RB67Residual`): the family datum
carrying `RB4box`, `RB5` and `RB67` gives `NodeRestrictedB` at `η₀ = 1/1800`.

This is the exact conclusion of the design note's node `D7`
(`nodeRestrictedB_holds` with `η₀ = 1/1800`), minus the three residual
obligations, which are stated in `Defs.lean`. -/
theorem nodeRestrictedB_holds_of_exists {v : ℝ³ → ℝ} {h : ScatSol v} {R J' : ℝ}
    (hav : 0 < a v) (hR : 0 ≤ R) (hJ' : lhyC < J')
    (hres : ∃ D : ℝ → KzDatum,
      RB4box v h R J' D ∧ RB5 v h R D ∧ RB67 v h R D) :
    ∃ η₀ : ℝ, 1 / 2000 < η₀ ∧ η₀ < 2 / 323 ∧
      ∃ C : ℝ, 0 ≤ C ∧ NodeRestrictedB v h J' η₀ C := by
  obtain ⟨D, h4, h5, h67⟩ := hres
  exact nodeRestrictedB_holds_of_residuals hav hR hJ' h4 h5 h67

end Work.BoseFixR
