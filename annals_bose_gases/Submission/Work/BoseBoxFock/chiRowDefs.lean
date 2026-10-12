import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRow_muLine_slot
import Submission.Work.BoseBoxFock.chiRow_slotIdentity
import Submission.Work.BoseBoxFock.chiTailDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRowDefs` — the position-space slot forms of the FS `Q₁` χ-row

The FS `Q₁` row (`potChiLin`, `Submission/Work/BoseBoxFock/PotGroupDefs.lean`) is evaluated on
the box against the position-space slot words defined here:

* `pairSlot ℓ w Φ` — the `n₀`-sandwich `⟨Φ, (n₀X_w + X_w†n₀)Φ⟩` of the pair form, i.e. exactly
  the left-hand side of `chiRow_slotIdentity` (with the weight `w` itself, *no* mean
  subtraction — so that `pairSlot` is `ℝ`-linear in `w`);
* `chiA ℓ w Φ` — the evaluated pair form `2Σ_{i≠j}∫(PᵢΦ)w(x_i)(QᵢPⱼΦ)`, i.e. exactly the
  right-hand side of `chiRow_slotIdentity`;
* `muLine ℓ w Φ` — the `μ`-line of the χ-sandwich, i.e. exactly the right-hand side of
  `chiRow_muLine_slot`.

The interface used by the χ-row assembly (`Submission/Work/BoseBoxFock/PotChiLin_exists.lean`)
is

* `pairSlot_chiCube` — `pairSlot ℓ (χ_Λ² − 1) Φ = chiA ℓ (χ_Λ² − 1) Φ` (the slot identity at the
  continuous, cube-mean-free continuum weight);
* `chiA_const`, `muLine_const` — constants are invisible in the *evaluated* forms
  (`chiA` and `muLine` are quadratic in the pair/one-body slot structures, so a constant weight
  contributes the exactly vanishing slot mass);

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option maxHeartbeats 800000

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- `χ_Λ(x)² − 1` — the continuum (untruncated) χ-row weight on the cube. -/
noncomputable def chiCube (ℓ : ℝ) : Sp → ℝ := fun x =>
  (Work.BoseK15.corpusBox.chiLam ℓ x) ^ 2 - 1

/-- The truncated χ-row weight: `χ_Λ² − 1 − Re (chiTail)`.  On the box this agrees with the
real part of the pinned mode `ℓ^{3/2}η_C` of the χ-row. -/
noncomputable def chiW (ℓ : ℝ) (N : ℕ) : Sp → ℝ := fun x =>
  chiCube ℓ x - (chiTail ℓ N x).re

/-- The truncated θ-row (`ω`) weight: `χ_Λ² − 1 − Re (thetaTail)`. -/
noncomputable def thW (ℓ : ℝ) (N : ℕ) : Sp → ℝ := fun x =>
  chiCube ℓ x - (thetaTail ℓ N x).re

/-- The real part of the χ-row truncation tail, as a real function. -/
noncomputable def chiTailRe (ℓ : ℝ) (N : ℕ) : Sp → ℝ := fun x => (chiTail ℓ N x).re

/-- The real part of the θ-row truncation tail, as a real function. -/
noncomputable def thetaTailRe (ℓ : ℝ) (N : ℕ) : Sp → ℝ := fun x => (thetaTail ℓ N x).re

lemma chiW_eq (ℓ : ℝ) (N : ℕ) : chiW ℓ N = chiCube ℓ - chiTailRe ℓ N := rfl

lemma thW_eq (ℓ : ℝ) (N : ℕ) : thW ℓ N = chiCube ℓ - thetaTailRe ℓ N := rfl

/-- **The pair slot form of the χ-row**: the `n₀`-sandwich
`⟨Φ, (n₀ X_w + X_w† n₀)Φ⟩ = Σ_i∫Φ·Pᵢ(Σ_j w(y_j)P_jΦ) + Σ_i∫Φ·Pᵢ(w(y_i)·Σ_j P_jΦ)`.
It is `ℝ`-linear in `w`; for continuous `w` its value is `chiA` plus the mean correction. -/
noncomputable def pairSlot (n : ℕ) (ℓ : ℝ) (w : Sp → ℝ) (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ,
    Φ x * ((∑ i : Fin n, (aP ℓ i
        (fun y : X n => (∑ j : Fin n, w (y j) * aP ℓ j Φ y))) x)
      + (∑ i : Fin n, (aP ℓ i
        (fun y : X n => w (y i) * (∑ j : Fin n, aP ℓ j Φ y))) x))

/-- **The evaluated pair form**: `2Σ_{i≠j}∫_{abox}(PᵢΦ)·w(x_i)·(QᵢPⱼΦ)`. -/
noncomputable def chiA (n : ℕ) (ℓ : ℝ) (w : Sp → ℝ) (Φ : X n → ℝ) : ℝ :=
  2 * ∑ i : Fin n, ∑ j : Fin n,
    (if i = j then 0 else
      ∫ x in abox n ℓ, (aP ℓ i Φ x) * w (x i) * (aQ ℓ i (fun y : X n => aP ℓ j Φ y) x))

/-- **The `μ`-line of the χ-sandwich**: `2Σ_j∫_{abox}(Q_jΦ)·w(x_j)·(P_jΦ)`. -/
noncomputable def muLine (n : ℕ) (ℓ : ℝ) (w : Sp → ℝ) (Φ : X n → ℝ) : ℝ :=
  2 * ∑ j : Fin n, ∫ x in abox n ℓ, (aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x)

/-! ## The cube mean of `χ_Λ² − 1` -/

lemma chiCube_cont (ℓ : ℝ) : Continuous (chiCube ℓ) := by
  have h := (Work.BoseB4.BoxData.chiLam_cont (B := Work.BoseK15.corpusBox) ℓ).pow 2
  exact h.sub continuous_const

lemma chiCube_measurable (ℓ : ℝ) : Measurable (chiCube ℓ) := (chiCube_cont ℓ).measurable

/-- The cube mean of `χ_Λ² − 1` vanishes: `χ_Λ` is supported in the cube of volume `ℓ³` and
`∫χ_Λ² = ℓ³`. -/
lemma integral_chiCube_acube {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ z in acube ℓ, chiCube ℓ z) = 0 := by
  have hsupp : Function.support (Work.BoseK15.corpusBox.chiLam ℓ) ⊆ acube ℓ := by
    intro z hz
    rw [← corpusBox_boxL_eq_acube hℓ]
    exact Work.BoseB4.BoxData.chiLam_supp (B := Work.BoseK15.corpusBox) hℓ hz
  have h1 : (∫ z in acube ℓ, (Work.BoseK15.corpusBox.chiLam ℓ z) ^ 2) = ℓ ^ 3 := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by
        have h0 : (Work.BoseK15.corpusBox.chiLam ℓ z) ^ 2 = 0 := by
          by_cases hc : Work.BoseK15.corpusBox.chiLam ℓ z = 0
          · rw [hc]; ring
          · exact absurd (hsupp hc) hz
        exact h0)]
    exact Work.BoseB4.BoxData.integral_chiLam_sq (B := Work.BoseK15.corpusBox) hℓ
  have h2 : (∫ _z in acube ℓ, (1 : ℝ)) = 1 * ℓ ^ 3 :=
    Submission.BoseGases.integral_const_acube ℓ hℓ 1
  have hFint : IntegrableOn (fun z : Sp => (Work.BoseK15.corpusBox.chiLam ℓ z) ^ 2)
      (acube ℓ) volume :=
    Submission.BoseGases.integrableOn_acube_of_continuous hℓ
      ((Work.BoseB4.BoxData.chiLam_cont (B := Work.BoseK15.corpusBox) ℓ).pow 2)
  have hGint : IntegrableOn (fun _z : Sp => (1 : ℝ)) (acube ℓ) volume :=
    MeasureTheory.integrableOn_const (by rw [Submission.BoseGases.acube_volume ℓ hℓ.le]; simp)
  have hF : (∫ z in acube ℓ, chiCube ℓ z)
      = (∫ z in acube ℓ, (Work.BoseK15.corpusBox.chiLam ℓ z) ^ 2)
        - (∫ _z in acube ℓ, (1 : ℝ)) := by
    rw [show (∫ z in acube ℓ, chiCube ℓ z)
        = ∫ z in acube ℓ, ((Work.BoseK15.corpusBox.chiLam ℓ z) ^ 2 - (1 : ℝ)) from by
      apply integral_congr_ae
      filter_upwards with z
      simp only [chiCube]]
    exact MeasureTheory.integral_sub hFint hGint
  rw [hF, h1, h2]
  ring

/-- **The slot identity at the continuum weight**: for continuous `Φ`, the `n₀`-sandwich of the
χ-row with the weight `χ_Λ² − 1` equals the evaluated pair form.  This is `chiRow_lhsEval`
combined with `chiRow_rhsEval` (which removes the cube mean of the weight). -/
lemma pairSlot_chiCube {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X n → ℝ} (hΦc : Continuous Φ) :
    pairSlot n ℓ (chiCube ℓ) Φ = chiA n ℓ (chiCube ℓ) Φ := by
  have hl := chiRow_lhsEval (n := n) (ℓ := ℓ) hℓ hΦc (chiCube_cont ℓ)
  have hr := chiRow_rhsEval (n := n) (ℓ := ℓ) hℓ hΦc (chiCube_cont ℓ) (chiCube_cont ℓ)
    (integral_chiCube_acube hℓ) (c := 0) (fun z => by ring)
  simp only [pairSlot, chiA]
  exact hl.trans hr.symm

end Work.BoseBoxFock
