import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.aQ_aP_sq_integral_le
import Submission.Work.BoseBoxFock.PCFU.absMulLeSqOfSqLe
import Submission.Work.BoseBoxFock.PCFU.lowSlot_L2_le
import Submission.Work.BoseBoxFock.PCFU.slotNormReduction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.BslotNormLe` — the `(B)`-slot `sup |χF|` reduction

The `(B)` alias slot of the cubic dictionary (`Submission.Work.BoseBoxFock.PCFU.chBslot`) is, with
`ℓ = ellH v μ`, `χ = corpusBox.chiLam ℓ`, `F z = KχfrU z − ∫χ(y)W₁(y−z)dy` and
`Γ = lowSlot fc κ ℓ j (aQ ℓ j (aP ℓ i Θ))`,

    `chBslot = ∫ x, Θ x · χ(x_j) · F(x_j) · Γ x dx`.

The target is the *sharp* `sup |χF|` reduction

    `‖chBslot‖ ≤ M · ∫_{abox n ℓ} Θ² ,`   whenever  `∀ z, χ z · ‖F z‖ ≤ M`,

for a state `Θ` which is measurable, globally bounded and supported in the box.  It is the
*repaired* form of `PCFU.chBslot_norm_le` (see `PCFU/chBslot_norm_le.lean`, which explains why the
measurability of `Θ` is indispensable: without it the right-hand side `∫_{abox} Θ²` is a junk
zero).

## The chain

Pointwise, norms multiplies (`χ ≥ 0`) and `hM` gives

    `‖Θ x · χ(x_j) · F(x_j) · Γ x‖ = |Θ x| · (χ(x_j)‖F(x_j)‖) · |Γ x| ≤ M·|Θ x|·|Γ x|`,

while `‖∫ f‖ ≤ ∫ ‖f‖` and `Support Θ ⊆ abox` turn the whole-space integral into one over the box.
The remaining step is the `L²` bound

    `∫_{abox} |Θ|·|Γ| ≤ ∫_{abox} Θ²`   from   `∫_{abox} Γ² ≤ ∫_{abox} Θ²`,

which is AM–GM (`2|Θ||Γ| ≤ Θ² + Γ²`) plus the two **contractions**

* `PCFU.lowSlot_L2_le` (`∫ (lowSlot Ψ)² ≤ ∫ Ψ²`, the low-momentum cut-off is an `L²`-contraction),
* `PCFU.aQ_aP_sq_integral_le` (`∫ (Q_j P_i Θ)² ≤ ∫ Θ²`, the fluctuation of a slot mean contracts),

applied to `Ψ = aQ ℓ j (aP ℓ i Θ)`.  Measurability and uniform boundedness of `Γ` come from
`PCFU.lowSlot_aQ_aP_measurable_bounded`, which needs only that `Θ` is measurable and bounded.

The two pure-analysis steps are delegated lemmas:
`PCFU.slotNormReduction` (the norm reduction against `M ∫ |Θ||Γ|`) and
`PCFU.absMulLeSqOfSqLe` (the AM–GM step).  This file is the assembly of those two with the two
`L²`-contractions above.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory
open scoped Topology BigOperators

set_option linter.style.haveILetI false

theorem BslotNormLe {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}
    {μ : ℝ} {N n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ) (hκ : 0 < Work.BoseBoxFock.PCFU.chKappa v μ)
    {M : ℝ} (hM : ∀ z : EuclideanSpace ℝ (Fin 3), (Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z) *
        ‖Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
          - ((∫ y : EuclideanSpace ℝ (Fin 3), (((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) y : ℝ)) : ℂ) *
              (((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (y - z) : ℝ)) : ℂ)) : ℂ)‖ ≤ M)
    {Θ : Submission.BoseGases.X n → ℝ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    ‖Work.BoseBoxFock.PCFU.chBslot v h fc fu μ N i j Θ‖
      ≤ M * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ), (Θ x) ^ 2) := by
  classical
  -- ## 1. The state data: a nonnegative bound `Cθ` for `Θ`
  obtain ⟨C₀, hC₀⟩ := hΘb
  set Cθ : ℝ := max C₀ 0 with hCθdef
  have hCθ : 0 ≤ Cθ := by rw [hCθdef]; exact le_max_right _ _
  have hΘb' : ∀ x, |Θ x| ≤ Cθ := fun x =>
    le_trans (hC₀ x) (by rw [hCθdef]; exact le_max_left _ _)
  haveI : IsFiniteMeasure ((volume : Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ))) :=
    Work.BoseBoxFock.Weak.abox_isFiniteMeasure n hℓ.le
  -- ## 2. The slot-`j` low-momentum fibre `Γ`
  let Γ : Submission.BoseGases.X n → ℝ := fun x =>
    Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ) (Work.BoseBoxFock.ellH v μ) j
      (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)) x
  have hΓdata := lowSlot_aQ_aP_measurable_bounded (fc := fc) (μ := μ)
    (ℓ := Work.BoseBoxFock.ellH v μ) (κ := Work.BoseBoxFock.PCFU.chKappa v μ)
    (Cθ := Cθ) (i := i) (j := j) hℓ hκ hCθ hΘm hΘb'
  obtain ⟨hΓm, D, hD0, hΓb⟩ := hΓdata
  have hΓm' : Measurable Γ := hΓm
  have hΓb' : ∀ x, |Γ x| ≤ D := hΓb
  -- ## 3. `Θ` lies in `L²` of the box
  have hMemLp : MeasureTheory.MemLp Θ 2 ((volume : Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ))) :=
    MeasureTheory.MemLp.of_bound hΘm.aestronglyMeasurable Cθ
      (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hΘb' x))
  -- ## 4. The two `L²` contractions
  have hΨm : Measurable (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
      (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)) :=
    Work.BoseBoxFock.Weak.aQ_measurable (ℓ := Work.BoseBoxFock.ellH v μ) j
      (Work.BoseBoxFock.Weak.aP_measurable (ℓ := Work.BoseBoxFock.ellH v μ) i hΘm)
  have hΨb : ∀ x ∈ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
      |Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ) x| ≤ 2 * Cθ :=
    fun x _ => Work.BoseBoxFock.Weak.aQ_abs_le hℓ j (by positivity)
      (Work.BoseBoxFock.Weak.aP_abs_le hℓ i hCθ hΘb') x
  have hcont1 := lowSlot_L2_le (fc := fc) (κ := Work.BoseBoxFock.PCFU.chKappa v μ)
    (ℓ := Work.BoseBoxFock.ellH v μ) (C := 2 * Cθ) j hκ hℓ (by positivity) hΨm hΨb
  have hcont2 := aQ_aP_sq_integral_le (n := n) (ℓ := Work.BoseBoxFock.ellH v μ)
    (i := i) (j := j) hℓ hij hMemLp
  have hΓsq : (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ), (Γ x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ), (Θ x) ^ 2 := by
    dsimp only [Γ]
    exact le_trans hcont1 hcont2
  -- ## 5. The two delegated analytic pieces
  have hχnn : ∀ z : EuclideanSpace ℝ (Fin 3),
      0 ≤ (fun z => Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z) z :=
    fun z => Work.BoseB4.BoxData.chiLam_nonneg (B := Work.BoseK15.corpusBox)
      (Work.BoseBoxFock.ellH v μ) z
  have hstep1 := slotNormReduction (n := n) (ℓ := Work.BoseBoxFock.ellH v μ) hℓ j
    (χ := fun z => Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z)
    (F := fun z => Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
      - (∫ y : EuclideanSpace ℝ (Fin 3),
          (((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) y : ℝ)) : ℂ) *
          (((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (y - z) : ℝ)) : ℂ)))
    (Θ := Θ) (Γ := Γ) (C := Cθ) (D := D) hχnn hM hCθ hD0 hΘm hΘb' hΘs hΓm' hΓb'
  have hstep2 := absMulLeSqOfSqLe
    (μ := (volume : Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)))
    (f := Θ) (g := Γ) (C := Cθ) (D := D) hCθ hD0 hΘm hΘb' hΓm' hΓb' hΓsq
  -- ## 6. `M ≥ 0`
  have hMnn : 0 ≤ M := by
    refine le_trans ?_ (hM 0)
    exact mul_nonneg (Work.BoseB4.BoxData.chiLam_nonneg (B := Work.BoseK15.corpusBox)
      (Work.BoseBoxFock.ellH v μ) 0) (norm_nonneg _)
  -- ## 7. Assembly
  have hchain : ‖chBslot v h fc fu μ N i j Θ‖
      ≤ M * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ), (Θ x) ^ 2) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hstep2 hMnn)
    simp only [chBslot]
    exact hstep1
  exact hchain

end Work.BoseBoxFock.PCFU
