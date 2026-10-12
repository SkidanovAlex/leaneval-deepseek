import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.PCFU.MiddleV_bricks
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.frameSmear`

Two `k`-frame facts used by the `(C)`/`(D)`-channels of the cubic dictionary:

* `integral_chiLam_KfrU` — the **`χ`-smear of the `k`-frame**:
  `∫_w χ_Λ(w)·KfrU(z+w) = ℓ³·KχfrU(z)` (the exact `k`-frame twin of the proved
  `PCFU.integral_chiLam_Ksfr` for the `s`-frame);
* `slotAvg_neg` — the **slot-average change of variables**: for an even window, the plus-shifted
  smear `∫_w χ(w)·KfrU(u+w)·H(−w)` is the minus-shifted smear `∫_z χ(z)·KfrU(u−z)·H(z)`.

The second is the step that puts the `(C)`-channel's
`∫_w χ(w)KfrU(x_i+w)·lowSlot_jψ(x[j↦−w])` into the shape of the word's
`χ(x_i)χ(x_j)W1fun(x_i−x_j)`-weighted integral (with the slot-`j` integration variable renamed
`x_j = −w`).  The first is its separable companion.

Both are `sorry`-free and axiom-clean.
-/

noncomputable section
open MeasureTheory
namespace Work.BoseBoxFock.PCFU

local notation "Ω" => EuclideanSpace ℝ (Fin 3)
open Work.BoseBoxFock
set_option linter.unusedVariables false

/-- The `univ` `k`-frame is even (`KχfrU_neg`'s twin; `sum_univ_neg` + `W1h_neg`). -/
lemma KfrU_neg {v : Ω → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {fu : Work.BoseBoxFix.LowCut}
    {N : ℕ} (z : Ω) :
    KfrU v h μ fu N (-z) = KfrU v h μ fu N z := by
  simp only [KfrU]
  rw [← sum_univ_neg (fun k => (((W1h v h μ fu N k : ℝ)) : ℂ)
    * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [W1h_neg, kmomLab_neg, inner_neg_left, inner_neg_right]

/-- **The `χ`-smear of the `k`-frame**: `∫_w χ_Λ(w)·KfrU(z+w) = ℓ³·KχfrU(z)`
(the `k`-frame twin of `integral_chiLam_Ksfr`). -/
theorem integral_chiLam_KfrU {v : Ω → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ} (z : Ω) :
    ∫ w : Ω, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ) * KfrU v h μ fu N (z + w)
      = (((ellH v μ) ^ 3 : ℝ) : ℂ) * KχfrU v h μ fu N z := by
  classical
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have h3 : (((ellH v μ) ^ 3 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact pow_ne_zero _ (ne_of_gt hℓ)
  have hexp : ∀ s : Lab N, ∀ w : Ω,
      Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (z + w) : ℂ))
        = Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) z : ℂ))
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) w : ℂ)) := by
    intro s w
    rw [inner_add_right]
    push_cast
    rw [← Complex.exp_add]
    congr 1
    ring
  have hbase : ∀ s : Lab N,
      ∫ w : Ω, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) w : ℂ))
        = (((ellH v μ) ^ 3 : ℝ) : ℂ) * ((hatChih v μ N s : ℝ) : ℂ) := by
    intro s
    have hb := hatChi_eq_integral_plus hℓ (kmomLab (ellH v μ) N s)
    rw [hatChih]
    rw [hb, ← mul_assoc, mul_inv_cancel₀ h3, one_mul]
  have hterm : ∀ s : Lab N,
      ∫ w : Ω, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * (((W1h v h μ fu N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (z + w) : ℂ)))
        = (((ellH v μ) ^ 3 : ℝ) : ℂ)
            * (((W1h v h μ fu N s * hatChih v μ N s : ℝ) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) z : ℂ))) := by
    intro s
    rw [show (fun w : Ω => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * (((W1h v h μ fu N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (z + w) : ℂ))))
        = (fun w : Ω => (((W1h v h μ fu N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) z : ℂ)))
            * (((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) w : ℂ))))
        from by funext w; rw [hexp s w]; ring]
    rw [MeasureTheory.integral_const_mul, hbase]
    simp only [Complex.ofReal_mul]
    ring
  have hint : ∀ s : Lab N, Integrable (fun w : Ω =>
      ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * (((W1h v h μ fu N s : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (z + w) : ℂ)))) := by
    intro s
    have h1 : Integrable (fun w : Ω =>
        ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) w : ℂ))) :=
      integrable_chiLam_mul_exp_plus (ellH v μ) hℓ (kmomLab (ellH v μ) N s)
    have h2 := h1.const_mul (((W1h v h μ fu N s : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) z : ℂ)))
    refine h2.congr (Filter.Eventually.of_forall (fun w => ?_))
    simp only [hexp s w]
    ring
  simp only [KfrU, KχfrU]
  rw [Finset.mul_sum]
  rw [show (fun w : Ω => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * (∑ s : Lab N,
            ((W1h v h μ fu N s : ℝ) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (z + w) : ℂ))))
      = (fun w : Ω => ∑ s : Lab N,
          ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
            * (((W1h v h μ fu N s : ℝ) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (z + w) : ℂ))))
      from by
    funext w
    rw [Finset.mul_sum]]
  rw [MeasureTheory.integral_finsetSum _ (fun s _ => hint s)]
  exact Finset.sum_congr rfl (fun s _ => hterm s)

/-- **The slot-average change of variables.**  With an even window `χ_Λ`,
`∫_w χ_Λ(w)·KfrU(u+w)·H(−w) = ∫_z χ_Λ(z)·KfrU(u−z)·H(z)`: the measure-preserving map `w ↦ −w`
carries one to the other, using `χ(−z) = χ(z)` and `u − (−w) = u + w`. -/
theorem slotAvg_neg {v : Ω → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {fu : Work.BoseBoxFix.LowCut} {N : ℕ} (u : Ω) (H : Ω → ℂ) :
    (∫ w : Ω, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * KfrU v h μ fu N (u + w) * H (-w))
      = ∫ z : Ω, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)
        * KfrU v h μ fu N (u - z) * H z := by
  have hsub := (Measure.measurePreserving_neg (volume : Measure Ω)).integral_comp
    measurableEmbedding_neg
    (fun z : Ω => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)
      * KfrU v h μ fu N (u - z) * H z)
  rw [← hsub]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
  show ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * KfrU v h μ fu N (u + w) * H (-w)
      = ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (-w) : ℝ) : ℂ)
        * KfrU v h μ fu N (u - (-w)) * H (-w)
  rw [Work.BoseB4.BoxData.chiLam_even, sub_neg_eq_add]

end Work.BoseBoxFock.PCFU
