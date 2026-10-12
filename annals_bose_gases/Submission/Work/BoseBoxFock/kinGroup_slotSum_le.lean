import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.frkCore
import Submission.Work.BoseBoxFock.integrableOn_kinFT_winState_fibre
import Submission.Work.BoseBoxFock.kinGroupRhs_slotSum_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

namespace Work.BoseBoxFock

open MeasureTheory

/-!
# The one-body kinetic-group row, summed over the particle slots

The one-body kinetic-group inequality (`OBineq4`, the conclusion of
`Work.BoseBoxFock.FRK.oneBody_kinGroup_le4`)

    `kinGroupLL ψ ≤ kinGroupRR ψ`

is summed over the particle slots of an `n`-body state `Φ` with the `ℓ⁻³·1_{Λ(0)}(xⱼ)` weight of
the box slot lifting.  The three rows of the sum are then identified with the box kinetic word and
its two reserves:

* `Σⱼ ℓ⁻³ ∫_{abox} 1_{Λ(0)}(xⱼ)·fsT(fibreⱼ) = kinFormB` (definitional),
* `Σⱼ ℓ⁻³ ∫_{abox} 1_{Λ(0)}(xⱼ)·gapBare(fibreⱼ) = cnPlus` (`bf3a_cnplus`),
* `Σⱼ ℓ⁻³ ∫_{abox} 1_{Λ(0)}(xⱼ)·momForm(fibreⱼ) = nPlusHB` (definitional).

The monotonicity step is `integral_mono_ae`; it needs the integrability of the two integrands.  The
reserve integrand is integrable by the parameter decomposition of `fsT`
(`pieces_integrableOn_fibre`, `integrableOn_fsT_fibre_smooth`); the kinetic-group integrand is a
finite sum over the modes `Lab N` of the `winState` Fourier coefficients of the fibre, whose
integrability on the box is `Work.BoseBoxFock.integrableOn_kinFT_winState_fibre`.
-/

/-! ## 1. The one-body kinetic group as named functions -/

/-- The lattice `τ̃`-row of the one-body kinetic group at the one-body state `ψ`. -/
noncomputable def kinTauLat (N : ℕ) (eT s d ℓ : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ :=
  ∑ k : Lab N, tauSm eT s d ℓ (kmomLab ℓ N k) *
    ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2)

/-- The lattice `η_H`-row of the one-body kinetic group at the one-body state `ψ`. -/
noncomputable def kinEtaLat (N : ℕ) (fu : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ)
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ :=
  ∑ k : Lab N, etaH fu κ (kmomLab ℓ N k) *
    ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomLab ℓ N k)‖ ^ 2)

/-- The one-body kinetic-group bracket (the left side of `OBineq4`). -/
noncomputable def kinGroupLL (N : ℕ) (ℓ s d eT b κ : ℝ) (fu : Work.BoseBoxFix.LowCut)
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ :=
  kinTauLat N eT s d ℓ ψ + b / (2 * ℓ ^ 2) * Work.BoseKinLoc.gapBare ℓ 0 ψ
    + eT * b / (2 * d ^ 2 * ℓ ^ 2) * ((1 / 32 : ℝ) * kinEtaLat N fu κ ℓ ψ)

/-- The one-body reserve (the right side of `OBineq4`). -/
noncomputable def kinGroupRR (ℓ s d eT b : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ :=
  Work.BoseKinLoc.fsT ℓ d s eT b 0 ψ - b / 4 * ((ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ)
    - b / 100 * (eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.momForm ℓ d 0 ψ)

/-! ## 2. Integrability of the slot-`j` integrands -/

/-- The `τ̃`-row of the kinetic group is integrable on the box, slot by slot. -/
lemma integrableOn_indU_kinTauLat_fibre {N n : ℕ} {ℓ s d eT : ℝ} (hℓ : 0 < ℓ) (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j)
      * kinTauLat N eT s d ℓ (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) := by
  classical
  have hterm : ∀ k : Lab N, IntegrableOn (fun x : Submission.BoseGases.X n =>
      tauSm eT s d ℓ (kmomLab ℓ N k) * (ℓ ^ 3)⁻¹ *
        (Work.BoseKinLoc.indU ℓ 0 (x j) *
          ‖Submission.BoseGases.kinFT (winState ℓ (Work.BoseKinLoc.fibre n j Φ x))
            (kmomLab ℓ N k)‖ ^ 2)) (Submission.BoseGases.abox n ℓ) :=
    fun k => (integrableOn_kinFT_winState_fibre hℓ j hΦ (kmomLab ℓ N k)).const_mul _
  have hsum := MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Lab N))
    (fun k (_ : k ∈ (Finset.univ : Finset (Lab N))) => hterm k)
  refine MeasureTheory.Integrable.congr hsum (Filter.Eventually.of_forall (fun x => ?_))
  simp only [kinTauLat]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- The `η_H`-row of the kinetic group is integrable on the box, slot by slot. -/
lemma integrableOn_indU_kinEtaLat_fibre {N n : ℕ} {ℓ κ : ℝ} {fu : Work.BoseBoxFix.LowCut}
    (hℓ : 0 < ℓ) (j : Fin n) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j)
      * kinEtaLat N fu κ ℓ (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) := by
  classical
  have hterm : ∀ k : Lab N, IntegrableOn (fun x : Submission.BoseGases.X n =>
      etaH fu κ (kmomLab ℓ N k) * (ℓ ^ 3)⁻¹ *
        (Work.BoseKinLoc.indU ℓ 0 (x j) *
          ‖Submission.BoseGases.kinFT (winState ℓ (Work.BoseKinLoc.fibre n j Φ x))
            (kmomLab ℓ N k)‖ ^ 2)) (Submission.BoseGases.abox n ℓ) :=
    fun k => (integrableOn_kinFT_winState_fibre hℓ j hΦ (kmomLab ℓ N k)).const_mul _
  have hsum := MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Lab N))
    (fun k (_ : k ∈ (Finset.univ : Finset (Lab N))) => hterm k)
  refine MeasureTheory.Integrable.congr hsum (Filter.Eventually.of_forall (fun x => ?_))
  simp only [kinEtaLat]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- The bare gap mass is integrable on the box, slot by slot (the `b = ℓ²` case of the gap word). -/
lemma integrableOn_indU_gapBare_fibre {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j)
      * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) := by
  obtain ⟨hg, _, _, _⟩ := Work.BoseFixB2.DvApriori.KinOffdiag.pieces_integrableOn_fibre
    (ℓ := ℓ) (d := 1) (s := 1) (εT := 1) (b := ℓ ^ 2) hℓ j hΦ
  refine hg.congr_fun (fun x _ => ?_) (Submission.BoseGases.abox_measurable n ℓ)
  beta_reduce
  rw [gapWord_sq_eq_gapBare hℓ]

/-- The bare momentum form is integrable on the box, slot by slot (the `b = 1`, `ε_T = (dℓ)²` case
of the momentum word). -/
lemma integrableOn_indU_momForm_fibre {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j)
      * Work.BoseKinLoc.momForm ℓ d 0 (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) := by
  obtain ⟨_, hm, _, _⟩ := Work.BoseFixB2.DvApriori.KinOffdiag.pieces_integrableOn_fibre
    (ℓ := ℓ) (d := d) (s := 1) (εT := (d * ℓ) ^ 2) (b := 1) hℓ j hΦ
  have hz : 1 * (d * ℓ) ^ 2 * (d * ℓ) ^ (-2 : ℤ) = 1 := by
    rw [one_mul, show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
    exact mul_inv_cancel₀ (pow_ne_zero 2 (mul_ne_zero (ne_of_gt hd) (ne_of_gt hℓ)))
  refine hm.congr_fun (fun x _ => ?_) (Submission.BoseGases.abox_measurable n ℓ)
  beta_reduce
  simp only [Work.BoseKinLoc.momWord]
  rw [hz, one_mul]

/-- The one-body kinetic-group bracket is integrable on the box, slot by slot. -/
lemma integrableOn_indU_kinGroupLL_fibre {N n : ℕ} {ℓ s d eT b κ : ℝ} (hℓ : 0 < ℓ)
    (fu : Work.BoseBoxFix.LowCut) (j : Fin n) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j)
      * kinGroupLL N ℓ s d eT b κ fu (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) := by
  have h1 := integrableOn_indU_kinTauLat_fibre (N := N) (s := s) (d := d) (eT := eT) hℓ j hΦ
  have h2 := (integrableOn_indU_gapBare_fibre (ℓ := ℓ) hℓ j hΦ).const_mul
    (b / (2 * ℓ ^ 2))
  have h3 := ((integrableOn_indU_kinEtaLat_fibre (N := N) (κ := κ) (fu := fu) hℓ j
    hΦ).const_mul (1 / 32 : ℝ)).const_mul (eT * b / (2 * d ^ 2 * ℓ ^ 2))
  refine ((h1.add h2).add h3).congr_fun (fun x _ => ?_)
    (Submission.BoseGases.abox_measurable n ℓ)
  simp only [Pi.add_apply]
  simp only [kinGroupLL]
  ring

/-- The one-body reserve is integrable on the box, slot by slot. -/
lemma integrableOn_indU_kinGroupRR_fibre {n : ℕ} {ℓ s d eT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (j : Fin n) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j)
      * kinGroupRR ℓ s d eT b (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) := by
  have h1 := Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (ℓ := ℓ) (d := d) (s := s)
    (εT := eT) (b := b) hℓ j hΦ
  have h2 := (integrableOn_indU_gapBare_fibre (ℓ := ℓ) hℓ j hΦ).const_mul
    (b / 4 * (ℓ ^ 2)⁻¹)
  have h3 := (integrableOn_indU_momForm_fibre (ℓ := ℓ) (d := d) hℓ hd j hΦ).const_mul
    (b / 100 * (eT * (d * ℓ) ^ (-2 : ℤ)))
  refine ((h1.sub h2).sub h3).congr_fun (fun x _ => ?_)
    (Submission.BoseGases.abox_measurable n ℓ)
  simp only [Pi.sub_apply]
  simp only [kinGroupRR]
  ring

/-! ## 3. The slot-`j` inequality -/

/-- **The pointwise slot inequality**: the one-body kinetic-group inequality at the slot-`j` fibre
of `Φ`, multiplied by the nonnegative window `1_{Λ(0)}(xⱼ)`. -/
lemma indU_mul_kinGroupLL_le {N n : ℕ} {ℓ s d eT b κ : ℝ} (fu : Work.BoseBoxFix.LowCut)
    (hτ : ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      kinGroupLL N ℓ s d eT b κ fu ψ ≤ kinGroupRR ℓ s d eT b ψ)
    (j : Fin n) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (x : Submission.BoseGases.X n) :
    Work.BoseKinLoc.indU ℓ 0 (x j) * kinGroupLL N ℓ s d eT b κ fu
        (Work.BoseKinLoc.fibre n j Φ x)
      ≤ Work.BoseKinLoc.indU ℓ 0 (x j) * kinGroupRR ℓ s d eT b
        (Work.BoseKinLoc.fibre n j Φ x) :=
  mul_le_mul_of_nonneg_left
    (hτ _ (hΦ.comp (contDiff_update (⊤ : ℕ∞) x j)))
    (Work.BoseKinLoc.Word.kinFormB_indU_nonneg ℓ 0 (x j))

/-- **The integrated slot inequality** (FS `prop:Hamilton2ndQuant`, slot `j`): the box integral of
the windowed kinetic group of the slot-`j` fibre is dominated by that of the reserve. -/
lemma integral_slot_kinGroupLL_le {N n : ℕ} {ℓ s d eT b κ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (fu : Work.BoseBoxFix.LowCut) (j : Fin n) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hτ : ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      kinGroupLL N ℓ s d eT b κ fu ψ ≤ kinGroupRR ℓ s d eT b ψ) :
    (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j)
        * kinGroupLL N ℓ s d eT b κ fu (Work.BoseKinLoc.fibre n j Φ x))
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j)
        * kinGroupRR ℓ s d eT b (Work.BoseKinLoc.fibre n j Φ x) :=
  integral_mono_ae (integrableOn_indU_kinGroupLL_fibre (N := N) hℓ fu j hΦ)
    (integrableOn_indU_kinGroupRR_fibre (ℓ := ℓ) (s := s) (d := d) (eT := eT) (b := b)
      hℓ hd j hΦ)
    (Filter.Eventually.of_forall (fun x =>
      indU_mul_kinGroupLL_le (N := N) (ℓ := ℓ) (s := s) (d := d) (eT := eT) (b := b) (κ := κ)
        fu hτ j hΦ x))

/-- The per-slot one-body inequality summed over the slots: the box slot integrals of the kinetic
group are dominated by `kinFormB` minus the reserves. -/
theorem kinGroup_slotSum_le {n : ℕ} {ℓ s d eT b κ : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (hd : 0 < d)
    (hd1 : d ≤ 1) (heT : 0 ≤ eT) (hb : 0 < b) {N : ℕ} (fu : Work.BoseBoxFix.LowCut)
    (hτ : ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∑ k : Work.BoseBoxFock.Lab N,
          Work.BoseBoxFock.tauSm eT s d ℓ (Work.BoseBoxFock.kmomLab ℓ N k) *
          ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
            (Work.BoseBoxFock.winState ℓ ψ) (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2))
        + b / (2 * ℓ ^ 2) * Work.BoseKinLoc.gapBare ℓ 0 ψ
        + eT * b / (2 * d ^ 2 * ℓ ^ 2) * ((1 / 32 : ℝ) * ∑ k : Work.BoseBoxFock.Lab N,
            Work.BoseBoxFock.etaH fu κ (Work.BoseBoxFock.kmomLab ℓ N k) *
              ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
                (Work.BoseBoxFock.winState ℓ ψ) (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2))
        ≤ Work.BoseKinLoc.fsT ℓ d s eT b 0 ψ
          - b / 4 * ((ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ)
          - b / 100 * (eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.momForm ℓ d 0 ψ))
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) *
          ((∑ k : Work.BoseBoxFock.Lab N,
              Work.BoseBoxFock.tauSm eT s d ℓ (Work.BoseBoxFock.kmomLab ℓ N k) *
              ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
                (Work.BoseBoxFock.winState ℓ (Work.BoseKinLoc.fibre n j Φ x))
                (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2))
            + b / (2 * ℓ ^ 2) *
                Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x)
            + eT * b / (2 * d ^ 2 * ℓ ^ 2) * ((1 / 32 : ℝ) *
                ∑ k : Work.BoseBoxFock.Lab N,
                  Work.BoseBoxFock.etaH fu κ (Work.BoseBoxFock.kmomLab ℓ N k) *
                  ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
                    (Work.BoseBoxFock.winState ℓ (Work.BoseKinLoc.fibre n j Φ x))
                    (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2))))
      ≤ Work.BoseKinLoc.kinFormB n ℓ d s eT b Φ
        - b / 4 * (ℓ ^ (-2 : ℤ) * Submission.BoseGases.cnPlus ℓ Φ)
        - b / 100 * (eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseBoxFix.nPlusHB ℓ d Φ) := by
  have hτ' : ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      kinGroupLL N ℓ s d eT b κ fu ψ ≤ kinGroupRR ℓ s d eT b ψ :=
    fun ψ hψ => hτ ψ hψ
  calc (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) *
          kinGroupLL N ℓ s d eT b κ fu (Work.BoseKinLoc.fibre n j Φ x))
      ≤ ∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) *
          kinGroupRR ℓ s d eT b (Work.BoseKinLoc.fibre n j Φ x) :=
        Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left
            (integral_slot_kinGroupLL_le (N := N) (κ := κ) hℓ hd fu j hΦ hτ')
            (by positivity))
    _ = Work.BoseKinLoc.kinFormB n ℓ d s eT b Φ
        - b / 4 * (ℓ ^ (-2 : ℤ) * Submission.BoseGases.cnPlus ℓ Φ)
        - b / 100 * (eT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseBoxFix.nPlusHB ℓ d Φ) :=
        kinGroupRhs_slotSum_eq (n := n) (ℓ := ℓ) (s := s) (d := d) (eT := eT) (b := b)
          hℓ hΦ

end Work.BoseBoxFock
