import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseB1Cube.PerBoxLHS
import Submission.Work.BoseFixB1B.matchedChainedBound
import Submission.Work.BoseFixB1S.perBoxGapBranchB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open Submission.BoseGases
open Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

/-! ## 1. Elementary integral bounds -/

private lemma setIntegral_normSq_le {k : ℕ} {s : Set (X k)}
    {E : Type*} [SeminormedAddCommGroup E]
    (hs : MeasurableSet s)
    [IsFiniteMeasure ((volume : Measure (X k)).restrict s)]
    {f : X k → E} {K : ℝ}
    (hb : ∀ z ∈ s, ‖f z‖ ≤ K) :
    ∫ z in s, ‖f z‖ ^ 2 ≤ K ^ 2 * (volume : Measure (X k)).real s := by
  have hK : Integrable (fun _ : X k => K ^ 2) ((volume : Measure (X k)).restrict s) := by
    rw [MeasureTheory.integrable_const_iff]
    exact Or.inr inferInstance
  have hae : ∀ᵐ z ∂((volume : Measure (X k)).restrict s), ‖f z‖ ^ 2 ≤ K ^ 2 := by
    rw [MeasureTheory.ae_restrict_iff' hs]
    exact Filter.Eventually.of_forall fun z hz => pow_le_pow_left₀ (norm_nonneg _) (hb z hz) 2
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => sq_nonneg (‖f z‖)) hK hae
  calc ∫ z in s, ‖f z‖ ^ 2
      = ∫ z, ‖f z‖ ^ 2 ∂((volume : Measure (X k)).restrict s) := rfl
    _ ≤ ∫ z, K ^ 2 ∂((volume : Measure (X k)).restrict s) := hmono
    _ = ∫ z in s, K ^ 2 := rfl
    _ = K ^ 2 * (volume : Measure (X k)).real s := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]

private theorem sum_tBamp_normSq_aux {n : ℕ} {A : Set ℝ³} (hA : MeasurableSet A) {χ : ℝ³ → ℝ}
    (hχ : ∀ z, χ z ≠ 0 → z ∈ A) {volA : ℝ} (i : Fin n) {Φ : X n → ℝ} (p : ℝ³) (x : X n) :
    ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2
      = ∑ k ∈ Finset.range (n + 1),
          ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2 := by
  classical
  set k0 : ℕ := (if x i ∈ A then boxOccupancy A x else boxOccupancy A x + 1) with hk0
  have hxk0 : x ∈ ampSector A i k0 := (mem_ampSector_iff A i k0 x).mpr hk0.symm
  have hk0mem : k0 ∈ Finset.range (n + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (ampShift_le A i hxk0))
  have hB : Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x
      = Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k0 Φ)) i x := by
    refine tBamp_congr_of_eqOn_fibre χ hχ p i (fun z hz => ?_)
    have hocc : boxOccupancy A (Function.update x i z) = k0 :=
      (boxOccupancy_update_of_mem A x i hz).trans hk0.symm
    exact boxQInd_sectorPiece_eq_of_mem (A := A) (volA := volA) hA i
      ((mem_sectorSet_iff A k0 (Function.update x i z)).mpr hocc)
  have hzero : ∀ k ∈ Finset.range (n + 1), k ≠ k0 →
      ‖Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2 = 0 := by
    intro k _ hne
    have hxnot : x ∉ ampSector A i k := by
      intro hmem
      rw [mem_ampSector_iff] at hmem
      exact hne (hmem.symm.trans hk0.symm)
    have h0 : Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x = 0 :=
      tBamp_eq_zero_of_notMem_ampSector hχ p
        (fun y hy => boxQInd_sectorPiece_eq_zero hA i hy) i hxnot
    rw [h0]
    simp
  rw [hB, Finset.sum_eq_single k0 hzero (fun hnot => absurd hk0mem hnot)]


/-! ## 2bis. The cube window: compact support, decay, and integrability of the sector amplitudes -/

/-- `chiSmallB M ℓ d u` is compactly supported: its support is contained in the support of the
big-box factor `chiScale ℓ x = χ(x/ℓ)`, hence in the compact box `acube ℓ`. -/
private lemma hcs_chiSmallB (M : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (d : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) :
    HasCompactSupport (Submission.BoseGases.chiSmallB M ℓ d u) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (Submission.BoseGases.acube_compact hℓ) ?_
  intro x hx
  exact Submission.BoseGases.chiScale_mem_acube hℓ
    (fun h => hx (by simp [Submission.BoseGases.chiSmallB, h]))

/-- **Rapid decay of the amplitude of FS's box projection at the cube cutoff.**  The window
`chiSmallB M ℓ d u` is `C³` (`M ≥ 4`) and compactly supported with support in `dlBox ℓ d u`, so
FS's decomposition `Q_{B,i}Φ = 1_BΦ − P_{B,i}Φ` (`Work.BoseBox.tBamp_boxQInd_eq_sub`) writes the
amplitude as the amplitude of the fixed smooth state `Φ` minus the box mean times the amplitude of
the constant state; both decay like `(1+‖p‖)^{-3}` by the Fourier decay engine
(`Work.BoseFixB1S.win.tBamp_decay_three`), and the box-mean factor is bounded by the sup of `Φ`
(`Work.BoseFixB1.boxP_dlBox_abs_le`). -/
lemma tBamp_chiSmallB_boxQInd_decay {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {M : ℕ} (hM : 4 ≤ M) (u : EuclideanSpace ℝ (Fin 3))
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Submission.BoseGases.X n), x ∈ Submission.BoseGases.abox n ℓ →
      ∀ (i : Fin n) (p : EuclideanSpace ℝ (Fin 3)),
      ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ≤ C / (1 + ‖p‖) ^ 3 := by
  classical
  obtain ⟨Mφ, hMφ0, hMφ⟩ :=
    Work.BoseFixB1.exists_bound_abox_pos (N := n) (ℓ := ℓ) hℓ hΦ.continuous
  have hMφ' : ∀ x : Submission.BoseGases.X n,
      (∀ j : Fin n, x j ∈ Submission.BoseGases.acube ℓ) → |Φ x| ≤ Mφ :=
    fun x hx => hMφ x ((Submission.BoseGases.mem_abox_iff n ℓ x).mpr hx)
  have hχc3 : ContDiff ℝ 3 (Submission.BoseGases.chiSmallB M ℓ d u) :=
    Work.BoseFixB1S.win.contDiff_three_chiSmallB hM hℓ hd u
  have hχcs : HasCompactSupport (Submission.BoseGases.chiSmallB M ℓ d u) :=
    hcs_chiSmallB M hℓ d u
  have hzero : ∀ z : EuclideanSpace ℝ (Fin 3),
      z ∉ Submission.BoseGases.dlBox ℓ d u → Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
    intro z hz
    by_contra hne
    exact hz (Work.SlotWord.chiSmallB_support_mem_dlBox (M := M) (by omega) hℓ hd hne)
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    Work.BoseFixB1S.win.tBamp_decay_three (N := n) (a := ℓ) hℓ hχc3 hχcs hΦ
  obtain ⟨C₂, hC₂0, hC₂⟩ :=
    Work.BoseFixB1S.win.tBamp_decay_three (N := n) (a := ℓ) hℓ hχc3 hχcs
      (Φ := fun _ : Submission.BoseGases.X n => (1 : ℝ)) contDiff_const
  refine ⟨C₁ + Mφ * C₂, by positivity, ?_⟩
  intro x hx i p
  rw [Work.BoseBox.tBamp_boxQInd_eq_sub Φ i p x 0 hzero hχc3.continuous hχcs hΦ.continuous]
  have hbP : |Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) i Φ (Function.update x i 0)| ≤ Mφ :=
    Work.BoseFixB1.boxP_dlBox_abs_le hℓ hd hMφ' i u x 0
      ((Submission.BoseGases.mem_abox_iff n ℓ x).mp hx)
  calc ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p Φ i x
        - ((Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ (Function.update x i 0) : ℝ) : ℂ)
          * Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
              (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x‖
      ≤ ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p Φ i x‖
        + ‖((Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ (Function.update x i 0) : ℝ) : ℂ)
          * Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
              (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x‖ := norm_sub_le _ _
    _ ≤ C₁ / (1 + ‖p‖) ^ 3 + Mφ * (C₂ / (1 + ‖p‖) ^ 3) := by
        refine add_le_add (hC₁ x hx i p) ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul hbP (hC₂ x hx i p) (norm_nonneg _) hMφ0
    _ = (C₁ + Mφ * C₂) / (1 + ‖p‖) ^ 3 := by ring

/-- **Integrability of the squared sector amplitudes at the cube cutoff.**  The sector amplitude is
dominated by the whole state's amplitude (pointwise Parseval, `sum_tBamp_normSq_aux`), which is
`≤ C(1+‖p‖)^{-3}` on `abox n a`; `abox n a` has finite measure, whence `IntegrableOn`. -/
private theorem integrableOn_amp_sq_of_decay {n : ℕ} {A : Set ℝ³} (hA : MeasurableSet A)
    {χ : ℝ³ → ℝ} (hχ : ∀ z, χ z ≠ 0 → z ∈ A) {volA a C : ℝ} (ha : 0 < a)
    {Φ : Submission.BoseGases.X n → ℝ} (i : Fin n)
    (hpair : ∀ k : ℕ, Measurable (fun q : ℝ³ × Submission.BoseGases.X n =>
      ‖Work.SmallBoxTBWord.tBamp χ q.1
        (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i q.2‖ ^ 2))
    (hdec : ∀ (x : Submission.BoseGases.X n), x ∈ Submission.BoseGases.abox n a → ∀ p : ℝ³,
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖
        ≤ C / (1 + ‖p‖) ^ 3)
    (p : ℝ³) (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      ‖Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2)
      (Submission.BoseGases.abox n a) := by
  refine MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n a ha.le) ?_
    ((C / (1 + ‖p‖) ^ 3) ^ 2) ?_
  · exact ((hpair k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem
      (Submission.BoseGases.abox_measurable n a)] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg (‖Work.SmallBoxTBWord.tBamp χ p
      (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖))]
    have hle : ‖Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖
        ≤ ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ := by
      have hsum := sum_tBamp_normSq_aux (volA := volA) (Φ := Φ) hA hχ i p x
      have h2 : ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2
          ≤ ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2 := by
        rw [hsum]
        exact Finset.single_le_sum (f := fun j : ℕ => ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd volA A i (sectorPiece A j Φ)) i x‖ ^ 2)
          (fun j _ => sq_nonneg _) hk
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _)
        (by norm_num : (2 : ℕ) ≠ 0)).mp h2
    exact pow_le_pow_left₀ (norm_nonneg _) (le_trans hle (hdec x hx p)) 2

private theorem tBdiagFormInd_sectorPiece_eq_aux {n : ℕ} {A : Set ℝ³} (hA : MeasurableSet A)
    {χ : ℝ³ → ℝ} (hχ : ∀ z, χ z ≠ 0 → z ∈ A) {volA a c : ℝ} (ha : 0 < a) (i : Fin n)
    {Φ : X n → ℝ}
    (hpair : ∀ k : ℕ, Measurable (fun q : ℝ³ × X n =>
      ‖Work.SmallBoxTBWord.tBamp χ q.1
        (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i q.2‖ ^ 2))
    (hdec : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : X n), x ∈ Submission.BoseGases.abox n a → ∀ p : ℝ³,
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖
        ≤ C / (1 + ‖p‖) ^ 3)
    (hXint : ∀ (p : ℝ³) (k : ℕ), k ∈ Finset.range (n + 1) →
      IntegrableOn (fun x : X n => ‖Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2)
        (Submission.BoseGases.abox n a)) :
    (∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2))
      = ∑ k ∈ Finset.range (n + 1),
          ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
            ∫ x in Submission.BoseGases.abox n a,
              ‖Work.SmallBoxTBWord.tBamp χ p
                (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2) := by
  classical
  obtain ⟨C, _hC0, hdec⟩ := hdec
  set V : ℝ := (volume : Measure (X n)).real (Submission.BoseGases.abox n a) with hV
  have hVnn : 0 ≤ V := by rw [hV]; exact MeasureTheory.measureReal_nonneg
  haveI hboxFin : IsFiniteMeasure ((volume : Measure (X n)).restrict
      (Submission.BoseGases.abox n a)) := by
    rw [Submission.BoseGases.restrict_abox_eq_pi]
    infer_instance
  have ha3inv : (0 : ℝ) < (a ^ 3)⁻¹ := by positivity
  -- (1) the pointwise Parseval identity
  have hsum : ∀ (p : ℝ³) (x : X n),
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2
        = ∑ k ∈ Finset.range (n + 1), ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2 :=
    fun p x => sum_tBamp_normSq_aux hA hχ i p x
  -- (2) the `x`-integral of the whole amplitude is the sum over the sectors
  have hfib : ∀ p : ℝ³,
      (∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2)
        = ∑ k ∈ Finset.range (n + 1), ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2 := by
    intro p
    rw [show (∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2)
        = ∫ x in Submission.BoseGases.abox n a, ∑ k ∈ Finset.range (n + 1),
            ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2
        from MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => hsum p x))]
    exact MeasureTheory.integral_finsetSum (Finset.range (n + 1)) (fun k hk => hXint p k hk)
  -- (3) the sector `x`-integral is bounded by the decay profile
  have hbound : ∀ (p : ℝ³) (k : ℕ), k ∈ Finset.range (n + 1) →
      (∫ x in Submission.BoseGases.abox n a, ‖Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2)
        ≤ (C / (1 + ‖p‖) ^ 3) ^ 2 * V := by
    intro p k hk
    rw [hV]
    refine setIntegral_normSq_le (f := fun x : X n => Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x)
      (K := C / (1 + ‖p‖) ^ 3) (Submission.BoseGases.abox_measurable n a) (fun x hx => ?_)
    have h1 : ‖Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2
        ≤ ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2 := by
      rw [hsum p x]
      exact Finset.single_le_sum (f := fun j : ℕ => ‖Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd volA A i (sectorPiece A j Φ)) i x‖ ^ 2)
        (fun j _ => sq_nonneg _) hk
    have h2 : ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖
        ≤ C / (1 + ‖p‖) ^ 3 := hdec x hx p
    exact le_trans ((pow_le_pow_iff_left₀
      (show (0 : ℝ) ≤ ‖Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖ from norm_nonneg _)
      (show (0 : ℝ) ≤ ‖Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ from norm_nonneg _)
      (by norm_num : (2 : ℕ) ≠ 0)).mp h1) h2
  -- (4) the `p`-integral of each summand is integrable
  have hPint : ∀ k ∈ Finset.range (n + 1), Integrable (fun p : ℝ³ =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a, ‖Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2)) := by
    intro k hk
    have hG : Integrable (fun p : ℝ³ => ((a ^ 3)⁻¹ * V) *
        (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2)) :=
      (Work.SlotWord.integrable_fsKinCoeff_decay c C).const_mul _
    refine hG.mono' ?_ ?_
    · have hjoint : AEStronglyMeasurable (fun q : ℝ³ × X n =>
          ‖Work.SmallBoxTBWord.tBamp χ q.1
            (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i q.2‖ ^ 2)
          ((volume : Measure ℝ³).prod
            ((volume : Measure (X n)).restrict (Submission.BoseGases.abox n a))) :=
        ((hpair k).aestronglyMeasurable).mono_measure
          (MeasureTheory.Measure.prod_mono le_rfl MeasureTheory.Measure.restrict_le_self)
      have hint := hjoint.integral_prod_right'
        (ν := (volume : Measure (X n)).restrict (Submission.BoseGases.abox n a))
      have hfsK : Continuous (fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
        rw [show (fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c ‖p‖)
            = (fun r : ℝ => (max (r - c) 0) ^ 2) ∘ fun p : ℝ³ => ‖p‖ from rfl]
        exact (((continuous_id.sub continuous_const).max continuous_const).pow 2).comp
          continuous_norm
      exact hfsK.aestronglyMeasurable.mul (hint.const_mul ((a ^ 3)⁻¹))
    · filter_upwards with p
      have hinner := hbound p k hk
      have hnn : 0 ≤ ∫ x in Submission.BoseGases.abox n a, ‖Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2 :=
        integral_nonneg (fun x => sq_nonneg _)
      rw [Real.norm_of_nonneg (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖)
        (mul_nonneg ha3inv.le hnn))]
      calc Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
            ∫ x in Submission.BoseGases.abox n a, ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2)
          ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
              ((C / (1 + ‖p‖) ^ 3) ^ 2 * V)) := by
            refine mul_le_mul_of_nonneg_left ?_ (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖)
            exact mul_le_mul_of_nonneg_left hinner ha3inv.le
        _ = ((a ^ 3)⁻¹ * V) *
            (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) := by ring
  -- (5) the two integrands agree
  have hpoint : (fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2))
      = fun p : ℝ³ => ∑ k ∈ Finset.range (n + 1),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
            ∫ x in Submission.BoseGases.abox n a, ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2) := by
    funext p
    rw [hfib p]
    simp only [Finset.mul_sum]
  rw [hpoint, MeasureTheory.integral_finsetSum (Finset.range (n + 1)) hPint]

/-- **Cube-window sector additivity of the spectral (`p`-diagonal) half of the small-box kinetic
word**: the faithful cube twin of the PROVED `Work.BoseFixB1.tBdiagFormInd_eq_sum_sectorPiece`,
with the ball cutoff `chiB ℓ d u` replaced by the cube cutoff `chiSmallB M ℓ d u` (the cutoff of
`Work.BoseFixB1B.sbKinCube`/`cubeSpectral`).  Proof recipe: copy the private helpers
`setIntegral_normSq_le`, `sum_tBamp_normSq_aux`, `tBdiagFormInd_sectorPiece_eq_aux` of
`Submission/Work/BoseFixB1/tBdiagFormInd_eq_sum_sectorPiece.lean` verbatim (they are generic in
`χ`), and supply the four hypotheses with `hχ := Work.SlotWord.chiSmallB_support_mem_dlBox`,
`hpair := Work.BoseFixB1.measurable_tBamp_boxQInd_pair` (needs only `Continuous χ`),
`hXint` (from the decay bound of the next item) and `hdec` := the whole-state cube decay, which is
the private lemma `tBamp_boxQInd_decay` of
`Submission/Work/BoseFixB1S/cubeSpectral_uniformBound.lean` §4 — re-derive it from the PUBLIC
`Work.BoseFixB1S.win.tBamp_decay_three` (`C³` window + compact support) together with
`Work.BoseBox.tBamp_boxQInd_eq_sub` and `Work.BoseFixB1.exists_bound_abox_pos`, exactly as
`Work.BoseFixB1S.win.boxWinModePGen_decay_three`'s `hdecQ`/`hboxP` steps do. -/
theorem tBdiagFormInd_cube_eq_sum_sectorPiece {n : ℕ} {ℓ d c : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) {M : ℕ} (hM : 4 ≤ M)
    (u : EuclideanSpace ℝ (Fin 3)) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin n) :
    (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2))
      = ∑ k ∈ Finset.range (n + 1),
          ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
              ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i
                  (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ)) i x‖ ^ 2)
    := by
  classical
  obtain ⟨C, hC0, hdec⟩ :=
    tBamp_chiSmallB_boxQInd_decay (n := n) (ℓ := ℓ) (d := d) hℓ hd hM u hΦ
  have hA : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hχc : Continuous (Submission.BoseGases.chiSmallB M ℓ d u) :=
    (Work.BoseFixB1S.win.contDiff_three_chiSmallB hM hℓ hd u).continuous
  have hχmem : ∀ z : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M ℓ d u z ≠ 0 →
      z ∈ Submission.BoseGases.dlBox ℓ d u :=
    fun z hz => Work.SlotWord.chiSmallB_support_mem_dlBox (M := M) (by omega) hℓ hd hz
  have hpairAll : ∀ k : ℕ, Measurable (fun q : EuclideanSpace ℝ (Fin 3) ×
      Submission.BoseGases.X n =>
      ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) q.1
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i
          (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ)) i q.2‖ ^ 2) :=
    fun k => Work.BoseFixB1.measurable_tBamp_boxQInd_pair hA hχc
      (hΦ.continuous.measurable.indicator
        (Work.FockBridge.sectorSet_measurable (Submission.BoseGases.dlBox ℓ d u) hA k)) i
  have hdec' : ∀ (x : Submission.BoseGases.X n), x ∈ Submission.BoseGases.abox n ℓ →
      ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ≤ C / (1 + ‖p‖) ^ 3 :=
    fun x hx p => hdec x hx i p
  exact tBdiagFormInd_sectorPiece_eq_aux (A := Submission.BoseGases.dlBox ℓ d u)
    (χ := Submission.BoseGases.chiSmallB M ℓ d u) (volA := Work.SmallBoxSliding.boxMass ℓ d u)
    (a := ℓ) (c := c) hA hχmem hℓ i hpairAll ⟨C, hC0, hdec'⟩
    (fun p k hk => integrableOn_amp_sq_of_decay (A := Submission.BoseGases.dlBox ℓ d u)
      (χ := Submission.BoseGases.chiSmallB M ℓ d u)
      (volA := Work.SmallBoxSliding.boxMass ℓ d u) (a := ℓ) (C := C) (Φ := Φ)
      hA hχmem hℓ i hpairAll hdec' p k hk)

end Work.BoseB1Cube
