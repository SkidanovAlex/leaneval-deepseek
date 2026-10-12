import ChallengeDeps
import Mathlib.CategoryTheory.Countable
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.boxMass_pos_of_goodSet
import Submission.Work.BoseFixB1B.sharpSlotJunkTransfer
import Submission.Work.BoseFixB1B.slotKinFibre
import Submission.Work.BoseFixB1B.slotPotFibreIntegrable
import Submission.Work.BoseFixB1B.tBwordBInd_boxInd_eq_zero
import Submission.Work.BoseKinLoc.Sector.integrable_sqNormB_fibState
import Submission.Work.BoseKinLoc.Sector.slotBox_setIntegral_slotIso
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.sharpSlotBound` --- the per-slot-set fibre assembly

The obligation `hslot` of `Work.BoseFixB1B.sectorCountBoxMaster`: for every slot set `S` of the
`B(u)`-occupancy decomposition of an `n`-particle box state `Phi`, the slot mass times the count
threshold is dominated by the sliding word of the slot piece.

## Proof structure: the case split on the integrability of the potential density

The intended vehicle is the PROVED `Work.BoseFixB1B.slotBound_of_sharp`, whose hypotheses are the
fibre factorisation of the word (`hfac`), the `y`-integrability of the fibre word (`hwordI`),
the mass identity (`hmassreal`) and the two a.e. identifications (`hid`, `hidm`).  The potential
halves of `hfac` and `hwordI` need the integrability of the localised potential density
`qLHSden * (slotPiece)^2` on the box --- which the statement's hypotheses do not supply: `Adm v
eps0 mu` with an *arbitrary* `eps0` admits non-dilute `mu`, where the one-body fibre of the
localised kernel diverges at the face of the box and the density is not integrable.  Hence the
proof splits on that integrability.

* **Good case** (`slotBound_of_integrable_on`).  If the potential density is integrable on the
  box, then the fibre factorisation of the word (`qLHSword_slotFibre` together with the Fubini
  step `slotPotFibreIntegrable`, and the kinetic word factorisation `slotKinFibre`) and the
  mass identity (`integral_slotFibreMassReal_piece_eq_slotMass` /
  `integrable_slotFibreMassReal_piece`, with the a.e. identification
  `slotFibreMassReal_eq_integral_sharp`) are available; the pointwise sharp core `hcore` at the
  fibre `slotFibreState S (slotIso S) Phi y` gives `m(y) * T <= fibreWord (pieceFibre y)` for
  a.e. `y`, and `integral_mono_ae` plus the mass identity and the word factorisation conclude.

* **Junk case** (`slotBound_of_not_integrable`).  If the potential density is NOT integrable,
  then `qLHSwordB (slotPiece ...)` is the junk value `0`.  The same non-integrability transfers
  to the sharp box state `1_{B^k}` (`Work.BoseFixB1B.qLHSsharp_junk`, in the companion module
  `Submission.Work.BoseFixB1B.sharpSlotJunkTransfer`), and
  `tBwordBInd` vanishes at `1_{B^k}` (`tBwordBInd_boxInd_eq_zero`, because the FS-faithful
  projection `Q_B = 1_B - P_B` annihilates the box indicator); `hcore` at the constant state
  `psi = 1` then forces `T <= 0`, and since the mass of the sharp constant is positive
  (`integral_sharpBoxState_one_sq_pos`), `tBwordBInd >= 0` and `slotMass >= 0`, the inequality
  follows.
-/

namespace Work.BoseFixB1B

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- On the outside configurations, the fibre of the slot piece is the sharp state of the fibre of
the state. -/
theorem pieceFibre_eq_sharpBoxState {n : ℕ} {L d : ℝ} (u : E3) (S : Finset (Fin n))
    (e : Work.PerSector.SlotIn n S ≃ Fin S.card) (Φ : Submission.BoseGases.X n → ℝ)
    (y : Work.PerSector.SlotOut n S → E3)
    (hy : ∀ j : Work.PerSector.SlotOut n S, y j ∉ Submission.BoseGases.dlBox L d u)
    (x : Submission.BoseGases.X S.card) :
    Work.SlotWord.pieceFibre (Submission.BoseGases.dlBox L d u) S e Φ y x
      = sharpBoxState (Submission.BoseGases.dlBox L d u)
          (Work.PerSector.slotFibreState S e Φ y) x := by
  classical
  rw [Work.SlotWord.pieceFibre_apply, sharpState_apply]
  by_cases hx : ∀ i : Fin S.card, x i ∈ Submission.BoseGases.dlBox L d u
  · rw [if_pos hx, Work.PerSector.slotFibreState_apply]
    exact Work.PerSector.slotPiece_slotComb _ S Φ (fun i => x (e i)) y
      (fun i => hx (e i)) hy
  · rw [if_neg hx]
    by_contra hne
    have hmem : Work.PerSector.slotComb S (fun i : Work.PerSector.SlotIn n S => x (e i)) y
        ∈ Work.PerSector.slotSet (Submission.BoseGases.dlBox L d u) S := by
      by_contra h0
      rw [Work.PerSector.slotPiece, Set.indicator_of_notMem h0] at hne
      exact hne rfl
    push_neg at hx
    obtain ⟨i, hi⟩ := hx
    have h1 := (Work.PerSector.slotComb_mem_slotSet_iff (Submission.BoseGases.dlBox L d u) S
      (fun i : Work.PerSector.SlotIn n S => x (e i)) y).mp hmem
    have h2 := h1.1 (e.symm i)
    rw [Equiv.apply_symm_apply] at h2
    exact hi h2


/-- For the slot piece of a localised box, the fibre mass over the localised box equals the fibre
mass over the ambient box. -/
theorem slotFibreMassReal_slotPiece_dlBox_eq_acube {n : ℕ} {L d : ℝ} (u : E3) (S : Finset (Fin n))
    {Φ : Submission.BoseGases.X n → ℝ} (y : Work.PerSector.SlotOut n S → E3)
    (hy : y ∈ Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S) :
    Work.PerSector.slotFibreMassReal (Submission.BoseGases.dlBox L d u) S
        (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y
      = Work.PerSector.slotFibreMassReal (Submission.BoseGases.acube L) S
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y := by
  classical
  set B : Set E3 := Submission.BoseGases.dlBox L d u with hBdef
  rw [Work.PerSector.slotFibreMassReal, Work.PerSector.slotFibreMassReal,
    Work.PerSector.slotFibreMass, Work.PerSector.slotFibreMass]
  set A : Set (Work.PerSector.SlotIn n S → E3) :=
    Work.PerSector.slotBox (ι := Work.PerSector.SlotIn n S) (Submission.BoseGases.acube L) with hAdef
  set A' : Set (Work.PerSector.SlotIn n S → E3) :=
    Work.PerSector.slotBox (ι := Work.PerSector.SlotIn n S) B with hA'def
  set f : (Work.PerSector.SlotIn n S → E3) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal ((Work.PerSector.slotPiece B S Φ (Work.PerSector.slotComb S z y)) ^ 2) with hfdef
  have hsub : A' ⊆ A := by
    rw [hAdef, hA'def]
    exact Work.PerSector.Work.PerSector.slotBox_mono (Work.SmallBoxSliding.dlBox_subset_acube L d u)
  have hAmeas : MeasurableSet A := by
    rw [hAdef]
    exact Work.PerSector.Work.PerSector.slotBox_measurable (Submission.BoseGases.acube_measurable L)
  have hA'meas : MeasurableSet A' := by
    rw [hA'def]
    exact Work.PerSector.Work.PerSector.slotBox_measurable (Work.SmallBoxSliding.measurableSet_dlBox L d u)
  have hvan : ∀ z ∈ A ∩ A'ᶜ, f z = 0 := by
    rintro z ⟨hzA, hznot⟩
    have hzB : ¬ ∀ i : Work.PerSector.SlotIn n S, z i ∈ B := by
      intro h
      exact hznot (by simpa [hA'def, Work.PerSector.slotBox] using h)
    obtain ⟨i, hi⟩ : ∃ i : Work.PerSector.SlotIn n S, z i ∉ B := by
      by_contra hcon
      exact hzB (fun i => by by_contra hc; exact hcon ⟨i, hc⟩)
    have hnotmem : Work.PerSector.slotComb S z y ∉ Work.PerSector.slotSet B S := by
      intro hmem
      have h1 := (Work.PerSector.slotComb_mem_slotSet_iff B S z y).mp hmem
      exact hi (h1.1 i)
    rw [hfdef]
    simp only
    rw [Work.PerSector.slotPiece, Set.indicator_of_notMem hnotmem]
    simp
  have hAeq : ∫⁻ z in A, f z = ∫⁻ z in A, A'.indicator f z := by
    refine lintegral_congr_ae ?_
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hAmeas]
    refine Filter.Eventually.of_forall (fun z hz => ?_)
    by_cases hz' : z ∈ A'
    · rw [Set.indicator_of_mem hz']
    · rw [Set.indicator_of_notMem hz']
      exact hvan z ⟨hz, hz'⟩
  rw [hAeq]
  have h1 : ∫⁻ z in A, A'.indicator f z = ∫⁻ z in A', f z ∂(MeasureTheory.volume.restrict A) := by
    rw [show (∫⁻ z in A, A'.indicator f z)
        = ∫⁻ z, A'.indicator f z ∂(MeasureTheory.volume.restrict A) from rfl,
      MeasureTheory.lintegral_indicator hA'meas]
  rw [h1]
  rw [show (∫⁻ z in A', f z ∂(MeasureTheory.volume.restrict A))
      = ∫⁻ z, f z ∂((MeasureTheory.volume.restrict A).restrict A') from rfl,
    MeasureTheory.Measure.restrict_restrict_of_subset hsub]


/-- **The a.e. mass identification**: the fibre mass of the slot piece is the `L²`-mass of the
sharp state of the fibre of the state. -/
theorem slotFibreMassReal_eq_integral_sharp {n : ℕ} {L d : ℝ} (hL : 0 < L) (u : E3)
    (S : Finset (Fin n)) {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    ∀ᵐ y ∂((MeasureTheory.volume : MeasureTheory.Measure
        (Work.PerSector.SlotOut n S → E3)).restrict
        (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S)),
      Work.PerSector.slotFibreMassReal (Submission.BoseGases.dlBox L d u) S
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y
        = ∫ x in Submission.BoseGases.abox S.card L,
            (sharpBoxState (Submission.BoseGases.dlBox L d u)
              (Work.PerSector.slotFibreState S (Work.BoseKinLoc.Sector.slotIso S) Φ y) x) ^ 2 := by
  classical
  set B : Set E3 := Submission.BoseGases.dlBox L d u with hBdef
  have hBsub : B ⊆ Submission.BoseGases.acube L := Work.SmallBoxSliding.dlBox_subset_acube L d u
  have hBmeas : MeasurableSet B := Work.SmallBoxSliding.measurableSet_dlBox L d u
  have hout : MeasurableSet (Work.PerSector.slotOutside L B S) :=
    Work.SlotWord.measurableSet_slotOutside L hBmeas S
  rw [MeasureTheory.ae_restrict_iff' hout]
  refine Filter.Eventually.of_forall (fun y hy => ?_)
  have hyB : ∀ j : Work.PerSector.SlotOut n S, y j ∉ B :=
    (Work.PerSector.mem_slotOutside_iff.mp hy).2
  have hyL : ∀ j : Work.PerSector.SlotOut n S, y j ∈ Submission.BoseGases.acube L :=
    (Work.PerSector.mem_slotOutside_iff.mp hy).1
  set A : Set (Work.PerSector.SlotIn n S → E3) :=
    Work.PerSector.slotBox (ι := Work.PerSector.SlotIn n S) B with hAdef
  set A' : Set (Fin S.card → E3) := Work.PerSector.slotBox (ι := Fin S.card) B with hA'def
  have hAmeas : MeasurableSet A := by
    rw [hAdef]
    exact Work.PerSector.Work.PerSector.slotBox_measurable hBmeas
  have hA'meas : MeasurableSet A' := by
    rw [hA'def]
    exact Work.PerSector.Work.PerSector.slotBox_measurable hBmeas
  have hboxsub : A' ⊆ Submission.BoseGases.abox S.card L := by
    intro z hz i
    exact hBsub (by simpa [hA'def, Work.PerSector.slotBox] using hz i)
  -- the bound on `Φ` over the ambient box and the integrability of the fibre map
  obtain ⟨CΦ, hCΦ⟩ := (Submission.BoseGases.abox_compact n hL).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n L) (f := Φ) hΦc.continuousOn
  have hAeq' : A = Set.univ.pi (fun _ : Work.PerSector.SlotIn n S => B) := by
    ext z; simp [hAdef, Work.PerSector.slotBox]
  have hAfin : (MeasureTheory.volume : MeasureTheory.Measure
      (Work.PerSector.SlotIn n S → E3)) A < ∞ := by
    rw [show A = Set.univ.pi (fun _ : Work.PerSector.SlotIn n S => B) from hAeq']
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
    exact ENNReal.prod_lt_top (fun _ _ => Work.SmallBoxSliding.volume_dlBox_lt_top hL d u)
  have hint : MeasureTheory.IntegrableOn
      (fun z : Work.PerSector.SlotIn n S → E3 => (Φ (Work.PerSector.slotComb S z y)) ^ 2) A := by
    refine MeasureTheory.IntegrableOn.of_bound hAfin ?_ (CΦ ^ 2) ?_
    · exact (((hΦc.comp (Work.FibreWord.continuous_slotComb_snd S y)).measurable).pow_const 2).aestronglyMeasurable
    · rw [MeasureTheory.ae_restrict_iff' hAmeas]
      refine Filter.Eventually.of_forall (fun z hz => ?_)
      have hzA : ∀ i, z i ∈ B := by simpa [hAdef, Work.PerSector.slotBox] using hz
      have hmem : Work.PerSector.slotComb S z y ∈ Submission.BoseGases.abox n L := by
        intro i
        rw [Work.PerSector.slotComb_apply]
        by_cases h : i ∈ S
        · rw [dif_pos h]; exact hBsub (hzA ⟨i, h⟩)
        · rw [dif_neg h]; exact hyL ⟨i, h⟩
      have h1 := hCΦ _ hmem
      have hCnn : 0 ≤ CΦ := le_trans (norm_nonneg _) h1
      rw [Real.norm_eq_abs] at h1
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      nlinarith [h1, abs_nonneg (Φ (Work.PerSector.slotComb S z y)), hCnn]
  -- step (a): the piece's integrand agrees with the state's on the slot box
  have hstep1 : Work.PerSector.slotFibreMassReal B S (Work.PerSector.slotPiece B S Φ) y
      = (∫⁻ z in A, ENNReal.ofReal ((Φ (Work.PerSector.slotComb S z y)) ^ 2)).toReal := by
    rw [Work.PerSector.slotFibreMassReal, Work.PerSector.slotFibreMass]
    congr 1
    rw [show (∫⁻ z in A, ENNReal.ofReal
          ((Work.PerSector.slotPiece B S Φ (Work.PerSector.slotComb S z y)) ^ 2))
        = ∫⁻ z, A.indicator (fun z => ENNReal.ofReal
            ((Work.PerSector.slotPiece B S Φ (Work.PerSector.slotComb S z y)) ^ 2)) z
        from (MeasureTheory.lintegral_indicator hAmeas
          (fun z => ENNReal.ofReal
            ((Work.PerSector.slotPiece B S Φ (Work.PerSector.slotComb S z y)) ^ 2))).symm,
      show (∫⁻ z in A, ENNReal.ofReal ((Φ (Work.PerSector.slotComb S z y)) ^ 2))
        = ∫⁻ z, A.indicator (fun z => ENNReal.ofReal
            ((Φ (Work.PerSector.slotComb S z y)) ^ 2)) z
        from (MeasureTheory.lintegral_indicator hAmeas
          (fun z => ENNReal.ofReal ((Φ (Work.PerSector.slotComb S z y)) ^ 2))).symm]
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz,
        Work.PerSector.slotPiece_slotComb B S Φ z y
          (by simpa [hAdef, Work.PerSector.slotBox] using hz) hyB]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
  -- step (b): `toReal` of the lintegral is the integral
  have hstep2 : (∫⁻ z in A, ENNReal.ofReal ((Φ (Work.PerSector.slotComb S z y)) ^ 2)).toReal
      = ∫ z in A, (Φ (Work.PerSector.slotComb S z y)) ^ 2 := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun z => sq_nonneg _)),
      ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg (fun z => sq_nonneg _))]
  -- step (c): the re-indexing along `slotIso S`
  have hstep3 : (∫ z in A, (Φ (Work.PerSector.slotComb S z y)) ^ 2)
      = ∫ x in A', (Φ (Work.PerSector.slotComb S
          (fun i : Work.PerSector.SlotIn n S => x (Work.BoseKinLoc.Sector.slotIso S i)) y)) ^ 2 := by
    have := Work.BoseKinLoc.Sector.slotBox_setIntegral_slotIso (N := n) S
      (fun x : Fin S.card → E3 => (Φ (Work.PerSector.slotComb S
        (fun i : Work.PerSector.SlotIn n S => x (Work.BoseKinLoc.Sector.slotIso S i)) y)) ^ 2)
      (by simpa only [hAdef, Equiv.symm_apply_apply] using hint)
    simpa only [hAdef, hA'def, Equiv.symm_apply_apply] using this
  -- step (d): the sharp state over the ambient box is the same integral
  have hstep4 : (∫ x in Submission.BoseGases.abox S.card L,
        (sharpBoxState B (Work.PerSector.slotFibreState S (Work.BoseKinLoc.Sector.slotIso S) Φ y) x) ^ 2)
      = ∫ x in A', (Φ (Work.PerSector.slotComb S
          (fun i : Work.PerSector.SlotIn n S => x (Work.BoseKinLoc.Sector.slotIso S i)) y)) ^ 2 := by
    have hsharp_eq : ∀ x : Fin S.card → E3,
        (sharpBoxState B (Work.PerSector.slotFibreState S (Work.BoseKinLoc.Sector.slotIso S) Φ y) x) ^ 2
          = A'.indicator (fun x => (Work.PerSector.slotFibreState S (Work.BoseKinLoc.Sector.slotIso S) Φ y x) ^ 2) x := by
      intro x
      rw [sharpState_apply]
      by_cases hx : ∀ i : Fin S.card, x i ∈ B
      · rw [if_pos hx, Set.indicator_of_mem (by simpa [hA'def, Work.PerSector.slotBox] using hx)]
      · rw [if_neg hx, Set.indicator_of_notMem (by simpa [hA'def, Work.PerSector.slotBox] using hx)]
        norm_num
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsharp_eq)]
    rw [MeasureTheory.setIntegral_indicator hA'meas]
    rw [Set.inter_eq_right.mpr hboxsub]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Work.PerSector.slotFibreState_apply]
  rw [hstep1, hstep2, hstep3, ← hstep4]


/-- **The good case**: if the potential density of the slot piece is integrable on the box, the
per-slot bound holds (fibre factorisation of the word + the pointwise core bound). -/
theorem slotBound_of_integrable_on {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    {ε₀ c C : ℝ} (hε₀ : 0 < ε₀) {μ : ℝ} (hμ : Work.BoseBoxFix.Adm v ε₀ μ)
    {u : E3} (hu : u ∈ Work.SmallBoxSliding.goodSet (PBℓ v μ) (PBd v μ) μ)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ))
    (S : Finset (Fin n)) (hS : 0 < S.card)
    (hcore : ∀ k : ℕ, SharpCountCoreAt h (PBM v μ) (PBℓ v μ) (PBd v μ) (PBeT v μ)
        (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) μ u k (PBThresh h c C μ u k))
    (hgi : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2
          * Submission.BoseGases.qLHSden n (PBℓ v μ) μ
              (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
              (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) x)
      (Submission.BoseGases.abox n (PBℓ v μ)))
    :
    Work.PerSector.slotMass (PBℓ v μ) (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ)
        * PBThresh h c C μ u S.card
      ≤ Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
          (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
          (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ))
        + Work.SmallBoxSliding.qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
          (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ)) := by
  classical
  have hM1 : 1 ≤ PBM v μ := by
    show 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hL : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hμ
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hμ
  -- the mass side, from the corpus (identity + integrability + the a.e. identification)
  have hBL : PBB v μ u ⊆ Submission.BoseGases.acube (PBℓ v μ) :=
    Work.SmallBoxSliding.dlBox_subset_acube (PBℓ v μ) (PBd v μ) u
  have hBmeas : MeasurableSet (PBB v μ u) :=
    Work.SmallBoxSliding.measurableSet_dlBox (PBℓ v μ) (PBd v μ) u
  have hΦm : Measurable (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous.measurable
  have hfin : (∫⁻ x in Submission.BoseGases.abox n (PBℓ v μ),
      ENNReal.ofReal (((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)) ≠ ⊤ :=
    Work.FockBridge.sectorMassENN_ne_top_of_continuous Φ.contDiff.continuous
  have hmass : Work.PerSector.slotMass (PBℓ v μ) (PBB v μ u) S
        (Φ : Submission.BoseGases.X n → ℝ)
      = ∫ y in Work.PerSector.slotOutside (PBℓ v μ) (PBB v μ u) S,
          Work.PerSector.slotFibreMassReal (PBB v μ u) S
            (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ)) y :=
    (Work.SlotWord.integral_slotFibreMassReal_piece_eq_slotMass (N := n) (PBℓ v μ) S
      hBL hBmeas hΦm hfin).symm
  have hmassI : MeasureTheory.Integrable
      (fun y : Work.PerSector.SlotOut n S → E3 =>
        Work.PerSector.slotFibreMassReal (PBB v μ u) S
          (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ)) y)
      ((MeasureTheory.volume : MeasureTheory.Measure (Work.PerSector.SlotOut n S → E3)).restrict
        (Work.PerSector.slotOutside (PBℓ v μ) (PBB v μ u) S)) :=
    Work.SlotWord.integrable_slotFibreMassReal_piece (N := n) (PBℓ v μ) S hBL hBmeas hΦm hfin
  have hidm := slotFibreMassReal_eq_integral_sharp (d := PBd v μ) hL u S Φ.contDiff.continuous
  obtain ⟨hkinI, hkinFac⟩ :=
    slotKinFibre (c := c) (C := C) h hv hv1 hvrad hR hv_supp hav hε₀ hμ hu Φ S hS
      (Work.BoseKinLoc.Sector.slotIso S)
  have hpotI := slotPotFibreIntegrable (c := c) (C := C) h hv hv1 hvrad hR hv_supp hav hε₀ hμ hu Φ S
    (Work.BoseKinLoc.Sector.slotIso S) hgi
  have hout : MeasurableSet (Work.PerSector.slotOutside (PBℓ v μ) (PBB v μ u) S) :=
    Work.SlotWord.measurableSet_slotOutside (PBℓ v μ)
      (Work.SmallBoxSliding.measurableSet_dlBox _ _ _) S
  have hsupp1 : ∀ x : E3, x ∉ Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u →
      ∀ y : E3, Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u x y = 0 :=
    fun x hx y => Work.SlotWord.wSmall1Pair_support_left hM1 hL hd u hx y
  have hsupp2 : ∀ x y : E3, (x ∉ Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u ∨
      y ∉ Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) →
      Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v x y = 0 := by
    intro x y hxy
    rcases hxy with hx | hy
    · exact Work.SlotWord.wSmallPair_support_left hM1 hL hd u v hx y
    · have h0 : Submission.BoseGases.chiSmallB (PBM v μ) (PBℓ v μ) (PBd v μ) u y = 0 := by
        by_contra hne
        exact hy (Work.SlotWord.chiSmallB_support_mem_dlBox hM1 hL hd hne)
      rw [Submission.BoseGases.wSmallPair, h0, mul_zero]
  -- the `hid` identification, a.e.
  have hid : ∀ᵐ y ∂((MeasureTheory.volume : MeasureTheory.Measure
        (Work.PerSector.SlotOut n S → E3)).restrict
        (Work.PerSector.slotOutside (PBℓ v μ) (PBB v μ u) S)),
      Work.SlotWord.pieceFibre (PBB v μ u) S (Work.BoseKinLoc.Sector.slotIso S)
          (Φ : Submission.BoseGases.X n → ℝ) y
        = sharpBoxState (PBB v μ u)
            (Work.PerSector.slotFibreState S (Work.BoseKinLoc.Sector.slotIso S)
              (Φ : Submission.BoseGases.X n → ℝ) y) := by
    rw [MeasureTheory.ae_restrict_iff' hout]
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    funext x
    exact pieceFibre_eq_sharpBoxState u S (Work.BoseKinLoc.Sector.slotIso S)
      (Φ : Submission.BoseGases.X n → ℝ) y (Work.PerSector.mem_slotOutside_iff.mp hy).2 x
  -- the potential factorisation
  have hpotFac : Work.SmallBoxSliding.qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
        (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ))
      = ∫ y in Work.PerSector.slotOutside (PBℓ v μ) (PBB v μ u) S,
          Submission.BoseGases.qLHSword (N := S.card) (PBℓ v μ) μ
            (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
            (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
            (Work.SlotWord.pieceFibre (PBB v μ u) S (Work.BoseKinLoc.Sector.slotIso S)
              (Φ : Submission.BoseGases.X n → ℝ) y) := by
    have h1 := Work.SlotWord.qLHSword_slotFibre (N := n) (PBℓ v μ) (PBd v μ) μ u S
      (Φ : Submission.BoseGases.X n → ℝ) (Work.BoseKinLoc.Sector.slotIso S)
      (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
      (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) hsupp1 hsupp2 hgi
    simpa only [Work.SmallBoxSliding.qLHSwordB, PBB, Work.SlotWord.pieceFibre] using h1
  -- the fibre word is integrable (presented as the pointwise sum)
  have hwordI : MeasureTheory.Integrable
      (fun y : Work.PerSector.SlotOut n S → E3 =>
        Work.UBBInputs8.tBwordBInd S.card (PBℓ v μ) (PBd v μ) (PBeT v μ)
            (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
            (Work.SlotWord.pieceFibre (PBB v μ u) S (Work.BoseKinLoc.Sector.slotIso S)
              (Φ : Submission.BoseGases.X n → ℝ) y)
          + Submission.BoseGases.qLHSword (N := S.card) (PBℓ v μ) μ
              (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
              (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
              (Work.SlotWord.pieceFibre (PBB v μ u) S (Work.BoseKinLoc.Sector.slotIso S)
                (Φ : Submission.BoseGases.X n → ℝ) y))
      ((MeasureTheory.volume : MeasureTheory.Measure (Work.PerSector.SlotOut n S → E3)).restrict
        (Work.PerSector.slotOutside (PBℓ v μ) (PBB v μ u) S)) :=
    hkinI.add hpotI
  -- the word factorisation, in the pointwise-sum form matching the goal
  have hwordFac : Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
          (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
          (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ))
        + Work.SmallBoxSliding.qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
          (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ))
      = ∫ y in Work.PerSector.slotOutside (PBℓ v μ) (PBB v μ u) S,
          (Work.UBBInputs8.tBwordBInd S.card (PBℓ v μ) (PBd v μ) (PBeT v μ)
              (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
              (Work.SlotWord.pieceFibre (PBB v μ u) S (Work.BoseKinLoc.Sector.slotIso S)
                (Φ : Submission.BoseGases.X n → ℝ) y)
            + Submission.BoseGases.qLHSword (N := S.card) (PBℓ v μ) μ
                (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
                (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
                (Work.SlotWord.pieceFibre (PBB v μ u) S (Work.BoseKinLoc.Sector.slotIso S)
                  (Φ : Submission.BoseGases.X n → ℝ) y)) := by
    rw [hkinFac, hpotFac, ← MeasureTheory.integral_add hkinI hpotI]
  -- the pointwise core bound, a.e. in `y`
  have hpt : ∀ᵐ y ∂((MeasureTheory.volume : MeasureTheory.Measure
        (Work.PerSector.SlotOut n S → E3)).restrict
        (Work.PerSector.slotOutside (PBℓ v μ) (PBB v μ u) S)),
      Work.PerSector.slotFibreMassReal (PBB v μ u) S
          (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ)) y
        * PBThresh h c C μ u S.card
      ≤ Work.UBBInputs8.tBwordBInd S.card (PBℓ v μ) (PBd v μ) (PBeT v μ)
            (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
            (Work.SlotWord.pieceFibre (PBB v μ u) S (Work.BoseKinLoc.Sector.slotIso S)
              (Φ : Submission.BoseGases.X n → ℝ) y)
          + Submission.BoseGases.qLHSword (N := S.card) (PBℓ v μ) μ
              (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
              (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
              (Work.SlotWord.pieceFibre (PBB v μ u) S (Work.BoseKinLoc.Sector.slotIso S)
                (Φ : Submission.BoseGases.X n → ℝ) y) := by
    filter_upwards [hidm, hid] with y h1 h2
    have hc := hcore S.card
      (Work.PerSector.slotFibreState S (Work.BoseKinLoc.Sector.slotIso S)
        (Φ : Submission.BoseGases.X n → ℝ) y)
      (Work.PerSector.contDiff_slotFibreState S (Work.BoseKinLoc.Sector.slotIso S) Φ.contDiff y)
      (Work.BoseFixB1B.permInvariant_slotFibreState S (Work.BoseKinLoc.Sector.slotIso S) Φ.symm y)
    rw [← h1, ← h2, Work.SlotWord.fibreWord] at hc
    exact hc
  -- integrate
  have hmono := MeasureTheory.integral_mono_ae (hmassI.mul_const _) hwordI hpt
  calc Work.PerSector.slotMass (PBℓ v μ) (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ)
        * PBThresh h c C μ u S.card
      = (∫ y in Work.PerSector.slotOutside (PBℓ v μ) (PBB v μ u) S,
          Work.PerSector.slotFibreMassReal (PBB v μ u) S
            (Work.PerSector.slotPiece (PBB v μ u) S
              (Φ : Submission.BoseGases.X n → ℝ)) y) * PBThresh h c C μ u S.card := by
            rw [hmass]
    _ = ∫ y in Work.PerSector.slotOutside (PBℓ v μ) (PBB v μ u) S,
          Work.PerSector.slotFibreMassReal (PBB v μ u) S
            (Work.PerSector.slotPiece (PBB v μ u) S
              (Φ : Submission.BoseGases.X n → ℝ)) y * PBThresh h c C μ u S.card :=
            (MeasureTheory.integral_mul_const _ _).symm
    _ ≤ ∫ y in Work.PerSector.slotOutside (PBℓ v μ) (PBB v μ u) S,
          (Work.UBBInputs8.tBwordBInd S.card (PBℓ v μ) (PBd v μ) (PBeT v μ)
              (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
              (Work.SlotWord.pieceFibre (PBB v μ u) S (Work.BoseKinLoc.Sector.slotIso S)
                (Φ : Submission.BoseGases.X n → ℝ) y)
            + Submission.BoseGases.qLHSword (N := S.card) (PBℓ v μ) μ
                (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
                (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
                (Work.SlotWord.pieceFibre (PBB v μ u) S (Work.BoseKinLoc.Sector.slotIso S)
                  (Φ : Submission.BoseGases.X n → ℝ) y)) := hmono
    _ = Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
          (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
          (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ))
        + Work.SmallBoxSliding.qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
          (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ)) :=
            hwordFac.symm

/-- The `L²`-mass of the sharp box state of the constant is the `S.card`-th power of the box mass. -/
theorem integral_sharpBoxState_one_sq {L d : ℝ} (hL : 0 < L) (u : E3) (k : ℕ) :
    ∫ x in Submission.BoseGases.abox k L,
        (sharpBoxState (Submission.BoseGases.dlBox L d u)
          (fun _ : Submission.BoseGases.X k => (1 : ℝ)) x) ^ 2
      = ((MeasureTheory.volume (Submission.BoseGases.dlBox L d u)) ^ k).toReal := by
  classical
  set B : Set E3 := Submission.BoseGases.dlBox L d u with hB
  have hBsub : B ⊆ Submission.BoseGases.acube L :=
    Work.SmallBoxSliding.dlBox_subset_acube L d u
  have hBmeas : MeasurableSet B := Work.SmallBoxSliding.measurableSet_dlBox L d u
  have hsharp_eq : ∀ x : Submission.BoseGases.X k,
      (sharpBoxState B (fun _ : Submission.BoseGases.X k => (1 : ℝ)) x) ^ 2
        = (Work.PerSector.slotBox (ι := Fin k) B).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    rw [sharpState_apply]
    by_cases hx : ∀ i : Fin k, x i ∈ B
    · rw [if_pos hx, Set.indicator_of_mem (by simpa [Work.PerSector.slotBox] using hx)]
      norm_num
    · rw [if_neg hx, Set.indicator_of_notMem (by simpa [Work.PerSector.slotBox] using hx)]
      norm_num
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsharp_eq)]
  have hslotBox : Work.PerSector.slotBox (ι := Fin k) B = Set.univ.pi (fun _ : Fin k => B) := by
    ext x; simp [Work.PerSector.slotBox]
  rw [hslotBox]
  have hmeasBox : MeasurableSet (Set.univ.pi (fun _ : Fin k => B)) :=
    MeasurableSet.pi Set.countable_univ (fun i _ => hBmeas)
  rw [MeasureTheory.setIntegral_indicator hmeasBox]
  have hsubset : Set.univ.pi (fun _ : Fin k => B) ⊆ Submission.BoseGases.abox k L := by
    intro x hx i
    exact hBsub (by simpa using hx i)
  have hinter : Submission.BoseGases.abox k L ∩ Set.univ.pi (fun _ : Fin k => B)
      = Set.univ.pi (fun _ : Fin k => B) :=
    Set.inter_eq_right.mpr hsubset
  rw [hinter]
  rw [MeasureTheory.setIntegral_const]
  rw [smul_eq_mul, mul_one]
  rw [MeasureTheory.volume_pi, MeasureTheory.Measure.real, MeasureTheory.Measure.pi_pi]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]


/-- The `L²`-mass of the sharp box state of the constant is positive. -/
theorem integral_sharpBoxState_one_sq_pos {L d μ : ℝ} (hL : 0 < L) (hd : 0 < d) (hμ : 0 < μ)
    {u : E3} (hu : u ∈ Work.SmallBoxSliding.goodSet L d μ) (k : ℕ) :
    0 < ∫ x in Submission.BoseGases.abox k L,
        (sharpBoxState (Submission.BoseGases.dlBox L d u)
          (fun _ : Submission.BoseGases.X k => (1 : ℝ)) x) ^ 2 := by
  rw [integral_sharpBoxState_one_sq hL u k]
  have hbm : 0 < Work.SmallBoxSliding.boxMass L d u :=
    Work.BoseFixB1.boxMass_pos_of_goodSet hL hd hμ hu
  have hreal : 0 < MeasureTheory.volume.real (Submission.BoseGases.dlBox L d u) := by
    rwa [← Work.SmallBoxSliding.boxMass_eq_measureReal L d u]
  rw [MeasureTheory.Measure.real] at hreal
  have hne : (MeasureTheory.volume (Submission.BoseGases.dlBox L d u)) ≠ 0 := by
    intro h0
    rw [h0] at hreal
    simp at hreal
  rw [ENNReal.toReal_pow]
  exact pow_pos (ENNReal.toReal_pos hne
    (Work.SmallBoxSliding.volume_dlBox_lt_top hL d u).ne) k

/-- **The junk case of the per-slot bound**: if the potential density of the slot piece is not
integrable on the box, then its potential word is the junk value `0`, the same non-integrability
forces the sharp box state's potential word to `0`, and `hcore` at the constant state gives
`T <= 0`; with `tBwordBInd >= 0` and `slotMass >= 0` the per-slot bound follows. -/
theorem slotBound_of_not_integrable {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    {ε₀ c C : ℝ} (hε₀ : 0 < ε₀) {μ : ℝ} (hμ : Work.BoseBoxFix.Adm v ε₀ μ)
    {u : E3} (hu : u ∈ Work.SmallBoxSliding.goodSet (PBℓ v μ) (PBd v μ) μ)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ))
    (hcore : ∀ k : ℕ, SharpCountCoreAt h (PBM v μ) (PBℓ v μ) (PBd v μ) (PBeT v μ)
        (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) μ u k (PBThresh h c C μ u k))
    (S : Finset (Fin n)) (hS : 0 < S.card)
    (hni : ¬ MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2
          * Submission.BoseGases.qLHSden n (PBℓ v μ) μ
              (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
              (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) x)
      (Submission.BoseGases.abox n (PBℓ v μ)))
    :
    Work.PerSector.slotMass (PBℓ v μ) (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ)
        * PBThresh h c C μ u S.card
      ≤ Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
          (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
          (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ))
        + Work.SmallBoxSliding.qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
          (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ)) := by
  classical
  have hL : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hμ
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hμ
  have hμpos : 0 < μ := hμ.1
  -- the slot piece's potential word is the junk value `0`
  have hQ : Work.SmallBoxSliding.qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
      (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ)) = 0 := by
    rw [Work.SmallBoxSliding.qLHSwordB, Submission.BoseGases.qLHSword]
    exact MeasureTheory.integral_undef (by
      simpa only [MeasureTheory.IntegrableOn, Submission.BoseGases.qLHSden] using hni)
  -- `hcore` at the constant state gives `T <= 0`
  have hvol : 0 < ∫ x in Submission.BoseGases.abox S.card (PBℓ v μ),
      (sharpBoxState (PBB v μ u) (fun _ : Submission.BoseGases.X S.card => (1 : ℝ)) x) ^ 2 :=
    integral_sharpBoxState_one_sq_pos hL hd hμpos hu S.card
  have hQ0 : Work.SmallBoxSliding.qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
      (sharpBoxState (PBB v μ u) (fun _ : Submission.BoseGases.X S.card => (1 : ℝ))) = 0 :=
    qLHSsharp_junk h hv hv1 hvrad hR hv_supp hav hε₀ hμ hu Φ S hS hni
  have hT0 : Work.UBBInputs8.tBwordBInd S.card (PBℓ v μ) (PBd v μ) (PBeT v μ)
      (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
      (sharpBoxState (PBB v μ u) (fun _ : Submission.BoseGases.X S.card => (1 : ℝ))) = 0 :=
    tBwordBInd_boxInd_eq_zero hL hd u S.card
  have hc := hcore S.card (fun _ : Submission.BoseGases.X S.card => (1 : ℝ))
    contDiff_const (fun σ x => rfl)
  rw [Work.SlotWord.fibreWord, hT0, hQ0, add_zero] at hc
  have hT : PBThresh h c C μ u S.card ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [hvol, hc]
  -- assemble
  have hsm : 0 ≤ Work.PerSector.slotMass (PBℓ v μ) (PBB v μ u) S
      (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.PerSector.slotMass_nonneg _ _ _ _
  have htbn : 0 ≤ Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
      (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
      (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ)) :=
    Work.UBBInputs9.A.tBwordBInd_nonneg hL (Work.BoseFixB1.adm_eT_bounds hμ).1 u _
  calc Work.PerSector.slotMass (PBℓ v μ) (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ)
        * PBThresh h c C μ u S.card
      ≤ Work.PerSector.slotMass (PBℓ v μ) (PBB v μ u) S
          (Φ : Submission.BoseGases.X n → ℝ) * 0 := mul_le_mul_of_nonneg_left hT hsm
    _ = 0 := mul_zero _
    _ ≤ Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
          (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
          (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ))
        + Work.SmallBoxSliding.qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
          (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ)) := by
        rw [hQ, add_zero]
        exact htbn


/-- **`Work.BoseFixB1B.sharpSlotBound`** --- the per-slot-set fibre assembly (the `hslot`
obligation of `Work.BoseFixB1B.sectorCountBoxMaster`). -/
theorem sharpSlotBound {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    {ε₀ c C : ℝ} (hε₀ : 0 < ε₀) {μ : ℝ} (hμ : Work.BoseBoxFix.Adm v ε₀ μ)
    {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseFixB1B.PBℓ v μ))
    (hcore : ∀ k : ℕ, Work.BoseFixB1B.SharpCountCoreAt h (Work.BoseFixB1B.PBM v μ)
        (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) (Work.BoseFixB1B.PBeT v μ)
        (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) μ u k
        (Work.BoseFixB1B.PBThresh h c C μ u k)) :
    ∀ S : Finset (Fin n), 0 < S.card →
      Work.PerSector.slotMass (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u)
          S (Φ : Submission.BoseGases.X n → ℝ) * Work.BoseFixB1B.PBThresh h c C μ u S.card
        ≤ Work.UBBInputs8.tBwordBInd n (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ)
            (Work.BoseFixB1B.PBeT v μ) (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
            (Work.PerSector.slotPiece (Work.BoseFixB1B.PBB v μ u) S
              (Φ : Submission.BoseGases.X n → ℝ))
          + Work.SmallBoxSliding.qLHSwordB h (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) μ u
            (Work.PerSector.slotPiece (Work.BoseFixB1B.PBB v μ u) S
              (Φ : Submission.BoseGases.X n → ℝ))  := by
  intro S hS
  by_cases hgi : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        (Work.PerSector.slotPiece (Work.BoseFixB1B.PBB v μ u) S
            (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2
          * Submission.BoseGases.qLHSden n (Work.BoseFixB1B.PBℓ v μ) μ
              (Submission.BoseGases.wSmallPair (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                (Work.BoseFixB1B.PBd v μ) u v)
              (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                (Work.BoseFixB1B.PBd v μ) u) x)
      (Submission.BoseGases.abox n (Work.BoseFixB1B.PBℓ v μ))
  · exact slotBound_of_integrable_on h hv hv1 hvrad hR hv_supp hav hε₀ hμ hu Φ S hS hcore hgi
  · exact slotBound_of_not_integrable h hv hv1 hvrad hR hv_supp hav hε₀ hμ hu Φ hcore S hS hgi

end Work.BoseFixB1B
