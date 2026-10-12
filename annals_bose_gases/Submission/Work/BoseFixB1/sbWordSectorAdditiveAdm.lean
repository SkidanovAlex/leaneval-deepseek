import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseFixB1.integrableOn_sectorPiece_sq_qLHSden_regime
import Submission.Work.BoseFixB1.integrableOn_tBamp_sectorPiece_sq
import Submission.Work.BoseFixB1.integrable_prod_ampEnergy_sectorPiece
import Submission.Work.BoseFixB1.integrable_tBamp_kernel_sectorPiece
import Submission.Work.FibreKinPot.Trunc.integrableOn_tBamp_boxQInd_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.sbWordSectorAdditiveAdm`

The **`Adm`-restricted sector additivity of the frozen localised small-box word**

    ∃ ε₀ > 0, SbWordSectorAdditive v h ε₀

under the six standing hypotheses of Theorem 1.2 (`ScatSol v`, `0 ≤ v`, `v ∈ L¹`, radial,
`tsupport v ⊆ ball 0 R`, `0 < a v`).

## The two halves

`SbWordSectorAdditive v h ε₀` asks, for every admissible `μ` (`Adm v ε₀ μ`, i.e. the dilute
regime) and every `n`, `Φ`, `u`,

    sbWord h μ u Φ = Σ_{k ≤ n} [ tBwordBInd n ℓ d ε_T (dsℓ)⁻¹ u Φ_k + qLHSwordB h M ℓ d μ u Φ_k ] ,

with `ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`, `M = (paramsAt μ (a v)).M`,
`Φ_k = sectorPiece (dlBox ℓ d u) k Φ` and `sbWord = sbKin + sbPot`.  Both halves are *locality*
statements:

* **kinetic half** `tBwordBInd n ℓ d ε c u Φ = Σ_k tBwordBInd n ℓ d ε c u Φ_k`
  (`tBwordBInd_eq_sum_sectorPiece` below) — `tBwordInd_eq_sum_sectorPiece` fed the two per-slot
  additivities `cnPlusBoxInd_eq_sum_sectorPiece_sliding` (gap) and
  `tBdiagFormInd_sectorPiece_additive` (spectral);
* **potential half** `qLHSwordB h M ℓ d μ u Φ = Σ_k qLHSwordB h M ℓ d μ u Φ_k`
  — `qLHSword_eq_sum_sectorPiece`, whose `IntegrableOn` side condition is discharged in the
  regime by `integrableOn_sectorPiece_sq_qLHSden_regime`.

The `Adm` binder is **load-bearing** (see `FINDING_sbWordSectorAdditive_needs_integrable.md`):
the potential half splits a *signed* Bochner integral, so it needs the `IntegrableOn` of every
sector summand, which the six standing hypotheses do not supply outside the regime.  The regime
threshold `ε₀` is chosen from `regime_sideAt_ge` so that for every admitted `μ` both
`R ≤ ℓ d / 16` and `R ≤ ℓ · chiR0` hold — exactly the standing hypotheses of every supplier of
the localised-kernel bounds.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge
open Work.BoseFixB1B

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. Bounds of a continuous state on the box, and the gap half of the kinetic word -/

/-- A continuous function is bounded on the box `abox n ℓ`. -/
private lemma exists_abs_bound_abox' {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : X n → ℝ} (hΦc : Continuous Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ abox n ℓ, |Φ x| ≤ C := by
  obtain ⟨C, hC⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have h := hC x hx
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-- **The box excited count is additive over the `B(u)`-occupancy sectors** (the gap half of the
kinetic word): for a continuous state `Φ`, `∫ (Q_{B(u),i}Φ)²` is the sum, over the occupancy
sectors, of `∫ (Q_{B(u),i}Φ_k)²`.  Each piece is bounded on the box, so the integrability side
condition of `cnPlusBoxInd_eq_sum_sectorPiece` is automatic. -/
theorem cnPlusBoxInd_eq_sum_sectorPiece_sliding {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {Φ : X n → ℝ} (hΦc : Continuous Φ) (i : Fin n) :
    (∫ x in abox n ℓ,
        (Work.UBBInputs8.boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
      = ∑ k ∈ Finset.range (n + 1),
          ∫ x in abox n ℓ,
            (Work.UBBInputs8.boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i
              (sectorPiece (dlBox ℓ d u) k Φ) x) ^ 2 := by
  have hA : MeasurableSet (dlBox ℓ d u) := measurableSet_dlBox ℓ d u
  obtain ⟨C, hC0, hCb⟩ := exists_abs_bound_abox' (n := n) (ℓ := ℓ) hℓ hΦc
  have hpiece : ∀ k : ℕ, IntegrableOn (fun x : X n =>
      (Work.UBBInputs8.boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i
        (sectorPiece (dlBox ℓ d u) k Φ) x) ^ 2) (abox n ℓ) := by
    intro k
    refine boxQInd_sq_integrableOn_of_bound (N := n) hℓ u ?_ hC0 ?_ i
    · exact Measurable.indicator hΦc.measurable
        (Work.FockBridge.sectorSet_measurable (dlBox ℓ d u) hA k)
    · intro x hx
      by_cases hxs : x ∈ Work.FockBridge.sectorSet (dlBox ℓ d u) k
      · rw [sectorPiece, Set.indicator_of_mem hxs]
        exact hCb x hx
      · rw [sectorPiece, Set.indicator_of_notMem hxs]
        simpa using hC0
  refine Work.FockBridge.cnPlusBoxInd_eq_sum_sectorPiece hA i (fun k _ => hpiece k) ?_
  exact boxQInd_sq_integrableOn_of_bound (N := n) hℓ u hΦc.measurable hC0 hCb i

/-! ## 1. The spectral (gap-free) half of the kinetic word -/

/-- **Sector additivity of the `p`-diagonal (spectral) half of the small-box kinetic word.**

The squared windowed amplitude of FS's box projection splits pointwise over the `B(u)`-occupancy
sectors (`Work.FockBridge.sum_tBamp_normSq`: `Q_{B,i}` maps the count-`k` piece into the count-`k`
sector, so at most one summand survives at each configuration, and it *equals* the whole state's
amplitude).  The two finite-sum/integral interchanges are then legitimate because

* each squared sector amplitude is `abox`-integrable (`integrableOn_tBamp_sectorPiece_sq`, from the
  sup bound of the piece on the compact box), and
* each `p`-diagonal summand is `p`-integrable: its joint `(p,x)`-integrand is integrable against
  `volume.prod (volume.restrict (abox n ℓ))` (`integrable_prod_ampEnergy_sectorPiece`), so Fubini
  (`Integrable.integral_prod_left`) gives the `p`-integrability. -/
theorem tBdiagFormInd_sectorPiece_additive {n : ℕ} {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin n) :
    (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2))
      = ∑ k ∈ Finset.range (n + 1),
          ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
              ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i
                  (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ)) i x‖ ^ 2) := by
  have hA : MeasurableSet (dlBox ℓ d u) := measurableSet_dlBox ℓ d u
  have hχ : ∀ z : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.chiB ℓ d u z ≠ 0 → z ∈ Submission.BoseGases.dlBox ℓ d u :=
    fun z hz => chiB_support_mem hℓ hd u z hz
  obtain ⟨hkern, hkern0⟩ :=
    integrable_tBamp_kernel_sectorPiece (ℓ := ℓ) (d := d) hℓ hd u i hΦ.continuous
  -- the box `L¹`-integrability of the squared amplitudes of the sector pieces
  have hXint : ∀ (k : ℕ) (p : EuclideanSpace ℝ (Fin 3)), IntegrableOn (fun x : X n =>
      ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (dlBox ℓ d u) i
          (sectorPiece (dlBox ℓ d u) k Φ)) i x‖ ^ 2)
      (abox n ℓ) :=
    fun k p => integrableOn_tBamp_sectorPiece_sq hℓ hd u hΦ.continuous i p k
  -- the box `L¹`-integrability of the squared amplitude of the state itself
  have hXint0 : ∀ p : EuclideanSpace ℝ (Fin 3), IntegrableOn (fun x : X n =>
      ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (dlBox ℓ d u) i Φ) i x‖ ^ 2)
      (abox n ℓ) := by
    intro p
    obtain ⟨B, hB0, hBb⟩ := exists_abs_bound_abox' (n := n) (ℓ := ℓ) hℓ hΦ.continuous
    have hχint_abs : Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
        |Submission.BoseGases.chiB ℓ d u z|) :=
      ((Work.SlotWord.continuous_chiB ℓ d u).integrable_of_hasCompactSupport
        (Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u)).abs
    exact Work.FibreKinPot.Trunc.integrableOn_tBamp_boxQInd_sq (L := ℓ) hℓ hA
      (dlBox_subset_acube ℓ d u) (volume_dlBox_lt_top hℓ d u) (boxMass_eq_measureReal ℓ d u)
      (Work.SlotWord.continuous_chiB ℓ d u).measurable hχint_abs
      (fun z hz => (chiB_support_mem hℓ hd u z hz).1) hΦ.continuous.measurable hB0 hBb i p
  -- the joint (`p`,`x`)-integrability of the `p`-diagonal energy of each sector piece
  have hprod : ∀ k : ℕ, Integrable (fun q : EuclideanSpace ℝ (Fin 3) × X n =>
      Submission.BoseGases.fsKinCoeff c ‖q.1‖ * ((ℓ ^ 3)⁻¹ *
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) q.1
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (dlBox ℓ d u) i
            (sectorPiece (dlBox ℓ d u) k Φ)) i q.2‖ ^ 2))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (X n)).restrict (abox n ℓ))) :=
    fun k => integrable_prod_ampEnergy_sectorPiece hℓ hd u hΦ i k
  -- `p`-integrability of each sector summand (Fubini along `volume.prod (volume.restrict abox)`)
  have hPint : ∀ k : ℕ, Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in abox n ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (dlBox ℓ d u) i (sectorPiece (dlBox ℓ d u) k Φ)) i x‖ ^ 2)) := by
    intro k
    have h : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        ∫ x, Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((ℓ ^ 3)⁻¹ *
            ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (dlBox ℓ d u) i (sectorPiece (dlBox ℓ d u) k Φ)) i x‖ ^ 2)
        ∂((MeasureTheory.volume : MeasureTheory.Measure (X n)).restrict (abox n ℓ)))
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
      MeasureTheory.Integrable.integral_prod_left (hprod k)
    refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only []
    rw [integral_const_mul, integral_const_mul]
  -- the pointwise (in `p`) splitting of the box energy
  have hinner : ∀ p : EuclideanSpace ℝ (Fin 3),
      (∫ x in abox n ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (dlBox ℓ d u) i Φ) i x‖ ^ 2)
        = ∑ k ∈ Finset.range (n + 1),
            ∫ x in abox n ℓ,
              ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (dlBox ℓ d u) i (sectorPiece (dlBox ℓ d u) k Φ)) i x‖ ^ 2 := by
    intro p
    rw [show (∫ x in abox n ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (dlBox ℓ d u) i Φ) i x‖ ^ 2)
        = ∫ x in abox n ℓ,
            ∑ k ∈ Finset.range (n + 1),
              ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (dlBox ℓ d u) i (sectorPiece (dlBox ℓ d u) k Φ)) i x‖ ^ 2
      from integral_congr_ae (Filter.Eventually.of_forall (fun x =>
        sum_tBamp_normSq hA (Submission.BoseGases.chiB ℓ d u) hχ i p
          (fun k x => hkern k p x) (fun x => hkern0 p x) x))]
    rw [integral_finsetSum _ (fun k _ => hXint k p)]
  calc (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in abox n ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (dlBox ℓ d u) i Φ) i x‖ ^ 2))
      = ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((ℓ ^ 3)⁻¹ * ∑ k ∈ Finset.range (n + 1),
            ∫ x in abox n ℓ,
              ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (dlBox ℓ d u) i (sectorPiece (dlBox ℓ d u) k Φ)) i x‖ ^ 2) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        simp only []
        rw [hinner p]
    _ = ∫ p : EuclideanSpace ℝ (Fin 3), ∑ k ∈ Finset.range (n + 1),
          Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ((ℓ ^ 3)⁻¹ * ∫ x in abox n ℓ,
              ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (dlBox ℓ d u) i (sectorPiece (dlBox ℓ d u) k Φ)) i x‖ ^ 2) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        simp only []
        rw [Finset.mul_sum, Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (n + 1),
          ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ((ℓ ^ 3)⁻¹ * ∫ x in abox n ℓ,
              ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (dlBox ℓ d u) i (sectorPiece (dlBox ℓ d u) k Φ)) i x‖ ^ 2) :=
        integral_finsetSum _ (fun k _ => hPint k)

/-! ## 2. The kinetic half of the word -/

/-- **The localised per-box kinetic word is sector-additive** at the sliding box, under the
regime hypotheses `0 < ℓ`, `0 < d` and a smooth state.  This is
`Work.FockBridge.tBwordInd_eq_sum_sectorPiece` with the two per-slot additivities supplied by
`cnPlusBoxInd_eq_sum_sectorPiece_sliding` and `tBdiagFormInd_sectorPiece_additive`. -/
theorem tBwordBInd_eq_sum_sectorPiece {n : ℕ} {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {Φ : X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    Work.UBBInputs8.tBwordBInd n ℓ d ε c u Φ
      = ∑ k ∈ Finset.range (n + 1),
          Work.UBBInputs8.tBwordBInd n ℓ d ε c u
            (sectorPiece (dlBox ℓ d u) k Φ) := by
  refine Work.FockBridge.tBwordInd_eq_sum_sectorPiece
    (A := dlBox ℓ d u) (volA := boxMass ℓ d u) (a := ℓ) (s := ℓ * d)
    (ε := ε) (c := c) (χ := chiB ℓ d u)
    (fun i => cnPlusBoxInd_eq_sum_sectorPiece_sliding hℓ hd u hΦ.continuous i)
    (fun i => tBdiagFormInd_sectorPiece_additive hℓ hd u hΦ i)

/-! ## 3. The potential half of the word -/

/-- **The localised potential word is sector-additive** at the sliding box, under the standing
hypotheses of the paper and the regime.  This is `Work.FockBridge.qLHSword_eq_sum_sectorPiece`
with the integrability side condition discharged by
`integrableOn_sectorPiece_sq_qLHSden_regime`. -/
theorem qLHSwordB_eq_sum_sectorPiece_regime {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {M : ℕ} (hM : 1 ≤ M) {ℓ d μ R0 : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hv1 : MeasureTheory.MemLp v 1) (hR0 : 0 < R0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (hdR : R0 ≤ ℓ * d / 16) (hdRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : X n → ℝ} (hΦc : Continuous Φ) :
    qLHSwordB h M ℓ d μ u Φ
      = ∑ k ∈ Finset.range (n + 1),
          qLHSwordB h M ℓ d μ u (sectorPiece (dlBox ℓ d u) k Φ) := by
  refine Work.FockBridge.qLHSword_eq_sum_sectorPiece
    (B := dlBox ℓ d u) (w := wSmallPair M ℓ d u v) (w1 := wSmall1Pair h M ℓ d u)
    (fun k _ => integrableOn_sectorPiece_sq_qLHSden_regime hM hℓ hd hv1 hR0 hv_supp hdR hdRχ
      u hΦc k)

/-! ## 4. The regime threshold -/

/-- The diluteness threshold of `regime_sideAt_ge`, downgraded to `Adm`. -/
theorem exists_adm_regime {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hav : 0 < _root_.BoseGases.a v) {R : ℝ} (hR : 0 < R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
      R ≤ sideAt μ (_root_.BoseGases.a v) * (paramsAt μ (_root_.BoseGases.a v)).d / 16 ∧
      R ≤ sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 := by
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := regime_sideAt_ge hav hR
  exact ⟨ε₀, hε₀pos, fun μ hAdm => hε₀ μ hAdm.1 hAdm.2.1⟩

/-! ## 5. The main theorem -/

theorem sbWordSectorAdditiveAdm {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ Work.BoseFixB1.SbWordSectorAdditive v h ε₀ := by
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := exists_adm_regime hav hR
  refine ⟨ε₀, hε₀pos, fun μ hAdm n Φ u => ?_⟩
  have hℓ : 0 < PBℓ v μ := adm_ell_pos hAdm
  have hd : 0 < PBd v μ := adm_d_pos hAdm
  have hM : 1 ≤ PBM v μ := by
    change 1 ≤ Work.BoseBox.mValue
    decide
  obtain ⟨hreg1, hreg2⟩ := hε₀ μ hAdm
  have hkin : sbKin (v := v) μ (PBM v μ) u (Φ : X n → ℝ)
      = ∑ k ∈ Finset.range (n + 1),
          Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
            (sbCut μ (_root_.BoseGases.a v)) u
            (sectorPiece (PBB v μ u) k (Φ : X n → ℝ)) := by
    rw [show sbKin (v := v) μ (PBM v μ) u (Φ : X n → ℝ)
        = Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
            (sbCut μ (_root_.BoseGases.a v)) u (Φ : X n → ℝ) from rfl]
    exact tBwordBInd_eq_sum_sectorPiece hℓ hd u Φ.contDiff
  have hpot : sbPot h μ u (Φ : X n → ℝ)
      = ∑ k ∈ Finset.range (n + 1),
          qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
            (sectorPiece (PBB v μ u) k (Φ : X n → ℝ)) := by
    rw [show sbPot h μ u (Φ : X n → ℝ)
        = qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u (Φ : X n → ℝ) from rfl]
    exact qLHSwordB_eq_sum_sectorPiece_regime hM hℓ hd hv1 hR hv_supp hreg1 hreg2 u
      Φ.contDiff.continuous
  rw [show sbWord h μ u (Φ : X n → ℝ)
      = sbKin (v := v) μ (PBM v μ) u (Φ : X n → ℝ) + sbPot h μ u (Φ : X n → ℝ) from rfl,
    hkin, hpot, Finset.sum_add_distrib]

end Work.BoseFixB1
