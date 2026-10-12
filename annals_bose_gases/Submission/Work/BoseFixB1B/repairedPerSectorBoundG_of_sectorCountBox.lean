import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1B.exists_smoothCutoffB
import Submission.Work.BoseFixB1B.fibreWord_ae_eq_zero
import Submission.Work.BoseFixB1B.fibreWord_tendsto_cutProd
import Submission.Work.BoseFixB1B.integrableOn_slotPiece_sq_qLHSden_sliding
import Submission.Work.BoseFixB1B.isCutFamilyOfSmooth
import Submission.Work.BoseFixB1B.sectorCountBoxMaster
import Submission.Work.BoseFixB1B.sectorPieceWordAdditive
import Submission.Work.BoseFixB1B.sharpCoreAtOfBody
import Submission.Work.BoseFixB1B.sharpSlotBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.repairedPerSectorBoundG_of_sectorCountBox`

The repaired per-sector residual `RepairedPerSectorBoundG v h R` (FS's `thm:LHY-Box` sectorwise at
the sliding box `B(u)`, with the `F`-weight read at the box volume `boxMass`) from the count-indexed
core `SectorCountSmallboxBox v h` (FS's `thm:smallbox` at the count).

The assembly is `repairedPerSectorBoundG_of_pieces` (`sectorCountBoxMaster`), whose inputs are
supplied here:

* `hPBW` — `∬w_{1,B(u)} ≥ 0` (`PBW_nonneg`, pointwise nonnegativity of the kernel);
* `hreg` — the dilute-regime facts `R ≤ ℓd/16`, `R ≤ ℓ·chiR0` at the diluteness threshold
  (`Work.BoseFixB1.regime_sideAt_ge`);
* `hpot` — the `abox`-integrability of `qLHSden` at the sliding kernels, with the regime;
* `hcore` — the sharp count core at the count-core constants: the sharp extension
  (`sharpCountCoreAt_of_bodyBox`) from the count core (`countCoreAt_of_bodyBox`), the smooth cutoff
  family, the word convergence, the mass convergence (`tendsto_cutProd_mass`) and the degenerate
  case (`fibreWord_ae_eq_zero`);
* `hslot`, `hadd` — the per-slot fibre assembly and the slot additivity (`sectorPieceWordAdditive`).
-/

namespace Work.BoseFixB1B

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge Work.PerSector Work.SlotWord

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary facts about the sliding parameters -/

/-- The positive side `ℓ = PBℓ v μ` at an admissible `μ`. -/
theorem pb_ell_pos {v : E3 → ℝ} {ε₀ μ : ℝ} (hμ : Work.BoseBoxFix.Adm v ε₀ μ) : 0 < PBℓ v μ :=
  Work.BoseFixB1.adm_ell_pos hμ

/-- The positive `d = PBd v μ` at an admissible `μ`. -/
theorem pb_d_pos {v : E3 → ℝ} {ε₀ μ : ℝ} (hμ : Work.BoseBoxFix.Adm v ε₀ μ) : 0 < PBd v μ :=
  (Work.BoseBox.paramsAt_facts hμ.1 hμ.2.2).2.1

/-- The dilute-regime facts at the sliding parameters, in the form consumed by the master
assembly: from `Work.BoseFixB1.regime_sideAt_ge` at the diluteness threshold `εr`. -/
theorem regime_facts {v : E3 → ℝ} {R : ℝ} (hav : 0 < _root_.BoseGases.a v) (hR : 0 < R) :
    ∃ εr : ℝ, 0 < εr ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v εr μ →
      R ≤ PBℓ v μ * PBd v μ / 16 ∧ R ≤ PBℓ v μ * Submission.BoseGases.chiR0 := by
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  exact ⟨εr, hεr, fun μ hμ => hreg μ hμ.1 hμ.2.1⟩

/-! ## The degenerate case of the sharp extension, locally

`Work.BoseFixB1B.sharpBoxState_ae_eq_zero_of_mass_zero` is re-proved here under names of its own:
the file declaring it also declares `abs_sharpBoxState_le`, which collides with the declaration of
the same name in the word-convergence chain, so the two modules cannot be imported together. -/

/-- The sharp in-box state `1_{B^k}·ψ` is dominated pointwise by `ψ`. -/
theorem abs_sharpBoxState_le_aux {k : ℕ} {B : Set (EuclideanSpace ℝ (Fin 3))}
    (ψ : Submission.BoseGases.X k → ℝ) (x : Submission.BoseGases.X k) :
    |sharpBoxState B ψ x| ≤ |ψ x| := by
  classical
  rw [sharpBoxState, Set.indicator_apply]
  split_ifs with h
  · rfl
  · simp

/-- `B^k ⊆ (Fin k → ℝ³)` is measurable for measurable `B`. -/
theorem measurableSet_slotBox_fin_aux {k : ℕ} {B : Set (EuclideanSpace ℝ (Fin 3))}
    (hB : MeasurableSet B) : MeasurableSet (Work.PerSector.slotBox (ι := Fin k) B) := by
  have hset : Work.PerSector.slotBox (ι := Fin k) B
      = ⋂ i : Fin k, (fun z : Submission.BoseGases.X k => z i) ⁻¹' B := by
    ext z; simp [Work.PerSector.slotBox]
  rw [hset]
  exact MeasurableSet.iInter (fun i => (measurable_pi_apply i) hB)

theorem measurable_sharpBoxState_aux {k : ℕ} {B : Set (EuclideanSpace ℝ (Fin 3))}
    (hB : MeasurableSet B) {ψ : Submission.BoseGases.X k → ℝ} (hψ : Measurable ψ) :
    Measurable (sharpBoxState B ψ) :=
  hψ.indicator (measurableSet_slotBox_fin_aux hB)

/-- The squared sharp state is integrable on the box (it is dominated by the continuous `ψ²`). -/
theorem integrable_sharpBoxState_sq_aux {k : ℕ} {L d : ℝ} (u : EuclideanSpace ℝ (Fin 3))
    {ψ : Submission.BoseGases.X k → ℝ} (hψ : Continuous ψ) :
    Integrable (fun x : Submission.BoseGases.X k =>
        (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ x) ^ 2)
      ((volume : Measure (Submission.BoseGases.X k)).restrict (Submission.BoseGases.abox k L)) := by
  have hB : MeasurableSet (Submission.BoseGases.dlBox L d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox L d u
  have hmeas : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X k =>
        (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ x) ^ 2)
      ((volume : Measure (Submission.BoseGases.X k)).restrict (Submission.BoseGases.abox k L)) :=
    ((measurable_sharpBoxState_aux hB hψ.measurable).pow_const 2).aestronglyMeasurable
  have hψ2 : Integrable (fun x : Submission.BoseGases.X k => (ψ x) ^ 2)
      ((volume : Measure (Submission.BoseGases.X k)).restrict (Submission.BoseGases.abox k L)) :=
    Work.UBBInputs9.B.integrableOn_abox_of_continuous' (N := k) (ℓ := L) (hψ.pow 2)
  refine hψ2.mono' hmeas ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_sq.mpr (abs_sharpBoxState_le_aux ψ x)

/-- **The degenerate case**: a vanishing sharp mass forces the sharp state to vanish a.e. -/
theorem sharpState_ae_zero_aux {k : ℕ} {L d : ℝ} (u : EuclideanSpace ℝ (Fin 3))
    {ψ : Submission.BoseGases.X k → ℝ} (hψ : Continuous ψ)
    (h0 : ∫ x in Submission.BoseGases.abox k L,
        (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ x) ^ 2 = 0) :
    ∀ᵐ x ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict
        (Submission.BoseGases.abox k L)),
      Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ x = 0 := by
  have hint := integrable_sharpBoxState_sq_aux (k := k) (L := L) (d := d) u (ψ := ψ) hψ
  have hne : 0 ≤ᵐ[((volume : Measure (Submission.BoseGases.X k)).restrict
      (Submission.BoseGases.abox k L))]
      (fun x => (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ x) ^ 2) :=
    Filter.Eventually.of_forall (fun x => sq_nonneg _)
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae hne hint).mp h0
  filter_upwards [hae] with x hx
  exact sq_eq_zero_iff.mp hx

/-! ## The sharp count core at the sliding data -/

/-- **The sharp count core at the count-core constants.**  The count core
(`countCoreAt_of_bodyBox`) at the fibre, extended from the smooth to the sharp class by
`sharpCountCoreAt_of_bodyBox` (`sharpCoreAtOfBody`), whose four inputs are supplied from the
geometric input, the two convergences and the two a.e.-vanishing lemmas. -/
theorem sharpCoreAt_PBThresh {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v)
    {ε₀ c C : ℝ} (hbody : SectorCountBodyBox v h ε₀ c C) {μ : ℝ}
    (hμ : Work.BoseBoxFix.Adm v ε₀ μ)
    (hR16 : R ≤ PBℓ v μ * PBd v μ / 16) (hRχ : R ≤ PBℓ v μ * Submission.BoseGases.chiR0)
    {u : E3} (hu : u ∈ goodSet (PBℓ v μ) (PBd v μ) μ) (k : ℕ) :
    SharpCountCoreAt h (PBM v μ) (PBℓ v μ) (PBd v μ) (PBeT v μ)
      (Work.BoseFixB1.sbCut μ (a v)) μ u k (PBThresh h c C μ u k) := by
  have hℓ : 0 < PBℓ v μ := pb_ell_pos hμ
  have hd : 0 < PBd v μ := pb_d_pos hμ
  have hpot : MeasureTheory.IntegrableOn
      (fun x : X k => qLHSden k (PBℓ v μ) μ
        (wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
        (wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) x) (abox k (PBℓ v μ)) := by
    exact integrable_qLHSden_regime (h := h) (M := PBM v μ) (ℓ := PBℓ v μ) (d := PBd v μ)
      (μ := μ) (R0 := R) (one_le_PBM v μ) hℓ hd hv1 hR hv_supp hR16 hRχ u
  refine sharpCountCoreAt_of_bodyBox (h := h) (M := PBM v μ) (L := PBℓ v μ) (d := PBd v μ)
    (ε := PBeT v μ) (c := Work.BoseFixB1.sbCut μ (a v)) (μ := μ) (u := u) (k := k)
    (T := PBThresh h c C μ u k) hℓ hd (countCoreAt_of_bodyBox hbody hμ hu k) ?_ ?_ ?_ ?_
  · -- the smooth cutoff family of the sliding box
    exact exists_isCutFamily_of_smoothCutoff (exists_smoothCutoffB hℓ hd u)
  · -- the word convergence along the approximants
    intro ψ hψcd K γ hcut Cb hCb hψb
    exact fibreWord_tendsto_cutProd h (PBM v μ) k (PBℓ v μ) (PBd v μ) (PBeT v μ)
      (Work.BoseFixB1.sbCut μ (a v)) μ u hℓ hd hcut hψcd hCb hψb hpot
  · -- the degenerate case: the sharp state vanishes a.e. on the box
    intro ψ hψc hm0
    exact sharpState_ae_zero_aux u hψc hm0
  · -- the degenerate case: the word of an a.e.-vanishing state vanishes
    intro Ψ h0
    exact fibreWord_ae_eq_zero h (PBM v μ) k (PBℓ v μ) (PBd v μ) (PBeT v μ)
      (Work.BoseFixB1.sbCut μ (a v)) μ u hℓ h0


/-! ## The target -/

theorem repairedPerSectorBoundG_of_sectorCountBox {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hS : Work.BoseFixB1B.SectorCountSmallboxBox v h) :
    Work.BoseFixB1B.RepairedPerSectorBoundG v h R := by
  classical
  refine Work.BoseFixB1B.repairedPerSectorBoundG_of_pieces (v := v) (h := h) (R := R)
    hS hav ?_ ?_ ?_ ?_ ?_ ?_
  · -- `hPBW`
    intro μ u
    exact PBW_nonneg h hv hvrad hR hv_supp μ u
  · -- `hpot` (at the regime, which the master supplies through the shrunken `ε₀`)
    intro ε₀ c C hbody μ hμ hR16 hRχ u hu k
    exact integrable_qLHSden_regime (h := h) (M := PBM v μ) (ℓ := PBℓ v μ) (d := PBd v μ)
      (μ := μ) (R0 := R) (one_le_PBM v μ) (pb_ell_pos hμ) (pb_d_pos hμ) hv1 hR hv_supp hR16 hRχ u
  · -- `hcore`
    intro ε₀ c C hbody μ hμ hR16 hRχ u hu k
    exact sharpCoreAt_PBThresh (h := h) (R := R) hv hv1 hvrad hR hv_supp hav hbody hμ hR16 hRχ hu k
  · -- `hslot`: the per-slot fibre assembly at the sharp core
    intro ε₀ c C hbody μ hμ hR16 hRχ u hu n Φ S hS'
    have hε₀ : 0 < ε₀ := lt_of_lt_of_le (mul_pos hμ.1 (pow_pos hav 3)) hμ.2.1
    refine sharpSlotBound h hv hv1 hvrad hR hv_supp hav hε₀ hμ hu Φ ?_ S hS'
    intro j
    exact sharpCoreAt_PBThresh (h := h) (R := R) hv hv1 hvrad hR hv_supp hav hbody hμ hR16 hRχ hu j
  · -- `hreg`
    exact regime_facts hav hR
  · -- `hadd`: the slot additivity of the word with the potential integrability
    intro ε₀ c C hbody μ hμ hR16 hRχ u hu n k Φ
    obtain ⟨Cb, hCb⟩ := (abox_compact n (pb_ell_pos hμ)).exists_bound_of_continuousOn
      Φ.contDiff.continuous.continuousOn
    set Cb' : ℝ := max Cb 0 with hCb'def
    have hCb'0 : 0 ≤ Cb' := le_max_right _ _
    have hb : ∀ x ∈ abox n (PBℓ v μ), |Φ x| ≤ Cb' := by
      intro x hx
      rw [← Real.norm_eq_abs]
      exact le_trans (hCb x hx) (le_max_left _ _)
    refine sectorPieceWordAdditive (h := h) (M := PBM v μ) (L := PBℓ v μ) (d := PBd v μ)
      (ε := PBeT v μ) (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) (μ := μ) (u := u)
      (n := n) (k := k) (Cb := Cb') (pb_ell_pos hμ) (pb_d_pos hμ) Φ.contDiff hCb'0 hb ?_
    intro S
    exact integrableOn_slotPiece_sq_qLHSden_sliding (h := h) (M := PBM v μ) (ℓ := PBℓ v μ)
      (d := PBd v μ) (μ := μ) (R0 := R) (one_le_PBM v μ) (pb_ell_pos hμ) (pb_d_pos hμ) hv1 hR
      hv_supp hR16 hRχ u Φ.contDiff.continuous hCb'0 hb S

end Work.BoseFixB1B
