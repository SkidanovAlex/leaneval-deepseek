import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.sharpTotalCore_of_inBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.slotDemandAux` — the shared helpers of `slotDemand_le_word`

The per-slot-set demand inequality `Work.BoseFixB1B.slotDemand_le_word` needs three kinds of
bookkeeping, isolated here so that the (independently delegated) analytic pieces
(integrability of the demand at the sharp fibre, and of the fibre word at the piece fibre) can
import them without a cycle.

* `integrableOn_slotPiece_sq_qLHSden` — **(P1)** the potential density of a slot piece is
  integrable on the analysis box in the dilute regime (`R ≤ ℓd/16`, `R ≤ ℓ·chiR0`).  This is
  `Work.BoseFixB1B.integrable_qLHSden_regime` (which gives the integrability of `qLHSden` itself)
  combined with the boundedness of `Φ` on the box: `(slotPiece)² ≤ ‖Φ‖²_∞`.
* `sharpBoxState_zero_count` — **(P2)** the sharp box state at `k = 0` is the state itself (the
  box condition is vacuously true).
* `fibreWord_zero_count` — **(P3)** the sliding word of a state of `0` particles vanishes (all its
  sums are empty).
* `qLHSwordB_slotPiece_empty_eq_zero` — **(P5)** the potential word of the empty slot piece
  `1_{∀i, x i ∉ B}·Φ` vanishes: its density is supported on the configurations all of whose
  coordinates lie outside the sliding box, where `qLHSden` vanishes identically.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge Work.PerSector Work.SlotWord

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## (P1) The potential density of a slot piece is integrable on the box -/

/-- **(P1)** In the dilute regime the potential density of a slot piece is integrable on the
analysis box: `qLHSden` is integrable there (`Work.BoseFixB1B.integrable_qLHSden_regime`) and the
square of the slot piece is bounded by `‖Φ‖_∞²` on the box. -/
theorem integrableOn_slotPiece_sq_qLHSden {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ε₀ μ : ℝ}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (hε₀ : 0 < ε₀) (hμ : Work.BoseBoxFix.Adm v ε₀ μ)
    (hR16 : R ≤ PBℓ v μ * PBd v μ / 16) (hRχ : R ≤ PBℓ v μ * Submission.BoseGases.chiR0)
    {u : E3} (hu : u ∈ Work.SmallBoxSliding.goodSet (PBℓ v μ) (PBd v μ) μ)
    {N : ℕ} (Φ : Work.BoseKinLoc.BoxState N (PBℓ v μ)) (S : Finset (Fin N)) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X N → ℝ) x) ^ 2
          * Submission.BoseGases.qLHSden N (PBℓ v μ) μ
              (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
              (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) x)
      (Submission.BoseGases.abox N (PBℓ v μ)) := by
  classical
  have hL : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hμ
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hμ
  have hM1 : 1 ≤ PBM v μ := Work.BoseFixB1B.one_le_PBM v μ
  -- `qLHSden` itself is integrable
  have hq : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N =>
        Submission.BoseGases.qLHSden N (PBℓ v μ) μ
          (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
          (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) x)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N (PBℓ v μ))) :=
    Work.BoseFixB1B.integrable_qLHSden_regime (h := h) (M := PBM v μ) (ℓ := PBℓ v μ)
      (d := PBd v μ) (μ := μ) (R0 := R) hM1 hL hd hv1 hR hv_supp hR16 hRχ u
  -- the sup bound of `Φ` on the box
  obtain ⟨C₀, hC₀⟩ :=
    (Submission.BoseGases.abox_compact N hL).exists_bound_of_continuousOn
      (f := fun x : Submission.BoseGases.X N => (Φ : Submission.BoseGases.X N → ℝ) x)
      Φ.contDiff.continuous.continuousOn
  set Cb : ℝ := max C₀ 0 with hCbdef
  have hCb : ∀ x ∈ Submission.BoseGases.abox N (PBℓ v μ),
      ‖(Φ : Submission.BoseGases.X N → ℝ) x‖ ≤ Cb :=
    fun x hx => le_trans (hC₀ x hx) (le_max_left _ _)
  have hCb0 : 0 ≤ Cb := le_max_right _ _
  -- the a.e.-strong-measurability of the density
  have hBmeas : MeasurableSet (PBB v μ u) :=
    Work.SmallBoxSliding.measurableSet_dlBox (PBℓ v μ) (PBd v μ) u
  have hpiece : Measurable (Work.PerSector.slotPiece (PBB v μ u) S
      (Φ : Submission.BoseGases.X N → ℝ)) :=
    Work.PerSector.slotPiece_measurable (PBB v μ u) hBmeas S Φ.contDiff.continuous.measurable
  have hden := Work.BoseFixB1B.qLHSden_aeStronglyMeasurable (h := h) (c := 0) (C := 0)
      hv hv1 hvrad hR hv_supp hav hε₀ hμ hu (n := N)
  have haesm : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N =>
        (Work.PerSector.slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X N → ℝ) x) ^ 2
          * Submission.BoseGases.qLHSden N (PBℓ v μ) μ
              (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
              (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) x)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N (PBℓ v μ))) :=
    ((hpiece.pow_const 2).aestronglyMeasurable).mul hden
  -- the pointwise bound
  refine (hq.abs.const_mul (Cb ^ 2)).mono' haesm ?_
  rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N (PBℓ v μ))]
  refine Filter.Eventually.of_forall (fun x hx => ?_)
  have hxΦ : ‖(Φ : Submission.BoseGases.X N → ℝ) x‖ ≤ Cb := hCb x hx
  have hsq : ((Φ : Submission.BoseGases.X N → ℝ) x) ^ 2 ≤ Cb ^ 2 := by
    rw [← sq_abs]
    rw [sq, sq]
    exact mul_self_le_mul_self (abs_nonneg _) hxΦ
  have hpiece_sq : (Work.PerSector.slotPiece (PBB v μ u) S
      (Φ : Submission.BoseGases.X N → ℝ) x) ^ 2 ≤ Cb ^ 2 := by
    by_cases hxs : x ∈ Work.PerSector.slotSet (PBB v μ u) S
    · rw [Work.PerSector.slotPiece, Set.indicator_of_mem hxs]
      exact hsq
    · rw [Work.PerSector.slotPiece, Set.indicator_of_notMem hxs]
      rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      exact sq_nonneg Cb
  have hkey : ‖(Work.PerSector.slotPiece (PBB v μ u) S
        (Φ : Submission.BoseGases.X N → ℝ) x) ^ 2
        * Submission.BoseGases.qLHSden N (PBℓ v μ) μ
            (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
            (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) x‖
      = (Work.PerSector.slotPiece (PBB v μ u) S
          (Φ : Submission.BoseGases.X N → ℝ) x) ^ 2
        * |Submission.BoseGases.qLHSden N (PBℓ v μ) μ
            (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
            (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) x| := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  rw [hkey]
  calc (Work.PerSector.slotPiece (PBB v μ u) S
          (Φ : Submission.BoseGases.X N → ℝ) x) ^ 2
        * |Submission.BoseGases.qLHSden N (PBℓ v μ) μ
            (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
            (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) x|
      ≤ Cb ^ 2 * |Submission.BoseGases.qLHSden N (PBℓ v μ) μ
            (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
            (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) x| :=
        mul_le_mul_of_nonneg_right hpiece_sq (abs_nonneg _)

/-! ## (P2) The sharp box state at `k = 0` is the state itself -/

/-- **(P2)** At `k = 0` the box condition `∀ i : Fin 0, x i ∈ B` is vacuous, so the sharp box
state is the state.  (Stated for a general `k` with an explicit `hk : k = 0` so that it applies at
types such as `X (∅ : Finset (Fin N)).card`, where `rw` cannot see the definitional equality with
`X 0`.) -/
theorem sharpBoxState_zero_count (B : Set E3) {k : ℕ} (hk : k = 0)
    (ψ : Submission.BoseGases.X k → ℝ) :
    sharpBoxState B ψ = ψ := by
  subst hk
  funext x
  rw [sharpState_apply, if_pos (fun i => i.elim0)]

/-! ## (P3) The sliding word at `0` particles vanishes -/

/-- **(P3)** The sliding word of a `0`-particle state vanishes: every sum in `tBwordBInd` and in
`qLHSden` is empty.  (Stated for a general `k` with an explicit `hk : k = 0`, as in
`sharpBoxState_zero_count`.) -/
theorem fibreWord_zero_count {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (L d ε c μ : ℝ)
    (u : E3) {k : ℕ} (hk : k = 0) (Ψ : Submission.BoseGases.X k → ℝ) :
    Work.SlotWord.fibreWord h M k L d ε c μ u Ψ = 0 := by
  subst hk
  have h1 : Work.UBBInputs8.tBwordBInd 0 L d ε c u Ψ = 0 := by
    simp only [Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd,
      Work.UBBInputs8.cnPlusBoxInd, Work.UBBInputs8.tBwordKinInd,
      Work.UBBInputs8.tBdiagFormInd, Finset.univ_eq_empty, Finset.sum_empty, zero_mul,
      mul_zero, add_zero]
  have hpair : Submission.BoseGases.pairSet 0 = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr (fun p _ => ?_)
    exact Fin.elim0 p.1
  have h2 : Work.SmallBoxSliding.qLHSwordB h M L d μ u (N := 0) Ψ = 0 := by
    rw [Work.SmallBoxSliding.qLHSwordB]
    simp [Submission.BoseGases.qLHSword, hpair]
  rw [Work.SlotWord.fibreWord, h1, h2, add_zero]

/-! ## (P5) The potential word of the empty slot piece vanishes -/

/-- **(P5)** The potential word of the empty slot piece vanishes: the piece is supported on the
configurations all of whose coordinates lie outside the sliding box, and there `qLHSden` is
identically zero (both localised kernels are supported in the box in each variable). -/
theorem qLHSwordB_slotPiece_empty_eq_zero {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {ε₀ μ : ℝ}
    (hμ : Work.BoseBoxFix.Adm v ε₀ μ) {N : ℕ}
    (Φ : Work.BoseKinLoc.BoxState N (PBℓ v μ)) (u : E3) :
    Work.SmallBoxSliding.qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
        (Work.PerSector.slotPiece (PBB v μ u) (∅ : Finset (Fin N))
          (Φ : Submission.BoseGases.X N → ℝ)) = 0 := by
  classical
  have hL : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hμ
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hμ
  have hM1 : 1 ≤ PBM v μ := Work.BoseFixB1B.one_le_PBM v μ
  have hsupp1 : ∀ x : E3, x ∉ PBB v μ u → ∀ y : E3,
      Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u x y = 0 :=
    fun x hx y => Work.SlotWord.wSmall1Pair_support_left hM1 hL hd u hx y
  have hsupp2 : ∀ x y : E3, (x ∉ PBB v μ u ∨ y ∉ PBB v μ u) →
      Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v x y = 0 := by
    intro x y hxy
    rcases hxy with hx | hy
    · exact Work.SlotWord.wSmallPair_support_left hM1 hL hd u v hx y
    · have h0 : Submission.BoseGases.chiSmallB (PBM v μ) (PBℓ v μ) (PBd v μ) u y = 0 := by
        by_contra hne
        exact hy (Work.SlotWord.chiSmallB_support_mem_dlBox hM1 hL hd hne)
      rw [Submission.BoseGases.wSmallPair, h0, mul_zero]
  rw [Work.SmallBoxSliding.qLHSwordB, Submission.BoseGases.qLHSword]
  change (∫ x in Submission.BoseGases.abox N (PBℓ v μ),
      (Work.PerSector.slotPiece (PBB v μ u) (∅ : Finset (Fin N))
          (Φ : Submission.BoseGases.X N → ℝ) x) ^ 2
        * Submission.BoseGases.qLHSden N (PBℓ v μ) μ
            (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
            (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) x) = 0
  have hzero : ∀ x : Submission.BoseGases.X N,
      (Work.PerSector.slotPiece (PBB v μ u) (∅ : Finset (Fin N))
          (Φ : Submission.BoseGases.X N → ℝ) x) ^ 2
        * Submission.BoseGases.qLHSden N (PBℓ v μ) μ
            (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
            (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) x = 0 := by
    intro x
    by_cases hx : x ∈ Work.PerSector.slotSet (PBB v μ u) (∅ : Finset (Fin N))
    · have hxout : ∀ i : Fin N, x i ∉ PBB v μ u := by
        intro i
        have h := (Work.PerSector.mem_slotSet_iff (PBB v μ u) (∅ : Finset (Fin N)) x).mp hx i
        exact fun hb => (Finset.notMem_empty i) (h.mp hb)
      have hden0 : Submission.BoseGases.qLHSden N (PBℓ v μ) μ
          (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
          (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) x = 0 := by
        rw [Submission.BoseGases.qLHSden]
        have hsum1 : (∑ i : Fin N,
            Submission.BoseGases.w1Fibre (PBℓ v μ)
              (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) (x i)) = 0 := by
          refine Finset.sum_eq_zero (fun i _ => ?_)
          rw [Submission.BoseGases.w1Fibre]
          have hf : (fun y : E3 =>
              Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u (x i) y) = 0 :=
            funext (fun y => hsupp1 (x i) (hxout i) y)
          rw [hf]
          simp
        have hsum2 : (∑ p ∈ Submission.BoseGases.pairSet N,
            Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v
              (x p.1) (x p.2)) = 0 := by
          refine Finset.sum_eq_zero (fun p _ => ?_)
          exact hsupp2 (x p.1) (x p.2) (Or.inl (hxout p.1))
        rw [hsum1, hsum2]
        ring
      rw [Work.PerSector.slotPiece, Set.indicator_of_mem hx, hden0, mul_zero]
    · rw [Work.PerSector.slotPiece, Set.indicator_of_notMem hx]
      simp
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hzero)]
  simp

end Work.BoseFixB1B
