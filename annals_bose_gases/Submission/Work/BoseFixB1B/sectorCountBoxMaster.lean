import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.sectorCountBoxAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.sectorCountBoxMaster` — the master assembly

The target `Work.BoseFixB1B.RepairedPerSectorBoundG v h R` is assembled here from the four named
obligations of the sharp-extension route:

* `hcore` — the **sharp count core** at the count-core constants (the sharp extension
  `sharpCountCoreAt_of_countCoreAt`, from the convergence of the word along the smooth
  approximants, the mass convergence `tendsto_cutProd_mass`, the degenerate case
  `sharpState_eq_zero_of_mass_eq_zero` and the geometric inputs);
* `hpot` — the bare integrability of the potential density `qLHSden` at the sliding data
  (`integrable_qLHSden_sliding`);
* `hslot` — the **per-slot-set** fibre assembly (`sharpSlotBound`);
* `hadd` — the **sector additivity** of the sliding word (`sectorPieceWordAdditive`).

Everything else (the count-core constants, the `k = 0` sector, the mass identity, the summation
over the slot sets, the packaging) is proved here.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge Work.PerSector Work.SlotWord

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The `k = 0` threshold is nonpositive.** -/
theorem PBThresh_zero_nonpos {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {c C μ : ℝ} {u : E3}
    (hc : 0 < c) (hc14 : c ≤ 1 / 4) (hC : 0 ≤ C) (hμ : 0 < μ) (ha : 0 < a v)
    (hV : 0 ≤ PBW h μ u) (hΓ : 0 ≤ PBΓ v μ) :
    PBThresh h c C μ u 0 ≤ 0 := by
  have hdw : (0 : ℝ) / PBBV v μ u = 0 := zero_div _
  have hpsi : psiWeight 1 μ 0 = μ ^ 2 := by
    rw [psiWeight]
    field_simp
    ring
  have hcoef : c * psiWeight 1 μ (0 / PBBV v μ u) - (1 / 2 - c) * μ ^ 2 ≤ 0 := by
    rw [hdw, hpsi]
    nlinarith [sq_nonneg μ, mul_le_mul_of_nonneg_right hc14 (sq_nonneg μ)]
  have herr : 0 ≤ C * (μ ^ 2 * (a v) * PBΓ v μ * PBW h μ u + μ * (a v)) := by
    refine mul_nonneg hC (add_nonneg ?_ ?_)
    · exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) (le_of_lt ha)) hΓ) hV
    · exact mul_nonneg (le_of_lt hμ) (le_of_lt ha)
  rw [PBThresh]
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hcoef hV]

/-- **The master assembly.** -/
theorem repairedPerSectorBoundG_of_pieces {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hS : SectorCountSmallboxBox v h) (hav : 0 < a v)
    (hPBW : ∀ μ : ℝ, ∀ u : E3, 0 ≤ PBW h μ u)
    (hpot : ∀ ε₀ c C : ℝ, SectorCountBodyBox v h ε₀ c C →
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        R ≤ PBℓ v μ * PBd v μ / 16 → R ≤ PBℓ v μ * Submission.BoseGases.chiR0 →
        ∀ u ∈ goodSet (PBℓ v μ) (PBd v μ) μ, ∀ k : ℕ,
          MeasureTheory.IntegrableOn
            (fun x : X k => qLHSden k (PBℓ v μ) μ
              (wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
              (wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) x)
            (abox k (PBℓ v μ)))
    (hcore : ∀ ε₀ c C : ℝ, SectorCountBodyBox v h ε₀ c C →
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        R ≤ PBℓ v μ * PBd v μ / 16 → R ≤ PBℓ v μ * Submission.BoseGases.chiR0 →
        ∀ u ∈ goodSet (PBℓ v μ) (PBd v μ) μ, ∀ k : ℕ,
          SharpCountCoreAt h (PBM v μ) (PBℓ v μ) (PBd v μ) (PBeT v μ)
            (Work.BoseFixB1.sbCut μ (a v)) μ u k (PBThresh h c C μ u k))
    (hslot : ∀ ε₀ c C : ℝ, SectorCountBodyBox v h ε₀ c C →
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        R ≤ PBℓ v μ * PBd v μ / 16 → R ≤ PBℓ v μ * Submission.BoseGases.chiR0 →
        ∀ u ∈ goodSet (PBℓ v μ) (PBd v μ) μ, ∀ n : ℕ,
          ∀ Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ),
            ∀ S : Finset (Fin n), 0 < S.card →
              slotMass (PBℓ v μ) (PBB v μ u) S (Φ : X n → ℝ) * PBThresh h c C μ u S.card
                ≤ Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
                    (Work.BoseFixB1.sbCut μ (a v)) u (slotPiece (PBB v μ u) S (Φ : X n → ℝ))
                  + qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
                    (slotPiece (PBB v μ u) S (Φ : X n → ℝ)))
    (hreg : ∃ εr : ℝ, 0 < εr ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v εr μ →
        R ≤ PBℓ v μ * PBd v μ / 16 ∧ R ≤ PBℓ v μ * Submission.BoseGases.chiR0)
    (hadd : ∀ ε₀ c C : ℝ, SectorCountBodyBox v h ε₀ c C →
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        R ≤ PBℓ v μ * PBd v μ / 16 → R ≤ PBℓ v μ * Submission.BoseGases.chiR0 →
        ∀ u ∈ goodSet (PBℓ v μ) (PBd v μ) μ, ∀ n k : ℕ,
          ∀ Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ),
            Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
                (Work.BoseFixB1.sbCut μ (a v)) u
                (sectorPiece (dlBox (PBℓ v μ) (PBd v μ) u) k ((Φ : X n → ℝ)))
              + qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
                (sectorPiece (dlBox (PBℓ v μ) (PBd v μ) u) k ((Φ : X n → ℝ)))
            = ∑ S ∈ Finset.powersetCard k Finset.univ,
                (Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
                    (Work.BoseFixB1.sbCut μ (a v)) u
                    (slotPiece (dlBox (PBℓ v μ) (PBd v μ) u) S (Φ : X n → ℝ))
                  + qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
                    (slotPiece (dlBox (PBℓ v μ) (PBd v μ) u) S (Φ : X n → ℝ)))) :
    RepairedPerSectorBoundG v h R := by
  obtain ⟨ε₀, c, C, hε₀, hc0, hc14, hC0, hbody⟩ := hS
  obtain ⟨εr, hεr, hreg'⟩ := hreg
  -- shrink `ε₀` so that the dilute-regime facts hold: `min ε₀ εr`
  refine ⟨min ε₀ εr, c, C, lt_min hε₀ hεr, hc0, hc14, hC0, ?_⟩
  intro μ hμ n Φ u hu k hk
  classical
  have hμ₀ : Work.BoseBoxFix.Adm v ε₀ μ :=
    ⟨hμ.1, le_trans hμ.2.1 (min_le_left _ _), hμ.2.2⟩
  have hμr : Work.BoseBoxFix.Adm v εr μ :=
    ⟨hμ.1, le_trans hμ.2.1 (min_le_right _ _), hμ.2.2⟩
  obtain ⟨hR16, hRχ⟩ := hreg' μ hμr
  have hbody' : SectorCountBodyBox v h (min ε₀ εr) c C := fun ν hν =>
    hbody ν ⟨hν.1, le_trans hν.2.1 (min_le_left _ _), hν.2.2⟩
  have hdl : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hμ
  have hdd : 0 < PBd v μ := (Work.BoseBox.paramsAt_facts hμ.1 hμ.2.2).2.1
  rw [Finset.mem_range] at hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- the zero sector
    subst hk0
    refine sectorBound_zero (h := h) (M := PBM v μ) (L := PBℓ v μ) (d := PBd v μ)
      (ε := PBeT v μ) (c := Work.BoseFixB1.sbCut μ (a v)) (μ := μ) (u := u) hdl hdd ?_
    refine PBThresh_zero_nonpos (v := v) (h := h) (c := c) (C := C) (μ := μ) (u := u)
      hc0 hc14 hC0 hμ.1 hav (hPBW μ u) ?_
    rw [PBΓ, Work.FockBridge.dlGamma]
    refine mul_nonneg (pow_nonneg (le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hμ)) 3) ?_
    exact Real.rpow_nonneg (mul_nonneg hμ.1.le (pow_nonneg hav.le 3)) _
  · -- the nonzero sectors: the sum over the slot sets
    have hBmeas : MeasurableSet (dlBox (PBℓ v μ) (PBd v μ) u) :=
      measurableSet_dlBox (PBℓ v μ) (PBd v μ) u
    have hΦmeas : Measurable ((Φ : X n → ℝ)) := (Φ.contDiff.continuous).measurable
    -- the mass identity
    have hmass := Work.PerSector.sectorMass_eq_sum_slotMass (N := n) (PBℓ v μ) hBmeas hΦmeas
      (sectorMassENN_ne_top_of_continuous (N := n) (L := PBℓ v μ) Φ.contDiff.continuous) k
    -- the additivity
    have hadd' := hadd (min ε₀ εr) c C hbody' μ hμ hR16 hRχ u hu n k Φ
    have hmass' : sectorMass (PBℓ v μ) (dlBox (PBℓ v μ) (PBd v μ) u) ((Φ : X n → ℝ)) k
        = ∑ S ∈ Finset.powersetCard k Finset.univ,
            slotMass (PBℓ v μ) (PBB v μ u) S ((Φ : X n → ℝ)) := by
      simpa only [PBB] using hmass
    have hadd'' : Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
            (Work.BoseFixB1.sbCut μ (a v)) u
            (sectorPiece (PBB v μ u) k ((Φ : X n → ℝ)))
          + qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
            (sectorPiece (PBB v μ u) k ((Φ : X n → ℝ)))
        = ∑ S ∈ Finset.powersetCard k Finset.univ,
            (Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
                (Work.BoseFixB1.sbCut μ (a v)) u
                (slotPiece (PBB v μ u) S ((Φ : X n → ℝ)))
              + qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
                (slotPiece (PBB v μ u) S ((Φ : X n → ℝ)))) := by
      simpa only [PBB] using hadd'
    -- the per-slot bounds, at the threshold of the sector count
    refine sectorBound_of_slotBounds (h := h) (M := PBM v μ) (L := PBℓ v μ)
      (d := PBd v μ) (ε := PBeT v μ) (c := Work.BoseFixB1.sbCut μ (a v)) (μ := μ) (u := u)
      (n := n) (k := k) (T := PBThresh h c C μ u k) (Φ := (Φ : X n → ℝ))
      hmass' hadd'' ?_
    intro S hS
    have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    have h1 := hslot (min ε₀ εr) c C hbody' μ hμ hR16 hRχ u hu n Φ S (by omega)
    rw [← hcard]
    exact h1

end Work.BoseFixB1B
