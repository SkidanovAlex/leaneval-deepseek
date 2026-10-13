import Submission.Work.WilCrux.GR.Helpers
import Submission.Work.WilCrux.GR.OrderEmbIdx
import Submission.Work.WilCrux.GR.RankTransfer
import Submission.Work.WilCrux.GR.Transfer
import Submission.Work.WilCrux.GR.PairMaps
import Submission.Work.WilCrux.GR.BandRegion

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

/-! ## 9. The band step -/

theorem sheetData_snoc_band (m N : ℕ) (w' : Fin N → CellType) (κ' : Set (Fin (m + N) → ℝ))
    (hdata : SheetData m N w' κ')
    (a b : (Fin (m + N) → ℝ) → EReal) (ha : ContinuousOn a κ') (hb : ContinuousOn b κ')
    (hab : ∀ x ∈ κ', a x < b x)
    (κ : Set (Fin (m + N + 1) → ℝ))
    (hκ : κ = {z : Fin (m + N + 1) → ℝ | Fin.init z ∈ κ' ∧
        a (Fin.init z) < ((z (Fin.last (m + N)) : ℝ) : EReal) ∧
        ((z (Fin.last (m + N)) : ℝ) : EReal) < b (Fin.init z)}) :
    SheetData m (N + 1) (Fin.snoc w' CellType.band) κ := by
  obtain ⟨T', φ', hTne, hTopen, hφcont, hφ0, hproj, hrec, hsheet, hagree⟩ := hdata
  obtain ⟨hPM1, hPM2, hPM3, hPM4, hPM5⟩ := GR.PairMaps m N w'
  obtain ⟨_, _, _, _, _, hT6, _, _, hT9, hT10, hT11⟩ := GR.Transfer m N w'
  let a'' : (Fin (m + nBand N w') → ℝ) → EReal :=
    fun v' => a (sheetPtM (wordEquiv w') v' (φ' v'))
  let b'' : (Fin (m + nBand N w') → ℝ) → EReal :=
    fun v' => b (sheetPtM (wordEquiv w') v' (φ' v'))
  let T : Set (Fin (m + nBand (N + 1) (Fin.snoc w' CellType.band)) → ℝ) :=
    {v | resB m N w' v ∈ T' ∧ a'' (resB m N w' v) < ((lastB m N w' v : ℝ) : EReal) ∧
      ((lastB m N w' v : ℝ) : EReal) < b'' (resB m N w' v)}
  let φ : (Fin (m + nBand (N + 1) (Fin.snoc w' CellType.band)) → ℝ) →
      (Fin (nGraph (N + 1) (Fin.snoc w' CellType.band)) → ℝ) :=
    fun v => if v ∈ T then liftUb N w' (φ' (resB m N w' v)) else 0
  have hφT : ∀ v ∈ T, φ v = liftUb N w' (φ' (resB m N w' v)) := by
    intro v hv
    show (if v ∈ T then liftUb N w' (φ' (resB m N w' v)) else
      (0 : Fin (nGraph (N + 1) (Fin.snoc w' CellType.band)) → ℝ)) = _
    rw [ite_eq_left hv]
  have hφ0 : ∀ v ∉ T, φ v = 0 := by
    intro v hv
    show (if v ∈ T then liftUb N w' (φ' (resB m N w' v)) else
      (0 : Fin (nGraph (N + 1) (Fin.snoc w' CellType.band)) → ℝ)) = 0
    rw [ite_eq_right hv]
  have ha''eq : ∀ v', a'' v' = a (sheetPtM (wordEquiv w') v' (φ' v')) := fun v' => rfl
  have hb''eq : ∀ v', b'' v' = b (sheetPtM (wordEquiv w') v' (φ' v')) := fun v' => rfl
  have hresB : Continuous (resB m N w') := by
    unfold resB
    exact continuous_pi fun i => continuous_apply _
  have hlastB : Continuous (lastB m N w') := by
    unfold lastB
    exact continuous_apply _
  have hF : Continuous (fun v => (resB m N w' v, lastB m N w' v)) := hresB.prodMk hlastB
  have hsp : ContinuousOn (fun v' => sheetPtM (wordEquiv w') v' (φ' v')) T' :=
    (continuous_sheetPtM (wordEquiv w')).continuousOn.comp
      (continuousOn_id.prodMk hφcont) fun v hv => Set.mem_univ _
  have ha'' : ContinuousOn a'' T' := ha.comp hsp fun v hv => hsheet v hv
  have hb'' : ContinuousOn b'' T' := hb.comp hsp fun v hv => hsheet v hv
  have hreg := GR.BandRegion (m + nBand N w') hTopen ha'' hb''
  refine ⟨T, φ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨v', hv'⟩ := hTne
    obtain ⟨lam, hl1, hl2⟩ := EReal.lt_iff_exists_real_btwn.mp (hab _ (hsheet v' hv'))
    refine ⟨mkB m N w' (v', lam), ?_⟩
    show resB m N w' (mkB m N w' (v', lam)) ∈ T' ∧
      a'' (resB m N w' (mkB m N w' (v', lam))) <
        ((lastB m N w' (mkB m N w' (v', lam)) : ℝ) : EReal) ∧
      ((lastB m N w' (mkB m N w' (v', lam)) : ℝ) : EReal) <
        b'' (resB m N w' (mkB m N w' (v', lam)))
    rw [hPM1, hPM2]
    exact ⟨hv', hl1, hl2⟩
  · show IsOpen ((fun v => (resB m N w' v, lastB m N w' v)) ⁻¹'
      {vw : (Fin (m + nBand N w') → ℝ) × ℝ | vw.1 ∈ T' ∧
        a'' vw.1 < ((vw.2 : ℝ) : EReal) ∧ ((vw.2 : ℝ) : EReal) < b'' vw.1})
    exact hreg.preimage hF
  · have h1 : ContinuousOn (fun v => φ' (resB m N w' v)) T :=
      hφcont.comp hresB.continuousOn fun v hv => hv.1
    have h2 : ContinuousOn (fun v => liftUb N w' (φ' (resB m N w' v))) T :=
      (continuous_reindex (Fin.cast (nGraph_snoc_band N w'))).continuousOn.comp h1
        fun v hv => Set.mem_univ _
    exact h2.congr fun v hv => hφT v hv
  · intro v hv
    exact hφ0 v hv
  · intro z hz
    have hzP : Fin.init z ∈ κ' ∧ a (Fin.init z) < ((z (Fin.last (m + N)) : ℝ) : EReal) ∧
        ((z (Fin.last (m + N)) : ℝ) : EReal) < b (Fin.init z) := by
      rw [hκ] at hz; exact hz
    show resB m N w' (fun i => z (selBand m (Fin.snoc w' CellType.band) i)) ∈ T' ∧
      a'' (resB m N w' (fun i => z (selBand m (Fin.snoc w' CellType.band) i))) <
        ((lastB m N w' (fun i => z (selBand m (Fin.snoc w' CellType.band) i)) : ℝ) : EReal) ∧
      ((lastB m N w' (fun i => z (selBand m (Fin.snoc w' CellType.band) i)) : ℝ) : EReal) <
        b'' (resB m N w' (fun i => z (selBand m (Fin.snoc w' CellType.band) i)))
    rw [proj_snoc_band_res w' z, proj_snoc_band_last w' z]
    refine ⟨hproj _ hzP.1, ?_, ?_⟩
    · rw [ha''eq, hagree _ hzP.1, hrec _ hzP.1]
      exact hzP.2.1
    · rw [hb''eq, hagree _ hzP.1, hrec _ hzP.1]
      exact hzP.2.2
  · intro z hz
    have hzP : Fin.init z ∈ κ' ∧ a (Fin.init z) < ((z (Fin.last (m + N)) : ℝ) : EReal) ∧
        ((z (Fin.last (m + N)) : ℝ) : EReal) < b (Fin.init z) := by
      rw [hκ] at hz; exact hz
    rw [graphIdx_snoc_band_lift w' z,
      hT11 (fun i => z (selBand m (Fin.snoc w' CellType.band) i))
        (fun k => Fin.init z (Fin.natAdd m (graphIdx w' k))),
      proj_snoc_band_res w' z, proj_snoc_band_last w' z]
    rw [hrec _ hzP.1]
    exact Fin.snoc_init_self z
  · intro v hv
    have hv1 : resB m N w' v ∈ T' := hv.1
    rw [hφT v hv, hT11 v (φ' (resB m N w' v))]
    exact snoc_mem_band_cell hκ (hsheet _ hv1) hv.2.1 hv.2.2
  · intro z hz
    have hzP : Fin.init z ∈ κ' ∧ a (Fin.init z) < ((z (Fin.last (m + N)) : ℝ) : EReal) ∧
        ((z (Fin.last (m + N)) : ℝ) : EReal) < b (Fin.init z) := by
      rw [hκ] at hz; exact hz
    have hTz : (fun i => z (selBand m (Fin.snoc w' CellType.band) i)) ∈ T := by
      show resB m N w' _ ∈ T' ∧ a'' (resB m N w' _) <
          ((lastB m N w' _ : ℝ) : EReal) ∧ ((lastB m N w' _ : ℝ) : EReal) < b'' (resB m N w' _)
      rw [proj_snoc_band_res w' z, proj_snoc_band_last w' z]
      refine ⟨hproj _ hzP.1, ?_, ?_⟩
      · rw [ha''eq, hagree _ hzP.1, hrec _ hzP.1]
        exact hzP.2.1
      · rw [hb''eq, hagree _ hzP.1, hrec _ hzP.1]
        exact hzP.2.2
    rw [hφT _ hTz, proj_snoc_band_res w' z, hagree _ hzP.1]
    exact (graphIdx_snoc_band_lift w' z).symm


end Work.WilCrux
