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

/-! ## 8. The graph step -/

theorem sheetData_snoc_graph (m N : ℕ) (w' : Fin N → CellType) (κ' : Set (Fin (m + N) → ℝ))
    (hdata : SheetData m N w' κ')
    (f : (Fin (m + N) → ℝ) → ℝ) (hf : ContinuousOn f κ')
    (κ : Set (Fin (m + N + 1) → ℝ))
    (hκ : κ = {z : Fin (m + N + 1) → ℝ | Fin.init z ∈ κ' ∧
      z (Fin.last (m + N)) = f (Fin.init z)}) :
    SheetData m (N + 1) (Fin.snoc w' CellType.graph) κ := by
  obtain ⟨T', φ', hTne, hTopen, hφcont, hφ0, hproj, hrec, hsheet, hagree⟩ := hdata
  obtain ⟨hPM1, hPM2, hPM3, hPM4, hPM5⟩ := GR.PairMaps m N w'
  obtain ⟨_, hT2, hT3, _, _, _, hT7, hT8, _, _, _⟩ := GR.Transfer m N w'
  let T : Set (Fin (m + nBand (N + 1) (Fin.snoc w' CellType.graph)) → ℝ) :=
    {v | resG m N w' v ∈ T'}
  let φ : (Fin (m + nBand (N + 1) (Fin.snoc w' CellType.graph)) → ℝ) →
      (Fin (nGraph (N + 1) (Fin.snoc w' CellType.graph)) → ℝ) :=
    fun v => if v ∈ T then
      fun k => (Fin.snoc (α := fun _ => ℝ) (φ' (resG m N w' v))
        (f (sheetPtM (wordEquiv w') (resG m N w' v) (φ' (resG m N w' v)))))
        (Fin.cast (nGraph_snoc_graph N w') k)
      else 0
  have hφT : ∀ v ∈ T, φ v = fun k => (Fin.snoc (α := fun _ => ℝ) (φ' (resG m N w' v))
      (f (sheetPtM (wordEquiv w') (resG m N w' v) (φ' (resG m N w' v)))))
      (Fin.cast (nGraph_snoc_graph N w') k) := by
    intro v hv
    show (if v ∈ T then _ else (0 : Fin (nGraph (N + 1) (Fin.snoc w' CellType.graph)) → ℝ)) = _
    rw [ite_eq_left hv]
  have hφ0 : ∀ v ∉ T, φ v = 0 := by
    intro v hv
    show (if v ∈ T then _ else (0 : Fin (nGraph (N + 1) (Fin.snoc w' CellType.graph)) → ℝ)) = 0
    rw [ite_eq_right hv]
  have hres : Continuous (resG m N w') := by
    unfold resG
    exact continuous_pi fun i => continuous_apply _
  refine ⟨T, φ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨v', hv'⟩ := hTne
    exact ⟨liftG m N w' v', by
      show resG m N w' (liftG m N w' v') ∈ T'
      rw [hPM4 v']
      exact hv'⟩
  · show IsOpen (resG m N w' ⁻¹' T')
    exact hTopen.preimage hres
  · have hφ' : ContinuousOn (fun v => φ' (resG m N w' v)) T :=
      hφcont.comp hres.continuousOn fun v hv => hv
    have hsp : ContinuousOn
        (fun v => sheetPtM (wordEquiv w') (resG m N w' v) (φ' (resG m N w' v))) T :=
      (continuous_sheetPtM (wordEquiv w')).continuousOn.comp
        (hres.continuousOn.prodMk hφ') fun v hv => Set.mem_univ _
    have hf' : ContinuousOn
        (fun v => f (sheetPtM (wordEquiv w') (resG m N w' v) (φ' (resG m N w' v)))) T :=
      hf.comp hsp fun v hv => hsheet (resG m N w' v) hv
    have hsnoc : Continuous (fun p : (Fin (nGraph N w') → ℝ) × ℝ =>
        fun k : Fin (nGraph (N + 1) (Fin.snoc w' CellType.graph)) =>
          (Fin.snoc (α := fun _ => ℝ) p.1 p.2) (Fin.cast (nGraph_snoc_graph N w') k)) :=
      (continuous_reindex (Fin.cast (nGraph_snoc_graph N w'))).comp
        (continuous_finSnoc (n := nGraph N w'))
    have hmain : ContinuousOn (fun v => fun k =>
        (Fin.snoc (α := fun _ => ℝ) (φ' (resG m N w' v))
          (f (sheetPtM (wordEquiv w') (resG m N w' v) (φ' (resG m N w' v)))))
          (Fin.cast (nGraph_snoc_graph N w') k)) T :=
      hsnoc.continuousOn.comp (hφ'.prodMk hf') fun v hv => Set.mem_univ _
    exact hmain.congr fun v hv => hφT v hv
  · intro v hv
    exact hφ0 v hv
  · intro z hz
    have hz' : Fin.init z ∈ κ' := by
      rw [hκ] at hz; exact hz.1
    show resG m N w' (fun i => z (selBand m (Fin.snoc w' CellType.graph) i)) ∈ T'
    rw [proj_snoc_graph_lift w' z]
    exact hproj _ hz'
  · intro z hz
    have hzP : Fin.init z ∈ κ' ∧ z (Fin.last (m + N)) = f (Fin.init z) := by
      rw [hκ] at hz; exact hz
    rw [proj_snoc_graph_lift w' z, graphIdx_snoc_graph_lift w' z,
      hT8 (fun i => Fin.init z (selBand m w' i))
        (Fin.snoc (α := fun _ => ℝ) (fun k => Fin.init z (Fin.natAdd m (graphIdx w' k)))
          (z (Fin.last (m + N))))]
    simp only [Fin.init_snoc, Fin.snoc_last]
    rw [hrec _ hzP.1]
    exact Fin.snoc_init_self z
  · intro v hv
    have hv' : resG m N w' v ∈ T' := hv
    have hφv : φ v = liftUg N w' (Fin.snoc (α := fun _ => ℝ) (φ' (resG m N w' v))
        (f (sheetPtM (wordEquiv w') (resG m N w' v) (φ' (resG m N w' v))))) := by
      rw [hφT v hv]
      rfl
    have h4 : sheetPtM (wordEquiv (Fin.snoc w' CellType.graph)) v (φ v)
        = sheetPtM (wordEquiv (Fin.snoc w' CellType.graph)) (liftG m N w' (resG m N w' v))
            (liftUg N w' (Fin.snoc (α := fun _ => ℝ) (φ' (resG m N w' v))
              (f (sheetPtM (wordEquiv w') (resG m N w' v) (φ' (resG m N w' v)))))) := by
      rw [hφv]
      exact congrArg (fun x => sheetPtM (wordEquiv (Fin.snoc w' CellType.graph)) x
        (liftUg N w' (Fin.snoc (α := fun _ => ℝ) (φ' (resG m N w' v))
          (f (sheetPtM (wordEquiv w') (resG m N w' v) (φ' (resG m N w' v))))))) (hPM5 v).symm
    rw [h4, hT8 (resG m N w' v) (Fin.snoc (α := fun _ => ℝ) (φ' (resG m N w' v))
      (f (sheetPtM (wordEquiv w') (resG m N w' v) (φ' (resG m N w' v)))))]
    simp only [Fin.init_snoc, Fin.snoc_last]
    exact snoc_mem_graph_cell hκ (hsheet _ hv')
  · intro z hz
    have hzP : Fin.init z ∈ κ' ∧ z (Fin.last (m + N)) = f (Fin.init z) := by
      rw [hκ] at hz; exact hz
    have hTz : (fun i => z (selBand m (Fin.snoc w' CellType.graph) i)) ∈ T := by
      show resG m N w' _ ∈ T'
      rw [proj_snoc_graph_lift w' z]
      exact hproj _ hzP.1
    have h1 : φ (fun i => z (selBand m (Fin.snoc w' CellType.graph) i))
        = liftUg N w' (Fin.snoc (α := fun _ => ℝ)
            (fun k => Fin.init z (Fin.natAdd m (graphIdx w' k))) (z (Fin.last (m + N)))) := by
      rw [hφT (fun i => z (selBand m (Fin.snoc w' CellType.graph) i)) hTz,
        proj_snoc_graph_lift w' z, hPM4, hagree (Fin.init z) hzP.1,
        hrec (Fin.init z) hzP.1, ← hzP.2]
      rfl
    rw [h1]
    exact (graphIdx_snoc_graph_lift w' z).symm


end Work.WilCrux
