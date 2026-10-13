import Mathlib
import Submission.Work.WilCrux.SheetDefs
import Submission.Work.WilCrux.GR.Defs
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

/-! ## 1. Fin cast helpers -/

theorem fincast_cast_symm {n m : ℕ} (h : n = m) (x : Fin m) :
    Fin.cast h (Fin.cast h.symm x) = x := by
  subst h; simp

theorem fincast_symm_cast {n m : ℕ} (h : n = m) (x : Fin n) :
    Fin.cast h.symm (Fin.cast h x) = x := by
  subst h; simp

/-! ## 2. Continuity helpers -/

theorem continuous_reindex {a b : ℕ} (φ : Fin a → Fin b) :
    Continuous (fun g : Fin b → ℝ => fun i : Fin a => g (φ i)) :=
  continuous_pi fun i => continuous_apply (φ i)

theorem continuous_finSnoc {n : ℕ} :
    Continuous (fun p : (Fin n → ℝ) × ℝ => Fin.snoc (α := fun _ => ℝ) p.1 p.2) := by
  have h1 : Continuous (fun p : (Fin n → ℝ) × ℝ => (p.1, fun _ : Fin 1 => p.2)) :=
    continuous_fst.prodMk (continuous_pi fun _ => continuous_snd)
  have h3 : Continuous (fun p : (Fin n → ℝ) × ℝ => Fin.append p.1 (fun _ : Fin 1 => p.2)) :=
    (Fin.continuous_append n 1).comp h1
  exact h3.congr fun p => by rw [Fin.append_right_eq_snoc]

/-! ## 3. The index enumerations are inverse to the ranks -/

theorem bandIdx_injective {N : ℕ} (w : Fin N → CellType) : Function.Injective (bandIdx w) :=
  fun _ _ h => ((Finset.univ.filter (fun i : Fin N => bandBit (w i) = 1)).orderEmbOfFin
    (by rw [nBand_eq_card])).injective h

theorem graphIdx_injective {N : ℕ} (w : Fin N → CellType) : Function.Injective (graphIdx w) :=
  fun _ _ h => ((Finset.univ.filter (fun i : Fin N => graphBit (w i) = 1)).orderEmbOfFin
    (by rw [nGraph_eq_card])).injective h

theorem bandIdx_bandRank {N : ℕ} (w : Fin N → CellType) {j : Fin N} (hj : bandBit (w j) = 1) :
    bandIdx w ⟨bandRank w j, bandRank_lt_nBand w hj⟩ = j := by
  have hmem : j ∈ Finset.univ.filter (fun i : Fin N => bandBit (w i) = 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  have hiff := GR.OrderEmbIdx (Finset.univ.filter (fun i : Fin N => bandBit (w i) = 1))
    (h := by rw [nBand_eq_card]) ⟨bandRank w j, bandRank_lt_nBand w hj⟩ hmem
  have hmain : (Finset.univ.filter (fun i : Fin N => bandBit (w i) = 1)).orderEmbOfFin
      (by rw [nBand_eq_card]) ⟨bandRank w j, bandRank_lt_nBand w hj⟩ = bandIdx w
        ⟨bandRank w j, bandRank_lt_nBand w hj⟩ := rfl
  rw [hmain] at hiff
  refine hiff.mpr ?_
  show bandRank w j = ((Finset.univ.filter (fun i : Fin N => bandBit (w i) = 1)).filter
    (fun x => x < j)).card
  simp [bandRank, Finset.filter_comm, Finset.filter_filter, and_comm]

theorem graphIdx_graphRank {N : ℕ} (w : Fin N → CellType) {j : Fin N} (hj : graphBit (w j) = 1) :
    graphIdx w ⟨graphRank w j, graphRank_lt_nGraph w hj⟩ = j := by
  have hmem : j ∈ Finset.univ.filter (fun i : Fin N => graphBit (w i) = 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  have hiff := GR.OrderEmbIdx (Finset.univ.filter (fun i : Fin N => graphBit (w i) = 1))
    (h := by rw [nGraph_eq_card]) ⟨graphRank w j, graphRank_lt_nGraph w hj⟩ hmem
  have hmain : (Finset.univ.filter (fun i : Fin N => graphBit (w i) = 1)).orderEmbOfFin
      (by rw [nGraph_eq_card]) ⟨graphRank w j, graphRank_lt_nGraph w hj⟩ = graphIdx w
        ⟨graphRank w j, graphRank_lt_nGraph w hj⟩ := rfl
  rw [hmain] at hiff
  refine hiff.mpr ?_
  show graphRank w j = ((Finset.univ.filter (fun i : Fin N => graphBit (w i) = 1)).filter
    (fun x => x < j)).card
  simp [graphRank, Finset.filter_comm, Finset.filter_filter, and_comm]

/-! ## 4. The projection identity of the sheet parametrisation -/

theorem proj_sheetPtM {m N : ℕ} (w : Fin N → CellType) (v : Fin (m + nBand N w) → ℝ)
    (u : Fin (nGraph N w) → ℝ) :
    (fun i => sheetPtM (wordEquiv w) v u (selBand m w i)) = v := by
  funext i
  refine Fin.addCases (m := m) (n := nBand N w)
    (motive := fun i => sheetPtM (wordEquiv w) v u (selBand m w i) = v i) ?_ ?_ i
  · intro i'
    rw [selBand_castAdd, sheetPtM_castAdd]
  · intro k
    rw [selBand_natAdd, sheetPt_wordEquiv_band w v u (bandIdx w k) (bandIdx_band w k)]
    have hk : (⟨bandRank w (bandIdx w k), bandRank_lt_nBand w (bandIdx_band w k)⟩ :
        Fin (nBand N w)) = k :=
      bandIdx_injective w (bandIdx_bandRank w (bandIdx_band w k))
    rw [hk]

/-! ## 5. Transfer lemmas in the "lift" form -/

theorem proj_snoc_graph_lift {m N : ℕ} (w' : Fin N → CellType) (z : Fin (m + N + 1) → ℝ) :
    (fun i => z (selBand m (Fin.snoc w' CellType.graph) i)) =
      liftG m N w' (fun i => Fin.init z (selBand m w' i)) := by
  obtain ⟨_, _, _, _, _, _, hT7, _, _, _, _⟩ := GR.Transfer m N w'
  funext j
  have hstep : z (selBand m (Fin.snoc w' CellType.graph) j)
      = z (selBand m (Fin.snoc w' CellType.graph)
          (Fin.cast (congrArg (Nat.add m) (nBand_snoc_graph N w').symm)
            (Fin.cast (congrArg (Nat.add m) (nBand_snoc_graph N w')) j))) :=
    congrArg (fun x => z (selBand m (Fin.snoc w' CellType.graph) x))
      (fincast_symm_cast (congrArg (Nat.add m) (nBand_snoc_graph N w')) j).symm
  rw [hstep, hT7 z (Fin.cast (congrArg (Nat.add m) (nBand_snoc_graph N w')) j)]
  rfl

theorem graphIdx_snoc_graph_lift {m N : ℕ} (w' : Fin N → CellType)
    (z : Fin (m + N + 1) → ℝ) :
    (fun k => z (Fin.natAdd m (graphIdx (Fin.snoc w' CellType.graph) k))) =
      liftUg N w' (Fin.snoc (α := fun _ => ℝ)
        (fun k => Fin.init z (Fin.natAdd m (graphIdx w' k))) (z (Fin.last (m + N)))) := by
  obtain ⟨_, hT2, hT3, _, _, _, _, _, _, _, _⟩ := GR.Transfer m N w'
  have key : ∀ k₀ : Fin (nGraph N w' + 1),
      z (Fin.natAdd m (graphIdx (Fin.snoc w' CellType.graph)
          (Fin.cast (nGraph_snoc_graph N w').symm k₀))) =
        (Fin.snoc (α := fun _ => ℝ) (fun k => Fin.init z (Fin.natAdd m (graphIdx w' k)))
          (z (Fin.last (m + N)))) k₀ := by
    intro k₀
    refine Fin.lastCases ?_ ?_ k₀
    · rw [hT3, Fin.snoc_last]
      rfl
    · intro k₁
      rw [hT2 k₁, Fin.natAdd_castSucc, Fin.snoc_castSucc]
      rfl
  funext k
  have hstep : z (Fin.natAdd m (graphIdx (Fin.snoc w' CellType.graph) k))
      = z (Fin.natAdd m (graphIdx (Fin.snoc w' CellType.graph)
          (Fin.cast (nGraph_snoc_graph N w').symm
            (Fin.cast (nGraph_snoc_graph N w') k)))) :=
    congrArg (fun x => z (Fin.natAdd m (graphIdx (Fin.snoc w' CellType.graph) x)))
      (fincast_symm_cast (nGraph_snoc_graph N w') k).symm
  rw [hstep, key]
  rfl

theorem proj_snoc_band_res {m N : ℕ} (w' : Fin N → CellType) (z : Fin (m + N + 1) → ℝ) :
    resB m N w' (fun i => z (selBand m (Fin.snoc w' CellType.band) i)) =
      fun i => Fin.init z (selBand m w' i) := by
  obtain ⟨_, _, _, _, _, _, _, _, hT9, _, _⟩ := GR.Transfer m N w'
  funext i
  exact hT9 z i

theorem proj_snoc_band_last {m N : ℕ} (w' : Fin N → CellType) (z : Fin (m + N + 1) → ℝ) :
    lastB m N w' (fun i => z (selBand m (Fin.snoc w' CellType.band) i)) =
      z (Fin.last (m + N)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hT10, _⟩ := GR.Transfer m N w'
  exact hT10 z

theorem graphIdx_snoc_band_lift {m N : ℕ} (w' : Fin N → CellType) (z : Fin (m + N + 1) → ℝ) :
    (fun k => z (Fin.natAdd m (graphIdx (Fin.snoc w' CellType.band) k))) =
      liftUb N w' (fun k => Fin.init z (Fin.natAdd m (graphIdx w' k))) := by
  obtain ⟨_, _, _, _, _, hT6, _, _, _, _, _⟩ := GR.Transfer m N w'
  have key : ∀ k₀ : Fin (nGraph N w'),
      z (Fin.natAdd m (graphIdx (Fin.snoc w' CellType.band)
        (Fin.cast (nGraph_snoc_band N w').symm k₀))) =
        Fin.init z (Fin.natAdd m (graphIdx w' k₀)) := by
    intro k₀
    rw [hT6 k₀, Fin.natAdd_castSucc]
    rfl
  funext k
  have hstep : z (Fin.natAdd m (graphIdx (Fin.snoc w' CellType.band) k))
      = z (Fin.natAdd m (graphIdx (Fin.snoc w' CellType.band)
          (Fin.cast (nGraph_snoc_band N w').symm
            (Fin.cast (nGraph_snoc_band N w') k)))) :=
    congrArg (fun x => z (Fin.natAdd m (graphIdx (Fin.snoc w' CellType.band) x)))
      (fincast_symm_cast (nGraph_snoc_band N w') k).symm
  rw [hstep, key (Fin.cast (nGraph_snoc_band N w') k)]
  rfl

/-! ## 5b. Membership in a one-level cell -/

theorem snoc_mem_graph_cell {m N : ℕ} {κ' : Set (Fin (m + N) → ℝ)}
    {f : (Fin (m + N) → ℝ) → ℝ} {κ : Set (Fin (m + N + 1) → ℝ)}
    (hκ : κ = {z : Fin (m + N + 1) → ℝ | Fin.init z ∈ κ' ∧
      z (Fin.last (m + N)) = f (Fin.init z)})
    {A : Fin (m + N) → ℝ} (hA : A ∈ κ') : Fin.snoc (α := fun _ => ℝ) A (f A) ∈ κ := by
  rw [hκ]
  show Fin.init (Fin.snoc (α := fun _ => ℝ) A (f A)) ∈ κ' ∧
    Fin.snoc (α := fun _ => ℝ) A (f A) (Fin.last (m + N)) =
      f (Fin.init (Fin.snoc (α := fun _ => ℝ) A (f A)))
  rw [Fin.init_snoc, Fin.snoc_last]
  exact ⟨hA, rfl⟩

theorem snoc_mem_band_cell {m N : ℕ} {κ' : Set (Fin (m + N) → ℝ)}
    {a b : (Fin (m + N) → ℝ) → EReal} {κ : Set (Fin (m + N + 1) → ℝ)}
    (hκ : κ = {z : Fin (m + N + 1) → ℝ | Fin.init z ∈ κ' ∧
      a (Fin.init z) < ((z (Fin.last (m + N)) : ℝ) : EReal) ∧
      ((z (Fin.last (m + N)) : ℝ) : EReal) < b (Fin.init z)})
    {A : Fin (m + N) → ℝ} {t : ℝ} (hA : A ∈ κ') (h1 : a A < ((t : ℝ) : EReal))
    (h2 : ((t : ℝ) : EReal) < b A) : Fin.snoc (α := fun _ => ℝ) A t ∈ κ := by
  rw [hκ]
  show Fin.init (Fin.snoc (α := fun _ => ℝ) A t) ∈ κ' ∧
    a (Fin.init (Fin.snoc (α := fun _ => ℝ) A t)) <
      (((Fin.snoc (α := fun _ => ℝ) A t) (Fin.last (m + N)) : ℝ) : EReal) ∧
    (((Fin.snoc (α := fun _ => ℝ) A t) (Fin.last (m + N)) : ℝ) : EReal) <
      b (Fin.init (Fin.snoc (α := fun _ => ℝ) A t))
  rw [Fin.init_snoc, Fin.snoc_last]
  exact ⟨hA, h1, h2⟩

/-! ## 6. The sheet structure of a cell -/

/-- The sheet structure attached to a type word `w` and a cell `κ ⊆ ℝ^{m+N}`, whose level types
are recorded by `w`: an open nonempty set `T` of "band coordinates", a map `φ` continuous on `T`
and zero off `T`, such that the `w`-sheet parametrisation sends `π z, φ (π z)` back to `z` (`π`
being the projection onto the parameters and the band coordinates), the sheet over every point of
`T` lies in `κ`, and `φ (π z)` is the graph-coordinate block of `z`. -/
def SheetData (m N : ℕ) (w : Fin N → CellType) (κ : Set (Fin (m + N) → ℝ)) : Prop :=
  ∃ (T : Set (Fin (m + nBand N w) → ℝ))
    (φ : (Fin (m + nBand N w) → ℝ) → (Fin (nGraph N w) → ℝ)),
    T.Nonempty ∧ IsOpen T ∧ ContinuousOn φ T ∧ (∀ v ∉ T, φ v = 0) ∧
    (∀ z ∈ κ, (fun i => z (selBand m w i)) ∈ T) ∧
    (∀ z ∈ κ, sheetPtM (wordEquiv w) (fun i => z (selBand m w i))
        (fun k => z (Fin.natAdd m (graphIdx w k))) = z) ∧
    (∀ v ∈ T, sheetPtM (wordEquiv w) v (φ v) ∈ κ) ∧
    (∀ z ∈ κ, φ (fun i => z (selBand m w i)) = fun k => z (Fin.natAdd m (graphIdx w k)))


end Work.WilCrux
