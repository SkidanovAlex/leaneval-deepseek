import Mathlib
import Submission.Work.RatHurewicz.Triad.Stage

/-!
# The preparation theorem of the triad argument (tom Dieck 6.9.2)

This file proves `exists_preparation`: from the compression hypotheses for the two
pairs `(B, B ∩ C)` and `(C, B ∩ C)` one deforms an admissible map
`Φ : I^{n+1} → X` through admissible maps into a map `Ψ` which, on every cell of the
given grid, satisfies the clauses `ConClauses` of the rule of the grid induction, and
which is `B`-valued (`ValsB`) resp. `C`-valued (`ValsC`) on the `CellB`- resp. `CellC`-cells.

The proof is the induction over the cells of the grid described in
`Submission/Work/RatHurewicz/Triad/NOTES_triadCompression.md`: cells are processed in
increasing dimension, each cell being treated by `Treat.rule` (compression, `K`-trick,
`G`-trick, or the `0`-cell path) and the resulting cell homotopies concatenated.  The
invariant carried through the induction is `PrepKeep`: the clauses for the processed
cells, the value-set properties, the initial face and admissibility of the current map.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

open Work.ThomBordism.TwoSet

noncomputable section

variable {X : Type} [TopologicalSpace X] {B C : Set X} {x₀ : ↥(B ∩ C)} {n p q N : ℕ}

/-- **The invariant of the grid induction.**  For the current map `g` and the set `S` of
already processed cells: every cell of `S` satisfies its clauses, `g` is `B`-valued on the
`CellB`-cells and `C`-valued on the `CellC`-cells, fixes the initial face, and is admissible. -/
def PrepKeep (p q : ℕ) (B C : Set X) (x₀ : ↥(B ∩ C)) (Φ : C(IC (n + 1), X))
    (S : Set (CellIdx (n + 1) N)) (g : C(IC (n + 1), X)) : Prop :=
  (∀ c ∈ S, ConClauses p q B C Φ g c) ∧ ValsB (N := N) B Φ g ∧ ValsC (N := N) C Φ g ∧
    InitFace (x₀ : X) g ∧ TriadAdmissible B C x₀ g


/-- A cell of the `j`-grid of `I^j` has at most `j` interval directions. -/
theorem prepCellDim_le {j N : ℕ} (c : CellIdx j N) : cellDim c ≤ j := by
  rw [cellDim]
  calc (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)).card
      ≤ (Finset.univ : Finset (Fin j)).card := Finset.card_filter_le _ _
    _ = j := by simp

/-- A cell which is mapped by `Φ` into `B ∩ C` satisfies all its clauses vacuously. -/
theorem prepConClauses_of_cellBC {Φ g : C(IC (n + 1), X)} {c : CellIdx (n + 1) N}
    (h : CellB B Φ c ∧ CellC C Φ c) : ConClauses p q B C Φ g c :=
  ⟨fun _ hnC => (hnC h.2).elim, fun _ hnC => (hnC h.2).elim,
   fun hnB _ => (hnB h.1).elim, fun hnB _ => (hnB h.1).elim⟩

/-- The initial map itself satisfies the invariant for the empty set of processed cells. -/
theorem prepKeep_empty {Φ : C(IC (n + 1), X)} (hadm : TriadAdmissible B C x₀ Φ) :
    PrepKeep p q B C x₀ Φ (∅ : Set (CellIdx (n + 1) N)) Φ :=
  ⟨fun c hc => absurd hc (Set.notMem_empty c), fun _ hB => hB, fun _ hC => hC,
   fun z hz => by
     have hs : Fin.snoc (initC n z) (z (Fin.last n)) = z := snoc_initC z
     rw [hz] at hs
     exact hs ▸ hadm.1 (initC n z),
   hadm⟩

/-- The base case `d = 0` of the induction, in the form in which the stage lemma wants it:
there are no cells of dimension `< 0`. -/
theorem prepKeep_zero {Φ : C(IC (n + 1), X)} (hadm : TriadAdmissible B C x₀ Φ) :
    PrepKeep p q B C x₀ Φ {c : CellIdx (n + 1) N | cellDim c < 0} Φ := by
  have hset : {c : CellIdx (n + 1) N | cellDim c < 0} = (∅ : Set (CellIdx (n + 1) N)) := by
    ext c
    simp
  rw [hset]
  exact prepKeep_empty hadm

/-- Collecting a cell mapped into `B ∩ C` into the processed set is harmless: its clauses
are vacuous. -/
theorem prepKeep_insert_both {Φ g : C(IC (n + 1), X)} {S : Set (CellIdx (n + 1) N)}
    {c : CellIdx (n + 1) N}
    (hboth : CellB B Φ c ∧ CellC C Φ c) (hkeep : PrepKeep p q B C x₀ Φ S g) :
    PrepKeep p q B C x₀ Φ (insert c S) g :=
  ⟨fun c' hc' => by
      rcases hc' with rfl | hc''
      · exact prepConClauses_of_cellBC hboth
      · exact hkeep.1 c' hc'',
    hkeep.2.1, hkeep.2.2.1, hkeep.2.2.2.1, hkeep.2.2.2.2⟩

/-- **One step of the grid induction.**  If `S` consists of cells of dimension `< d` (and
contains all of them), and `c` is a cell of dimension exactly `d` which is not mapped into
`B ∩ C`, then the treatment of `c` by the rule of the grid induction produces a homotopy of
the current map `g` through admissible maps whose end satisfies the invariant for
`insert c S`. -/
theorem prepStepCell {d : ℕ} {S : Set (CellIdx (n + 1) N)} {g : C(IC (n + 1), X)}
    {Φ : C(IC (n + 1), X)}
    (hN : 1 ≤ N) (hadm : TriadAdmissible B C x₀ Φ)
    (hBc : ∀ d, 1 ≤ d → d ≤ p + 1 → CompressRelBd
      {y : ↥B | (y : X) ∈ B ∩ C}
      {y : ↥B | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    (hCc : ∀ d, 1 ≤ d → d ≤ q + 1 → CompressRelBd
      {y : ↥C | (y : X) ∈ B ∩ C}
      {y : ↥C | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    (hB0 : ∀ b : ↥B, (b : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.1⟩ b))
    (hC0 : ∀ c : ↥C, (c : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.2⟩ c))
    (hsub : ∀ c : CellIdx (n + 1) N, CellB B Φ c ∨ CellC C Φ c)
    (hSlo : ∀ c' : CellIdx (n + 1) N, cellDim c' < d → c' ∈ S)
    (hSdim : ∀ c' ∈ S, cellDim c' ≤ d)
    {c : CellIdx (n + 1) N} (hc : cellDim c = d) (hcS : c ∉ S)
    (hcnb : ¬ (CellB B Φ c ∧ CellC C Φ c)) (hkeep : PrepKeep p q B C x₀ Φ S g) :
    ∃ (g' : C(IC (n + 1), X)) (Θ : C(IC (n + 1) × I, X)),
      (∀ z, Θ (z, 0) = g z) ∧ (∀ z, Θ (z, 1) = g' z) ∧
      (∀ s : I, TriadAdmissible B C x₀ (sliceOf Θ s)) ∧
      PrepKeep p q B C x₀ Φ (insert c S) g' := by
  classical
  obtain ⟨hcon, hVB, hVC, hInit, hAdm⟩ := hkeep
  have hPG : ∀ z : IC (n + 1), g z ∈ pathComponent (x₀ : X) :=
    mem_pathComponent_of_initFace hInit
  have hCon : ∀ c' : CellIdx (n + 1) N, c' ≠ c → Subcell c' c →
      ConClauses p q B C Φ g c' := by
    intro c' hne hsc
    have hlt : cellDim c' < d := by
      have h1 : cellDim c' ≤ cellDim c := cellDim_le_of_subcell hsc
      have h2 : cellDim c' ≠ cellDim c := fun h => hne (Subcell.eq_of_cellDim_eq hsc h)
      omega
    exact hcon c' (hSlo c' hlt)
  obtain ⟨T⟩ := Treat.rule hN hadm hBc hCc hB0 hC0 (hsub c) hcnb hVB hVC hPG hCon
  refine ⟨T.gs 1, T.G, ?_, ?_, ?_, ?_⟩
  · intro z; exact (T.hgs 0 z).symm.trans (T.gs_zero z)
  · intro z; exact (T.hgs 1 z).symm
  · intro s
    have hslice : sliceOf T.G s = T.gs s := ContinuousMap.ext fun z => (T.hgs s z).symm
    rw [hslice]
    exact T.at_admissible (eps_bound hN) hInit hVB hVC s
  · refine ⟨?_, T.maintain_ValsB (eps_bound hN) hVB 1, T.maintain_ValsC (eps_bound hN) hVC 1,
        T.maintain_InitFace (eps_bound hN) hInit 1,
        T.at_admissible (eps_bound hN) hInit hVB hVC 1⟩
    intro c' hc'
    rcases hc' with rfl | hc''
    · exact ⟨T.hcon1, T.hcon2, T.hcon3, T.hcon4⟩
    · exact T.maintain_Con (eps_bound hN) (by have h := hSdim c' hc''; omega)
        (fun h => hcS (h ▸ hc'')) (hcon c' hc'') 1

/-- **A stage of the grid induction.**  Processing the cells of the list `L` — all of
dimension `d`, and all cells of dimension `d` — one after the other, starting from a map
satisfying the invariant for the cells of dimension `< d`, produces a homotopy through
admissible maps whose end satisfies the invariant for the cells of dimension `≤ d`. -/
theorem prepStepList {d : ℕ} {S : Set (CellIdx (n + 1) N)} {g : C(IC (n + 1), X)}
    {Φ : C(IC (n + 1), X)}
    (hN : 1 ≤ N) (hadm : TriadAdmissible B C x₀ Φ)
    (hBc : ∀ d, 1 ≤ d → d ≤ p + 1 → CompressRelBd
      {y : ↥B | (y : X) ∈ B ∩ C}
      {y : ↥B | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    (hCc : ∀ d, 1 ≤ d → d ≤ q + 1 → CompressRelBd
      {y : ↥C | (y : X) ∈ B ∩ C}
      {y : ↥C | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    (hB0 : ∀ b : ↥B, (b : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.1⟩ b))
    (hC0 : ∀ c : ↥C, (c : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.2⟩ c))
    (hsub : ∀ c : CellIdx (n + 1) N, CellB B Φ c ∨ CellC C Φ c)
    (hSlo : ∀ c' : CellIdx (n + 1) N, cellDim c' < d → c' ∈ S)
    (hSdim : ∀ c' ∈ S, cellDim c' ≤ d)
    {L : List (CellIdx (n + 1) N)} (hLdim : ∀ c ∈ L, cellDim c = d)
    (hLnd : L.Nodup) (hLS : ∀ c ∈ L, c ∉ S)
    (hkeep : PrepKeep p q B C x₀ Φ S g) :
    ∃ (g' : C(IC (n + 1), X)) (Θ : C(IC (n + 1) × I, X)),
      (∀ z, Θ (z, 0) = g z) ∧ (∀ z, Θ (z, 1) = g' z) ∧
      (∀ s : I, TriadAdmissible B C x₀ (sliceOf Θ s)) ∧
      PrepKeep p q B C x₀ Φ (S ∪ {c | c ∈ L}) g' := by
  classical
  induction L generalizing g S with
  | nil =>
      refine ⟨g, ⟨fun p => g p.1, g.continuous.comp continuous_fst⟩, ?_, ?_, ?_, ?_⟩
      · intro z; rfl
      · intro z; rfl
      · intro s
        have hslice : sliceOf (⟨fun p : IC (n + 1) × I => g p.1,
            g.continuous.comp continuous_fst⟩ : C(IC (n + 1) × I, X)) s = g := by
          ext z; rfl
        rw [hslice]
        exact hkeep.2.2.2.2
      · simpa using hkeep
  | cons c L' ih =>
      have hcdim : cellDim c = d := hLdim c List.mem_cons_self
      have hnd_c : c ∉ L' := (List.nodup_cons.mp hLnd).1
      have hnd' : L'.Nodup := (List.nodup_cons.mp hLnd).2
      have hdim' : ∀ c' ∈ L', cellDim c' = d :=
        fun c' hc' => hLdim c' (List.mem_cons_of_mem c hc')
      have hcS : c ∉ S := hLS c List.mem_cons_self
      have hSlo' : ∀ c' : CellIdx (n + 1) N, cellDim c' < d → c' ∈ insert c S :=
        fun c' h => Or.inr (hSlo c' h)
      have hSdim' : ∀ c' ∈ insert c S, cellDim c' ≤ d := by
        intro c' hc'
        rcases hc' with rfl | hc''
        · exact le_of_eq hcdim
        · exact hSdim c' hc''
      have hLS' : ∀ c' ∈ L', c' ∉ insert c S := by
        intro c' hc' hmem
        rcases hmem with rfl | hmem'
        · exact hnd_c hc'
        · exact hLS c' (List.mem_cons_of_mem c hc') hmem'
      have hset : S ∪ {c₁ | c₁ ∈ c :: L'} = insert c S ∪ {c₁ | c₁ ∈ L'} := by
        ext x
        simp only [Set.mem_union, Set.mem_ofPred_eq, List.mem_cons, Set.mem_insert_iff]
        tauto
      by_cases hboth : CellB B Φ c ∧ CellC C Φ c
      · have hkeep' : PrepKeep p q B C x₀ Φ (insert c S) g := prepKeep_insert_both hboth hkeep
        obtain ⟨g', Θ, h0, h1, hadm', hk'⟩ := ih hSlo' hSdim' hdim' hnd' hLS' hkeep'
        exact ⟨g', Θ, h0, h1, hadm', hset ▸ hk'⟩
      · obtain ⟨g₁, Θ₁, h10, h11, hadm1, hk1⟩ :=
          prepStepCell hN hadm hBc hCc hB0 hC0 hsub hSlo hSdim hcdim hcS hboth hkeep
        obtain ⟨g₂, Θ₂, h20, h21, hadm2, hk2⟩ := ih hSlo' hSdim' hdim' hnd' hLS' hk1
        have hjoin : ∀ x : IC (n + 1), Θ₁ (x, 1) = Θ₂ (x, 0) := fun x => by rw [h11 x, h20 x]
        obtain ⟨Θ, hΘ0, hΘ1, hΘle, hΘge⟩ := homotopyConcat (A := IC (n + 1)) (Y := X) hjoin
        refine ⟨g₂, Θ, ?_, ?_, ?_, hset ▸ hk2⟩
        · intro z; rw [hΘ0 z, h10 z]
        · intro z; rw [hΘ1 z, h21 z]
        · intro s
          rcases lt_or_ge (s : ℝ) (1 / 2) with hs | hs
          · have hslice : sliceOf Θ s = sliceOf Θ₁ (phiOne s) := by
              ext z; rw [sliceOf_apply, sliceOf_apply, hΘle s (le_of_lt hs) z]
            rw [hslice]; exact hadm1 (phiOne s)
          · have hslice : sliceOf Θ s = sliceOf Θ₂ (phiTwo s) := by
              ext z; rw [sliceOf_apply, sliceOf_apply, hΘge s hs z]
            rw [hslice]; exact hadm2 (phiTwo s)

/-- **The stage `d` of the grid induction.**  Starting from the map `g` satisfying the
invariant for the cells of dimension `< d`, all cells of dimension `d` are treated and the
invariant holds for the cells of dimension `≤ d`. -/
theorem prepStage {d : ℕ} {g : C(IC (n + 1), X)} {Φ : C(IC (n + 1), X)}
    (hN : 1 ≤ N) (hadm : TriadAdmissible B C x₀ Φ)
    (hBc : ∀ d, 1 ≤ d → d ≤ p + 1 → CompressRelBd
      {y : ↥B | (y : X) ∈ B ∩ C}
      {y : ↥B | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    (hCc : ∀ d, 1 ≤ d → d ≤ q + 1 → CompressRelBd
      {y : ↥C | (y : X) ∈ B ∩ C}
      {y : ↥C | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    (hB0 : ∀ b : ↥B, (b : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.1⟩ b))
    (hC0 : ∀ c : ↥C, (c : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.2⟩ c))
    (hsub : ∀ c : CellIdx (n + 1) N, CellB B Φ c ∨ CellC C Φ c)
    (hkeep : PrepKeep p q B C x₀ Φ {c : CellIdx (n + 1) N | cellDim c < d} g) :
    ∃ (g' : C(IC (n + 1), X)) (Θ : C(IC (n + 1) × I, X)),
      (∀ z, Θ (z, 0) = g z) ∧ (∀ z, Θ (z, 1) = g' z) ∧
      (∀ s : I, TriadAdmissible B C x₀ (sliceOf Θ s)) ∧
      PrepKeep p q B C x₀ Φ {c : CellIdx (n + 1) N | cellDim c ≤ d} g' := by
  classical
  have hLS : ∀ c ∈ (Finset.univ.filter (fun c : CellIdx (n + 1) N => cellDim c = d)).toList,
      c ∉ {c' : CellIdx (n + 1) N | cellDim c' < d} := by
    intro c hc hmem
    have hcd : cellDim c = d := (Finset.mem_filter.mp (Finset.mem_toList.mp hc)).2
    have hclt : cellDim c < d := hmem
    omega
  obtain ⟨g', Θ, h0, h1, hadm', hk⟩ :=
    prepStepList (S := {c : CellIdx (n + 1) N | cellDim c < d})
      hN hadm hBc hCc hB0 hC0 hsub
      (fun c' h => by simpa using h) (fun c' h => by have h' : cellDim c' < d := h; omega)
      (L := (Finset.univ.filter (fun c : CellIdx (n + 1) N => cellDim c = d)).toList)
      (fun c hc => (Finset.mem_filter.mp (Finset.mem_toList.mp hc)).2)
      (Finset.nodup_toList _) hLS hkeep
  refine ⟨g', Θ, h0, h1, hadm', ?_⟩
  have hset : {c : CellIdx (n + 1) N | cellDim c < d}
        ∪ {c | c ∈ (Finset.univ.filter (fun c : CellIdx (n + 1) N => cellDim c = d)).toList}
      = {c : CellIdx (n + 1) N | cellDim c ≤ d} := by
    ext x
    simp only [Set.mem_union, Set.mem_ofPred_eq, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro (h | h)
      · omega
      · omega
    · intro h
      by_cases hlt : cellDim x < d
      · exact Or.inl hlt
      · exact Or.inr (by omega)
  exact hset ▸ hk

/-- **The induction over the dimensions.**  After the stages `0, …, d` there is a homotopy
from `Φ` through admissible maps to a map satisfying the invariant for the cells of
dimension `≤ d`. -/
theorem prepExistsStage {Φ : C(IC (n + 1), X)} (hN : 1 ≤ N)
    (hadm : TriadAdmissible B C x₀ Φ)
    (hBc : ∀ d, 1 ≤ d → d ≤ p + 1 → CompressRelBd
      {y : ↥B | (y : X) ∈ B ∩ C}
      {y : ↥B | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    (hCc : ∀ d, 1 ≤ d → d ≤ q + 1 → CompressRelBd
      {y : ↥C | (y : X) ∈ B ∩ C}
      {y : ↥C | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    (hB0 : ∀ b : ↥B, (b : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.1⟩ b))
    (hC0 : ∀ c : ↥C, (c : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.2⟩ c))
    (hsub : ∀ c : CellIdx (n + 1) N, CellB B Φ c ∨ CellC C Φ c) (d : ℕ) :
    ∃ (g : C(IC (n + 1), X)) (Θ : C(IC (n + 1) × I, X)),
      (∀ z, Θ (z, 0) = Φ z) ∧ (∀ z, Θ (z, 1) = g z) ∧
      (∀ s : I, TriadAdmissible B C x₀ (sliceOf Θ s)) ∧
      PrepKeep p q B C x₀ Φ {c : CellIdx (n + 1) N | cellDim c ≤ d} g := by
  classical
  induction d with
  | zero =>
      obtain ⟨g, Θ, h0, h1, ha, hk⟩ := prepStage (d := 0) hN hadm hBc hCc hB0 hC0 hsub
        (prepKeep_zero hadm)
      exact ⟨g, Θ, h0, h1, ha, hk⟩
  | succ d ih =>
      obtain ⟨g, Θ, h0, h1, ha, hk⟩ := ih
      have hk' : PrepKeep p q B C x₀ Φ {c : CellIdx (n + 1) N | cellDim c < d + 1} g := by
        rw [show {c : CellIdx (n + 1) N | cellDim c < d + 1}
            = {c : CellIdx (n + 1) N | cellDim c ≤ d} from by
          ext x; simp only [Set.mem_ofPred_eq]; omega]
        exact hk
      obtain ⟨g', Θ', h0', h1', ha', hk''⟩ := prepStage (d := d + 1) hN hadm hBc hCc hB0 hC0
        hsub hk'
      have hjoin : ∀ x : IC (n + 1), Θ (x, 1) = Θ' (x, 0) := fun x => by rw [h1 x, h0' x]
      obtain ⟨Θc, hc0, hc1, hcle, hcge⟩ := homotopyConcat (A := IC (n + 1)) (Y := X) hjoin
      refine ⟨g', Θc, ?_, ?_, ?_, hk''⟩
      · intro z; rw [hc0 z, h0 z]
      · intro z; rw [hc1 z, h1' z]
      · intro s
        rcases lt_or_ge (s : ℝ) (1 / 2) with hs | hs
        · have hslice : sliceOf Θc s = sliceOf Θ (phiOne s) := by
            ext z; rw [sliceOf_apply, sliceOf_apply, hcle s (le_of_lt hs) z]
          rw [hslice]; exact ha (phiOne s)
        · have hslice : sliceOf Θc s = sliceOf Θ' (phiTwo s) := by
            ext z; rw [sliceOf_apply, sliceOf_apply, hcge s hs z]
          rw [hslice]; exact ha' (phiTwo s)

theorem exists_preparation {X : Type} [TopologicalSpace X] {B C : Set X} {x₀ : ↥(B ∩ C)}
    {n p q N : ℕ} {Φ : C(Work.ThomBordism.TwoSet.IC (n + 1), X)} (hN : 1 ≤ N)
    (hadm : Work.RatHurewicz.Triad.TriadAdmissible B C x₀ Φ)
    (hBc : ∀ d, 1 ≤ d → d ≤ p + 1 → Work.RatHurewicz.CompressRelBd
      {y : ↥B | (y : X) ∈ B ∩ C}
      {y : ↥B | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    (hCc : ∀ d, 1 ≤ d → d ≤ q + 1 → Work.RatHurewicz.CompressRelBd
      {y : ↥C | (y : X) ∈ B ∩ C}
      {y : ↥C | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    (hB0 : ∀ b : ↥B, (b : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.1⟩ b))
    (hC0 : ∀ c : ↥C, (c : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.2⟩ c))
    (hsub : ∀ c : Work.ThomBordism.TwoSet.CellIdx (n + 1) N,
      Work.RatHurewicz.Triad.CellB B Φ c ∨ Work.RatHurewicz.Triad.CellC C Φ c) :
    ∃ (Ψ : C(Work.ThomBordism.TwoSet.IC (n + 1), X))
      (Θ : C(Work.ThomBordism.TwoSet.IC (n + 1) × unitInterval, X)),
      (∀ z, Θ (z, 0) = Φ z) ∧ (∀ z, Θ (z, 1) = Ψ z) ∧
      (∀ s : unitInterval, Work.RatHurewicz.Triad.TriadAdmissible B C x₀
        (Work.RatHurewicz.Triad.sliceOf Θ s)) ∧
      (∀ c : Work.ThomBordism.TwoSet.CellIdx (n + 1) N,
        Work.RatHurewicz.Triad.ConClauses p q B C Φ Ψ c) ∧
      Work.RatHurewicz.Triad.ValsB (N := N) B Φ Ψ ∧
      Work.RatHurewicz.Triad.ValsC (N := N) C Φ Ψ := by
  classical
  obtain ⟨g, Θ, h0, h1, ha, hk⟩ := prepExistsStage (n := n) (p := p) (q := q) (N := N)
    hN hadm hBc hCc hB0 hC0 hsub (n + 1)
  refine ⟨g, Θ, h0, h1, ha, fun c => hk.1 c ?_, hk.2.1, hk.2.2.1⟩
  show cellDim c ≤ n + 1
  exact prepCellDim_le c

end

end Work.RatHurewicz.Triad
