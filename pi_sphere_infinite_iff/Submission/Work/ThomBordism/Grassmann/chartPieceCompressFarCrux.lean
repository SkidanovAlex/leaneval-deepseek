import Mathlib
import Submission.Work.ThomBordism.Grassmann.thomSpacePieces
import Submission.Work.ThomBordism.Grassmann.Torsion.contractibleFar
import Submission.Work.ThomBordism.Grassmann.escapeToFar
import Submission.Work.ThomBordism.TwoSet.CompressBasic
import Submission.Work.ThomBordism.TwoSet.Assembly
import Submission.Work.ThomBordism.TwoSet.Cells
import Submission.Work.ThomBordism.TwoSet.Cutoff
import Submission.Work.ThomBordism.TwoSet.Setup
import Submission.Work.ThomBordism.TwoSet.Fold
import Submission.Work.ThomBordism.TwoSet.Step
import Submission.Work.ThomBordism.TwoSet.CollarSubdivision
import Submission.Work.ThomBordism.TwoSet.spreadCell
import Submission.Work.ThomBordism.TwoSet.Subdivision
import Submission.Work.ThomBordism.Grassmann.chartPieceShellCompress
import Submission.Work.Stems.subsingleton_of_contractible
import Submission.Work.Stems.subsingleton_homotopyGroup_change_basepoint

/-!
# The chart piece `far 1 ∪ π⁻¹(W)` compresses into the far region

**Target** (`Work.ThomBordism.Grassmann.chartPieceCompressFarCrux`): for `k m : ℕ`, a chart
`S₀ : ChartIdx k m` and an open `W ⊆ (tautologicalBundle k m).baseSet S₀`,

    Compress ↥(far 1 ∪ π⁻¹W) (far 1 ∩ (far 1 ∪ π⁻¹W)) j      for every `j < k`.

## Strategy

Write `Z = far 1 ∪ π⁻¹W` and `S = π⁻¹W ⊆ Z`.  The piece `Z` is covered by the two *open* sets
`Z ∩ far 1` (contractible) and `Z ∩ S = S`.

On `S` the *shell computation* is available: `chartPieceShellCompress` says that every map
`(I^d, ∂I^d) → (S, S ∩ far 1)` is compressible into `S ∩ far 1` for `d < k` (this is the input of
`Submission/Work/ThomBordism/Grassmann/chartPieceShellCompress.lean`, whose proof is the chart
trivialisation plus the connectivity of spheres).

The two-set collapse `compressRel_twoSet` cannot be applied directly: its hypothesis
`Compress ↥(far 1) (far 1 ∩ S) d` is **false** (the trace `far 1 ∩ S ≃ W × S^{k-1}` sees `π_*(W)`,
while `far 1` is contractible).  The point of the variant below is that the pieces whose images lie
in `far 1` need *no* processing at all — they are already in the target — so only the `V`-typed
cells have to be compressed, and for those `Compress ↥S (S ∩ far 1) d` does hold.

Concretely: a Lebesgue (collared) subdivision of `I^j` for the open cover `{Z ∩ far, S}` gives a
labelling of the grid boxes, and the cells are processed in increasing dimension: a cell contained
in an `S`-labelled box is compressed into `S ∩ far ⊆ far` using `chartPieceShellCompress`, and the
cells contained in `far`-labelled boxes are left untouched.  The invariants maintained are the type
invariant `Jinv` (unambiguous `V`-cells are `V`-valued, unambiguous `U`-cells are `U`-valued,
ambiguous cells are `U ∩ V`-valued) and the restricted value invariant `Iinv2` (points whose
minimal cell is away from `∂I^j` and `V`-typed have values in `U ∩ V` while their dimension is
below the threshold).

The `SubdivisionCollared` collar condition guarantees that boxes touching `∂I^j` are `U`-labelled
(`U = far 1`), so every modification is supported away from `∂I^j`.
-/

open scoped Topology unitInterval
open Work.ThomBordism.TwoSet

namespace Work.ThomBordism.Grassmann

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

variable {X : Type*} [TopologicalSpace X] {j N : ℕ} {U V : Set X}

/-- **The `Vcell`-restricted value invariant.** -/
def Iinv2 (lab : (Fin j → Fin N) → Bool) (W : Set X) (Δ : ℕ) (Q : Finset (CellIdx j N))
    (g : C(IC j, X)) : Prop :=
  ∀ x : IC j, Away (cOf N x) → Vcell lab (cOf N x) →
    (cellDim (cOf N x) < Δ ∨ (cellDim (cOf N x) = Δ ∧ cOf N x ∈ Q)) → g x ∈ W

/-- **One step of the compression, `V`-typed cells only.** -/
theorem stepV (lab : (Fin j → Fin N) → Bool)
    (hVc : ∀ d, d ≤ j → Compress ↥V {v : ↥V | (v : X) ∈ U} d)
    (hN : 1 ≤ N) {c : CellIdx j N} (hcAway : Away c) (hcV : Vcell lab c)
    (hcU : ¬ Ucell lab c) {Δ : ℕ} (hΔ : cellDim c = Δ)
    {Q : Finset (CellIdx j N)} {g : C(IC j, X)}
    (hJ : Jinv (U := U) (V := V) lab g) (hI : Iinv2 lab (U ∩ V) Δ Q g) :
    ∃ (g' : C(IC j, X)) (G : C(IC j × I, X)),
      (∀ x, G (x, 0) = g x) ∧
      (∀ x, x ∈ Cube.boundary (Fin j) → ∀ t, G (x, t) = g x) ∧
      (∀ x, G (x, 1) = g' x) ∧
      Jinv (U := U) (V := V) lab g' ∧ Iinv2 lab (U ∩ V) Δ (insert c Q) g' := by
  classical
  have hdj : cellDim c ≤ j := by
    rw [cellDim]
    simpa using Finset.card_le_univ (Finset.univ.filter fun i : Fin j => c.lo i < c.hi i)
  obtain ⟨e, he⟩ := exists_cellHomeo hN c
  have hcellA : ∀ x ∈ cellSet c, g x ∈ V := hJ.1 c hcV hcU
  let f : C(cellSet c, ↥V) := ⟨fun z => ⟨g z, hcellA z z.2⟩,
    Continuous.subtype_mk (g.continuous.comp continuous_subtype_val) _⟩
  have hfb : ∀ z : cellSet c,
      z ∈ ({z : cellSet c | ((z : IC j) ∈ cellRelbd c)} : Set (cellSet c)) →
      f z ∈ {a : ↥V | (a : X) ∈ U} := by
    intro z hz
    exact (hI (z : IC j) (Away_mono (cellSet_cOf_subset hN c z.2) hcAway)
      (Vcell_mono hN (cellSet_cOf_subset hN c z.2) hcV)
      (Or.inl (by rw [← hΔ]; exact cellDim_cOf_lt_of_mem_cellRelbd N hN hz z.2))).1
  obtain ⟨Gc, hGc0, hGcbd, hGc1⟩ := compresses_homeo (hVc (cellDim c) hdj) e
    ({z : cellSet c | ((z : IC j) ∈ cellRelbd c)} : Set (cellSet c)) he f hfb
  let H : C(cellSet c × unitInterval, X) :=
    ⟨fun p => (Gc p : X), continuous_subtype_val.comp Gc.continuous⟩
  have hH0 : ∀ z : cellSet c, H (z, 0) = g z := fun z => congrArg Subtype.val (hGc0 z)
  have hHbd : ∀ (z : cellSet c), ((z : IC j) ∈ cellRelbd c) → ∀ t, H (z, t) = g z :=
    fun z hz t => congrArg Subtype.val (hGcbd z hz t)
  have hHA : ∀ z : cellSet c, ∀ t : unitInterval, H (z, t) ∈ V := fun z t => (Gc (z, t)).2
  have hHB : ∀ z : cellSet c, H (z, 1) ∈ U := fun z => hGc1 z
  obtain ⟨G, hG0, hGcell, hGzero, hG4, hG5, hG6⟩ := spreadCell c hN g H hH0 hHbd
  let g' : C(IC j, X) := ⟨fun x => G (x, 1),
    G.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hclampmem : ∀ {x : IC j}, clampCell c hN x ∈ cellRelbd c →
      g (clampCell c hN x) ∈ U ∩ V := by
    intro x hbd
    exact hI (clampCell c hN x)
      (Away_mono (cellSet_cOf_subset hN c (clampCell_mem c hN x)) hcAway)
      (Vcell_mono hN (cellSet_cOf_subset hN c (clampCell_mem c hN x)) hcV)
      (Or.inl (by rw [← hΔ]; exact cellDim_cOf_lt_of_mem_cellRelbd N hN hbd (clampCell_mem c hN x)))
  have hsub : ∀ {d : CellIdx j N} {x : IC j}, x ∈ cellSet d →
      ∀ y ∈ cellSet (cOf N x), y ∈ cellSet d := fun hx y hy =>
    cellSet_antitone (fun i => (cellSet_cOf_subset hN _ hx i).1) (fun i => (cellSet_cOf_subset hN _ hx i).2) hy
  have hkeycell : ∀ {d : CellIdx j N} {x : IC j}, x ∈ cellSet d → x ∉ cellSet c →
      0 < nuOf c x → clampCell c hN x ∉ cellRelbd c →
      ∀ i, d.lo i ≤ c.lo i ∧ c.hi i ≤ d.hi i := by
    intro d x hx hxc hpos hbd i
    have hkey := keyLemma hN c (close_of_nuOf_pos c hpos) hbd
    exact ⟨le_trans (cellSet_cOf_subset hN d hx i).1 (hkey.1 i),
      le_trans (hkey.2.1 i) (cellSet_cOf_subset hN d hx i).2⟩
  refine ⟨g', G, hG0, ?_, fun x => rfl, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx t
    rw [hGzero x (nuOf_eq_zero_of_away_of_mem_boundary hN hcAway hx) t]
  · intro d hdA hdB x hx
    change G (x, 1) ∈ V
    by_cases hc : x ∈ cellSet c
    · rw [hGcell ⟨x, hc⟩ 1]
      exact hHA ⟨x, hc⟩ 1
    · by_cases hnu : nuOf c x = 0
      · rw [hGzero x hnu 1]
        exact hJ.1 d hdA hdB x hx
      · have hpos : 0 < nuOf c x := lt_of_le_of_ne (nuOf_nonneg c x) (Ne.symm hnu)
        rcases le_or_gt (rOf c x) (nuOf c x) with hle | hlt
        · by_cases hbd : clampCell c hN x ∈ cellRelbd c
          · rw [hG5 x hc hpos hle hbd]
            exact (hclampmem hbd).2
          · rcases hG4 x hc hpos hle with ⟨z, hz, s, hval⟩
            rw [hval]
            exact hHA ⟨z, hz⟩ s
        · rcases hG6 x hc hpos hlt with ⟨y, hy, hval⟩
          rw [hval]
          exact hJ.1 d hdA hdB y (hsub hx y hy)
  · intro d hdB hdA x hx
    change G (x, 1) ∈ U
    by_cases hc : x ∈ cellSet c
    · rw [hGcell ⟨x, hc⟩ 1]
      exact hHB ⟨x, hc⟩
    · by_cases hnu : nuOf c x = 0
      · rw [hGzero x hnu 1]
        exact hJ.2.1 d hdB hdA x hx
      · have hpos : 0 < nuOf c x := lt_of_le_of_ne (nuOf_nonneg c x) (Ne.symm hnu)
        rcases le_or_gt (rOf c x) (nuOf c x) with hle | hlt
        · by_cases hbd : clampCell c hN x ∈ cellRelbd c
          · rw [hG5 x hc hpos hle hbd]
            exact (hclampmem hbd).1
          · exact absurd (Ucell_mono hN (hkeycell hx hc hpos hbd) hdB) hcU
        · rcases hG6 x hc hpos hlt with ⟨y, hy, hval⟩
          rw [hval]
          exact hJ.2.1 d hdB hdA y (hsub hx y hy)
  · intro d hdA hdB x hx
    change G (x, 1) ∈ U ∩ V
    by_cases hc : x ∈ cellSet c
    · rw [hGcell ⟨x, hc⟩ 1]
      exact ⟨hHB ⟨x, hc⟩, hHA ⟨x, hc⟩ 1⟩
    · by_cases hnu : nuOf c x = 0
      · rw [hGzero x hnu 1]
        exact hJ.2.2 d hdA hdB x hx
      · have hpos : 0 < nuOf c x := lt_of_le_of_ne (nuOf_nonneg c x) (Ne.symm hnu)
        rcases le_or_gt (rOf c x) (nuOf c x) with hle | hlt
        · by_cases hbd : clampCell c hN x ∈ cellRelbd c
          · rw [hG5 x hc hpos hle hbd]
            exact hclampmem hbd
          · exact absurd (Ucell_mono hN (hkeycell hx hc hpos hbd) hdB) hcU
        · rcases hG6 x hc hpos hlt with ⟨y, hy, hval⟩
          rw [hval]
          exact hJ.2.2 d hdA hdB y (hsub hx y hy)
  · intro x hAw hVcell hd
    change G (x, 1) ∈ U ∩ V
    by_cases hc : x ∈ cellSet c
    · rw [hGcell ⟨x, hc⟩ 1]
      exact ⟨hHB ⟨x, hc⟩, hHA ⟨x, hc⟩ 1⟩
    · by_cases hnu : nuOf c x = 0
      · rw [hGzero x hnu 1]
        refine hI x hAw hVcell ?_
        rcases hd with h1 | ⟨h2, h3⟩
        · exact Or.inl h1
        · refine Or.inr ⟨h2, ?_⟩
          rcases Finset.mem_insert.mp h3 with h4 | h4
          · exact absurd (h4 ▸ mem_cOf N hN x) hc
          · exact h4
      · have hpos : 0 < nuOf c x := lt_of_le_of_ne (nuOf_nonneg c x) (Ne.symm hnu)
        rcases le_or_gt (rOf c x) (nuOf c x) with hle | hlt
        · by_cases hbd : clampCell c hN x ∈ cellRelbd c
          · rw [hG5 x hc hpos hle hbd]
            exact hclampmem hbd
          · exfalso
            have hkey := keyLemma hN c (close_of_nuOf_pos c hpos) hbd
            have hgt : Δ < cellDim (cOf N x) := by rw [← hΔ]; exact hkey.2.2 hc
            rcases hd with h1 | ⟨h2, _⟩ <;> omega
        · rcases hG6 x hc hpos hlt with ⟨y, hy, hval⟩
          rw [hval]
          refine hI y (Away_mono (cellSet_cOf_subset hN (cOf N x) hy) hAw)
            (Vcell_mono hN (cellSet_cOf_subset hN (cOf N x) hy) hVcell) ?_
          have hle' : cellDim (cOf N y) ≤ cellDim (cOf N x) := cellDim_cOf_le_of_mem hN (cOf N x) hy
          rcases hd with h1 | ⟨h2, h3⟩
          · exact Or.inl (lt_of_le_of_lt hle' h1)
          · by_cases hlt' : cellDim (cOf N y) < Δ
            · exact Or.inl hlt'
            · refine Or.inr ⟨by omega, ?_⟩
              rcases Finset.mem_insert.mp h3 with h4 | h4
              · exact absurd (h4 ▸ mem_cOf N hN x) hc
              · have hdim : cellDim (cOf N y) = cellDim (cOf N x) := by omega
                have heq : cOf N y = cOf N x :=
                  cellIdx_eq_of_le_of_cellDim_eq
                    (fun i => (cellSet_cOf_subset hN (cOf N x) hy i).1)
                    (fun i => (cellSet_cOf_subset hN (cOf N x) hy i).2) hdim
                rw [heq]
                exact h4

/-! ## The rounds and the assembly -/

/-- The cells processed in dimension `Δ`: away from the boundary, in a `V`-labelled box and in no
`U`-labelled box. -/
noncomputable def Qall2 (lab : (Fin j → Fin N) → Bool) (Δ : ℕ) : Finset (CellIdx j N) := by
  classical
  exact Finset.univ.filter (fun c => Away c ∧ Vcell lab c ∧ ¬ Ucell lab c ∧ cellDim c = Δ)

theorem mem_Qall2 {lab : (Fin j → Fin N) → Bool} {Δ : ℕ} {c : CellIdx j N} :
    c ∈ Qall2 lab Δ ↔ Away c ∧ Vcell lab c ∧ ¬ Ucell lab c ∧ cellDim c = Δ := by
  classical
  unfold Qall2
  simp

/-- **The round of a fixed dimension.** -/
theorem round_aux2 {lab : (Fin j → Fin N) → Bool} (hN : 1 ≤ N)
    (hVc : ∀ d, d ≤ j → Compress ↥V {v : ↥V | (v : X) ∈ U} d)
    (Δ : ℕ) (T : Finset (CellIdx j N))
    (hT : ∀ c ∈ T, Away c ∧ Vcell lab c ∧ ¬ Ucell lab c ∧ cellDim c = Δ) :
    ∀ Rem : Finset (CellIdx j N), Rem ⊆ T →
    ∀ g : C(IC j, X), Jinv (U := U) (V := V) lab g →
    Iinv2 lab (U ∩ V) Δ (T \ Rem) g →
    ∃ (g' : C(IC j, X)) (_ : g.HomotopyRel g' (Cube.boundary (Fin j))),
      Jinv (U := U) (V := V) lab g' ∧ Iinv2 lab (U ∩ V) Δ T g' := by
  classical
  intro Rem
  induction Rem using Finset.induction with
  | empty =>
    intro _ g hJ hI
    exact ⟨g, ContinuousMap.HomotopyRel.refl g (Cube.boundary (Fin j)), hJ, by simpa using hI⟩
  | insert a Rem' ha ih =>
    intro hRem g hJ hI
    have haT : a ∈ T := hRem (Finset.mem_insert_self a Rem')
    obtain ⟨hAway, hVa, hUa, hdim⟩ := hT a haT
    obtain ⟨g₁, G, h0, h1, h2, hJ₁, hI₁⟩ := stepV lab hVc hN hAway hVa hUa hdim hJ hI
    have hRel₁ : g.HomotopyRel g₁ (Cube.boundary (Fin j)) := homotopyRel_of_raw h0 h2 h1
    have hsub : Rem' ⊆ T := fun c hc => hRem (Finset.mem_insert_of_mem hc)
    have hseteq : insert a (T \ insert a Rem') = T \ Rem' := by
      ext c
      simp only [Finset.mem_insert, Finset.mem_sdiff, not_or]
      constructor
      · rintro (rfl | ⟨hcT, hca, hcR⟩)
        · exact ⟨haT, ha⟩
        · exact ⟨hcT, hcR⟩
      · rintro ⟨hcT, hcR⟩
        by_cases hca : c = a
        · exact Or.inl hca
        · exact Or.inr ⟨hcT, hca, hcR⟩
    have hI₁' : Iinv2 lab (U ∩ V) Δ (T \ Rem') g₁ := by
      rw [← hseteq]
      exact hI₁
    obtain ⟨g', H', hJ', hI'⟩ := ih hsub g₁ hJ₁ hI₁'
    exact ⟨g', hRel₁.trans H', hJ', hI'⟩

/-- **Advancing the dimension threshold.** -/
theorem advance2 {lab : (Fin j → Fin N) → Bool} (hN : 1 ≤ N) {g : C(IC j, X)} {Δ : ℕ}
    {T : Finset (CellIdx j N)}
    (hT : ∀ c, Away c → Vcell lab c → ¬ Ucell lab c → cellDim c = Δ → c ∈ T)
    (hJ : Jinv (U := U) (V := V) lab g) (hI : Iinv2 lab (U ∩ V) Δ T g) :
    Iinv2 lab (U ∩ V) (Δ + 1) ∅ g := by
  intro x hAw hV hd
  rcases hd with h1 | ⟨h2, h3⟩
  · by_cases hle : cellDim (cOf N x) < Δ
    · exact hI x hAw hV (Or.inl hle)
    · have hdim : cellDim (cOf N x) = Δ := by omega
      by_cases hU : Ucell lab (cOf N x)
      · exact hJ.2.2 (cOf N x) hV hU x (mem_cOf N hN x)
      · exact hI x hAw hV (Or.inr ⟨hdim, hT (cOf N x) hAw hV hU hdim⟩)
  · exact absurd h3 (Finset.notMem_empty _)

/-- **All the rounds.** -/
theorem process_all2 {lab : (Fin j → Fin N) → Bool} (hN : 1 ≤ N)
    (hVc : ∀ d, d ≤ j → Compress ↥V {v : ↥V | (v : X) ∈ U} d)
    (f : C(IC j, X)) (hJ : Jinv (U := U) (V := V) lab f) :
    ∀ Δ, Δ ≤ j + 1 → ∃ (g : C(IC j, X)) (_ : f.HomotopyRel g (Cube.boundary (Fin j))),
      Jinv (U := U) (V := V) lab g ∧ Iinv2 lab (U ∩ V) Δ ∅ g := by
  intro Δ
  induction Δ with
  | zero =>
    intro _
    exact ⟨f, ContinuousMap.HomotopyRel.refl f (Cube.boundary (Fin j)), hJ, fun x _ _ hd => by
      rcases hd with h | ⟨h, hmem⟩
      · omega
      · exact absurd hmem (Finset.notMem_empty _)⟩
  | succ n ih =>
    intro hn
    have hn' : n ≤ j + 1 := by omega
    obtain ⟨g, H, hJg, hIg⟩ := ih hn'
    obtain ⟨g', H', hJ', hI'⟩ :=
      round_aux2 hN hVc n (Qall2 lab n) (fun c hc => mem_Qall2.mp hc)
        (Qall2 lab n) (Finset.Subset.refl _) g hJg (by simpa using hIg)
    have hadv : Iinv2 lab (U ∩ V) (n + 1) ∅ g' :=
      advance2 hN (fun c hAw hV hU hdim => mem_Qall2.mpr ⟨hAw, hV, hU, hdim⟩) hJ' hI'
    exact ⟨g', H.trans H', hJ', hadv⟩

/-- **The endgame.** -/
theorem endgame2 {lab : (Fin j → Fin N) → Bool} (hN : 1 ≤ N)
    (hfar : ∀ m, lab m = true → ∀ x ∈ boxSet m, ∀ i,
      2/(N:ℝ) ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ 1 - 2/(N:ℝ))
    {g : C(IC j, X)} (hJ : Jinv (U := U) (V := V) lab g)
    (hI : Iinv2 lab (U ∩ V) (j + 1) ∅ g) : ∀ x, g x ∈ U := by
  intro x
  by_cases hU : Ucell lab (cOf N x)
  · by_cases hV : Vcell lab (cOf N x)
    · exact (hJ.2.2 (cOf N x) hV hU x (mem_cOf N hN x)).1
    · exact hJ.2.1 (cOf N x) hU hV x (mem_cOf N hN x)
  · have hV : Vcell lab (cOf N x) := (cell_typed hN (cOf N x)).resolve_right hU
    have hAw : Away (cOf N x) := Vcell_away hN hfar hV
    exact (hI x hAw hV (Or.inl (by have := cellDim_le (cOf N x); omega))).1

/-- **The cell-by-cell compression, `V`-typed cells only.** -/
theorem processCells2 {X : Type*} [TopologicalSpace X] {U V : Set X} {j N : ℕ} (hN : 3 ≤ N)
    (lab : (Fin j → Fin N) → Bool)
    (hVc : ∀ d, d ≤ j → Compress ↥V {v : ↥V | (v : X) ∈ U} d)
    (hfar : ∀ m, lab m = true → ∀ x ∈ boxSet m, ∀ i,
      2/(N:ℝ) ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ 1 - 2/(N:ℝ))
    (f : C(IC j, X))
    (hlabU : ∀ m, lab m = false → ∀ x ∈ boxSet m, f x ∈ U)
    (hlabV : ∀ m, lab m = true → ∀ x ∈ boxSet m, f x ∈ V)
    (hbd : ∀ x, x ∈ Cube.boundary (Fin j) → f x ∈ U) :
    ∃ G : C(IC j × I, X),
      (∀ x, G (x, 0) = f x) ∧
      (∀ x, x ∈ Cube.boundary (Fin j) → ∀ t, G (x, t) = f x) ∧
      (∀ x, G (x, 1) ∈ U) := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hJf : Jinv (U := U) (V := V) lab f := by
    refine ⟨?_, ?_, ?_⟩
    · rintro d ⟨m, hm, hmc⟩ - x hx
      exact hlabV m hm x (hmc hx)
    · rintro d ⟨m, hm, hmc⟩ - x hx
      exact hlabU m hm x (hmc hx)
    · rintro d ⟨m, hm, hmc⟩ ⟨m', hm', hm'c⟩ x hx
      exact ⟨hlabU m' hm' x (hm'c hx), hlabV m hm x (hmc hx)⟩
  obtain ⟨g, H, hJg, hIg⟩ := process_all2 hN1 hVc f hJf (j + 1) le_rfl
  have hend : ∀ x, g x ∈ U := endgame2 hN1 hfar hJg hIg
  refine ⟨⟨fun p : IC j × I => H.toHomotopy (p.2, p.1),
    H.toHomotopy.continuous.comp (continuous_snd.prodMk continuous_fst)⟩, ?_, ?_, ?_⟩
  · intro x
    show H.toHomotopy ((0 : I), x) = f x
    exact H.toHomotopy.map_zero_left x
  · intro x hx t
    show H.toHomotopy (t, x) = f x
    exact H.prop' t x hx
  · intro x
    show H.toHomotopy ((1 : I), x) ∈ U
    rw [show H.toHomotopy ((1 : I), x) = g x from H.toHomotopy.map_one_left x]
    exact hend x


/-! ## The geometric instantiation -/

variable {k m : ℕ}

/-- The chart piece `Z = far 1 ∪ π⁻¹W` of the Thom space. -/
abbrev pieceS (k m : ℕ) (W : Set (OG k m)) : Set (Torsion.TP k m) :=
  Torsion.far k m 1 ∪ OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' W)

/-- The trace of the far region in the piece. -/
abbrev farTr (k m : ℕ) (W : Set (OG k m)) : Set ↥(pieceS k m W) :=
  {x | (x : Torsion.TP k m) ∈ Torsion.far k m 1}

/-- The `π⁻¹W` part of the Thom space. -/
abbrev shellS (k m : ℕ) (W : Set (OG k m)) : Set (Torsion.TP k m) :=
  OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' W)

/-- The `π⁻¹W` part, seen inside the chart piece. -/
abbrev shellSub (k m : ℕ) (W : Set (OG k m)) : Set ↥(pieceS k m W) :=
  {z | (z : Torsion.TP k m) ∈ shellS k m W}

theorem shellS_preimage_eq (k m : ℕ) (W : Set (OG k m)) :
    OnePoint.some ⁻¹' (shellS k m W) = (tautologicalBundle k m).proj ⁻¹' W := by
  ext p
  constructor
  · rintro ⟨q, hq, hqp⟩
    rw [← Option.some.inj hqp]
    exact hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem shellS_subset_range (k m : ℕ) (W : Set (OG k m)) :
    shellS k m W ⊆ Set.range (OnePoint.some : Torsion.TM k m → Torsion.TP k m) :=
  fun x hx => by rcases hx with ⟨p, -, rfl⟩; exact ⟨p, rfl⟩

theorem isOpen_shellS (k m : ℕ) (W : Set (OG k m)) (hW : IsOpen W) : IsOpen (shellS k m W) := by
  rw [OnePoint.isOpen_def]
  refine ⟨fun h => absurd h ?_, ?_⟩
  · rintro ⟨p, -, hpe⟩
    exact Option.some_ne_none p hpe
  · rw [shellS_preimage_eq]
    exact hW.preimage (tautologicalBundle k m).continuous_proj

theorem isOpen_shellSub (k m : ℕ) (W : Set (OG k m)) (hW : IsOpen W) :
    IsOpen (shellSub k m W) :=
  (isOpen_shellS k m W hW).preimage continuous_subtype_val

theorem isOpen_farTr (k m : ℕ) (W : Set (OG k m)) : IsOpen (farTr k m W) :=
  (Torsion.isOpen_far_one k m).preimage continuous_subtype_val

theorem farTr_union_shellSub (k m : ℕ) (W : Set (OG k m)) :
    farTr k m W ∪ shellSub k m W = Set.univ := by
  refine Set.eq_univ_of_forall (fun z => ?_)
  rcases z.2 with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **The homeomorphism `↥(π⁻¹W) ≃ₜ ↥(shellS k m W)`** induced by the open embedding
`OnePoint.some`. -/
noncomputable def shellSHomeo (k m : ℕ) (W : Set (OG k m)) :
    ↥((tautologicalBundle k m).proj ⁻¹' W) ≃ₜ ↥(shellS k m W) :=
  (Homeomorph.setCongr (shellS_preimage_eq k m W).symm).trans
    ((OnePoint.isOpenEmbedding_coe (X := Torsion.TM k m)).isEmbedding.homeomorphOfSubsetRange
      (shellS_subset_range k m W))

theorem shellSHomeo_apply_coe (k m : ℕ) (W : Set (OG k m))
    (x : ↥((tautologicalBundle k m).proj ⁻¹' W)) :
    ((shellSHomeo k m W x : ↥(shellS k m W)) : Torsion.TP k m) =
      OnePoint.some (x : Torsion.TM k m) := by
  have h := Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe
    (OnePoint.isOpenEmbedding_coe (X := Torsion.TM k m)).isEmbedding
    (shellS_subset_range k m W)
    ((Homeomorph.setCongr (shellS_preimage_eq k m W).symm) x)
  rw [shellSHomeo, Homeomorph.trans_apply]
  exact h

/-- **The homeomorphism `↥(shellSub k m W) ≃ₜ ↥(π⁻¹W)`**: the `π⁻¹W`-part of the chart piece,
identified with the total space over `W`. -/
noncomputable def shellSubHomeo (k m : ℕ) (W : Set (OG k m)) :
    ↥(shellSub k m W) ≃ₜ ↥((tautologicalBundle k m).proj ⁻¹' W) :=
  (subSubHomeo (Z := pieceS k m W) (W := shellS k m W) Set.subset_union_right).trans
    (shellSHomeo k m W).symm

theorem shellSubHomeo_apply_coe (k m : ℕ) (W : Set (OG k m)) (v : ↥(shellSub k m W)) :
    OnePoint.some (((shellSubHomeo k m W v : ↥((tautologicalBundle k m).proj ⁻¹' W)) :
        Torsion.TM k m)) = (v.1.1 : Torsion.TP k m) := by
  have h1 : ((shellSubHomeo k m W v :
        ↥((tautologicalBundle k m).proj ⁻¹' W)) : Torsion.TM k m)
      = ↑((shellSHomeo k m W).symm (subSubHomeo (Z := pieceS k m W) (W := shellS k m W)
          Set.subset_union_right v)) := rfl
  rw [h1, ← shellSHomeo_apply_coe k m W ((shellSHomeo k m W).symm
      (subSubHomeo (Z := pieceS k m W) (W := shellS k m W) Set.subset_union_right v)),
    Homeomorph.apply_symm_apply]
  rfl

/-- **The pair condition** for `shellSubHomeo`: the shell `{1 < fibN}` corresponds to the trace of
the far region. -/
theorem shellSubHomeo_pair (k m : ℕ) (W : Set (OG k m)) (v : ↥(shellSub k m W)) :
    (shellSubHomeo k m W v ∈ {p : ↥((tautologicalBundle k m).proj ⁻¹' W) |
        (1 : ℝ) < Torsion.fibN k m (p : Torsion.TM k m)}) ↔
      v ∈ {v : ↥(shellSub k m W) | (v : ↥(pieceS k m W)) ∈ farTr k m W} := by
  obtain ⟨p, hp⟩ : ∃ p : Torsion.TM k m,
      ((v : ↥(pieceS k m W)) : Torsion.TP k m) = OnePoint.some p := by
    rcases v.2 with ⟨q, -, hq⟩
    exact ⟨q, hq.symm⟩
  have hcoe : ((shellSubHomeo k m W v : ↥((tautologicalBundle k m).proj ⁻¹' W)) :
      Torsion.TM k m) = p := by
    refine Option.some.inj ?_
    calc (OnePoint.some (((shellSubHomeo k m W v :
            ↥((tautologicalBundle k m).proj ⁻¹' W)) : Torsion.TM k m)) : Torsion.TP k m)
        = (v.1.1 : Torsion.TP k m) := shellSubHomeo_apply_coe k m W v
      _ = OnePoint.some p := hp
  constructor
  · intro h
    rw [Set.mem_ofPred_eq] at h
    have h1 : (1 : ℝ) < Torsion.fibN k m p := by rw [← hcoe]; exact h
    show ((v : ↥(pieceS k m W)) : Torsion.TP k m) ∈ Torsion.far k m 1
    rw [hp]
    exact (Torsion.some_mem_far_iff k m 1 p).mpr h1
  · intro h
    rw [Set.mem_ofPred_eq]
    have h1 : (OnePoint.some p : Torsion.TP k m) ∈ Torsion.far k m 1 := by rw [← hp]; exact h
    have h2 : (1 : ℝ) < Torsion.fibN k m p := (Torsion.some_mem_far_iff k m 1 p).mp h1
    show (1 : ℝ) < Torsion.fibN k m
      ((shellSubHomeo k m W v : ↥((tautologicalBundle k m).proj ⁻¹' W)) : Torsion.TM k m)
    rw [hcoe]
    exact h2

/-- **The shell compression in the chart piece**: maps of pairs `(I^d, ∂I^d) → (S, S ∩ far)` are
compressible into `S ∩ far` for `d < k`. -/
theorem compress_shellSub (k m : ℕ) (S₀ : ChartIdx k m) (W : Set (OG k m)) (hW : IsOpen W)
    (hWsub : W ⊆ (tautologicalBundle k m).baseSet S₀) {d : ℕ} (hd : d < k) :
    Compress ↥(shellSub k m W)
      {v : ↥(shellSub k m W) | (v : ↥(pieceS k m W)) ∈ farTr k m W} d :=
  Work.ThomBordism.Grassmann.TwoSet.Compress.of_homeo (shellSubHomeo k m W) (shellSubHomeo_pair k m W)
    (chartPieceShellCompress k m S₀ W hW hWsub d hd)

/-- **The chart piece compresses into the far region.** -/
theorem chartPieceCompressFarCrux (k m : ℕ) (S₀ : ChartIdx k m) (W : Set (OG k m))
    (hW : IsOpen W) (hWsub : W ⊆ (tautologicalBundle k m).baseSet S₀) :
    ∀ j : ℕ, j < k →
      Work.ThomBordism.TwoSet.Compress
        ↥(Torsion.far k m 1 ∪ OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' W))
        {x : ↥(Torsion.far k m 1 ∪ OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' W))
          | (x : Torsion.TP k m) ∈ Torsion.far k m 1} j := by
  classical
  intro j hj
  have hU : IsOpen (farTr k m W) := isOpen_farTr k m W
  have hV : IsOpen (shellSub k m W) := isOpen_shellSub k m W hW
  have hcov : farTr k m W ∪ shellSub k m W = Set.univ := farTr_union_shellSub k m W
  intro f hf
  -- the collared Lebesgue subdivision
  obtain ⟨N, hN3, hsub⟩ := SubdivisionCollared hU hV hcov f hf
  have hN1 : 1 ≤ N := by omega
  -- the labelling: `lab m = true` when the box is *not* (provably) mapped into `far`
  let lab : (Fin j → Fin N) → Bool :=
    fun mm => decide (¬ ∀ x : IC j, x ∈ boxSet mm → f x ∈ farTr k m W)
  have hlabU : ∀ mm, lab mm = false → ∀ x ∈ boxSet mm, f x ∈ farTr k m W := by
    intro mm hm
    have h2 : ¬ ¬ (∀ x : IC j, x ∈ boxSet mm → f x ∈ farTr k m W) := of_decide_eq_false hm
    exact fun x hx => (not_not.mp h2) x hx
  have hlabV : ∀ mm, lab mm = true → ∀ x ∈ boxSet mm, f x ∈ shellSub k m W := by
    intro mm hm x hx
    have hneg : ¬ ∀ x : IC j, x ∈ boxSet mm → f x ∈ farTr k m W := of_decide_eq_true hm
    rcases (hsub mm).1 with h | h
    · exact absurd h hneg
    · exact h x hx
  have hfar : ∀ mm, lab mm = true → ∀ x ∈ boxSet mm, ∀ i,
      2/((N : ℝ)) ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ 1 - 2/((N : ℝ)) := by
    intro mm hm x hx i
    have hneg : ¬ ∀ x : IC j, x ∈ boxSet mm → f x ∈ farTr k m W := of_decide_eq_true hm
    have hnot : ¬ (∃ i, (mm i : ℕ) = 0 ∨ (mm i : ℕ) = 1 ∨ (mm i : ℕ) = N - 2 ∨
        (mm i : ℕ) = N - 1) := by
      rintro ⟨i, hi⟩
      exact hneg fun y hy => (hsub mm).2 ⟨i, hi⟩ y hy
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hmge : 2 ≤ (mm i : ℕ) := by
      by_contra hcon
      exact hnot ⟨i, by omega⟩
    have hmle : (mm i : ℕ) ≤ N - 3 := by
      have h1 : (mm i : ℕ) < N := (mm i).isLt
      by_contra hcon
      exact hnot ⟨i, by omega⟩
    have hxi := hx i
    constructor
    · have h3 : (2 : ℝ) ≤ ((mm i : ℕ) : ℝ) := by exact_mod_cast hmge
      have h4 : (2 : ℝ) ≤ (N : ℝ) * (x i : ℝ) := by linarith [hxi.1]
      exact (div_le_iff₀ hNpos).mpr (by linarith [h4])
    · have h3 : ((mm i : ℕ) + 1 : ℕ) ≤ N - 2 := by omega
      have h4 : (((mm i : ℕ) + 1 : ℕ) : ℝ) ≤ ((N - 2 : ℕ) : ℝ) := by exact_mod_cast h3
      have h5 : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ N)]; norm_num
      rw [h5] at h4
      push_cast at h4
      have h6 : (N : ℝ) * (x i : ℝ) ≤ (N : ℝ) - 2 := by linarith [hxi.2, h4]
      have h7 : (x i : ℝ) ≤ ((N : ℝ) - 2) / N := by
        rw [le_div_iff₀ hNpos]; linarith [h6]
      have h8 : ((N : ℝ) - 2) / N = 1 - 2/(N : ℝ) := by field_simp
      linarith [h7, h8]
  obtain ⟨G, hG0, hGbd, hG1⟩ :=
    processCells2 hN3 lab (fun d hd => compress_shellSub k m S₀ W hW hWsub (lt_of_le_of_lt hd hj))
      hfar f hlabU hlabV hf
  exact ⟨G, hG0, hGbd, hG1⟩

end Work.ThomBordism.Grassmann
