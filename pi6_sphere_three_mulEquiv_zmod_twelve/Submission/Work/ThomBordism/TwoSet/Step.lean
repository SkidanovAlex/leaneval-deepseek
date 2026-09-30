import Submission.Work.ThomBordism.TwoSet.Setup

/-!
# One step of the cell-by-cell compression

`step_general` treats a single grid cell `c`: given the value invariant (`Ac`-cells are `A`-valued,
`Bc`-cells are `B`-valued, ambiguous cells are `A ∩ B`-valued) and the dimension invariant
(`Iinv`), it compresses the values on `c` using the compression hypothesis for the pair
`(A, A ∩ B)` — transported to the cell through `exists_cellHomeo` and `compresses_homeo` — and
spreads the resulting homotopy over the cube with `spreadCell`.  The invariants are preserved,
with the cell `c` added to the list `Q` of treated cells.

`step` is the specialisation to the two typing predicates `Vcell`/`Ucell` of a box labelling.
-/

set_option maxHeartbeats 1000000

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

variable {X : Type*} [TopologicalSpace X] {j N : ℕ} {U V : Set X}

/-- The value invariant of the two-set compression: unambiguous `V`-cells are `V`-valued,
unambiguous `U`-cells are `U`-valued, and ambiguous cells are `U ∩ V`-valued. -/
def Jinv (lab : (Fin j → Fin N) → Bool) (g : C(IC j, X)) : Prop :=
  (∀ d : CellIdx j N, Vcell lab d → ¬ Ucell lab d → ∀ x ∈ cellSet d, g x ∈ V) ∧
  (∀ d : CellIdx j N, Ucell lab d → ¬ Vcell lab d → ∀ x ∈ cellSet d, g x ∈ U) ∧
  (∀ d : CellIdx j N, Vcell lab d → Ucell lab d → ∀ x ∈ cellSet d, g x ∈ U ∩ V)

/-- The dimension invariant: points whose minimal cell is away from the boundary and of dimension
`< Δ` (or of dimension `Δ` and already treated) have values in `W`. -/
def Iinv (W : Set X) (Δ : ℕ) (Q : Finset (CellIdx j N)) (g : C(IC j, X)) : Prop :=
  ∀ x : IC j, Away (cOf N x) →
    (cellDim (cOf N x) < Δ ∨ (cellDim (cOf N x) = Δ ∧ cOf N x ∈ Q)) → g x ∈ W

/-- **One step of the compression.**  Processing the cell `c` (away from the boundary, `A`-typed
and not `B`-typed) preserves both invariants, adding `c` to `Q`. -/
theorem step_general {A B : Set X}
    (hA : ∀ d, d ≤ j → Compress ↥A {a : ↥A | (a : X) ∈ B} d)
    (hN : 1 ≤ N) {Ac Bc : CellIdx j N → Prop}
    (hBmono : ∀ {c c' : CellIdx j N}, (∀ i, c.lo i ≤ c'.lo i ∧ c'.hi i ≤ c.hi i) → Bc c → Bc c')
    {c : CellIdx j N} (hcAway : Away c) (hcA : Ac c) (hcB : ¬ Bc c)
    {Δ : ℕ} (hΔ : cellDim c = Δ) {Q : Finset (CellIdx j N)} {g : C(IC j, X)}
    (hJA : ∀ d, Ac d → ¬ Bc d → ∀ x ∈ cellSet d, g x ∈ A)
    (hJB : ∀ d, Bc d → ¬ Ac d → ∀ x ∈ cellSet d, g x ∈ B)
    (hJAB : ∀ d, Ac d → Bc d → ∀ x ∈ cellSet d, g x ∈ A ∩ B)
    (hI : Iinv (A ∩ B) Δ Q g) :
    ∃ (g' : C(IC j, X)) (G : C(IC j × I, X)),
      (∀ x, G (x, 0) = g x) ∧
      (∀ x, x ∈ Cube.boundary (Fin j) → ∀ t, G (x, t) = g x) ∧
      (∀ x, G (x, 1) = g' x) ∧
      (∀ d, Ac d → ¬ Bc d → ∀ x ∈ cellSet d, g' x ∈ A) ∧
      (∀ d, Bc d → ¬ Ac d → ∀ x ∈ cellSet d, g' x ∈ B) ∧
      (∀ d, Ac d → Bc d → ∀ x ∈ cellSet d, g' x ∈ A ∩ B) ∧
      Iinv (A ∩ B) Δ (insert c Q) g' := by
  classical
  have hdj : cellDim c ≤ j := by
    rw [cellDim]
    simpa using Finset.card_le_univ (Finset.univ.filter fun i : Fin j => c.lo i < c.hi i)
  obtain ⟨e, he⟩ := exists_cellHomeo hN c
  have hcellA : ∀ x ∈ cellSet c, g x ∈ A := hJA c hcA hcB
  let f : C(cellSet c, ↥A) := ⟨fun z => ⟨g z, hcellA z z.2⟩,
    Continuous.subtype_mk (g.continuous.comp continuous_subtype_val) _⟩
  have hfb : ∀ z : cellSet c,
      z ∈ ({z : cellSet c | ((z : IC j) ∈ cellRelbd c)} : Set (cellSet c)) →
      f z ∈ {a : ↥A | (a : X) ∈ B} := by
    intro z hz
    exact (hI (z : IC j) (Away_mono (cellSet_cOf_subset hN c z.2) hcAway)
      (Or.inl (by rw [← hΔ]; exact cellDim_cOf_lt_of_mem_cellRelbd N hN hz z.2))).2
  obtain ⟨Gc, hGc0, hGcbd, hGc1⟩ := compresses_homeo (hA (cellDim c) hdj) e
    ({z : cellSet c | ((z : IC j) ∈ cellRelbd c)} : Set (cellSet c)) he f hfb
  let H : C(cellSet c × unitInterval, X) :=
    ⟨fun p => (Gc p : X), continuous_subtype_val.comp Gc.continuous⟩
  have hH0 : ∀ z : cellSet c, H (z, 0) = g z := fun z => congrArg Subtype.val (hGc0 z)
  have hHbd : ∀ (z : cellSet c), ((z : IC j) ∈ cellRelbd c) → ∀ t, H (z, t) = g z :=
    fun z hz t => congrArg Subtype.val (hGcbd z hz t)
  have hHA : ∀ z : cellSet c, ∀ t : unitInterval, H (z, t) ∈ A := fun z t => (Gc (z, t)).2
  have hHB : ∀ z : cellSet c, H (z, 1) ∈ B := fun z => hGc1 z
  obtain ⟨G, hG0, hGcell, hGzero, hG4, hG5, hG6⟩ := spreadCell c hN g H hH0 hHbd
  let g' : C(IC j, X) := ⟨fun x => G (x, 1),
    G.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hclampmem : ∀ {x : IC j}, clampCell c hN x ∈ cellRelbd c → g (clampCell c hN x) ∈ A ∩ B := by
    intro x hbd
    exact hI (clampCell c hN x)
      (Away_mono (cellSet_cOf_subset hN c (clampCell_mem c hN x)) hcAway)
      (Or.inl (by rw [← hΔ]; exact cellDim_cOf_lt_of_mem_cellRelbd N hN hbd (clampCell_mem c hN x)))
  have hsub : ∀ {d : CellIdx j N} {x : IC j}, x ∈ cellSet d →
      ∀ y ∈ cellSet (cOf N x), y ∈ cellSet d := fun hx y hy =>
    cellSet_antitone (fun i => (cellSet_cOf_subset hN _ hx i).1) (fun i => (cellSet_cOf_subset hN _ hx i).2) hy
  -- the key lemma consequence: `c ⊆ d` for a `c`-close point of `d`
  have hkeycell : ∀ {d : CellIdx j N} {x : IC j}, x ∈ cellSet d → x ∉ cellSet c →
      0 < nuOf c x → clampCell c hN x ∉ cellRelbd c →
      ∀ i, d.lo i ≤ c.lo i ∧ c.hi i ≤ d.hi i := by
    intro d x hx hxc hpos hbd i
    have hkey := keyLemma hN c (close_of_nuOf_pos c hpos) hbd
    exact ⟨le_trans (cellSet_cOf_subset hN d hx i).1 (hkey.1 i),
      le_trans (hkey.2.1 i) (cellSet_cOf_subset hN d hx i).2⟩
  refine ⟨g', G, hG0, ?_, fun x => rfl, ?_, ?_, ?_, ?_⟩
  · intro x hx t
    rw [hGzero x (nuOf_eq_zero_of_away_of_mem_boundary hN hcAway hx) t]
  · intro d hdA hdB x hx
    change G (x, 1) ∈ A
    by_cases hc : x ∈ cellSet c
    · rw [hGcell ⟨x, hc⟩ 1]
      exact hHA ⟨x, hc⟩ 1
    · by_cases hnu : nuOf c x = 0
      · rw [hGzero x hnu 1]
        exact hJA d hdA hdB x hx
      · have hpos : 0 < nuOf c x := lt_of_le_of_ne (nuOf_nonneg c x) (Ne.symm hnu)
        rcases le_or_gt (rOf c x) (nuOf c x) with hle | hlt
        · by_cases hbd : clampCell c hN x ∈ cellRelbd c
          · rw [hG5 x hc hpos hle hbd]
            exact (hclampmem hbd).1
          · rcases hG4 x hc hpos hle with ⟨z, hz, s, hval⟩
            rw [hval]
            exact hHA ⟨z, hz⟩ s
        · rcases hG6 x hc hpos hlt with ⟨y, hy, hval⟩
          rw [hval]
          exact hJA d hdA hdB y (hsub hx y hy)
  · intro d hdB hdA x hx
    change G (x, 1) ∈ B
    by_cases hc : x ∈ cellSet c
    · rw [hGcell ⟨x, hc⟩ 1]
      exact hHB ⟨x, hc⟩
    · by_cases hnu : nuOf c x = 0
      · rw [hGzero x hnu 1]
        exact hJB d hdB hdA x hx
      · have hpos : 0 < nuOf c x := lt_of_le_of_ne (nuOf_nonneg c x) (Ne.symm hnu)
        rcases le_or_gt (rOf c x) (nuOf c x) with hle | hlt
        · by_cases hbd : clampCell c hN x ∈ cellRelbd c
          · rw [hG5 x hc hpos hle hbd]
            exact (hclampmem hbd).2
          · exact absurd (hBmono (hkeycell hx hc hpos hbd) hdB) hcB
        · rcases hG6 x hc hpos hlt with ⟨y, hy, hval⟩
          rw [hval]
          exact hJB d hdB hdA y (hsub hx y hy)
  · intro d hdA hdB x hx
    change G (x, 1) ∈ A ∩ B
    by_cases hc : x ∈ cellSet c
    · rw [hGcell ⟨x, hc⟩ 1]
      exact ⟨hHA ⟨x, hc⟩ 1, hHB ⟨x, hc⟩⟩
    · by_cases hnu : nuOf c x = 0
      · rw [hGzero x hnu 1]
        exact hJAB d hdA hdB x hx
      · have hpos : 0 < nuOf c x := lt_of_le_of_ne (nuOf_nonneg c x) (Ne.symm hnu)
        rcases le_or_gt (rOf c x) (nuOf c x) with hle | hlt
        · by_cases hbd : clampCell c hN x ∈ cellRelbd c
          · rw [hG5 x hc hpos hle hbd]
            exact hclampmem hbd
          · exact absurd (hBmono (hkeycell hx hc hpos hbd) hdB) hcB
        · rcases hG6 x hc hpos hlt with ⟨y, hy, hval⟩
          rw [hval]
          exact hJAB d hdA hdB y (hsub hx y hy)
  · intro x hAw hd
    change G (x, 1) ∈ A ∩ B
    by_cases hc : x ∈ cellSet c
    · rw [hGcell ⟨x, hc⟩ 1]
      exact ⟨hHA ⟨x, hc⟩ 1, hHB ⟨x, hc⟩⟩
    · by_cases hnu : nuOf c x = 0
      · rw [hGzero x hnu 1]
        refine hI x hAw ?_
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
          refine hI y (Away_mono (cellSet_cOf_subset hN (cOf N x) hy) hAw) ?_
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

/-- **Processing one cell.** -/
theorem step {lab : (Fin j → Fin N) → Bool} (hN : 1 ≤ N)
    (hVc : ∀ d, d ≤ j → Compress ↥V {v : ↥V | (v : X) ∈ U} d)
    (hUc : ∀ d, d ≤ j → Compress ↥U {u : ↥U | (u : X) ∈ V} d)
    {c : CellIdx j N} (hcAway : Away c)
    (hcType : (Vcell lab c ∧ ¬ Ucell lab c) ∨ (Ucell lab c ∧ ¬ Vcell lab c))
    {Δ : ℕ} (hΔ : cellDim c = Δ) {Q : Finset (CellIdx j N)} {g : C(IC j, X)}
    (hJ : Jinv (U := U) (V := V) lab g) (hI : Iinv (U ∩ V) Δ Q g) :
    ∃ (g' : C(IC j, X)) (G : C(IC j × I, X)),
      (∀ x, G (x, 0) = g x) ∧
      (∀ x, x ∈ Cube.boundary (Fin j) → ∀ t, G (x, t) = g x) ∧
      (∀ x, G (x, 1) = g' x) ∧
      Jinv (U := U) (V := V) lab g' ∧ Iinv (U ∩ V) Δ (insert c Q) g' := by
  rcases hcType with ⟨hcV, hcU⟩ | ⟨hcU, hcV⟩
  · obtain ⟨g', G, h0, h1, h2, hrest⟩ :=
      step_general (A := V) (B := U) (Ac := Vcell lab) (Bc := Ucell lab) hVc hN
        (fun hcd hc => Ucell_mono hN hcd hc) hcAway hcV hcU hΔ hJ.1 hJ.2.1
        (fun d h1 h2 x hx => by have := hJ.2.2 d h1 h2 x hx; rwa [Set.inter_comm] at this)
        (fun x hx hd => by have := hI x hx hd; rwa [Set.inter_comm] at this)
    refine ⟨g', G, h0, h1, h2, ⟨hrest.1, hrest.2.1, ?_⟩, ?_⟩
    · intro d h1' h2' x hx
      have := hrest.2.2.1 d h1' h2' x hx
      rwa [Set.inter_comm] at this
    · intro x hx hd
      have := hrest.2.2.2 x hx hd
      rwa [Set.inter_comm] at this
  · obtain ⟨g', G, h0, h1, h2, hrest⟩ :=
      step_general (A := U) (B := V) (Ac := Ucell lab) (Bc := Vcell lab) hUc hN
        (fun hcd hc => Vcell_mono hN hcd hc) hcAway hcU hcV hΔ hJ.2.1 hJ.1
        (fun d h1 h2 x hx => hJ.2.2 d h2 h1 x hx) hI
    exact ⟨g', G, h0, h1, h2, ⟨hrest.2.1, hrest.1,
      fun d h1' h2' x hx => hrest.2.2.1 d h2' h1' x hx⟩, hrest.2.2.2⟩

end Work.ThomBordism.TwoSet
