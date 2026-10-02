import Mathlib
import Submission.Work.RatHurewicz.Triad.Rule
import Submission.Work.RatHurewicz.exists_cutoffs_collar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Structural facts about the grid, and the labelling of the faces

* the subcell relation is a partial order; a proper face of a cell lies on its relative boundary;
* a point of the collared support `cellStarCollar c ε` (`N ε < 1`) whose clamp onto `c` is in the
  relative interior of `c` has `c` as a subcell of its owner;
* the cells of the wall, the final face and the initial face are labelled by
  `B`, `C`, `B ∩ C` respectively, by admissibility of `Φ`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

open Work.ThomBordism.TwoSet

noncomputable section

variable {X : Type} [TopologicalSpace X] {B C : Set X} {x₀ : ↥(B ∩ C)}
  {j N : ℕ} {n p q : ℕ}

section Subcell

theorem Subcell.trans {c c' c'' : CellIdx j N} (h : Subcell c c') (h' : Subcell c' c'') :
    Subcell c c'' :=
  ⟨fun i => le_trans (h'.1 i) (h.1 i), fun i => le_trans (h.2 i) (h'.2 i)⟩

theorem Subcell.eq_of_antisymm {c c' : CellIdx j N} (h : Subcell c c') (h' : Subcell c' c) :
    c = c' := by
  have h1 : c.lo = c'.lo := funext fun i => le_antisymm (h'.1 i) (h.1 i)
  have h2 : c.hi = c'.hi := funext fun i => le_antisymm (h.2 i) (h'.2 i)
  cases c; cases c'; simp_all

/-- If a point lies in two cells and not on the relative boundary of the first, then the second
cell is a subcell of the first. -/
theorem subcell_of_mem_inter_of_not_mem_cellRelbd {c c' : CellIdx j N} {x : IC j}
    (hx : x ∈ cellSet c) (hx' : x ∈ cellSet c') (h : x ∉ cellRelbd c) : Subcell c c' := by
  obtain ⟨hlo, hhi⟩ := cOf_sub_of_mem_cellSet hx'
  obtain ⟨e1, e2⟩ := lo_hi_eq_cOf_of_mem_cellSet_of_not_mem_cellRelbd hx h
  exact ⟨fun i => by rw [e1 i]; exact hlo i, fun i => by rw [e2 i]; exact hhi i⟩

/-- **A proper face of a cell lies on its relative boundary.** -/
theorem cellSet_subset_cellRelbd {c c' : CellIdx j N} (h : Subcell c c') (hne : c ≠ c') :
    cellSet c ⊆ cellRelbd c' := by
  intro x hx
  by_contra hcon
  have hx' : x ∈ cellSet c' := cellSet_subcell h hx
  have heq := lo_hi_eq_cOf_of_mem_cellSet_of_not_mem_cellRelbd hx' hcon
  have h1 : c'.lo = (cOf N x).lo := funext fun i => heq.1 i
  have h2 : c'.hi = (cOf N x).hi := funext fun i => heq.2 i
  have hsub : Subcell c' c := by
    rw [show c' = cOf N x from by cases c'; simp_all]
    exact cOf_sub_of_mem_cellSet hx
  exact hne (Subcell.eq_of_antisymm h hsub)

end Subcell

section Collar

/-- The clamp of a point of the collared support onto the cell lies in its owner cell. -/
theorem clamp_mem_cellSet_cOf {c : CellIdx j N} {ε : ℝ} (hN : 1 ≤ N) (hεN : (N : ℝ) * ε ≤ 1 / 2)
    {x : IC j} (hx : x ∈ cellStarCollar c ε) : clampCell c hN x ∈ cellSet (cOf N x) := by
  have h := segMap_clamp_mem_cellSet (c := c) (c' := cOf N x) hN hεN hx (mem_cOf N hN x) 1
  simpa using h

/-- A point of the collared support of `c` (`N ε < 1`) whose clamp onto `c` is in the relative
interior of `c` has `c` as a subcell of its owner cell. -/
theorem subcell_of_collar_clamp_relint {c : CellIdx j N} {ε : ℝ} (hN : 1 ≤ N)
    (hε1 : (N : ℝ) * ε < 1) {x : IC j} (hx : x ∈ cellStarCollar c ε)
    (hclamp : clampCell c hN x ∈ cellRelint c) : Subcell c (cOf N x) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcl := hclamp.2
  have key : ∀ i, (cOf N x).lo i ≤ c.lo i ∧ c.hi i ≤ (cOf N x).hi i := by
    intro i
    by_cases hint : c.lo i < c.hi i
    · have hne1 : ((clampCell c hN x i : unitInterval) : ℝ) ≠ (c.lo i : ℝ) / N := by
        intro hcon
        exact hcl (by rw [mem_cellRelbd]; exact ⟨i, hint, Or.inl hcon⟩)
      have hne2 : ((clampCell c hN x i : unitInterval) : ℝ) ≠ (c.hi i : ℝ) / N := by
        intro hcon
        exact hcl (by rw [mem_cellRelbd]; exact ⟨i, hint, Or.inr hcon⟩)
      have hne1' : clampR N (c.lo i) (c.hi i) (x i : ℝ) ≠ (c.lo i : ℝ) / N := by
        intro hcon; exact hne1 (by rw [clampCell_val]; exact hcon)
      have hne2' : clampR N (c.lo i) (c.hi i) (x i : ℝ) ≠ (c.hi i : ℝ) / N := by
        intro hcon; exact hne2 (by rw [clampCell_val]; exact hcon)
      have hinter := clampR_inl_interior hN hint (c.hhi i) (x i).2 hne1' hne2'
      have hstep : c.hi i = c.lo i + 1 := by have := c.hstep i; omega
      have hstepR : (c.hi i : ℝ) = (c.lo i : ℝ) + 1 := by rw [hstep]; push_cast; ring
      have hlt1 : (c.lo i : ℝ) < (N : ℝ) * (x i : ℝ) := by
        have h := hinter.1; rw [div_lt_iff₀ hNpos] at h; linarith
      have hlt2 : (N : ℝ) * (x i : ℝ) < (c.hi i : ℝ) := by
        have h := hinter.2; rw [lt_div_iff₀ hNpos] at h; linarith
      constructor
      · rw [cOf_lo]
        have := (Nat.floor_lt (mul_nonneg (le_of_lt hNpos) (x i).2.1)).mpr
          (show (N : ℝ) * (x i : ℝ) < (((c.lo i + 1 : ℕ)) : ℝ) by
            push_cast; linarith [hlt2, hstepR])
        omega
      · rw [cOf_hi]
        have hlt : (((c.hi i - 1 : ℕ)) : ℝ) < (N : ℝ) * (x i : ℝ) := by
          have hcast : (((c.hi i - 1 : ℕ)) : ℝ) = (c.hi i : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ c.hi i)]; norm_num
          have hlo : (c.lo i : ℝ) = (c.hi i : ℝ) - 1 := by rw [hstep]; push_cast; ring
          rw [hlo] at hlt1
          rwa [hcast]
        have := (Nat.lt_ceil).mpr hlt
        omega
    · have hnode : c.lo i = c.hi i := le_antisymm (c.hle i) (not_lt.mp hint)
      have h1 := hx i
      have hmul := mul_le_mul_of_nonneg_left h1.2 (le_of_lt hNpos)
      have hmul2 := mul_le_mul_of_nonneg_left h1.1 (le_of_lt hNpos)
      have heq : (N : ℝ) * (((c.hi i : ℝ)) / N + ε) = (c.hi i : ℝ) + (N : ℝ) * ε := by
        field_simp
      have heq2 : (N : ℝ) * (((c.lo i : ℝ)) / N - ε) = (c.lo i : ℝ) - (N : ℝ) * ε := by
        field_simp
      have hupper : (N : ℝ) * (x i : ℝ) < (((c.lo i + 1 : ℕ)) : ℝ) := by
        rw [heq, ← hnode] at hmul; push_cast; linarith
      have hlower : (c.lo i : ℝ) - 1 < (N : ℝ) * (x i : ℝ) := by
        rw [heq2] at hmul2; linarith
      constructor
      · rw [cOf_lo]
        have := (Nat.floor_lt (mul_nonneg (le_of_lt hNpos) (x i).2.1)).mpr hupper
        omega
      · rw [cOf_hi, ← hnode]
        rcases Nat.eq_zero_or_pos (c.lo i) with hz | hpos
        · rw [hz]; exact Nat.zero_le _
        · have hcast : (((c.lo i - 1 : ℕ)) : ℝ) = (c.lo i : ℝ) - 1 := by
            rw [Nat.cast_sub hpos]; norm_num
          have hlt : ((c.lo i - 1 : ℕ) : ℝ) < (N : ℝ) * (x i : ℝ) := by
            rw [hcast]; exact hlower
          have := (Nat.lt_ceil).mpr hlt
          omega
  exact ⟨fun i => (key i).1, fun i => (key i).2⟩

end Collar

section Faces

/-- A point whose space coordinate `i` is `0` or `1` lies in the wall, and its owner cell is
labelled `B`. -/
theorem cellB_of_wall {N : ℕ} {Φ : C(IC (n + 1), X)} (hadm : TriadAdmissible B C x₀ Φ)
    {z : IC (n + 1)} {i : Fin n} (hN : 1 ≤ N)
    (hi : z i.castSucc = 0 ∨ z i.castSucc = 1) : CellB B Φ (cOf N z) := by
  have hNne : ((N : ℝ)) ≠ 0 := by positivity
  intro y hy
  have hcoord : y i.castSucc = 0 ∨ y i.castSucc = 1 := by
    rcases hi with h | h
    · left
      have h0 : ((z i.castSucc : unitInterval) : ℝ) = ((0 : ℕ) : ℝ) / N := by rw [h]; norm_num
      have := coord_eq_of_mem_cellSet_cOf (j := n + 1) hN (Nat.zero_le N) h0 hy
      exact Subtype.ext (by simpa using this)
    · right
      have h0 : ((z i.castSucc : unitInterval) : ℝ) = ((N : ℕ) : ℝ) / N := by
        rw [h]
        show (1 : ℝ) = ((N : ℕ) : ℝ) / N
        exact (div_self hNne).symm
      have hthis := coord_eq_of_mem_cellSet_cOf (j := n + 1) hN (le_refl N) h0 hy
      exact Subtype.ext (by rw [hthis]; exact div_self hNne)
  have hbd : initC n y ∈ Cube.boundary (Fin n) := ⟨i, hcoord⟩
  have hval := hadm.2.2 (initC n y) hbd (y (Fin.last n))
  rwa [snoc_initC] at hval

/-- A point with last coordinate `1` has its owner cell labelled `C`. -/
theorem cellC_of_final {N : ℕ} {Φ : C(IC (n + 1), X)} (hadm : TriadAdmissible B C x₀ Φ)
    {z : IC (n + 1)} (hN : 1 ≤ N) (hz : z (Fin.last n) = 1) : CellC C Φ (cOf N z) := by
  have hNne : ((N : ℝ)) ≠ 0 := by positivity
  intro y hy
  have hcoord : y (Fin.last n) = 1 := by
    have h0 : ((z (Fin.last n) : unitInterval) : ℝ) = ((N : ℕ) : ℝ) / N := by
      rw [hz]
      show (1 : ℝ) = ((N : ℕ) : ℝ) / N
      exact (div_self hNne).symm
    have hthis := coord_eq_of_mem_cellSet_cOf (j := n + 1) hN (le_refl N) h0 hy
    exact Subtype.ext (by rw [hthis]; exact div_self hNne)
  have hval := hadm.2.1 (initC n y)
  rw [← hcoord, snoc_initC] at hval
  exact hval

/-- A point with last coordinate `0` has its owner cell labelled both `B` and `C`. -/
theorem cellBC_of_init {N : ℕ} {Φ : C(IC (n + 1), X)} (hadm : TriadAdmissible B C x₀ Φ)
    {z : IC (n + 1)} (hN : 1 ≤ N) (hz : z (Fin.last n) = 0) :
    CellB B Φ (cOf N z) ∧ CellC C Φ (cOf N z) := by
  have hcoord : ∀ y ∈ cellSet (cOf N z), y (Fin.last n) = 0 := by
    intro y hy
    have h0 : ((z (Fin.last n) : unitInterval) : ℝ) = ((0 : ℕ) : ℝ) / N := by
      rw [hz]; norm_num
    have := coord_eq_of_mem_cellSet_cOf (j := n + 1) hN (Nat.zero_le N) h0 hy
    exact Subtype.ext (by simpa using this)
  constructor
  · intro y hy
    have hval := hadm.1 (initC n y)
    rw [← hcoord y hy, snoc_initC] at hval
    exact hval ▸ x₀.2.1
  · intro y hy
    have hval := hadm.1 (initC n y)
    rw [← hcoord y hy, snoc_initC] at hval
    exact hval ▸ x₀.2.2

/-- Subcells have no more interval directions. -/
theorem cellDim_le_of_subcell {c c' : CellIdx j N} (h : Subcell c c') : cellDim c ≤ cellDim c' := by
  have hsub : (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)) ⊆
      (Finset.univ.filter (fun i : Fin j => c'.lo i < c'.hi i)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact lt_of_le_of_lt (h.1 i) (lt_of_lt_of_le hi (h.2 i))
  rw [cellDim, cellDim]
  exact Finset.card_le_card hsub

/-- Two subcells of the same dimension are equal. -/
theorem Subcell.eq_of_cellDim_eq {c c' : CellIdx j N} (h : Subcell c c')
    (hd : cellDim c = cellDim c') : c = c' := by
  have hint : ∀ i, (c.lo i < c.hi i ↔ c'.lo i < c'.hi i) := by
    have hsub : (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)) ⊆
        (Finset.univ.filter (fun i : Fin j => c'.lo i < c'.hi i)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact lt_of_le_of_lt (h.1 i) (lt_of_lt_of_le hi (h.2 i))
    have hset : (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)) =
        (Finset.univ.filter (fun i : Fin j => c'.lo i < c'.hi i)) := by
      refine Finset.eq_of_subset_of_card_le hsub ?_
      rw [show (Finset.univ.filter (fun i : Fin j => c'.lo i < c'.hi i)).card = cellDim c' from rfl,
        show (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)).card = cellDim c from rfl,
        ← hd]
    intro i
    constructor
    · intro hi
      have h1 : i ∈ (Finset.univ.filter (fun k : Fin j => c.lo k < c.hi k)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi
      rw [hset] at h1
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h1
    · intro hi
      have h1 : i ∈ (Finset.univ.filter (fun k : Fin j => c'.lo k < c'.hi k)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi
      rw [← hset] at h1
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h1
  have hlo : c.lo = c'.lo := by
    funext i
    rcases lt_or_ge (c.lo i) (c.hi i) with hi | hi
    · have h1 : c'.lo i < c'.hi i := (hint i).mp hi
      have e1 : c'.hi i = c'.lo i + 1 := by have := c'.hstep i; omega
      have e2 : c.hi i = c.lo i + 1 := by have := c.hstep i; omega
      have h4 := h.1 i
      have h5 := h.2 i
      omega
    · have h2 : c.lo i = c.hi i := le_antisymm (c.hle i) hi
      have h3 : ¬ (c'.lo i < c'.hi i) := fun hcon => absurd ((hint i).mpr hcon) (by omega)
      have h3' : c'.lo i = c'.hi i := le_antisymm (c'.hle i) (not_lt.mp h3)
      have h4 := h.1 i
      have h5 := h.2 i
      omega
  have hhi : c.hi = c'.hi := by
    funext i
    rcases lt_or_ge (c.lo i) (c.hi i) with hi | hi
    · have h1 : c'.lo i < c'.hi i := (hint i).mp hi
      have h4 : c.lo i = c'.lo i := by rw [hlo]
      have e1 : c'.hi i = c'.lo i + 1 := by have := c'.hstep i; omega
      have e2 : c.hi i = c.lo i + 1 := by have := c.hstep i; omega
      omega
    · have h2 : c.lo i = c.hi i := le_antisymm (c.hle i) hi
      have h3 : ¬ (c'.lo i < c'.hi i) := fun hcon => absurd ((hint i).mpr hcon) (by omega)
      have h3' : c'.lo i = c'.hi i := le_antisymm (c'.hle i) (not_lt.mp h3)
      have h4 := h.1 i
      have h5 := h.2 i
      omega
  cases c; cases c'; simp_all

/-- A cell all of whose points have last coordinate `0` is labelled by both `B` and `C`. -/
theorem cellBC_of_node_last_zero {N : ℕ} {Φ : C(IC (n + 1), X)}
    (hadm : TriadAdmissible B C x₀ Φ) {c : CellIdx (n + 1) N}
    (hc : c.lo (Fin.last n) = 0 ∧ c.hi (Fin.last n) = 0) :
    CellB B Φ c ∧ CellC C Φ c := by
  have hcoord : ∀ y ∈ cellSet c, y (Fin.last n) = 0 := by
    intro y hy
    have h1 := (mem_cellSet.mp hy (Fin.last n)).1
    have h2 := (mem_cellSet.mp hy (Fin.last n)).2
    rw [hc.1] at h1; rw [hc.2] at h2
    have h1' : (0:ℝ) ≤ (y (Fin.last n) : ℝ) := by simpa using h1
    have h2' : (y (Fin.last n) : ℝ) ≤ 0 := by simpa using h2
    exact Subtype.ext (le_antisymm h2' h1')
  constructor
  · intro y hy
    have hval := hadm.1 (initC n y)
    rw [← hcoord y hy, snoc_initC] at hval
    exact hval ▸ x₀.2.1
  · intro y hy
    have hval := hadm.1 (initC n y)
    rw [← hcoord y hy, snoc_initC] at hval
    exact hval ▸ x₀.2.2

/-- A point of the wall has its value in `B` if the map is `CellB`-valued on its cells. -/
theorem valB_of_wall {N : ℕ} {Φ g : C(IC (n + 1), X)} (hadm : TriadAdmissible B C x₀ Φ)
    (hVB : ValsB (N := N) B Φ g) {z : IC (n + 1)} {i : Fin n} (hN : 1 ≤ N)
    (hi : z i.castSucc = 0 ∨ z i.castSucc = 1) : g z ∈ B :=
  hVB (cOf N z) (cellB_of_wall hadm hN hi) z (mem_cOf N hN z)

/-- A point of the final face has its value in `C` if the map is `CellC`-valued on its cells. -/
theorem valC_of_final {N : ℕ} {Φ g : C(IC (n + 1), X)} (hadm : TriadAdmissible B C x₀ Φ)
    (hVC : ValsC (N := N) C Φ g) {z : IC (n + 1)} (hN : 1 ≤ N) (hz : z (Fin.last n) = 1) :
    g z ∈ C :=
  hVC (cOf N z) (cellC_of_final hadm hN hz) z (mem_cOf N hN z)

end Faces

end

end Work.RatHurewicz.Triad
