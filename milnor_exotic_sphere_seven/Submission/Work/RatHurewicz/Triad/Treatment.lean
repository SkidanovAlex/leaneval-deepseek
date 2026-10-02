import Mathlib
import Submission.Work.RatHurewicz.Triad.Rule
import Submission.Work.RatHurewicz.Triad.Structural
import Submission.Work.RatHurewicz.exists_cellTreatmentOf
import Submission.Work.RatHurewicz.exists_cutoffs_collar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The treatment of one cell, and the invariants

A **treatment** of a grid cell `c` is a homotopy `G` of the whole cube which
* is the identity outside the collared support `cellStarCollar c ε`;
* on the support is given by the two-phase formula of `exists_cellTreatmentOf`: before the flow
  `1 ≤ s·μ x` arrives it is the current map at the flow point, afterwards the cell homotopy `H` at
  the clamp of `x`;
and whose cell homotopy has the properties the induction needs (its values lie in `B` on a `CellB`
cell and in `C` on its complement, and its time-`1` values satisfy the clauses `ConClauses`).

`Treat.damage` describes every value of the treatment: it is the old value, or a value of the old
map at a point of the owner cell of `x`, or a value of the cell homotopy at (the clamp of) `x`.
From it the file proves the invariance of `ValsB`, `ValsC`, `InitFace` and the staged clauses
`ConClauses` for the cells of dimension at most that of the treated cell.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

open Work.ThomBordism.TwoSet

noncomputable section

variable {X : Type} [TopologicalSpace X] {B C : Set X} {x₀ : ↥(B ∩ C)} {N : ℕ} {n p q : ℕ}

/-- **A treatment of the cell `c`.** -/
structure Treat (hN : 1 ≤ N) (B C : Set X) (x₀ : ↥(B ∩ C)) (Φ g : C(IC (n + 1), X)) (p q : ℕ)
    (c : CellIdx (n + 1) N) (ε : ℝ) where
  hadm : TriadAdmissible B C x₀ Φ
  hnotboth : ¬ (CellB B Φ c ∧ CellC C Φ c)
  G : C(IC (n + 1) × I, X)
  gs : ∀ s : I, C(IC (n + 1), X)
  hgs : ∀ s z, gs s z = G (z, s)
  H : C(cellSet c × I, X)
  μ : C(IC (n + 1), ℝ)
  ν : C(IC (n + 1), I)
  hμ0 : ∀ x, x ∉ cellStarCollar c ε → μ x = 0
  hμ2 : ∀ x, x ∈ cellSet c → 2 ≤ μ x
  hν1 : ∀ x, x ∈ cellSet c → ν x = 1
  hform : ∀ x s, G (x, s) = if (s : ℝ) * μ x ≤ 1 then g (flowCell c hN μ x s)
      else H (⟨clampCell c hN x, clampCell_mem c hN x⟩, pushTime μ ν x s)
  hH0 : ∀ u : cellSet c, H (u, 0) = g u
  hHbd : ∀ (u : cellSet c), (u : IC (n + 1)) ∈ cellRelbd c → ∀ t, H (u, t) = g u
  hHvalsB : CellB B Φ c → ∀ u t, (H (u, t) : X) ∈ B
  hHvalsC : ¬ CellB B Φ c → ∀ u t, (H (u, t) : X) ∈ C
  hcon1 : CellB B Φ c → ¬ CellC C Φ c → cellDim c ≤ p + 1 →
    ∀ z, z ∈ cellSet c → gs 1 z ∈ B ∩ C
  hcon2 : CellB B Φ c → ¬ CellC C Φ c → p + 1 < cellDim c →
    ∀ z, z ∈ cellSet c → gs 1 z ∉ C → KW N (p + 2) c z
  hcon3 : ¬ CellB B Φ c → CellC C Φ c → cellDim c ≤ q + 1 →
    ∀ z, z ∈ cellSet c → gs 1 z ∈ B ∩ C
  hcon4 : ¬ CellB B Φ c → CellC C Φ c → q + 1 < cellDim c →
    ∀ z, z ∈ cellSet c → gs 1 z ∉ B → GW N (q + 2) c z

namespace Treat

variable {hN : 1 ≤ N} {Φ g : C(IC (n + 1), X)} {c : CellIdx (n + 1) N} {ε : ℝ}

/-- Off the collared support the treatment is the identity. -/
theorem off (T : Treat hN B C x₀ Φ g p q c ε) (x : IC (n + 1)) (hx : x ∉ cellStarCollar c ε)
    (s : I) : T.G (x, s) = g x := by
  have h0 : T.μ x = 0 := T.hμ0 x hx
  rw [T.hform, if_pos (by rw [h0, mul_zero]; norm_num),
    flowCell_eq_self_of_mu_eq_zero hN h0 s]

/-- At time `0` the treatment is the identity. -/
theorem gs_zero (T : Treat hN B C x₀ Φ g p q c ε) (z : IC (n + 1)) : T.gs 0 z = g z := by
  rw [T.hgs, T.hform]
  simp

/-- **The damage lemma.**  A treatment changes the value at `x` at time `s` only into the old value,
a value of the old map on the flow segment from `x` to its clamp, a value of the cell homotopy at
`x` itself, or a value of the cell homotopy at the clamp of `x`. -/
theorem damage (T : Treat hN B C x₀ Φ g p q c ε) (hεN : (N : ℝ) * ε ≤ 1 / 2)
    (x : IC (n + 1)) (s : I) :
    T.G (x, s) = g x ∨
    (x ∈ cellStarCollar c ε ∧ ∃ τ : I,
      T.G (x, s) = g (segMap x (clampCell c hN x) τ)) ∨
    (∃ (hx : x ∈ cellSet c) (τ : I), T.G (x, s) = T.H (⟨x, hx⟩, τ)) ∨
    (x ∈ cellStarCollar c ε ∧ ∃ τ : I,
      T.G (x, s) = T.H (⟨clampCell c hN x, clampCell_mem c hN x⟩, τ) ∧
        clampCell c hN x ∈ cellRelint c) := by
  by_cases hS : x ∈ cellStarCollar c ε
  · by_cases h1 : (s : ℝ) * T.μ x ≤ 1
    · refine Or.inr (Or.inl ⟨hS, flowParam T.μ x s, ?_⟩)
      rw [T.hform, if_pos h1]
      rfl
    · push_neg at h1
      by_cases hxc : x ∈ cellSet c
      · refine Or.inr (Or.inr (Or.inl ⟨hxc, pushTime T.μ T.ν x s, ?_⟩))
        rw [T.hform, if_neg (not_le.mpr h1)]
        rw [show (⟨clampCell c hN x, clampCell_mem c hN x⟩ : cellSet c) = ⟨x, hxc⟩ from
          Subtype.ext (clampCell_eq_self c hN hxc)]
      · rw [T.hform, if_neg (not_le.mpr h1)]
        by_cases hbd : clampCell c hN x ∈ cellRelbd c
        · refine Or.inr (Or.inl ⟨hS, 1, ?_⟩)
          rw [segMap_one, T.hHbd ⟨clampCell c hN x, clampCell_mem c hN x⟩ hbd
              (pushTime T.μ T.ν x s)]
        · exact Or.inr (Or.inr (Or.inr ⟨hS, pushTime T.μ T.ν x s, rfl,
            ⟨clampCell_mem c hN x, hbd⟩⟩))
  · left
    exact T.off x hS s

/-- **The initial face stays fixed.** -/
theorem maintain_InitFace (T : Treat hN B C x₀ Φ g p q c ε) (hε : (N : ℝ) * ε < 1 / 2)
    (hInit : InitFace (x₀ : X) g) (s : I) : InitFace (x₀ : X) (T.gs s) := by
  intro x hx0
  rw [T.hgs]
  rcases T.damage (le_of_lt hε) x s with h | ⟨hS, τ', heq⟩ | ⟨hxc, τ, heq⟩ | ⟨hS, τ, heq, hrel⟩
  · rw [h]; exact hInit x hx0
  · rw [heq]
    exact hInit _ (last_eq_zero_of_mem_cellSet_cOf hN hx0
      (segMap_clamp_mem_cellSet hN (le_of_lt hε) hS (mem_cOf N hN x) τ'))
  · by_cases hbd : x ∈ cellRelbd c
    · rw [heq, T.hHbd ⟨x, hxc⟩ hbd τ]; exact hInit x hx0
    · exfalso
      have heq' := lo_hi_eq_cOf_of_mem_cellSet_of_not_mem_cellRelbd hxc hbd
      have hx0' : ((x (Fin.last n) : unitInterval) : ℝ) = ((0 : ℕ) : ℝ) / N := by
        rw [hx0]; norm_num
      obtain ⟨a, b⟩ := cOf_lo_eq_cOf_hi_of_coord_eq (i := Fin.last n) hN (Nat.zero_le N) hx0'
      have hc : c.lo (Fin.last n) = 0 ∧ c.hi (Fin.last n) = 0 := by
        refine ⟨?_, ?_⟩
        · rw [heq'.1 (Fin.last n)]; exact a
        · rw [heq'.2 (Fin.last n)]; exact b
      exact T.hnotboth (cellBC_of_node_last_zero T.hadm hc)
  · exfalso
    have hsub : Subcell c (cOf N x) :=
      subcell_of_collar_clamp_relint hN (by linarith) hS hrel
    have hx0' : ((x (Fin.last n) : unitInterval) : ℝ) = ((0 : ℕ) : ℝ) / N := by
      rw [hx0]; norm_num
    obtain ⟨a, b⟩ := cOf_lo_eq_cOf_hi_of_coord_eq (i := Fin.last n) hN (Nat.zero_le N) hx0'
    have hc : c.lo (Fin.last n) = 0 ∧ c.hi (Fin.last n) = 0 := by
      have h1 := hsub.2 (Fin.last n)
      have h2 : c.hi (Fin.last n) = 0 := by omega
      refine ⟨?_, h2⟩
      have h3 := c.hle (Fin.last n)
      omega
    exact T.hnotboth (cellBC_of_node_last_zero T.hadm hc)

/-- **The value-set property for `B` is maintained.** -/
theorem maintain_ValsB (T : Treat hN B C x₀ Φ g p q c ε) (hε : (N : ℝ) * ε < 1 / 2)
    (hVB : ValsB (N := N) B Φ g) (s : I) : ValsB (N := N) B Φ (T.gs s) := by
  intro c₂ hB2 x hx2
  rw [T.hgs]
  rcases T.damage (le_of_lt hε) x s with h | ⟨hS, τ', heq⟩ | ⟨hxc, τ, heq⟩ | ⟨hS, τ, heq, hrel⟩
  · rw [h]; exact hVB c₂ hB2 x hx2
  · rw [heq]
    exact hVB c₂ hB2 _
      (cellSet_subcell (cOf_sub_of_mem_cellSet hx2)
        (segMap_clamp_mem_cellSet hN (le_of_lt hε) hS (mem_cOf N hN x) τ'))
  · by_cases hbd : x ∈ cellRelbd c
    · rw [heq, T.hHbd ⟨x, hxc⟩ hbd τ]; exact hVB c₂ hB2 x hx2
    · have hsub : Subcell c c₂ := subcell_of_mem_inter_of_not_mem_cellRelbd hxc hx2 hbd
      have hBc : CellB B Φ c := CellB_subcell hsub hB2
      rw [heq]; exact T.hHvalsB hBc ⟨x, hxc⟩ τ
  · have hsub : Subcell c c₂ :=
      Subcell.trans (subcell_of_collar_clamp_relint hN (by linarith) hS hrel)
        (cOf_sub_of_mem_cellSet hx2)
    have hBc : CellB B Φ c := CellB_subcell hsub hB2
    rw [heq]
    exact T.hHvalsB hBc ⟨clampCell c hN x, clampCell_mem c hN x⟩ τ

/-- **The value-set property for `C` is maintained.** -/
theorem maintain_ValsC (T : Treat hN B C x₀ Φ g p q c ε) (hε : (N : ℝ) * ε < 1 / 2)
    (hVC : ValsC (N := N) C Φ g) (s : I) : ValsC (N := N) C Φ (T.gs s) := by
  intro c₂ hC2 x hx2
  rw [T.hgs]
  rcases T.damage (le_of_lt hε) x s with h | ⟨hS, τ', heq⟩ | ⟨hxc, τ, heq⟩ | ⟨hS, τ, heq, hrel⟩
  · rw [h]; exact hVC c₂ hC2 x hx2
  · rw [heq]
    exact hVC c₂ hC2 _
      (cellSet_subcell (cOf_sub_of_mem_cellSet hx2)
        (segMap_clamp_mem_cellSet hN (le_of_lt hε) hS (mem_cOf N hN x) τ'))
  · by_cases hbd : x ∈ cellRelbd c
    · rw [heq, T.hHbd ⟨x, hxc⟩ hbd τ]; exact hVC c₂ hC2 x hx2
    · have hsub : Subcell c c₂ := subcell_of_mem_inter_of_not_mem_cellRelbd hxc hx2 hbd
      have hnB : ¬ CellB B Φ c := fun hB => T.hnotboth ⟨hB, CellC_subcell hsub hC2⟩
      rw [heq]; exact T.hHvalsC hnB ⟨x, hxc⟩ τ
  · have hsub : Subcell c c₂ :=
      Subcell.trans (subcell_of_collar_clamp_relint hN (by linarith) hS hrel)
        (cOf_sub_of_mem_cellSet hx2)
    have hnB : ¬ CellB B Φ c := fun hB => T.hnotboth ⟨hB, CellC_subcell hsub hC2⟩
    rw [heq]
    exact T.hHvalsC hnB ⟨clampCell c hN x, clampCell_mem c hN x⟩ τ

/-- **The staged clauses are maintained for the cells of dimension at most that of the treated
cell.** -/
theorem maintain_Con (T : Treat hN B C x₀ Φ g p q c ε) (hε : (N : ℝ) * ε < 1 / 2)
    {c₂ : CellIdx (n + 1) N} (hle : cellDim c₂ ≤ cellDim c) (hne : c₂ ≠ c)
    (hCon : ConClauses p q B C Φ g c₂) (s : I) : ConClauses p q B C Φ (T.gs s) c₂ := by
  obtain ⟨cl1, cl2, cl3, cl4⟩ := hCon
  have hkill : ∀ {z : IC (n + 1)}, z ∈ cellSet c₂ → (z ∈ cellSet c ∧ z ∉ cellRelbd c) → False := by
    intro z hz hz'
    have hsub : Subcell c c₂ := subcell_of_mem_inter_of_not_mem_cellRelbd hz'.1 hz hz'.2
    have hdim : cellDim c = cellDim c₂ := le_antisymm (cellDim_le_of_subcell hsub) hle
    exact hne (Subcell.eq_of_cellDim_eq hsub hdim).symm
  have hkill2 : ∀ {z : IC (n + 1)} (hS : z ∈ cellStarCollar c ε) (hrel : clampCell c hN z ∈ cellRelint c)
      (hz : z ∈ cellSet c₂), False := by
    intro z hS hrel hz
    have hsub : Subcell c c₂ :=
      Subcell.trans (subcell_of_collar_clamp_relint hN (by linarith) hS hrel)
        (cOf_sub_of_mem_cellSet hz)
    have hdim : cellDim c = cellDim c₂ := le_antisymm (cellDim_le_of_subcell hsub) hle
    exact hne (Subcell.eq_of_cellDim_eq hsub hdim).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hB2 hnC2 hdim z hz
    rw [T.hgs]
    rcases T.damage (le_of_lt hε) z s with h | ⟨hS, τ', heq⟩ | ⟨hzc, τ, heq⟩ | ⟨hS, τ, heq, hrel⟩
    · rw [h]; exact cl1 hB2 hnC2 hdim z hz
    · rw [heq]
      exact cl1 hB2 hnC2 hdim _
        (cellSet_subcell (cOf_sub_of_mem_cellSet hz)
          (segMap_clamp_mem_cellSet hN (le_of_lt hε) hS (mem_cOf N hN z) τ'))
    · by_cases hbd : z ∈ cellRelbd c
      · rw [heq, T.hHbd ⟨z, hzc⟩ hbd τ]; exact cl1 hB2 hnC2 hdim z hz
      · exact (hkill hz ⟨hzc, hbd⟩).elim
    · exact (hkill2 hS hrel hz).elim
  · intro hB2 hnC2 hdim z hz hnotC
    have hnotC' : T.G (z, s) ∉ C := by rwa [T.hgs] at hnotC
    rcases T.damage (le_of_lt hε) z s with h | ⟨hS, τ', heq⟩ | ⟨hzc, τ, heq⟩ | ⟨hS, τ, heq, hrel⟩
    · rw [h] at hnotC'; exact cl2 hB2 hnC2 hdim z hz hnotC'
    · rw [heq] at hnotC'
      obtain ⟨L, hL, hLi⟩ :=
        cl2 hB2 hnC2 hdim _
          (cellSet_subcell (cOf_sub_of_mem_cellSet hz)
            (segMap_clamp_mem_cellSet hN (le_of_lt hε) hS (mem_cOf N hN z) τ')) hnotC'
      exact ⟨L, hL, fun i hi => smallIn_segMap_clamp hN hε hS τ' i (hLi i hi)⟩
    · by_cases hbd : z ∈ cellRelbd c
      · rw [heq] at hnotC'
        rw [T.hHbd ⟨z, hzc⟩ hbd τ] at hnotC'
        exact cl2 hB2 hnC2 hdim z hz hnotC'
      · exact (hkill hz ⟨hzc, hbd⟩).elim
    · exact (hkill2 hS hrel hz).elim
  · intro hnB2 hC2 hdim z hz
    rw [T.hgs]
    rcases T.damage (le_of_lt hε) z s with h | ⟨hS, τ', heq⟩ | ⟨hzc, τ, heq⟩ | ⟨hS, τ, heq, hrel⟩
    · rw [h]; exact cl3 hnB2 hC2 hdim z hz
    · rw [heq]
      exact cl3 hnB2 hC2 hdim _
        (cellSet_subcell (cOf_sub_of_mem_cellSet hz)
          (segMap_clamp_mem_cellSet hN (le_of_lt hε) hS (mem_cOf N hN z) τ'))
    · by_cases hbd : z ∈ cellRelbd c
      · rw [heq, T.hHbd ⟨z, hzc⟩ hbd τ]; exact cl3 hnB2 hC2 hdim z hz
      · exact (hkill hz ⟨hzc, hbd⟩).elim
    · exact (hkill2 hS hrel hz).elim
  · intro hnB2 hC2 hdim z hz hnotB
    have hnotB' : T.G (z, s) ∉ B := by rwa [T.hgs] at hnotB
    rcases T.damage (le_of_lt hε) z s with h | ⟨hS, τ', heq⟩ | ⟨hzc, τ, heq⟩ | ⟨hS, τ, heq, hrel⟩
    · rw [h] at hnotB'; exact cl4 hnB2 hC2 hdim z hz hnotB'
    · rw [heq] at hnotB'
      obtain ⟨L, hL, hLi⟩ :=
        cl4 hnB2 hC2 hdim _
          (cellSet_subcell (cOf_sub_of_mem_cellSet hz)
            (segMap_clamp_mem_cellSet hN (le_of_lt hε) hS (mem_cOf N hN z) τ')) hnotB'
      exact ⟨L, hL, fun i hi => largeIn_segMap_clamp hN hε hS τ' i (hLi i hi)⟩
    · by_cases hbd : z ∈ cellRelbd c
      · rw [heq] at hnotB'
        rw [T.hHbd ⟨z, hzc⟩ hbd τ] at hnotB'
        exact cl4 hnB2 hC2 hdim z hz hnotB'
      · exact (hkill hz ⟨hzc, hbd⟩).elim
    · exact (hkill2 hS hrel hz).elim

/-- **Every slice of a treatment is admissible.** -/
theorem at_admissible (T : Treat hN B C x₀ Φ g p q c ε) (hε : (N : ℝ) * ε < 1 / 2)
    (hInit : InitFace (x₀ : X) g) (hVB : ValsB (N := N) B Φ g) (hVC : ValsC (N := N) C Φ g) (s : I) :
    TriadAdmissible B C x₀ (T.gs s) := by
  have hI := T.maintain_InitFace hε hInit s
  have hB := T.maintain_ValsB hε hVB s
  have hC := T.maintain_ValsC hε hVC s
  refine ⟨fun x => ?_, fun x => ?_, fun x hx t => ?_⟩
  · exact hI (Fin.snoc x 0) (by rw [Fin.snoc_last])
  · exact valC_of_final T.hadm hC (z := Fin.snoc x 1) hN (by rw [Fin.snoc_last])
  · rcases hx with ⟨i, hi⟩
    exact valB_of_wall T.hadm hB hN (z := Fin.snoc x t) (i := i)
      (by rw [Fin.snoc_castSucc]; exact hi)

end Treat

end

end Work.RatHurewicz.Triad
