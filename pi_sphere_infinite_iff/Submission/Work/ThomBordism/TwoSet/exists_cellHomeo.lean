import Mathlib
import Submission.Work.ThomBordism.TwoSet.Cells

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

variable {j N : ℕ}

abbrev freeIdx (c : CellIdx j N) : Type := {i : Fin j // c.lo i < c.hi i}

theorem card_freeIdx (c : CellIdx j N) : Fintype.card (freeIdx c) = cellDim c := by
  rw [cellDim, Fintype.card_subtype]

noncomputable def cellPsi (c : CellIdx j N) : Fin (cellDim c) ≃ freeIdx c :=
  (Fintype.equivFinOfCardEq (card_freeIdx c)).symm

noncomputable def outGz (c : CellIdx j N) (t : Fin (cellDim c) → unitInterval) :
    Fin j → unitInterval :=
  fun i => if h : c.lo i < c.hi i then t ((cellPsi c).symm ⟨i, h⟩) else 0

theorem outGz_pos {c : CellIdx j N} {t : Fin (cellDim c) → unitInterval} {i : Fin j}
    (h : c.lo i < c.hi i) : outGz c t i = t ((cellPsi c).symm ⟨i, h⟩) := dif_pos h

theorem outGz_neg {c : CellIdx j N} {t : Fin (cellDim c) → unitInterval} {i : Fin j}
    (h : ¬ c.lo i < c.hi i) : outGz c t i = 0 := dif_neg h

theorem outGz_psi (c : CellIdx j N) (t : Fin (cellDim c) → unitInterval)
    (m : Fin (cellDim c)) : outGz c t (cellPsi c m).1 = t m := by
  rw [outGz_pos (c := c) (t := t) (i := (cellPsi c m).1) (cellPsi c m).2]
  congr 1
  simpa using Equiv.symm_apply_apply (cellPsi c) m

theorem hsub_of_lt {c : CellIdx j N} {i : Fin j} (h : c.lo i < c.hi i) :
    (c.hi i : ℝ) - (c.lo i : ℝ) = 1 := by
  have h1 : c.hi i = c.lo i + 1 := by
    have hs := c.hstep i; omega
  rw [h1]; push_cast; ring

theorem heq_of_not_lt {c : CellIdx j N} {i : Fin j} (h : ¬ c.lo i < c.hi i) :
    c.hi i = c.lo i := by
  have hle := c.hle i; omega

noncomputable def cellMapReal (c : CellIdx j N) (t : Fin (cellDim c) → unitInterval)
    (i : Fin j) : ℝ :=
  ((c.lo i : ℝ) + ((c.hi i : ℝ) - (c.lo i : ℝ)) * ((outGz c t i : unitInterval) : ℝ)) / N

theorem cellMapReal_mem (c : CellIdx j N) (hN : 1 ≤ N) (t : Fin (cellDim c) → unitInterval)
    (i : Fin j) : cellMapReal c t i ∈ unitInterval := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hg0 : (0:ℝ) ≤ ((outGz c t i : unitInterval) : ℝ) := (outGz c t i).2.1
  have hg1 : ((outGz c t i : unitInterval) : ℝ) ≤ 1 := (outGz c t i).2.2
  have hle : (c.lo i : ℝ) ≤ (c.hi i : ℝ) := by exact_mod_cast c.hle i
  constructor
  · rw [cellMapReal]
    apply div_nonneg _ (le_of_lt hNpos)
    have : 0 ≤ ((c.hi i : ℝ) - (c.lo i : ℝ)) * ((outGz c t i : unitInterval) : ℝ) :=
      mul_nonneg (by linarith) hg0
    linarith
  · rw [cellMapReal, div_le_one hNpos]
    have : ((c.hi i : ℝ) - (c.lo i : ℝ)) * ((outGz c t i : unitInterval) : ℝ)
        ≤ (c.hi i : ℝ) - (c.lo i : ℝ) :=
      mul_le_of_le_one_right (by linarith) hg1
    have hhi : (c.hi i : ℝ) ≤ (N : ℝ) := by exact_mod_cast c.hhi i
    linarith

noncomputable def cellMapFun (c : CellIdx j N) (hN : 1 ≤ N)
    (t : Fin (cellDim c) → unitInterval) : IC j :=
  fun i => ⟨cellMapReal c t i, cellMapReal_mem c hN t i⟩

theorem cellMapFun_mem (c : CellIdx j N) (hN : 1 ≤ N) (t : Fin (cellDim c) → unitInterval) :
    cellMapFun c hN t ∈ cellSet c := by
  intro i
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hg0 : (0:ℝ) ≤ ((outGz c t i : unitInterval) : ℝ) := (outGz c t i).2.1
  have hg1 : ((outGz c t i : unitInterval) : ℝ) ≤ 1 := (outGz c t i).2.2
  have hle : (c.lo i : ℝ) ≤ (c.hi i : ℝ) := by exact_mod_cast c.hle i
  change (c.lo i : ℝ) / N ≤ cellMapReal c t i ∧ cellMapReal c t i ≤ (c.hi i : ℝ) / N
  constructor
  · rw [cellMapReal, div_le_div_iff_of_pos_right hNpos]
    have : 0 ≤ ((c.hi i : ℝ) - (c.lo i : ℝ)) * ((outGz c t i : unitInterval) : ℝ) :=
      mul_nonneg (by linarith) hg0
    linarith
  · rw [cellMapReal, div_le_div_iff_of_pos_right hNpos]
    have : ((c.hi i : ℝ) - (c.lo i : ℝ)) * ((outGz c t i : unitInterval) : ℝ)
        ≤ (c.hi i : ℝ) - (c.lo i : ℝ) :=
      mul_le_of_le_one_right (by linarith) hg1
    have hhi : (c.hi i : ℝ) ≤ (N : ℝ) := by exact_mod_cast c.hhi i
    linarith

noncomputable def invReal (c : CellIdx j N) (x : cellSet c) (m : Fin (cellDim c)) : ℝ :=
  (N : ℝ) * (((x : IC j) ((cellPsi c m).1) : unitInterval) : ℝ) - (c.lo (cellPsi c m).1 : ℝ)

theorem invReal_mem (c : CellIdx j N) (hN : 1 ≤ N) (x : cellSet c) (m : Fin (cellDim c)) :
    invReal c x m ∈ unitInterval := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  simp only [invReal]
  set i := (cellPsi c m).1 with hi_def
  have hx := (mem_cellSet.mp x.2) i
  constructor
  · have h1 : (c.lo i : ℝ) ≤ (N:ℝ) * (((x:IC j) i : unitInterval) : ℝ) := by
      have h2 := hx.1
      rw [div_le_iff₀ hNpos] at h2
      linarith
    linarith
  · have h2 : (N:ℝ) * (((x:IC j) i : unitInterval) : ℝ) ≤ (c.hi i : ℝ) := by
      have h3 := hx.2
      rw [le_div_iff₀ hNpos] at h3
      linarith
    have h3 : (c.hi i : ℝ) ≤ (c.lo i : ℝ) + 1 := by
      have hs : (c.hi i : ℕ) ≤ c.lo i + 1 := c.hstep i
      have hcast : (c.hi i : ℝ) ≤ ((c.lo i + 1 : ℕ) : ℝ) := by exact_mod_cast hs
      simpa using hcast
    linarith

noncomputable def invMap (c : CellIdx j N) (hN : 1 ≤ N) (x : cellSet c) :
    Fin (cellDim c) → unitInterval :=
  fun m => ⟨invReal c x m, invReal_mem c hN x m⟩

theorem continuous_outGz (c : CellIdx j N) (i : Fin j) :
    Continuous (fun t : Fin (cellDim c) → unitInterval => ((outGz c t i : unitInterval) : ℝ)) := by
  by_cases h : c.lo i < c.hi i
  · have hfun : (fun t : Fin (cellDim c) → unitInterval => ((outGz c t i : unitInterval) : ℝ))
        = fun t => ((t ((cellPsi c).symm ⟨i, h⟩) : unitInterval) : ℝ) := by
      funext t; rw [outGz_pos (c := c) (t := t) (i := i) h]
    rw [hfun]
    exact continuous_subtype_val.comp (continuous_apply _)
  · have hfun : (fun t : Fin (cellDim c) → unitInterval => ((outGz c t i : unitInterval) : ℝ))
        = fun _ => (0:ℝ) := by
      funext t; rw [outGz_neg (c := c) (t := t) (i := i) h]; rfl
    rw [hfun]; exact continuous_const

theorem continuous_cellMapReal (c : CellIdx j N) (i : Fin j) :
    Continuous (fun t : Fin (cellDim c) → unitInterval => cellMapReal c t i) := by
  simp only [cellMapReal]
  apply Continuous.div_const
  apply Continuous.add continuous_const
  apply Continuous.mul continuous_const
  exact continuous_outGz c i

theorem continuous_cellMapFun (c : CellIdx j N) (hN : 1 ≤ N) :
    Continuous (fun t : Fin (cellDim c) → unitInterval => cellMapFun c hN t) := by
  apply continuous_pi
  intro i
  exact Continuous.subtype_mk (continuous_cellMapReal c i) (fun t => cellMapReal_mem c hN t i)

theorem continuous_cellMap_coe (c : CellIdx j N) (hN : 1 ≤ N) :
    Continuous (fun t : Fin (cellDim c) → unitInterval =>
      (⟨cellMapFun c hN t, cellMapFun_mem c hN t⟩ : cellSet c)) :=
  Continuous.subtype_mk (continuous_cellMapFun c hN) _

theorem continuous_invReal (c : CellIdx j N) (m : Fin (cellDim c)) :
    Continuous (fun x : cellSet c => invReal c x m) := by
  have h1 : Continuous (fun x : cellSet c => (((x : IC j) (cellPsi c m).1 : unitInterval) : ℝ)) :=
    (continuous_subtype_val (p := (· ∈ unitInterval))).comp
      ((continuous_apply (cellPsi c m).1).comp (continuous_subtype_val (p := (· ∈ cellSet c))))
  simp only [invReal]
  exact (continuous_const.mul h1).sub continuous_const

theorem continuous_invMap (c : CellIdx j N) (hN : 1 ≤ N) :
    Continuous (fun x : cellSet c => invMap c hN x) := by
  apply continuous_pi
  intro m
  exact Continuous.subtype_mk (continuous_invReal c m) (fun x => invReal_mem c hN x m)


theorem cellMapReal_invMap (c : CellIdx j N) (hN : 1 ≤ N) (x : cellSet c) (i : Fin j) :
    cellMapReal c (invMap c hN x) i = ((x : IC j) i : ℝ) := by
  have hNne : (N:ℝ) ≠ 0 := by
    have h : (0:ℝ) < N := by exact_mod_cast hN
    exact ne_of_gt h
  by_cases h : c.lo i < c.hi i
  · have hgz : ((outGz c (invMap c hN x) i : unitInterval) : ℝ)
        = (N:ℝ) * ((x : IC j) i : ℝ) - (c.lo i : ℝ) := by
      rw [outGz_pos (c := c) (t := invMap c hN x) (i := i) h]
      have h1 : (cellPsi c ((cellPsi c).symm ⟨i, h⟩)).1 = i := by rw [Equiv.apply_symm_apply]
      simp only [invMap, invReal, h1]
    rw [cellMapReal, hsub_of_lt h, hgz]
    rw [div_eq_iff hNne]
    ring
  · have hlo : c.hi i = c.lo i := heq_of_not_lt h
    have hgz : ((outGz c (invMap c hN x) i : unitInterval) : ℝ) = 0 := by
      rw [outGz_neg (c := c) (t := invMap c hN x) (i := i) h]; rfl
    have hxe : ((x : IC j) i : ℝ) = (c.lo i : ℝ) / N := by
      have hx := (mem_cellSet.mp x.2) i
      refine le_antisymm ?_ hx.1
      rw [← hlo]; exact hx.2
    rw [cellMapReal, hgz, hxe, hlo]
    simp

theorem invReal_cellMap (c : CellIdx j N) (hN : 1 ≤ N)
    (t : Fin (cellDim c) → unitInterval) (m : Fin (cellDim c)) :
    invReal c ⟨cellMapFun c hN t, cellMapFun_mem c hN t⟩ m = ((t m : unitInterval) : ℝ) := by
  have hNne : (N:ℝ) ≠ 0 := by
    have h : (0:ℝ) < N := by exact_mod_cast hN
    exact ne_of_gt h
  have hgz : ((outGz c t (cellPsi c m).1 : unitInterval) : ℝ) = ((t m : unitInterval) : ℝ) :=
    congrArg Subtype.val (outGz_psi c t m)
  simp only [invReal, cellMapFun, cellMapReal, hsub_of_lt (cellPsi c m).2, hgz]
  rw [mul_div_cancel₀ _ hNne]
  ring

theorem cellMapFun_invMap (c : CellIdx j N) (hN : 1 ≤ N) (x : cellSet c) :
    cellMapFun c hN (invMap c hN x) = (x : IC j) := by
  funext i
  apply Subtype.ext
  exact cellMapReal_invMap c hN x i

noncomputable def cellEquiv (c : CellIdx j N) (hN : 1 ≤ N) :
    (Fin (cellDim c) → unitInterval) ≃ cellSet c where
  toFun t := ⟨cellMapFun c hN t, cellMapFun_mem c hN t⟩
  invFun x := invMap c hN x
  left_inv t := by
    funext m
    apply Subtype.ext
    exact invReal_cellMap c hN t m
  right_inv x := by
    apply Subtype.ext
    exact cellMapFun_invMap c hN x

noncomputable def cellHomeo (c : CellIdx j N) (hN : 1 ≤ N) :
    (Fin (cellDim c) → unitInterval) ≃ₜ cellSet c where
  toEquiv := cellEquiv c hN
  continuous_toFun := continuous_cellMap_coe c hN
  continuous_invFun := continuous_invMap c hN

theorem invReal_eq_zero_iff (c : CellIdx j N) (hN : 1 ≤ N) (z : cellSet c)
    (m : Fin (cellDim c)) :
    invReal c z m = 0 ↔ ((z : IC j) (cellPsi c m).1 : ℝ) = (c.lo (cellPsi c m).1 : ℝ) / N := by
  have hNne : (N:ℝ) ≠ 0 := by
    have h : (0:ℝ) < N := by exact_mod_cast hN
    exact ne_of_gt h
  rw [invReal, sub_eq_zero]
  constructor
  · intro h
    rw [eq_div_iff hNne]
    rw [mul_comm]; exact h
  · intro h
    rw [h, mul_div_cancel₀ _ hNne]

theorem invReal_eq_one_iff (c : CellIdx j N) (hN : 1 ≤ N) (z : cellSet c)
    (m : Fin (cellDim c)) :
    invReal c z m = 1 ↔ ((z : IC j) (cellPsi c m).1 : ℝ) = (c.hi (cellPsi c m).1 : ℝ) / N := by
  have hNne : (N:ℝ) ≠ 0 := by
    have h : (0:ℝ) < N := by exact_mod_cast hN
    exact ne_of_gt h
  have hhi : (c.hi (cellPsi c m).1 : ℝ) = (c.lo (cellPsi c m).1 : ℝ) + 1 := by
    have h1 : c.hi (cellPsi c m).1 = c.lo (cellPsi c m).1 + 1 := by
      have hs := c.hstep (cellPsi c m).1; have hlt := (cellPsi c m).2; omega
    rw [h1]; push_cast; ring
  rw [invReal, hhi]
  constructor
  · intro h
    rw [eq_div_iff hNne]
    have h2 : (N:ℝ) * (((z:IC j) (cellPsi c m).1 : unitInterval) : ℝ)
        = (c.lo (cellPsi c m).1 : ℝ) + 1 := by linarith
    rw [mul_comm]; exact h2
  · intro h
    rw [h, mul_div_cancel₀ _ hNne]
    ring

theorem invMap_mem_boundary_iff (c : CellIdx j N) (hN : 1 ≤ N) (z : cellSet c) :
    invMap c hN z ∈ Cube.boundary (Fin (cellDim c)) ↔ (z : IC j) ∈ cellRelbd c := by
  rw [Cube.boundary, Set.mem_ofPred_eq, mem_cellRelbd]
  constructor
  · rintro ⟨m, hm | hm⟩
    · have h0 : invReal c z m = 0 := by
        have h1 : ((invMap c hN z m : unitInterval) : ℝ) = (0 : ℝ) := by rw [hm]; rfl
        exact h1
      rw [invReal_eq_zero_iff c hN z m] at h0
      exact ⟨(cellPsi c m).1, (cellPsi c m).2, Or.inl h0⟩
    · have h0 : invReal c z m = 1 := by
        have h1 : ((invMap c hN z m : unitInterval) : ℝ) = (1 : ℝ) := by rw [hm]; rfl
        exact h1
      rw [invReal_eq_one_iff c hN z m] at h0
      exact ⟨(cellPsi c m).1, (cellPsi c m).2, Or.inr h0⟩
  · rintro ⟨i, hi, h | h⟩
    · refine ⟨(cellPsi c).symm ⟨i, hi⟩, Or.inl ?_⟩
      apply Subtype.ext
      change invReal c z ((cellPsi c).symm ⟨i, hi⟩) = 0
      rw [invReal_eq_zero_iff c hN z ((cellPsi c).symm ⟨i, hi⟩)]
      have h1 : (cellPsi c ((cellPsi c).symm ⟨i, hi⟩)).1 = i := by rw [Equiv.apply_symm_apply]
      rw [h1]; exact h
    · refine ⟨(cellPsi c).symm ⟨i, hi⟩, Or.inr ?_⟩
      apply Subtype.ext
      change invReal c z ((cellPsi c).symm ⟨i, hi⟩) = 1
      rw [invReal_eq_one_iff c hN z ((cellPsi c).symm ⟨i, hi⟩)]
      have h1 : (cellPsi c ((cellPsi c).symm ⟨i, hi⟩)).1 = i := by rw [Equiv.apply_symm_apply]
      rw [h1]; exact h

theorem exists_cellHomeo {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N) :
    ∃ e : (Fin (cellDim c) → unitInterval) ≃ₜ (cellSet c),
      e '' Cube.boundary (Fin (cellDim c)) = {z : cellSet c | (z : IC j) ∈ cellRelbd c} := by
  refine ⟨cellHomeo c hN, ?_⟩
  rw [Homeomorph.image_eq_preimage_symm]
  ext z
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  exact invMap_mem_boundary_iff c hN z

end Work.ThomBordism.TwoSet
