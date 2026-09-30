import Mathlib
import Submission.Work.RatHurewicz.Triad.Structural
import Submission.Work.RatHurewicz.exists_cellTreatmentOf
import Submission.Work.RatHurewicz.exists_cutoffs_collar
import Submission.Work.RatHurewicz.zeroCellPath

/-!
# Preliminary lemmas for the treatment of a cell

* the two-phase formula of the treatment (`cellTreatmentFormula`);
* the small mesh `eps`;
* the dictionary between the ambient half-conditions `SmallIn`/`LargeIn` and the cell-local
  coordinates of `kTrick_cell`/`gTrick_cell`;
* the treatment of a `0`-cell (`zeroCellTreatment`).
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

open Work.ThomBordism.TwoSet

noncomputable section

variable {X : Type} [TopologicalSpace X] {B C : Set X} {x₀ : ↥(B ∩ C)} {N : ℕ} {n p q : ℕ}

/-- **The mesh used by the grid induction.** -/
noncomputable def eps (N : ℕ) : ℝ := 1 / (8 * N)

theorem eps_pos {N : ℕ} (hN : 1 ≤ N) : 0 < eps N := by
  have : (0:ℝ) < N := by exact_mod_cast hN
  rw [eps]; positivity

theorem eps_bound {N : ℕ} (hN : 1 ≤ N) : (N : ℝ) * eps N < 1 / 2 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  rw [eps, mul_one_div, div_lt_iff₀ (by positivity : (0:ℝ) < 8 * (N:ℝ))]
  linarith

/-- **The treatment formula.**  `exists_cellTreatmentOf` with the explicit two-phase formula as the
first clause. -/
theorem cellTreatmentFormula {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N)
    (S : Set (IC j))
    {Y : Type} [TopologicalSpace Y] (g : C(IC j, Y))
    (H : C(cellSet c × unitInterval, Y))
    (hH0 : ∀ z : cellSet c, H (z, 0) = g z)
    (hHbd : ∀ z : cellSet c, (z : IC j) ∈ cellRelbd c → ∀ t, H (z, t) = g z)
    (μ : C(IC j, ℝ)) (ν : C(IC j, unitInterval))
    (hμ0 : ∀ x, x ∉ S → μ x = 0)
    (hμ2 : ∀ x, x ∈ cellSet c → 2 ≤ μ x)
    (hν1 : ∀ x, x ∈ cellSet c → ν x = 1) :
    ∃ G : C(IC j × unitInterval, Y),
      (∀ x s, G (x, s) = if (s : ℝ) * μ x ≤ 1 then g (flowCell c hN μ x s)
        else H (⟨clampCell c hN x, clampCell_mem c hN x⟩, pushTime μ ν x s)) ∧
      (∀ x, G (x, 0) = g x) ∧
      (∀ x, x ∉ S → ∀ s, G (x, s) = g x) := by
  classical
  have hkey : ∀ p : IC j × I, (p.2 : ℝ) * μ p.1 = 1 →
      g (flowCell c hN μ p.1 p.2) =
        H (⟨clampCell c hN p.1, clampCell_mem c hN p.1⟩, pushTime μ ν p.1 p.2) := by
    intro p hp
    have harr : 1 ≤ (p.2 : ℝ) * μ p.1 := le_of_eq hp.symm
    have hflow : flowCell c hN μ p.1 p.2 = clampCell c hN p.1 := by
      have hpar : flowParam μ p.1 p.2 = 1 := by
        apply Subtype.ext
        simp only [flowParam_val]
        exact min_eq_left (le_trans harr (le_max_right 0 _))
      rw [flowCell, hpar, segMap_one]
    have hpt : pushTime μ ν p.1 p.2 = 0 := pushTime_eq_zero_of_le (le_of_eq hp)
    rw [hflow, hpt]
    exact (hH0 ⟨clampCell c hN p.1, clampCell_mem c hN p.1⟩).symm
  have hcont : Continuous fun p : IC j × I =>
      if (p.2 : ℝ) * μ p.1 ≤ (1:ℝ) then g (flowCell c hN μ p.1 p.2)
      else H (⟨clampCell c hN p.1, clampCell_mem c hN p.1⟩, pushTime μ ν p.1 p.2) :=
    Continuous.if_le (g.continuous.comp (continuous_flowCell_pair hN c μ))
      (H.continuous.comp (Continuous.prodMk
        (Continuous.subtype_mk ((clampCell c hN).continuous.comp continuous_fst) _)
        (continuous_pushTime_pair μ ν)))
      ((continuous_subtype_val.comp continuous_snd).mul (μ.continuous.comp continuous_fst))
      continuous_const hkey
  refine ⟨⟨fun p => if (p.2 : ℝ) * μ p.1 ≤ (1:ℝ) then g (flowCell c hN μ p.1 p.2)
      else H (⟨clampCell c hN p.1, clampCell_mem c hN p.1⟩, pushTime μ ν p.1 p.2), hcont⟩,
    fun x s => rfl, ?_, ?_⟩
  · intro x
    have h : ((0 : I) : ℝ) * μ x ≤ (1:ℝ) := by simp
    show (if ((0 : I) : ℝ) * μ x ≤ (1:ℝ) then g (flowCell c hN μ x 0)
      else H (⟨clampCell c hN x, clampCell_mem c hN x⟩, pushTime μ ν x 0)) = g x
    rw [if_pos h, flowCell_zero]
  · intro x hx s
    have hμ : μ x = 0 := hμ0 x hx
    have h : (s : ℝ) * μ x ≤ (1:ℝ) := by rw [hμ, mul_zero]; norm_num
    show (if (s : ℝ) * μ x ≤ (1:ℝ) then g (flowCell c hN μ x s)
      else H (⟨clampCell c hN x, clampCell_mem c hN x⟩, pushTime μ ν x s)) = g x
    rw [if_pos h, flowCell_eq_self_of_mu_eq_zero hN hμ s]

section Local

/-- Interval directions of a subcell have the same interval in the bigger cell. -/
theorem subcell_interval_eq {j N : ℕ} {c c' : CellIdx j N} (h : Subcell c c') {i : Fin j}
    (hi : c.lo i < c.hi i) : c.lo i = c'.lo i ∧ c.hi i = c'.hi i := by
  have hstep : c.hi i = c.lo i + 1 := by have := c.hstep i; omega
  have hlo := h.1 i
  have hhi := h.2 i
  have hlt' : c'.lo i < c'.hi i := by omega
  have hstep' : c'.hi i = c'.lo i + 1 := by have := c'.hstep i; omega
  constructor <;> omega

/-- The ambient half-condition is the cell-local one. -/
theorem smallIn_iff_invMap {j N : ℕ} (hN : 1 ≤ N) {c : CellIdx j N} {z : IC j}
    (hz : z ∈ cellSet c) (m : Fin (cellDim c)) :
    SmallIn N c z (cellPsi c m).1 ↔
      ((invMap c hN ⟨z, hz⟩ m : unitInterval) : ℝ) < 1 / 2 := by
  have hlt := (cellPsi c m).2
  have hval : ((invMap c hN ⟨z, hz⟩ m : unitInterval) : ℝ) =
      (N : ℝ) * (z (cellPsi c m).1 : ℝ) - (c.lo (cellPsi c m).1 : ℝ) := rfl
  rw [SmallIn, hval]
  constructor
  · intro h; linarith [h.1, h.2]
  · intro h; exact ⟨hlt, by linarith⟩

/-- The ambient half-condition is the cell-local one (upper half). -/
theorem largeIn_iff_invMap {j N : ℕ} (hN : 1 ≤ N) {c : CellIdx j N} {z : IC j}
    (hz : z ∈ cellSet c) (m : Fin (cellDim c)) :
    LargeIn N c z (cellPsi c m).1 ↔
      1 / 2 < ((invMap c hN ⟨z, hz⟩ m : unitInterval) : ℝ) := by
  have hlt := (cellPsi c m).2
  have hval : ((invMap c hN ⟨z, hz⟩ m : unitInterval) : ℝ) =
      (N : ℝ) * (z (cellPsi c m).1 : ℝ) - (c.lo (cellPsi c m).1 : ℝ) := rfl
  rw [LargeIn, hval]
  constructor
  · intro h; linarith [h.1, h.2]
  · intro h; exact ⟨hlt, by linarith⟩

/-- The ambient `KW` condition, in the cell-local coordinates. -/
theorem kw_of_local {j N : ℕ} (hN : 1 ≤ N) {P : ℕ} {c : CellIdx j N} {z : IC j}
    (hz : z ∈ cellSet c)
    (h : ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
      ∀ m ∈ L, ((invMap c hN ⟨z, hz⟩ m : unitInterval) : ℝ) < 1 / 2) :
    KW N P c z := by
  obtain ⟨L, hL, hLi⟩ := h
  refine ⟨L.image (fun m => (cellPsi c m).1), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (fun a b hab => cellPsi c |>.injective (Subtype.ext hab))]
    exact hL
  · intro i hi
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hi
    exact (smallIn_iff_invMap hN hz m).mpr (hLi m hm)

/-- The cell-local `KW` condition, in the ambient coordinates. -/
theorem local_of_kw {j N : ℕ} (hN : 1 ≤ N) {P : ℕ} {c : CellIdx j N} {z : IC j}
    (hz : z ∈ cellSet c) (h : KW N P c z) :
    ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
      ∀ m ∈ L, ((invMap c hN ⟨z, hz⟩ m : unitInterval) : ℝ) < 1 / 2 := by
  obtain ⟨L, hL, hLi⟩ := h
  let g : ↥L → Fin (cellDim c) := fun i => (cellPsi c).symm ⟨i.1, (hLi i.1 i.2).1⟩
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : (⟨a.1, (hLi a.1 a.2).1⟩ : {i : Fin j // c.lo i < c.hi i}) =
        ⟨b.1, (hLi b.1 b.2).1⟩ := (cellPsi c).symm.injective hab
    exact Subtype.ext (congrArg (fun t : {i : Fin j // c.lo i < c.hi i} => t.1) h1)
  refine ⟨L.attach.map ⟨g, hg⟩, ?_, ?_⟩
  · rw [Finset.card_map]
    simpa using hL
  · intro m hm
    obtain ⟨i, -, hi⟩ := Finset.mem_map.mp hm
    rw [← hi]
    change ((invMap c hN ⟨z, hz⟩ (g i) : unitInterval) : ℝ) < 1 / 2
    have hdir : (cellPsi c (g i)).1 = i.1 := by
      show (cellPsi c ((cellPsi c).symm ⟨i.1, (hLi i.1 i.2).1⟩)).1 = i.1
      rw [Equiv.apply_symm_apply]
    rw [← smallIn_iff_invMap hN hz (g i), hdir]
    exact hLi i.1 i.2

/-- The ambient `GW` condition, in the cell-local coordinates. -/
theorem gw_of_local {j N : ℕ} (hN : 1 ≤ N) {P : ℕ} {c : CellIdx j N} {z : IC j}
    (hz : z ∈ cellSet c)
    (h : ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
      ∀ m ∈ L, 1 / 2 < ((invMap c hN ⟨z, hz⟩ m : unitInterval) : ℝ)) :
    GW N P c z := by
  obtain ⟨L, hL, hLi⟩ := h
  refine ⟨L.image (fun m => (cellPsi c m).1), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (fun a b hab => cellPsi c |>.injective (Subtype.ext hab))]
    exact hL
  · intro i hi
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hi
    exact (largeIn_iff_invMap hN hz m).mpr (hLi m hm)

/-- The cell-local `GW` condition, in the ambient coordinates. -/
theorem local_of_gw {j N : ℕ} (hN : 1 ≤ N) {P : ℕ} {c : CellIdx j N} {z : IC j}
    (hz : z ∈ cellSet c) (h : GW N P c z) :
    ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
      ∀ m ∈ L, 1 / 2 < ((invMap c hN ⟨z, hz⟩ m : unitInterval) : ℝ) := by
  obtain ⟨L, hL, hLi⟩ := h
  let g : ↥L → Fin (cellDim c) := fun i => (cellPsi c).symm ⟨i.1, (hLi i.1 i.2).1⟩
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : (⟨a.1, (hLi a.1 a.2).1⟩ : {i : Fin j // c.lo i < c.hi i}) =
        ⟨b.1, (hLi b.1 b.2).1⟩ := (cellPsi c).symm.injective hab
    exact Subtype.ext (congrArg (fun t : {i : Fin j // c.lo i < c.hi i} => t.1) h1)
  refine ⟨L.attach.map ⟨g, hg⟩, ?_, ?_⟩
  · rw [Finset.card_map]
    simpa using hL
  · intro m hm
    obtain ⟨i, -, hi⟩ := Finset.mem_map.mp hm
    rw [← hi]
    change 1 / 2 < ((invMap c hN ⟨z, hz⟩ (g i) : unitInterval) : ℝ)
    have hdir : (cellPsi c (g i)).1 = i.1 := by
      show (cellPsi c ((cellPsi c).symm ⟨i.1, (hLi i.1 i.2).1⟩)).1 = i.1
      rw [Equiv.apply_symm_apply]
    rw [← largeIn_iff_invMap hN hz (g i), hdir]
    exact hLi i.1 i.2

end Local

/-- The relative boundary of a `0`-cell is empty. -/
theorem not_mem_cellRelbd_of_cellDim_zero {j N : ℕ} {c : CellIdx j N} (hc : cellDim c = 0)
    {x : IC j} : x ∉ cellRelbd c := by
  intro hx
  rw [mem_cellRelbd] at hx
  obtain ⟨i, hi, -⟩ := hx
  have hmem : i ∈ (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)) := by simp [hi]
  have hpos : 0 < (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)).card :=
    Finset.card_pos.mpr ⟨i, hmem⟩
  rw [← cellDim, hc] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- All points of a `0`-cell are equal. -/
theorem eq_of_mem_cellSet_of_cellDim_zero {j N : ℕ} (hN : 1 ≤ N) {c : CellIdx j N}
    (hc : cellDim c = 0) {x y : IC j} (hx : x ∈ cellSet c) (hy : y ∈ cellSet c) : x = y := by
  have hnode : ∀ i : Fin j, c.lo i = c.hi i := by
    intro i
    by_contra hne
    have hlt : c.lo i < c.hi i := lt_of_le_of_ne (c.hle i) hne
    have hmem : i ∈ (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)) := by simp [hlt]
    have hpos : 0 < (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)).card :=
      Finset.card_pos.mpr ⟨i, hmem⟩
    rw [← cellDim, hc] at hpos
    exact absurd hpos (lt_irrefl 0)
  funext i
  have h1 := (mem_cellSet.mp hx i).1
  have h2 := (mem_cellSet.mp hx i).2
  have h3 := (mem_cellSet.mp hy i).1
  have h4 := (mem_cellSet.mp hy i).2
  have h5 : (c.lo i : ℝ) / N = (c.hi i : ℝ) / N := by rw [hnode i]
  exact Subtype.ext (le_antisymm (by linarith) (by linarith))

/-- A chosen point of a `0`-cell. -/
theorem mem_cellSet_clamp_zero {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N) :
    clampCell c hN (fun _ : Fin j => 0) ∈ cellSet c :=
  clampCell_mem c hN (fun _ : Fin j => 0)

/-- **The treatment of a `0`-cell, `B`-side.** -/
theorem zeroCellTreatmentB {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N) (hc : cellDim c = 0)
    (g : C(IC j, X))
    (hB0 : ∀ b : ↥B, (b : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.1⟩ b))
    (hvals : ∀ x : cellSet c, (g x : X) ∈ B)
    (hP : ∀ x : cellSet c, (g x : X) ∈ pathComponent (x₀ : X)) :
    ∃ H : C(cellSet c × unitInterval, X),
      (∀ x, H (x, 0) = g x) ∧
      (∀ (x : cellSet c) (hx : (x : IC j) ∈ cellRelbd c) (t : unitInterval), H (x, t) = g x) ∧
      (∀ x, (H (x, 1) : X) ∈ B ∩ C) ∧
      (∀ x t, (H (x, t) : X) ∈ B) ∧
      (∀ x t, (H (x, t) : X) ∈ pathComponent (x₀ : X)) := by
  classical
  let x₀' : IC j := fun _ : Fin j => 0
  let x₁ : cellSet c := ⟨clampCell c hN x₀', clampCell_mem c hN x₀'⟩
  obtain ⟨a, ⟨γ⟩⟩ := hB0 ⟨(g x₁ : X), hvals x₁⟩ (hP x₁)
  have hγ0 : γ.symm 0 = ⟨(g x₁ : X), hvals x₁⟩ := Path.source γ.symm
  have hγ1 : γ.symm 1 = (⟨a.1, a.2.1⟩ : ↥B) := Path.target γ.symm
  refine ⟨⟨fun xt => ((γ.symm xt.2 : ↥B) : X),
    (continuous_subtype_val.comp (γ.symm.continuous.comp continuous_snd))⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show ((γ.symm 0 : ↥B) : X) = g x
    rw [hγ0]
    exact congrArg g (eq_of_mem_cellSet_of_cellDim_zero hN hc x₁.2 x.2)
  · intro x hx t
    exact absurd hx (not_mem_cellRelbd_of_cellDim_zero hc)
  · intro x
    show ((γ.symm 1 : ↥B) : X) ∈ B ∩ C
    rw [hγ1]
    exact a.2
  · intro x t
    exact (γ.symm t).2
  · intro x t
    have hpc : IsPathConnected
        (Set.range ((setIncl B).comp (γ.symm : C(I, ↥B)) : C(I, X))) :=
      isPathConnected_range (ContinuousMap.continuous _)
    have hmem : ((setIncl B).comp (γ.symm : C(I, ↥B)) : C(I, X)) t ∈
        Set.range ((setIncl B).comp (γ.symm : C(I, ↥B)) : C(I, X)) := ⟨t, rfl⟩
    have h2 := hpc.subset_pathComponent (x := ((setIncl B).comp (γ.symm : C(I, ↥B)) : C(I, X)) 0)
      ⟨0, rfl⟩ hmem
    have h0 : ((setIncl B).comp (γ.symm : C(I, ↥B)) : C(I, X)) 0 = (g x₁ : X) := by
      show ((γ.symm 0 : ↥B) : X) = (g x₁ : X)
      rw [hγ0]
    rw [h0, pathComponent_congr (hP x₁)] at h2
    exact h2

/-- **The treatment of a `0`-cell, `C`-side.** -/
theorem zeroCellTreatmentC {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N) (hc : cellDim c = 0)
    (g : C(IC j, X))
    (hC0 : ∀ b : ↥C, (b : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.2⟩ b))
    (hvals : ∀ x : cellSet c, (g x : X) ∈ C)
    (hP : ∀ x : cellSet c, (g x : X) ∈ pathComponent (x₀ : X)) :
    ∃ H : C(cellSet c × unitInterval, X),
      (∀ x, H (x, 0) = g x) ∧
      (∀ (x : cellSet c) (hx : (x : IC j) ∈ cellRelbd c) (t : unitInterval), H (x, t) = g x) ∧
      (∀ x, (H (x, 1) : X) ∈ B ∩ C) ∧
      (∀ x t, (H (x, t) : X) ∈ C) ∧
      (∀ x t, (H (x, t) : X) ∈ pathComponent (x₀ : X)) := by
  classical
  let x₀' : IC j := fun _ : Fin j => 0
  let x₁ : cellSet c := ⟨clampCell c hN x₀', clampCell_mem c hN x₀'⟩
  obtain ⟨a, ⟨γ⟩⟩ := hC0 ⟨(g x₁ : X), hvals x₁⟩ (hP x₁)
  have hγ0 : γ.symm 0 = ⟨(g x₁ : X), hvals x₁⟩ := Path.source γ.symm
  have hγ1 : γ.symm 1 = (⟨a.1, a.2.2⟩ : ↥C) := Path.target γ.symm
  refine ⟨⟨fun xt => ((γ.symm xt.2 : ↥C) : X),
    (continuous_subtype_val.comp (γ.symm.continuous.comp continuous_snd))⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show ((γ.symm 0 : ↥C) : X) = g x
    rw [hγ0]
    exact congrArg g (eq_of_mem_cellSet_of_cellDim_zero hN hc x₁.2 x.2)
  · intro x hx t
    exact absurd hx (not_mem_cellRelbd_of_cellDim_zero hc)
  · intro x
    show ((γ.symm 1 : ↥C) : X) ∈ B ∩ C
    rw [hγ1]
    exact a.2
  · intro x t
    exact (γ.symm t).2
  · intro x t
    have hpc : IsPathConnected
        (Set.range ((setIncl C).comp (γ.symm : C(I, ↥C)) : C(I, X))) :=
      isPathConnected_range (ContinuousMap.continuous _)
    have hmem : ((setIncl C).comp (γ.symm : C(I, ↥C)) : C(I, X)) t ∈
        Set.range ((setIncl C).comp (γ.symm : C(I, ↥C)) : C(I, X)) := ⟨t, rfl⟩
    have h2 := hpc.subset_pathComponent (x := ((setIncl C).comp (γ.symm : C(I, ↥C)) : C(I, X)) 0)
      ⟨0, rfl⟩ hmem
    have h0 : ((setIncl C).comp (γ.symm : C(I, ↥C)) : C(I, X)) 0 = (g x₁ : X) := by
      show ((γ.symm 0 : ↥C) : X) = (g x₁ : X)
      rw [hγ0]
    rw [h0, pathComponent_congr (hP x₁)] at h2
    exact h2

end

end Work.RatHurewicz.Triad
