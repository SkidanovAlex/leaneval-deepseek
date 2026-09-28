import Mathlib
import Submission.Work.RatHurewicz.Triad.Treatment
import Submission.Work.RatHurewicz.Triad.Prelim
import Submission.Work.RatHurewicz.Triad.TrickVals
import Submission.Work.RatHurewicz.cellCompression
import Submission.Work.RatHurewicz.kTrick_cell
import Submission.Work.RatHurewicz.gTrick_cell

/-!
# The construction of the treatment of a cell

For each branch of the rule of the grid induction (`0`-cell, `B`-compression, `K`-trick and the
`C`-duals) this file produces the cell homotopy, and `Treat.mk_of_cellHomotopy` spreads it to the
cube with the cutoffs of `exists_cutoffs_collar`, assembling a `Treat`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

open Work.ThomBordism.TwoSet

noncomputable section

variable {X : Type} [TopologicalSpace X] {B C : Set X} {x₀ : ↥(B ∩ C)} {n p q : ℕ}
variable {Φ : C(IC (n + 1), X)}

/-- The inclusion of a subspace, as a continuous map. -/
def inclOf (S : Set X) : C(↥S, X) := ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem inclOf_apply (S : Set X) (x : ↥S) : inclOf S x = (x : X) := rfl

namespace Treat

/-- **Assembling a treatment from a cell homotopy.**  The cutoffs of `exists_cutoffs_collar` and
the two-phase spread of `cellTreatmentFormula` turn a cell homotopy with the required properties
into a `Treat`. -/
theorem mk_of_cellHomotopy {N : ℕ} (hN : 1 ≤ N) (hadm : TriadAdmissible B C x₀ Φ)
    {c : CellIdx (n + 1) N} (hnotboth : ¬ (CellB B Φ c ∧ CellC C Φ c))
    {g : C(IC (n + 1), X)} (H : C(cellSet c × I, X))
    (hH0 : ∀ u : cellSet c, H (u, 0) = g u)
    (hHbd : ∀ (u : cellSet c), (u : IC (n + 1)) ∈ cellRelbd c → ∀ t, H (u, t) = g u)
    (hHvalsB : CellB B Φ c → ∀ u t, (H (u, t) : X) ∈ B)
    (hHvalsC : ¬ CellB B Φ c → ∀ u t, (H (u, t) : X) ∈ C)
    (hconH1 : CellB B Φ c → ¬ CellC C Φ c → cellDim c ≤ p + 1 →
      ∀ z : cellSet c, (H (z, 1) : X) ∈ B ∩ C)
    (hconH2 : CellB B Φ c → ¬ CellC C Φ c → p + 1 < cellDim c →
      ∀ z : cellSet c, (H (z, 1) : X) ∉ C → KW N (p + 2) c (z : IC (n + 1)))
    (hconH3 : ¬ CellB B Φ c → CellC C Φ c → cellDim c ≤ q + 1 →
      ∀ z : cellSet c, (H (z, 1) : X) ∈ B ∩ C)
    (hconH4 : ¬ CellB B Φ c → CellC C Φ c → q + 1 < cellDim c →
      ∀ z : cellSet c, (H (z, 1) : X) ∉ B → GW N (q + 2) c (z : IC (n + 1))) :
    Nonempty (Treat hN B C x₀ Φ g p q c (eps N)) := by
  obtain ⟨μ, ν, hμ0, hμ2, hν1, hν0⟩ := exists_cutoffs_collar hN c (eps_pos hN)
  obtain ⟨G, hGform, hG0, hGoff⟩ :=
    cellTreatmentFormula hN c (cellStarCollar c (eps N)) g H hH0 hHbd μ ν hμ0 hμ2 hν1
  have hGone : ∀ z : cellSet c, G ((z : IC (n + 1)), 1) = H (z, 1) := by
    intro z
    rw [hGform, if_neg]
    · rw [show (⟨clampCell c hN (z : IC (n + 1)), clampCell_mem c hN (z : IC (n + 1))⟩ :
        cellSet c) = z from Subtype.ext (clampCell_eq_self c hN z.2),
        pushTime_one_eq (hμ2 _ z.2) (hν1 _ z.2), hν1 _ z.2]
    · intro hcon
      have h2 := hμ2 _ z.2
      norm_num at hcon
      linarith
  let gs' : ∀ s : I, C(IC (n + 1), X) :=
    fun s => ⟨fun z => G (z, s), G.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hgs' : ∀ s z, gs' s z = G (z, s) := fun s z => rfl
  refine ⟨hadm, hnotboth, G, gs', hgs', H, μ, ν, hμ0, hμ2, hν1, hGform, hH0, hHbd,
    hHvalsB, hHvalsC, ?_, ?_, ?_, ?_⟩
  · intro hB hnC hd z hz
    change G (z, 1) ∈ B ∩ C
    rw [hGone ⟨z, hz⟩]
    exact hconH1 hB hnC hd ⟨z, hz⟩
  · intro hB hnC hd z hz hnot
    change G (z, 1) ∉ C at hnot
    rw [hGone ⟨z, hz⟩] at hnot
    exact hconH2 hB hnC hd ⟨z, hz⟩ hnot
  · intro hnB hC hd z hz
    change G (z, 1) ∈ B ∩ C
    rw [hGone ⟨z, hz⟩]
    exact hconH3 hnB hC hd ⟨z, hz⟩
  · intro hnB hC hd z hz hnot
    change G (z, 1) ∉ B at hnot
    rw [hGone ⟨z, hz⟩] at hnot
    exact hconH4 hnB hC hd ⟨z, hz⟩ hnot


section Branches

variable {N : ℕ}

/-- The `KW`-condition of a subcell, in the cell-local coordinates of the bigger cell. -/
theorem kLocal_of_con {j N : ℕ} (hN : 1 ≤ N) {c c' : CellIdx j N} (hsub : Subcell c' c)
    {P : ℕ} {u : IC j} (hu : u ∈ cellSet c) (h : KW N P c' u) :
    ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
      ∀ m ∈ L, ((invMap c hN ⟨u, hu⟩ m : unitInterval) : ℝ) < 1 / 2 := by
  obtain ⟨L, hL, hLi⟩ := h
  have hdir_lt : ∀ i : ↥L, c.lo i.1 < c.hi i.1 := by
    intro i
    obtain ⟨h1, -⟩ := hLi i.1 i.2
    obtain ⟨h2, h3⟩ := subcell_interval_eq hsub h1
    omega
  let g : ↥L → Fin (cellDim c) := fun i => (cellPsi c).symm ⟨i.1, hdir_lt i⟩
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : (⟨a.1, _⟩ : {i : Fin j // c.lo i < c.hi i}) = ⟨b.1, _⟩ :=
      (cellPsi c).symm.injective hab
    exact Subtype.ext (congrArg (fun t : {i : Fin j // c.lo i < c.hi i} => t.1) h1)
  refine ⟨L.attach.map ⟨g, hg⟩, ?_, ?_⟩
  · rw [Finset.card_map]
    simpa using hL
  · intro m hm
    obtain ⟨i, -, hi⟩ := Finset.mem_map.mp hm
    rw [← hi]
    change ((invMap c hN ⟨u, hu⟩ (g i) : unitInterval) : ℝ) < 1 / 2
    have hdir : (cellPsi c (g i)).1 = i.1 := by
      show (cellPsi c ((cellPsi c).symm ⟨i.1, hdir_lt i⟩)).1 = i.1
      rw [Equiv.apply_symm_apply]
    have hsl : SmallIn N c u i.1 := by
      obtain ⟨h1, h2⟩ := hLi i.1 i.2
      obtain ⟨h3, h4⟩ := subcell_interval_eq hsub h1
      refine ⟨by omega, ?_⟩
      rw [h3] at h2
      exact h2
    rw [← smallIn_iff_invMap hN hu (g i), hdir]
    exact hsl

/-- **The `B`-compression branch of the rule.** -/
theorem bcomp {N : ℕ} (hN : 1 ≤ N) (hadm : TriadAdmissible B C x₀ Φ)
    (hBc : ∀ d, 1 ≤ d → d ≤ p + 1 → CompressRelBd
      {y : ↥B | (y : X) ∈ B ∩ C}
      {y : ↥B | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    {c : CellIdx (n + 1) N} (hB : CellB B Φ c) (hnC : ¬ CellC C Φ c)
    (hd1 : 1 ≤ cellDim c) (hd2 : cellDim c ≤ p + 1)
    {g : C(IC (n + 1), X)} (hVB : ValsB (N := N) B Φ g) (hVC : ValsC (N := N) C Φ g)
    (hPG : ∀ z, g z ∈ pathComponent (x₀ : X))
    (hCon : ∀ c' : CellIdx (n + 1) N, c' ≠ c → Subcell c' c → ConClauses p q B C Φ g c') :
    Nonempty (Treat hN B C x₀ Φ g p q c (eps N)) := by
  classical
  let f : C(cellSet c, ↥B) :=
    ⟨fun u => ⟨g u, hVB c hB u u.2⟩,
      Continuous.subtype_mk (g.continuous.comp continuous_subtype_val) _⟩
  have hbd : ∀ u : cellSet c, (u : IC (n + 1)) ∈ cellRelbd c →
      ((f u : X) ∈ B ∩ C ∧ (f u : X) ∈ pathComponent (x₀ : X)) := by
    intro u hu
    have hsub : Subcell (cOf N (u : IC (n + 1))) c := cOf_sub_of_mem_cellSet u.2
    have hB' : CellB B Φ (cOf N (u : IC (n + 1))) := CellB_subcell hsub hB
    have hlt : cellDim (cOf N (u : IC (n + 1))) < cellDim c :=
      cellDim_cOf_lt_of_mem_cellRelbd N hN hu u.2
    have hne : cOf N (u : IC (n + 1)) ≠ c := fun h => by rw [h] at hlt; omega
    have hmem : (u : IC (n + 1)) ∈ cellSet (cOf N (u : IC (n + 1))) := mem_cOf N hN _
    refine ⟨⟨hVB _ hB' _ hmem, ?_⟩, hPG _⟩
    by_cases hC' : CellC C Φ (cOf N (u : IC (n + 1)))
    · exact hVC _ hC' _ hmem
    · obtain ⟨cl1, -, -, -⟩ := hCon _ hne hsub
      exact (cl1 hB' hC' (by omega) (u : IC (n + 1)) hmem).2
  obtain ⟨HB, hHB0, hHBbd, hHB1⟩ := cellCompression x₀ p hBc hN c hd1 hd2 f hbd
  have hH0' : ∀ u : cellSet c, (inclOf B |>.comp HB) (u, 0) = g u := by
    intro u
    show ((HB (u, 0) : ↥B) : X) = g u
    exact congrArg (fun w : ↥B => (w : X)) (hHB0 u)
  have hHbd' : ∀ (u : cellSet c), (u : IC (n + 1)) ∈ cellRelbd c → ∀ t,
      (inclOf B |>.comp HB) (u, t) = g u := by
    intro u hu t
    show ((HB (u, t) : ↥B) : X) = g u
    exact congrArg (fun w : ↥B => (w : X)) (hHBbd u hu t)
  have hHvalsB' : CellB B Φ c → ∀ u t, ((inclOf B |>.comp HB) (u, t) : X) ∈ B := by
    intro _ u t
    exact (HB (u, t)).2
  have hHvalsC' : ¬ CellB B Φ c → ∀ u t, ((inclOf B |>.comp HB) (u, t) : X) ∈ C :=
    fun h => absurd hB h
  have hcon1' : CellB B Φ c → ¬ CellC C Φ c → cellDim c ≤ p + 1 →
      ∀ z : cellSet c, ((inclOf B |>.comp HB) (z, 1) : X) ∈ B ∩ C := by
    intro _ _ _ z
    show ((HB (z, 1) : ↥B) : X) ∈ B ∩ C
    exact hHB1 z
  have hcon2' : CellB B Φ c → ¬ CellC C Φ c → p + 1 < cellDim c →
      ∀ z : cellSet c, ((inclOf B |>.comp HB) (z, 1) : X) ∉ C →
        KW N (p + 2) c (z : IC (n + 1)) := by
    intro _ _ hd z
    exact absurd hd (by omega)
  have hcon3' : ¬ CellB B Φ c → CellC C Φ c → cellDim c ≤ q + 1 →
      ∀ z : cellSet c, ((inclOf B |>.comp HB) (z, 1) : X) ∈ B ∩ C := by
    intro hnB _ _ z
    exact absurd hB hnB
  have hcon4' : ¬ CellB B Φ c → CellC C Φ c → q + 1 < cellDim c →
      ∀ z : cellSet c, ((inclOf B |>.comp HB) (z, 1) : X) ∉ B → GW N (q + 2) c (z : IC (n + 1)) := by
    intro hnB _ hd z
    exact absurd hB hnB
  exact Treat.mk_of_cellHomotopy hN hadm (fun h => hnC h.2) (inclOf B |>.comp HB)
    hH0' hHbd' hHvalsB' hHvalsC' hcon1' hcon2' hcon3' hcon4'

/-- **The `K`-trick branch of the rule.** -/
theorem ktrick {N : ℕ} (hN : 1 ≤ N) (hadm : TriadAdmissible B C x₀ Φ)
    {c : CellIdx (n + 1) N} (hB : CellB B Φ c) (hnC : ¬ CellC C Φ c)
    (hd : p + 1 < cellDim c)
    {g : C(IC (n + 1), X)} (hVB : ValsB (N := N) B Φ g) (hVC : ValsC (N := N) C Φ g)
    (hPG : ∀ z, g z ∈ pathComponent (x₀ : X))
    (hCon : ∀ c' : CellIdx (n + 1) N, c' ≠ c → Subcell c' c → ConClauses p q B C Φ g c') :
    Nonempty (Treat hN B C x₀ Φ g p q c (eps N)) := by
  classical
  let f : C(cellSet c, X) := ⟨fun u => g u, g.continuous.comp continuous_subtype_val⟩
  have hhyp : ∀ u : cellSet c, (u : IC (n + 1)) ∈ cellRelbd c → f u ∈ {y : X | y ∉ C} →
      ∃ L : Finset (Fin (cellDim c)), p + 2 ≤ L.card ∧
        ∀ m ∈ L, ((invMap c hN u m : unitInterval) : ℝ) < 1 / 2 := by
    intro u hu huC
    have hsub : Subcell (cOf N (u : IC (n + 1))) c := cOf_sub_of_mem_cellSet u.2
    have hlt : cellDim (cOf N (u : IC (n + 1))) < cellDim c :=
      cellDim_cOf_lt_of_mem_cellRelbd N hN hu u.2
    have hne : cOf N (u : IC (n + 1)) ≠ c := fun h => by rw [h] at hlt; omega
    have hB' : CellB B Φ (cOf N (u : IC (n + 1))) := CellB_subcell hsub hB
    have hmem : (u : IC (n + 1)) ∈ cellSet (cOf N (u : IC (n + 1))) := mem_cOf N hN _
    have hnC' : ¬ CellC C Φ (cOf N (u : IC (n + 1))) := by
      intro hC'
      exact huC (hVC _ hC' _ hmem)
    obtain ⟨cl1, cl2, -, -⟩ := hCon _ hne hsub
    by_cases hle : cellDim (cOf N (u : IC (n + 1))) ≤ p + 1
    · exfalso
      exact huC (cl1 hB' hnC' hle (u : IC (n + 1)) hmem).2
    · exact kLocal_of_con hN hsub u.2 (cl2 hB' hnC' (by omega) (u : IC (n + 1)) hmem huC)
  obtain ⟨HB, hHB0, hHBbd, hHBvals, hHB1⟩ := kTrickCellVals hN c (p + 2) (by omega) f _
    (by intro u hu huA; exact hhyp u hu huA)
  have hHvalsB' : CellB B Φ c → ∀ u t, (HB (u, t) : X) ∈ B := by
    intro _ u t
    obtain ⟨u', hu'⟩ := hHBvals u t
    rw [hu']; exact hVB c hB u' u'.2
  have hHvalsC' : ¬ CellB B Φ c → ∀ u t, (HB (u, t) : X) ∈ C :=
    fun h => absurd hB h
  have hcon1' : CellB B Φ c → ¬ CellC C Φ c → cellDim c ≤ p + 1 →
      ∀ z : cellSet c, (HB (z, 1) : X) ∈ B ∩ C := by
    intro _ _ hd' z
    exact absurd hd' (by omega)
  have hcon2' : CellB B Φ c → ¬ CellC C Φ c → p + 1 < cellDim c →
      ∀ z : cellSet c, (HB (z, 1) : X) ∉ C → KW N (p + 2) c (z : IC (n + 1)) := by
    intro _ _ _ z hz
    obtain ⟨L, hL, hLi⟩ := hHB1 z hz
    exact kw_of_local hN z.2 ⟨L, hL, hLi⟩
  have hcon3' : ¬ CellB B Φ c → CellC C Φ c → cellDim c ≤ q + 1 →
      ∀ z : cellSet c, (HB (z, 1) : X) ∈ B ∩ C := by
    intro hnB _ _ z
    exact absurd hB hnB
  have hcon4' : ¬ CellB B Φ c → CellC C Φ c → q + 1 < cellDim c →
      ∀ z : cellSet c, (HB (z, 1) : X) ∉ B → GW N (q + 2) c (z : IC (n + 1)) := by
    intro hnB _ _ z
    exact absurd hB hnB
  exact Treat.mk_of_cellHomotopy hN hadm (fun h => hnC h.2) HB
    hHB0 hHBbd hHvalsB' hHvalsC' hcon1' hcon2' hcon3' hcon4'

/-- The `GW`-condition of a subcell, in the cell-local coordinates of the bigger cell. -/
theorem gLocal_of_con {j N : ℕ} (hN : 1 ≤ N) {c c' : CellIdx j N} (hsub : Subcell c' c)
    {P : ℕ} {u : IC j} (hu : u ∈ cellSet c) (h : GW N P c' u) :
    ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
      ∀ m ∈ L, 1 / 2 < ((invMap c hN ⟨u, hu⟩ m : unitInterval) : ℝ) := by
  obtain ⟨L, hL, hLi⟩ := h
  have hdir_lt : ∀ i : ↥L, c.lo i.1 < c.hi i.1 := by
    intro i
    obtain ⟨h1, -⟩ := hLi i.1 i.2
    obtain ⟨h2, h3⟩ := subcell_interval_eq hsub h1
    omega
  let g : ↥L → Fin (cellDim c) := fun i => (cellPsi c).symm ⟨i.1, hdir_lt i⟩
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : (⟨a.1, hdir_lt a⟩ : {i : Fin j // c.lo i < c.hi i}) = ⟨b.1, hdir_lt b⟩ :=
      (cellPsi c).symm.injective hab
    exact Subtype.ext (congrArg (fun t : {i : Fin j // c.lo i < c.hi i} => t.1) h1)
  refine ⟨L.attach.map ⟨g, hg⟩, ?_, ?_⟩
  · rw [Finset.card_map]
    simpa using hL
  · intro m hm
    obtain ⟨i, -, hi⟩ := Finset.mem_map.mp hm
    rw [← hi]
    change 1 / 2 < ((invMap c hN ⟨u, hu⟩ (g i) : unitInterval) : ℝ)
    have hdir : (cellPsi c (g i)).1 = i.1 := by
      show (cellPsi c ((cellPsi c).symm ⟨i.1, hdir_lt i⟩)).1 = i.1
      rw [Equiv.apply_symm_apply]
    have hsl : LargeIn N c u i.1 := by
      obtain ⟨h1, h2⟩ := hLi i.1 i.2
      obtain ⟨h3, h4⟩ := subcell_interval_eq hsub h1
      refine ⟨by omega, ?_⟩
      rw [h3] at h2
      exact h2
    rw [← largeIn_iff_invMap hN hu (g i), hdir]
    exact hsl

/-- **The `0`-cell branch of the rule, `B`-side.** -/
theorem zeroB {N : ℕ} (hN : 1 ≤ N) (hadm : TriadAdmissible B C x₀ Φ)
    {c : CellIdx (n + 1) N} (hB : CellB B Φ c) (hnotboth : ¬ (CellB B Φ c ∧ CellC C Φ c))
    (h0 : cellDim c = 0)
    {g : C(IC (n + 1), X)} (hVB : ValsB (N := N) B Φ g)
    (hPG : ∀ z, g z ∈ pathComponent (x₀ : X))
    (hB0 : ∀ b : ↥B, (b : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.1⟩ b)) :
    Nonempty (Treat hN B C x₀ Φ g p q c (eps N)) := by
  obtain ⟨H, hH0, hHbd, hH1, hHvals, -⟩ :=
    zeroCellTreatmentB hN c h0 g hB0 (fun x => hVB c hB x x.2) (fun x => hPG _)
  exact mk_of_cellHomotopy hN hadm hnotboth H hH0 hHbd
    (fun _ => hHvals) (fun h => absurd hB h)
    (fun _ _ _ z => hH1 z)
    (fun _ _ hd z => absurd hd (by omega))
    (fun hnB _ _ z => absurd hB hnB)
    (fun _ _ hd z => absurd hd (by omega))

/-- **The `0`-cell branch of the rule, `C`-side.** -/
theorem zeroC {N : ℕ} (hN : 1 ≤ N) (hadm : TriadAdmissible B C x₀ Φ)
    {c : CellIdx (n + 1) N} (hC : CellC C Φ c) (hnotboth : ¬ (CellB B Φ c ∧ CellC C Φ c))
    (h0 : cellDim c = 0)
    {g : C(IC (n + 1), X)} (hVC : ValsC (N := N) C Φ g)
    (hPG : ∀ z, g z ∈ pathComponent (x₀ : X))
    (hC0 : ∀ b : ↥C, (b : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.2⟩ b)) :
    Nonempty (Treat hN B C x₀ Φ g p q c (eps N)) := by
  obtain ⟨H, hH0, hHbd, hH1, hHvals, -⟩ :=
    zeroCellTreatmentC hN c h0 g hC0 (fun x => hVC c hC x x.2) (fun x => hPG _)
  exact mk_of_cellHomotopy hN hadm hnotboth H hH0 hHbd
    (fun hB => (hnotboth ⟨hB, hC⟩).elim) (fun _ => hHvals)
    (fun hB _ _ z => absurd hB (fun hB' => hnotboth ⟨hB', hC⟩))
    (fun _ _ hd z => absurd hd (by omega))
    (fun _ _ _ z => hH1 z)
    (fun _ _ hd z => absurd hd (by omega))

/-- **The `C`-compression branch of the rule.** -/
theorem ccomp {N : ℕ} (hN : 1 ≤ N) (hadm : TriadAdmissible B C x₀ Φ)
    (hCc : ∀ d, 1 ≤ d → d ≤ q + 1 → CompressRelBd
      {y : ↥C | (y : X) ∈ B ∩ C}
      {y : ↥C | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    {c : CellIdx (n + 1) N} (hnB : ¬ CellB B Φ c) (hC : CellC C Φ c)
    (hd1 : 1 ≤ cellDim c) (hd2 : cellDim c ≤ q + 1)
    {g : C(IC (n + 1), X)} (hVC : ValsC (N := N) C Φ g) (hVB : ValsB (N := N) B Φ g)
    (hPG : ∀ z, g z ∈ pathComponent (x₀ : X))
    (hCon : ∀ c' : CellIdx (n + 1) N, c' ≠ c → Subcell c' c → ConClauses p q B C Φ g c') :
    Nonempty (Treat hN B C x₀ Φ g p q c (eps N)) := by
  classical
  let f : C(cellSet c, ↥C) :=
    ⟨fun u => ⟨g u, hVC c hC u u.2⟩,
      Continuous.subtype_mk (g.continuous.comp continuous_subtype_val) _⟩
  have hbd : ∀ u : cellSet c, (u : IC (n + 1)) ∈ cellRelbd c →
      ((f u : X) ∈ B ∩ C ∧ (f u : X) ∈ pathComponent (x₀ : X)) := by
    intro u hu
    have hsub : Subcell (cOf N (u : IC (n + 1))) c := cOf_sub_of_mem_cellSet u.2
    have hC' : CellC C Φ (cOf N (u : IC (n + 1))) := CellC_subcell hsub hC
    have hlt : cellDim (cOf N (u : IC (n + 1))) < cellDim c :=
      cellDim_cOf_lt_of_mem_cellRelbd N hN hu u.2
    have hne : cOf N (u : IC (n + 1)) ≠ c := fun h => by rw [h] at hlt; omega
    have hmem : (u : IC (n + 1)) ∈ cellSet (cOf N (u : IC (n + 1))) := mem_cOf N hN _
    refine ⟨⟨?_, hVC _ hC' _ hmem⟩, hPG _⟩
    by_cases hB' : CellB B Φ (cOf N (u : IC (n + 1)))
    · exact hVB _ hB' _ hmem
    · obtain ⟨-, -, cl3, -⟩ := hCon _ hne hsub
      exact (cl3 hB' hC' (by omega) (u : IC (n + 1)) hmem).1
  obtain ⟨HB, hHB0, hHBbd, hHB1⟩ := cellCompressionRight x₀ q hCc hN c hd1 hd2 f hbd
  have hH0' : ∀ u : cellSet c, (inclOf C |>.comp HB) (u, 0) = g u := by
    intro u
    show ((HB (u, 0) : ↥C) : X) = g u
    exact congrArg (fun w : ↥C => (w : X)) (hHB0 u)
  have hHbd' : ∀ (u : cellSet c), (u : IC (n + 1)) ∈ cellRelbd c → ∀ t,
      (inclOf C |>.comp HB) (u, t) = g u := by
    intro u hu t
    show ((HB (u, t) : ↥C) : X) = g u
    exact congrArg (fun w : ↥C => (w : X)) (hHBbd u hu t)
  have hHvalsB' : CellB B Φ c → ∀ u t, ((inclOf C |>.comp HB) (u, t) : X) ∈ B :=
    fun h => absurd h hnB
  have hHvalsC' : ¬ CellB B Φ c → ∀ u t, ((inclOf C |>.comp HB) (u, t) : X) ∈ C := by
    intro _ u t
    exact (HB (u, t)).2
  have hcon1' : CellB B Φ c → ¬ CellC C Φ c → cellDim c ≤ p + 1 →
      ∀ z : cellSet c, ((inclOf C |>.comp HB) (z, 1) : X) ∈ B ∩ C := by
    intro hB _ _ z
    exact absurd hB hnB
  have hcon2' : CellB B Φ c → ¬ CellC C Φ c → p + 1 < cellDim c →
      ∀ z : cellSet c, ((inclOf C |>.comp HB) (z, 1) : X) ∉ C →
        KW N (p + 2) c (z : IC (n + 1)) := by
    intro hB _ _ z
    exact absurd hB hnB
  have hcon3' : ¬ CellB B Φ c → CellC C Φ c → cellDim c ≤ q + 1 →
      ∀ z : cellSet c, ((inclOf C |>.comp HB) (z, 1) : X) ∈ B ∩ C := by
    intro _ _ _ z
    show ((HB (z, 1) : ↥C) : X) ∈ B ∩ C
    exact hHB1 z
  have hcon4' : ¬ CellB B Φ c → CellC C Φ c → q + 1 < cellDim c →
      ∀ z : cellSet c, ((inclOf C |>.comp HB) (z, 1) : X) ∉ B →
        GW N (q + 2) c (z : IC (n + 1)) := by
    intro _ _ hd' z
    exact absurd hd' (by omega)
  exact mk_of_cellHomotopy hN hadm (fun h => hnB h.1) (inclOf C |>.comp HB)
    hH0' hHbd' hHvalsB' hHvalsC' hcon1' hcon2' hcon3' hcon4'

/-- **The `G`-trick branch of the rule.** -/
theorem gtrick {N : ℕ} (hN : 1 ≤ N) (hadm : TriadAdmissible B C x₀ Φ)
    {c : CellIdx (n + 1) N} (hnB : ¬ CellB B Φ c) (hC : CellC C Φ c)
    (hd : q + 1 < cellDim c)
    {g : C(IC (n + 1), X)} (hVC : ValsC (N := N) C Φ g) (hVB : ValsB (N := N) B Φ g)
    (hPG : ∀ z, g z ∈ pathComponent (x₀ : X))
    (hCon : ∀ c' : CellIdx (n + 1) N, c' ≠ c → Subcell c' c → ConClauses p q B C Φ g c') :
    Nonempty (Treat hN B C x₀ Φ g p q c (eps N)) := by
  classical
  let f : C(cellSet c, X) := ⟨fun u => g u, g.continuous.comp continuous_subtype_val⟩
  have hhyp : ∀ u : cellSet c, (u : IC (n + 1)) ∈ cellRelbd c → f u ∈ {y : X | y ∉ B} →
      ∃ L : Finset (Fin (cellDim c)), q + 2 ≤ L.card ∧
        ∀ m ∈ L, 1 / 2 < ((invMap c hN u m : unitInterval) : ℝ) := by
    intro u hu huB
    have hsub : Subcell (cOf N (u : IC (n + 1))) c := cOf_sub_of_mem_cellSet u.2
    have hlt : cellDim (cOf N (u : IC (n + 1))) < cellDim c :=
      cellDim_cOf_lt_of_mem_cellRelbd N hN hu u.2
    have hne : cOf N (u : IC (n + 1)) ≠ c := fun h => by rw [h] at hlt; omega
    have hC' : CellC C Φ (cOf N (u : IC (n + 1))) := CellC_subcell hsub hC
    have hmem : (u : IC (n + 1)) ∈ cellSet (cOf N (u : IC (n + 1))) := mem_cOf N hN _
    have hnB' : ¬ CellB B Φ (cOf N (u : IC (n + 1))) := by
      intro hB'
      exact huB (hVB _ hB' _ hmem)
    obtain ⟨-, -, cl3, cl4⟩ := hCon _ hne hsub
    by_cases hle : cellDim (cOf N (u : IC (n + 1))) ≤ q + 1
    · exfalso
      exact huB (cl3 hnB' hC' hle (u : IC (n + 1)) hmem).1
    · exact gLocal_of_con hN hsub u.2 (cl4 hnB' hC' (by omega) (u : IC (n + 1)) hmem huB)
  obtain ⟨HB, hHB0, hHBbd, hHBvals, hHB1⟩ := gTrickCellVals hN c (q + 2) (by omega) f _
    (by intro u hu huA; exact hhyp u hu huA)
  have hHvalsC' : ¬ CellB B Φ c → ∀ u t, (HB (u, t) : X) ∈ C := by
    intro _ u t
    obtain ⟨u', hu'⟩ := hHBvals u t
    rw [hu']; exact hVC c hC u' u'.2
  have hHvalsB' : CellB B Φ c → ∀ u t, (HB (u, t) : X) ∈ B :=
    fun h => absurd h hnB
  have hcon3' : ¬ CellB B Φ c → CellC C Φ c → cellDim c ≤ q + 1 →
      ∀ z : cellSet c, (HB (z, 1) : X) ∈ B ∩ C := by
    intro _ _ hd' z
    exact absurd hd' (by omega)
  have hcon4' : ¬ CellB B Φ c → CellC C Φ c → q + 1 < cellDim c →
      ∀ z : cellSet c, (HB (z, 1) : X) ∉ B → GW N (q + 2) c (z : IC (n + 1)) := by
    intro _ _ _ z hz
    obtain ⟨L, hL, hLi⟩ := hHB1 z hz
    exact gw_of_local hN z.2 ⟨L, hL, hLi⟩
  have hcon1' : CellB B Φ c → ¬ CellC C Φ c → cellDim c ≤ p + 1 →
      ∀ z : cellSet c, (HB (z, 1) : X) ∈ B ∩ C :=
    fun hB _ _ z => absurd hB hnB
  have hcon2' : CellB B Φ c → ¬ CellC C Φ c → p + 1 < cellDim c →
      ∀ z : cellSet c, (HB (z, 1) : X) ∉ C → KW N (p + 2) c (z : IC (n + 1)) :=
    fun hB _ _ z => absurd hB hnB
  exact mk_of_cellHomotopy hN hadm (fun h => hnB h.1) HB
    hHB0 hHBbd hHvalsB' hHvalsC' hcon1' hcon2' hcon3' hcon4'

/-- **The rule of the grid induction**: every cell which is not labelled by both `B` and `C` is
treated, by compression when its dimension is at most the relevant bound and by the
`K`/`G`-trick otherwise; a `0`-cell is joined to `B ∩ C` by a path. -/
theorem rule {N : ℕ} (hN : 1 ≤ N) (hadm : TriadAdmissible B C x₀ Φ)
    (hBc : ∀ d, 1 ≤ d → d ≤ p + 1 → CompressRelBd
      {y : ↥B | (y : X) ∈ B ∩ C}
      {y : ↥B | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    (hCc : ∀ d, 1 ≤ d → d ≤ q + 1 → CompressRelBd
      {y : ↥C | (y : X) ∈ B ∩ C}
      {y : ↥C | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    (hB0 : ∀ b : ↥B, (b : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.1⟩ b))
    (hC0 : ∀ b : ↥C, (b : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.2⟩ b))
    {c : CellIdx (n + 1) N} (hsub : CellB B Φ c ∨ CellC C Φ c)
    (hnotboth : ¬ (CellB B Φ c ∧ CellC C Φ c))
    {g : C(IC (n + 1), X)} (hVB : ValsB (N := N) B Φ g) (hVC : ValsC (N := N) C Φ g)
    (hPG : ∀ z, g z ∈ pathComponent (x₀ : X))
    (hCon : ∀ c' : CellIdx (n + 1) N, c' ≠ c → Subcell c' c → ConClauses p q B C Φ g c') :
    Nonempty (Treat hN B C x₀ Φ g p q c (eps N)) := by
  by_cases hB : CellB B Φ c
  · by_cases h0 : cellDim c = 0
    · exact zeroB hN hadm hB hnotboth h0 hVB hPG hB0
    · have hd1 : 1 ≤ cellDim c := by omega
      by_cases hle : cellDim c ≤ p + 1
      · exact  bcomp hN hadm hBc hB (fun hC => hnotboth ⟨hB, hC⟩) hd1 hle hVB hVC hPG hCon
      · exact  ktrick hN hadm hB (fun hC => hnotboth ⟨hB, hC⟩) (by omega) hVB hVC hPG hCon
  · have hC : CellC C Φ c := hsub.resolve_left hB
    by_cases h0 : cellDim c = 0
    · exact zeroC hN hadm hC hnotboth h0 hVC hPG hC0
    · have hd1 : 1 ≤ cellDim c := by omega
      by_cases hle : cellDim c ≤ q + 1
      · exact  ccomp hN hadm hCc hB hC hd1 hle hVC hVB hPG hCon
      · exact  gtrick hN hadm hB hC (by omega) hVC hVB hPG hCon

end Branches

end Treat

end

end Work.RatHurewicz.Triad
