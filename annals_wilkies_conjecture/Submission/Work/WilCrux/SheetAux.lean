/-
  `Work.WilCrux` — assembly helpers for `IsolatedSheet` (node N1 of `WilCrux/DESIGN.md`).

  Projection bookkeeping: the iterated projection `projOver` of a set, membership of the
  projections of the cells of a cylindrical decomposition in the projected decomposition, and
  the construction of `IsCellOver` from a cell of a decomposition.
-/
import Mathlib
import Submission.Work.WilCrux.SheetDefs
import Submission.Work.WilCrux.sep_or_lex
import Submission.Work.WilCrux.bandRank_bandIdx
import Submission.Work.WilCrux.graphRank_graphIdx

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign WilkiesConjecture

/-! ## 1. Basic API of a cylindrical decomposition -/

/-- Cells of a cylindrical decomposition are cells and nonempty. -/
theorem isCylDecomp_cell {n : ℕ} {C : Finset (Set (Fin n → ℝ))} (h : IsCylDecomp n C)
    {κ : Set (Fin n → ℝ)} (hκ : κ ∈ C) : IsCell n κ ∧ κ.Nonempty := by
  cases n with
  | zero =>
      rw [show C = {Set.univ} from h, Finset.mem_singleton] at hκ
      subst hκ
      exact ⟨IsCell.zero, ⟨fun i => i.elim0, trivial⟩⟩
  | succ n => exact h.1 κ hκ

/-- A cell of a cylindrical decomposition is nonempty. -/
theorem cylDecomp_cell_nonempty {n : ℕ} {C : Finset (Set (Fin n → ℝ))} (h : IsCylDecomp n C)
    {κ : Set (Fin n → ℝ)} (hκ : κ ∈ C) : κ.Nonempty := (isCylDecomp_cell h hκ).2

/-- The cells of a cylindrical decomposition are pairwise disjoint. -/
theorem cylDecomp_pairwiseDisjoint {n : ℕ} {C : Finset (Set (Fin n → ℝ))}
    (h : IsCylDecomp n C) : (C : Set (Set (Fin n → ℝ))).PairwiseDisjoint id := by
  cases n with
  | zero =>
      intro a ha b hb hne
      rw [show C = {Set.univ} from h] at ha hb
      have ha' : a = Set.univ := by simpa using ha
      have hb' : b = Set.univ := by simpa using hb
      exact absurd (ha'.trans hb'.symm) hne
  | succ n => exact h.2.1

/-- The cells of a cylindrical decomposition cover. -/
theorem cylDecomp_cover {n : ℕ} {C : Finset (Set (Fin n → ℝ))} (h : IsCylDecomp n C)
    (z : Fin n → ℝ) : ∃ κ ∈ C, z ∈ κ := by
  cases n with
  | zero =>
      refine ⟨Set.univ, ?_, trivial⟩
      rw [show C = {Set.univ} from h]
      exact Finset.mem_singleton_self _
  | succ n => exact h.2.2.1 z

/-! ## 2. Projections of a set and of a decomposition -/

/-- The projection of a point of `κ` to the first `m` coordinates is a point of `projOver`. -/
theorem mem_projOver {m N : ℕ} {κ : Set (Fin (m + N) → ℝ)} {p : Fin (m + N) → ℝ}
    (hp : p ∈ κ) : (fun i : Fin m => p (Fin.castAdd N i)) ∈ projOver m N κ := by
  induction N with
  | zero => simpa using hp
  | succ N ih =>
      have h1 : Fin.init p ∈ base κ := ⟨p, hp, rfl⟩
      have h2 : (fun i : Fin m => Fin.init p (Fin.castAdd N i)) ∈ projOver m N (base κ) :=
        ih h1
      have hfun : (fun i : Fin m => Fin.init p (Fin.castAdd N i))
          = fun i : Fin m => p (Fin.castAdd (N + 1) i) := by
        funext i
        exact congrArg p (Fin.ext rfl)
      rw [projOver_succ, ← hfun]
      exact h2

/-- The projection of a cell of a decomposition belongs to the projected decomposition. -/
theorem projOver_mem_projDecomp {m N : ℕ} {C : Finset (Set (Fin (m + N) → ℝ))}
    {κ : Set (Fin (m + N) → ℝ)} (hκ : κ ∈ C) : projOver m N κ ∈ projDecomp m N C := by
  induction N with
  | zero => exact hκ
  | succ N ih =>
      have h1 : Fin.init '' κ ∈ C.image (fun σ => Fin.init '' σ) :=
        Finset.mem_image.mpr ⟨κ, hκ, rfl⟩
      have h2 := ih (C := C.image (fun σ => Fin.init '' σ)) h1
      rw [projDecomp, projOver_succ]
      exact h2

/-- The projection of a cylindrical decomposition is a cylindrical decomposition. -/
theorem isCylDecomp_projDecomp {m N : ℕ} {C : Finset (Set (Fin (m + N) → ℝ))}
    (h : IsCylDecomp (m + N) C) : IsCylDecomp m (projDecomp m N C) := by
  induction N with
  | zero => exact h
  | succ N ih =>
      have h1 : IsCylDecomp (m + N) (C.image (fun κ => Fin.init '' κ)) := h.2.2.2
      rw [projDecomp]
      exact ih h1

/-- A cell of the projected decomposition is nonempty. -/
theorem projOver_nonempty {m N : ℕ} {κ : Set (Fin (m + N) → ℝ)} (h : κ.Nonempty) :
    (projOver m N κ).Nonempty := by
  obtain ⟨p, hp⟩ := h
  exact ⟨_, mem_projOver hp⟩

/-- A cell of the projected decomposition is a cell. -/
theorem projOver_isCell {m N : ℕ} {C : Finset (Set (Fin (m + N) → ℝ))}
    (hdec : IsCylDecomp (m + N) C) {κ : Set (Fin (m + N) → ℝ)} (hκ : κ ∈ C) :
    IsCell m (projOver m N κ) :=
  (isCylDecomp_cell (isCylDecomp_projDecomp hdec) (projOver_mem_projDecomp hκ)).1

/-! ## 3. Cells of a decomposition over a prescribed base -/

/-- A cell of a decomposition, with the projection prescribed, is a cell over that base. -/
theorem IsCellOver.of_mem {m : ℕ} (N : ℕ) {C : Finset (Set (Fin (m + N) → ℝ))} :
    IsCylDecomp (m + N) C → ∀ {C₀ : Set (Fin m → ℝ)} {κ : Set (Fin (m + N) → ℝ)},
    κ ∈ C → projOver m N κ = C₀ → IsCellOver m N C₀ κ := by
  induction N with
  | zero =>
      intro hdec C₀ κ hκ hproj
      unfold IsCellOver
      exact ⟨hproj, cylDecomp_cell_nonempty hdec hκ⟩
  | succ N ih =>
      intro hdec C₀ κ hκ hproj
      refine ⟨(isCylDecomp_cell hdec hκ).2, (isCylDecomp_cell hdec hκ).1, ?_⟩
      have h3 : projOver m N (base κ) = C₀ := by rw [← projOver_succ]; exact hproj
      exact ih hdec.2.2.2 (Finset.mem_image.mpr ⟨κ, hκ, rfl⟩) h3

/-- Two cells of the projected decomposition that share a point are equal. -/
theorem eq_of_mem_projDecomp {m N : ℕ} {C : Finset (Set (Fin (m + N) → ℝ))}
    (hdec : IsCylDecomp (m + N) C) {σ σ' : Set (Fin m → ℝ)}
    (hσ : σ ∈ projDecomp m N C) (hσ' : σ' ∈ projDecomp m N C) {x : Fin m → ℝ}
    (hx : x ∈ σ) (hx' : x ∈ σ') : σ = σ' := by
  by_contra hne
  have hdisj : Disjoint σ σ' :=
    cylDecomp_pairwiseDisjoint (isCylDecomp_projDecomp hdec) hσ hσ' hne
  exact (Set.disjoint_left.mp hdisj hx) hx'


/-! ## 4. The box `W × U` and distance estimates -/

/-- The box of points of `ℝ^{m+N}` over `W` with fibre in `U`. -/
def box (m N : ℕ) (W : Set (Fin m → ℝ)) (U : Set (Fin N → ℝ)) : Set (Fin (m + N) → ℝ) :=
  {z | (fun i : Fin m => z (Fin.castAdd N i)) ∈ W ∧
    (fun j : Fin N => z (Fin.natAdd m j)) ∈ U}

theorem isOpen_box {m N : ℕ} {W : Set (Fin m → ℝ)} {U : Set (Fin N → ℝ)}
    (hW : IsOpen W) (hU : IsOpen U) : IsOpen (box m N W U) := by
  refine IsOpen.inter ?_ ?_
  · exact hW.preimage (continuous_pi fun i => continuous_apply _)
  · exact hU.preimage (continuous_pi fun j => continuous_apply _)

/-- The projection to the first `m` coordinates does not increase distances. -/
theorem dist_proj_le {m N : ℕ} (z p : Fin (m + N) → ℝ) :
    dist (fun i : Fin m => z (Fin.castAdd N i)) (fun i : Fin m => p (Fin.castAdd N i))
      ≤ dist z p := by
  refine (dist_pi_le_iff dist_nonneg).mpr fun i => ?_
  exact dist_le_pi_dist z p _

/-- A point outside a closed set is at positive distance from it. -/
theorem exists_pos_dist_of_not_mem_closure {α : Type*} [PseudoMetricSpace α] {A : Set α} {x : α}
    (h : x ∉ closure A) : ∃ ε > 0, ∀ y ∈ A, ε ≤ dist x y := by
  rw [Metric.mem_closure_iff] at h
  push_neg at h
  obtain ⟨ε, hε, hball⟩ := h
  exact ⟨ε, hε, fun y hy => hball y hy⟩

/-! ## 5. Isolation of the maximal cell -/

/-- **(N1, isolation.)**  Let `κ` be a cell of a decomposition `C` of `ℝ^{m+N}`, contained in
`Z`, over the open base cell `C₀`, and maximal among the `Z`-cells over `C₀` that meet
`W × U` in the word order.  Then each of its points over `W × U` is isolated inside `Z`. -/
theorem isolation {m N : ℕ} {C : Finset (Set (Fin (m + N) → ℝ))} (hdec : IsCylDecomp (m + N) C)
    {C₀ : Set (Fin m → ℝ)} (hC₀o : IsOpen C₀)
    {W : Set (Fin m → ℝ)} (hW : IsOpen W) {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    {Z : Set (Fin (m + N) → ℝ)} (hsep : ∀ κ ∈ C, κ ⊆ Z ∨ Disjoint κ Z)
    {κ : Set (Fin (m + N) → ℝ)} (hκC : κ ∈ C) (hκZ : κ ⊆ Z)
    (hproj : projOver m N κ = C₀)
    (hmax : ∀ κ' ∈ C, κ' ⊆ Z → projOver m N κ' = C₀ → (κ' ∩ box m N W U).Nonempty →
      ¬ LexLt (word m N κ) (word m N κ'))
    {p : Fin (m + N) → ℝ} (hpκ : p ∈ κ) (hpbox : p ∈ box m N W U) :
    ∃ ε > 0, ∀ z ∈ Z, dist z p < ε → z ∈ κ := by
  classical
  have hWU : IsOpen (box m N W U) := isOpen_box hW hU
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.isOpen_iff.mp hWU p hpbox
  have hpC₀ : (fun i : Fin m => p (Fin.castAdd N i)) ∈ C₀ := by
    rw [← hproj]; exact mem_projOver hpκ
  obtain ⟨ε₂, hε₂, hb₂⟩ :=
    Metric.isOpen_iff.mp hC₀o (fun i : Fin m => p (Fin.castAdd N i)) hpC₀
  have hC₀mem : C₀ ∈ projDecomp m N C := by
    rw [← hproj]; exact projOver_mem_projDecomp hκC
  set Bad : Finset (Set (Fin (m + N) → ℝ)) :=
    C.filter (fun κ' => κ' ⊆ Z ∧ projOver m N κ' = C₀ ∧ κ' ≠ κ) with hBad
  have hfar : ∀ κ' ∈ Bad, ∃ r : ℝ, 0 < r ∧ Disjoint κ' (Metric.ball p r) := by
    intro κ' hκ'
    rw [hBad, Finset.mem_filter] at hκ'
    obtain ⟨hκ'C, hκ'Z, hκ'proj, hκ'ne⟩ := hκ'
    rcases sep_or_lex hdec hC₀o hκC hκ'C hproj hκ'proj hκ'ne.symm with hdisj | hlex
    · have hpnot : p ∉ closure κ' := by
        intro hmem
        have : p ∈ κ ∩ closure κ' := ⟨hpκ, hmem⟩
        rw [hdisj] at this
        exact this
      obtain ⟨r, hr, hr'⟩ := exists_pos_dist_of_not_mem_closure hpnot
      refine ⟨r, hr, ?_⟩
      rw [Set.disjoint_left]
      intro x hx hxball
      have hlt : dist p x < r := by
        simpa [Metric.mem_ball, dist_comm] using hxball
      exact absurd (hr' x hx) (not_le.mpr hlt)
    · have hempty : κ' ∩ box m N W U = ∅ := by
        by_contra hcon
        exact hmax κ' hκ'C hκ'Z hκ'proj (Set.nonempty_iff_ne_empty.mpr hcon) hlex
      refine ⟨ε₁, hε₁, ?_⟩
      rw [Set.disjoint_left]
      intro x hx hxball
      have : x ∈ κ' ∩ box m N W U := ⟨hx, hb₁ hxball⟩
      rw [hempty] at this
      exact this
  have hε₃ : ∃ ε₃ > 0, ∀ κ' ∈ Bad, Disjoint κ' (Metric.ball p ε₃) := by
    by_cases hB : Bad.Nonempty
    · let g : Set (Fin (m + N) → ℝ) → ℝ := fun κ' =>
        if h : κ' ∈ Bad then Classical.choose (hfar κ' h) else 1
      have hgpos : ∀ κ' ∈ Bad, 0 < g κ' := by
        intro κ' hκ'
        rw [show g κ' = Classical.choose (hfar κ' hκ') from dif_pos hκ']
        exact (Classical.choose_spec (hfar κ' hκ')).1
      have hgdisj : ∀ κ' ∈ Bad, Disjoint κ' (Metric.ball p (g κ')) := by
        intro κ' hκ'
        rw [show g κ' = Classical.choose (hfar κ' hκ') from dif_pos hκ']
        exact (Classical.choose_spec (hfar κ' hκ')).2
      have hne : (Bad.image g).Nonempty := hB.image g
      refine ⟨(Bad.image g).min' hne, ?_, ?_⟩
      · have hmem := Finset.min'_mem (Bad.image g) hne
        rw [Finset.mem_image] at hmem
        obtain ⟨κ', hκ', hgk⟩ := hmem
        rw [← hgk]
        exact hgpos κ' hκ'
      · intro κ' hκ'
        exact (hgdisj κ' hκ').mono_right (Metric.ball_subset_ball
          (Finset.min'_le (Bad.image g) (g κ') (Finset.mem_image.mpr ⟨κ', hκ', rfl⟩)))
    · refine ⟨1, one_pos, ?_⟩
      intro κ' hκ'
      exact absurd ⟨κ', hκ'⟩ hB
  obtain ⟨ε₃, hε₃pos, hε₃disj⟩ := hε₃
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃pos), ?_⟩
  intro z hzZ hz
  have hz₁ : dist z p < ε₁ := lt_of_lt_of_le hz (min_le_left _ _)
  have hz₂ : dist z p < ε₂ :=
    lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))
  have hz₃ : dist z p < ε₃ :=
    lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_right _ _))
  have hzbox : z ∈ box m N W U := hb₁ (Metric.mem_ball.mpr hz₁)
  obtain ⟨κz, hκzC, hzκz⟩ := cylDecomp_cover hdec z
  have hκzZ : κz ⊆ Z := by
    rcases hsep κz hκzC with h | hd
    · exact h
    · exact absurd hzZ (Set.disjoint_left.mp hd hzκz)
  have hκzproj : projOver m N κz = C₀ := by
    by_contra hne
    have hmem : projOver m N κz ∈ projDecomp m N C := projOver_mem_projDecomp hκzC
    have hxmem : (fun i : Fin m => z (Fin.castAdd N i)) ∈ projOver m N κz := mem_projOver hzκz
    have hlt : dist (fun i : Fin m => z (Fin.castAdd N i))
        (fun i : Fin m => p (Fin.castAdd N i)) < ε₂ := lt_of_le_of_lt (dist_proj_le z p) hz₂
    have hxC₀ : (fun i : Fin m => z (Fin.castAdd N i)) ∈ C₀ := hb₂ (Metric.mem_ball.mpr hlt)
    exact hne (eq_of_mem_projDecomp hdec hmem hC₀mem hxmem hxC₀)
  by_cases hκzeq : κz = κ
  · rwa [hκzeq] at hzκz
  · have hbad : κz ∈ Bad := by
      rw [hBad, Finset.mem_filter]
      exact ⟨hκzC, hκzZ, hκzproj, hκzeq⟩
    exact absurd (Metric.mem_ball.mpr hz₃) (Set.disjoint_left.mp (hε₃disj κz hbad) hzκz)


/-! ## 6. Recovering the parameters from a sheet point -/

/-- A sheet point composed with the parameter/band selection recovers the parameters. -/
theorem sheetPtM_comp_selBand {m N : ℕ} (w : Fin N → CellType)
    (v : Fin (m + nBand N w) → ℝ) (u : Fin (nGraph N w) → ℝ) :
    (sheetPtM (wordEquiv w) v u) ∘ selBand m w = v := by
  funext i
  refine Fin.addCases (motive := fun i : Fin (m + nBand N w) =>
    sheetPtM (wordEquiv w) v u (selBand m w i) = v i) ?_ ?_ i
  · intro i'
    rw [selBand_castAdd, sheetPtM_castAdd]
  · intro k
    rw [selBand_natAdd]
    rw [sheetPt_wordEquiv_band w v u (bandIdx w k) (bandIdx_band w k)]
    have h : (⟨bandRank w (bandIdx w k),
        bandRank_lt_nBand w (bandIdx_band w k)⟩ : Fin (nBand N w)) = k :=
      Fin.ext (bandRank_bandIdx w k)
    rw [h]

/-- `T` is exactly the projection of `κ` to the parameters and the band coordinates. -/
theorem mem_T_iff {m N : ℕ} {κ : Set (Fin (m + N) → ℝ)}
    {T : Set (Fin (m + nBand N (word m N κ)) → ℝ)}
    {φ : (Fin (m + nBand N (word m N κ)) → ℝ) → (Fin (nGraph N (word m N κ)) → ℝ)}
    (hTmem : ∀ v ∈ T, sheetPtM (wordEquiv (word m N κ)) v (φ v) ∈ κ)
    (hTsurj : ∀ z ∈ κ, ∃ v ∈ T, z = sheetPtM (wordEquiv (word m N κ)) v (φ v)) :
    ∀ v, v ∈ T ↔ ∃ p : Fin (m + N) → ℝ, p ∈ κ ∧ v = p ∘ selBand m (word m N κ) := by
  intro v
  constructor
  · intro hv
    exact ⟨_, hTmem v hv, (sheetPtM_comp_selBand _ v (φ v)).symm⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨v', hv', hveq⟩ := hTsurj p hp
    rw [hveq, sheetPtM_comp_selBand]
    exact hv'

/-- The graph coordinates of any point of `κ` lying over `v ∈ T`. -/
theorem phi_eq_graph {m N : ℕ} {κ : Set (Fin (m + N) → ℝ)}
    {T : Set (Fin (m + nBand N (word m N κ)) → ℝ)}
    {φ : (Fin (m + nBand N (word m N κ)) → ℝ) → (Fin (nGraph N (word m N κ)) → ℝ)}
    (hTmem : ∀ v ∈ T, sheetPtM (wordEquiv (word m N κ)) v (φ v) ∈ κ)
    (hTsurj : ∀ z ∈ κ, ∃ v ∈ T, z = sheetPtM (wordEquiv (word m N κ)) v (φ v)) :
    ∀ (v : Fin (m + nBand N (word m N κ)) → ℝ), v ∈ T → ∀ (p : Fin (m + N) → ℝ), p ∈ κ →
      v = p ∘ selBand m (word m N κ) → ∀ j : Fin (nGraph N (word m N κ)),
        φ v j = p (Fin.natAdd m (graphIdx (word m N κ) j)) := by
  intro v hv p hp hvp j
  obtain ⟨v', hv', hveq⟩ := hTsurj p hp
  have hvv : v' = v := by
    have h1 : v' = (sheetPtM (wordEquiv (word m N κ)) v' (φ v')) ∘ selBand m (word m N κ) :=
      (sheetPtM_comp_selBand _ v' (φ v')).symm
    rw [← hveq] at h1
    exact h1.trans hvp.symm
  rw [hvv] at hveq
  have hgg := graphIdx_graph (word m N κ) j
  have hbg : bandBit (word m N κ (graphIdx (word m N κ) j)) = 0 := by
    cases hc : word m N κ (graphIdx (word m N κ) j) with
    | graph => rfl
    | band =>
        rw [hc] at hgg
        simp [graphBit] at hgg
  rw [hveq, sheetPt_wordEquiv_graph (word m N κ) v (φ v) (graphIdx (word m N κ) j) hbg]
  exact congrArg (φ v) (Fin.ext (graphRank_graphIdx (word m N κ) j)).symm

end Work.WilCrux

