import Mathlib
import Submission.Work.SphereJordan.mayerVietorisDefs
import Submission.Work.SphereJordan.mvTransferHomotopicBase
import Submission.Work.SphereJordan.pi1PlaneCyclic

/-!
# The annulus-cover pigeonhole

For open preconnected `U V ⊆ ℂ` with `U ∪ V = {0}ᶜ`, of any three points of `U ∩ V` two lie in the
same connected component.  The content is that `ker (H0PairMap U V)` is cyclic: `U ∪ V = ℂ∖{0}` is
an annulus with `H₁ ≅ ℤ`, and Mayer–Vietoris identifies the kernel with the image of the connecting
map `H₁(ℂ∖{0}) → H₀(U ∩ V)`.

We formalise the connecting map via the **transfer** on subdivided labelled paths.
-/

namespace Work.Spike

open Set
open Work.SphereJordan

noncomputable section

/-! ## `H₀` bookkeeping -/

/-- `H0Map` on a generator. -/
theorem H0Map_of {α : Type*} [TopologicalSpace α] {S T : Set α} (h : S ⊆ T)
    (c : ConnectedComponents ↥S) :
    H0Map h (FreeAbelianGroup.of c) = FreeAbelianGroup.of (mapComponents h c) :=
  FreeAbelianGroup.lift_apply_of _ c

/-- The class in `H₀(W)` of a point of `W`, and `0` for a point outside `W`. -/
def h0cls {α : Type*} [TopologicalSpace α] (W : Set α) (x : α) : H0 W := by
  classical
  exact if hx : x ∈ W then FreeAbelianGroup.of (ConnectedComponents.mk ⟨x, hx⟩) else 0

@[simp] theorem h0cls_of_mem {α : Type*} [TopologicalSpace α] {W : Set α} {x : α}
    (hx : x ∈ W) : h0cls W x = FreeAbelianGroup.of (ConnectedComponents.mk ⟨x, hx⟩) := by
  classical
  rw [h0cls]; exact dif_pos hx

@[simp] theorem h0cls_of_notMem {α : Type*} [TopologicalSpace α] {W : Set α} {x : α}
    (hx : x ∉ W) : h0cls W x = 0 := by
  classical
  rw [h0cls]; exact dif_neg hx

/-- The coefficient functional at a component class of a free abelian group. -/
def coord {α : Type*} (c : α) : FreeAbelianGroup α →+ ℤ := by
  classical
  exact FreeAbelianGroup.lift (fun c' => if c' = c then 1 else 0)

theorem coord_of {α : Type*} [DecidableEq α] (c c' : α) :
    coord c (FreeAbelianGroup.of c') = if c' = c then 1 else 0 := by
  classical
  simp [coord]

/-- Equal class-points in `U ∩ V` have equal `connectedComponentIn`. -/
theorem connectedComponentIn_eq_of_mk_eq {α : Type*} [TopologicalSpace α] {F : Set α} {x y : α}
    (hx : x ∈ F) (hy : y ∈ F)
    (h : ConnectedComponents.mk (⟨x, hx⟩ : ↥F) = ConnectedComponents.mk (⟨y, hy⟩ : ↥F)) :
    connectedComponentIn F x = connectedComponentIn F y := by
  rw [ConnectedComponents.coe_eq_coe] at h
  simp only [connectedComponentIn, dif_pos hx, dif_pos hy, h]

/-- **Cyclic kernel ⟹ pigeonhole.** -/
theorem classes_eq_of_cyclic {α : Type*} [TopologicalSpace α] {U V : Set α}
    (hUp : IsPreconnected U) (hVp : IsPreconnected V)
    (hcyc : ∃ g : H0 (U ∩ V), g ∈ AddMonoidHom.ker (H0PairMap U V) ∧
      ∀ x ∈ AddMonoidHom.ker (H0PairMap U V), ∃ n : ℤ, x = n • g) :
    ∀ a b c : ConnectedComponents ↥(U ∩ V), a = b ∨ a = c ∨ b = c := by
  classical
  have subs : ∀ S : Set α, IsPreconnected S → Subsingleton (ConnectedComponents ↥S) := by
    intro S hS
    haveI : PreconnectedSpace ↥S := isPreconnected_iff_preconnectedSpace.mp hS
    exact inferInstance
  haveI hUsub : Subsingleton (ConnectedComponents ↥U) := subs U hUp
  haveI hVsub : Subsingleton (ConnectedComponents ↥V) := subs V hVp
  intro a b c
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hab, hac, hbc⟩ := hcon
  set e₁ : H0 (U ∩ V) := FreeAbelianGroup.of a - FreeAbelianGroup.of b with he₁
  set e₂ : H0 (U ∩ V) := FreeAbelianGroup.of b - FreeAbelianGroup.of c with he₂
  have hker_sub : ∀ z z' : ConnectedComponents ↥(U ∩ V),
      FreeAbelianGroup.of z - FreeAbelianGroup.of z' ∈ AddMonoidHom.ker (H0PairMap U V) := by
    intro z z'
    rw [AddMonoidHom.mem_ker, map_sub, sub_eq_zero]
    ext <;>
      · simp only [H0PairMap, H0Map]
        exact congrArg FreeAbelianGroup.of (Subsingleton.elim _ _)
  have hker₁ : e₁ ∈ AddMonoidHom.ker (H0PairMap U V) := by
    rw [he₁]; exact hker_sub a b
  have hker₂ : e₂ ∈ AddMonoidHom.ker (H0PairMap U V) := by
    rw [he₂]; exact hker_sub b c
  have hcoord₁ : coord a e₁ = 1 := by
    rw [he₁, map_sub, coord_of, coord_of]
    simp [Ne.symm hab]
  have hcoord₂ : coord a e₂ = 0 := by
    rw [he₂, map_sub, coord_of, coord_of]
    simp [Ne.symm hab, Ne.symm hac]
  have hne₂ : e₂ ≠ 0 := by
    have h₁ : coord b e₂ = 1 := by
      rw [he₂, map_sub, coord_of, coord_of]
      simp [Ne.symm hbc]
    intro h
    rw [h, map_zero] at h₁
    exact one_ne_zero h₁.symm
  have hind : ∀ m n : ℤ, m • e₁ + n • e₂ = 0 → m = 0 := by
    intro m n hmn
    have h := congrArg (coord a) hmn
    rw [map_zero, map_add, map_zsmul, map_zsmul, hcoord₁, hcoord₂] at h
    simpa using h
  obtain ⟨g, hg, hgen⟩ := hcyc
  obtain ⟨m, hm⟩ := hgen e₁ hker₁
  obtain ⟨n, hn⟩ := hgen e₂ hker₂
  have hzero : (n : ℤ) • e₁ + (-m) • e₂ = 0 := by
    rw [hm, hn, smul_smul, smul_smul, ← add_smul,
      show (n * m + -m * n : ℤ) = 0 from by ring, zero_smul]
  have hn0 : n = 0 := hind n (-m) hzero
  rw [hn0, zero_smul] at hn
  exact hne₂ hn

/-! ## Subdivided labelled paths and the transfer -/

section Transfer

variable {α : Type*} [TopologicalSpace α]

/-- The next element of `P` after `p` (`p` itself if there is none). -/
noncomputable def nextPt (P : Finset unitInterval) (p : unitInterval) : unitInterval :=
  if h : (P.filter (fun q => p < q)).Nonempty then (P.filter (fun q => p < q)).min' h else p

/-- The largest element of `P` that is `≤ p` (`p` itself if there is none). -/
noncomputable def prevPt (P : Finset unitInterval) (p : unitInterval) : unitInterval :=
  if h : (P.filter (fun q => q ≤ p)).Nonempty then (P.filter (fun q => q ≤ p)).max' h else p

theorem nextPt_mem {P : Finset unitInterval} {p : unitInterval} (h1 : (1 : unitInterval) ∈ P)
    (hp : p < 1) : nextPt P p ∈ P := by
  have hne : (P.filter (fun q => p < q)).Nonempty :=
    ⟨1, by rw [Finset.mem_filter]; exact ⟨h1, hp⟩⟩
  rw [nextPt, dif_pos hne]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1

theorem lt_nextPt {P : Finset unitInterval} {p : unitInterval} (h1 : (1 : unitInterval) ∈ P)
    (hp : p < 1) : p < nextPt P p := by
  have hne : (P.filter (fun q => p < q)).Nonempty :=
    ⟨1, by rw [Finset.mem_filter]; exact ⟨h1, hp⟩⟩
  rw [nextPt, dif_pos hne]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2

theorem nextPt_le {P : Finset unitInterval} {p q : unitInterval} (h1 : (1 : unitInterval) ∈ P)
    (hp : p < 1) (hq : q ∈ P) (hpq : p < q) : nextPt P p ≤ q := by
  have hne : (P.filter (fun q => p < q)).Nonempty :=
    ⟨1, by rw [Finset.mem_filter]; exact ⟨h1, hp⟩⟩
  rw [nextPt, dif_pos hne]
  exact Finset.min'_le _ q (Finset.mem_filter.mpr ⟨hq, hpq⟩)

theorem prevPt_mem {P : Finset unitInterval} {p : unitInterval} (h0 : (0 : unitInterval) ∈ P) :
    prevPt P p ∈ P := by
  have hne : (P.filter (fun q => q ≤ p)).Nonempty :=
    ⟨0, by rw [Finset.mem_filter]; exact ⟨h0, by simpa using p.2.1⟩⟩
  rw [prevPt, dif_pos hne]
  exact (Finset.mem_filter.mp (Finset.max'_mem _ hne)).1

theorem prevPt_le {P : Finset unitInterval} {p : unitInterval} : prevPt P p ≤ p := by
  rw [prevPt]
  split_ifs with h
  · exact (Finset.mem_filter.mp (Finset.max'_mem _ h)).2
  · exact le_refl p

theorem le_prevPt {P : Finset unitInterval} {q p : unitInterval} (hq : q ∈ P) (hqp : q ≤ p) :
    q ≤ prevPt P p := by
  have hne : (P.filter (fun r => r ≤ p)).Nonempty := ⟨q, Finset.mem_filter.mpr ⟨hq, hqp⟩⟩
  rw [prevPt, dif_pos hne]
  exact Finset.le_max' _ q (Finset.mem_filter.mpr ⟨hq, hqp⟩)

/-- A **labelled subdivision** of a path. -/
structure SData (U V : Set α) {a b : α} (γ : Path a b) where
  P : Finset unitInterval
  mem_zero : (0 : unitInterval) ∈ P
  mem_one : (1 : unitInterval) ∈ P
  side : unitInterval → Bool
  validU : ∀ p : unitInterval, p ∈ P → p ≠ 1 → side p = true →
    ∀ s : unitInterval, p ≤ s → s ≤ nextPt P p → γ s ∈ U
  validV : ∀ p : unitInterval, p ∈ P → p ≠ 1 → side p = false →
    ∀ s : unitInterval, p ≤ s → s ≤ nextPt P p → γ s ∈ V

namespace SData

variable {U V : Set α} {a b : α} {γ : Path a b}

/-- The **transfer** of a labelled subdivision. -/
def transfer (d : SData U V γ) : H0 (U ∩ V) :=
  ∑ p ∈ d.P, if p = 1 then 0
    else if d.side p then (h0cls (U ∩ V) (γ (nextPt d.P p)) - h0cls (U ∩ V) (γ p)) else 0

end SData

end Transfer


/-! ## A uniform grid on the unit interval -/

section Grid

variable {α : Type*} [TopologicalSpace α]
variable {a b : α}

/-- The uniform grid point `i / N` of the unit interval, for `i ≤ N` and `N > 0`. -/
noncomputable def gridPt (N : ℕ) (hN : 0 < N) (i : ℕ) (hi : i ≤ N) : unitInterval :=
  ⟨(i : ℝ) / N, by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by exact_mod_cast hN)]
    exact_mod_cast hi⟩

theorem gridPt_val {N : ℕ} (hN : 0 < N) {i : ℕ} (hi : i ≤ N) :
    (gridPt N hN i hi : ℝ) = (i : ℝ) / N := rfl

theorem gridPt_inj {N : ℕ} (hN : 0 < N) {i j : ℕ} (hi : i ≤ N) (hj : j ≤ N)
    (h : gridPt N hN i hi = gridPt N hN j hj) : i = j := by
  have h' : (i : ℝ) / N = (j : ℝ) / N := congrArg Subtype.val h
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have h'' : (i : ℝ) * N = (j : ℝ) * N := (div_eq_div_iff hN' hN').mp h'
  have : (i : ℝ) = (j : ℝ) := mul_right_cancel₀ hN' h''
  exact_mod_cast this

theorem gridPt_le {N : ℕ} (hN : 0 < N) {i j : ℕ} (hi : i ≤ N) (hj : j ≤ N) (hij : i ≤ j) :
    gridPt N hN i hi ≤ gridPt N hN j hj := by
  show ((i : ℝ) / N) ≤ ((j : ℝ) / N)
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)

theorem gridPt_lt {N : ℕ} (hN : 0 < N) {i j : ℕ} (hi : i ≤ N) (hj : j ≤ N) (hij : i < j) :
    gridPt N hN i hi < gridPt N hN j hj := by
  show ((i : ℝ) / N) < ((j : ℝ) / N)
  exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by positivity)

/-- The uniform grid as a `Finset`. -/
noncomputable def gridSet (N : ℕ) (hN : 0 < N) : Finset unitInterval :=
  (Finset.range (N + 1)).image (fun i => if h : i ≤ N then gridPt N hN i h else 1)

theorem mem_gridSet {N : ℕ} (hN : 0 < N) {i : ℕ} (hi : i ≤ N) :
    gridPt N hN i hi ∈ gridSet N hN := by
  rw [gridSet]
  refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
  rw [dif_pos hi]

theorem gridSet_zero {N : ℕ} (hN : 0 < N) : (0 : unitInterval) ∈ gridSet N hN := by
  have h := mem_gridSet hN (i := 0) (by omega)
  have h0 : gridPt N hN 0 (by omega) = 0 := by
    apply Subtype.ext; simp [gridPt_val]
  rwa [h0] at h

theorem gridSet_one {N : ℕ} (hN : 0 < N) : (1 : unitInterval) ∈ gridSet N hN := by
  have h := mem_gridSet hN (i := N) le_rfl
  have h1 : gridPt N hN N le_rfl = 1 := by
    apply Subtype.ext
    rw [gridPt_val]
    simp [Nat.cast_ne_zero.mpr hN.ne']
  rwa [h1] at h

theorem gridSet_cases {N : ℕ} (hN : 0 < N) {p : unitInterval} (hp : p ∈ gridSet N hN) :
    p = 1 ∨ ∃ i : ℕ, i < N ∧ ∃ hi : i ≤ N, p = gridPt N hN i hi := by
  rw [gridSet] at hp
  obtain ⟨j, hjmem, hj⟩ := Finset.mem_image.mp hp
  have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem)
  rw [dif_pos hjN] at hj
  by_cases hjEq : j = N
  · left
    subst hjEq
    rw [← hj]
    apply Subtype.ext
    rw [gridPt_val]
    simp [Nat.cast_ne_zero.mpr hN.ne']
  · right
    exact ⟨j, by omega, hjN, hj.symm⟩

theorem nextPt_gridSet {N : ℕ} (hN : 0 < N) {i : ℕ} (hi : i < N) :
    nextPt (gridSet N hN) (gridPt N hN i (le_of_lt hi)) =
      gridPt N hN (i + 1) (by omega) := by
  have h1 : (1 : unitInterval) ∈ gridSet N hN := gridSet_one hN
  have hone : gridPt N hN N le_rfl = 1 := by
    apply Subtype.ext
    rw [gridPt_val]; simp [Nat.cast_ne_zero.mpr hN.ne']
  have hlt : gridPt N hN i (le_of_lt hi) < 1 := by
    have := gridPt_lt hN (le_of_lt hi) le_rfl hi
    rwa [hone] at this
  refine le_antisymm (nextPt_le h1 hlt (mem_gridSet hN (by omega))
    (gridPt_lt hN (le_of_lt hi) (by omega) (by omega))) ?_
  have hmem := nextPt_mem h1 hlt
  have hgt := lt_nextPt h1 hlt
  rcases gridSet_cases hN hmem with hEq | ⟨j, hjN, hjle, hjeq⟩
  · rw [hEq, ← hone]
    exact gridPt_le hN (Nat.succ_le_of_lt hi) le_rfl (Nat.succ_le_of_lt hi)
  · rw [hjeq]
    have hgt' : gridPt N hN i (le_of_lt hi) < gridPt N hN j hjle := by
      rw [← hjeq]; exact hgt
    have hij : i < j := by
      by_contra hcon
      push Not at hcon
      exact absurd (gridPt_le hN hjle (le_of_lt hi) hcon) (not_le.mpr hgt')
    exact gridPt_le hN (Nat.succ_le_of_lt hi) hjle (Nat.succ_le_of_lt hij)

/-- A grid piece lies in the ball of radius `δ` about its left endpoint, when `1/N < δ`. -/
theorem gridPt_piece_ball {N : ℕ} (hN : 0 < N) {δ : ℝ} (hNδ : (1 : ℝ) / N < δ) {i : ℕ}
    (hi : i < N) {s : unitInterval}
    (hs : gridPt N hN i (le_of_lt hi) ≤ s)
    (hs' : s ≤ gridPt N hN (i + 1) (by omega)) :
    s ∈ Metric.ball (gridPt N hN i (le_of_lt hi)) δ := by
  have h1 : (i : ℝ) / N ≤ (s : ℝ) := by
    have h' : (gridPt N hN i (le_of_lt hi) : ℝ) ≤ (s : ℝ) := hs
    rwa [gridPt_val] at h'
  have h2 : (s : ℝ) ≤ (i : ℝ) / N + 1 / N := by
    have h' : (s : ℝ) ≤ ((i : ℝ) + 1) / N := by
      have h'' : (s : ℝ) ≤ (gridPt N hN (i + 1) (by omega) : ℝ) := hs'
      rw [gridPt_val] at h''
      push_cast at h''
      exact h''
    calc (s : ℝ) ≤ ((i : ℝ) + 1) / N := h'
      _ = (i : ℝ) / N + 1 / N := by rw [add_div]
  have hδpos : 0 < δ := lt_of_lt_of_le (by positivity : (0:ℝ) < (1:ℝ)/N) hNδ.le
  rw [Metric.mem_ball]
  show dist (s : ℝ) (gridPt N hN i (le_of_lt hi) : ℝ) < δ
  rw [Real.dist_eq, abs_lt]
  rw [gridPt_val]
  constructor <;> linarith

theorem gridSet_piece_cover {U V : Set α} {γ : Path a b} {N : ℕ} (hN : 0 < N) {δ : ℝ}
    (hδ : ∀ x : unitInterval, Metric.ball x δ ⊆ γ ⁻¹' U ∨ Metric.ball x δ ⊆ γ ⁻¹' V)
    (hNδ : (1 : ℝ) / N < δ) :
    ∀ p : ↥(gridSet N hN), (p : unitInterval) ≠ 1 →
      (∀ s : unitInterval, (p : unitInterval) ≤ s → s ≤ nextPt (gridSet N hN) p → γ s ∈ U) ∨
      (∀ s : unitInterval, (p : unitInterval) ≤ s → s ≤ nextPt (gridSet N hN) p → γ s ∈ V) := by
  intro p hp1
  rcases Or.resolve_left (gridSet_cases hN p.2) (by simpa using hp1) with ⟨i, hiN, hile, hpi⟩
  rw [hpi, nextPt_gridSet hN hiN]
  have hball := hδ (gridPt N hN i (le_of_lt hiN))
  exact hball.imp (fun hb s hs hs' => hb (gridPt_piece_ball hN hNδ hiN hs hs'))
    (fun hb s hs hs' => hb (gridPt_piece_ball hN hNδ hiN hs hs'))

end Grid


/-! ## Existence of a labelled subdivision -/

section Existence

variable {α : Type*} [TopologicalSpace α]
variable {a b : α}

/-- Every path whose range lies in the union of two open sets `U`, `V` admits a labelled
subdivision. -/
theorem exists_sdata {U V : Set α} (hUo : IsOpen U) (hVo : IsOpen V)
    {γ : Path a b} (hγ : ∀ s : unitInterval, γ s ∈ U ∪ V) :
    Nonempty (SData U V γ) := by
  classical
  have hcopen : ∀ i : Fin 2, IsOpen (if i = 0 then γ ⁻¹' U else γ ⁻¹' V) := by
    intro i
    fin_cases i <;>
      simp [hUo.preimage γ.continuous, hVo.preimage γ.continuous]
  have hccov : (Set.univ : Set unitInterval) ⊆
      ⋃ i : Fin 2, (if i = 0 then γ ⁻¹' U else γ ⁻¹' V) := by
    intro s _
    rcases hγ s with h | h
    · exact Set.mem_iUnion.mpr ⟨0, by simp [h]⟩
    · exact Set.mem_iUnion.mpr ⟨1, by simp [h]⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric isCompact_univ hcopen hccov
  have hδ' : ∀ x : unitInterval, Metric.ball x δ ⊆ γ ⁻¹' U ∨ Metric.ball x δ ⊆ γ ⁻¹' V := by
    intro x
    obtain ⟨i, hi⟩ := hδ x (Set.mem_univ x)
    fin_cases i
    · exact Or.inl (by simpa using hi)
    · exact Or.inr (by simpa using hi)
  obtain ⟨N, hNpos, hNδ⟩ : ∃ N : ℕ, 0 < N ∧ (1 : ℝ) / N < δ := by
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
    refine ⟨max M 1, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), ?_⟩
    have hNpos' : (0:ℝ) < (max M 1 : ℝ) :=
      lt_of_lt_of_le one_pos (by exact_mod_cast le_max_right M 1)
    have hMN : (1:ℝ) / δ < (max M 1 : ℝ) :=
      lt_of_lt_of_le hM (by exact_mod_cast le_max_left M 1)
    rw [Nat.cast_max, Nat.cast_one, div_lt_iff₀ hNpos']
    rw [div_lt_iff₀ hδpos] at hMN
    nlinarith [hMN]
  refine ⟨{
    P := gridSet N hNpos
    mem_zero := gridSet_zero hNpos
    mem_one := gridSet_one hNpos
    side := fun p => decide (∀ s : unitInterval,
      p ≤ s → s ≤ nextPt (gridSet N hNpos) p → γ s ∈ U)
    validU := ?_
    validV := ?_ }⟩
  · intro p hpP hp1 hside s hps hps'
    exact of_decide_eq_true hside s hps hps'
  · intro p hpP hp1 hside s hps hps'
    have hC : ¬ (∀ s : unitInterval,
        p ≤ s → s ≤ nextPt (gridSet N hNpos) p → γ s ∈ U) :=
      of_decide_eq_false hside
    rcases gridSet_piece_cover (U := U) (V := V) (γ := γ) hNpos hδ' hNδ ⟨p, hpP⟩ hp1 with h | h
    · exact absurd h hC
    · exact h s hps hps'

end Existence


/-! ## Well-definedness of the transfer -/

section WellDefined

variable {α : Type*} [TopologicalSpace α]
variable {U V : Set α} {a b : α} {γ : Path a b}

theorem prevPt_eq_self {P : Finset unitInterval} {p : unitInterval} (hp : p ∈ P) :
    prevPt P p = p := by
  rw [prevPt]
  have hne : (P.filter (fun q => q ≤ p)).Nonempty :=
    ⟨p, Finset.mem_filter.mpr ⟨hp, le_refl p⟩⟩
  rw [dif_pos hne]
  exact le_antisymm (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
    (Finset.le_max' (P.filter (fun q => q ≤ p)) p (Finset.mem_filter.mpr ⟨hp, le_refl p⟩))

theorem prevPt_mono {P : Finset unitInterval} {a b : unitInterval} (h0 : (0 : unitInterval) ∈ P)
    (hab : a ≤ b) : prevPt P a ≤ prevPt P b := by
  have ha : prevPt P a ∈ P := prevPt_mem h0
  have hle : prevPt P a ≤ a := prevPt_le
  exact le_prevPt ha (le_trans hle hab)

theorem prevPt_prevPt {P P' : Finset unitInterval} (h0 : (0 : unitInterval) ∈ P)
    (hsub : P ⊆ P') (p : unitInterval) : prevPt P (prevPt P' p) = prevPt P p := by
  refine le_antisymm ?_ ?_
  · exact prevPt_mono h0 prevPt_le
  · exact le_prevPt (prevPt_mem h0) (le_prevPt (hsub (prevPt_mem h0)) prevPt_le)

/-- Points of `W` lying in a common preconnected subset of `W` have the same `H₀`-class. -/
theorem h0cls_eq_of_preconnected {W T : Set α} {x y : α} (hx : x ∈ W) (hy : y ∈ W)
    (hT : IsPreconnected T) (hTW : T ⊆ W) (hxT : x ∈ T) (hyT : y ∈ T) :
    h0cls W x = h0cls W y := by
  rw [h0cls_of_mem hx, h0cls_of_mem hy]
  congr 1
  rw [ConnectedComponents.coe_eq_coe']
  have hmem : x ∈ connectedComponentIn W y := hT.subset_connectedComponentIn hyT hTW hxT
  rw [connectedComponentIn_eq_image hy] at hmem
  obtain ⟨hx', hmem1, hmem2⟩ := hmem
  rw [show (⟨x, hx⟩ : ↥W) = hx' from Subtype.ext hmem2.symm]
  exact hmem1

/-- The transfer sum, as a function of the cut set and the side function. -/
def tsum (P : Finset unitInterval) (side : unitInterval → Bool) (γ : Path a b) : H0 (U ∩ V) :=
  ∑ p ∈ P, if p = 1 then 0
    else if side p then (h0cls (U ∩ V) (γ (nextPt P p)) - h0cls (U ∩ V) (γ p)) else 0

theorem transfer_eq_tsum (d : SData U V γ) :
    d.transfer = tsum (U := U) (V := V) d.P d.side γ := rfl

/-- **Relabelling** does not change the transfer, as long as the relabelled pieces lie in
`U ∩ V`. -/
theorem tsum_relabel {P : Finset unitInterval} (h1 : (1 : unitInterval) ∈ P)
    {side side' : unitInterval → Bool}
    (h : ∀ p ∈ P, p ≠ 1 → side p ≠ side' p →
      ∀ s : unitInterval, p ≤ s → s ≤ nextPt P p → γ s ∈ U ∩ V) :
    tsum (U := U) (V := V) P side γ = tsum (U := U) (V := V) P side' γ := by
  refine Finset.sum_congr rfl ?_
  intro p hp
  by_cases hp1 : p = 1
  · simp [hp1]
  · simp only [if_neg hp1]
    by_cases heq : side p = side' p
    · rw [heq]
    · have hpl1 : p < 1 := lt_of_le_of_ne p.2.2 hp1
      have hlt : p < nextPt P p := lt_nextPt h1 hpl1
      have hmem : ∀ s : unitInterval, p ≤ s → s ≤ nextPt P p → γ s ∈ U ∩ V :=
        h p hp hp1 heq
      have hpiece : γ (nextPt P p) ∈ U ∩ V := hmem _ hlt.le le_rfl
      have hpW : γ p ∈ U ∩ V := hmem _ le_rfl hlt.le
      have heq0 : h0cls (U ∩ V) (γ (nextPt P p)) = h0cls (U ∩ V) (γ p) :=
        h0cls_eq_of_preconnected (W := U ∩ V) (T := γ '' Set.Icc p (nextPt P p))
          (x := γ (nextPt P p)) (y := γ p) hpiece hpW
          ((isPreconnected_Icc (a := p) (b := nextPt P p)).image _ γ.continuous.continuousOn)
          (fun z hz => by rcases hz with ⟨s, hs, rfl⟩; exact hmem s hs.1 hs.2)
          ⟨nextPt P p, ⟨hlt.le, le_rfl⟩, rfl⟩
          ⟨p, ⟨le_rfl, hlt.le⟩, rfl⟩
      have hzero : (h0cls (U ∩ V) (γ (nextPt P p)) - h0cls (U ∩ V) (γ p)) = 0 := by
        rw [heq0, sub_self]
      rw [hzero]
      cases side p <;> cases side' p <;> rfl

end WellDefined


section Insert

variable {α : Type*} [TopologicalSpace α]
variable {U V : Set α} {a b : α} {γ : Path a b}

theorem prevPt_lt_self {P : Finset unitInterval} {p : unitInterval} (h0 : (0 : unitInterval) ∈ P)
    (hp : p ∉ P) : prevPt P p < p :=
  lt_of_le_of_ne prevPt_le (fun h => hp (h ▸ prevPt_mem h0))

theorem lt_nextPt_prevPt {P : Finset unitInterval} {p : unitInterval} (h0 : (0 : unitInterval) ∈ P)
    (h1 : (1 : unitInterval) ∈ P) (hp : p ∉ P) (hp1 : p < 1) :
    p < nextPt P (prevPt P p) := by
  by_contra hcon
  push Not at hcon
  have hq : prevPt P p ∈ P := prevPt_mem h0
  have hlt : prevPt P p < 1 := lt_trans (prevPt_lt_self h0 hp) hp1
  exact absurd (le_prevPt (nextPt_mem h1 hlt) hcon) (not_le.mpr (lt_nextPt h1 hlt))

theorem nextPt_insert_self {P : Finset unitInterval} {p0 : unitInterval} (h0 : (0 : unitInterval) ∈ P)
    (h1 : (1 : unitInterval) ∈ P) (hp0 : p0 ∉ P) (hp01 : p0 < 1) :
    nextPt (insert p0 P) p0 = nextPt P (prevPt P p0) := by
  have hq1 : prevPt P p0 < 1 := lt_trans (prevPt_lt_self h0 hp0) hp01
  refine le_antisymm ?_ ?_
  · exact nextPt_le (Finset.mem_insert_of_mem h1) hp01
      (Finset.mem_insert_of_mem (nextPt_mem h1 hq1)) (lt_nextPt_prevPt h0 h1 hp0 hp01)
  ·
    have hgt : p0 < nextPt (insert p0 P) p0 :=
      lt_nextPt (P := insert p0 P) (Finset.mem_insert_of_mem h1) hp01
    have hmem := nextPt_mem (P := insert p0 P) (Finset.mem_insert_of_mem h1) hp01
    have hmemP : nextPt (insert p0 P) p0 ∈ P := by
      rcases Finset.mem_insert.mp hmem with h | h
      · exact absurd h.symm (ne_of_lt hgt)
      · exact h
    exact nextPt_le h1 hq1 hmemP (lt_of_lt_of_le (prevPt_lt_self h0 hp0) hgt.le)

theorem nextPt_insert_prev {P : Finset unitInterval} {p0 : unitInterval} (h0 : (0 : unitInterval) ∈ P)
    (h1 : (1 : unitInterval) ∈ P) (hp0 : p0 ∉ P) (hp01 : p0 < 1) :
    nextPt (insert p0 P) (prevPt P p0) = p0 := by
  have hq1 : prevPt P p0 < 1 := lt_trans (prevPt_lt_self h0 hp0) hp01
  have h1' : (1 : unitInterval) ∈ insert p0 P := Finset.mem_insert_of_mem h1
  refine le_antisymm ?_ ?_
  · exact nextPt_le h1' hq1 (Finset.mem_insert_self p0 P) (prevPt_lt_self h0 hp0)
  · have hlt := lt_nextPt h1' hq1
    by_contra hcon
    push Not at hcon
    have hmem := nextPt_mem h1' hq1
    rcases Finset.mem_insert.mp hmem with h | h
    · rw [h] at hcon; exact absurd hcon (lt_irrefl p0)
    · exact absurd (le_prevPt h hcon.le) (not_le.mpr hlt)

theorem nextPt_insert_of_ne {P : Finset unitInterval} {p0 p : unitInterval}
    (h0 : (0 : unitInterval) ∈ P) (h1 : (1 : unitInterval) ∈ P) (hp0 : p0 ∉ P) (hp01 : p0 < 1)
    (hp : p ∈ P) (hpne1 : p ≠ 1) (hne : p ≠ prevPt P p0) :
    nextPt (insert p0 P) p = nextPt P p := by
  have hp1 : p < 1 := lt_of_le_of_ne p.2.2 hpne1
  have h1' : (1 : unitInterval) ∈ insert p0 P := Finset.mem_insert_of_mem h1
  refine le_antisymm ?_ ?_
  · exact nextPt_le h1' hp1 (Finset.mem_insert_of_mem (nextPt_mem h1 hp1)) (lt_nextPt h1 hp1)
  · by_contra hcon
    push Not at hcon
    have hmem := nextPt_mem (P := insert p0 P) h1' hp1
    have hgt := lt_nextPt (P := insert p0 P) h1' hp1
    rcases Finset.mem_insert.mp hmem with h | h
    · have hp_lt : p < p0 := by rw [h] at hgt; exact hgt
      have hnext : p0 < nextPt P p := by rw [h] at hcon; exact hcon
      have hqp : prevPt P p0 = p := by
        refine le_antisymm ?_ (le_prevPt hp hp_lt.le)
        by_contra hc
        push Not at hc
        exact absurd (nextPt_le h1 hp1 (prevPt_mem h0) hc)
          (not_le.mpr (lt_of_le_of_lt prevPt_le hnext))
      exact hne hqp.symm
    · exact absurd (nextPt_le h1 hp1 h hgt) (not_le.mpr hcon)

end Insert



section InsertSum

variable {α : Type*} [TopologicalSpace α]
variable {U V : Set α} {a b : α} {γ : Path a b}

/-- **Inserting a cut point** does not change the transfer. -/
theorem tsum_insert {P : Finset unitInterval} {side : unitInterval → Bool}
    (h0 : (0 : unitInterval) ∈ P) (h1 : (1 : unitInterval) ∈ P)
    {p0 : unitInterval} (hp0 : p0 ∉ P) (hp01 : p0 < 1) (side' : unitInterval → Bool)
    (hside0 : side' p0 = side (prevPt P p0)) (hside : ∀ p ∈ P, side' p = side p) :
    tsum (U := U) (V := V) (insert p0 P) side' γ = tsum (U := U) (V := V) P side γ := by
  set q := prevPt P p0 with hq
  have hqP : q ∈ P := prevPt_mem h0
  have hsq : side' q = side q := hside q hqP
  have hqt : nextPt (insert p0 P) p0 = nextPt P q := nextPt_insert_self h0 h1 hp0 hp01
  have hqs : nextPt (insert p0 P) q = p0 := nextPt_insert_prev h0 h1 hp0 hp01
  have hp0ne : p0 ≠ 1 := ne_of_lt hp01
  have hq1 : q < 1 := lt_trans (prevPt_lt_self h0 hp0) hp01
  have hqne : q ≠ 1 := ne_of_lt hq1
  set F : unitInterval → H0 (U ∩ V) := fun p => if p = 1 then 0
    else if side p then (h0cls (U ∩ V) (γ (nextPt P p)) - h0cls (U ∩ V) (γ p)) else 0 with hF
  set F' : unitInterval → H0 (U ∩ V) := fun p => if p = 1 then 0
    else if side' p then (h0cls (U ∩ V) (γ (nextPt (insert p0 P) p)) - h0cls (U ∩ V) (γ p))
    else 0 with hF'
  have hgoal : tsum (U := U) (V := V) (insert p0 P) side' γ = ∑ p ∈ insert p0 P, F' p := rfl
  have hgoal2 : tsum (U := U) (V := V) P side γ = ∑ p ∈ P, F p := rfl
  rw [hgoal, hgoal2, Finset.sum_insert hp0,
    ← Finset.sum_erase_add (s := P) (f := F') hqP,
    ← Finset.sum_erase_add (s := P) (f := F) hqP]
  have hrest : ∀ p ∈ P.erase q, F' p = F p := by
    intro p hp
    have hpP : p ∈ P := Finset.mem_of_mem_erase hp
    have hpq : p ≠ q := (Finset.mem_erase.mp hp).1
    simp only [hF, hF']
    by_cases hp1 : p = 1
    · rw [if_pos hp1, if_pos hp1]
    · rw [if_neg hp1, if_neg hp1, nextPt_insert_of_ne h0 h1 hp0 hp01 hpP hp1 hpq, hside p hpP]
  have hjoin : F' p0 + F' q = F q := by
    simp only [hF, hF']
    rw [if_neg hp0ne, if_neg hqne, if_neg hqne, hqt, hside0, hqs, hsq]
    cases side q <;> simp only [if_true, if_false, Bool.false_eq_true, add_zero] <;> abel
  rw [Finset.sum_congr rfl hrest, ← hjoin]
  abel

end InsertSum



section Refine

variable {α : Type*} [TopologicalSpace α]
variable {U V : Set α} {a b : α} {γ : Path a b}

/-- For `P ⊆ P'`, the `P'`-piece at `p` is contained in the `P`-piece at `p`. -/
theorem nextPt_le_nextPt {P P' : Finset unitInterval} (h0 : (0 : unitInterval) ∈ P)
    (h1 : (1 : unitInterval) ∈ P) (hsub : P ⊆ P') {p : unitInterval} (hp : p ∈ P')
    (hp1 : p < 1) : nextPt P' p ≤ nextPt P (prevPt P p) := by
  have hprev : prevPt P p ∈ P := prevPt_mem h0
  have hprev1 : prevPt P p < 1 := lt_of_le_of_lt prevPt_le hp1
  have hnextmem : nextPt P (prevPt P p) ∈ P' := hsub (nextPt_mem h1 hprev1)
  have hgt : p < nextPt P (prevPt P p) := by
    by_contra hcon
    push Not at hcon
    exact absurd (le_prevPt (nextPt_mem h1 hprev1) hcon) (not_le.mpr (lt_nextPt h1 hprev1))
  exact nextPt_le (hsub h1) hp1 hnextmem hgt

/-- **Refinement**: refining a labelled subdivision does not change the transfer. -/
theorem tsum_refine {P : Finset unitInterval} (h0 : (0 : unitInterval) ∈ P)
    (h1 : (1 : unitInterval) ∈ P) {side : unitInterval → Bool} :
    ∀ P' : Finset unitInterval, (0 : unitInterval) ∈ P' → (1 : unitInterval) ∈ P' → P ⊆ P' →
      ∀ side' : unitInterval → Bool, (∀ p ∈ P', side' p = side (prevPt P p)) →
      tsum (U := U) (V := V) P' side' γ = tsum (U := U) (V := V) P side γ := by
  suffices H : ∀ n, ∀ P' : Finset unitInterval, (P'.filter (fun p => p ∉ P)).card = n →
      (0 : unitInterval) ∈ P' → (1 : unitInterval) ∈ P' → P ⊆ P' →
      ∀ side' : unitInterval → Bool, (∀ p ∈ P', side' p = side (prevPt P p)) →
      tsum (U := U) (V := V) P' side' γ = tsum (U := U) (V := V) P side γ by
    intro P' h0' h1' hsub side' hside
    exact H _ P' rfl h0' h1' hsub side' hside
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P' hcard h0' h1' hsub side' hside
    by_cases hempty : (P'.filter (fun p => p ∉ P)).Nonempty
    · obtain ⟨p0, hp0mem⟩ := hempty
      have hp0' : p0 ∈ P' := (Finset.mem_filter.mp hp0mem).1
      have hp0notP : p0 ∉ P := (Finset.mem_filter.mp hp0mem).2
      have hp01 : p0 < 1 := lt_of_le_of_ne p0.2.2 (fun h => hp0notP (h ▸ h1))
      have hnotin : p0 ∉ P'.erase p0 := Finset.notMem_erase p0 P'
      have hsub'' : P ⊆ P'.erase p0 := fun p hp =>
        Finset.mem_erase.mpr ⟨fun h => hp0notP (h ▸ hp), hsub hp⟩
      have h0'' : (0 : unitInterval) ∈ P'.erase p0 := hsub'' h0
      have h1'' : (1 : unitInterval) ∈ P'.erase p0 := hsub'' h1
      have hcard'' : ((P'.erase p0).filter (fun p => p ∉ P)).card < n := by
        rw [← hcard]
        have heq : (P'.erase p0).filter (fun p => p ∉ P) = (P'.filter (fun p => p ∉ P)).erase p0 := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_erase]
          tauto
        rw [heq]
        exact Finset.card_erase_lt_of_mem hp0mem
      have ih' := ih _ hcard'' _ rfl h0'' h1'' hsub'' side'
        (fun p hp => hside p (Finset.mem_of_mem_erase hp))
      have hside0 : side' p0 = side' (prevPt (P'.erase p0) p0) := by
        have hmem : prevPt (P'.erase p0) p0 ∈ P'.erase p0 := prevPt_mem h0''
        rw [hside _ hp0', hside _ (Finset.mem_of_mem_erase hmem),
          prevPt_prevPt h0 hsub'' p0]
      have hins := tsum_insert (U := U) (V := V) (γ := γ) (P := P'.erase p0) (side := side')
        h0'' h1'' hnotin hp01 side' hside0 (fun p _ => rfl)
      rw [Finset.insert_erase hp0'] at hins
      rw [hins, ih']
    · have hsub' : P' ⊆ P := by
        intro p hp
        by_contra hc
        exact hempty ⟨p, Finset.mem_filter.mpr ⟨hp, hc⟩⟩
      have hPeq : P' = P := Finset.ext fun p => ⟨fun hp => hsub' hp, fun hp => hsub hp⟩
      rw [hPeq]
      show tsum (U := U) (V := V) P side' γ = tsum (U := U) (V := V) P side γ
      unfold tsum
      refine Finset.sum_congr rfl fun p hp => ?_
      have hsp : side' p = side p := by
        rw [hside p (hPeq.symm ▸ hp), prevPt_eq_self hp]
      rw [hsp]

end Refine



section WellDef

variable {α : Type*} [TopologicalSpace α]
variable {U V : Set α} {a b : α} {γ : Path a b}

theorem piece_subset_dpiece {d : SData U V γ} {Q : Finset unitInterval} (hsub : d.P ⊆ Q)
    (h1Q : (1 : unitInterval) ∈ Q) {p : unitInterval} (hp : p ∈ Q) (hp1 : p < 1) :
    ∀ s : unitInterval, p ≤ s → s ≤ nextPt Q p →
      prevPt d.P p ≤ s ∧ s ≤ nextPt d.P (prevPt d.P p) := by
  intro s hps hps'
  have hnext := nextPt_le_nextPt (P := d.P) (P' := Q) d.mem_zero d.mem_one hsub hp hp1
  exact ⟨le_trans prevPt_le hps, le_trans hps' hnext⟩

/-- **Well-definedness of the transfer.** -/
theorem transfer_eq (d d' : SData U V γ) : d.transfer = d'.transfer := by
  set Q : Finset unitInterval := d.P ∪ d'.P with hQdef
  have h0Q : (0 : unitInterval) ∈ Q := Finset.mem_union_left _ d.mem_zero
  have h1Q : (1 : unitInterval) ∈ Q := Finset.mem_union_left _ d.mem_one
  have h0Q' : (0 : unitInterval) ∈ Q := Finset.mem_union_right _ d'.mem_zero
  have h1Q' : (1 : unitInterval) ∈ Q := Finset.mem_union_right _ d'.mem_one
  have hsubL : d.P ⊆ Q := Finset.subset_union_left
  have hsubR : d'.P ⊆ Q := Finset.subset_union_right
  have step1 : d.transfer = tsum (U := U) (V := V) Q (fun p => d.side (prevPt d.P p)) γ := by
    rw [transfer_eq_tsum]
    exact (tsum_refine (U := U) (V := V) d.mem_zero d.mem_one Q h0Q h1Q hsubL
      (fun p => d.side (prevPt d.P p)) (fun p _ => rfl)).symm
  have step2 : d'.transfer = tsum (U := U) (V := V) Q (fun p => d'.side (prevPt d'.P p)) γ := by
    rw [transfer_eq_tsum]
    exact (tsum_refine (U := U) (V := V) d'.mem_zero d'.mem_one Q h0Q' h1Q' hsubR
      (fun p => d'.side (prevPt d'.P p)) (fun p _ => rfl)).symm
  have hpieceU : ∀ (e : SData U V γ) (hsub : e.P ⊆ Q) (p : unitInterval), p ∈ Q → p ≠ 1 →
      e.side (prevPt e.P p) = true → ∀ s, p ≤ s → s ≤ nextPt Q p → γ s ∈ U := by
    intro e hsub p hp hp1 hs s hps hps'
    have hp1' : p < 1 := lt_of_le_of_ne p.2.2 hp1
    obtain ⟨h1, h2⟩ := piece_subset_dpiece (d := e) hsub h1Q hp hp1' s hps hps'
    exact e.validU _ (prevPt_mem e.mem_zero) (ne_of_lt (lt_of_le_of_lt prevPt_le hp1')) hs s h1 h2
  have hpieceV : ∀ (e : SData U V γ) (hsub : e.P ⊆ Q) (p : unitInterval), p ∈ Q → p ≠ 1 →
      e.side (prevPt e.P p) = false → ∀ s, p ≤ s → s ≤ nextPt Q p → γ s ∈ V := by
    intro e hsub p hp hp1 hs s hps hps'
    have hp1' : p < 1 := lt_of_le_of_ne p.2.2 hp1
    obtain ⟨h1, h2⟩ := piece_subset_dpiece (d := e) hsub h1Q hp hp1' s hps hps'
    exact e.validV _ (prevPt_mem e.mem_zero) (ne_of_lt (lt_of_le_of_lt prevPt_le hp1')) hs s h1 h2
  have step3 : tsum (U := U) (V := V) Q (fun p => d.side (prevPt d.P p)) γ =
      tsum (U := U) (V := V) Q (fun p => d'.side (prevPt d'.P p)) γ := by
    refine tsum_relabel (U := U) (V := V) h1Q ?_
    intro p hp hp1 hne s hps hps'
    cases h : d.side (prevPt d.P p)
    · have h2 : d'.side (prevPt d'.P p) = true := by
        cases hh : d'.side (prevPt d'.P p)
        · exact absurd (h.trans hh.symm) hne
        · rfl
      exact ⟨hpieceU d' hsubR p hp hp1 h2 s hps hps', hpieceV d hsubL p hp hp1 h s hps hps'⟩
    · have h2 : d'.side (prevPt d'.P p) = false := by
        cases hh : d'.side (prevPt d'.P p)
        · rfl
        · exact absurd (h.trans hh.symm) hne
      exact ⟨hpieceU d hsubL p hp hp1 h s hps hps', hpieceV d' hsubR p hp hp1 h2 s hps hps'⟩
  rw [step1, step3, ← step2]

end WellDef

/-! ## The transfer as a function on paths in `ℂ`

We use the fleet's `Work.SphereJordan.LSub` (an `ℕ`-indexed labelled subdivision), whose
well-definedness `LSub.transfer_eq` is already proved. -/

noncomputable section TransferPath

section

variable {U V : Set ℂ}



/-! ## Bridging the `ℕ`-indexed labelled subdivisions to the `Finset`-based ones

We prove well-definedness of `LSub.transfer` (`LSub_transfer_eq'`) by transporting an `LSub` to a
`Work.Spike.SData` (a `Finset`-indexed labelled subdivision), for which well-definedness
(`Work.Spike.transfer_eq`) is already available. -/

section Bridge

variable {U V : Set ℂ}

/-- The two definitions of `h0cls` agree. -/
theorem h0cls_bridge {α : Type*} [TopologicalSpace α] (W : Set α) (x : α) :
    Work.Spike.h0cls W x = Work.SphereJordan.h0cls W x := by
  by_cases hx : x ∈ W <;> simp [Work.Spike.h0cls, Work.SphereJordan.h0cls, hx]

/-- Characterisation of `nextPt` as the least element of `P` above `p`. -/
theorem nextPt_eq_of {P : Finset unitInterval} {p q : unitInterval}
    (h1 : (1 : unitInterval) ∈ P) (hp : p < 1) (hq : q ∈ P) (hpq : p < q)
    (hmin : ∀ r ∈ P, p < r → q ≤ r) : nextPt P p = q := by
  have hne : (P.filter (fun r => p < r)).Nonempty := ⟨1, Finset.mem_filter.mpr ⟨h1, hp⟩⟩
  rw [nextPt, dif_pos hne]
  exact le_antisymm
    (Finset.min'_le _ q (Finset.mem_filter.mpr ⟨hq, hpq⟩))
    (Finset.le_min' _ _ q fun r hr =>
      hmin r (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hr).2)

/-- Monotonicity of the cut points of a labelled subdivision. -/
theorem LSub_t_mono {a b : ℂ} {γ : Path a b} (d : Work.SphereJordan.LSub U V γ) :
    ∀ i j, i ≤ j → j ≤ d.N → d.t i ≤ d.t j := by
  intro i j hij hj
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact le_rfl
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with h | h
    · rw [← h]
    · exact le_trans (ih (by omega) (by omega)) (d.strict j (by omega)).le

/-- Strict monotonicity of the cut points of a labelled subdivision. -/
theorem LSub_t_strict {a b : ℂ} {γ : Path a b} (d : Work.SphereJordan.LSub U V γ) :
    ∀ i j, i < j → j ≤ d.N → d.t i < d.t j := by
  intro i j hij hj
  suffices H : ∀ k, i + k + 1 ≤ d.N → d.t i < d.t (i + k + 1) by
    obtain ⟨k, hk⟩ : ∃ k, j = i + k + 1 := ⟨j - i - 1, by omega⟩
    rw [hk]
    exact H _ (by omega)
  intro k
  induction k with
  | zero =>
    intro h
    simpa using d.strict i (by omega)
  | succ k ih =>
    intro h
    exact lt_trans (ih (by omega)) (d.strict (i + k + 1) (by omega))

theorem LSub_t_inj {a b : ℂ} {γ : Path a b} (d : Work.SphereJordan.LSub U V γ) :
    ∀ i j, i ≤ d.N → j ≤ d.N → d.t i = d.t j → i = j := by
  intro i j hi hj h
  rcases lt_trichotomy i j with h' | h' | h'
  · exact absurd (LSub_t_strict d i j h' hj) (by rw [h]; exact lt_irrefl _)
  · exact h'
  · exact absurd (LSub_t_strict d j i h' hi) (by rw [← h]; exact lt_irrefl _)

/-- The next cut point of the image of `d.t` after `d.t i` is `d.t (i+1)`. -/
theorem nextPt_image {a b : ℂ} {γ : Path a b} (d : Work.SphereJordan.LSub U V γ) {i : ℕ}
    (hi : i < d.N) :
    nextPt ((Finset.range (d.N + 1)).image d.t) (d.t i) = d.t (i + 1) := by
  refine nextPt_eq_of ?_ ?_ ?_ ?_ ?_
  · exact Finset.mem_image.mpr ⟨d.N, Finset.mem_range.mpr (by omega), d.tN⟩
  · rw [← d.tN]
    exact LSub_t_strict d i d.N hi le_rfl
  · exact Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr (by omega), rfl⟩
  · exact d.strict i hi
  · intro r hr hpr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
    rw [Finset.mem_range] at hj
    have hij : i < j := by
      by_contra hcon
      push Not at hcon
      exact absurd (LSub_t_mono d j i hcon hi.le) (not_le.mpr hpr)
    exact LSub_t_mono d (i + 1) j (by omega) (by omega)

/-- The side of the image subdivision at `d.t i`. -/
theorem side_image {a b : ℂ} {γ : Path a b} (d : Work.SphereJordan.LSub U V γ) {i : ℕ}
    (hi : i < d.N) :
    decide (∃ j, j < d.N ∧ d.t j = d.t i ∧ d.side j = Work.SphereJordan.Side.U) =
      (if d.side i = Work.SphereJordan.Side.U then true else false) := by
  by_cases h : d.side i = Work.SphereJordan.Side.U
  · rw [if_pos h]
    exact decide_eq_true ⟨i, hi, rfl, h⟩
  · rw [if_neg h]
    refine decide_eq_false fun hcon => ?_
    obtain ⟨j, hj, hji, hjs⟩ := hcon
    have hji' : j = i := LSub_t_inj d j i (le_of_lt hj) hi.le hji
    subst hji'
    exact h hjs

/-- An `LSub` as a `Finset`-indexed labelled subdivision. -/
noncomputable def sdataOfLSub {a b : ℂ} {γ : Path a b} (d : Work.SphereJordan.LSub U V γ) :
    Work.Spike.SData U V γ where
  P := (Finset.range (d.N + 1)).image d.t
  mem_zero := Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), d.t0⟩
  mem_one := Finset.mem_image.mpr ⟨d.N, Finset.mem_range.mpr (by omega), d.tN⟩
  side := fun p => decide (∃ i, i < d.N ∧ d.t i = p ∧ d.side i = Work.SphereJordan.Side.U)
  validU := by
    intro p hp hp1 hs s hs1 hs2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    rw [Finset.mem_range] at hi
    have hilt : i < d.N := by
      by_contra hcon
      push Not at hcon
      have hEq : i = d.N := by omega
      exact hp1 (by rw [hEq, d.tN])
    have hside : d.side i = Work.SphereJordan.Side.U := by
      rw [side_image d hilt] at hs
      by_cases h : d.side i = Work.SphereJordan.Side.U
      · exact h
      · rw [if_neg h] at hs
        exact absurd hs (by decide)
    rw [nextPt_image d hilt] at hs2
    exact d.validU i hilt hside s hs1 hs2
  validV := by
    intro p hp hp1 hs s hs1 hs2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    rw [Finset.mem_range] at hi
    have hilt : i < d.N := by
      by_contra hcon
      push Not at hcon
      have hEq : i = d.N := by omega
      exact hp1 (by rw [hEq, d.tN])
    have hside : d.side i = Work.SphereJordan.Side.V := by
      rw [side_image d hilt] at hs
      by_cases h : d.side i = Work.SphereJordan.Side.U
      · rw [if_pos h] at hs
        exact absurd hs (by decide)
      · cases h' : d.side i with
        | U => exact absurd h' h
        | V => rfl
    rw [nextPt_image d hilt] at hs2
    exact d.validV i hilt hside s hs1 hs2

/-- The transfer of `sdataOfLSub d` is the transfer of `d`. -/
theorem tsum_eq_wTrans_of_LSub {a b : ℂ} {γ : Path a b} (d : Work.SphereJordan.LSub U V γ) :
    Work.Spike.tsum (U := U) (V := V) ((Finset.range (d.N + 1)).image d.t)
        (fun p => decide (∃ i, i < d.N ∧ d.t i = p ∧ d.side i = Work.SphereJordan.Side.U)) γ
      = Work.SphereJordan.wTrans U V (fun i => γ (d.t i))
          (fun i => if d.side i = Work.SphereJordan.Side.U then 1 else 0) d.N := by
  let G : unitInterval → H0 (U ∩ V) := fun p => if p = 1 then 0 else
    (if (decide (∃ j, j < d.N ∧ d.t j = p ∧ d.side j = Work.SphereJordan.Side.U) = true) then
      (Work.Spike.h0cls (U ∩ V) (γ (nextPt ((Finset.range (d.N + 1)).image d.t) p))
        - Work.Spike.h0cls (U ∩ V) (γ p)) else 0)
  have hinj : Set.InjOn d.t (↑(Finset.range (d.N + 1)) : Set ℕ) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_range] at hx hy
    exact LSub_t_inj d x y (by omega) (by omega) hxy
  have hsm : (∑ p ∈ (Finset.range (d.N + 1)).image d.t, G p)
      = ∑ i ∈ Finset.range (d.N + 1), G (d.t i) :=
    Finset.sum_image (f := G) hinj
  rw [Work.SphereJordan.wTrans, Work.Spike.tsum]
  change (∑ p ∈ (Finset.range (d.N + 1)).image d.t, G p)
      = ∑ i ∈ Finset.range d.N,
          (if d.side i = Work.SphereJordan.Side.U then (1 : ℤ) else 0) •
            (Work.SphereJordan.h0cls (U ∩ V) (γ (d.t (i + 1)))
              - Work.SphereJordan.h0cls (U ∩ V) (γ (d.t i)))
  rw [hsm, Finset.sum_range_succ]
  have hlast : G (d.t d.N) = 0 := by
    simp [G, d.tN]
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hne1 : d.t i ≠ 1 := by
    intro hcon
    have h2 : d.t i = d.t d.N := by rw [hcon, d.tN]
    have h3 : i = d.N := LSub_t_inj d i d.N hi.le le_rfl h2
    omega
  have hG : G (d.t i) = (if (decide (∃ j, j < d.N ∧ d.t j = d.t i ∧
      d.side j = Work.SphereJordan.Side.U) = true) then
      (Work.Spike.h0cls (U ∩ V) (γ (nextPt ((Finset.range (d.N + 1)).image d.t) (d.t i)))
        - Work.Spike.h0cls (U ∩ V) (γ (d.t i))) else 0) := by
    simp only [G, hne1, if_false]
  rw [hG, side_image d hi, nextPt_image d hi, h0cls_bridge, h0cls_bridge]
  by_cases h : d.side i = Work.SphereJordan.Side.U <;> simp [h]

/-- **Well-definedness of the `ℕ`-indexed transfer.** -/
theorem LSub_transfer_eq' {a b : ℂ} {γ : Path a b}
    (d d' : Work.SphereJordan.LSub U V γ) : d.transfer = d'.transfer := by
  have hd : d.transfer = (sdataOfLSub d).transfer := by
    rw [Work.SphereJordan.LSub.transfer_def, Work.SphereJordan.wTrans]
    exact (tsum_eq_wTrans_of_LSub d).symm
  have hd' : d'.transfer = (sdataOfLSub d').transfer := by
    rw [Work.SphereJordan.LSub.transfer_def, Work.SphereJordan.wTrans]
    exact (tsum_eq_wTrans_of_LSub d').symm
  rw [hd, hd']
  exact Work.Spike.transfer_eq _ _

end Bridge

/-- Every path in `U ∪ V` admits a labelled subdivision. -/
theorem exists_LSub {a b : ℂ} {γ : Path a b} (hUo : IsOpen U) (hVo : IsOpen V)
    (hγ : ∀ s : unitInterval, γ s ∈ U ∪ V) : Nonempty (Work.SphereJordan.LSub U V γ) := by
  classical
  have hcopen : ∀ i : Fin 2, IsOpen (if i = 0 then γ ⁻¹' U else γ ⁻¹' V) := by
    intro i
    fin_cases i <;>
      simp [hUo.preimage γ.continuous, hVo.preimage γ.continuous]
  have hccov : (Set.univ : Set unitInterval) ⊆
      ⋃ i : Fin 2, (if i = 0 then γ ⁻¹' U else γ ⁻¹' V) := by
    intro s _
    rcases hγ s with h | h
    · exact Set.mem_iUnion.mpr ⟨0, by simp [h]⟩
    · exact Set.mem_iUnion.mpr ⟨1, by simp [h]⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric isCompact_univ hcopen hccov
  have hδ' : ∀ x : unitInterval, Metric.ball x δ ⊆ γ ⁻¹' U ∨ Metric.ball x δ ⊆ γ ⁻¹' V := by
    intro x
    obtain ⟨i, hi⟩ := hδ x (Set.mem_univ x)
    fin_cases i
    · exact Or.inl (by simpa using hi)
    · exact Or.inr (by simpa using hi)
  obtain ⟨N, hNpos, hNδ⟩ : ∃ N : ℕ, 0 < N ∧ (1 : ℝ) / N < δ := by
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
    refine ⟨max M 1, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), ?_⟩
    have hNpos' : (0 : ℝ) < (max M 1 : ℝ) :=
      lt_of_lt_of_le one_pos (by exact_mod_cast le_max_right M 1)
    have hMN : (1 : ℝ) / δ < (max M 1 : ℝ) :=
      lt_of_lt_of_le hM (by exact_mod_cast le_max_left M 1)
    rw [Nat.cast_max, Nat.cast_one, div_lt_iff₀ hNpos']
    rw [div_lt_iff₀ hδpos] at hMN
    nlinarith [hMN]
  let C : ℕ → Prop := fun i => ∀ s : unitInterval, (i : ℝ) / N ≤ (s : ℝ) →
      (s : ℝ) ≤ ((i : ℝ) + 1) / N → γ s ∈ U
  let D : ℕ → Prop := fun i => ∀ s : unitInterval, (i : ℝ) / N ≤ (s : ℝ) →
      (s : ℝ) ≤ ((i : ℝ) + 1) / N → γ s ∈ V
  have hor : ∀ i, i < N → C i ∨ D i := by
    intro i hi
    have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    rcases hδ' (gridPt N hNpos i (le_of_lt hi)) with h | h
    · refine Or.inl fun s hs1 hs2 => h (gridPt_piece_ball hNpos hNδ hi ?_ ?_)
      · show ((gridPt N hNpos i (le_of_lt hi) : unitInterval) : ℝ) ≤ (s : ℝ)
        rw [gridPt_val]; exact hs1
      · show (s : ℝ) ≤ ((gridPt N hNpos (i + 1) (by omega) : unitInterval) : ℝ)
        rw [gridPt_val, hcast]; exact hs2
    · refine Or.inr fun s hs1 hs2 => h (gridPt_piece_ball hNpos hNδ hi ?_ ?_)
      · show ((gridPt N hNpos i (le_of_lt hi) : unitInterval) : ℝ) ≤ (s : ℝ)
        rw [gridPt_val]; exact hs1
      · show (s : ℝ) ≤ ((gridPt N hNpos (i + 1) (by omega) : unitInterval) : ℝ)
        rw [gridPt_val, hcast]; exact hs2
  let tt : ℕ → unitInterval := fun i => if h : i ≤ N then gridPt N hNpos i h else 1
  let sd : ℕ → Work.SphereJordan.Side := fun i =>
    if i < N ∧ C i then Work.SphereJordan.Side.U else Work.SphereJordan.Side.V
  have hsdU : ∀ i, sd i = Work.SphereJordan.Side.U → i < N ∧ C i := by
    intro i hsu
    by_contra hcon
    have h : sd i = Work.SphereJordan.Side.V := by
      show (if i < N ∧ C i then Work.SphereJordan.Side.U
        else Work.SphereJordan.Side.V) = _
      rw [if_neg hcon]
    rw [h] at hsu
    exact absurd hsu (by decide)
  have hsdV : ∀ i, sd i = Work.SphereJordan.Side.V → ¬ (i < N ∧ C i) := by
    intro i hsv hcon
    have h : sd i = Work.SphereJordan.Side.U := by
      show (if i < N ∧ C i then Work.SphereJordan.Side.U
        else Work.SphereJordan.Side.V) = _
      rw [if_pos hcon]
    rw [h] at hsv
    exact absurd hsv (by decide)
  have hreal1 : ∀ i (hi : i < N) (s : unitInterval), tt i ≤ s → (i : ℝ) / N ≤ (s : ℝ) := by
    intro i hi s hs
    have h' : ((tt i : unitInterval) : ℝ) ≤ ((s : unitInterval) : ℝ) := hs
    rw [show tt i = gridPt N hNpos i (le_of_lt hi) from dif_pos (le_of_lt hi)] at h'
    rw [gridPt_val] at h'
    exact h'
  have hreal2 : ∀ i (hi : i < N) (s : unitInterval), s ≤ tt (i + 1) →
      (s : ℝ) ≤ ((i : ℝ) + 1) / N := by
    intro i hi s hs
    have h' : ((s : unitInterval) : ℝ) ≤ ((tt (i + 1) : unitInterval) : ℝ) := hs
    rw [show tt (i + 1) = gridPt N hNpos (i + 1) (by omega) from dif_pos (by omega)] at h'
    rw [gridPt_val] at h'
    have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h'
    exact h'
  have hvalidU : ∀ i, i < N → sd i = Work.SphereJordan.Side.U → ∀ s : unitInterval,
      tt i ≤ s → s ≤ tt (i + 1) → γ s ∈ U := by
    intro i hi hsu s hs1 hs2
    exact (hsdU i hsu).2 s (hreal1 i hi s hs1) (hreal2 i hi s hs2)
  have hvalidV : ∀ i, i < N → sd i = Work.SphereJordan.Side.V → ∀ s : unitInterval,
      tt i ≤ s → s ≤ tt (i + 1) → γ s ∈ V := by
    intro i hi hsv s hs1 hs2
    have hD := (hor i hi).resolve_left fun hC => hsdV i hsv ⟨hi, hC⟩
    exact hD s (hreal1 i hi s hs1) (hreal2 i hi s hs2)
  have ht0 : tt 0 = 0 := by
    apply Subtype.ext
    rw [show tt 0 = gridPt N hNpos 0 (Nat.zero_le N) from dif_pos (Nat.zero_le N), gridPt_val]
    norm_num
  have htN : tt N = 1 := by
    apply Subtype.ext
    rw [show tt N = gridPt N hNpos N le_rfl from dif_pos le_rfl, gridPt_val]
    show (N : ℝ) / N = (1 : ℝ)
    rw [div_self (by exact_mod_cast hNpos.ne' : (N : ℝ) ≠ 0)]
  have htstrict : ∀ i, i < N → tt i < tt (i + 1) := by
    intro i hi
    rw [show tt i = gridPt N hNpos i (le_of_lt hi) from dif_pos (le_of_lt hi),
      show tt (i + 1) = gridPt N hNpos (i + 1) (by omega) from dif_pos (by omega)]
    exact gridPt_lt hNpos (le_of_lt hi) (by omega) (Nat.lt_succ_self i)
  exact Nonempty.intro (Work.SphereJordan.LSub.mk N tt ht0 htN htstrict sd hvalidU hvalidV)

/-- The **transfer** of a path lying in `U ∪ V`: any labelled subdivision of it; the result does
not depend on the choice (`LSub.transfer_eq`). -/
def Xfer (hUo : IsOpen U) (hVo : IsOpen V) {a b : ℂ} (γ : Path a b)
    (hγ : ∀ s : unitInterval, γ s ∈ U ∪ V) : H0 (U ∩ V) :=
  (Classical.choice (exists_LSub hUo hVo hγ)).transfer

theorem Xfer_eq {hUo : IsOpen U} {hVo : IsOpen V} {a b : ℂ} {γ : Path a b}
    (hγ : ∀ s : unitInterval, γ s ∈ U ∪ V) (d : Work.SphereJordan.LSub U V γ) :
    Xfer hUo hVo γ hγ = d.transfer :=
  LSub_transfer_eq' _ _

theorem Xfer_proof_irrel {hUo : IsOpen U} {hVo : IsOpen V} {a b : ℂ} {γ : Path a b}
    (h₁ h₂ : ∀ s : unitInterval, γ s ∈ U ∪ V) :
    Xfer hUo hVo γ h₁ = Xfer hUo hVo γ h₂ :=
  congrArg (fun h => Xfer hUo hVo γ h) (funext fun s => Subsingleton.elim _ _)

theorem Xfer_congr {hUo : IsOpen U} {hVo : IsOpen V} {a b : ℂ} {γ γ' : Path a b} (heq : γ = γ')
    (h₁ : ∀ s : unitInterval, γ s ∈ U ∪ V) (h₂ : ∀ s : unitInterval, γ' s ∈ U ∪ V) :
    Xfer hUo hVo γ h₁ = Xfer hUo hVo γ' h₂ := by
  subst heq
  exact Xfer_proof_irrel _ _

/-- The single-piece labelled subdivision of a path lying in `U`. -/
def lsubOfU {a b : ℂ} (γ : Path a b) (h : ∀ s : unitInterval, γ s ∈ U) :
    Work.SphereJordan.LSub U V γ :=
  let t : ℕ → unitInterval := fun i => if i = 0 then 0 else 1
  { N := 1
    t := t
    t0 := by simp [t]
    tN := by simp [t]
    strict := by
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      show t 0 < t (0 + 1)
      rw [show t 0 = 0 from by simp [t], show t (0 + 1) = 1 from by simp [t]]
      show (0 : ℝ) < 1
      norm_num
    side := fun _ => Work.SphereJordan.Side.U
    validU := fun i hi hsu s hs1 hs2 => h s
    validV := fun i hi hsv s hs1 hs2 => absurd hsv (by decide) }

/-- The single-piece labelled subdivision of a path lying in `V`. -/
def lsubOfV {a b : ℂ} (γ : Path a b) (h : ∀ s : unitInterval, γ s ∈ V) :
    Work.SphereJordan.LSub U V γ :=
  let t : ℕ → unitInterval := fun i => if i = 0 then 0 else 1
  { N := 1
    t := t
    t0 := by simp [t]
    tN := by simp [t]
    strict := by
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      show t 0 < t (0 + 1)
      rw [show t 0 = 0 from by simp [t], show t (0 + 1) = 1 from by simp [t]]
      show (0 : ℝ) < 1
      norm_num
    side := fun _ => Work.SphereJordan.Side.V
    validU := fun i hi hsu s hs1 hs2 => absurd hsu (by decide)
    validV := fun i hi hsv s hs1 hs2 => h s }

/-- The transfer of a path lying in `U` is the difference of the classes of its endpoints. -/
theorem Xfer_of_mem_U {hUo : IsOpen U} {hVo : IsOpen V} {a b : ℂ} {γ : Path a b}
    (hU : ∀ s : unitInterval, γ s ∈ U) (hγ : ∀ s : unitInterval, γ s ∈ U ∪ V) :
    Xfer hUo hVo γ hγ = Work.SphereJordan.h0cls (U ∩ V) b - Work.SphereJordan.h0cls (U ∩ V) a := by
  have hN : (lsubOfU (U := U) (V := V) γ hU).N = 1 := rfl
  have h0 : (lsubOfU (U := U) (V := V) γ hU).t 0 = 0 := by simp [lsubOfU]
  have h1 : (lsubOfU (U := U) (V := V) γ hU).t 1 = 1 := by simp [lsubOfU]
  have hw : (lsubOfU (U := U) (V := V) γ hU).weight 0 = 1 := by
    rw [Work.SphereJordan.LSub.weight]
    simp [lsubOfU]
  rw [Xfer_eq hγ (lsubOfU γ hU), Work.SphereJordan.LSub.transfer_def, hN,
    Work.SphereJordan.wTrans, Finset.sum_range_one, hw, one_smul, h0, h1,
    Path.target, Path.source]

/-- The transfer of a path lying in `V` vanishes. -/
theorem Xfer_of_mem_V {hUo : IsOpen U} {hVo : IsOpen V} {a b : ℂ} {γ : Path a b}
    (hV : ∀ s : unitInterval, γ s ∈ V) (hγ : ∀ s : unitInterval, γ s ∈ U ∪ V) :
    Xfer hUo hVo γ hγ = 0 := by
  have hN : (lsubOfV (U := U) (V := V) γ hV).N = 1 := rfl
  have hw : (lsubOfV (U := U) (V := V) γ hV).weight 0 = 0 := by
    rw [Work.SphereJordan.LSub.weight]
    simp [lsubOfV]
  rw [Xfer_eq hγ (lsubOfV γ hV), Work.SphereJordan.LSub.transfer_def, hN,
    Work.SphereJordan.wTrans, Finset.sum_range_one, hw, zero_smul]

/-- The transfer of a constant path vanishes. -/
theorem Xfer_refl {hUo : IsOpen U} {hVo : IsOpen V} (x : ℂ)
    (hγ : ∀ s : unitInterval, (Path.refl x) s ∈ U ∪ V) :
    Xfer hUo hVo (Path.refl x) hγ = 0 := by
  rw [Xfer_eq hγ (Classical.choice (exists_LSub hUo hVo hγ)),
    Work.SphereJordan.LSub.transfer_def, Work.SphereJordan.wTrans]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Path.refl_apply, Path.refl_apply, sub_self, smul_zero]

end

/-! ## Additivity of the transfer under concatenation -/

section Additivity

variable {U V : Set ℂ}

/-- The map `u ↦ u/2` of the unit interval. -/
def half (u : unitInterval) : unitInterval :=
  ⟨(u : ℝ) / 2, by
    refine ⟨?_, ?_⟩
    · linarith [u.2.1]
    · linarith [u.2.2]⟩

/-- The map `u ↦ (u+1)/2` of the unit interval. -/
def shalf (u : unitInterval) : unitInterval :=
  ⟨(u : ℝ) / 2 + 1 / 2, by
    refine ⟨?_, ?_⟩
    · linarith [u.2.1]
    · linarith [u.2.2]⟩

@[simp] theorem half_coe (u : unitInterval) : ((half u : unitInterval) : ℝ) = (u : ℝ) / 2 := rfl
@[simp] theorem shalf_coe (u : unitInterval) :
    ((shalf u : unitInterval) : ℝ) = (u : ℝ) / 2 + 1 / 2 := rfl

theorem half_strictMono : StrictMono half := by
  intro u v huv
  have huv' : (u : ℝ) < (v : ℝ) := huv
  show (u : ℝ) / 2 < (v : ℝ) / 2
  linarith

theorem shalf_strictMono : StrictMono shalf := by
  intro u v huv
  have huv' : (u : ℝ) < (v : ℝ) := huv
  show (u : ℝ) / 2 + 1 / 2 < (v : ℝ) / 2 + 1 / 2
  linarith

theorem half_one_eq_shalf_zero : half (1 : unitInterval) = shalf 0 := by
  apply Subtype.ext
  rw [half_coe, shalf_coe]
  norm_num

/-- `(γ.trans δ)` at a time of the first half is `γ` at twice that time. -/
theorem trans_half {a b c : ℂ} (γ : Path a b) (δ : Path b c) (u : unitInterval) :
    (γ.trans δ) (half u) = γ u := by
  rw [Path.trans_apply]
  have h : ((half u : unitInterval) : ℝ) ≤ 1 / 2 := by
    rw [half_coe]; linarith [u.2.2]
  rw [dif_pos h]
  have h2 : (⟨2 * ((half u : unitInterval) : ℝ), by
      rw [half_coe]; constructor <;> linarith [u.2.1, u.2.2]⟩ : unitInterval) = u := by
    apply Subtype.ext
    show 2 * ((half u : unitInterval) : ℝ) = (u : ℝ)
    rw [half_coe]
    ring
  rw [h2]

/-- `(γ.trans δ)` at a time of the second half is `δ` at twice minus one. -/
theorem trans_shalf {a b c : ℂ} (γ : Path a b) (δ : Path b c) (u : unitInterval) :
    (γ.trans δ) (shalf u) = δ u := by
  rw [Path.trans_apply]
  by_cases h : ((shalf u : unitInterval) : ℝ) ≤ 1 / 2
  · rw [dif_pos h]
    have hval : (u : ℝ) / 2 + 1 / 2 = 1 / 2 := by
      have h' := h
      rw [shalf_coe] at h'
      linarith [u.2.1]
    have hu : u = 0 := by
      have h2 : shalf u = shalf 0 := by
        apply Subtype.ext
        show (u : ℝ) / 2 + 1 / 2 = (0 : ℝ) / 2 + 1 / 2
        rw [hval]
        norm_num
      exact shalf_strictMono.injective h2
    subst hu
    have h2 : (⟨2 * ((shalf (0 : unitInterval) : unitInterval) : ℝ), by
        rw [shalf_coe]; constructor <;> norm_num⟩ : unitInterval) = 1 := by
      apply Subtype.ext
      show 2 * ((shalf (0 : unitInterval) : unitInterval) : ℝ) = (1 : ℝ)
      rw [shalf_coe]
      norm_num
    rw [h2, Path.target, Path.source]
  · rw [dif_neg h]
    have h2 : (⟨2 * ((shalf u : unitInterval) : ℝ) - 1, by
        rw [shalf_coe]; constructor <;> linarith [u.2.1, u.2.2]⟩ : unitInterval) = u := by
      apply Subtype.ext
      show 2 * ((shalf u : unitInterval) : ℝ) - 1 = (u : ℝ)
      rw [shalf_coe]
      ring
    rw [h2]

/-- **Additivity**: the transfer of `γ.trans δ` is the sum of the transfers. -/
theorem LSub_trans_add {a b c : ℂ} {γ : Path a b} {δ : Path b c}
    (d : Work.SphereJordan.LSub U V γ) (e : Work.SphereJordan.LSub U V δ) :
    ∃ d'' : Work.SphereJordan.LSub U V (γ.trans δ),
      d''.transfer = d.transfer + e.transfer := by
  classical
  have hdN : 1 ≤ d.N := by
    rcases Nat.eq_zero_or_pos d.N with h | h
    · exfalso
      have h1 : (d.t 0 : ℝ) = (d.t d.N : ℝ) := by rw [h]
      rw [d.t0, d.tN] at h1
      norm_num at h1
    · exact h
  have heN : 1 ≤ e.N := by
    rcases Nat.eq_zero_or_pos e.N with h | h
    · exfalso
      have h1 : (e.t 0 : ℝ) = (e.t e.N : ℝ) := by rw [h]
      rw [e.t0, e.tN] at h1
      norm_num at h1
    · exact h
  let T : ℕ → unitInterval :=
    fun i => if i ≤ d.N then half (d.t i) else shalf (e.t (i - d.N))
  let S : ℕ → Work.SphereJordan.Side :=
    fun i => if i < d.N then d.side i else e.side (i - d.N)
  have hTzero : T 0 = 0 := by
    rw [show T 0 = half (d.t 0) from if_pos (Nat.zero_le d.N), d.t0]
    apply Subtype.ext
    rw [half_coe]
    norm_num
  have hTone : T (d.N + e.N) = 1 := by
    have hsub : d.N + e.N - d.N = e.N := by omega
    rw [show T (d.N + e.N) = shalf (e.t (d.N + e.N - d.N)) from if_neg (by omega), hsub, e.tN]
    apply Subtype.ext
    rw [shalf_coe]
    norm_num
  have hTstrict : ∀ i, i < d.N + e.N → T i < T (i + 1) := by
    intro i hi
    by_cases h1 : i + 1 ≤ d.N
    · rw [show T i = half (d.t i) from if_pos (by omega),
        show T (i + 1) = half (d.t (i + 1)) from if_pos h1]
      exact half_strictMono (d.strict i (by omega))
    · rw [show T (i + 1) = shalf (e.t (i + 1 - d.N)) from if_neg h1]
      by_cases h2 : i ≤ d.N
      · have hieq : i = d.N := by omega
        rw [show T i = half (d.t i) from if_pos h2, hieq, d.tN, half_one_eq_shalf_zero]
        have hsub : d.N + 1 - d.N = 1 := by omega
        rw [hsub]
        have h0 : (0 : unitInterval) < e.t 1 := by
          simpa [e.t0] using e.strict 0 (by omega)
        exact shalf_strictMono h0
      · have h3 : d.N < i := by omega
        rw [show T i = shalf (e.t (i - d.N)) from if_neg h2]
        have hsub : i - d.N + 1 = i + 1 - d.N := by omega
        rw [← hsub]
        exact shalf_strictMono (e.strict (i - d.N) (by omega))
  have hTU : ∀ i, i < d.N + e.N → S i = Work.SphereJordan.Side.U →
      ∀ s : unitInterval, T i ≤ s → s ≤ T (i + 1) → (γ.trans δ) s ∈ U := by
    intro i hi hside s hs1 hs2
    by_cases h1 : i < d.N
    · have hi1 : i + 1 ≤ d.N := by omega
      have hTi : T i = half (d.t i) := if_pos (by omega)
      have hTi1 : T (i + 1) = half (d.t (i + 1)) := if_pos hi1
      have hdU : d.side i = Work.SphereJordan.Side.U := by
        have := hside; rwa [show S i = d.side i from if_pos h1] at this
      rw [hTi] at hs1
      rw [hTi1] at hs2
      have hsle : ((s : unitInterval) : ℝ) ≤ 1 / 2 := by
        have h2 : (s : ℝ) ≤ ((half (d.t (i + 1)) : unitInterval) : ℝ) := hs2
        rw [half_coe] at h2
        linarith [(d.t (i + 1)).2.2]
      rw [Path.trans_apply, dif_pos hsle]
      refine d.validU i h1 hdU _ ?_ ?_
      · show (d.t i : ℝ) ≤ 2 * (s : ℝ)
        have h2 : ((half (d.t i) : unitInterval) : ℝ) ≤ (s : ℝ) := hs1
        rw [half_coe] at h2
        linarith
      · show 2 * (s : ℝ) ≤ (d.t (i + 1) : ℝ)
        have h2 : (s : ℝ) ≤ ((half (d.t (i + 1)) : unitInterval) : ℝ) := hs2
        rw [half_coe] at h2
        linarith
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (by omega : d.N ≤ i)
      have hj : j < e.N := by omega
      have hSj : S (d.N + j) = e.side j := by
        rw [show S (d.N + j) = e.side (d.N + j - d.N) from if_neg (by omega),
          show d.N + j - d.N = j from by omega]
      have heU : e.side j = Work.SphereJordan.Side.U := by
        have := hside; rwa [hSj] at this
      have hTj : T (d.N + j) = shalf (e.t j) := by
        by_cases hj0 : j = 0
        · subst hj0
          rw [show T (d.N + 0) = half (d.t (d.N + 0)) from if_pos (by omega), Nat.add_zero, d.tN,
            half_one_eq_shalf_zero, e.t0]
        · rw [show T (d.N + j) = shalf (e.t (d.N + j - d.N)) from if_neg (by omega),
            show d.N + j - d.N = j from by omega]
      have hTj1 : T (d.N + j + 1) = shalf (e.t (j + 1)) := by
        rw [show T (d.N + j + 1) = shalf (e.t (d.N + j + 1 - d.N)) from if_neg (by omega),
          show d.N + j + 1 - d.N = j + 1 from by omega]
      rw [hTj] at hs1
      rw [hTj1] at hs2
      by_cases hj0 : j = 0
      · subst hj0
        by_cases hsle : ((s : unitInterval) : ℝ) ≤ 1 / 2
        · rw [Path.trans_apply, dif_pos hsle]
          have hsval : (s : ℝ) = 1 / 2 := by
            have h2 : ((shalf (e.t 0) : unitInterval) : ℝ) ≤ (s : ℝ) := hs1
            rw [shalf_coe] at h2
            linarith [(e.t 0).2.1]
          have h2 : (⟨2 * (s : ℝ), by
              rw [hsval]; constructor <;> norm_num⟩ : unitInterval) = 1 := by
            apply Subtype.ext
            show 2 * (s : ℝ) = (1 : ℝ)
            rw [hsval]; norm_num
          rw [h2, Path.target]
          have hb : δ 0 ∈ U := by
            have h3 := e.validU 0 (by omega) heU (e.t 0) le_rfl (e.strict 0 (by omega)).le
            rwa [e.t0] at h3
          rwa [Path.source δ] at hb
        · rw [Path.trans_apply, dif_neg hsle]
          refine e.validU 0 (by omega) heU _ ?_ ?_
          · show (e.t 0 : ℝ) ≤ 2 * (s : ℝ) - 1
            have h2 : ((shalf (e.t 0) : unitInterval) : ℝ) ≤ (s : ℝ) := hs1
            rw [shalf_coe] at h2
            linarith
          · show 2 * (s : ℝ) - 1 ≤ (e.t 1 : ℝ)
            have h2 : (s : ℝ) ≤ ((shalf (e.t 1) : unitInterval) : ℝ) := hs2
            rw [shalf_coe] at h2
            linarith
      · have hgt : (1 : ℝ) / 2 < ((shalf (e.t j) : unitInterval) : ℝ) := by
          have h4 : (e.t 0 : ℝ) < (e.t j : ℝ) :=
            LSub_t_strict e 0 j (by omega) (by omega)
          have h5 : (e.t 0 : ℝ) = (0 : ℝ) := by simp [e.t0]
          rw [shalf_coe]
          linarith
        rw [Path.trans_apply, dif_neg (by
          intro hcon
          have h2 : ((shalf (e.t j) : unitInterval) : ℝ) ≤ (s : ℝ) := hs1
          linarith)]
        refine e.validU j hj heU _ ?_ ?_
        · show (e.t j : ℝ) ≤ 2 * (s : ℝ) - 1
          have h2 : ((shalf (e.t j) : unitInterval) : ℝ) ≤ (s : ℝ) := hs1
          rw [shalf_coe] at h2
          linarith
        · show 2 * (s : ℝ) - 1 ≤ (e.t (j + 1) : ℝ)
          have h2 : (s : ℝ) ≤ ((shalf (e.t (j + 1)) : unitInterval) : ℝ) := hs2
          rw [shalf_coe] at h2
          linarith
  have hTV : ∀ i, i < d.N + e.N → S i = Work.SphereJordan.Side.V →
      ∀ s : unitInterval, T i ≤ s → s ≤ T (i + 1) → (γ.trans δ) s ∈ V := by
    intro i hi hside s hs1 hs2
    by_cases h1 : i < d.N
    · have hi1 : i + 1 ≤ d.N := by omega
      have hTi : T i = half (d.t i) := if_pos (by omega)
      have hTi1 : T (i + 1) = half (d.t (i + 1)) := if_pos hi1
      have hdV : d.side i = Work.SphereJordan.Side.V := by
        have := hside; rwa [show S i = d.side i from if_pos h1] at this
      rw [hTi] at hs1
      rw [hTi1] at hs2
      have hsle : ((s : unitInterval) : ℝ) ≤ 1 / 2 := by
        have h2 : (s : ℝ) ≤ ((half (d.t (i + 1)) : unitInterval) : ℝ) := hs2
        rw [half_coe] at h2
        linarith [(d.t (i + 1)).2.2]
      rw [Path.trans_apply, dif_pos hsle]
      refine d.validV i h1 hdV _ ?_ ?_
      · show (d.t i : ℝ) ≤ 2 * (s : ℝ)
        have h2 : ((half (d.t i) : unitInterval) : ℝ) ≤ (s : ℝ) := hs1
        rw [half_coe] at h2
        linarith
      · show 2 * (s : ℝ) ≤ (d.t (i + 1) : ℝ)
        have h2 : (s : ℝ) ≤ ((half (d.t (i + 1)) : unitInterval) : ℝ) := hs2
        rw [half_coe] at h2
        linarith
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (by omega : d.N ≤ i)
      have hj : j < e.N := by omega
      have hSj : S (d.N + j) = e.side j := by
        rw [show S (d.N + j) = e.side (d.N + j - d.N) from if_neg (by omega),
          show d.N + j - d.N = j from by omega]
      have heV : e.side j = Work.SphereJordan.Side.V := by
        have := hside; rwa [hSj] at this
      have hTj : T (d.N + j) = shalf (e.t j) := by
        by_cases hj0 : j = 0
        · subst hj0
          rw [show T (d.N + 0) = half (d.t (d.N + 0)) from if_pos (by omega), Nat.add_zero, d.tN,
            half_one_eq_shalf_zero, e.t0]
        · rw [show T (d.N + j) = shalf (e.t (d.N + j - d.N)) from if_neg (by omega),
            show d.N + j - d.N = j from by omega]
      have hTj1 : T (d.N + j + 1) = shalf (e.t (j + 1)) := by
        rw [show T (d.N + j + 1) = shalf (e.t (d.N + j + 1 - d.N)) from if_neg (by omega),
          show d.N + j + 1 - d.N = j + 1 from by omega]
      rw [hTj] at hs1
      rw [hTj1] at hs2
      by_cases hj0 : j = 0
      · subst hj0
        by_cases hsle : ((s : unitInterval) : ℝ) ≤ 1 / 2
        · rw [Path.trans_apply, dif_pos hsle]
          have hsval : (s : ℝ) = 1 / 2 := by
            have h2 : ((shalf (e.t 0) : unitInterval) : ℝ) ≤ (s : ℝ) := hs1
            rw [shalf_coe] at h2
            linarith [(e.t 0).2.1]
          have h2 : (⟨2 * (s : ℝ), by
              rw [hsval]; constructor <;> norm_num⟩ : unitInterval) = 1 := by
            apply Subtype.ext
            show 2 * (s : ℝ) = (1 : ℝ)
            rw [hsval]; norm_num
          rw [h2, Path.target]
          have hb : δ 0 ∈ V := by
            have h3 := e.validV 0 (by omega) heV (e.t 0) le_rfl (e.strict 0 (by omega)).le
            rwa [e.t0] at h3
          rwa [Path.source δ] at hb
        · rw [Path.trans_apply, dif_neg hsle]
          refine e.validV 0 (by omega) heV _ ?_ ?_
          · show (e.t 0 : ℝ) ≤ 2 * (s : ℝ) - 1
            have h2 : ((shalf (e.t 0) : unitInterval) : ℝ) ≤ (s : ℝ) := hs1
            rw [shalf_coe] at h2
            linarith
          · show 2 * (s : ℝ) - 1 ≤ (e.t 1 : ℝ)
            have h2 : (s : ℝ) ≤ ((shalf (e.t 1) : unitInterval) : ℝ) := hs2
            rw [shalf_coe] at h2
            linarith
      · have hgt : (1 : ℝ) / 2 < ((shalf (e.t j) : unitInterval) : ℝ) := by
          have h4 : (e.t 0 : ℝ) < (e.t j : ℝ) :=
            LSub_t_strict e 0 j (by omega) (by omega)
          have h5 : (e.t 0 : ℝ) = (0 : ℝ) := by simp [e.t0]
          rw [shalf_coe]
          linarith
        rw [Path.trans_apply, dif_neg (by
          intro hcon
          have h2 : ((shalf (e.t j) : unitInterval) : ℝ) ≤ (s : ℝ) := hs1
          linarith)]
        refine e.validV j hj heV _ ?_ ?_
        · show (e.t j : ℝ) ≤ 2 * (s : ℝ) - 1
          have h2 : ((shalf (e.t j) : unitInterval) : ℝ) ≤ (s : ℝ) := hs1
          rw [shalf_coe] at h2
          linarith
        · show 2 * (s : ℝ) - 1 ≤ (e.t (j + 1) : ℝ)
          have h2 : (s : ℝ) ≤ ((shalf (e.t (j + 1)) : unitInterval) : ℝ) := hs2
          rw [shalf_coe] at h2
          linarith
  let d'' : Work.SphereJordan.LSub U V (γ.trans δ) :=
    Work.SphereJordan.LSub.mk (d.N + e.N) T hTzero hTone hTstrict S hTU hTV
  refine ⟨d'', ?_⟩
  show Work.SphereJordan.wTrans U V (fun i => (γ.trans δ) (T i))
      (fun i => if S i = Work.SphereJordan.Side.U then 1 else 0) (d.N + e.N)
    = d.transfer + e.transfer
  rw [Work.SphereJordan.wTrans, Finset.sum_range_add,
    Work.SphereJordan.LSub.transfer_def, Work.SphereJordan.wTrans]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hTi : T i = half (d.t i) := if_pos (le_of_lt hi)
    have hTi1 : T (i + 1) = half (d.t (i + 1)) := if_pos hi
    have hSi : S i = d.side i := if_pos hi
    rw [hTi, hTi1, hSi, trans_half, trans_half]
    rfl
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hTj : T (d.N + j) = shalf (e.t j) := by
      by_cases hj0 : j = 0
      · subst hj0
        rw [show T (d.N + 0) = half (d.t (d.N + 0)) from if_pos (by omega), Nat.add_zero, d.tN,
          half_one_eq_shalf_zero, e.t0]
      · rw [show T (d.N + j) = shalf (e.t (d.N + j - d.N)) from if_neg (by omega),
          show d.N + j - d.N = j from by omega]
    have hTj1 : T (d.N + j + 1) = shalf (e.t (j + 1)) := by
      rw [show T (d.N + j + 1) = shalf (e.t (d.N + j + 1 - d.N)) from if_neg (by omega),
        show d.N + j + 1 - d.N = j + 1 from by omega]
    have hSj : S (d.N + j) = e.side j := by
      rw [show S (d.N + j) = e.side (d.N + j - d.N) from if_neg (by omega),
        show d.N + j - d.N = j from by omega]
    rw [hTj, hTj1, hSj, trans_shalf, trans_shalf]
    rfl

/-- **Additivity** of the transfer under concatenation of paths. -/
theorem Xfer_trans {hUo : IsOpen U} {hVo : IsOpen V} {a b c : ℂ} {γ : Path a b} {δ : Path b c}
    (hγ : ∀ s : unitInterval, γ s ∈ U ∪ V) (hδ : ∀ s : unitInterval, δ s ∈ U ∪ V)
    (hγδ : ∀ s : unitInterval, (γ.trans δ) s ∈ U ∪ V) :
    Xfer hUo hVo (γ.trans δ) hγδ = Xfer hUo hVo γ hγ + Xfer hUo hVo δ hδ := by
  obtain ⟨d'', hd''⟩ := LSub_trans_add (U := U) (V := V)
    (Classical.choice (exists_LSub hUo hVo hγ)) (Classical.choice (exists_LSub hUo hVo hδ))
  rw [Xfer_eq hγδ d'', hd'', Xfer_eq hγ _, Xfer_eq hδ _]

end Additivity

/-! ## The labelled grid for a map out of the square, and the grid identity -/

section Grid

/-- **Existence of a labelled grid.**  For open `U, V ⊆ ℂ` with `U ∪ V ⊇ range H` and
`H : I × I → ℂ` continuous, there is a uniform grid `0 = u 0 < u 1 < ⋯ < u n = 1` and a labelling
of the cells by sides of the cover such that each cell maps into the corresponding side. -/
theorem gridExists {U V : Set ℂ} (hUo : IsOpen U) (hVo : IsOpen V)
    (H : C(unitInterval × unitInterval, ℂ)) (hH : ∀ q, H q ∈ U ∪ V) :
    ∃ (n : ℕ) (_ : 0 < n) (u : ℕ → unitInterval) (lab : ℕ → ℕ → Work.SphereJordan.Side),
      (∀ i, i < n → u i < u (i + 1)) ∧ u 0 = 0 ∧ u n = 1 ∧
      (∀ i j, i < n → j < n → ∀ a b : unitInterval,
        u i ≤ a → a ≤ u (i + 1) → u j ≤ b → b ≤ u (j + 1) →
          H (a, b) ∈ Work.SphereJordan.Side.set U V (lab i j)) := by
  classical
  have hcopen : ∀ i : Fin 2, IsOpen (if i = 0 then H ⁻¹' U else H ⁻¹' V) := by
    intro i
    fin_cases i <;> simp [hUo.preimage H.continuous, hVo.preimage H.continuous]
  have hccov : (Set.univ : Set (unitInterval × unitInterval)) ⊆
      ⋃ i : Fin 2, (if i = 0 then H ⁻¹' U else H ⁻¹' V) := by
    intro s _
    rcases hH s with h | h
    · exact Set.mem_iUnion.mpr ⟨0, by simp [h]⟩
    · exact Set.mem_iUnion.mpr ⟨1, by simp [h]⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric isCompact_univ hcopen hccov
  have hδ' : ∀ x : unitInterval × unitInterval,
      Metric.ball x δ ⊆ H ⁻¹' U ∨ Metric.ball x δ ⊆ H ⁻¹' V := by
    intro x
    obtain ⟨i, hi⟩ := hδ x (Set.mem_univ x)
    fin_cases i
    · exact Or.inl (by simpa using hi)
    · exact Or.inr (by simpa using hi)
  obtain ⟨N, hNpos, hNδ⟩ : ∃ N : ℕ, 0 < N ∧ (1 : ℝ) / N < δ := by
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
    refine ⟨max M 1, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), ?_⟩
    have hNpos' : (0 : ℝ) < (max M 1 : ℝ) :=
      lt_of_lt_of_le one_pos (by exact_mod_cast le_max_right M 1)
    have hMN : (1 : ℝ) / δ < (max M 1 : ℝ) :=
      lt_of_lt_of_le hM (by exact_mod_cast le_max_left M 1)
    rw [Nat.cast_max, Nat.cast_one, div_lt_iff₀ hNpos']
    rw [div_lt_iff₀ hδpos] at hMN
    nlinarith [hMN]
  let u : ℕ → unitInterval := fun i => if h : i ≤ N then gridPt N hNpos i h else 1
  have hu_strict : ∀ i, i < N → u i < u (i + 1) := by
    intro i hi
    rw [show u i = gridPt N hNpos i (le_of_lt hi) from dif_pos (le_of_lt hi),
      show u (i + 1) = gridPt N hNpos (i + 1) (by omega) from dif_pos (by omega)]
    exact gridPt_lt hNpos (le_of_lt hi) (by omega) (Nat.lt_succ_self i)
  have hu_zero : u 0 = 0 := by
    apply Subtype.ext
    rw [show u 0 = gridPt N hNpos 0 (Nat.zero_le N) from dif_pos (Nat.zero_le N), gridPt_val]
    norm_num
  have hu_one : u N = 1 := by
    apply Subtype.ext
    rw [show u N = gridPt N hNpos N le_rfl from dif_pos le_rfl, gridPt_val]
    show (N : ℝ) / N = (1 : ℝ)
    rw [div_self (by exact_mod_cast hNpos.ne' : (N : ℝ) ≠ 0)]
  let C : ℕ → ℕ → Prop := fun i j =>
    ∀ q : unitInterval × unitInterval, dist q (u i, u j) < δ → H q ∈ U
  let D : ℕ → ℕ → Prop := fun i j =>
    ∀ q : unitInterval × unitInterval, dist q (u i, u j) < δ → H q ∈ V
  have hor : ∀ i j, i < N → j < N → C i j ∨ D i j := by
    intro i j hi hj
    rcases hδ' (u i, u j) with h | h
    · exact Or.inl fun q hq => h (Metric.mem_ball.mpr hq)
    · exact Or.inr fun q hq => h (Metric.mem_ball.mpr hq)
  have hu_real : ∀ i, i ≤ N → (u i : ℝ) = (i : ℝ) / N := by
    intro i hi
    rw [show u i = gridPt N hNpos i hi from dif_pos hi, gridPt_val]
  have hcell : ∀ i j, i < N → j < N → ∀ a b : unitInterval,
      u i ≤ a → a ≤ u (i + 1) → u j ≤ b → b ≤ u (j + 1) →
        dist (a, b) (u i, u j) < δ := by
    intro i j hi hj a b ha1 ha2 hb1 hb2
    have ha1' : (u i : ℝ) ≤ (a : ℝ) := ha1
    have ha2' : (a : ℝ) ≤ (u (i + 1) : ℝ) := ha2
    have hb1' : (u j : ℝ) ≤ (b : ℝ) := hb1
    have hb2' : (b : ℝ) ≤ (u (j + 1) : ℝ) := hb2
    rw [hu_real i (le_of_lt hi)] at ha1'
    rw [hu_real (i + 1) (by omega)] at ha2'
    rw [hu_real j (le_of_lt hj)] at hb1'
    rw [hu_real (j + 1) (by omega)] at hb2'
    have hcast1 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [hcast1] at ha2'
    rw [hcast2] at hb2'
    have hsplit1 : ((i : ℝ) + 1) / N = (i : ℝ) / N + 1 / N := by ring
    have hsplit2 : ((j : ℝ) + 1) / N = (j : ℝ) / N + 1 / N := by ring
    have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
    have h1 : dist a (u i) ≤ 1 / N := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_le_iff]
      constructor
      · rw [hu_real i (le_of_lt hi)]
        linarith [inv_nonneg.mpr hNposR.le]
      · rw [hu_real i (le_of_lt hi)]
        rw [hsplit1] at ha2'
        linarith
    have h2 : dist b (u j) ≤ 1 / N := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_le_iff]
      constructor
      · rw [hu_real j (le_of_lt hj)]
        linarith [inv_nonneg.mpr hNposR.le]
      · rw [hu_real j (le_of_lt hj)]
        rw [hsplit2] at hb2'
        linarith
    rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · exact lt_of_le_of_lt h1 hNδ
    · exact lt_of_le_of_lt h2 hNδ
  refine ⟨N, hNpos, u, (fun i j =>
    if i < N ∧ j < N ∧ C i j then Work.SphereJordan.Side.U else Work.SphereJordan.Side.V),
    hu_strict, hu_zero, hu_one, ?_⟩
  intro i j hi hj a b ha1 ha2 hb1 hb2
  by_cases hlab : i < N ∧ j < N ∧ C i j
  · rw [show ((fun i j => if i < N ∧ j < N ∧ C i j then Work.SphereJordan.Side.U
        else Work.SphereJordan.Side.V) i j) = Work.SphereJordan.Side.U from if_pos hlab,
      Work.SphereJordan.Side.set_U]
    exact hlab.2.2 (a, b) (hcell i j hi hj a b ha1 ha2 hb1 hb2)
  · rw [show ((fun i j => if i < N ∧ j < N ∧ C i j then Work.SphereJordan.Side.U
        else Work.SphereJordan.Side.V) i j) = Work.SphereJordan.Side.V from if_neg hlab,
      Work.SphereJordan.Side.set_V]
    exact ((hor i j hi hj).resolve_left fun hC => hlab ⟨hi, hj, hC⟩) (a, b)
      (hcell i j hi hj a b ha1 ha2 hb1 hb2)

/-- **The grid identity.**  For a doubly indexed family `f` with weights `w`, if two adjacent
weights along an interior edge may be replaced by one another whenever the corresponding
increment vanishes, then the boundary sums on the two sides agree. -/
theorem grid_alg {A : Type*} [AddCommGroup A] (n : ℕ) (f : ℕ → ℕ → A) (w : ℕ → ℕ → ℤ)
    (hH : ∀ i k, i < n → 1 ≤ k → k < n → w i k = w i (k - 1) ∨ f (i + 1) k - f i k = 0)
    (hV : ∀ k j, 1 ≤ k → k < n → j < n → w k j = w (k - 1) j ∨ f k (j + 1) - f k j = 0)
    (hV0 : ∀ j, j < n → f 0 (j + 1) - f 0 j = 0)
    (hVn : ∀ j, j < n → f n (j + 1) - f n j = 0) :
    (∑ i ∈ Finset.range n, w i 0 • (f (i + 1) 0 - f i 0)) =
      (∑ i ∈ Finset.range n, w i (n - 1) • (f (i + 1) n - f i n)) := by
  have tel : ∀ (wn : ℕ → ℤ) (g : ℕ → A),
      (∀ k, 1 ≤ k → k < n → wn k = wn (k - 1) ∨ g k = 0) →
      (∑ j ∈ Finset.range n, wn j • g j) - (∑ j ∈ Finset.range n, wn j • g (j + 1))
        = wn 0 • g 0 - wn (n - 1) • g n := by
    intro wn g hg
    have hfk : ∀ k, k < n → wn (k - 1) • g k = wn k • g k := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp
      · rcases hg k h hk with h' | h'
        · rw [h']
        · rw [h', smul_zero, smul_zero]
    have hshift : (∑ k ∈ Finset.range (n + 1), wn (k - 1) • g k)
        = (∑ j ∈ Finset.range n, wn j • g (j + 1)) + wn 0 • g 0 := by
      rw [Finset.sum_range_succ' (fun k => wn (k - 1) • g k) n]
      simp only [Nat.add_sub_cancel, Nat.zero_sub]
    have hdecomp : (∑ k ∈ Finset.range (n + 1), wn (k - 1) • g k)
        = (∑ k ∈ Finset.range n, wn (k - 1) • g k) + wn (n - 1) • g n :=
      Finset.sum_range_succ _ n
    have hmid : (∑ k ∈ Finset.range n, wn (k - 1) • g k)
        = (∑ k ∈ Finset.range n, wn k • g k) :=
      Finset.sum_congr rfl fun k hk => hfk k (Finset.mem_range.mp hk)
    have key : (∑ k ∈ Finset.range n, wn k • g k) + wn (n - 1) • g n
        = (∑ j ∈ Finset.range n, wn j • g (j + 1)) + wn 0 • g 0 := by
      rw [← hmid, ← hdecomp]
      exact hshift
    have hB : (∑ j ∈ Finset.range n, wn j • g (j + 1))
        = (∑ k ∈ Finset.range n, wn k • g k) + wn (n - 1) • g n - wn 0 • g 0 := by
      rw [eq_sub_iff_add_eq]
      exact key.symm
    rw [hB]
    abel
  have hcell_id : ∀ i j, w i j • ((f (i + 1) j - f i j) + (f (i + 1) (j + 1) - f (i + 1) j)
      - (f (i + 1) (j + 1) - f i (j + 1)) - (f i (j + 1) - f i j)) = 0 := by
    intro i j
    rw [show (f (i + 1) j - f i j) + (f (i + 1) (j + 1) - f (i + 1) j)
      - (f (i + 1) (j + 1) - f i (j + 1)) - (f i (j + 1) - f i j) = 0 from by abel,
      smul_zero]
  have hz : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, w i j •
      ((f (i + 1) j - f i j) + (f (i + 1) (j + 1) - f (i + 1) j)
        - (f (i + 1) (j + 1) - f i (j + 1)) - (f i (j + 1) - f i j))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => hcell_id i j
  have hdec : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, w i j •
        ((f (i + 1) j - f i j) + (f (i + 1) (j + 1) - f (i + 1) j)
          - (f (i + 1) (j + 1) - f i (j + 1)) - (f i (j + 1) - f i j)))
      = ((∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, w i j • (f (i + 1) j - f i j))
          - (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
              w i j • (f (i + 1) (j + 1) - f i (j + 1))))
        + ((∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
              w i j • (f (i + 1) (j + 1) - f (i + 1) j))
          - (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, w i j • (f i (j + 1) - f i j))) := by
    simp only [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    abel
  have h13 : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, w i j • (f (i + 1) j - f i j))
      - (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, w i j • (f (i + 1) (j + 1) - f i (j + 1)))
      = ∑ i ∈ Finset.range n,
          (w i 0 • (f (i + 1) 0 - f i 0) - w i (n - 1) • (f (i + 1) n - f i n)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact tel (fun k => w i k) (fun k => f (i + 1) k - f i k)
      (fun k h1 h2 => hH i k hi h1 h2)
  have h24 : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, w i j • (f (i + 1) (j + 1) - f (i + 1) j))
      - (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, w i j • (f i (j + 1) - f i j)) = 0 := by
    rw [Finset.sum_comm (s := Finset.range n) (t := Finset.range n)
        (f := fun i j => w i j • (f (i + 1) (j + 1) - f (i + 1) j)),
      Finset.sum_comm (s := Finset.range n) (t := Finset.range n)
        (f := fun i j => w i j • (f i (j + 1) - f i j)),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    have h := tel (fun k => w k j) (fun k => f k (j + 1) - f k j)
      (fun k h1 h2 => hV k j h1 h2 hj)
    rw [hV0 j hj, hVn j hj, smul_zero, smul_zero, sub_zero] at h
    have h' : (∑ i ∈ Finset.range n, w i j • (f i (j + 1) - f i j))
        = (∑ i ∈ Finset.range n, w i j • (f (i + 1) (j + 1) - f (i + 1) j)) :=
      sub_eq_zero.mp h
    rw [← h']
    exact sub_self _
  have hmain : ((∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, w i j • (f (i + 1) j - f i j))
      - (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, w i j • (f (i + 1) (j + 1) - f i (j + 1))))
      + ((∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, w i j • (f (i + 1) (j + 1) - f (i + 1) j))
      - (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, w i j • (f i (j + 1) - f i j))) = 0 := by
    rw [← hdec, hz]
  rw [h13, h24] at hmain
  simp only [add_zero] at hmain
  rw [Finset.sum_sub_distrib, sub_eq_zero] at hmain
  exact hmain

/-! ## Homotopy invariance of the transfer -/

section Homotopy

variable {U V : Set ℂ}

/-- Evaluation of a path homotopy at an intermediate time. -/
theorem Homotopy_eval_apply {x : ℂ} {p q : Path x x} (F : p.Homotopy q) (s v : unitInterval) :
    (F.eval s) v = F (s, v) := by
  rw [Path.Homotopy.eval_apply, ContinuousMap.Homotopy.curry_apply,
    ContinuousMap.HomotopyWith.coe_toHomotopy]

/-- **Homotopy invariance of the transfer.**  Loops based at `x ≠ 0` that are homotopic through
loops avoiding `0` have the same transfer. -/
theorem Xfer_homotopic (hUo : IsOpen U) (hVo : IsOpen V) (hcov : U ∪ V = ({0} : Set ℂ)ᶜ)
    {x : ℂ} {p q : Path x x} (F : p.Homotopy q) (hF : ∀ t s : unitInterval, F (t, s) ≠ 0)
    (hp : ∀ s : unitInterval, p s ∈ U ∪ V) (hq : ∀ s : unitInterval, q s ∈ U ∪ V) :
    Xfer hUo hVo p hp = Xfer hUo hVo q hq := by
  classical
  have hHmem : ∀ Q : unitInterval × unitInterval, (⇑F) Q ∈ U ∪ V := by
    intro Q
    have hne : (⇑F) Q ≠ 0 := hF Q.1 Q.2
    have h : (⇑F) Q ∈ ({0} : Set ℂ)ᶜ := hne
    rwa [← hcov] at h
  obtain ⟨N, hN, u, lab, hstrict, hu0, huN, hcell⟩ :=
    gridExists hUo hVo ⟨⇑F, F.continuous⟩ hHmem
  set f : ℕ → ℕ → H0 (U ∩ V) := fun i j => Work.SphereJordan.h0cls (U ∩ V) (F (u j, u i)) with hf
  set w : ℕ → ℕ → ℤ := fun i j => if lab j i = Work.SphereJordan.Side.U then 1 else 0 with hw
  -- the two rows
  have hf0 : ∀ i, f i 0 = Work.SphereJordan.h0cls (U ∩ V) (p (u i)) := by
    intro i
    simp only [hf]
    congr 1
    rw [hu0]
    rw [← Homotopy_eval_apply F 0 (u i), Path.Homotopy.eval_zero]
  have hfN : ∀ i, f i N = Work.SphereJordan.h0cls (U ∩ V) (q (u i)) := by
    intro i
    simp only [hf]
    congr 1
    rw [huN]
    rw [← Homotopy_eval_apply F 1 (u i), Path.Homotopy.eval_one]
  -- the constant columns
  have hcol0 : ∀ j, f 0 j = Work.SphereJordan.h0cls (U ∩ V) x := by
    intro j
    simp only [hf]
    rw [hu0, Path.Homotopy.source]
  have hcolN : ∀ j, f N j = Work.SphereJordan.h0cls (U ∩ V) x := by
    intro j
    simp only [hf]
    rw [huN, Path.Homotopy.target]
  have humono : ∀ a b, a ≤ b → b ≤ N → u a ≤ u b := by
    intro a b hab hb
    induction b with
    | zero =>
      have : a = 0 := by omega
      subst this; exact le_rfl
    | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with h | h
      · rw [← h]
      · exact le_trans (ih (by omega) (by omega)) (hstrict b (by omega)).le
  have hV0 : ∀ j, j < N → f 0 (j + 1) - f 0 j = 0 := by
    intro j hj
    rw [hcol0 j, hcol0 (j + 1), sub_self]
  have hVn : ∀ j, j < N → f N (j + 1) - f N j = 0 := by
    intro j hj
    rw [hcolN j, hcolN (j + 1), sub_self]
  -- the horizontal vanishing
  have hH' : ∀ i k, i < N → 1 ≤ k → k < N → w i k = w i (k - 1) ∨ f (i + 1) k - f i k = 0 := by
    intro i k hi hk1 hkN
    by_cases hlab : lab k i = lab (k - 1) i
    · left
      simp only [hw]
      rw [hlab]
    · right
      have hedge : ∀ s ∈ Set.Icc (u i) (u (i + 1)), F (u k, s) ∈ U ∩ V := by
        intro s hs
        have h1 : F (u k, s) ∈ Work.SphereJordan.Side.set U V (lab k i) :=
          hcell k i hkN hi (u k) s le_rfl ((hstrict k hkN).le) hs.1 hs.2
        have h2 : F (u k, s) ∈ Work.SphereJordan.Side.set U V (lab (k - 1) i) :=
          hcell (k - 1) i (by omega) hi (u k) s (humono (k - 1) k (by omega) (by omega))
            (by rw [show k - 1 + 1 = k from by omega]) hs.1 hs.2
        have hmem : F (u k, s) ∈ Work.SphereJordan.Side.set U V (lab k i)
            ∩ Work.SphereJordan.Side.set U V (lab (k - 1) i) := ⟨h1, h2⟩
        rwa [Work.SphereJordan.side_set_mono hlab] at hmem
      have hpiece := Work.SphereJordan.h0cls_eq_of_piece (W := U ∩ V) (γ := F.eval (u k))
        (p := u i) (q := u (i + 1)) ((hstrict i hi).le) (by
          intro s hs
          rw [Homotopy_eval_apply]
          exact hedge s hs)
      simp only [hf]
      rw [Homotopy_eval_apply, Homotopy_eval_apply] at hpiece
      rw [hpiece, sub_self]
  -- the vertical vanishing
  have hV' : ∀ k j, 1 ≤ k → k < N → j < N → w k j = w (k - 1) j ∨ f k (j + 1) - f k j = 0 := by
    intro k j hk1 hkN hj
    by_cases hlab : lab j k = lab j (k - 1)
    · left
      simp only [hw]
      rw [hlab]
    · right
      let col : Path (p (u k)) (q (u k)) :=
        { toContinuousMap := ⟨fun t => F (t, u k), by fun_prop⟩
          source' := by
            show (⇑F) (0, u k) = p (u k)
            rw [← Homotopy_eval_apply F 0 (u k), Path.Homotopy.eval_zero]
          target' := by
            show (⇑F) (1, u k) = q (u k)
            rw [← Homotopy_eval_apply F 1 (u k), Path.Homotopy.eval_one] }
      have hcv : ∀ t, col t = F (t, u k) := fun t => rfl
      have hedge : ∀ t ∈ Set.Icc (u j) (u (j + 1)), F (t, u k) ∈ U ∩ V := by
        intro t ht
        have h1 : F (t, u k) ∈ Work.SphereJordan.Side.set U V (lab j k) :=
          hcell j k hj hkN t (u k) ht.1 ht.2 le_rfl ((hstrict k hkN).le)
        have h2 : F (t, u k) ∈ Work.SphereJordan.Side.set U V (lab j (k - 1)) :=
          hcell j (k - 1) hj (by omega) t (u k) ht.1 ht.2
            (humono (k - 1) k (by omega) (by omega))
            (by rw [show k - 1 + 1 = k from by omega])
        have hmem : F (t, u k) ∈ Work.SphereJordan.Side.set U V (lab j k)
            ∩ Work.SphereJordan.Side.set U V (lab j (k - 1)) := ⟨h1, h2⟩
        rwa [Work.SphereJordan.side_set_mono hlab] at hmem
      have hpiece := Work.SphereJordan.h0cls_eq_of_piece (W := U ∩ V) (γ := col)
        (p := u j) (q := u (j + 1)) ((hstrict j hj).le) (by
          intro t ht
          rw [hcv]
          exact hedge t ht)
      rw [hcv, hcv] at hpiece
      simp only [hf]
      rw [hpiece, sub_self]
  -- the two boundary sums
  let sdP : ℕ → Work.SphereJordan.Side := fun i =>
    if lab 0 i = Work.SphereJordan.Side.U then Work.SphereJordan.Side.U else Work.SphereJordan.Side.V
  have hvalidP : ∀ i, i < N → sdP i = Work.SphereJordan.Side.U → ∀ s : unitInterval,
      u i ≤ s → s ≤ u (i + 1) → p s ∈ U := by
    intro i hi hsu s hs1 hs2
    have hlab : lab 0 i = Work.SphereJordan.Side.U := by
      by_cases h : lab 0 i = Work.SphereJordan.Side.U
      · exact h
      · simp only [sdP, if_neg h] at hsu
        exact absurd hsu (by decide)
    have hp' : p s = (⇑F) (0, s) := by
      rw [← Homotopy_eval_apply F 0 s, Path.Homotopy.eval_zero]
    have hmem := hcell 0 i hN hi 0 s (by rw [hu0]) (u 1).2.1 hs1 hs2
    rw [hlab] at hmem
    rw [hp']
    exact hmem
  have hvalidPV : ∀ i, i < N → sdP i = Work.SphereJordan.Side.V → ∀ s : unitInterval,
      u i ≤ s → s ≤ u (i + 1) → p s ∈ V := by
    intro i hi hsv s hs1 hs2
    have hlab : lab 0 i ≠ Work.SphereJordan.Side.U := by
      intro h
      simp only [sdP, if_pos h] at hsv
      exact absurd hsv (by decide)
    have hp' : p s = (⇑F) (0, s) := by
      rw [← Homotopy_eval_apply F 0 s, Path.Homotopy.eval_zero]
    have hmem := hcell 0 i hN hi 0 s (by rw [hu0]) (u 1).2.1 hs1 hs2
    have hlabV : lab 0 i = Work.SphereJordan.Side.V := by
      cases h : lab 0 i with
      | U => exact absurd h hlab
      | V => rfl
    rw [hlabV] at hmem
    rw [hp']
    exact hmem
  let lsp : Work.SphereJordan.LSub U V p :=
    Work.SphereJordan.LSub.mk N u hu0 huN hstrict sdP hvalidP hvalidPV
  have hXp : Xfer hUo hVo p hp
      = ∑ i ∈ Finset.range N, w i 0 • (f (i + 1) 0 - f i 0) := by
    rw [Xfer_eq hp lsp, Work.SphereJordan.LSub.transfer_def]
    show Work.SphereJordan.wTrans U V (fun i => p (u i))
      (fun i => if lsp.side i = Work.SphereJordan.Side.U then 1 else 0) N = _
    rw [Work.SphereJordan.wTrans]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hw0 : w i 0 = (if sdP i = Work.SphereJordan.Side.U then (1 : ℤ) else 0) := by
      simp only [hw, sdP]
      by_cases h : lab 0 i = Work.SphereJordan.Side.U <;> simp [h]
    rw [hw0, ← hf0 i, ← hf0 (i + 1)]
  let sdQ : ℕ → Work.SphereJordan.Side := fun i =>
    if lab (N - 1) i = Work.SphereJordan.Side.U then Work.SphereJordan.Side.U
    else Work.SphereJordan.Side.V
  have hvalidQ : ∀ i, i < N → sdQ i = Work.SphereJordan.Side.U → ∀ s : unitInterval,
      u i ≤ s → s ≤ u (i + 1) → q s ∈ U := by
    intro i hi hsu s hs1 hs2
    have hlab : lab (N - 1) i = Work.SphereJordan.Side.U := by
      by_cases h : lab (N - 1) i = Work.SphereJordan.Side.U
      · exact h
      · simp only [sdQ, if_neg h] at hsu
        exact absurd hsu (by decide)
    have hq' : q s = (⇑F) (1, s) := by
      rw [← Homotopy_eval_apply F 1 s, Path.Homotopy.eval_one]
    have hmem := hcell (N - 1) i (by omega) hi 1 s (u (N - 1)).2.2
      (by rw [show N - 1 + 1 = N from by omega, huN]) hs1 hs2
    rw [hlab] at hmem
    rw [hq']
    exact hmem
  have hvalidQV : ∀ i, i < N → sdQ i = Work.SphereJordan.Side.V → ∀ s : unitInterval,
      u i ≤ s → s ≤ u (i + 1) → q s ∈ V := by
    intro i hi hsv s hs1 hs2
    have hlab : lab (N - 1) i ≠ Work.SphereJordan.Side.U := by
      intro h
      simp only [sdQ, if_pos h] at hsv
      exact absurd hsv (by decide)
    have hq' : q s = (⇑F) (1, s) := by
      rw [← Homotopy_eval_apply F 1 s, Path.Homotopy.eval_one]
    have hmem := hcell (N - 1) i (by omega) hi 1 s (u (N - 1)).2.2
      (by rw [show N - 1 + 1 = N from by omega, huN]) hs1 hs2
    have hlabV : lab (N - 1) i = Work.SphereJordan.Side.V := by
      cases h : lab (N - 1) i with
      | U => exact absurd h hlab
      | V => rfl
    rw [hlabV] at hmem
    rw [hq']
    exact hmem
  let lsq : Work.SphereJordan.LSub U V q :=
    Work.SphereJordan.LSub.mk N u hu0 huN hstrict sdQ hvalidQ hvalidQV
  have hXq : Xfer hUo hVo q hq
      = ∑ i ∈ Finset.range N, w i (N - 1) • (f (i + 1) N - f i N) := by
    rw [Xfer_eq hq lsq, Work.SphereJordan.LSub.transfer_def]
    show Work.SphereJordan.wTrans U V (fun i => q (u i))
      (fun i => if lsq.side i = Work.SphereJordan.Side.U then 1 else 0) N = _
    rw [Work.SphereJordan.wTrans]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hw0 : w i (N - 1) = (if sdQ i = Work.SphereJordan.Side.U then (1 : ℤ) else 0) := by
      simp only [hw, sdQ]
      by_cases h : lab (N - 1) i = Work.SphereJordan.Side.U <;> simp [h]
    rw [hw0, ← hfN i, ← hfN (i + 1)]
  rw [hXp, hXq]
  exact grid_alg N f w hH' hV' hV0 hVn

end Homotopy

/-! ## The transfer of the power loops spans the image -/

section Powers

variable {U V : Set ℂ}

/-- The inclusion of the punctured plane in the plane. -/
def toPlane : C(Work.SphereJordan.Cs, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩

theorem toPlane_apply (x : Work.SphereJordan.Cs) : toPlane x = (x : ℂ) := rfl

/-- Membership transfer along `toPlane` for paths in the punctured plane. -/
theorem map_mem {a b : Work.SphereJordan.Cs} {γ : Path a b}
    (hγ : ∀ s : unitInterval, toPlane (γ s) ∈ U ∪ V) :
    ∀ s : unitInterval, (γ.map toPlane.continuous) s ∈ U ∪ V := fun s => by
  rw [Path.map_coe]
  exact hγ s

/-- The `n`-th power loop around `0`, as a loop in `ℂ` based at `exp ζ`. -/
noncomputable def ploop (ζ : ℂ) (n : ℤ) : Path (Complex.exp ζ) (Complex.exp ζ) :=
  (Work.SphereJordan.powerLoop (Work.SphereJordan.expP ζ) n).map toPlane.continuous

theorem ploop_apply (ζ : ℂ) (n : ℤ) (s : unitInterval) :
    ploop ζ n s = ((Work.SphereJordan.powerLoop (Work.SphereJordan.expP ζ) n s :
      Work.SphereJordan.Cs) : ℂ) := rfl

theorem ploop_ne (ζ : ℂ) (n : ℤ) (s : unitInterval) : ploop ζ n s ≠ 0 :=
  (Work.SphereJordan.powerLoop (Work.SphereJordan.expP ζ) n s).2

theorem ploop_mem (hcov : U ∪ V = ({0} : Set ℂ)ᶜ) (ζ : ℂ) (n : ℤ) (s : unitInterval) :
    ploop ζ n s ∈ U ∪ V := by
  rw [hcov]
  exact ploop_ne ζ n s

/-- **Homotopy invariance, punctured-plane form.** -/
theorem Xfer_homotopic_cs (hUo : IsOpen U) (hVo : IsOpen V)
    (hcov : U ∪ V = ({0} : Set ℂ)ᶜ) {ζ : ℂ}
    {lam lam' : Path (Work.SphereJordan.expP ζ) (Work.SphereJordan.expP ζ)}
    (h : lam.Homotopic lam')
    (hlam : ∀ s : unitInterval, toPlane (lam s) ∈ U ∪ V)
    (hlam' : ∀ s : unitInterval, toPlane (lam' s) ∈ U ∪ V) :
    Xfer hUo hVo (lam.map toPlane.continuous) (map_mem hlam)
      = Xfer hUo hVo (lam'.map toPlane.continuous) (map_mem hlam') := by
  obtain ⟨F⟩ := h
  refine Xfer_homotopic hUo hVo hcov (F.map toPlane) ?_ (map_mem hlam) (map_mem hlam')
  intro t s
  rw [Path.Homotopy.map_apply]
  exact (F (t, s)).2

/-- **The transfer of the `n`-th power loop is `n` times the transfer of the generator.** -/
theorem Xfer_ploop_zsmul (hUo : IsOpen U) (hVo : IsOpen V)
    (hcov : U ∪ V = ({0} : Set ℂ)ᶜ) (ζ : ℂ) (n : ℤ) :
    Xfer hUo hVo (ploop ζ n) (ploop_mem hcov ζ n)
      = n • Xfer hUo hVo (ploop ζ 1) (ploop_mem hcov ζ 1) := by
  have hpmem : ∀ n s, toPlane (Work.SphereJordan.powerLoop (Work.SphereJordan.expP ζ) n s)
      ∈ U ∪ V := fun n s => by
    rw [hcov]
    exact (Work.SphereJordan.powerLoop (Work.SphereJordan.expP ζ) n s).2
  have htmem : ∀ m n s, ((ploop ζ m).trans (ploop ζ n)) s ∈ U ∪ V :=
    fun m n s => hcov ▸ (by
      rw [Path.trans_apply]
      split_ifs with h
      · exact (Work.SphereJordan.powerLoop (Work.SphereJordan.expP ζ) m _).2
      · exact (Work.SphereJordan.powerLoop (Work.SphereJordan.expP ζ) n _).2)
  have hadd : ∀ m n : ℤ, Xfer hUo hVo (ploop ζ (m + n)) (ploop_mem hcov ζ (m + n))
      = Xfer hUo hVo (ploop ζ m) (ploop_mem hcov ζ m)
        + Xfer hUo hVo (ploop ζ n) (ploop_mem hcov ζ n) := by
    intro m n
    have hcouple : ∀ s : unitInterval,
        toPlane (((Work.SphereJordan.powerLoop (Work.SphereJordan.expP ζ) m).trans
          (Work.SphereJordan.powerLoop (Work.SphereJordan.expP ζ) n)) s) ∈ U ∪ V := by
      intro s
      rw [Path.trans_apply]
      split_ifs with h
      · exact hpmem m _
      · exact hpmem n _
    have hhom := Xfer_homotopic_cs (U := U) (V := V) hUo hVo hcov
      (Work.SphereJordan.powerLoop_trans_homotopic (ζ := ζ) m n) hcouple (hpmem (m + n))
    have heq : (ploop ζ m).trans (ploop ζ n)
        = ((Work.SphereJordan.powerLoop (Work.SphereJordan.expP ζ) m).trans
            (Work.SphereJordan.powerLoop (Work.SphereJordan.expP ζ) n)).map
              toPlane.continuous := by
      rw [Path.map_trans]
      rfl
    have h1 := Xfer_congr (U := U) (V := V) (hUo := hUo) (hVo := hVo) heq
      (htmem m n) (map_mem hcouple)
    have h2 : Xfer hUo hVo (ploop ζ (m + n)) (ploop_mem hcov ζ (m + n))
        = Xfer hUo hVo ((Work.SphereJordan.powerLoop (Work.SphereJordan.expP ζ) (m + n)).map
            toPlane.continuous) (map_mem (hpmem (m + n))) := Xfer_proof_irrel _ _
    calc Xfer hUo hVo (ploop ζ (m + n)) (ploop_mem hcov ζ (m + n))
        = Xfer hUo hVo ((Work.SphereJordan.powerLoop (Work.SphereJordan.expP ζ) (m + n)).map
            toPlane.continuous) (map_mem (hpmem (m + n))) := h2
      _ = Xfer hUo hVo (((Work.SphereJordan.powerLoop (Work.SphereJordan.expP ζ) m).trans
            (Work.SphereJordan.powerLoop (Work.SphereJordan.expP ζ) n)).map
              toPlane.continuous) (map_mem hcouple) := hhom.symm
      _ = Xfer hUo hVo ((ploop ζ m).trans (ploop ζ n)) (htmem m n) := h1.symm
      _ = Xfer hUo hVo (ploop ζ m) (ploop_mem hcov ζ m)
            + Xfer hUo hVo (ploop ζ n) (ploop_mem hcov ζ n) :=
          Xfer_trans (hUo := hUo) (hVo := hVo) (γ := ploop ζ m) (δ := ploop ζ n)
            (ploop_mem hcov ζ m) (ploop_mem hcov ζ n) (htmem m n)
  have h0 : Xfer hUo hVo (ploop ζ 0) (ploop_mem hcov ζ 0)
      = (0 : ℤ) • Xfer hUo hVo (ploop ζ 1) (ploop_mem hcov ζ 1) := by
    rw [zero_smul]
    have h := hadd 0 0
    rw [show (0 : ℤ) + 0 = 0 from rfl] at h
    exact add_left_cancel (by rw [add_zero]; exact h.symm)
  have hneg1 : Xfer hUo hVo (ploop ζ (-1)) (ploop_mem hcov ζ (-1))
      = - Xfer hUo hVo (ploop ζ 1) (ploop_mem hcov ζ 1) := by
    have h := hadd 1 (-1)
    rw [show (1 : ℤ) + (-1) = 0 from by ring, h0, zero_smul] at h
    have h' : Xfer hUo hVo (ploop ζ 1) (ploop_mem hcov ζ 1)
        + Xfer hUo hVo (ploop ζ (-1)) (ploop_mem hcov ζ (-1)) = 0 := h.symm
    calc Xfer hUo hVo (ploop ζ (-1)) (ploop_mem hcov ζ (-1))
        = (Xfer hUo hVo (ploop ζ 1) (ploop_mem hcov ζ 1)
            + Xfer hUo hVo (ploop ζ (-1)) (ploop_mem hcov ζ (-1)))
          - Xfer hUo hVo (ploop ζ 1) (ploop_mem hcov ζ 1) := by abel
      _ = 0 - Xfer hUo hVo (ploop ζ 1) (ploop_mem hcov ζ 1) := by rw [h']
      _ = - Xfer hUo hVo (ploop ζ 1) (ploop_mem hcov ζ 1) := by rw [zero_sub]
  refine Int.induction_on n (motive := fun n => Xfer hUo hVo (ploop ζ n) (ploop_mem hcov ζ n)
    = n • Xfer hUo hVo (ploop ζ 1) (ploop_mem hcov ζ 1)) h0 ?_ ?_
  · intro k ih
    rw [show ((k : ℤ) + 1) = (k : ℤ) + 1 from rfl, hadd (k : ℤ) 1, ih, add_one_zsmul]
  · intro k ih
    rw [show (-(k : ℤ) - 1) = (-(k : ℤ)) + (-1) from by ring, hadd (-(k : ℤ)) (-1), ih,
      hneg1, add_zsmul, neg_one_zsmul]

/-- Every loop in the punctured plane based at `exp ζ` has transfer a multiple of the
generator's. -/
theorem Xfer_loop_zsmul (hUo : IsOpen U) (hVo : IsOpen V) (hcov : U ∪ V = ({0} : Set ℂ)ᶜ)
    (ζ : ℂ) (lam : Path (Work.SphereJordan.expP ζ) (Work.SphereJordan.expP ζ))
    (hlam : ∀ s : unitInterval, toPlane (lam s) ∈ U ∪ V) :
    ∃ m : ℤ, Xfer hUo hVo (lam.map toPlane.continuous) (map_mem hlam)
      = m • Xfer hUo hVo (ploop ζ 1) (ploop_mem hcov ζ 1) := by
  obtain ⟨m, hm⟩ := Work.SphereJordan.exists_int_lift_endpoint (ζ := ζ) lam
  have hhom := Work.SphereJordan.homotopic_powerLoop (ζ := ζ) lam hm
  have h := Xfer_homotopic_cs (U := U) (V := V) hUo hVo hcov hhom hlam
    (fun s => ploop_mem (U := U) (V := V) hcov ζ m s)
  refine ⟨m, ?_⟩
  have h3 : Xfer hUo hVo ((Work.SphereJordan.powerLoop (Work.SphereJordan.expP ζ) m).map
      toPlane.continuous) (map_mem (fun s => ploop_mem (U := U) (V := V) hcov ζ m s))
      = Xfer hUo hVo (ploop ζ m) (ploop_mem hcov ζ m) := Xfer_proof_irrel _ _
  rw [h, h3]
  exact Xfer_ploop_zsmul (U := U) (V := V) hUo hVo hcov ζ m

end Powers

end Grid

end TransferPath
end

/-! ## The annulus-cover pigeonhole -/

/-! ## The annulus-cover pigeonhole -/

section Final

variable {U V : Set ℂ}

/-- A nonzero complex number is in the cover (when `U ∪ V = ℂ∖{0}`). -/
theorem mem_of_ne_zero (hcov : U ∪ V = ({0} : Set ℂ)ᶜ) {w : ℂ} (h : w ≠ 0) : w ∈ U ∪ V := by
  rw [hcov]
  exact h

/-- A path in `ℂ` avoiding `0`, as a path in the punctured plane. -/
noncomputable def toCsPath {a b : ℂ} (ha : a ∈ ({0} : Set ℂ)ᶜ) (hb : b ∈ ({0} : Set ℂ)ᶜ)
    (γ : Path a b) (hγ : ∀ t : unitInterval, γ t ∈ ({0} : Set ℂ)ᶜ) :
    Path (⟨a, ha⟩ : Work.SphereJordan.Cs) ⟨b, hb⟩ where
  toContinuousMap := ⟨fun t => ⟨γ t, hγ t⟩, Continuous.subtype_mk γ.continuous hγ⟩
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

theorem toCsPath_map {a b : ℂ} (ha : a ∈ ({0} : Set ℂ)ᶜ) (hb : b ∈ ({0} : Set ℂ)ᶜ)
    (γ : Path a b) (hγ : ∀ t : unitInterval, γ t ∈ ({0} : Set ℂ)ᶜ) :
    (toCsPath ha hb γ hγ).map toPlane.continuous = γ := by
  apply Path.ext
  funext t
  rw [Path.map_coe]
  rfl

/-- The classes of `h0cls` and `H0Class` agree. -/
theorem h0cls_eq_H0Class {W : Set ℂ} {w : ℂ} (hw : w ∈ W) :
    Work.SphereJordan.h0cls W w = H0Class W w hw := by
  rw [Work.SphereJordan.h0cls_of_mem hw, H0Class]

end Final

section Pigeonhole

variable {U V : Set ℂ}

/-- **The annulus-cover pigeonhole.** -/
theorem annulusCoverPigeonhole {U V : Set ℂ} (hUo : IsOpen U) (hVo : IsOpen V)
    (hUc : IsPreconnected U) (hVc : IsPreconnected V)
    (hcov : U ∪ V = ({0} : Set ℂ)ᶜ) :
    ∀ x y z : ℂ, x ∈ U ∩ V → y ∈ U ∩ V → z ∈ U ∩ V →
      connectedComponentIn (U ∩ V) x = connectedComponentIn (U ∩ V) y ∨
      connectedComponentIn (U ∩ V) x = connectedComponentIn (U ∩ V) z ∨
      connectedComponentIn (U ∩ V) y = connectedComponentIn (U ∩ V) z := by
  intro x y z hx hy hz
  rcases eq_or_ne x y with rfl | hxy
  · exact Or.inl rfl
  rcases eq_or_ne x z with rfl | hxz
  · exact Or.inr (Or.inl rfl)
  rcases eq_or_ne y z with rfl | hyz
  · exact Or.inr (Or.inr rfl)
  classical
  -- write the base point as `exp ζ`
  have hxne : x ≠ 0 := by
    have h : x ∈ U ∪ V := Or.inl hx.1
    rwa [hcov] at h
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, Complex.exp ζ = x := ⟨Complex.log x, Complex.exp_log hxne⟩
  subst hζ
  -- the base point is now `Complex.exp ζ`
  have hy0 : y ∈ ({0} : Set ℂ)ᶜ := by
    have h : y ∈ U ∪ V := Or.inl hy.1
    rwa [hcov] at h
  have hz0 : z ∈ ({0} : Set ℂ)ᶜ := by
    have h : z ∈ U ∪ V := Or.inl hz.1
    rwa [hcov] at h
  -- paths inside `U` and inside `V`
  have hUpc : IsPathConnected U :=
    (hUo.isConnected_iff_isPathConnected).mp ⟨⟨Complex.exp ζ, hx.1⟩, hUc⟩
  have hVpc : IsPathConnected V :=
    (hVo.isConnected_iff_isPathConnected).mp ⟨⟨y, hy.2⟩, hVc⟩
  obtain ⟨γ₁, hγ₁⟩ := hUpc.joinedIn (Complex.exp ζ) hx.1 y hy.1
  obtain ⟨γ₂, hγ₂⟩ := hUpc.joinedIn y hy.1 z hz.1
  obtain ⟨δ₁, hδ₁⟩ := hVpc.joinedIn y hy.2 (Complex.exp ζ) hx.2
  obtain ⟨δ₂, hδ₂⟩ := hVpc.joinedIn z hz.2 y hy.2
  -- nonzero-ness
  have hγ₁n : ∀ t, γ₁ t ∈ ({0} : Set ℂ)ᶜ := fun t => by
    rw [← hcov]; exact Or.inl (hγ₁ t)
  have hγ₂n : ∀ t, γ₂ t ∈ ({0} : Set ℂ)ᶜ := fun t => by
    rw [← hcov]; exact Or.inl (hγ₂ _)
  have hδ₁n : ∀ t, δ₁ t ∈ ({0} : Set ℂ)ᶜ := fun t => by
    rw [← hcov]; exact Or.inr (hδ₁ _)
  have hδ₂n : ∀ t, δ₂ t ∈ ({0} : Set ℂ)ᶜ := fun t => by
    rw [← hcov]; exact Or.inr (hδ₂ _)
  -- the two loops in `ℂ`
  let mu₁ : Path (Complex.exp ζ) (Complex.exp ζ) := γ₁.trans δ₁
  let mu₂ : Path (Complex.exp ζ) (Complex.exp ζ) := γ₁.trans (γ₂.trans (δ₂.trans δ₁))
  have hmu₁z : ∀ t, mu₁ t ≠ 0 := fun t => by
    simp only [mu₁]
    rw [Path.trans_apply]
    split_ifs with h
    · exact hγ₁n _
    · exact hδ₁n _
  have hmu₂z : ∀ t, mu₂ t ≠ 0 := fun t => by
    simp only [mu₂]
    rw [Path.trans_apply]
    split_ifs with h
    · exact hγ₁n _
    · rw [Path.trans_apply]
      split_ifs with h2
      · exact hγ₂n _
      · rw [Path.trans_apply]
        split_ifs with h3
        · exact hδ₂n _
        · exact hδ₁n _
  -- memberships of the intermediate composites
  have hmem₂ : ∀ t, (γ₂.trans (δ₂.trans δ₁)) t ∈ U ∪ V := fun t => by
    rw [Path.trans_apply]
    split_ifs with h
    · exact Or.inl (hγ₂ _)
    · rw [Path.trans_apply]
      split_ifs with h2
      · exact Or.inr (hδ₂ _)
      · exact Or.inr (hδ₁ _)
  have hmemδ : ∀ t, (δ₂.trans δ₁) t ∈ U ∪ V := fun t => by
    rw [Path.trans_apply]
    split_ifs with h
    · exact Or.inr (hδ₂ _)
    · exact Or.inr (hδ₁ _)
  -- transfers of the two loops
  have hX₁ : Xfer hUo hVo mu₁ (fun t => mem_of_ne_zero hcov (hmu₁z t))
      = Work.SphereJordan.h0cls (U ∩ V) y - Work.SphereJordan.h0cls (U ∩ V) (Complex.exp ζ) := by
    simp only [mu₁]
    rw [Xfer_trans (hUo := hUo) (hVo := hVo) (γ := γ₁) (δ := δ₁)
      (fun t => Or.inl (hγ₁ t)) (fun t => Or.inr (hδ₁ t))
      (fun t => mem_of_ne_zero hcov (by
        rw [Path.trans_apply]
        split_ifs with h
        · exact hγ₁n _
        · exact hδ₁n _)),
      Xfer_of_mem_U hγ₁ (fun t => Or.inl (hγ₁ t)),
      Xfer_of_mem_V hδ₁ (fun t => Or.inr (hδ₁ t)), add_zero]
  have hX₂ : Xfer hUo hVo mu₂ (fun t => mem_of_ne_zero hcov (hmu₂z t))
      = Work.SphereJordan.h0cls (U ∩ V) z - Work.SphereJordan.h0cls (U ∩ V) (Complex.exp ζ) := by
    simp only [mu₂]
    rw [Xfer_trans (hUo := hUo) (hVo := hVo) (γ := γ₁) (δ := γ₂.trans (δ₂.trans δ₁))
      (fun t => Or.inl (hγ₁ t)) hmem₂ (fun t => mem_of_ne_zero hcov (by
        rw [Path.trans_apply]
        split_ifs with h
        · exact hγ₁n _
        · rw [Path.trans_apply]
          split_ifs with h2
          · exact hγ₂n _
          · rw [Path.trans_apply]
            split_ifs with h3
            · exact hδ₂n _
            · exact hδ₁n _)),
      Xfer_of_mem_U hγ₁ (fun t => Or.inl (hγ₁ t))]
    rw [Xfer_trans (hUo := hUo) (hVo := hVo) (γ := γ₂) (δ := δ₂.trans δ₁)
      (fun t => Or.inl (hγ₂ t)) hmemδ (fun t => mem_of_ne_zero hcov (by
        rw [Path.trans_apply]
        split_ifs with h
        · exact hγ₂n _
        · rw [Path.trans_apply]
          split_ifs with h2
          · exact hδ₂n _
          · exact hδ₁n _)),
      Xfer_trans (hUo := hUo) (hVo := hVo) (γ := δ₂) (δ := δ₁)
        (fun t => Or.inr (hδ₂ t)) (fun t => Or.inr (hδ₁ t))
        (fun t => mem_of_ne_zero hcov (by
          rw [Path.trans_apply]
          split_ifs with h
          · exact hδ₂n _
          · exact hδ₁n _)),
      Xfer_of_mem_U hγ₂ (fun t => Or.inl (hγ₂ t)),
      Xfer_of_mem_V hδ₂ (fun t => Or.inr (hδ₂ t)),
      Xfer_of_mem_V hδ₁ (fun t => Or.inr (hδ₁ t))]
    abel
  -- the same loops in the punctured plane (built by hand so that the base point is `expP ζ`)
  let γ₁c : Path (Work.SphereJordan.expP ζ) (⟨y, hy0⟩ : Work.SphereJordan.Cs) :=
    { toContinuousMap := ⟨fun t => ⟨γ₁ t, hγ₁n t⟩, Continuous.subtype_mk γ₁.continuous hγ₁n⟩
      source' := Subtype.ext γ₁.source
      target' := Subtype.ext γ₁.target }
  let γ₂c : Path (⟨y, hy0⟩ : Work.SphereJordan.Cs) (⟨z, hz0⟩ : Work.SphereJordan.Cs) :=
    { toContinuousMap := ⟨fun t => ⟨γ₂ t, hγ₂n t⟩, Continuous.subtype_mk γ₂.continuous hγ₂n⟩
      source' := Subtype.ext γ₂.source
      target' := Subtype.ext γ₂.target }
  let δ₂c : Path (⟨z, hz0⟩ : Work.SphereJordan.Cs) (⟨y, hy0⟩ : Work.SphereJordan.Cs) :=
    { toContinuousMap := ⟨fun t => ⟨δ₂ t, hδ₂n t⟩, Continuous.subtype_mk δ₂.continuous hδ₂n⟩
      source' := Subtype.ext δ₂.source
      target' := Subtype.ext δ₂.target }
  let δ₁c : Path (⟨y, hy0⟩ : Work.SphereJordan.Cs) (Work.SphereJordan.expP ζ) :=
    { toContinuousMap := ⟨fun t => ⟨δ₁ t, hδ₁n t⟩, Continuous.subtype_mk δ₁.continuous hδ₁n⟩
      source' := Subtype.ext δ₁.source
      target' := Subtype.ext δ₁.target }
  have hmapγ₁ : γ₁c.map toPlane.continuous = γ₁ := by
    apply Path.ext; funext t; rw [Path.map_coe]; rfl
  have hmapγ₂ : γ₂c.map toPlane.continuous = γ₂ := by
    apply Path.ext; funext t; rw [Path.map_coe]; rfl
  have hmapδ₂ : δ₂c.map toPlane.continuous = δ₂ := by
    apply Path.ext; funext t; rw [Path.map_coe]; rfl
  have hmapδ₁ : δ₁c.map toPlane.continuous = δ₁ := by
    apply Path.ext; funext t; rw [Path.map_coe]; rfl
  let lam₁ : Path (Work.SphereJordan.expP ζ) (Work.SphereJordan.expP ζ) := γ₁c.trans δ₁c
  let lam₂ : Path (Work.SphereJordan.expP ζ) (Work.SphereJordan.expP ζ) :=
    γ₁c.trans (γ₂c.trans (δ₂c.trans δ₁c))
  have hmap₁ : lam₁.map toPlane.continuous = mu₁ := by
    simp only [lam₁, mu₁]
    rw [Path.map_trans, hmapγ₁, hmapδ₁]
    rfl
  have hmap₂ : lam₂.map toPlane.continuous = mu₂ := by
    simp only [lam₂, mu₂]
    rw [Path.map_trans, Path.map_trans, Path.map_trans, hmapγ₁, hmapγ₂, hmapδ₂, hmapδ₁]
    rfl
  have hlam₁_mem : ∀ s, toPlane (lam₁ s) ∈ U ∪ V := fun s => by
    have h1 : (lam₁.map toPlane.continuous) s = toPlane (lam₁ s) :=
      congrFun (Path.map_coe lam₁ toPlane.continuous) s
    rw [← h1, hmap₁]
    exact mem_of_ne_zero hcov (hmu₁z s)
  have hlam₂_mem : ∀ s, toPlane (lam₂ s) ∈ U ∪ V := fun s => by
    have h1 : (lam₂.map toPlane.continuous) s = toPlane (lam₂ s) :=
      congrFun (Path.map_coe lam₂ toPlane.continuous) s
    rw [← h1, hmap₂]
    exact mem_of_ne_zero hcov (hmu₂z s)
  -- transfers are equal to those of the punctured-plane loops
  have hT₁ : Xfer hUo hVo mu₁ (fun t => mem_of_ne_zero hcov (hmu₁z t))
      = Xfer hUo hVo (lam₁.map toPlane.continuous) (map_mem hlam₁_mem) :=
    Xfer_congr (hUo := hUo) (hVo := hVo) hmap₁.symm _ _
  have hT₂ : Xfer hUo hVo mu₂ (fun t => mem_of_ne_zero hcov (hmu₂z t))
      = Xfer hUo hVo (lam₂.map toPlane.continuous) (map_mem hlam₂_mem) :=
    Xfer_congr (hUo := hUo) (hVo := hVo) hmap₂.symm _ _
  -- everything is a multiple of the generator
  set g : H0 (U ∩ V) := Xfer hUo hVo (ploop ζ 1) (ploop_mem hcov ζ 1) with hg
  obtain ⟨m₁, hm₁⟩ := Xfer_loop_zsmul (U := U) (V := V) hUo hVo hcov ζ lam₁ hlam₁_mem
  obtain ⟨m₂, hm₂⟩ := Xfer_loop_zsmul (U := U) (V := V) hUo hVo hcov ζ lam₂ hlam₂_mem
  have hE₁ : H0Class (U ∩ V) y hy - H0Class (U ∩ V) (Complex.exp ζ) hx = m₁ • g := by
    rw [← h0cls_eq_H0Class hy, ← h0cls_eq_H0Class hx, ← hX₁, hT₁, hm₁]
  have hE₂ : H0Class (U ∩ V) z hz - H0Class (U ∩ V) y hy = (m₂ - m₁) • g := by
    have h2 : H0Class (U ∩ V) z hz - H0Class (U ∩ V) (Complex.exp ζ) hx = m₂ • g := by
      rw [← h0cls_eq_H0Class hz, ← h0cls_eq_H0Class hx, ← hX₂, hT₂, hm₂]
    calc H0Class (U ∩ V) z hz - H0Class (U ∩ V) y hy
        = (H0Class (U ∩ V) z hz - H0Class (U ∩ V) (Complex.exp ζ) hx)
          - (H0Class (U ∩ V) y hy - H0Class (U ∩ V) (Complex.exp ζ) hx) := by abel
      _ = m₂ • g - m₁ • g := by rw [h2, hE₁]
      _ = (m₂ - m₁) • g := by rw [sub_smul]
  -- the contradiction
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hxy', hxz', hyz'⟩ := hcon
  have hcx_ne_cy : (ConnectedComponents.mk ⟨Complex.exp ζ, hx⟩ : ConnectedComponents ↥(U ∩ V))
      ≠ ConnectedComponents.mk ⟨y, hy⟩ := fun h =>
    hxy' (connectedComponentIn_eq_of_mk_eq hx hy h)
  have hcy_ne_cz : (ConnectedComponents.mk ⟨y, hy⟩ : ConnectedComponents ↥(U ∩ V))
      ≠ ConnectedComponents.mk ⟨z, hz⟩ := fun h =>
    hyz' (connectedComponentIn_eq_of_mk_eq hy hz h)
  have hcx_ne_cz : (ConnectedComponents.mk ⟨Complex.exp ζ, hx⟩ : ConnectedComponents ↥(U ∩ V))
      ≠ ConnectedComponents.mk ⟨z, hz⟩ := fun h =>
    hxz' (connectedComponentIn_eq_of_mk_eq hx hz h)
  have hcoordx : coord (ConnectedComponents.mk ⟨Complex.exp ζ, hx⟩)
      (H0Class (U ∩ V) y hy - H0Class (U ∩ V) (Complex.exp ζ) hx) = -1 := by
    rw [map_sub, H0Class, H0Class, coord_of, coord_of]
    rw [if_neg (Ne.symm hcx_ne_cy), if_pos rfl]
    norm_num
  have hcoordz₂ : coord (ConnectedComponents.mk ⟨Complex.exp ζ, hx⟩)
      (H0Class (U ∩ V) z hz - H0Class (U ∩ V) y hy) = 0 := by
    rw [map_sub, H0Class, H0Class, coord_of, coord_of]
    simp only [if_neg (Ne.symm hcx_ne_cz), if_neg (Ne.symm hcx_ne_cy), if_neg hcx_ne_cz,
      if_neg hcx_ne_cy]
    norm_num
  have hcoordz₁ : coord (ConnectedComponents.mk ⟨z, hz⟩)
      (H0Class (U ∩ V) y hy - H0Class (U ∩ V) (Complex.exp ζ) hx) = 0 := by
    rw [map_sub, H0Class, H0Class, coord_of, coord_of]
    simp only [if_neg hcy_ne_cz, if_neg hcx_ne_cz, if_neg (Ne.symm hcy_ne_cz),
      if_neg (Ne.symm hcx_ne_cz)]
    norm_num
  have hcoordz : coord (ConnectedComponents.mk ⟨z, hz⟩)
      (H0Class (U ∩ V) z hz - H0Class (U ∩ V) y hy) = 1 := by
    rw [map_sub, H0Class, H0Class, coord_of, coord_of]
    rw [if_pos rfl, if_neg hcy_ne_cz]
    norm_num
  have hrel : (m₂ - m₁) • (H0Class (U ∩ V) y hy - H0Class (U ∩ V) (Complex.exp ζ) hx)
      + (-m₁) • (H0Class (U ∩ V) z hz - H0Class (U ∩ V) y hy) = 0 := by
    rw [hE₁, hE₂, smul_smul, smul_smul, ← add_smul,
      show (m₂ - m₁) * m₁ + (-m₁) * (m₂ - m₁) = 0 from by ring, zero_smul]
  have hm1 : m₂ - m₁ = 0 := by
    have h := congrArg (coord (ConnectedComponents.mk ⟨Complex.exp ζ, hx⟩)) hrel
    rw [map_zero, map_add, map_zsmul, map_zsmul, hcoordx, hcoordz₂] at h
    have h' : m₁ - m₂ = 0 := by simpa using h
    omega
  have hm2 : m₁ = 0 := by
    have h := congrArg (coord (ConnectedComponents.mk ⟨z, hz⟩)) hrel
    rw [map_zero, map_add, map_zsmul, map_zsmul, hcoordz₁, hcoordz] at h
    simpa using h
  have hne₁ : H0Class (U ∩ V) y hy ≠ H0Class (U ∩ V) (Complex.exp ζ) hx := fun h => by
    rw [H0Class, H0Class] at h
    exact hxy' (connectedComponentIn_eq_of_mk_eq hx hy
      (FreeAbelianGroup.of_injective h.symm))
  have hzero : H0Class (U ∩ V) y hy - H0Class (U ∩ V) (Complex.exp ζ) hx = 0 := by
    rw [hE₁, hm2, zero_smul]
  exact hne₁ (sub_eq_zero.mp hzero)

end Pigeonhole

end Work.Spike
