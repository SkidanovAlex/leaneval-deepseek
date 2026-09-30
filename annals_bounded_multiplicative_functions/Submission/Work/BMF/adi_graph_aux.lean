import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.adi_graph_defs
import Submission.Work.BMF.tuple_setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# N5 `adi_cycles`: the walk-counting bridge

`pathSet Adj ℓ x y` is the set of walks of length `ℓ` from `x` to `y` in a finite graph, and
`walk_count_eq` identifies its cardinality with the `(x,y)`-entry of the `ℓ`-th power of the
adjacency matrix.  This is the bridge between the abstract bicycle count (`bike_count`) and the
combinatorics of `Submission.Work.BMF.adi_graph_defs`.
-/

namespace Work.BMF

open Polynomial Finset Real

/-- Walks of length `ℓ` from `x` to `y` in a graph with adjacency `Adj`, as vertex sequences. -/
noncomputable def pathSet {V : Type*} [Fintype V] [DecidableEq V] (Adj : V → V → Prop)
    [DecidableRel Adj] (ℓ : ℕ) (x y : V) : Finset (Fin (ℓ + 1) → V) :=
  (Finset.univ : Finset (Fin (ℓ + 1) → V)).filter
    (fun W => (∀ j : Fin ℓ, Adj (W j.castSucc) (W j.succ)) ∧
      W 0 = x ∧ W ⟨ℓ, Nat.lt_succ_self ℓ⟩ = y)

/-- Append an element at the end of a tuple. -/
def snocFun {α : Type*} {n : ℕ} (f : Fin n → α) (a : α) : Fin (n + 1) → α :=
  fun i => if h : i.val < n then f ⟨i.val, h⟩ else a

lemma snocFun_castSucc {α : Type*} {n : ℕ} (f : Fin n → α) (a : α) (i : Fin n) :
    snocFun f a i.castSucc = f i := by
  simp only [snocFun, Fin.val_castSucc, dif_pos i.isLt]

lemma snocFun_last {α : Type*} {n : ℕ} (f : Fin n → α) (a : α) :
    snocFun f a (Fin.last n) = a := by
  unfold snocFun
  rw [dif_neg (by simp [Fin.last])]

lemma castSucc_succ_eq_succ_castSucc {n : ℕ} (j : Fin n) :
    (((Fin.succ (Fin.castSucc j)) : Fin (n + 2))) = ((j.succ : Fin (n + 1)).castSucc : Fin (n + 2)) := by
  ext
  simp

lemma last_succ_eq_last {n : ℕ} :
    (((Fin.last n).succ) : Fin (n + 2)) = Fin.last (n + 1) := by
  ext
  simp [Fin.last]

/-- When `z` is not adjacent to `y`, no walk of length `ℓ+1` from `x` to `y` has `z` at
position `ℓ`. -/
lemma pathSet_fiber_empty {V : Type*} [Fintype V] [DecidableEq V] {Adj : V → V → Prop}
    [DecidableRel Adj] {ℓ : ℕ} {x y z : V} (hz : ¬ Adj z y) :
    ((pathSet Adj (ℓ + 1) x y).filter (fun W => W (Fin.castSucc (Fin.last ℓ)) = z)) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro W hW
  simp only [Finset.mem_filter, pathSet, Finset.mem_univ, true_and] at hW
  obtain ⟨⟨hadj, h0, hlast⟩, hmid⟩ := hW
  refine hz ?_
  have h := hadj (Fin.last ℓ)
  rw [hmid, last_succ_eq_last] at h
  have hl : W (Fin.last (ℓ + 1)) = y := by
    rw [show Fin.last (ℓ + 1) = (⟨ℓ + 1, by omega⟩ : Fin (ℓ + 2)) from
      Fin.ext (by simp [Fin.last])]
    exact hlast
  rw [hl] at h
  exact h

/-! ## The last-step decomposition -/

lemma pathSet_succ {V : Type*} [Fintype V] [DecidableEq V] (Adj : V → V → Prop)
    [DecidableRel Adj] (ℓ : ℕ) (x y : V) :
    (pathSet Adj (ℓ + 1) x y).card =
      ∑ z : V, (if Adj z y then 1 else 0) * (pathSet Adj ℓ x z).card := by
  classical
  have h1 : (pathSet Adj (ℓ + 1) x y).card =
      ∑ z : V, ((pathSet Adj (ℓ + 1) x y).filter
        (fun W => W (Fin.castSucc (Fin.last ℓ)) = z)).card :=
    Finset.card_eq_sum_card_fiberwise
      (f := fun W : Fin (ℓ + 2) → V => W (Fin.castSucc (Fin.last ℓ)))
      (t := Finset.univ) (fun W _ => Finset.mem_univ _)
  have hset : ∀ z : V, ((pathSet Adj (ℓ + 1) x y).filter (fun W => W (Fin.castSucc (Fin.last ℓ)) = z))
      = if Adj z y then (pathSet Adj ℓ x z).image (fun W' => snocFun W' y) else ∅ := by
    intro z
    by_cases hz : Adj z y
    · rw [if_pos hz]
      ext W
      simp only [Finset.mem_filter, Finset.mem_image, pathSet, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hadj, h0, hlast⟩, hmid⟩
        refine ⟨fun j => W j.castSucc, ⟨?_, ?_, ?_⟩, ?_⟩
        · intro j
          have h := hadj j.castSucc
          rw [castSucc_succ_eq_succ_castSucc j] at h
          exact h
        · show W ((0 : Fin (ℓ + 1)).castSucc) = x
          rw [show ((0 : Fin (ℓ + 1)).castSucc : Fin (ℓ + 2)) = 0 from by ext; simp]
          exact h0
        · show W (Fin.castSucc (Fin.last ℓ)) = z
          exact hmid
        · funext i
          induction i using Fin.lastCases with
          | last =>
              rw [snocFun_last]
              show y = W (Fin.last (ℓ + 1))
              rw [← last_succ_eq_last]
              exact hlast.symm
          | cast j =>
              show snocFun (fun j => W j.castSucc) y j.castSucc = W j.castSucc
              rw [snocFun_castSucc]
      · rintro ⟨W', ⟨hadj, h0, hlast⟩, rfl⟩
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · intro i
          induction i using Fin.lastCases with
          | last =>
              show Adj (snocFun W' y (Fin.castSucc (Fin.last ℓ))) (snocFun W' y (Fin.succ (Fin.last ℓ)))
              rw [snocFun_castSucc, last_succ_eq_last, snocFun_last]
              have hz' : W' (Fin.last ℓ) = z := hlast
              rw [hz']
              exact hz
          | cast j =>
              show Adj (snocFun W' y (Fin.castSucc (Fin.castSucc j))) (snocFun W' y (Fin.succ (Fin.castSucc j)))
              rw [castSucc_succ_eq_succ_castSucc j, snocFun_castSucc, snocFun_castSucc]
              exact hadj j
        · show snocFun W' y ((0 : Fin (ℓ + 1)).castSucc) = x
          rw [snocFun_castSucc]
          exact h0
        · show snocFun W' y (Fin.last (ℓ + 1)) = y
          rw [snocFun_last]
        · show snocFun W' y (Fin.castSucc (Fin.last ℓ)) = z
          rw [snocFun_castSucc]
          exact hlast
    · rw [if_neg hz, pathSet_fiber_empty (Adj := Adj) (x := x) (y := y) (ℓ := ℓ) hz]
  rw [h1]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [hset z]
  by_cases hz : Adj z y
  · have hcard : ((pathSet Adj ℓ x z).image (fun W' => snocFun W' y)).card
        = (pathSet Adj ℓ x z).card := by
      rw [Finset.card_image_of_injOn]
      intro W₁ _ W₂ _ h
      funext i
      have hh := congrFun h i.castSucc
      simpa only [snocFun_castSucc] using hh
    simp only [if_pos hz, hcard, one_mul]
  · simp only [if_neg hz, Finset.card_empty, zero_mul]

/-- **The walk count is the matrix entry.**  The `(x,y)`-entry of the `ℓ`-th power of the
adjacency matrix of a finite graph is the number of walks of length `ℓ` from `x` to `y`. -/
theorem walk_count_eq {V : Type*} [Fintype V] [DecidableEq V] (Adj : V → V → Prop)
    [DecidableRel Adj] (ℓ : ℕ) (x y : V) :
    ((Matrix.of (fun i j : V => if Adj i j then (1 : ℝ) else 0)) ^ ℓ) x y =
      ((pathSet Adj ℓ x y).card : ℝ) := by
  classical
  induction ℓ generalizing x y with
  | zero =>
      rw [pow_zero, Matrix.one_apply]
      by_cases h : x = y
      · subst h
        have hset : pathSet Adj 0 x x = {fun _ => x} := by
          ext W
          simp only [pathSet, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton]
          constructor
          · intro hW
            funext i
            have hi : i = (⟨0, Nat.lt_succ_self 0⟩ : Fin 1) := Fin.ext (by omega)
            rw [hi]
            exact hW.2.1
          · intro hW
            rw [hW]
            exact ⟨by simp, by simp⟩
        rw [hset, Finset.card_singleton]
        norm_num
      · have hset : pathSet Adj 0 x y = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro W hW
          simp only [pathSet, Finset.mem_filter, Finset.mem_univ, true_and] at hW
          have h0 : W 0 = x := hW.2.1
          have h1 : W 0 = y := by
            have hh := hW.2.2
            rwa [show (⟨0, Nat.lt_succ_self 0⟩ : Fin 1) = 0 from Fin.ext rfl] at hh
          exact h (h0.symm.trans h1)
        rw [hset, Finset.card_empty]
        simp [h]
  | succ ℓ ih =>
      rw [pow_succ, Matrix.mul_apply, pathSet_succ, Nat.cast_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Nat.cast_mul, ih x z]
      rw [show (Matrix.of (fun i j : V => if Adj i j then (1 : ℝ) else 0)) z y
          = (if Adj z y then (1 : ℝ) else 0) from rfl]
      by_cases hz : Adj z y <;> simp [hz]

/-! ## Labels determine the walk -/

section

variable {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}

/-- The labels of a walk of the `q`-subgraph, as a pair of `ℓ`-tuples of primes. -/
noncomputable def walkLabels (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ)
    (W : Fin (ℓ + 1) → GVert D) : (Fin ℓ → ℕ) × (Fin ℓ → ℕ) :=
  (fun j => stepV D (W j.castSucc) (W j.succ), fun j => stepU D (W j.castSucc) (W j.succ))

/-- Two walks in the `q`-subgraph which start at the same vertex and have the same labels
coincide. -/
theorem walk_eq_of_labels (D : QuadData k f c C X L P₁ P₂) (hP : 0 < P₁) (hL : 0 < L)
    {q ℓ : ℕ} {W W' : Fin (ℓ + 1) → GVert D}
    (hW : W ∈ walkSet D q ℓ) (hW' : W' ∈ walkSet D q ℓ) (h0 : W 0 = W' 0) :
    walkLabels D ℓ W = walkLabels D ℓ W' → W = W' := by
  intro hlab
  have hV : ∀ j : Fin ℓ, stepV D (W j.castSucc) (W j.succ) = stepV D (W' j.castSucc) (W' j.succ) :=
    fun j => congrFun (congrArg Prod.fst hlab) j
  have hU : ∀ j : Fin ℓ, stepU D (W j.castSucc) (W j.succ) = stepU D (W' j.castSucc) (W' j.succ) :=
    fun j => congrFun (congrArg Prod.snd hlab) j
  have hadjW : ∀ j : Fin ℓ, GAdjQ D q (W j.castSucc) (W j.succ) :=
    fun j => (Finset.mem_filter.mp hW).2 j
  have hadjW' : ∀ j : Fin ℓ, GAdjQ D q (W' j.castSucc) (W' j.succ) :=
    fun j => (Finset.mem_filter.mp hW').2 j
  funext i
  induction i using Fin.induction with
  | zero => exact h0
  | succ j ih =>
      have h1 : stepV D (W j.castSucc) (W j.succ) = stepV D (W j.castSucc) (W' j.succ) := by
        have hh := hV j
        rw [← ih] at hh
        exact hh
      have h2 : stepU D (W j.castSucc) (W j.succ) = stepU D (W j.castSucc) (W' j.succ) := by
        have hh := hU j
        rw [← ih] at hh
        exact hh
      have hxy' : GAdjQ D q (W j.castSucc) (W' j.succ) := by
        have hh := hadjW' j
        rw [← ih] at hh
        exact hh
      exact step_unique D hP hL (hadjW j) hxy' h1 h2

/-- The labels of a walk of the `q`-subgraph lie in `[P₁, 2P₁]`. -/
lemma walkLabels_mem (D : QuadData k f c C X L P₁ P₂) {q ℓ : ℕ} {W : Fin (ℓ + 1) → GVert D}
    (hW : W ∈ walkSet D q ℓ) {j : Fin ℓ} :
    IsPrimeIn P₁ (2 * P₁) (stepV D (W j.castSucc) (W j.succ)) ∧
      IsPrimeIn P₁ (2 * P₁) (stepU D (W j.castSucc) (W j.succ)) :=
  ⟨stepV_prime D ((Finset.mem_filter.mp hW).2 j), stepU_prime D ((Finset.mem_filter.mp hW).2 j)⟩


/-- The candidate label pairs: two `ℓ`-tuples of primes in `[P₁, 2P₁]`. -/
noncomputable def labelPairs (P₁ : ℝ) (ℓ : ℕ) : Finset ((Fin ℓ → ℕ) × (Fin ℓ → ℕ)) :=
  Fintype.piFinset (fun _ : Fin ℓ => primesIn P₁ (2 * P₁)) ×ˢ
    Fintype.piFinset (fun _ : Fin ℓ => primesIn P₁ (2 * P₁))

lemma walkLabels_mem_labelPairs (D : QuadData k f c C X L P₁ P₂) (hP : 0 < P₁) {q ℓ : ℕ}
    {W : Fin (ℓ + 1) → GVert D} (hW : W ∈ walkSet D q ℓ) :
    walkLabels D ℓ W ∈ labelPairs P₁ ℓ := by
  rw [labelPairs, Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]
  refine ⟨fun j => ?_, fun j => ?_⟩ <;>
    rw [mem_primesIn_iff (by positivity)]
  · exact ⟨(walkLabels_mem D hW).1.1, (walkLabels_mem D hW).1.2⟩
  · exact ⟨(walkLabels_mem D hW).2.1, (walkLabels_mem D hW).2.2⟩

/-- **Walks are at most as numerous as label pairs.**  For a fixed starting vertex and a
property of the labels, the walks of the `q`-subgraph of length `ℓ` satisfying it are no more
numerous than the label pairs in `[P₁, 2P₁]^{2ℓ}` satisfying the same property. -/
lemma card_walk_le_labels (D : QuadData k f c C X L P₁ P₂) (hP : 0 < P₁) (hL : 0 < L)
    {q ℓ : ℕ} (x : GVert D) (P : ((Fin ℓ → ℕ) × (Fin ℓ → ℕ)) → Prop) [DecidablePred P] :
    ((walkSet D q ℓ).filter (fun W => W 0 = x ∧ P (walkLabels D ℓ W))).card ≤
      ((labelPairs P₁ ℓ).filter (fun p => P p)).card := by
  classical
  have hinj : Set.InjOn (walkLabels D ℓ)
      ↑((walkSet D q ℓ).filter (fun W => W 0 = x ∧ P (walkLabels D ℓ W))) := by
    intro W hW W' hW' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hW hW'
    refine walk_eq_of_labels D hP hL hW.1 hW'.1 ?_ heq
    rw [hW.2.1, hW'.2.1]
  calc ((walkSet D q ℓ).filter (fun W => W 0 = x ∧ P (walkLabels D ℓ W))).card
      = (((walkSet D q ℓ).filter (fun W => W 0 = x ∧ P (walkLabels D ℓ W))).image
          (walkLabels D ℓ)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((labelPairs P₁ ℓ).filter (fun p => P p)).card := by
        refine Finset.card_le_card ?_
        intro p hp
        rw [Finset.mem_image] at hp
        obtain ⟨W, hW, rfl⟩ := hp
        rw [Finset.mem_filter] at hW ⊢
        exact ⟨walkLabels_mem_labelPairs D hP hW.1, hW.2.2⟩


/-! ## Closed walks: cardinality bounds -/

/-- `closedWalkVal` is the set of walks of `walkSet` from the vertex `⟨x, hx⟩` back to it. -/
lemma closedWalkVal_eq_filter (D : QuadData k f c C X L P₁ P₂) (q ℓ : ℕ) {x : ℝ}
    (hx : x ∈ D.fam) :
    closedWalkVal D q ℓ x =
      (walkSet D q ℓ).filter (fun W => W 0 = (⟨x, hx⟩ : GVert D) ∧
        W ⟨ℓ, Nat.lt_succ_self ℓ⟩ = (⟨x, hx⟩ : GVert D)) := by
  ext W
  simp only [closedWalkVal, Finset.mem_filter]
  constructor
  · rintro ⟨hW, hclosed, hval⟩
    exact ⟨hW, Subtype.ext hval, Subtype.ext (by rw [← hclosed, hval])⟩
  · rintro ⟨hW, h0, hlast⟩
    exact ⟨hW, by rw [h0, hlast], by rw [h0]⟩

/-- The double filter defining `closedWalkVal` is the walk set of the `q`-subgraph. -/
lemma filter_walkSet_eq_pathSet (D : QuadData k f c C X L P₁ P₂) (q ℓ : ℕ) (y : GVert D) :
    (walkSet D q ℓ).filter (fun W => W 0 = y ∧ W ⟨ℓ, Nat.lt_succ_self ℓ⟩ = y)
      = pathSet (GAdjQ D q) ℓ y y := by
  ext W
  simp only [walkSet, pathSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The number of closed walks through a vertex is the corresponding diagonal entry of the
`ℓ`-th power of the adjacency matrix of the `q`-subgraph. -/
lemma card_closedWalkVal (D : QuadData k f c C X L P₁ P₂) (q ℓ : ℕ) {x : ℝ}
    (hx : x ∈ D.fam) :
    ((closedWalkVal D q ℓ x).card : ℝ) =
      ((Matrix.of (fun i j : GVert D => if GAdjQ D q i j then (1 : ℝ) else 0)) ^ ℓ)
        ⟨x, hx⟩ ⟨x, hx⟩ := by
  rw [closedWalkVal_eq_filter D q ℓ hx, filter_walkSet_eq_pathSet,
    ← walk_count_eq (GAdjQ D q) ℓ ⟨x, hx⟩ ⟨x, hx⟩]

/-- **Closed walks are at most as numerous as label pairs**, for any property of the labels. -/
lemma card_closedWalk_le_labels (D : QuadData k f c C X L P₁ P₂) (hP : 0 < P₁) (hL : 0 < L)
    {q ℓ : ℕ} (x : ℝ) (P : ((Fin ℓ → ℕ) × (Fin ℓ → ℕ)) → Prop) [DecidablePred P] :
    ((closedWalkVal D q ℓ x).filter (fun W => P (walkLabels D ℓ W))).card ≤
      ((labelPairs P₁ ℓ).filter (fun p => P p)).card := by
  classical
  have hinj : Set.InjOn (walkLabels D ℓ)
      ↑((closedWalkVal D q ℓ x).filter (fun W => P (walkLabels D ℓ W))) := by
    intro W hW W' hW' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hW hW'
    rw [closedWalkVal, Finset.mem_filter] at hW hW'
    refine walk_eq_of_labels D hP hL hW.1.1 hW'.1.1 ?_ heq
    apply Subtype.ext
    rw [hW.1.2.2, hW'.1.2.2]
  calc ((closedWalkVal D q ℓ x).filter (fun W => P (walkLabels D ℓ W))).card
      = (((closedWalkVal D q ℓ x).filter (fun W => P (walkLabels D ℓ W))).image
          (walkLabels D ℓ)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((labelPairs P₁ ℓ).filter (fun p => P p)).card := by
        refine Finset.card_le_card ?_
        intro p hp
        rw [Finset.mem_image] at hp
        obtain ⟨W, hW, rfl⟩ := hp
        rw [closedWalkVal, Finset.mem_filter] at hW
        rw [Finset.mem_filter] at hW ⊢
        exact ⟨walkLabels_mem_labelPairs D hP hW.1.1, hW.2⟩

end

end Work.BMF
