import Mathlib
import Submission.Work.Smooth.JordanSeparation.GridWalkDefs

namespace Work.Smooth.JordanSeparation

open Set

noncomputable section

/-! ## The geometric realization of a lattice walk -/

lemma walkGr_iUnion_fin_one (g : Fin 1 → Set ℂ) : (⋃ i : Fin 1, g i) = g 0 := by
  apply Set.Subset.antisymm
  · intro a ha
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
    rwa [Subsingleton.elim i 0] at hi
  · intro a ha
    exact Set.mem_iUnion.mpr ⟨0, ha⟩

lemma walkGr_succ_castSucc_eq {n : ℕ} (i : Fin n) : (i.succ).castSucc = (i.castSucc).succ := by
  ext; simp [Fin.val_succ]

lemma walkGr_iUnion_fin_castSucc_last {n : ℕ} (f : Fin (n+1) → Set ℂ) :
    (⋃ i : Fin (n+1), f i) = (⋃ i : Fin n, f (i.castSucc)) ∪ f (Fin.last n) := by
  apply Set.Subset.antisymm
  · intro a ha
    rw [Set.mem_iUnion] at ha
    obtain ⟨i, hi⟩ := ha
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Or.inl (Set.mem_iUnion.mpr ⟨j, hi⟩)
    · exact Or.inr hi
  · intro a ha
    rw [Set.mem_union, Set.mem_iUnion] at ha
    rcases ha with ⟨j, hj⟩ | hlast
    · exact Set.mem_iUnion.mpr ⟨j.castSucc, hj⟩
    · exact Set.mem_iUnion.mpr ⟨Fin.last n, hlast⟩

lemma walkGr_range_aux (c : ℝ) : ∀ m, ∀ v : Fin (m+2) → ℤ × ℤ,
    Set.range (walkPath c (m+1) v) =
      ⋃ i : Fin (m+1), segment ℝ (c * gpt (v (i.castSucc))) (c * gpt (v (i.succ))) := by
  intro m
  induction m with
  | zero =>
    intro v
    have h : walkPath c (0+1) v = (walkPath c 0 (fun i : Fin (0+1) => v i.castSucc)).trans
        (segPath (c * gpt (v (0 : Fin (0+1+1)))) (c * gpt (v (Fin.last (0+1))))) := rfl
    rw [h, Path.trans_range, segPath_range]
    rw [show walkPath c 0 (fun i : Fin (0+1) => v i.castSucc) = Path.refl (c * gpt (v 0)) from rfl]
    rw [show Set.range (Path.refl (c * gpt (v 0))) = {c * gpt (v 0)} from by simp]
    rw [walkGr_iUnion_fin_one]
    apply Set.Subset.antisymm
    · intro z hz
      rcases hz with hz | hz
      · rw [Set.mem_singleton_iff] at hz; rw [hz]; exact left_mem_segment ℝ _ _
      · exact hz
    · intro z hz; exact Or.inr hz
  | succ k ih =>
    intro v
    have htr : Set.range (walkPath c (k+1+1) v) =
        Set.range ((walkPath c (k+1) (fun i : Fin (k+1+1) => v i.castSucc)).trans
          (segPath (c * gpt (v (Fin.castSucc (Fin.last (k+1)))))
            (c * gpt (v (Fin.last (k+1+1)))))) := by
      rw [show walkPath c (k+1+1) v =
        (walkPath c (k+1) (fun i : Fin (k+1+1) => v i.castSucc)).trans
          (segPath (c * gpt (v (Fin.castSucc (Fin.last (k+1)))))
            (c * gpt (v (Fin.last (k+1+1))))) from rfl]
      rfl
    rw [htr, Path.trans_range, segPath_range, ih (fun i : Fin (k+1+1) => v i.castSucc)]
    conv_rhs => rw [walkGr_iUnion_fin_castSucc_last]
    congr 1

/-- **The range of the realization of a lattice walk is the union of its edges.** -/
theorem gridWalk_range (W : GridWalk) :
    Set.range (walkPath W.c W.n W.v) =
      ⋃ i : Fin W.n, segment ℝ (W.pt i.castSucc) (W.pt i.succ) := by
  obtain ⟨n, pos, c, cpos, v, step, closed⟩ := W
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp pos)
  rw [walkGr_range_aux c m v]
  rfl

lemma walkPath_eq_concat (c : ℝ) : ∀ n (v : Fin (n+1) → ℤ × ℤ),
    walkPath c n v = Path.concat (fun i => c * gpt (v i))
      (fun i => segPath (c * gpt (v i.castSucc)) (c * gpt (v i.succ))) := by
  intro n
  induction n with
  | zero =>
    intro v
    rw [Path.concat_zero]
    rfl
  | succ k ih =>
    intro v
    rw [show walkPath c (k+1) v =
        (walkPath c k (fun i : Fin (k+1) => v i.castSucc)).trans
          (segPath (c * gpt (v (Fin.castSucc (Fin.last k)))) (c * gpt (v (Fin.last (k+1))))) from rfl]
    rw [Path.concat_succ]
    rw [ih (fun i : Fin (k+1) => v i.castSucc)]
    rfl

/-- Vertex membership from membership of the whole realization. -/
lemma GridWalk.pt_mem {U : Set ℂ} (W : GridWalk) (hval : ∀ t, walkPath W.c W.n W.v t ∈ U)
    (k : Fin (W.n+1)) : W.pt k ∈ U := by
  have hmem : W.pt k ∈ (⋃ i : Fin W.n, segment ℝ (W.pt i.castSucc) (W.pt i.succ)) := by
    rcases Fin.eq_castSucc_or_eq_last k with ⟨m, rfl⟩ | hlast
    · exact Set.mem_iUnion.mpr ⟨m, left_mem_segment ℝ _ _⟩
    · rw [hlast]
      refine Set.mem_iUnion.mpr ⟨⟨0, W.pos⟩, ?_⟩
      have h := left_mem_segment ℝ (W.pt (⟨0, W.pos⟩ : Fin W.n).castSucc)
        (W.pt (⟨0, W.pos⟩ : Fin W.n).succ)
      have h2 : W.pt 0 = W.pt (Fin.last W.n) := W.pt_last_eq.symm
      simpa [h2] using h
  rw [← gridWalk_range] at hmem
  obtain ⟨t, ht⟩ := hmem
  rw [← ht]; exact hval t

/-- Membership of the edges from membership of the realization. -/
lemma GridWalk.segPath_mem {U : Set ℂ} (W : GridWalk) (hval : ∀ t, walkPath W.c W.n W.v t ∈ U)
    (k : Fin W.n) : ∀ s, segPath (W.pt k.castSucc) (W.pt k.succ) s ∈ U := by
  intro s
  have hsub : Set.range (segPath (W.pt k.castSucc) (W.pt k.succ)) ⊆
      (⋃ i : Fin W.n, segment ℝ (W.pt i.castSucc) (W.pt i.succ)) := by
    rw [segPath_range]
    exact Set.subset_iUnion (fun i : Fin W.n => segment ℝ (W.pt i.castSucc) (W.pt i.succ)) k
  have hmem : segPath (W.pt k.castSucc) (W.pt k.succ) s ∈
      (⋃ i : Fin W.n, segment ℝ (W.pt i.castSucc) (W.pt i.succ)) := hsub ⟨s, rfl⟩
  rw [← gridWalk_range] at hmem
  obtain ⟨t, ht⟩ := hmem
  rw [← ht]; exact hval t

end

end Work.Smooth.JordanSeparation

namespace Work.Smooth.JordanSeparation

open Set

noncomputable section

/-- The vertices of a lattice walk, as points of the open set `U`. -/
def GridWalk.vp (W : GridWalk) {U : Set ℂ} (hval : ∀ t, walkPath W.c W.n W.v t ∈ U) :
    Fin (W.n+1) → ↥U := fun k => ⟨W.pt k, W.pt_mem hval k⟩

/-- The edges of a lattice walk, as paths in the open set `U`. -/
def GridWalk.ve (W : GridWalk) {U : Set ℂ} (hval : ∀ t, walkPath W.c W.n W.v t ∈ U) :
    (k : Fin W.n) → Path ((W.vp hval) k.castSucc) ((W.vp hval) k.succ) :=
  fun k => Path.liftU (W.pt_mem hval k.castSucc) (W.pt_mem hval k.succ)
    (segPath (W.pt k.castSucc) (W.pt k.succ)) (W.segPath_mem hval k)

/-- **The realization of a lattice walk as a loop in `U`.** -/
def GridWalk.loopOf (W : GridWalk) {U : Set ℂ} (hval : ∀ t, walkPath W.c W.n W.v t ∈ U) :
    Path (W.vp hval 0) (W.vp hval 0) :=
  (Path.concat (W.vp hval) (W.ve hval)).cast rfl
    (Subtype.ext (by simp only [GridWalk.vp]; exact W.pt_last_eq.symm))

@[simp] lemma GridWalk.loopOf_apply (W : GridWalk) {U : Set ℂ}
    (hval : ∀ t, walkPath W.c W.n W.v t ∈ U) (t : unitInterval) :
    (W.loopOf hval) t = (Path.concat (W.vp hval) (W.ve hval)) t := rfl

end

end Work.Smooth.JordanSeparation
