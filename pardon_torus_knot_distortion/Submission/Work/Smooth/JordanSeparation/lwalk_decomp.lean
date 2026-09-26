import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_delloop

/-!
# Simple closed lattice walks and the arrangement of a walk into simple cycles

* `LWalk.IsSimple` — no non-trivial double point;
* `LWalk.IsSubEdges` — every edge of `C` is an edge of `W` (same mesh);
* `exists_double_of_not_simple`;
* `range_subset_of_isSubEdges` — the trace of a sub-walk is inside the trace of the walk;
* and the induction `nullhomotopic_of_simple_subcycles`: a closed lattice walk whose image lies in
  `U` and all of whose simple sub-cycles are null-homotopic is itself null-homotopic.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

namespace LWalk

variable {W : LWalk}

/-- A closed walk is *simple* when it has no non-trivial double point. -/
def IsSimple (W : LWalk) : Prop :=
  ∀ i j, i < j → j ≤ W.n → (i, j) ≠ (0, W.n) → W.v i ≠ W.v j

/-- Every edge of `C` is an edge of `W` (same mesh, and vertices matching a consecutive pair of
`W`, in either order). -/
def IsSubEdges (C W : LWalk) : Prop :=
  C.c = W.c ∧ (∃ m, m ≤ W.n ∧ C.v 0 = W.v m) ∧
    ∀ k, k < C.n → ∃ m, m < W.n ∧
      ((C.v k = W.v m ∧ C.v (k + 1) = W.v (m + 1)) ∨
       (C.v k = W.v (m + 1) ∧ C.v (k + 1) = W.v m))

theorem isSubEdges_refl (W : LWalk) : W.IsSubEdges W :=
  ⟨rfl, ⟨0, Nat.zero_le _, rfl⟩, fun k hk => ⟨k, hk, Or.inl ⟨rfl, rfl⟩⟩⟩

theorem IsSubEdges.trans {A B C : LWalk} (h1 : A.IsSubEdges B) (h2 : B.IsSubEdges C) :
    A.IsSubEdges C := by
  obtain ⟨hc1, ⟨m0, hm0, hv0⟩, e1⟩ := h1
  obtain ⟨hc2, ⟨m0', hm0', hv0'⟩, e2⟩ := h2
  refine ⟨hc1.trans hc2, ?_, ?_⟩
  · rcases lt_or_eq_of_le hm0 with h | h
    · obtain ⟨m1, hm1, hc⟩ := e2 m0 h
      rcases hc with ⟨ha, -⟩ | ⟨ha, -⟩
      · exact ⟨m1, le_of_lt hm1, hv0.trans ha⟩
      · exact ⟨m1 + 1, by omega, hv0.trans ha⟩
    · subst h
      exact ⟨m0', hm0', hv0.trans (B.closed.trans hv0')⟩
  · intro k hk
    obtain ⟨m, hm, hc⟩ := e1 k hk
    obtain ⟨m1, hm1, hc1'⟩ := e2 m hm
    rcases hc with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rcases hc1' with ⟨hc1a, hc1b⟩ | ⟨hc1a, hc1b⟩
      · exact ⟨m1, hm1, Or.inl ⟨ha.trans hc1a, hb.trans hc1b⟩⟩
      · exact ⟨m1, hm1, Or.inr ⟨ha.trans hc1a, hb.trans hc1b⟩⟩
    · rcases hc1' with ⟨hc1a, hc1b⟩ | ⟨hc1a, hc1b⟩
      · exact ⟨m1, hm1, Or.inr ⟨ha.trans hc1b, hb.trans hc1a⟩⟩
      · exact ⟨m1, hm1, Or.inl ⟨ha.trans hc1b, hb.trans hc1a⟩⟩

theorem exists_double_of_not_simple (W : LWalk) (h : ¬ W.IsSimple) :
    ∃ i j, i < j ∧ j ≤ W.n ∧ (i, j) ≠ (0, W.n) ∧ W.v i = W.v j := by
  classical
  unfold IsSimple at h
  push_neg at h
  exact h

theorem edge_range_subset (W : LWalk) {k : ℕ} (hk : k < W.n) :
    Set.range (W.edge k) ⊆ Set.range W.path := by
  intro z hz
  rw [range_path]
  exact Or.inl (Set.mem_iUnion₂.mpr ⟨k, hk, hz⟩)

theorem pt_mem_range (W : LWalk) {m : ℕ} (hm : m ≤ W.n) : W.pt m ∈ Set.range W.path := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · rw [range_path]
    exact Or.inr rfl
  · have h1 : m - 1 < W.n := by omega
    refine edge_range_subset W h1 ?_
    refine ⟨1, ?_⟩
    show W.edge (m - 1) 1 = W.pt m
    rw [Path.target]
    congr 1
    omega

theorem range_subset_of_isSubEdges {C W : LWalk} (h : C.IsSubEdges W) :
    Set.range C.path ⊆ Set.range W.path := by
  obtain ⟨hcc, ⟨m0, hm0, hv0⟩, e⟩ := h
  intro z hz
  rw [range_path] at hz ⊢
  rcases hz with hz | hz
  · obtain ⟨k, hk, hz⟩ := Set.mem_iUnion₂.mp hz
    obtain ⟨m, hm, hc⟩ := e k hk
    have hseg : Set.range (C.edge k) ⊆ Set.range (W.edge m) := by
      rcases hc with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have hpk : C.pt k = W.pt m := by
          show C.c * gpt (C.v k) = W.c * gpt (W.v m)
          rw [hcc, ha]
        have hpk1 : C.pt (k + 1) = W.pt (m + 1) := by
          show C.c * gpt (C.v (k + 1)) = W.c * gpt (W.v (m + 1))
          rw [hcc, hb]
        rw [LWalk.edge, LWalk.edge, segPath_range, segPath_range, hpk, hpk1]
      · have hpk : C.pt k = W.pt (m + 1) := by
          show C.c * gpt (C.v k) = W.c * gpt (W.v (m + 1))
          rw [hcc, ha]
        have hpk1 : C.pt (k + 1) = W.pt m := by
          show C.c * gpt (C.v (k + 1)) = W.c * gpt (W.v m)
          rw [hcc, hb]
        rw [LWalk.edge, LWalk.edge, segPath_range, segPath_range, hpk, hpk1,
          segment_symm]
    exact Or.inl (Set.mem_iUnion₂.mpr ⟨m, hm, hseg hz⟩)
  · rw [Set.mem_singleton_iff] at hz
    have hpt : C.pt 0 = W.pt m0 := by
      show C.c * gpt (C.v 0) = W.c * gpt (W.v m0)
      rw [hcc, hv0]
    rw [hz, hpt, ← range_path]
    exact pt_mem_range W hm0


theorem sub_isSubEdges (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) :
    (W.sub i j hij hj hcl).IsSubEdges W := by
  refine ⟨rfl, ⟨i, by omega, rfl⟩, ?_⟩
  intro k hk
  have hsub_n : (W.sub i j hij hj hcl).n = j - i := rfl
  have hk' : k < j - i := hsub_n ▸ hk
  refine ⟨i + k, by omega, Or.inl ⟨rfl, rfl⟩⟩

/-- Vertices of `W.del` are vertices of `W` whenever the corresponding `pt`-images agree. -/
theorem del_v_of_pt (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j)
    {k m : ℕ} (h : (W.del i j hij hj hcl).pt k = W.pt m) :
    (W.del i j hij hj hcl).v k = W.v m := by
  have h1 : (W.del i j hij hj hcl).c * gpt ((W.del i j hij hj hcl).v k) = W.c * gpt (W.v m) := h
  rw [show (W.del i j hij hj hcl).c = W.c from rfl] at h1
  have hc : (W.c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt W.cpos)
  exact gpt_injective (mul_left_cancel₀ hc h1)

theorem del_isSubEdges (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) :
    (W.del i j hij hj hcl).IsSubEdges W := by
  refine ⟨rfl, ⟨0, Nat.zero_le _, ?_⟩, ?_⟩
  · exact del_v_of_pt (W := W) i j hij hj hcl (del_pt_zero W i j hij hj hcl)
  · intro k hk
    by_cases hki : k < i
    · refine ⟨k, by omega, Or.inl ⟨?_, ?_⟩⟩
      · exact del_v_of_pt (W := W) i j hij hj hcl
          (del_pt_of_le W i j hij hj hcl (by omega : k ≤ i))
      · exact del_v_of_pt (W := W) i j hij hj hcl
          (del_pt_of_le W i j hij hj hcl (by omega : k + 1 ≤ i))
    · have hki' : i ≤ k := by omega
      obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hki'
      have hdel_n : (W.del i j hij hj hcl).n = i + (W.n - j) := rfl
      have hlk : i + l < i + (W.n - j) := hdel_n ▸ hk
      have hl : l < W.n - j := by omega
      refine ⟨j + l, by omega, Or.inl ⟨?_, ?_⟩⟩
      · rcases Nat.eq_zero_or_pos l with h | h
        · subst h
          rw [Nat.add_zero]
          exact del_v_of_pt (W := W) i j hij hj hcl (del_pt_at_cut W i j hij hj hcl)
        · exact del_v_of_pt (W := W) i j hij hj hcl (del_pt_of_ge W i j hij hj hcl h)
      · rcases Nat.eq_zero_or_pos l with h | h
        · subst h
          rw [Nat.add_zero, Nat.add_zero]
          exact del_v_of_pt (W := W) i j hij hj hcl (del_pt_of_ge_one W i j hij hj hcl)
        · exact del_v_of_pt (W := W) i j hij hj hcl (del_pt_of_ge_succ W i j hij hj hcl l)

theorem sub_range_subset (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) :
    Set.range (W.sub i j hij hj hcl).path ⊆ Set.range W.path :=
  range_subset_of_isSubEdges (sub_isSubEdges (W := W) i j hij hj hcl)

theorem del_range_subset (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) :
    Set.range (W.del i j hij hj hcl).path ⊆ Set.range W.path :=
  range_subset_of_isSubEdges (del_isSubEdges (W := W) i j hij hj hcl)

/-- **Arrangement of a closed lattice walk into simple cycles.**  If every *simple* closed
sub-walk of `W` (using only edges of `W`) with image in `U` is null-homotopic in `ℂ`, then so
is `W`.  (The final statement for loops in `↥U` is obtained from this one by lifting; see
`PLAN_GRID_CRUX.md`.) -/
theorem nullhomotopic_of_simple_subcycles : ∀ (n : ℕ) (W : LWalk), W.n = n → ∀ {U : Set ℂ},
    (∀ t, W.path t ∈ U) →
    (∀ (C : LWalk), C.IsSimple → C.IsSubEdges W →
      Path.Homotopic C.loop (Path.refl (C.pt 0))) →
    Path.Homotopic W.loop (Path.refl (W.pt 0)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hWn U hval hcyc
    by_cases hsimple : W.IsSimple
    · exact hcyc W hsimple (isSubEdges_refl W)
    · obtain ⟨i, j, hij, hj, hne, hcl⟩ := exists_double_of_not_simple W hsimple
      have hne' : i ≠ 0 ∨ j ≠ W.n := by
        by_contra h
        push_neg at h
        exact hne (by rw [h.1, h.2])
      have hsub_lt : j - i < n := by omega
      have hdel_lt : i + (W.n - j) < n := by
        have : i + (W.n - j) < W.n := by omega
        omega
      have hδ : Path.Homotopic (W.sub i j hij hj hcl).loop
          (Path.refl ((W.sub i j hij hj hcl).pt 0)) :=
        ih (j - i) hsub_lt (W.sub i j hij hj hcl) rfl
          (fun t => by
            obtain ⟨t', ht'⟩ := sub_range_subset (W := W) i j hij hj hcl ⟨t, rfl⟩
            rw [← ht']; exact hval t')
          (fun C hC hsub => hcyc C hC (hsub.trans (sub_isSubEdges (W := W) i j hij hj hcl)))
      have hdel : Path.Homotopic (W.del i j hij hj hcl).loop
          (Path.refl ((W.del i j hij hj hcl).pt 0)) :=
        ih (i + (W.n - j)) hdel_lt (W.del i j hij hj hcl) rfl
          (fun t => by
            obtain ⟨t', ht'⟩ := del_range_subset (W := W) i j hij hj hcl ⟨t, rfl⟩
            rw [← ht']; exact hval t')
          (fun C hC hsub => hcyc C hC (hsub.trans (del_isSubEdges (W := W) i j hij hj hcl)))
      exact nullhomotopic_of_sub_del W i j hij hj hcl hδ hdel

end LWalk

end

end Work.Smooth.JordanSeparation
