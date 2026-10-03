import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.DartGraph

/-!
# The darts of a combinatorial cycle leaving a vertex

For a `DartGraph.Cycle` `C` (a cyclic sequence `w` of period `L ≥ 3` whose first `L` terms are
pairwise distinct), the darts of `C.darts` starting at a vertex `a` are exactly the
*successor* darts `(w j, w (j+1))` and the *predecessor* darts `(w j, w (j+L-1))` taken at the
indices `j < L` with `w j = a`.  Both families are in bijection with that index set and are
mutually disjoint, so the number of darts leaving `a` is twice the number of visits of `a` —
in particular it is even (it is `0` if the cycle does not visit `a`).

The proof only uses the periodicity and the injectivity of the first `L` vertices; the graph
structure `G.D` plays no role.
-/

namespace Work.HornSC.CellBoundaryJordan

variable {α : Type*} [DecidableEq α]

namespace DartGraph

/-- Iterating the periodicity of a cycle. -/
lemma Cycle.w_iter {G : DartGraph α} (C : G.Cycle) : ∀ k r : ℕ, C.w (C.L * k + r) = C.w r := by
  intro k
  induction k with
  | zero => intro r; simp
  | succ k ih =>
    intro r
    have h : C.L * (k + 1) + r = C.L * k + (r + C.L) := by ring
    rw [h, ih (r + C.L), C.per r]

/-- `w` is determined by its argument modulo the cycle length. -/
lemma Cycle.w_mod {G : DartGraph α} (C : G.Cycle) (n : ℕ) : C.w (n % C.L) = C.w n := by
  conv_rhs => rw [← Nat.div_add_mod n C.L]
  rw [C.w_iter]

/-- The `predecessor` dart at `j`: the dart joining `w j` to the previous vertex `w (j+L-1)`. -/
lemma Cycle.prev_mem {G : DartGraph α} (C : G.Cycle) {j : ℕ} (hj : j < C.L) :
    (C.w j, C.w (j + C.L - 1)) ∈ C.darts := by
  have hL3 : 3 ≤ C.L := C.hL
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    have h1 : C.L - 1 + 1 = C.L := by omega
    simpa [Nat.zero_add, h1, C.w_period] using C.mem_darts_backward (show C.L - 1 < C.L by omega)
  · have hper : C.w (j + C.L - 1) = C.w (j - 1) := by
      have h : j + C.L - 1 = (j - 1) + C.L := by omega
      rw [h, C.per]
    simpa [hper, Nat.sub_add_cancel hpos] using
      C.mem_darts_backward (show j - 1 < C.L by omega)

/-- The darts of `C` that leave the vertex `a` are the successor and predecessor darts at the
indices where `C` visits `a`. -/
lemma Cycle.darts_filter_eq {G : DartGraph α} (C : G.Cycle) (a : α) :
    C.darts.filter (fun e => e.1 = a) =
      ((Finset.range C.L).filter (fun j => C.w j = a)).image (fun j => (C.w j, C.w (j + 1))) ∪
      ((Finset.range C.L).filter (fun j => C.w j = a)).image
        (fun j => (C.w j, C.w (j + C.L - 1))) := by
  have hL3 : 3 ≤ C.L := C.hL
  ext e
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨he, h1⟩
    rw [Cycle.darts, Finset.mem_union] at he
    rcases he with he | he
    · obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp he
      refine Or.inl ⟨j, ⟨Finset.mem_range.mp hj, ?_⟩, hje⟩
      rw [← hje] at h1
      simpa using h1
    · obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp he
      have hjLt : j < C.L := Finset.mem_range.mp hj
      have h1' : C.w (j + 1) = a := by
        rw [← hje] at h1
        simpa using h1
      by_cases hjL : j + 1 < C.L
      · refine Or.inr ⟨j + 1, ⟨hjL, h1'⟩, ?_⟩
        rw [show j + 1 + C.L - 1 = j + C.L by omega, C.per]
        exact hje
      · have hjL' : j + 1 = C.L := by omega
        refine Or.inr ⟨0, ⟨by omega, ?_⟩, ?_⟩
        · rw [← C.w_period, ← hjL']
          exact h1'
        · rw [show (C.w 0, C.w (0 + C.L - 1)) = (C.w C.L, C.w (C.L - 1)) from by
              rw [Nat.zero_add, ← C.w_period]]
          rw [show C.L - 1 = j by omega, ← hjL']
          exact hje
  · rintro (⟨j, ⟨hj, hwj⟩, hje⟩ | ⟨j, ⟨hj, hwj⟩, hje⟩)
    · refine ⟨?_, ?_⟩
      · rw [← hje]; exact C.mem_darts_forward hj
      · rw [← hje]; exact hwj
    · refine ⟨?_, ?_⟩
      · rw [← hje]; exact C.prev_mem hj
      · rw [← hje]; exact hwj

end DartGraph

/-- The number of darts of a `G.Cycle` that *leave* a given vertex is even (it is `0` if the
vertex is not on the cycle and `2` otherwise). -/
theorem darts_leaving_even {α : Type*} [DecidableEq α] {G : DartGraph α} (C : G.Cycle) (a : α) :
    Even ((C.darts.filter (fun e => e.1 = a)).card) := by
  have hL3 : 3 ≤ C.L := C.hL
  have hLpos : 0 < C.L := by omega
  -- the successor and predecessor darts at the same index are distinct
  have hdist : ∀ i, i < C.L → C.w (i + 1) ≠ C.w (i + C.L - 1) := by
    intro i hi h
    have hm : (i + 1) ≡ (i + C.L - 1) [MOD C.L] := by
      have h1 : C.w ((i + 1) % C.L) = C.w ((i + C.L - 1) % C.L) := by
        rw [C.w_mod (i + 1), C.w_mod (i + C.L - 1), h]
      exact C.inj _ _ (Nat.mod_lt _ hLpos) (Nat.mod_lt _ hLpos) h1
    have hm' : i + 1 ≡ i + (C.L - 1) [MOD C.L] := by
      rw [Nat.add_sub_assoc (by omega : 1 ≤ C.L)] at hm
      exact hm
    have h3 : 1 ≡ C.L - 1 [MOD C.L] :=
      Nat.ModEq.add_left_cancel (Nat.ModEq.refl i) hm'
    have h4 : 1 = C.L - 1 := by
      have h5 : 1 % C.L = (C.L - 1) % C.L := h3
      rw [Nat.mod_eq_of_lt (by omega : 1 < C.L),
        Nat.mod_eq_of_lt (by omega : C.L - 1 < C.L)] at h5
      exact h5
    omega
  have hinj1 : Set.InjOn (fun j => (C.w j, C.w (j + 1)))
      ↑((Finset.range C.L).filter (fun j => C.w j = a)) := by
    intro i hi j hj h
    have hiL : i < C.L := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).1
    have hjL : j < C.L := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).1
    exact C.inj i j hiL hjL (congrArg Prod.fst h)
  have hinj2 : Set.InjOn (fun j => (C.w j, C.w (j + C.L - 1)))
      ↑((Finset.range C.L).filter (fun j => C.w j = a)) := by
    intro i hi j hj h
    have hiL : i < C.L := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).1
    have hjL : j < C.L := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).1
    exact C.inj i j hiL hjL (congrArg Prod.fst h)
  have hdisj : Disjoint
      (((Finset.range C.L).filter (fun j => C.w j = a)).image (fun j => (C.w j, C.w (j + 1))))
      (((Finset.range C.L).filter (fun j => C.w j = a)).image
        (fun j => (C.w j, C.w (j + C.L - 1)))) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he1
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp he2
    have hiL : i < C.L := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hjL : j < C.L := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hwij : C.w i = C.w j := (congrArg Prod.fst hji).symm
    have hij : i = j := C.inj i j hiL hjL hwij
    rw [hij.symm] at hji
    exact hdist i hiL (congrArg Prod.snd hji).symm
  rw [C.darts_filter_eq a, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injOn hinj1, Finset.card_image_of_injOn hinj2]
  exact ⟨((Finset.range C.L).filter (fun j => C.w j = a)).card, rfl⟩

end Work.HornSC.CellBoundaryJordan
