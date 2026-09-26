import Mathlib
import Submission.Work.Smooth.JordanSeparation.GridWalkDefs
import Submission.Work.Smooth.JordanSeparation.plApprox
import Submission.Work.Smooth.JordanSeparation.plWalk

/-!
# Closed lattice walks as total vertex functions

`LWalk` is a closed walk on the lattice `ℤ × ℤ` with mesh `c > 0`, given as a *total* vertex
function `ℕ → ℤ × ℤ` together with a length `n`.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-- A closed walk on the lattice `ℤ × ℤ` scaled by `c`: `n` unit steps, `v 0, …, v n` with
`v n = v 0`. -/
structure LWalk where
  /-- number of edges -/
  n : ℕ
  /-- the mesh -/
  c : ℝ
  /-- the mesh is positive -/
  cpos : 0 < c
  /-- the vertices -/
  v : ℕ → ℤ × ℤ
  /-- successive vertices are lattice neighbours -/
  step : ∀ k < n, GridStep (v k) (v (k + 1))
  /-- the walk is closed -/
  closed : v n = v 0

namespace LWalk

/-- The `k`-th vertex as a point of `ℂ`. -/
@[reducible] def pt (W : LWalk) (k : ℕ) : ℂ := W.c * gpt (W.v k)

/-- The `k`-th edge of the walk. -/
@[reducible] def edge (W : LWalk) (k : ℕ) : Path (W.pt k) (W.pt (k + 1)) := segPath (W.pt k) (W.pt (k + 1))

theorem pt_last (W : LWalk) : W.pt W.n = W.pt 0 := by
  show W.c * gpt (W.v W.n) = W.c * gpt (W.v 0)
  rw [W.closed]

/-- The realization of the walk, from the first to the (last) vertex. -/
def path (W : LWalk) : Path (W.pt 0) (W.pt W.n) :=
  joinNat (p := W.pt) (fun k => W.edge k) W.n

/-- The realization of the walk as a loop. -/
def loop (W : LWalk) : Path (W.pt 0) (W.pt 0) := W.path.cast rfl W.pt_last.symm

@[simp] theorem pt_zero (W : LWalk) : W.pt 0 = W.c * gpt (W.v 0) := rfl

theorem range_joinNat {p : ℕ → ℂ} (F : ∀ k, Path (p k) (p (k + 1))) (j : ℕ) :
    Set.range (joinNat F j) = (⋃ k, ⋃ (_ : k < j), Set.range (F k)) ∪ {p 0} := by
  induction j with
  | zero =>
    have h0 : (⋃ k, ⋃ (_ : k < 0), Set.range (F k)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hlt, -⟩ := Set.mem_iUnion.mp hk
      exact Nat.not_lt_zero k hlt
    have hrefl : Set.range (Path.refl (p 0)) = {p 0} := by
      have hc : (Path.refl (p 0) : unitInterval → ℂ) = fun _ => p 0 := rfl
      rw [hc]
      exact Set.range_const
    rw [h0, Set.empty_union, show joinNat F 0 = Path.refl (p 0) from rfl, hrefl]
  | succ i ih =>
    rw [show joinNat F (i + 1) = (joinNat F i).trans (F i) from rfl, Path.trans_range, ih]
    have hsplit : (⋃ k, ⋃ (_ : k < i + 1), Set.range (F k))
        = (⋃ k, ⋃ (_ : k < i), Set.range (F k)) ∪ Set.range (F i) := by
      ext z
      constructor
      · intro hz
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
        obtain ⟨hlt, hz'⟩ := Set.mem_iUnion.mp hk
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with h | h
        · exact Or.inl (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨h, hz'⟩⟩)
        · subst h; exact Or.inr hz'
      · rintro (hz | hz)
        · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
          obtain ⟨hlt, hz'⟩ := Set.mem_iUnion.mp hk
          exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨Nat.lt_succ_of_lt hlt, hz'⟩⟩
        · exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Nat.lt_succ_self i, hz⟩⟩
    rw [hsplit]
    ext z
    simp only [Set.mem_union]
    tauto

theorem range_path (W : LWalk) :
    Set.range W.path = (⋃ k, ⋃ (_ : k < W.n), Set.range (W.edge k)) ∪ {W.pt 0} :=
  range_joinNat (p := W.pt) (fun k => W.edge k) W.n

theorem range_edge_subset {W : LWalk} {U : Set ℂ} (hval : ∀ t, W.path t ∈ U) {k : ℕ}
    (hk : k < W.n) : Set.range (W.edge k) ⊆ U := by
  intro z hz
  have hmem : z ∈ Set.range W.path := by
    rw [range_path]
    exact Or.inl (Set.mem_iUnion₂.mpr ⟨k, hk, hz⟩)
  obtain ⟨t, ht⟩ := hmem
  rw [← ht]; exact hval t

theorem pt_mem {W : LWalk} {U : Set ℂ} (hval : ∀ t, W.path t ∈ U) {k : ℕ} (hk : k ≤ W.n) :
    W.pt k ∈ U := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · have hmem : W.pt 0 ∈ Set.range W.path := by
      rw [range_path]; exact Or.inr rfl
    obtain ⟨t, ht⟩ := hmem
    rw [← ht]; exact hval t
  · have hkit : k - 1 < W.n := by omega
    refine range_edge_subset hval hkit ?_
    refine ⟨1, ?_⟩
    show W.edge (k - 1) 1 = W.pt k
    rw [Path.target]
    congr 1
    omega

theorem edge_mem {W : LWalk} {U : Set ℂ} (hval : ∀ t, W.path t ∈ U) {k : ℕ} (hk : k < W.n) :
    ∀ s, W.edge k s ∈ U :=
  fun s => range_edge_subset hval hk ⟨s, rfl⟩


/-- The realization of a lattice walk as a loop in the subtype `↥U`, given that it stays in `U`. -/
def loopIn (W : LWalk) {U : Set ℂ} (hbase : W.pt 0 ∈ U) (hval : ∀ t, W.path t ∈ U) :
    Path (⟨W.pt 0, hbase⟩ : ↥U) (⟨W.pt 0, hbase⟩ : ↥U) :=
  Path.cast (Path.liftU hbase (by rw [W.pt_last]; exact hbase) W.path hval) rfl
    (Subtype.ext W.pt_last.symm)

end LWalk

end

end Work.Smooth.JordanSeparation
