/-
# The angle data of an admissible ray polygon

If `ps` is an admissible list of co-landing pairs (its `2m` angles are strictly cyclically
ordered), then for every pair `P` of `ps` the angles satisfy `P.a < P.b < P.a + 1`.  In
particular the counterclockwise arc from `P.a` to `P.b` has length `< 1` and the fractional
part `arcLen P.a P.b = Int.fract (P.b - P.a)` is the plain difference `P.b - P.a`, hence
nonzero.

The only input is the strict cyclic ordering: the flattened list `ps.flatMap fun P => [P.a, P.b]`
is strictly increasing and its last element is `<` its head `+ 1`, so every element is
`< head + 1`, while the head is `≤` every element.
-/
import Mathlib
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELTop

/-- The head of a strictly increasing list of reals is `≤` each of its members. -/
theorem headD_zero_le_of_mem_of_pairwise_lt {l : List ℝ} (h : l.Pairwise (· < ·)) {x : ℝ}
    (hx : x ∈ l) : l.headD 0 ≤ x := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    rw [List.headD_cons]
    rcases List.mem_cons.mp hx with hxa | hxt
    · exact le_of_eq hxa.symm
    · exact le_of_lt ((List.pairwise_cons.mp h).1 x hxt)

theorem arcLen_ne_zero_of_polyAdmissible {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    {ps : List (Work.EL.CoPair hN)} (hA : Work.EL.PolyAdmissible ps) :
    ∀ P ∈ ps, P.a < P.b ∧ P.b < P.a + 1 ∧ Work.EL.arcLen P.a P.b = P.b - P.a := by
  intro P hP
  obtain ⟨hne, hpair, hhead⟩ := hA.cyc
  -- `P.a` and `P.b` are the two consecutive entries of the flattened list at the block of `P`
  obtain ⟨l₁, l₂, rfl⟩ := List.mem_iff_append.mp hP
  have hpair_raw : (l₁.flatMap (fun Q : Work.EL.CoPair hN => [Q.a, Q.b]) ++
      ([P.a, P.b] ++ l₂.flatMap (fun Q : Work.EL.CoPair hN => [Q.a, Q.b]))).Pairwise
      (· < ·) := by
    simpa only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] using hpair
  have hb_pair : ([P.a, P.b] ++ l₂.flatMap (fun Q : Work.EL.CoPair hN => [Q.a, Q.b])).Pairwise
      (· < ·) := (List.pairwise_append.mp hpair_raw).2.1
  -- inside the pair: `a < b`
  have hab : P.a < P.b :=
    (List.pairwise_cons.mp ((List.pairwise_append.mp hb_pair).1)).1 P.b (by simp)
  -- the flattened list, its strict monotonicity and the cyclic bound
  set m : List ℝ := (l₁ ++ P :: l₂).flatMap fun Q => [Q.a, Q.b] with hm
  have hpair' : m.Pairwise (· < ·) := by rw [hm]; exact hpair
  have hhead' : ∀ x ∈ m, x < m.headD 0 + 1 := by rw [hm]; exact hhead
  have hpa : P.a ∈ m := by
    rw [hm]
    exact List.mem_flatMap.mpr ⟨P, by simp, by simp⟩
  have hpb : P.b ∈ m := by
    rw [hm]
    exact List.mem_flatMap.mpr ⟨P, by simp, by simp⟩
  -- the head of the flattened list is `P₀.a ≤ P.a`, and `P.b < head + 1`
  have hle : m.headD 0 ≤ P.a := headD_zero_le_of_mem_of_pairwise_lt hpair' hpa
  have hb_lt : P.b < P.a + 1 := lt_of_lt_of_le (hhead' P.b hpb) (by linarith)
  refine ⟨hab, hb_lt, ?_⟩
  rw [Work.EL.arcLen, Int.fract_eq_self]
  exact ⟨by linarith, by linarith⟩

end Work.ELTop
