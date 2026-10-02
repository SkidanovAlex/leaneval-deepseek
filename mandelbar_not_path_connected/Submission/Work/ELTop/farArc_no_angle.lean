/-
# No angle of a ray polygon lies in the open far arc of one of its pairs

Let `ps` be an admissible ray polygon, i.e. a nonempty list of co-landing pairs whose `2m`
angles, flattened as `ps.flatMap (fun P => [P.a, P.b])`, are strictly cyclically ordered:
strictly increasing as a list and lying in `[a₀, a₀ + 1)` where `a₀` is the first of them.

If a real number `x` lies strictly between the two angles `a_l, b_l` of the `l`-th pair
(*linearly*, not merely cyclically), then `x` is congruent modulo `ℤ` to none of the `2m`
angles of the polygon: for every pair `P ∈ ps` and every `k : ℤ` one has `x ≠ P.a + k` and
`x ≠ P.b + k`.

The reason is purely arithmetic.  Writing `ang := ps.flatMap (fun P => [P.a, P.b])`, the entry
at position `2i` of `ang` is `(ps.get i).a` and the entry at position `2i+1` is `(ps.get i).b`,
so the strict monotonicity of `ang` gives

* every entry of `ang` lies in `[ang.headD 0, ang.headD 0 + 1)` — the lower bound from
  monotonicity, the upper bound directly from `CyclicStrict`;
* no entry of `ang` equals `x`: the entries before position `2l` are `< a_l < x` and the
  entries after position `2l+1` are `> b_l > x`.

Since `a_l < x < b_l` with `a_l, b_l ∈ ang`, also `ang.headD 0 < x < ang.headD 0 + 1`.  Hence
for every entry `θ` of `ang` the difference `x - θ` lies in the open interval `(-1, 1)` of
length `2`; an integer lying there must be `0`, which is excluded because `x ≠ θ`.

This is the purely angular ingredient in the description of the *far* arcs of a ray polygon.
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

section Helpers

variable {α : Type*}

/-- The flattened list of the two entries of every element of a list has twice the length. -/
private theorem length_flatMap_pair (x y : α → ℝ) (l : List α) :
    (l.flatMap fun a => [x a, y a]).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
      ring

/-- The `2i`-th entry of the flattened list of pairs is the first entry of the `i`-th pair. -/
private theorem get_flatMap_pair_fst (x y : α → ℝ) (l : List α) (i : Fin l.length) :
    (l.flatMap fun a => [x a, y a]).get ⟨2 * i.val, by rw [length_flatMap_pair]; omega⟩
      = x (l.get i) := by
  induction l with
  | nil => exact i.elim0
  | cons a t ih =>
      rcases i with ⟨n, hn⟩
      cases n with
      | zero =>
        show (([x a, y a] : List ℝ) ++ t.flatMap (fun a => [x a, y a])).get
          ⟨2 * (0 : ℕ), by simp⟩ = x ((a :: t).get ⟨0, hn⟩)
        rfl
      | succ k =>
        have hk : k < t.length := by rw [List.length_cons] at hn; omega
        show (([x a, y a] : List ℝ) ++ t.flatMap (fun a => [x a, y a])).get
            ⟨2 * (k + 1), by
              simp only [List.length_append, List.length_cons, List.length_nil, length_flatMap_pair]
              rw [List.length_cons] at hn; omega⟩ =
          x ((a :: t).get ⟨k + 1, hn⟩)
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_right (show ([x a, y a] : List ℝ).length ≤ 2 * (k + 1) by simp)]
        show (List.flatMap (fun a => [x a, y a]) t)[2 * k]'(by rw [length_flatMap_pair]; omega) =
          x ((a :: t)[k + 1]'hn)
        rw [List.getElem_cons_succ]
        simpa only [List.get_eq_getElem] using ih ⟨k, hk⟩

/-- The `(2i+1)`-st entry of the flattened list of pairs is the second entry of the `i`-th
pair. -/
private theorem get_flatMap_pair_snd (x y : α → ℝ) (l : List α) (i : Fin l.length) :
    (l.flatMap fun a => [x a, y a]).get ⟨2 * i.val + 1, by rw [length_flatMap_pair]; omega⟩
      = y (l.get i) := by
  induction l with
  | nil => exact i.elim0
  | cons a t ih =>
      rcases i with ⟨n, hn⟩
      cases n with
      | zero =>
        show (([x a, y a] : List ℝ) ++ t.flatMap (fun a => [x a, y a])).get
          ⟨2 * (0 : ℕ) + 1, by simp⟩ = y ((a :: t).get ⟨0, hn⟩)
        rfl
      | succ k =>
        have hk : k < t.length := by rw [List.length_cons] at hn; omega
        show (([x a, y a] : List ℝ) ++ t.flatMap (fun a => [x a, y a])).get
            ⟨2 * (k + 1) + 1, by
              simp only [List.length_append, List.length_cons, List.length_nil, length_flatMap_pair]
              rw [List.length_cons] at hn; omega⟩ =
          y ((a :: t).get ⟨k + 1, hn⟩)
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_right (show ([x a, y a] : List ℝ).length ≤ 2 * (k + 1) + 1 by
          simp only [List.length_cons, List.length_nil]; omega)]
        show (List.flatMap (fun a => [x a, y a]) t)[2 * k + 1]'(by rw [length_flatMap_pair]; omega) =
          y ((a :: t)[k + 1]'hn)
        rw [List.getElem_cons_succ]
        simpa only [List.get_eq_getElem] using ih ⟨k, hk⟩

/-- In a strictly increasing flattened angle list, the head is the least entry. -/
private theorem flatMap_headD_le {x y : α → ℝ} {l : List α}
    (hpair : (l.flatMap fun a => [x a, y a]).Pairwise (· < ·)) (hne : l ≠ []) {θ : ℝ}
    (hθ : θ ∈ l.flatMap fun a => [x a, y a]) :
    (l.flatMap fun a => [x a, y a]).headD 0 ≤ θ := by
  obtain ⟨P, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
  have h : (x P :: y P :: tl.flatMap (fun a => [x a, y a])).Pairwise (· < ·) := by
    simpa only [List.flatMap_cons, List.cons_append, List.nil_append] using hpair
  have hhead : (List.flatMap (fun a => [x a, y a]) (P :: tl)).headD 0 = x P := by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.headD_cons]
  rw [hhead]
  rcases List.mem_cons.mp hθ with h1 | h1
  · exact le_of_eq h1.symm
  · exact le_of_lt (List.rel_of_pairwise_cons h h1)

/-- If `z` lies strictly between the two entries of the `i`-th pair, then no entry of the
strictly increasing flattened angle list equals `z`. -/
private theorem flatMap_get_ne_of_between {x y : α → ℝ} {l : List α}
    (hpair : (l.flatMap fun a => [x a, y a]).Pairwise (· < ·)) (i : Fin l.length) {z : ℝ}
    (ha : x (l.get i) < z) (hb : z < y (l.get i)) :
    ∀ j : Fin (l.flatMap fun a => [x a, y a]).length,
      (l.flatMap fun a => [x a, y a]).get j ≠ z := by
  intro j hx
  have hlen : (l.flatMap fun a => [x a, y a]).length = 2 * l.length := length_flatMap_pair x y l
  have h2i : 2 * i.val < (l.flatMap fun a => [x a, y a]).length := by rw [hlen]; omega
  have h2i1 : 2 * i.val + 1 < (l.flatMap fun a => [x a, y a]).length := by rw [hlen]; omega
  have hgeti : (l.flatMap fun a => [x a, y a]).get ⟨2 * i.val, h2i⟩ = x (l.get i) :=
    get_flatMap_pair_fst x y l i
  have hgeti1 : (l.flatMap fun a => [x a, y a]).get ⟨2 * i.val + 1, h2i1⟩ = y (l.get i) :=
    get_flatMap_pair_snd x y l i
  have hmono : ∀ {j j' : Fin (l.flatMap fun a => [x a, y a]).length}, j ≤ j' →
      (l.flatMap fun a => [x a, y a]).get j ≤ (l.flatMap fun a => [x a, y a]).get j' := by
    intro j j' hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact le_of_lt (List.Pairwise.rel_get_of_lt hpair hlt)
    · exact le_of_eq (by rw [heq])
  rcases le_or_gt j.val (2 * i.val) with hj | hj
  · have hle : j ≤ (⟨2 * i.val, h2i⟩ : Fin _) := by rw [Fin.le_def]; exact hj
    have hthis := hmono hle
    rw [hx] at hthis
    linarith
  · have hle : (⟨2 * i.val + 1, h2i1⟩ : Fin _) ≤ j := by
      rw [Fin.le_def]
      show 2 * i.val + 1 ≤ j.val
      omega
    have hthis := hmono hle
    rw [hgeti1] at hthis
    rw [hx] at hthis
    linarith

end Helpers

theorem farArc_no_angle {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps) :
    ∀ (l : Fin ps.length) (x : ℝ), (ps.get l).a < x → x < (ps.get l).b →
      ∀ (P : Work.EL.CoPair hN), P ∈ ps → ∀ k : ℤ, x ≠ P.a + k ∧ x ≠ P.b + k := by
  intro l x ha hb P hP k
  have hpair : (ps.flatMap (fun P => [P.a, P.b])).Pairwise (· < ·) := hA.cyc.2.1
  have hhead : ∀ θ ∈ ps.flatMap (fun P => [P.a, P.b]),
      θ < (ps.flatMap (fun P => [P.a, P.b])).headD 0 + 1 := hA.cyc.2.2
  have hpsne : ps ≠ [] := by
    rintro rfl
    exact hA.cyc.1 (by simp)
  have ha_mem : (ps.get l).a ∈ ps.flatMap (fun P => [P.a, P.b]) :=
    List.mem_flatMap.mpr ⟨ps.get l, List.get_mem ps l, by simp⟩
  have hb_mem : (ps.get l).b ∈ ps.flatMap (fun P => [P.a, P.b]) :=
    List.mem_flatMap.mpr ⟨ps.get l, List.get_mem ps l, by simp⟩
  -- no angle of the polygon equals `x`
  have hne_x : ∀ θ ∈ ps.flatMap (fun P => [P.a, P.b]), θ ≠ x := by
    intro θ hθ
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hθ
    rw [← hj]
    exact flatMap_get_ne_of_between hpair l ha hb j
  -- and hence no integer translate of an angle equals `x`
  have hcong : ∀ θ ∈ ps.flatMap (fun P => [P.a, P.b]), ∀ k : ℤ, x ≠ θ + k := by
    intro θ hθ k hk
    have h1 : (ps.flatMap (fun P => [P.a, P.b])).headD 0 ≤ θ :=
      flatMap_headD_le hpair hpsne hθ
    have h2 : θ < (ps.flatMap (fun P => [P.a, P.b])).headD 0 + 1 := hhead θ hθ
    have h3 : (ps.flatMap (fun P => [P.a, P.b])).headD 0 < x :=
      lt_of_le_of_lt (flatMap_headD_le hpair hpsne ha_mem) ha
    have h4 : x < (ps.flatMap (fun P => [P.a, P.b])).headD 0 + 1 :=
      lt_trans hb (hhead (ps.get l).b hb_mem)
    have hneθ : θ ≠ x := hne_x θ hθ
    have hk' : (k : ℝ) = x - θ := by linarith
    have hkl : (-1 : ℝ) < (k : ℝ) := by linarith
    have hkr : (k : ℝ) < 1 := by linarith
    have hkl' : (-1 : ℤ) < k := by exact_mod_cast hkl
    have hkr' : k < (1 : ℤ) := by exact_mod_cast hkr
    have hk0 : k = 0 := by omega
    rw [hk0] at hk
    push_cast at hk
    exact hneθ (by linarith)
  exact ⟨hcong P.a (List.mem_flatMap.mpr ⟨P, hP, by simp⟩) k,
         hcong P.b (List.mem_flatMap.mpr ⟨P, hP, by simp⟩) k⟩

end Work.ELTop
