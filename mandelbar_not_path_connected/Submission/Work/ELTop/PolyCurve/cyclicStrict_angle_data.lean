/-
# The angle data of a cyclically strictly ordered list of co-landing pairs

If the flattened list `ps.flatMap fun P => [P.a, P.b]` of the two angles of every pair of `ps`
is strictly cyclically ordered, then the angles of the pairs are interleaved exactly as the
cyclic order prescribes: inside a pair `a < b`, between consecutive pairs `b < a`, and
cyclically the last angle of the last pair is `< a₀ + 1`.

The proof is elementary list bookkeeping: the `2i`-th and `2i+1`-st entries of the flattened
list are the angles `a` and `b` of the `i`-th pair, so the `Pairwise` strict monotonicity of
the flattened list gives every incidence of the cyclic order.
-/
import Mathlib
import Submission.Work.ELTop.PolyCurve.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELTop.PolyCurve

section Helpers

variable {α β : Type*}

/-- The flattened list of the two entries of every element of a list has twice the length. -/
private theorem length_flatMap_pair (x y : α → β) (l : List α) :
    (l.flatMap fun a => [x a, y a]).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
      ring

/-- The `2i`-th entry of the flattened list of pairs is the first entry of the `i`-th pair. -/
private theorem get_flatMap_pair_fst (x y : α → β) (l : List α) (i : Fin l.length) :
    (l.flatMap fun a => [x a, y a]).get ⟨2 * i.val, by rw [length_flatMap_pair]; omega⟩
      = x (l.get i) := by
  induction l with
  | nil => exact i.elim0
  | cons a t ih =>
      rcases i with ⟨n, hn⟩
      cases n with
      | zero =>
        show (([x a, y a] : List β) ++ t.flatMap (fun a => [x a, y a])).get
          ⟨2 * (0 : ℕ), by simp⟩ = x ((a :: t).get ⟨0, hn⟩)
        rfl
      | succ k =>
        have hk : k < t.length := by rw [List.length_cons] at hn; omega
        show (([x a, y a] : List β) ++ t.flatMap (fun a => [x a, y a])).get
            ⟨2 * (k + 1), by
              simp only [List.length_append, List.length_cons, List.length_nil, length_flatMap_pair]
              rw [List.length_cons] at hn; omega⟩ =
          x ((a :: t).get ⟨k + 1, hn⟩)
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_right (show ([x a, y a] : List β).length ≤ 2 * (k + 1) by simp)]
        show (List.flatMap (fun a => [x a, y a]) t)[2 * k]'(by rw [length_flatMap_pair]; omega) =
          x ((a :: t)[k + 1]'hn)
        rw [List.getElem_cons_succ]
        simpa only [List.get_eq_getElem] using ih ⟨k, hk⟩

/-- The `(2i+1)`-st entry of the flattened list of pairs is the second entry of the `i`-th pair. -/
private theorem get_flatMap_pair_snd (x y : α → β) (l : List α) (i : Fin l.length) :
    (l.flatMap fun a => [x a, y a]).get ⟨2 * i.val + 1, by rw [length_flatMap_pair]; omega⟩
      = y (l.get i) := by
  induction l with
  | nil => exact i.elim0
  | cons a t ih =>
      rcases i with ⟨n, hn⟩
      cases n with
      | zero =>
        show (([x a, y a] : List β) ++ t.flatMap (fun a => [x a, y a])).get
          ⟨2 * (0 : ℕ) + 1, by simp⟩ = y ((a :: t).get ⟨0, hn⟩)
        rfl
      | succ k =>
        have hk : k < t.length := by rw [List.length_cons] at hn; omega
        show (([x a, y a] : List β) ++ t.flatMap (fun a => [x a, y a])).get
            ⟨2 * (k + 1) + 1, by
              simp only [List.length_append, List.length_cons, List.length_nil, length_flatMap_pair]
              rw [List.length_cons] at hn; omega⟩ =
          y ((a :: t).get ⟨k + 1, hn⟩)
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_right (show ([x a, y a] : List β).length ≤ 2 * (k + 1) + 1 by
          simp only [List.length_cons, List.length_nil]; omega)]
        show (List.flatMap (fun a => [x a, y a]) t)[2 * k + 1]'(by rw [length_flatMap_pair]; omega) =
          y ((a :: t)[k + 1]'hn)
        rw [List.getElem_cons_succ]
        simpa only [List.get_eq_getElem] using ih ⟨k, hk⟩

end Helpers

theorem cyclicStrict_angle_data {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (hpos : 0 < ps.length)
    (h : Work.EL.CyclicStrict (ps.flatMap fun P => [P.a, P.b])) :
    (∀ i : Fin ps.length, (ps.get i).a < (ps.get i).b) ∧
    (∀ i : Fin ps.length, ∀ hi : i.val + 1 < ps.length,
      (ps.get i).b < (ps.get ⟨i.val + 1, hi⟩).a) ∧
    (ps.get ⟨ps.length - 1, by omega⟩).b < (ps.get ⟨0, by omega⟩).a + 1 := by
  obtain ⟨hne, hpair, hhead⟩ := h
  have hlen : (ps.flatMap fun P => [P.a, P.b]).length = 2 * ps.length :=
    length_flatMap_pair (fun P : Work.EL.CoPair hN => P.a) (fun P => P.b) ps
  refine ⟨?_, ?_, ?_⟩
  · -- inside a pair: `a < b`
    intro i
    have ha : 2 * i.val < (ps.flatMap fun P => [P.a, P.b]).length := by rw [hlen]; omega
    have hb : 2 * i.val + 1 < (ps.flatMap fun P => [P.a, P.b]).length := by rw [hlen]; omega
    have hlt : (⟨2 * i.val, ha⟩ : Fin _) < (⟨2 * i.val + 1, hb⟩ : Fin _) := by simp
    have hres := List.Pairwise.rel_get_of_lt hpair hlt
    have h1 : (ps.flatMap fun P => [P.a, P.b]).get ⟨2 * i.val, ha⟩ = (ps.get i).a := by
      simpa using get_flatMap_pair_fst (fun P : Work.EL.CoPair hN => P.a) (fun P => P.b) ps i
    have h2 : (ps.flatMap fun P => [P.a, P.b]).get ⟨2 * i.val + 1, hb⟩ = (ps.get i).b := by
      simpa using get_flatMap_pair_snd (fun P : Work.EL.CoPair hN => P.a) (fun P => P.b) ps i
    rw [h1, h2] at hres
    exact hres
  · -- between consecutive pairs: `b_i < a_{i+1}`
    intro i hi
    have ha : 2 * i.val + 1 < (ps.flatMap fun P => [P.a, P.b]).length := by rw [hlen]; omega
    have hb : 2 * (i.val + 1) < (ps.flatMap fun P => [P.a, P.b]).length := by rw [hlen]; omega
    have hlt : (⟨2 * i.val + 1, ha⟩ : Fin _) < (⟨2 * (i.val + 1), hb⟩ : Fin _) := by simp; omega
    have hres := List.Pairwise.rel_get_of_lt hpair hlt
    have h1 : (ps.flatMap fun P => [P.a, P.b]).get ⟨2 * i.val + 1, ha⟩ = (ps.get i).b := by
      simpa using get_flatMap_pair_snd (fun P : Work.EL.CoPair hN => P.a) (fun P => P.b) ps i
    have h2 : (ps.flatMap fun P => [P.a, P.b]).get ⟨2 * (i.val + 1), hb⟩
        = (ps.get ⟨i.val + 1, hi⟩).a := by
      simpa using get_flatMap_pair_fst (fun P : Work.EL.CoPair hN => P.a) (fun P => P.b) ps
        ⟨i.val + 1, hi⟩
    rw [h1, h2] at hres
    exact hres
  · -- cyclically: `b_{m-1} < a_0 + 1`
    have hmem : (ps.get ⟨ps.length - 1, by omega⟩).b ∈ (ps.flatMap fun P => [P.a, P.b]) := by
      rw [List.mem_flatMap]
      exact ⟨ps.get ⟨ps.length - 1, by omega⟩, List.get_mem _ _, by simp⟩
    have hb := hhead _ hmem
    have hhead0 : (ps.flatMap fun P => [P.a, P.b]).headD 0 = (ps.get ⟨0, by omega⟩).a := by
      have hpsne : ps ≠ [] := by rintro rfl; simp at hpos
      obtain ⟨P, tl, rfl⟩ := List.exists_cons_of_ne_nil hpsne
      simp [List.flatMap_cons]
    rw [hhead0] at hb
    exact hb

end Work.ELTop.PolyCurve
