import Mathlib
import Submission.Work.EQ.UnivCover.CountableSetup

set_option autoImplicit false
open _root_.Topology
open scoped Topology unitInterval
open Classical

namespace Work.EQ.UnivCover

variable {X : Type*} [TopologicalSpace X]

/-- **The point reached by a chain only depends on the path components of the intermediate
points.**  Two lists of moves with the same indices, whose points are related by paths inside the
relevant intersections `U n ∩ U m`, and with the same last move, give the same point of the
universal cover. -/
theorem chainPt_invariant {U : ℕ → Set X} {hU : DiscCover U}
    {x₀ : X} (e : UC x₀) {L L' : List (ℕ × X)} (hlen : L.length = L'.length)
    (hn : ∀ (i : ℕ) (hi : i < L.length), (L[i]).1 = (L'[i]'(by omega)).1)
    (hmem : ∀ p ∈ L, p.2 ∈ U p.1) (hmem' : ∀ p ∈ L', p.2 ∈ U p.1)
    (hj : ∀ (i : ℕ) (hi : i + 1 < L.length),
      JoinedIn (U (L[i]).1 ∩ U (L[i+1]).1) (L[i]).2 (L'[i]'(by omega)).2)
    (hlast : L.getLast? = L'.getLast?) :
    chainPt U hU L e = chainPt U hU L' e := by
  have key : ∀ i, i ≤ L.length - 1 →
      chainPt U hU (L'.take i ++ L.drop i) e = chainPt U hU L e := by
    intro i
    induction i with
    | zero =>
        intro _
        rw [List.take_zero, List.nil_append, List.drop_zero]
    | succ i ih =>
        intro hi
        have hi1 : i + 1 < L.length := by omega
        have hi0 : i ≤ L.length - 1 := by omega
        have htake : L'.take (i + 1) = L'.take i ++ [L'[i]'(by omega)] := by
          rw [← List.take_concat_get (by omega), List.concat_eq_append]
        have hdrop : L.drop (i + 1) = L[i+1] :: L.drop (i + 2) :=
          List.drop_eq_getElem_cons (by omega)
        have hdropi : L.drop i = L[i] :: L.drop (i + 1) :=
          List.drop_eq_getElem_cons (by omega)
        have hentry : L'[i]'(by omega) = ((L[i]).1, (L'[i]'(by omega)).2) := by
          show ((L'[i]'(by omega)).1, (L'[i]'(by omega)).2) = _
          rw [← hn i (by omega)]
        have hlist : L'.take (i+1) ++ L.drop (i+1)
            = L'.take i ++ [((L[i]).1, (L'[i]'(by omega)).2), L[i+1]] ++ L.drop (i+2) := by
          rw [htake, hdrop, hentry]
          simp only [List.append_assoc, List.cons_append, List.singleton_append,
            List.nil_append]
        rw [hlist]
        rw [← chainPt_swap (L'.take i) (L.drop (i + 2)) e (hj i hi1)
              (hmem L[i+1] (List.getElem_mem (by omega)))]
        have hback : L'.take i ++ [L[i], L[i+1]] ++ L.drop (i+2)
            = L'.take i ++ L.drop i := by
          rw [hdropi, hdrop]
          simp only [List.append_assoc, List.cons_append, List.singleton_append,
            List.nil_append]
        rw [hback]
        exact ih hi0
  rcases Nat.eq_zero_or_pos L.length with h0 | hpos
  · have hL : L = [] := List.length_eq_zero_iff.mp h0
    have hL' : L' = [] := List.length_eq_zero_iff.mp (by omega)
    rw [hL, hL']
  · cases hL : L.getLast? with
    | none =>
        exfalso
        have h1 : L.length = 0 := List.length_eq_zero_iff.mpr (List.getLast?_eq_none_iff.mp hL)
        omega
    | some a =>
        have hL'last : L'.getLast? = some a := by rw [← hlast, hL]
        obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hL
        obtain ⟨ys', hys'⟩ := List.getLast?_eq_some_iff.mp hL'last
        have hyslen : ys.length = L.length - 1 := by
          have h2 : L.length = ys.length + 1 := by
            rw [hys, List.length_append, List.length_singleton]
          omega
        have hys'len : ys'.length = L.length - 1 := by
          have h2 : L'.length = ys'.length + 1 := by
            rw [hys', List.length_append, List.length_singleton]
          omega
        have hN : L'.take (L.length - 1) ++ L.drop (L.length - 1) = L' := by
          rw [show L.drop (L.length - 1) = L.drop ys.length from by rw [hyslen],
              show L'.take (L.length - 1) = L'.take ys'.length from by rw [hys'len]]
          rw [hys', hys, List.take_left, List.drop_left]
        have hkey := key (L.length - 1) (by omega)
        rw [hN] at hkey
        exact hkey.symm

end Work.EQ.UnivCover
