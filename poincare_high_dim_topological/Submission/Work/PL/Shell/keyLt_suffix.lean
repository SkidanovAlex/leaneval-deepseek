import Mathlib
import Submission.Work.PL.Shell.Basic

namespace Work.PL.Shell

variable {N : ℕ}

/-- Two lists have the same `i`-element prefix iff they agree pointwise strictly below `i`. -/
private lemma take_eq_take_iff_getElem? {α : Type*} (l₁ l₂ : List α) (i : ℕ) :
    l₁.take i = l₂.take i ↔ ∀ j, j < i → l₁[j]? = l₂[j]? := by
  constructor
  · intro h j hj
    rw [← List.getElem?_take_of_lt hj, h, List.getElem?_take_of_lt hj]
  · intro h
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take, List.getElem?_take]
    split_ifs with hj
    · exact h j hj
    · rfl

/-- Comparing two equal-length lists from the right (i.e. comparing their reverses
lexicographically from the left) is the same as: there is a position `i` such that everything
strictly to the right of `i` agrees, and at `i` the first list has a smaller entry. -/
private lemma keyLt_reverse_iff {α : Type*} [LT α] {U V : List α} (h : U.length = V.length) :
    keyLt U.reverse V.reverse ↔
      ∃ i, i < U.length ∧ (∀ j, i < j → j < U.length → U[j]? = V[j]?) ∧
        (∃ x y, U[i]? = some x ∧ V[i]? = some y ∧ x < y) := by
  rw [keyLt]
  constructor
  · rintro ⟨i, hi, htake, x, y, hx, hy, hlt⟩
    have hiU : i < U.length := by simpa using hi
    have hiV : i < V.length := by omega
    refine ⟨U.length - 1 - i, by omega, ?_, x, y, ?_, ?_, hlt⟩
    · intro k hk1 hk2
      have hji : U.length - 1 - k < i := by omega
      have h1 := (take_eq_take_iff_getElem? U.reverse V.reverse i).mp htake
        (U.length - 1 - k) hji
      have e1 : (U.reverse)[U.length - 1 - k]? = U[k]? := by
        rw [List.getElem?_reverse (by omega : U.length - 1 - k < U.length),
            show U.length - 1 - (U.length - 1 - k) = k by omega]
      have e2 : (V.reverse)[U.length - 1 - k]? = V[k]? := by
        rw [List.getElem?_reverse (by omega : U.length - 1 - k < V.length),
            show V.length - 1 - (U.length - 1 - k) = k by omega]
      rw [e1, e2] at h1
      exact h1
    · rw [List.getElem?_reverse hiU] at hx; exact hx
    · rw [List.getElem?_reverse hiV] at hy
      rw [h]
      exact hy
  · rintro ⟨m, hm, hsuf, x, y, hmx, hmy, hlt⟩
    refine ⟨U.length - 1 - m, by simp only [List.length_reverse]; omega, ?_, x, y, ?_, ?_, hlt⟩
    · rw [take_eq_take_iff_getElem?]
      intro j hj
      have hk1 : m < U.length - 1 - j := by omega
      have hk2 : U.length - 1 - j < U.length := by omega
      calc (U.reverse)[j]? = U[U.length - 1 - j]? := List.getElem?_reverse (by omega : j < U.length)
        _ = V[U.length - 1 - j]? := hsuf _ hk1 hk2
        _ = V[V.length - 1 - j]? := by rw [h]
        _ = (V.reverse)[j]? := (List.getElem?_reverse (by omega : j < V.length)).symm
    · rw [List.getElem?_reverse (by omega : U.length - 1 - m < U.length),
          show U.length - 1 - (U.length - 1 - m) = m by omega]
      exact hmx
    · rw [List.getElem?_reverse (by omega : U.length - 1 - m < V.length),
          show V.length - 1 - (U.length - 1 - m) = m by omega]
      exact hmy

theorem keyLt_suffix {vs : List (PL.E N)} {rk : PL.E N → ℕ} (hvs : vs.Nodup)
    (hrk : (vs.map rk).Pairwise (· < ·)) {l l' : List (PL.E N)}
    (hl : l.Perm vs) (hl' : l'.Perm vs) :
    Work.PL.Shell.keyLt (l'.reverse.map rk) (l.reverse.map rk) ↔
      ∃ i, i < l.length ∧ (∀ j, i < j → j < l.length → l'[j]? = l[j]?) ∧
        (∃ x y, l'[i]? = some x ∧ l[i]? = some y ∧ rk x < rk y) := by
  have hlen : l'.length = l.length := by rw [hl'.length_eq, hl.length_eq]
  have hnodup : (vs.map rk).Nodup := hrk.imp (fun hlt => ne_of_lt hlt)
  have hinj : ∀ x ∈ vs, ∀ y ∈ vs, rk x = rk y → x = y := by
    intro x hx y hy hxy
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨j, hj, hjy⟩ := List.mem_iff_getElem.mp hy
    have hix' : (vs.map rk)[i]? = some (rk x) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi, hix, Option.map_some]
    have hjy' : (vs.map rk)[j]? = some (rk y) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hj, hjy, Option.map_some]
    have hidx : i = j :=
      (List.Nodup.getElem?_inj (by simpa using hi) hnodup).mp (by rw [hix', hjy', hxy])
    have hsome : vs[i]? = vs[j]? := by rw [hidx]
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at hsome
    rw [hix, hjy] at hsome
    exact Option.some.inj hsome
  have hml : ∀ x ∈ l, x ∈ vs := fun x hx => (List.Perm.mem_iff hl).mp hx
  have hml' : ∀ x ∈ l', x ∈ vs := fun x hx => (List.Perm.mem_iff hl').mp hx
  have hG := keyLt_reverse_iff (U := l'.map rk) (V := l.map rk)
    (by rw [List.length_map, List.length_map, hlen])
  rw [List.map_reverse, List.map_reverse, hG]
  constructor
  · rintro ⟨i, hi, hsuf, hex⟩
    have hi' : i < l.length := by simp only [List.length_map] at hi; omega
    refine ⟨i, hi', ?_, ?_⟩
    · intro j hj1 hj2
      have hj' : j < l'.length := by omega
      have h := hsuf j hj1 (by simp only [List.length_map]; omega)
      rw [List.getElem?_map, List.getElem?_map,
          List.getElem?_eq_getElem hj', List.getElem?_eq_getElem hj2,
          Option.map_some, Option.map_some] at h
      have hrank : rk (l'[j]) = rk (l[j]) := Option.some.inj h
      have heq : l'[j] = l[j] :=
        hinj (l'[j]) (hml' (l'[j]) (List.getElem_mem hj')) (l[j])
          (hml (l[j]) (List.getElem_mem hj2)) hrank
      rw [List.getElem?_eq_getElem hj', List.getElem?_eq_getElem hj2, heq]
    · obtain ⟨x, y, hx, hy, hlt⟩ := hex
      have hx' : rk (l'[i]) = x := by
        rw [List.getElem?_map, List.getElem?_eq_getElem (by omega : i < l'.length),
            Option.map_some] at hx
        exact Option.some.inj hx
      have hy' : rk (l[i]) = y := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hi', Option.map_some] at hy
        exact Option.some.inj hy
      refine ⟨l'[i], l[i], List.getElem?_eq_getElem (by omega : i < l'.length),
        List.getElem?_eq_getElem hi', ?_⟩
      rw [hx', hy']
      exact hlt
  · rintro ⟨i, hi, hsuf, hex⟩
    refine ⟨i, by simp only [List.length_map]; omega, ?_, ?_⟩
    · intro j hj1 hj2
      have hj' : j < l.length := by simp only [List.length_map] at hj2; omega
      rw [List.getElem?_map, List.getElem?_map, hsuf j hj1 hj']
    · obtain ⟨x, y, hx, hy, hlt⟩ := hex
      exact ⟨rk x, rk y, by rw [List.getElem?_map, hx, Option.map_some],
        by rw [List.getElem?_map, hy, Option.map_some], hlt⟩

end Work.PL.Shell
