import Mathlib
import Submission.Work.Peluse.SwapC.agreeExistsMemChildren
import Submission.Work.Peluse.SwapC.coversSplit
import Submission.Work.Peluse.SwapC.pairDisjSplit
import Submission.Work.Peluse.SwapC.isSubdivIffCoversPairDisj
import Submission.Work.Peluse.SwapC.prefixOfFind
import Submission.Work.Peluse.SwapC.csplitFirstEqOfForall
import Submission.Work.Peluse.SwapC.refineEqOfNodupAppend
import Submission.Work.Peluse.SwapC.cellSumSplit
import Submission.Work.Peluse.SwapC.hasSplitIffLengthLt
import Submission.Work.Peluse.SwapC.depEqOfCellSumEqCard

namespace Work.Peluse.SwapC

variable {s : ℕ}

/-! ## A few elementary list facts (the rest of the bookkeeping is in the imported modules) -/

private lemma covers_singleton {l : CLeaf s} (h : l.dep = 0) : Covers [l] :=
  fun _ => ⟨l, List.mem_singleton.mpr rfl, fun _ hi => by rw [h] at hi; omega⟩

private lemma pairDisj_singleton (l : CLeaf s) : PairDisj [l] := by
  intro l₁ h₁ l₂ h₂ _
  rw [List.mem_singleton] at h₁ h₂
  rw [h₁, h₂]

/-- The first splittable leaf comes with a prefix of non-splittable leaves. -/
private lemma exists_prefix_all_not_split {Λ : List (CLeaf s)}
    (h : ¬ ∀ a ∈ Λ, ¬ a.dep < s) :
    ∃ P m Q, Λ = P ++ m :: Q ∧ (∀ a ∈ P, ¬ a.dep < s) ∧ m.dep < s := by
  induction Λ with
  | nil => exact absurd (fun a ha => absurd ha (by simp)) h
  | cons a t ih =>
    by_cases ha : a.dep < s
    · exact ⟨[], a, t, rfl, by simp, ha⟩
    · have ht : ¬ ∀ b ∈ t, ¬ b.dep < s := by
        intro hcon
        exact h (fun b hb => by
          rcases List.mem_cons.mp hb with rfl | hb'
          · exact ha
          · exact hcon b hb')
      obtain ⟨P, m, Q, hΛ, hP, hm⟩ := ih ht
      exact ⟨a :: P, m, Q, by rw [hΛ, List.cons_append], (fun b hb => by
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact ha
        · exact hP b hb'), hm⟩

/-- If a list has a splittable leaf, then splitting the first one gives exactly the decomposition
`P ++ children ++ Q`. -/
private lemma exists_split_decomp {Λ : List (CLeaf s)} (h : HasSplit Λ) :
    ∃ (P : List (CLeaf s)) (m : CLeaf s) (Q : List (CLeaf s)) (hm : m.dep < s),
      Λ = P ++ m :: Q ∧ (∀ a ∈ P, ¬ a.dep < s) ∧
        csplitFirst Λ = P ++ m.children hm ++ Q := by
  have h' : ¬ ∀ a ∈ Λ, ¬ a.dep < s := by
    rintro hcon
    obtain ⟨l, hl, hlt⟩ := h
    exact hcon l hl hlt
  obtain ⟨P, m, Q, hΛ, hP, hm⟩ := exists_prefix_all_not_split h'
  exact ⟨P, m, Q, hm, hΛ, hP, by rw [hΛ]; exact csplitFirstEqOfForall hP hm⟩

private lemma csplitFirst_eq_self_of_not_hasSplit {Λ : List (CLeaf s)} (h : ¬ HasSplit Λ) :
    csplitFirst Λ = Λ := by
  induction Λ with
  | nil => rfl
  | cons a t ih =>
    have ha : ¬ a.dep < s := fun hlt => h ⟨a, List.mem_cons_self .., hlt⟩
    have ht : ¬ HasSplit t := fun hcon =>
      h (by obtain ⟨b, hb, hlt⟩ := hcon; exact ⟨b, List.mem_cons_of_mem a hb, hlt⟩)
    rw [csplitFirst, dif_neg ha, ih ht]

private lemma csplitFirst_length_of_hasSplit {Λ : List (CLeaf s)} (h : HasSplit Λ) :
    (csplitFirst Λ).length = Λ.length + 1 := by
  induction Λ with
  | nil => exact absurd h (by rintro ⟨l, hl, _⟩; exact absurd hl (by simp))
  | cons a t ih =>
    by_cases ha : a.dep < s
    · rw [csplitFirst, dif_pos ha, List.length_append, List.length_cons]
      have hc : (a.children ha).length = 2 := rfl
      omega
    · rw [csplitFirst, dif_neg ha, List.length_cons]
      have ht : HasSplit t := by
        obtain ⟨l, hl, hlt⟩ := h
        rcases List.mem_cons.mp hl with rfl | hl'
        · exact absurd hlt ha
        · exact ⟨l, hl', hlt⟩
      rw [ih ht, List.length_cons]

private lemma cellSum_cons (l : CLeaf s) (Λ : List (CLeaf s)) :
    cellSum (l :: Λ) = 2 ^ (s - l.dep) + cellSum Λ := by
  simp [cellSum]

private lemma cellSum_length_le {Λ : List (CLeaf s)} : Λ.length ≤ cellSum Λ := by
  induction Λ with
  | nil => simp [cellSum]
  | cons l t ih =>
    rw [cellSum_cons, List.length_cons]
    have h1 : 1 ≤ 2 ^ (s - l.dep) := Nat.one_le_two_pow
    omega

private lemma cellSum_eq_length_of_all_dep {Λ : List (CLeaf s)} (h : ∀ l ∈ Λ, l.dep = s) :
    cellSum Λ = Λ.length := by
  induction Λ with
  | nil => simp [cellSum]
  | cons l t ih =>
    rw [cellSum_cons, List.length_cons,
      ih (fun a ha => h a (List.mem_cons_of_mem l ha)),
      h l (List.mem_cons_self ..)]
    rw [Nat.sub_self, pow_zero]
    omega

private lemma length_le_sum_of_one_le {u : List ℕ} (h : ∀ x ∈ u, 1 ≤ x) : u.length ≤ u.sum := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, List.sum_cons]
    have h1 : 1 ≤ a := h a (List.mem_cons_self ..)
    have h2 : t.length ≤ t.sum := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    omega

private lemma eq_one_of_sum_eq_length {u : List ℕ} (h : ∀ x ∈ u, 1 ≤ x) (hs : u.sum = u.length) :
    ∀ x ∈ u, x = 1 := by
  induction u with
  | nil => simp
  | cons a t ih =>
    intro x hx
    rw [List.sum_cons, List.length_cons] at hs
    have h1 : 1 ≤ a := h a (List.mem_cons_self ..)
    have h2 : t.length ≤ t.sum :=
      length_le_sum_of_one_le (fun y hy => h y (List.mem_cons_of_mem a hy))
    have ha : a = 1 := by omega
    have ht : t.sum = t.length := by omega
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ha
    · exact ih (fun y hy => h y (List.mem_cons_of_mem a hy)) ht x hx'

/-- **Bookkeeping of the depth-first refinement process** of `Work.Peluse.SwapC.concatAll`
(KKL Proposition 6.2's `2^s - 1` applications of `concatStep`).

`cproc s k` is the subdivision of `{0,1}^s` after `k` splits, a split replacing the first leaf of
depth `< s` (`cnextLeaf`, `csplitFirst`, `refine`) by its two children (`CLeaf.children`); a leaf is
a string with its depth and the padding condition `str i = false` for `dep ≤ i` (`CLeaf`);
`IsSubdiv Λ` says the cells `{x : x = str on the first dep coordinates}` of the leaves of `Λ`
partition `{0,1}^s`.

Claims: (1) every `cproc s k` is a subdivision; (2) for `k ≤ 2^s - 1` it has exactly `k + 1` leaves;
(3) at `k = 2^s - 1` every leaf has depth `s`; (4) for a `Nodup` list, `csplitFirst` is `refine` at
the next leaf.

Route: (1),(2),(3) by induction on `k`: each split replaces a leaf of depth `d < s` by its two
children of depth `d + 1`, whose cells partition the parent's cell (split by the `d`-th
coordinate), so `IsSubdiv` is preserved and the leaf count grows by one; the process is stuck exactly
when every depth is `s`, i.e. when the leaf count is `2^s`. For (4), `csplitFirst` splits the first
depth-`< s` leaf while `refine Λ l` splits every occurrence of `l`; under `Λ.Nodup` and
`cnextLeaf Λ = some l` there is exactly one such occurrence and it is the first depth-`< s` leaf. -/
theorem cprocBookkeeping (s : ℕ) :
    (∀ k : ℕ, IsSubdiv (cproc s k)) ∧
    (∀ k : ℕ, k ≤ 2 ^ s - 1 → (cproc s k).length = k + 1) ∧
    (∀ l ∈ cproc s (2 ^ s - 1), l.dep = s) ∧
    (∀ (Λ : List (CLeaf s)) (l : CLeaf s) (h : l.dep < s),
      Λ.Nodup → cnextLeaf Λ = some l → csplitFirst Λ = refine Λ l) := by
  have hInv : ∀ k : ℕ, IsSubdiv (cproc s k) ∧ (cproc s k).Nodup ∧
      cellSum (cproc s k) = 2 ^ s ∧ (cproc s k).length = min (k + 1) (2 ^ s) := by
    intro k
    induction k with
    | zero =>
      rw [cproc.eq_1]
      refine ⟨isSubdivIffCoversPairDisj.mpr ⟨covers_singleton rfl, pairDisj_singleton _⟩,
        ?_, ?_, ?_⟩
      · simp
      · simp [cellSum]
      · rw [List.length_singleton, Nat.min_eq_left Nat.one_le_two_pow]
    | succ k ih =>
      obtain ⟨hsub, hnod, hcs, hlen⟩ := ih
      rw [cproc.eq_2]
      by_cases hHs : HasSplit (cproc s k)
      · obtain ⟨P, m, Q, hm, hΛ, hP, hcf⟩ := exists_split_decomp hHs
        have hlen_lt : (cproc s k).length < 2 ^ s := (hasSplitIffLengthLt hcs).mp hHs
        have hk1le : k + 1 ≤ 2 ^ s := by
          by_contra hc
          rw [hlen, Nat.min_eq_right (le_of_lt (not_le.mp hc))] at hlen_lt
          omega
        have hk1 : (cproc s k).length = k + 1 := by rw [hlen, Nat.min_eq_left hk1le]
        have hk2 : k + 1 + 1 ≤ 2 ^ s := by omega
        have hnodΛ : (P ++ m :: Q).Nodup := by rw [← hΛ]; exact hnod
        have hsubΛ : IsSubdiv (P ++ m :: Q) := by rw [← hΛ]; exact hsub
        have hsplit := List.nodup_append'.mp hnodΛ
        have hd : P.Disjoint (m :: Q) := hsplit.2.2
        have hmP : m ∉ P := fun hmem =>
          (List.disjoint_iff_ne.mp hd) m hmem m (List.mem_cons_self ..) rfl
        have hmQ : m ∉ Q := (List.nodup_cons.mp hsplit.2.1).1
        have hcov : Covers (csplitFirst (cproc s k)) := by
          rw [hcf]
          exact coversSplit hm (isSubdivIffCoversPairDisj.mp hsubΛ).1
        have hpd : PairDisj (csplitFirst (cproc s k)) := by
          rw [hcf]
          exact pairDisjSplit hm hmP hmQ (isSubdivIffCoversPairDisj.mp hsubΛ).2
        refine ⟨isSubdivIffCoversPairDisj.mpr ⟨hcov, hpd⟩, ?_, ?_, ?_⟩
        · exact nodup_csplitFirst hnod (pairDisj_of_isSubdiv hsub)
        · rw [hcf, cellSumSplit hm, ← hΛ]
          exact hcs
        · rw [csplitFirst_length_of_hasSplit hHs, hk1, Nat.min_eq_left hk2]
      · have hfix := csplitFirst_eq_self_of_not_hasSplit hHs
        have hmin : min (k + 1) (2 ^ s) = 2 ^ s := by
          have hnotlt : ¬ (cproc s k).length < 2 ^ s := by
            rw [← hasSplitIffLengthLt hcs]; exact hHs
          have h1 : 2 ^ s ≤ (cproc s k).length := not_lt.mp hnotlt
          have h2 : (cproc s k).length ≤ 2 ^ s := by
            rw [← hcs]; exact cellSum_length_le
          rw [← hlen]
          exact le_antisymm h2 h1
        have hge : 2 ^ s ≤ k + 1 := by
          by_contra hc
          rw [Nat.min_eq_left (le_of_lt (not_le.mp hc))] at hmin
          omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hfix]; exact hsub
        · rw [hfix]; exact hnod
        · rw [hfix]; exact hcs
        · rw [hfix, hlen, hmin, Nat.min_eq_right (by omega)]
  refine ⟨fun k => (hInv k).1, ?_, ?_, ?_⟩
  · intro k hk
    have h := (hInv k).2.2.2
    have hk' : k + 1 ≤ 2 ^ s := by
      calc k + 1 ≤ (2 ^ s - 1) + 1 := Nat.succ_le_succ hk
        _ = 2 ^ s := Nat.sub_add_cancel Nat.one_le_two_pow
    rw [h, Nat.min_eq_left hk']
  · intro l hl
    have hcs : cellSum (cproc s (2 ^ s - 1)) = 2 ^ s := (hInv (2 ^ s - 1)).2.2.1
    have hlen : (cproc s (2 ^ s - 1)).length = 2 ^ s := by
      have h := (hInv (2 ^ s - 1)).2.2.2
      rw [h, Nat.sub_add_cancel Nat.one_le_two_pow, Nat.min_self]
    exact depEqOfCellSumEqCard hcs hlen l hl
  · intro Λ l h hnod hfind
    obtain ⟨P, Q, hΛ, hP⟩ := prefixOfFind hfind
    have h1 : csplitFirst (P ++ l :: Q) = P ++ l.children h ++ Q :=
      csplitFirstEqOfForall hP h
    have h2 : refine (P ++ l :: Q) l = P ++ l.children h ++ Q :=
      refineEqOfNodupAppend (by rw [← hΛ]; exact hnod) h
    rw [hΛ]
    exact h1.trans h2.symm

end Work.Peluse.SwapC
