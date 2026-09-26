import Mathlib
import Submission.Work.SG.SellStabDefs

namespace Work.SG

/-! # The coset representatives of a join certificate lie in a `gmul`-closed set

`Work.SG.CZ.joinReps S cos` (`Submission/Work/SG/SellStabDefs.lean`) is the list of coset
representatives of a join certificate, built by
`r₀ = S.one`, `r_{q+1} = r_{cos[q].1} · cos[q].2` (with `·` the table product
`Work.SG.CZ.gmul S a b = (S.mul.getD a []).getD b 0`).  The claim: if `F : Finset ℕ` contains
`S.one` and is closed under `gmul` (`∀ a ∈ F, ∀ b ∈ F, gmul S a b ∈ F`), and if every
certificate entry satisfies `(cos q).1 ≤ q` (so that the index `(cos q).1` points at an
*earlier* representative, which is what the checker `chkJoin` enforces) and `(cos q).2 ∈ F`,
then every representative lies in `F`.

This is a pure fold induction: at step `q` the accumulated list is
`[r₀, …, r_q]`, `(cos q).1 ≤ q` selects one of those (hence an element of `F`), and
`(cos q).2 ∈ F`, so the newly appended product is in `F`.  Formally, generalise the accumulator
(`∀ rs, (∀ r ∈ rs, r ∈ F) → ∀ q < cos.length, (cos q).1 < rs.length + q → …`). -/

namespace CZ

/-- `joinStep` appends precisely the table product of the `p.1`-th accumulated entry with `p.2`. -/
theorem joinStep_eq (S : Data.SellData) (rs : List ℕ) (p : ℕ × ℕ) :
    joinStep S rs p = rs ++ [gmul S (rs.getD p.1 0) p.2] := rfl

/-- An in-range `getD` is an element of the list. -/
theorem getD_mem {l : List ℕ} {n d : ℕ} (h : n < l.length) : l.getD n d ∈ l := by
  rw [List.getD_eq_getElem l d h]
  exact List.getElem_mem h

end CZ

/-- The fold induction underlying `joinReps_mem`: running `foldl (joinStep S)` over any list
`l` from an accumulator `rs` whose members lie in `F`, where each entry of `l` selects an
already-accumulated predecessor (the `(·).1` component of the `q`-th entry is `< rs.length + q`,
i.e. it points at an entry accumulated at a strictly earlier stage) and contributes a second
component in `F`, keeps every accumulated entry inside `F`. -/
private theorem foldl_joinStep_mem {S : Data.SellData} {F : Finset ℕ}
    (hclos : ∀ a ∈ F, ∀ b ∈ F, CZ.gmul S a b ∈ F) :
    ∀ (l : List (ℕ × ℕ)) (rs : List ℕ),
      (∀ r ∈ rs, r ∈ F) →
      (∀ q, q < l.length → (l.getD q (0, 0)).1 < rs.length + q) →
      (∀ q, q < l.length → (l.getD q (0, 0)).2 ∈ F) →
      ∀ r ∈ l.foldl (CZ.joinStep S) rs, r ∈ F := by
  intro l
  induction l with
  | nil =>
    intro rs hrs _ _ r hr
    simpa using hrs r hr
  | cons a l' ih =>
    intro rs hrs hidx hcos r hr
    rw [List.foldl_cons] at hr
    have hstep : CZ.joinStep S rs a = rs ++ [CZ.gmul S (rs.getD a.1 0) a.2] := rfl
    refine ih (CZ.joinStep S rs a) ?_ ?_ ?_ r hr
    · intro x hx
      rw [hstep, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hrs x hx
      · have h0 : a.1 < rs.length + 0 := hidx 0 (by simp)
        have ha1 : a.1 < rs.length := by simpa using h0
        exact hclos (rs.getD a.1 0) (hrs _ (CZ.getD_mem (d := 0) ha1)) a.2 (hcos 0 (by simp))
    · intro q hq
      have hq' : q + 1 < (a :: l').length := by simp only [List.length_cons]; omega
      have h := hidx (q + 1) hq'
      rw [List.getD_cons_succ] at h
      have hlen : (CZ.joinStep S rs a).length = rs.length + 1 := by
        rw [hstep]; simp
      rw [hlen]
      omega
    · intro q hq
      have hq' : q + 1 < (a :: l').length := by simp only [List.length_cons]; omega
      have h := hcos (q + 1) hq'
      rwa [List.getD_cons_succ] at h

theorem joinReps_mem {S : Work.SG.Data.SellData} {cos : List (ℕ × ℕ)} {F : Finset ℕ}
    (hone : S.one ∈ F)
    (hclos : ∀ a ∈ F, ∀ b ∈ F, Work.SG.CZ.gmul S a b ∈ F)
    (hidx : ∀ q, q < cos.length → (cos.getD q (0, 0)).1 ≤ q)
    (hcos : ∀ q, q < cos.length → (cos.getD q (0, 0)).2 ∈ F) :
    ∀ r ∈ Work.SG.CZ.joinReps S cos, r ∈ F := by
  intro r hr
  rw [Work.SG.CZ.joinReps] at hr
  refine foldl_joinStep_mem hclos cos [S.one] ?_ ?_ ?_ r hr
  · intro x hx
    rw [List.mem_singleton] at hx
    rw [hx]
    exact hone
  · intro q hq
    have h := hidx q hq
    simp only [List.length_singleton]
    omega
  · intro q hq
    exact hcos q hq

end Work.SG
