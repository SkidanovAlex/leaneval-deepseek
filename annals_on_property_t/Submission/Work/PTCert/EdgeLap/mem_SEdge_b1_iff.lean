import Mathlib
import Submission.Work.PTCert.LetterAPI

namespace Work.PTCert.EdgeLap

open Submission.FreeGroupAut

/-- Membership of a Nielsen transvection `Xtr i j hij k` (`k < 4`) in the *directed* edge set
`dirEdge i' j' hij' = {ρᵢ'ⱼ', ρᵢ'ⱼ'⁻¹, λᵢ'ⱼ', λᵢ'ⱼ'⁻¹}`: it is equivalent to `(i,j) = (i',j')`.

The forward direction is `XtrInjective`: each of the four generators of `dirEdge i' j' hij'` is
`Xtr i' j' hij' m` for `m ∈ {0,1,2,3}`; the reverse direction is `interval_cases` on `k`. -/
theorem Xtr_mem_dirEdge_iff {r : ℕ} (i j i' j' : Fin r) (hij : i ≠ j) (hij' : i' ≠ j')
    (k : ℕ) (hk : k < 4) :
    Submission.PTCert.Xtr i j hij k ∈ Submission.RouteB.Edge.dirEdge i' j' hij' ↔
      i = i' ∧ j = j' := by
  constructor
  · intro h
    rw [Submission.RouteB.Edge.mem_dirEdge] at h
    have key : ∀ m : ℕ, m < 4 → Submission.PTCert.Xtr i j hij k = Submission.PTCert.Xtr i' j' hij' m →
        i = i' ∧ j = j' := by
      intro m hm hkm
      obtain ⟨hi, hj, -⟩ := Work.PTCert.XtrInjective _ _ _ _ _ _ _ _ hk hm hkm
      exact ⟨hi, hj⟩
    rcases h with h | h | h | h
    · exact key 0 (by norm_num) (by rw [h, Submission.PTCert.Xtr_zero])
    · exact key 1 (by norm_num) (by rw [h, Submission.PTCert.Xtr_one])
    · exact key 2 (by norm_num) (by rw [h, Submission.PTCert.Xtr_two])
    · exact key 3 (by norm_num) (by rw [h, Submission.PTCert.Xtr_three])
  · rintro ⟨hi, hj⟩
    subst hi; subst hj
    interval_cases k <;>
      simp [Submission.RouteB.Edge.mem_dirEdge, Submission.PTCert.Xtr]

/-- Membership of a letter in the transvection set of an edge: for `1 ≤ a < NB1 r`, the letter
`b1 r a` (the Nielsen transvection `Xtr u v _ ((a-1)%4)` on the ordered pair
`(u,v) = pairOf r ((a-1)/4)`) lies in `SEdge p` (`p : Edge r`, vertices `i < j`) if and only if
the ordered pair `(u,v)` is `(i,j)` or `(j,i)`.
Route: `SEdge p = sEdgeOf i j hij = dirEdge i j hij ∪ dirEdge j i hij.symm` (`SEdge_def`,
`mem_sEdgeOf`), and `dirEdge i j hij = (Finset.range 4).image (fun k => Xtr i j hij k)` with
`XtrInjective` giving `Xtr u v huv k ∈ dirEdge i j hij ↔ u = i ∧ v = j` (`k < 4`).
Unfold `b1 r a` with `LetterAPI.b1_eq_ltr` + `LetterAPI.ltr_eq_Xtr` (note
`Submission.PTCert.four_decomp` gives `a = 1 + 4*((a-1)/4) + (a-1)%4`), and use
`Submission.PTCert.q_lt` / `Work.PTCert.pairOf_bounds` on `q = (a-1)/4`. -/
theorem mem_SEdge_b1_iff (r : ℕ) (hr : 2 ≤ r) (p : Submission.RouteB.Edge r) (a : ℕ)
    (ha1 : 1 ≤ a) (ha2 : a < Submission.PTCert.NB1 r) :
    Submission.PTCert.b1 r a ∈ Submission.RouteB.Edge.SEdge p ↔
      Submission.PTCert.pairOf r ((a - 1) / 4) = ((p.1.1 : ℕ), (p.1.2 : ℕ)) ∨
      Submission.PTCert.pairOf r ((a - 1) / 4) = ((p.1.2 : ℕ), (p.1.1 : ℕ)) := by
  have hq : (a - 1) / 4 < r * (r - 1) := Submission.PTCert.q_lt r a ha1 ha2
  have hPb := Work.PTCert.pairOf_bounds hq
  set i : Fin r := ⟨(Submission.PTCert.pairOf r ((a - 1) / 4)).1, hPb.1⟩ with hi
  set j : Fin r := ⟨(Submission.PTCert.pairOf r ((a - 1) / 4)).2, hPb.2.1⟩ with hj
  have hij : i ≠ j := fun e => hPb.2.2 (congrArg Fin.val e)
  have hb1 : Submission.PTCert.b1 r a = Submission.PTCert.Xtr i j hij ((a - 1) % 4) := by
    rw [Submission.PTCert.b1_eq_ltr r a hr ha1 ha2,
      Submission.PTCert.ltr_eq_Xtr r a hPb i j hij (by simp [hi, hj])]
  have hk4 : (a - 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hpair : ((i : ℕ), (j : ℕ)) = Submission.PTCert.pairOf r ((a - 1) / 4) := by simp [hi, hj]
  rw [hb1, Submission.RouteB.Edge.SEdge_def, Submission.RouteB.Edge.mem_sEdgeOf,
    Xtr_mem_dirEdge_iff i j p.1.1 p.1.2 hij (ne_of_lt p.2) _ hk4,
    Xtr_mem_dirEdge_iff i j p.1.2 p.1.1 hij (ne_of_lt p.2).symm _ hk4]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left
      have hh : ((i : ℕ), (j : ℕ)) = ((p.1.1 : ℕ), (p.1.2 : ℕ)) := by rw [h1, h2]
      exact hpair.symm.trans hh
    · right
      have hh : ((i : ℕ), (j : ℕ)) = ((p.1.2 : ℕ), (p.1.1 : ℕ)) := by rw [h1, h2]
      exact hpair.symm.trans hh
  · rintro (h | h)
    · exact Or.inl ⟨Fin.ext (congrArg Prod.fst (hpair.trans h)),
        Fin.ext (congrArg Prod.snd (hpair.trans h))⟩
    · exact Or.inr ⟨Fin.ext (congrArg Prod.fst (hpair.trans h)),
        Fin.ext (congrArg Prod.snd (hpair.trans h))⟩

end Work.PTCert.EdgeLap
