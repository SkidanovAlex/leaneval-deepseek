import Mathlib
import Submission.Work.ANALYTIC.CechPt.LevelAux

namespace Work.ANALYTIC.CechPt

theorem sum_mid_eq {M q : ℕ} (y : Work.ANALYTIC.CechPt.Level.lev M (q+1)) (G : Work.ANALYTIC.CechPt.Level.lev M (q+1) → ℤ) :
    (∑ p ∈ (Finset.univ : Finset (Fin (q+2) × Fin (q+3))).filter
        (fun p => (p.2:ℕ) = (p.1:ℕ) ∨ (p.2:ℕ) = (p.1:ℕ)+1),
        (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (Work.ANALYTIC.CechPt.Level.face p.2 (Work.ANALYTIC.CechPt.Level.W p.1 y)))
      = ∑ j : Fin (q+2), (G (Work.ANALYTIC.CechPt.Level.midH ⟨(j:ℕ), by omega⟩ y)
            - G (Work.ANALYTIC.CechPt.Level.midH ⟨(j:ℕ)+1, by omega⟩ y)) := by
  have h1 : (((Finset.univ : Finset (Fin (q+2) × Fin (q+3))).filter
        (fun p => (p.2:ℕ) = (p.1:ℕ) ∨ (p.2:ℕ) = (p.1:ℕ)+1)).filter
        (fun p => (p.2:ℕ) = (p.1:ℕ)))
      = (Finset.univ : Finset (Fin (q+2) × Fin (q+3))).filter
          (fun p => (p.2:ℕ) = (p.1:ℕ)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨Or.inl h, h⟩
  have h2 : (((Finset.univ : Finset (Fin (q+2) × Fin (q+3))).filter
        (fun p => (p.2:ℕ) = (p.1:ℕ) ∨ (p.2:ℕ) = (p.1:ℕ)+1)).filter
        (fun p => ¬ (p.2:ℕ) = (p.1:ℕ)))
      = (Finset.univ : Finset (Fin (q+2) × Fin (q+3))).filter
          (fun p => (p.2:ℕ) = (p.1:ℕ)+1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hR, hP⟩
      rcases hR with h | h
      · exact absurd h hP
      · exact h
    · exact fun h => ⟨Or.inr h, by omega⟩
  have hA : (∑ p ∈ (Finset.univ : Finset (Fin (q+2) × Fin (q+3))).filter
        (fun p => (p.2:ℕ) = (p.1:ℕ)),
        (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (Work.ANALYTIC.CechPt.Level.face p.2 (Work.ANALYTIC.CechPt.Level.W p.1 y)))
      = ∑ a : Fin (q+2), G (Work.ANALYTIC.CechPt.Level.midH ⟨(a:ℕ), by omega⟩ y) := by
    refine (Finset.sum_bij (s := (Finset.univ : Finset (Fin (q+2))))
      (t := (Finset.univ : Finset (Fin (q+2) × Fin (q+3))).filter
        (fun p => (p.2:ℕ) = (p.1:ℕ)))
      (f := fun a : Fin (q+2) => G (Work.ANALYTIC.CechPt.Level.midH ⟨(a:ℕ), by omega⟩ y))
      (g := fun p : Fin (q+2) × Fin (q+3) =>
        (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (Work.ANALYTIC.CechPt.Level.face p.2 (Work.ANALYTIC.CechPt.Level.W p.1 y)))
      (fun a _ => (a, ⟨(a:ℕ), by omega⟩)) ?_ ?_ ?_ ?_).symm
    · intro a _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro a₁ _ a₂ _ h
      exact congrArg Prod.fst h
    · intro b hb
      refine ⟨b.1, Finset.mem_univ _, Prod.ext rfl ?_⟩
      have hb' : (b.2:ℕ) = (b.1:ℕ) := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hb
      exact Fin.ext hb'.symm
    · intro a _
      show G (Work.ANALYTIC.CechPt.Level.midH ⟨(a:ℕ), by omega⟩ y)
        = (-1:ℤ)^((a:ℕ)+(a:ℕ)) * G (Work.ANALYTIC.CechPt.Level.face ⟨(a:ℕ), by omega⟩ (Work.ANALYTIC.CechPt.Level.W a y))
      rw [Level.face_W_eq (M := M) (p := q) a y]
      have hone : (-1:ℤ)^((a:ℕ)+(a:ℕ)) = 1 := by
        rw [show (a:ℕ)+(a:ℕ) = 2*(a:ℕ) by ring, pow_mul, neg_one_sq, one_pow]
      rw [hone, one_mul]
  have hB : (∑ p ∈ (Finset.univ : Finset (Fin (q+2) × Fin (q+3))).filter
        (fun p => (p.2:ℕ) = (p.1:ℕ)+1),
        (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (Work.ANALYTIC.CechPt.Level.face p.2 (Work.ANALYTIC.CechPt.Level.W p.1 y)))
      = ∑ a : Fin (q+2), -(G (Work.ANALYTIC.CechPt.Level.midH ⟨(a:ℕ)+1, by omega⟩ y)) := by
    refine (Finset.sum_bij (s := (Finset.univ : Finset (Fin (q+2))))
      (t := (Finset.univ : Finset (Fin (q+2) × Fin (q+3))).filter
        (fun p => (p.2:ℕ) = (p.1:ℕ)+1))
      (f := fun a : Fin (q+2) => -(G (Work.ANALYTIC.CechPt.Level.midH ⟨(a:ℕ)+1, by omega⟩ y)))
      (g := fun p : Fin (q+2) × Fin (q+3) =>
        (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (Work.ANALYTIC.CechPt.Level.face p.2 (Work.ANALYTIC.CechPt.Level.W p.1 y)))
      (fun a _ => (a, ⟨(a:ℕ)+1, by omega⟩)) ?_ ?_ ?_ ?_).symm
    · intro a _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro a₁ _ a₂ _ h
      exact congrArg Prod.fst h
    · intro b hb
      refine ⟨b.1, Finset.mem_univ _, Prod.ext rfl ?_⟩
      have hb' : (b.2:ℕ) = (b.1:ℕ)+1 := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hb
      exact Fin.ext hb'.symm
    · intro a _
      show -(G (Work.ANALYTIC.CechPt.Level.midH ⟨(a:ℕ)+1, by omega⟩ y))
        = (-1:ℤ)^((a:ℕ)+((a:ℕ)+1)) * G (Work.ANALYTIC.CechPt.Level.face ⟨(a:ℕ)+1, by omega⟩ (Work.ANALYTIC.CechPt.Level.W a y))
      rw [Level.face_W_succ (M := M) (p := q) a y]
      have hneg : (-1:ℤ)^((a:ℕ)+((a:ℕ)+1)) = -1 := by
        rw [show (a:ℕ)+((a:ℕ)+1) = 2*(a:ℕ)+1 by ring, pow_succ, pow_mul, neg_one_sq, one_pow,
          one_mul]
      rw [hneg, neg_one_mul]
  rw [← Finset.sum_filter_add_sum_filter_not
      ((Finset.univ : Finset (Fin (q+2) × Fin (q+3))).filter
        (fun p => (p.2:ℕ) = (p.1:ℕ) ∨ (p.2:ℕ) = (p.1:ℕ)+1))
      (fun p => (p.2:ℕ) = (p.1:ℕ))
      (fun p => (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (Work.ANALYTIC.CechPt.Level.face p.2 (Work.ANALYTIC.CechPt.Level.W p.1 y)))]
  rw [h1, h2, hA, hB, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [sub_eq_add_neg]

end Work.ANALYTIC.CechPt
