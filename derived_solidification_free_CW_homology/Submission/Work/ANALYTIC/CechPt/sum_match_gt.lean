import Mathlib
import Submission.Work.ANALYTIC.CechPt.LevelAux

namespace Work.ANALYTIC.CechPt

open Work.ANALYTIC.CechPt.Level

/-- `(-1)^m = -(-1)^(m-1)` for `m ≥ 1`. -/
private lemma neg_one_pow_eq_neg (m : ℕ) (hm : 1 ≤ m) :
    (-1 : ℤ) ^ m = -((-1 : ℤ) ^ (m - 1)) := by
  conv_lhs => rw [← Nat.sub_add_cancel hm]
  rw [pow_succ]
  ring

theorem sum_match_gt {M q : ℕ} (y : Work.ANALYTIC.CechPt.Level.lev M (q+1)) (G : Work.ANALYTIC.CechPt.Level.lev M (q+1) → ℤ) :
    (∑ p ∈ (Finset.univ : Finset (Fin (q+2) × Fin (q+3))).filter (fun p => (p.1:ℕ)+1 < (p.2:ℕ)),
        (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (Work.ANALYTIC.CechPt.Level.face p.2 (Work.ANALYTIC.CechPt.Level.W p.1 y)))
      = - (∑ p ∈ (Finset.univ : Finset (Fin (q+2) × Fin (q+1))).filter (fun p => ¬ (p.1:ℕ) ≤ (p.2:ℕ)),
        (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (Work.ANALYTIC.CechPt.Level.W p.2 (Work.ANALYTIC.CechPt.Level.face p.1 y))) := by
  classical
  have key := Finset.sum_bij'
    (s := (Finset.univ : Finset (Fin (q+2) × Fin (q+3))).filter (fun p => (p.1:ℕ)+1 < (p.2:ℕ)))
    (t := (Finset.univ : Finset (Fin (q+2) × Fin (q+1))).filter (fun p => ¬ (p.1:ℕ) ≤ (p.2:ℕ)))
    (f := fun p : Fin (q+2) × Fin (q+3) => (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (face p.2 (W p.1 y)))
    (g := fun r : Fin (q+2) × Fin (q+1) => -((-1:ℤ)^((r.1:ℕ)+(r.2:ℕ)) * G (W r.2 (face r.1 y))))
    (fun p hp => (⟨(p.2:ℕ)-1, by have h := (Finset.mem_filter.mp hp).2; have := p.2.isLt; omega⟩,
                  ⟨(p.1:ℕ), by have h := (Finset.mem_filter.mp hp).2; have := p.1.isLt; omega⟩))
    (fun r hr => (⟨(r.2:ℕ), by have := r.2.isLt; omega⟩,
                  ⟨(r.1:ℕ)+1, by have := r.1.isLt; omega⟩))
    (by
      intro p hp
      have hp' : (p.1:ℕ)+1 < (p.2:ℕ) := (Finset.mem_filter.mp hp).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show ¬ ((p.2:ℕ) - 1) ≤ (p.1:ℕ)
      omega)
    (by
      intro r hr
      have hr' : ¬ (r.1:ℕ) ≤ (r.2:ℕ) := (Finset.mem_filter.mp hr).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show ((r.2:ℕ) + 1) < ((r.1:ℕ) + 1)
      omega)
    (by
      intro p hp
      have hp' : (p.1:ℕ)+1 < (p.2:ℕ) := (Finset.mem_filter.mp hp).2
      apply Prod.ext
      · exact Fin.ext rfl
      · apply Fin.ext
        simp only []
        omega)
    (by
      intro r hr
      apply Prod.ext
      · apply Fin.ext
        simp only []
        omega
      · exact Fin.ext rfl)
    (by
      intro p hp
      have hp' : (p.1:ℕ)+1 < (p.2:ℕ) := (Finset.mem_filter.mp hp).2
      have hface : face p.2 (W p.1 y)
          = W (⟨(p.1:ℕ), by have := p.1.isLt; omega⟩ : Fin (q+1))
              (face (⟨(p.2:ℕ)-1, by have := p.2.isLt; omega⟩ : Fin (q+2)) y) := by
        have h := face_W_gt (M := M) (p := q)
          (j := (⟨(p.1:ℕ), by have := p.1.isLt; omega⟩ : Fin (q+1)))
          (y := y)
          (i := (⟨(p.2:ℕ)-1, by have := p.2.isLt; omega⟩ : Fin (q+2)))
          (by show (p.1:ℕ)+1 ≤ (p.2:ℕ)-1; omega)
        rw [show (⟨((p.2:ℕ)-1)+1, by omega⟩ : Fin (q+3)) = p.2 from
              Fin.ext (by simp only []; omega),
            show (Fin.castSucc (⟨(p.1:ℕ), by have := p.1.isLt; omega⟩ : Fin (q+1)) : Fin (q+2))
              = p.1 from Fin.ext (by simp only [Fin.val_castSucc])] at h
        exact h
      rw [hface]
      have hm : 1 ≤ (p.1:ℕ)+(p.2:ℕ) := by omega
      have hsub : ((p.2:ℕ)-1)+(p.1:ℕ) = (p.1:ℕ)+(p.2:ℕ)-1 := by omega
      rw [hsub, neg_one_pow_eq_neg _ hm]
      ring)
  rw [key, Finset.sum_neg_distrib]

end Work.ANALYTIC.CechPt
