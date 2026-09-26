import Mathlib
import Submission.Work.PTCert.QAdjOpDefs

namespace Work.PTCert

theorem adj_iff_shares (r : ℕ) (p q : Submission.RouteB.Edge r) :
    Submission.RouteB.Edge.Adj p q ↔ p ≠ q ∧
      Submission.PTCert.shares (Submission.PTCert.edgePair p)
        (Submission.PTCert.edgePair q) := by
  rw [Submission.RouteB.Edge.Adj]
  constructor
  · rintro ⟨hne, hnd⟩
    refine ⟨hne, ?_⟩
    rw [Submission.PTCert.shares, Submission.PTCert.edgePair]
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨k, hk1, hk2⟩ := hnd
    rw [Submission.RouteB.Edge.mem_toFinset] at hk1 hk2
    rcases hk1 with h1 | h1 <;> rcases hk2 with h2 | h2
    · exact Or.inl (congrArg Fin.val (h1.symm.trans h2))
    · exact Or.inr (Or.inl (congrArg Fin.val (h1.symm.trans h2)))
    · exact Or.inr (Or.inr (Or.inl (congrArg Fin.val (h1.symm.trans h2))))
    · exact Or.inr (Or.inr (Or.inr (congrArg Fin.val (h1.symm.trans h2))))
  · rintro ⟨hne, hs⟩
    refine ⟨hne, ?_⟩
    rw [Finset.not_disjoint_iff]
    rw [Submission.PTCert.shares, Submission.PTCert.edgePair] at hs
    rcases hs with h | h | h | h
    · exact ⟨p.1.1, by rw [Submission.RouteB.Edge.mem_toFinset]; exact Or.inl rfl,
        by rw [Submission.RouteB.Edge.mem_toFinset]; exact Or.inl (Fin.ext h)⟩
    · exact ⟨p.1.1, by rw [Submission.RouteB.Edge.mem_toFinset]; exact Or.inl rfl,
        by rw [Submission.RouteB.Edge.mem_toFinset]; exact Or.inr (Fin.ext h)⟩
    · exact ⟨p.1.2, by rw [Submission.RouteB.Edge.mem_toFinset]; exact Or.inr rfl,
        by rw [Submission.RouteB.Edge.mem_toFinset]; exact Or.inl (Fin.ext h)⟩
    · exact ⟨p.1.2, by rw [Submission.RouteB.Edge.mem_toFinset]; exact Or.inr rfl,
        by rw [Submission.RouteB.Edge.mem_toFinset]; exact Or.inr (Fin.ext h)⟩

end Work.PTCert
