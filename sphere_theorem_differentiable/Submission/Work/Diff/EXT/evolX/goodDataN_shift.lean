import Mathlib
import Submission.Work.Diff.EXT.evolX.ladderAtoms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evolX

theorem goodDataN_shift
    (m l N : ℕ) (s : Fin (m + 4))
    (κ : Fin (m + 4) → Fin N) (ξ : Fin (l + 3) → Fin N)
    (hgood : Work.Diff.EXT.evolX.GoodDataN m l N s κ ξ) :
    Work.Diff.EXT.evolX.GoodDataN (m + 1) l (N + 1) (Fin.succ s)
        (Fin.cons 0 (fun i : Fin (m + 4) => Fin.succ (κ i)))
        (fun r : Fin (l + 3) => Fin.succ (ξ r))
      ∧ Work.Diff.EXT.evolX.GoodDataN m (l + 1) (N + 1) s
        (fun i : Fin (m + 4) => Fin.succ (κ i))
        (Fin.cons 0 (fun r : Fin (l + 3) => Fin.succ (ξ r))) := by
  obtain ⟨hκ, hξ, hdisj, hcov⟩ := hgood
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · -- the `κ`-map of the first shift is injective off the new slot `Fin.succ s`
    intro i j hi hj hij
    obtain rfl | ⟨i', rfl⟩ := Fin.eq_zero_or_eq_succ i
    · obtain rfl | ⟨j', rfl⟩ := Fin.eq_zero_or_eq_succ j
      · rfl
      · simp only [Fin.cons_zero, Fin.cons_succ] at hij
        exact absurd hij.symm (Fin.succ_ne_zero (κ j'))
    · obtain rfl | ⟨j', rfl⟩ := Fin.eq_zero_or_eq_succ j
      · simp only [Fin.cons_zero, Fin.cons_succ] at hij
        exact absurd hij (Fin.succ_ne_zero (κ i'))
      · simp only [Fin.cons_succ] at hij
        have h1 : i' ≠ s := fun h => hi (congrArg Fin.succ h)
        have h2 : j' ≠ s := fun h => hj (congrArg Fin.succ h)
        exact congrArg Fin.succ (hκ i' j' h1 h2 (Fin.succ_inj.mp hij))
  · -- the `ξ`-map of the first shift is injective
    intro a b hab
    exact hξ (Fin.succ_inj.mp hab)
  · -- disjointness for the first shift
    intro i r hi h
    obtain rfl | ⟨i', rfl⟩ := Fin.eq_zero_or_eq_succ i
    · simp only [Fin.cons_zero] at h
      exact Fin.succ_ne_zero (ξ r) h.symm
    · simp only [Fin.cons_succ] at h
      exact hdisj i' r (fun hh => hi (congrArg Fin.succ hh)) (Fin.succ_inj.mp h)
  · -- covering for the first shift
    intro u
    obtain rfl | ⟨u', rfl⟩ := Fin.eq_zero_or_eq_succ u
    · exact Or.inl ⟨0, fun h => Fin.succ_ne_zero s h.symm, by simp⟩
    · rcases hcov u' with ⟨i', hi', hiu⟩ | ⟨r, hr⟩
      · exact Or.inl ⟨i'.succ, fun h => hi' (Fin.succ_inj.mp h), by
          simp only [Fin.cons_succ]; exact congrArg Fin.succ hiu⟩
      · exact Or.inr ⟨r, by simp only; exact congrArg Fin.succ hr⟩
  · -- the `κ`-map of the second shift is injective off `s`
    intro i j hi hj hij
    exact hκ i j hi hj (Fin.succ_inj.mp hij)
  · -- the `ξ`-map of the second shift is injective
    intro a b hab
    obtain rfl | ⟨a', rfl⟩ := Fin.eq_zero_or_eq_succ a
    · obtain rfl | ⟨b', rfl⟩ := Fin.eq_zero_or_eq_succ b
      · rfl
      · simp only [Fin.cons_zero, Fin.cons_succ] at hab
        exact absurd hab.symm (Fin.succ_ne_zero (ξ b'))
    · obtain rfl | ⟨b', rfl⟩ := Fin.eq_zero_or_eq_succ b
      · simp only [Fin.cons_zero, Fin.cons_succ] at hab
        exact absurd hab (Fin.succ_ne_zero (ξ a'))
      · simp only [Fin.cons_succ] at hab
        exact congrArg Fin.succ (hξ (Fin.succ_inj.mp hab))
  · -- disjointness for the second shift
    intro i r hi h
    obtain rfl | ⟨r', rfl⟩ := Fin.eq_zero_or_eq_succ r
    · simp only [Fin.cons_zero] at h
      exact Fin.succ_ne_zero (κ i) h
    · simp only [Fin.cons_succ] at h
      exact hdisj i r' hi (Fin.succ_inj.mp h)
  · -- covering for the second shift
    intro u
    obtain rfl | ⟨u', rfl⟩ := Fin.eq_zero_or_eq_succ u
    · exact Or.inr ⟨0, by simp⟩
    · rcases hcov u' with ⟨i', hi', hiu⟩ | ⟨r, hr⟩
      · exact Or.inl ⟨i', hi', congrArg Fin.succ hiu⟩
      · exact Or.inr ⟨r.succ, congrArg Fin.succ hr⟩

end Work.Diff.EXT.evolX
