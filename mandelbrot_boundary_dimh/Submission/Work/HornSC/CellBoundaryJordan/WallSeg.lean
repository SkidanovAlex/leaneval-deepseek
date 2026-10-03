import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.WallGraph

/-!
# Segments attached to lattice steps

A unit grid segment determines its two endpoints, so for unit-adjacent lattice points `a b` and
`c d` the closed segments `adjSeg a b` and `adjSeg c d` agree exactly when the unordered pairs
`{a,b}` and `{c,d}` agree.  This is what lets the cycle decomposition of the wall graph be
translated into a statement about the closed segments.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

/-- The canonical (east/north oriented) unit step with endpoints `a` and `b`, for unit-adjacent
`a`, `b`. -/
def canon (a b : ℤ × ℤ) : (ℤ × ℤ) × (ℤ × ℤ) :=
  if b = (a.1 + 1, a.2) then (a, b)
  else if b = (a.1 - 1, a.2) then (b, a)
  else if b = (a.1, a.2 + 1) then (a, b)
  else (b, a)

lemma canon_east {a b : ℤ × ℤ} (h : b = (a.1 + 1, a.2)) : canon a b = (a, b) := by
  simp only [canon, if_pos h]

lemma canon_west {a b : ℤ × ℤ} (h : b = (a.1 - 1, a.2)) : canon a b = (b, a) := by
  have h1 : ¬ (b = (a.1 + 1, a.2)) := by
    rw [h]; intro hc; simp only [Prod.mk.injEq] at hc; omega
  simp only [canon, if_neg h1, if_pos h]

lemma canon_north {a b : ℤ × ℤ} (h : b = (a.1, a.2 + 1)) : canon a b = (a, b) := by
  have h1 : ¬ (b = (a.1 + 1, a.2)) := by
    rw [h]; intro hc; simp only [Prod.mk.injEq] at hc; omega
  have h2 : ¬ (b = (a.1 - 1, a.2)) := by
    rw [h]; intro hc; simp only [Prod.mk.injEq] at hc; omega
  simp only [canon, if_neg h1, if_neg h2, if_pos h]

lemma canon_south {a b : ℤ × ℤ} (h : b = (a.1, a.2 - 1)) : canon a b = (b, a) := by
  have h1 : ¬ (b = (a.1 + 1, a.2)) := by
    rw [h]; intro hc; simp only [Prod.mk.injEq] at hc; omega
  have h2 : ¬ (b = (a.1 - 1, a.2)) := by
    rw [h]; intro hc; simp only [Prod.mk.injEq] at hc; omega
  have h3 : ¬ (b = (a.1, a.2 + 1)) := by
    rw [h]; intro hc; simp only [Prod.mk.injEq] at hc; omega
  simp only [canon, if_neg h1, if_neg h2, if_neg h3]

lemma canon_spec {a b : ℤ × ℤ} (h : IsUnitAdj a b) :
    ((canon a b).1 = a ∧ (canon a b).2 = b) ∨ ((canon a b).1 = b ∧ (canon a b).2 = a) := by
  rcases h with h | h | h | h
  · left; rw [canon_east h]; exact ⟨rfl, rfl⟩
  · right; rw [canon_west h]; exact ⟨rfl, rfl⟩
  · left; rw [canon_north h]; exact ⟨rfl, rfl⟩
  · right; rw [canon_south h]; exact ⟨rfl, rfl⟩

lemma canon_unitStep {a b : ℤ × ℤ} (h : IsUnitAdj a b) : IsUnitStep (canon a b) := by
  rcases h with h | h | h | h
  · rw [canon_east h]; exact Or.inl h
  · rw [canon_west h]
    exact Or.inl (by rw [h]; ext <;> simp)
  · rw [canon_north h]; exact Or.inr h
  · rw [canon_south h]
    exact Or.inr (by rw [h]; ext <;> simp)

lemma adjSeg_canon {a b : ℤ × ℤ} (h : IsUnitAdj a b) : adjSeg a b = stepSeg (canon a b) := by
  rcases h with h | h | h | h
  · rw [canon_east h, stepSeg_of_eq_east h, h, adjSeg_east_wg]
  · have ha : a = (b.1 + 1, b.2) := by rw [h]; ext <;> simp <;> ring
    rw [canon_west h, stepSeg_of_eq_east ha, adjSeg_comm, ha, adjSeg_east_wg]
  · rw [canon_north h, stepSeg_of_eq_north h, h, adjSeg_north_wg]
  · have ha : a = (b.1, b.2 + 1) := by rw [h]; ext <;> simp <;> ring
    rw [canon_south h, stepSeg_of_eq_north ha, adjSeg_comm, ha, adjSeg_north_wg]

lemma hSeg_inj {u v : ℤ × ℤ} (h : hSeg u = hSeg v) : u = v := by
  have h1 : lpt u ∈ hSeg v := by rw [← h]; exact lpt_mem_hSeg u
  have h2 : lpt (u.1 + 1, u.2) ∈ hSeg v := by rw [← h]; exact lpt_add_one_mem_hSeg u
  rw [mem_hSeg] at h1 h2
  obtain ⟨h1a, h1b, h1c⟩ := h1
  obtain ⟨h2a, h2b, h2c⟩ := h2
  have e1 : u.2 = v.2 := by simp only [lpt_im] at h1a; exact_mod_cast h1a
  have e2 : v.1 ≤ u.1 := by simp only [lpt_re] at h1b; exact_mod_cast h1b
  have e3 : u.1 + 1 ≤ v.1 + 1 := by
    have h2c' : ((u.1 : ℝ) + 1) ≤ ((v.1 : ℝ) + 1) := by simpa using h2c
    exact_mod_cast h2c'
  ext <;> omega

lemma vSeg_inj {u v : ℤ × ℤ} (h : vSeg u = vSeg v) : u = v := by
  have h1 : lpt u ∈ vSeg v := by rw [← h]; exact lpt_mem_vSeg u
  have h2 : lpt (u.1, u.2 + 1) ∈ vSeg v := by rw [← h]; exact lpt_add_one_mem_vSeg u
  rw [mem_vSeg] at h1 h2
  obtain ⟨h1a, h1b, h1c⟩ := h1
  obtain ⟨h2a, h2b, h2c⟩ := h2
  have e1 : u.1 = v.1 := by simp only [lpt_re] at h1a; exact_mod_cast h1a
  have e2 : v.2 ≤ u.2 := by simp only [lpt_im] at h1b; exact_mod_cast h1b
  have e3 : u.2 + 1 ≤ v.2 + 1 := by
    have h2c' : ((u.2 : ℝ) + 1) ≤ ((v.2 : ℝ) + 1) := by simpa using h2c
    exact_mod_cast h2c'
  ext <;> omega

lemma hSeg_ne_vSeg (u v : ℤ × ℤ) : hSeg u ≠ vSeg v := by
  intro h
  have h1 : lpt u ∈ vSeg v := by rw [← h]; exact lpt_mem_hSeg u
  have h2 : lpt (u.1 + 1, u.2) ∈ vSeg v := by rw [← h]; exact lpt_add_one_mem_hSeg u
  rw [mem_vSeg] at h1 h2
  have e1 : u.1 = v.1 := by simp only [lpt_re] at h1; exact_mod_cast h1.1
  have e2 : u.1 + 1 = v.1 := by simp only [lpt_re] at h2; exact_mod_cast h2.1
  omega

lemma stepSeg_inj {e e' : (ℤ × ℤ) × (ℤ × ℤ)} (he : IsUnitStep e) (he' : IsUnitStep e')
    (h : stepSeg e = stepSeg e') : e = e' := by
  rcases he with he | he <;> rcases he' with he' | he'
  · rw [stepSeg_of_eq_east he, stepSeg_of_eq_east he'] at h
    have h1 : e.1 = e'.1 := hSeg_inj h
    have h2 : e.2 = e'.2 := by rw [he, he', h1]
    exact Prod.ext h1 h2
  · have hc := h
    rw [stepSeg_of_eq_east he, stepSeg_of_eq_north he'] at hc
    exact absurd hc (hSeg_ne_vSeg e.1 e'.1)
  · have hc := h
    rw [stepSeg_of_eq_east he', stepSeg_of_eq_north he] at hc
    exact absurd hc.symm (hSeg_ne_vSeg e'.1 e.1)
  · rw [stepSeg_of_eq_north he, stepSeg_of_eq_north he'] at h
    have h1 : e.1 = e'.1 := vSeg_inj h
    have h2 : e.2 = e'.2 := by rw [he, he', h1]
    exact Prod.ext h1 h2

theorem adjSeg_eq_iff {a b c d : ℤ × ℤ} (hab : IsUnitAdj a b) (hcd : IsUnitAdj c d) :
    adjSeg a b = adjSeg c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have h' : stepSeg (canon a b) = stepSeg (canon c d) := by
      rw [← adjSeg_canon hab, ← adjSeg_canon hcd, h]
    have hc : canon a b = canon c d := stepSeg_inj (canon_unitStep hab) (canon_unitStep hcd) h'
    rcases canon_spec hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases canon_spec hcd with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inl ⟨h1.symm.trans ((congrArg Prod.fst hc).trans h3),
          h2.symm.trans ((congrArg Prod.snd hc).trans h4)⟩
      · exact Or.inr ⟨h1.symm.trans ((congrArg Prod.fst hc).trans h3),
          h2.symm.trans ((congrArg Prod.snd hc).trans h4)⟩
    · rcases canon_spec hcd with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inr ⟨h2.symm.trans ((congrArg Prod.snd hc).trans h4),
          h1.symm.trans ((congrArg Prod.fst hc).trans h3)⟩
      · exact Or.inl ⟨h2.symm.trans ((congrArg Prod.snd hc).trans h4),
          h1.symm.trans ((congrArg Prod.fst hc).trans h3)⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact adjSeg_comm _ _

end Work.HornSC.CellBoundaryJordan
