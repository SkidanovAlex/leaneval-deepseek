import Mathlib
import Submission.Work.RHContract.A.regionII.caC1_cert_defs

namespace Work.RHContract.A.regionII

/-- Every first component occurring in `tailsFrom l acc` is an element of `l`. -/
lemma mem_fst_tailsFrom {l : List ℕ} {acc p t : ℕ}
    (h : (p, t) ∈ tailsFrom l acc) : p ∈ l := by
  induction l generalizing acc with
  | nil => simp [tailsFrom] at h
  | cons a as ih =>
    rw [tailsFrom] at h
    rcases List.mem_cons.mp h with h | h
    · rw [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2
      simp
    · exact List.mem_cons_of_mem _ (ih h)

/-- The accumulator value paired with `p` is the initial accumulator plus the sum of `c1num`
over all cutoffs of `l` that are strictly larger than `p`. -/
theorem tailsFrom_mem (l : List ℕ) (hdec : l.Pairwise (· > ·)) (acc : ℕ)
    {p t : ℕ} (h : (p, t) ∈ Work.RHContract.A.regionII.tailsFrom l acc) :
    t = acc + ((l.filter (fun q => p < q)).map Work.RHContract.A.regionII.c1num).sum := by
  induction l generalizing acc with
  | nil => simp [tailsFrom] at h
  | cons a as ih =>
    rw [tailsFrom] at h
    rw [List.pairwise_cons] at hdec
    obtain ⟨hlt, hdec'⟩ := hdec
    rcases List.mem_cons.mp h with h | h
    · obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
      subst h1; subst h2
      have hfil : (p :: as).filter (fun q => p < q) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro b hb
        rw [List.mem_cons] at hb
        rcases hb with rfl | hb
        · simp
        · have : ¬ (p < b) := by have := hlt b hb; omega
          simp [this]
      rw [hfil]
      simp
    · have hp : p ∈ as := mem_fst_tailsFrom h
      have hpa : p < a := hlt p hp
      rw [ih hdec' (acc + c1num a) h]
      have hfil : (a :: as).filter (fun q => p < q) = a :: as.filter (fun q => p < q) := by
        apply List.filter_cons_of_pos
        simp [hpa]
      rw [hfil, List.map_cons, List.sum_cons]
      omega

end Work.RHContract.A.regionII
