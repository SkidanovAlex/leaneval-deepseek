import Mathlib

namespace Work.EKLC6Core

open scoped Classical

/-- Geometric core: if `a ≤ c < b` and `c < e` then the open intervals `(a,b)` and `(c,e)`
intersect.  (Used to turn disjointness of intervals into an ordering of their endpoints.) -/
private lemma Ioo_inter_nonempty {a b c e : ℝ} (h1 : a ≤ c) (h2 : c < b) (h3 : c < e) :
    (Set.Ioo a b ∩ Set.Ioo c e).Nonempty := by
  have hm : c < min b e := lt_min h2 h3
  refine ⟨(c + min b e) / 2, ?_, ?_⟩
  · simp only [Set.mem_Ioo]
    constructor
    · linarith
    · linarith [min_le_left b e]
  · simp only [Set.mem_Ioo]
    constructor
    · linarith
    · linarith [min_le_right b e]

private lemma main (f : ℝ → ℝ) (hf : Monotone f) :
    ∀ (T : Finset (ℝ × ℝ)) (c d : ℝ), c ≤ d → (∀ p ∈ T, c ≤ p.1) → (∀ p ∈ T, p.2 ≤ d) →
    (∀ p ∈ T, p.1 < p.2) →
    (∀ p ∈ T, ∀ q ∈ T, p ≠ q → Disjoint (Set.Ioo p.1 p.2) (Set.Ioo q.1 q.2)) →
    ∑ p ∈ T, (f p.2 - f p.1) ≤ f d - f c := by
  intro T
  induction T using Finset.strongInductionOn with
  | _ T ih =>
    intro c d hcd hc hdu hlt hdisj
    rcases Finset.eq_empty_or_nonempty T with rfl | hne
    · rw [Finset.sum_empty]
      exact sub_nonneg.mpr (hf hcd)
    · obtain ⟨p0, hp0T, hp0min⟩ := Finset.exists_min_image T (fun p : ℝ × ℝ => p.1) hne
      have hsub : T.erase p0 ⊂ T := Finset.erase_ssubset hp0T
      -- Every other interval lies to the right of `(p0.1, p0.2)`.
      have hge : ∀ p ∈ T.erase p0, p0.2 ≤ p.1 := by
        intro p hp
        rw [Finset.mem_erase] at hp
        obtain ⟨hpne, hpT⟩ := hp
        by_contra hcon
        have hcon' : p.1 < p0.2 := not_le.mp hcon
        have hle : p0.1 ≤ p.1 := hp0min p hpT
        have hltp : p.1 < p.2 := hlt p hpT
        have hdisjp : Disjoint (Set.Ioo p0.1 p0.2) (Set.Ioo p.1 p.2) :=
          hdisj p0 hp0T p hpT (fun h => hpne h.symm)
        exact (Set.not_disjoint_iff_nonempty_inter.mpr
          (Ioo_inter_nonempty hle hcon' hltp)) hdisjp
      have hres := ih (T.erase p0) hsub p0.2 d (hdu p0 hp0T) hge
        (fun p hp => hdu p (Finset.mem_of_mem_erase hp))
        (fun p hp => hlt p (Finset.mem_of_mem_erase hp))
        (fun p hp q hq hpq => hdisj p (Finset.mem_of_mem_erase hp)
          q (Finset.mem_of_mem_erase hq) hpq)
      rw [← Finset.add_sum_erase T (fun p => f p.2 - f p.1) hp0T]
      calc f p0.2 - f p0.1 + ∑ p ∈ T.erase p0, (f p.2 - f p.1)
          ≤ f p0.2 - f p0.1 + (f d - f p0.2) := by linarith
        _ = f d - f p0.1 := by ring
        _ ≤ f d - f c := by linarith [hf (hc p0 hp0T)]

theorem sum_sub_le_of_disjoint {f : ℝ → ℝ} (hf : Monotone f) {c d : ℝ} (hcd : c ≤ d)
    (T : Finset (ℝ × ℝ)) (hT : ∀ p ∈ T, c ≤ p.1 ∧ p.2 ≤ d)
    (hlt : ∀ p ∈ T, p.1 < p.2)
    (hd : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → Disjoint (Set.Ioo p.1 p.2) (Set.Ioo q.1 q.2)) :
    ∑ p ∈ T, (f p.2 - f p.1) ≤ f d - f c :=
  main f hf T c d hcd (fun p hp => (hT p hp).1) (fun p hp => (hT p hp).2) hlt hd

end Work.EKLC6Core
