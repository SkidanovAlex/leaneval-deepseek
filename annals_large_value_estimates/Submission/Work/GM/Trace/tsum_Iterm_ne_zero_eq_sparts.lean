import Mathlib
import Submission.Work.GM.Trace.Defs

namespace Work.GM.Trace

open Classical

/-!
# GM (5.5): splitting `∑'_{m ≠ 0} I_m` into `S₁ + S₂ + S₃`

`Submission.GM.Spart k N W = ∑'_{m : nzCount m = k} Iterm N W m`, and `nzCount m = 0 ↔ m = 0`,
so the nonzero `m ∈ ℤ³` split disjointly according to the number of nonzero coordinates
(`nzCount m ∈ {1,2,3}`).  This file records the resulting identity
`∑'_{m ≠ 0} I_m = S₁ + S₂ + S₃`, which GM use to write the cubic trace as `S₁+S₂+S₃`.
-/

/-- `nzCount m = 0` iff `m = 0`. -/
private lemma nzCount_eq_zero_iff (m : ℤ × ℤ × ℤ) : Submission.GM.nzCount m = 0 ↔ m = 0 := by
  constructor
  · intro h
    have h1 : m.1 = 0 := by
      by_contra hne
      have : 1 ≤ Submission.GM.nzCount m := by
        simp only [Submission.GM.nzCount]; rw [if_pos hne]; omega
      omega
    have h2 : m.2.1 = 0 := by
      by_contra hne
      have : 1 ≤ Submission.GM.nzCount m := by
        simp only [Submission.GM.nzCount]; rw [if_pos hne]; omega
      omega
    have h3 : m.2.2 = 0 := by
      by_contra hne
      have : 1 ≤ Submission.GM.nzCount m := by
        simp only [Submission.GM.nzCount]; rw [if_pos hne]; omega
      omega
    exact Prod.ext h1 (Prod.ext h2 h3)
  · intro h
    rw [h]; simp [Submission.GM.nzCount]

/-- `nzCount` never exceeds `3`. -/
private lemma nzCount_le_three (m : ℤ × ℤ × ℤ) : Submission.GM.nzCount m ≤ 3 := by
  simp only [Submission.GM.nzCount]; split_ifs <;> omega

/-- A nonzero `m ∈ ℤ³` has exactly `1`, `2` or `3` nonzero coordinates. -/
private lemma nzCount_mem_of_ne_zero {m : ℤ × ℤ × ℤ} (hm : m ≠ 0) :
    Submission.GM.nzCount m = 1 ∨ Submission.GM.nzCount m = 2 ∨ Submission.GM.nzCount m = 3 := by
  have h1 : 1 ≤ Submission.GM.nzCount m := by
    by_contra h; push Not at h
    exact hm ((nzCount_eq_zero_iff m).1 (by omega))
  have h3 := nzCount_le_three m
  omega

/-- Pointwise decomposition of the indicator of `{m ≠ 0}` into the indicators of the
three sets `{nzCount = k}`, `k = 1, 2, 3`. -/
private lemma indicator_identity (f : ℤ × ℤ × ℤ → ℂ) :
    ∀ m : ℤ × ℤ × ℤ,
      (Set.indicator {p : ℤ × ℤ × ℤ | p ≠ 0} f) m
        = (Set.indicator {p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 1} f) m
          + (Set.indicator {p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 2} f) m
          + (Set.indicator {p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 3} f) m := by
  intro m
  rcases eq_or_ne m 0 with hm | hm
  · rw [hm]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    norm_num [Submission.GM.nzCount]
  · rw [Set.indicator_of_mem (show m ∈ {p : ℤ × ℤ × ℤ | p ≠ 0} from hm),
        Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
    simp only [Set.mem_ofPred_eq]
    rcases nzCount_mem_of_ne_zero hm with h | h | h
    · rw [if_pos h, if_neg (by omega), if_neg (by omega)]; ring
    · rw [if_neg (by omega), if_pos h, if_neg (by omega)]; ring
    · rw [if_neg (by omega), if_neg (by omega), if_pos h]; ring

/-- Summability of `f` over the subtype `s` gives summability of the indicator family
`s.indicator f` (which vanishes off `s`). -/
private lemma summable_indicator_of_summable_subtype (f : ℤ × ℤ × ℤ → ℂ) (s : Set (ℤ × ℤ × ℤ))
    (h : Summable (fun x : s => f x)) : Summable (s.indicator f) := by
  rw [← summable_subtype_and_compl (f := s.indicator f) (s := s)]
  exact ⟨(summable_congr (fun x => Set.indicator_of_mem x.2 f)).mpr h,
         (summable_congr (fun x => Set.indicator_of_notMem x.2 f)).mpr summable_zero⟩

-- GM (5.5): the sum of `I_m` over the nonzero `m ∈ ℤ³` splits into the three pieces `S₁+S₂+S₃`
-- according to the number of nonzero coordinates of `m` (`nzCount m = 0` iff `m = 0`).
theorem tsum_Iterm_ne_zero_eq_sparts (N : ℕ) (W : Finset ℝ)
    (h1 : Summable (fun m : {m : ℤ × ℤ × ℤ // Submission.GM.nzCount m = 1} =>
      Submission.GM.Iterm N W m))
    (h2 : Summable (fun m : {m : ℤ × ℤ × ℤ // Submission.GM.nzCount m = 2} =>
      Submission.GM.Iterm N W m))
    (h3 : Summable (fun m : {m : ℤ × ℤ × ℤ // Submission.GM.nzCount m = 3} =>
      Submission.GM.Iterm N W m)) :
    (∑' m : {m : ℤ × ℤ × ℤ // m ≠ 0}, Submission.GM.Iterm N W m)
      = Submission.GM.Spart 1 N W + Submission.GM.Spart 2 N W + Submission.GM.Spart 3 N W := by
  have hsum1 : Summable (({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 1}
      : Set (ℤ × ℤ × ℤ)).indicator (fun m => Submission.GM.Iterm N W m)) :=
    summable_indicator_of_summable_subtype _ _ h1
  have hsum2 : Summable (({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 2}
      : Set (ℤ × ℤ × ℤ)).indicator (fun m => Submission.GM.Iterm N W m)) :=
    summable_indicator_of_summable_subtype _ _ h2
  have hsum3 : Summable (({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 3}
      : Set (ℤ × ℤ × ℤ)).indicator (fun m => Submission.GM.Iterm N W m)) :=
    summable_indicator_of_summable_subtype _ _ h3
  have step1 : (∑' m : {m : ℤ × ℤ × ℤ // m ≠ 0}, Submission.GM.Iterm N W m)
      = ∑' m : ℤ × ℤ × ℤ, ({p : ℤ × ℤ × ℤ | p ≠ 0} : Set (ℤ × ℤ × ℤ)).indicator
          (fun m => Submission.GM.Iterm N W m) m :=
    tsum_subtype ({p : ℤ × ℤ × ℤ | p ≠ 0} : Set (ℤ × ℤ × ℤ)) (fun m => Submission.GM.Iterm N W m)
  have step2 : (∑' m : ℤ × ℤ × ℤ, ({p : ℤ × ℤ × ℤ | p ≠ 0} : Set (ℤ × ℤ × ℤ)).indicator
        (fun m => Submission.GM.Iterm N W m) m)
      = ∑' m : ℤ × ℤ × ℤ, (({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 1}
            : Set (ℤ × ℤ × ℤ)).indicator (fun m => Submission.GM.Iterm N W m) m
          + ({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 2}
            : Set (ℤ × ℤ × ℤ)).indicator (fun m => Submission.GM.Iterm N W m) m
          + ({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 3}
            : Set (ℤ × ℤ × ℤ)).indicator (fun m => Submission.GM.Iterm N W m) m) :=
    tsum_congr (indicator_identity _)
  have step3 : (∑' m : ℤ × ℤ × ℤ, (({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 1}
            : Set (ℤ × ℤ × ℤ)).indicator (fun m => Submission.GM.Iterm N W m) m
          + ({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 2}
            : Set (ℤ × ℤ × ℤ)).indicator (fun m => Submission.GM.Iterm N W m) m
          + ({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 3}
            : Set (ℤ × ℤ × ℤ)).indicator (fun m => Submission.GM.Iterm N W m) m))
      = (∑' m : ℤ × ℤ × ℤ, ({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 1}
            : Set (ℤ × ℤ × ℤ)).indicator (fun m => Submission.GM.Iterm N W m) m)
          + (∑' m : ℤ × ℤ × ℤ, ({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 2}
            : Set (ℤ × ℤ × ℤ)).indicator (fun m => Submission.GM.Iterm N W m) m)
          + (∑' m : ℤ × ℤ × ℤ, ({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 3}
            : Set (ℤ × ℤ × ℤ)).indicator (fun m => Submission.GM.Iterm N W m) m) := by
    rw [Summable.tsum_add (hsum1.add hsum2) hsum3, Summable.tsum_add hsum1 hsum2]
  have step4 : (∑' m : ℤ × ℤ × ℤ, ({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 1}
        : Set (ℤ × ℤ × ℤ)).indicator (fun m => Submission.GM.Iterm N W m) m)
      = Submission.GM.Spart 1 N W :=
    (tsum_subtype ({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 1} : Set (ℤ × ℤ × ℤ))
      (fun m => Submission.GM.Iterm N W m)).symm
  have step5 : (∑' m : ℤ × ℤ × ℤ, ({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 2}
        : Set (ℤ × ℤ × ℤ)).indicator (fun m => Submission.GM.Iterm N W m) m)
      = Submission.GM.Spart 2 N W :=
    (tsum_subtype ({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 2} : Set (ℤ × ℤ × ℤ))
      (fun m => Submission.GM.Iterm N W m)).symm
  have step6 : (∑' m : ℤ × ℤ × ℤ, ({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 3}
        : Set (ℤ × ℤ × ℤ)).indicator (fun m => Submission.GM.Iterm N W m) m)
      = Submission.GM.Spart 3 N W :=
    (tsum_subtype ({p : ℤ × ℤ × ℤ | Submission.GM.nzCount p = 3} : Set (ℤ × ℤ × ℤ))
      (fun m => Submission.GM.Iterm N W m)).symm
  rw [step1, step2, step3, step4, step5, step6]

end Work.GM.Trace
