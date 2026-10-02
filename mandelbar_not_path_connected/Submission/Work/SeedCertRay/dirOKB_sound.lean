import Mathlib
import Submission.Work.SeedCertRay.Q
import Submission.Work.SeedCertRay.disk_mem_halfplane

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.SeedCertRay.dirOKB_sound` — soundness of the half-plane test (D2) (generated)
-/
namespace Work.SeedCertRay

set_option maxHeartbeats 2000000

/-- **Soundness of the (D2) mantissa test `hpB`.** -/
theorem hpB_Q (p q cx cy cr : ℤ) (h : hpB p q cx cy cr = true) :
    (|(Q p : ℚ)| + |(Q q : ℚ)|) * Q cr < Q p * Q cx + Q q * Q cy := by
  have hZ : (iabs p + iabs q) * cr < p * cx + q * cy := by
    simpa [hpB] using h
  rw [iabs, iabs, ← abs_eq_max_neg (a := p), ← abs_eq_max_neg (a := q)] at hZ
  have hQ : ((|p| : ℚ) + (|q| : ℚ)) * (cr : ℚ)
      < (p : ℚ) * (cx : ℚ) + (q : ℚ) * (cy : ℚ) := by
    exact_mod_cast hZ
  rw [Q, Q, Q, Q, Q, abs_div, abs_of_pos MS_pos, abs_div, abs_of_pos MS_pos]
  field_simp
  rw [div_lt_div_iff_of_pos_right (pow_pos MS_pos 2)]
  exact hQ

/-- One sub-disk of a `dirOKB` block lies in the corresponding open half-plane. -/
theorem dskOf_subset_halfplane (dl t : List ℤ) (j i : ℕ)
    (h : hpB (gI dl (2*j)) (gI dl (2*j+1))
          (gI t (3*(j*NC+i))) (gI t (3*(j*NC+i)+1)) (gI t (3*(j*NC+i)+2)) = true) :
    (dskOf t (j*NC+i)).toSet ⊆ halfplane (Q (gI dl (2*j)), Q (gI dl (2*j+1))) := by
  have hh := hpB_Q (gI dl (2*j)) (gI dl (2*j+1)) (gI t (3*(j*NC+i))) (gI t (3*(j*NC+i)+1))
    (gI t (3*(j*NC+i)+2)) h
  have hh2 : (|Q (gI dl (2*j))| + |Q (gI dl (2*j+1))|) * (dskOf t (j*NC+i)).r
      < Q (gI dl (2*j)) * (dskOf t (j*NC+i)).cx + Q (gI dl (2*j+1)) * (dskOf t (j*NC+i)).cy := by
    simpa only [dskOf] using hh
  exact disk_mem_halfplane (dskOf t (j*NC+i)) (Q (gI dl (2*j))) (Q (gI dl (2*j+1))) hh2

theorem dirOKB_sound (dl t s : List ℤ) (j : ℕ)
    (h : dirOKB dl t s (j % 10) = true) :
    (∀ i : Fin NC, (dskOf t ((j % 10) * NC + i.val)).toSet
        ⊆ halfplane (Q (gI dl (2 * (j % 10))), Q (gI dl (2 * (j % 10) + 1))))
    ∧ (∀ i : Fin NC, (dskOf s ((j % 10) * NC + i.val)).toSet
        ⊆ halfplane (Q (gI dl (2 * (j % 10))), Q (gI dl (2 * (j % 10) + 1)))) := by
  have hh := h
  simp only [dirOKB, Bool.and_eq_true, and_assoc] at hh
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hh
  refine ⟨fun i => ?_, fun i => ?_⟩

  · fin_cases i
    · exact dskOf_subset_halfplane dl t (j % 10) 0 (by simpa using h0)
    · exact dskOf_subset_halfplane dl t (j % 10) 1 (by simpa using h1)
    · exact dskOf_subset_halfplane dl t (j % 10) 2 (by simpa using h2)
    · exact dskOf_subset_halfplane dl t (j % 10) 3 (by simpa using h3)
    · exact dskOf_subset_halfplane dl t (j % 10) 4 (by simpa using h4)
    · exact dskOf_subset_halfplane dl t (j % 10) 5 (by simpa using h5)
  · fin_cases i
    · exact dskOf_subset_halfplane dl s (j % 10) 0 (by simpa using h6)
    · exact dskOf_subset_halfplane dl s (j % 10) 1 (by simpa using h7)
    · exact dskOf_subset_halfplane dl s (j % 10) 2 (by simpa using h8)
    · exact dskOf_subset_halfplane dl s (j % 10) 3 (by simpa using h9)
    · exact dskOf_subset_halfplane dl s (j % 10) 4 (by simpa using h10)
    · exact dskOf_subset_halfplane dl s (j % 10) 5 (by simpa using h11)

end Work.SeedCertRay
