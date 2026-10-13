import Mathlib
import Submission.Work.WilCrux.Clean.AccSetDefs

namespace Work.WilCrux.Clean

/-- On the product `Fin b → ℝ` (with its sup-norm, Mathlib's default on finite products), the
norm is `< t` exactly when every coordinate is, *provided* the index set is nonempty. -/
lemma norm_lt_iff_forall_abs_lt {b : ℕ} (hb : 0 < b) (z : Fin b → ℝ) (t : ℝ) :
    (∀ j, |z j| < t) ↔ ‖z‖ < t := by
  constructor
  · intro h
    -- nonemptiness of `Fin b` supplies a coordinate, whence `0 < t`
    have ht : 0 < t := lt_of_le_of_lt (abs_nonneg _) (h ⟨0, hb⟩)
    refine (pi_norm_lt_iff ht).2 (fun j => ?_)
    simpa [Real.norm_eq_abs] using h j
  · intro h
    have ht : 0 < t := lt_of_le_of_lt (norm_nonneg z) h
    intro j
    simpa [Real.norm_eq_abs] using (pi_norm_lt_iff ht).1 h j

theorem MemQset {a b : ℕ} {E : Set (Fin (a+b) → ℝ)} (hb : 0 < b) (v : Fin a → ℝ) (t : ℝ)
    (z : Fin b → ℝ) :
    Fin.append (Fin.snoc v t) z ∈ Work.WilCrux.Clean.Qset a b E ↔
      (Fin.append v z ∈ E ∧ z ≠ 0 ∧ ‖z‖ < t) := by
  have hz0 : (fun j : Fin b => Fin.append (Fin.snoc v t) z (zIdx a b j)) = z :=
    funext fun j => append_snoc_zIdx a b v t z j
  have hcomp : (Fin.append (Fin.snoc v t) z) ∘ (iIdx a b) = Fin.append v z :=
    append_snoc_comp_iIdx a b v t z
  simp only [Work.WilCrux.Clean.Qset, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [hcomp, hz0, append_snoc_dIdx]
  simp only [append_snoc_zIdx]
  constructor
  · rintro ⟨⟨hE, _ht⟩, hzne, hlt⟩
    exact ⟨hE, hzne, (norm_lt_iff_forall_abs_lt hb z t).1 hlt⟩
  · rintro ⟨hE, hzne, hn⟩
    have hlt := (norm_lt_iff_forall_abs_lt hb z t).2 hn
    exact ⟨⟨hE, lt_of_le_of_lt (abs_nonneg _) (hlt ⟨0, hb⟩)⟩, hzne, hlt⟩

end Work.WilCrux.Clean
