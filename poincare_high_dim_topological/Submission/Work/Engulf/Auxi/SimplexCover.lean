import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Basic

/-!
# A9 aux: a simplex is not the union of finitely many of its proper sub-simplices

`Work.Engulf.simp_cover`: if the simplex on a face `s` of a complex `K` is covered by finitely many
faces of `K`, then it is contained in one of them.  This is the "relative interior" argument in the
form area A9 (`Submission/Work/NOTES_LEAD_poincare_engulf.md` §8, E2) consumes it.

The proof uses the barycentre of `s` (all barycentric coordinates positive) together with the
uniqueness of the barycentric coordinates, which follows from `K.indep`.
-/

open Set Metric PL Finset

namespace Work.Engulf

variable {N : ℕ}

/-- The barycentre of a finite vertex set. -/
noncomputable def bary (s : Finset (E N)) : E N := ((s.card : ℝ))⁻¹ • ∑ v ∈ s, v

theorem bary_mem_simp {s : Finset (E N)} (hs : s.Nonempty) : bary s ∈ simp s := by
  classical
  have hcard : (s.card : ℝ) ≠ 0 := by simp [Finset.card_ne_zero.2 hs]
  rw [simp, Finset.mem_convexHull']
  refine ⟨fun v => if v ∈ s then ((s.card : ℝ))⁻¹ else 0, ?_, ?_, ?_⟩
  · intro y hy
    by_cases h : y ∈ s <;> simp [h, inv_nonneg]
  · rw [Finset.sum_congr rfl (fun x hx =>
      show (if x ∈ s then ((s.card : ℝ))⁻¹ else 0) = ((s.card : ℝ))⁻¹ by simp [hx])]
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  · rw [Finset.sum_congr rfl (fun x hx =>
      show (if x ∈ s then ((s.card : ℝ))⁻¹ else 0) • x = ((s.card : ℝ))⁻¹ • x by simp [hx])]
    rw [← Finset.smul_sum]
    rfl

/-- If the barycentre of a face `s` lies in the simplex on a face `t`, then `s ⊆ t`. -/
theorem bary_mem_simp_subset {K : Cx N} {s t : Finset (E N)} (hs : s ∈ K.faces)
    (ht : t ∈ K.faces) (h : bary s ∈ simp t) : s ⊆ t := by
  classical
  have hsne : s.Nonempty := K.nonempty_of_mem_faces hs
  have hst : bary s ∈ simp (s ∩ t) := by
    rw [← simp_inter hs ht]
    exact ⟨bary_mem_simp hsne, h⟩
  obtain ⟨ν, hν0, hν1, hν2⟩ := (Finset.mem_convexHull'.1 hst)
  set lam : E N → ℝ := fun v => if v ∈ s then ((s.card : ℝ))⁻¹ else 0 with hlam
  set ν' : E N → ℝ := fun v => if v ∈ s ∩ t then ν v else 0 with hν'
  have hzero_out : ∀ x ∈ s, x ∉ s ∩ t → ν' x = 0 := by
    intro x hx hx'; rw [hν']; simp [hx']
  have hcongr : ∑ x ∈ s ∩ t, ν' x = ∑ x ∈ s ∩ t, ν x :=
    Finset.sum_congr rfl (fun x hx => by rw [hν']; simp [hx])
  have hcongr2 : ∑ x ∈ s ∩ t, ν' x • x = ∑ x ∈ s ∩ t, ν x • x :=
    Finset.sum_congr rfl (fun x hx => by rw [hν']; simp [hx])
  have hsum1 : ∑ v ∈ s, lam v = ∑ v ∈ s, ν' v := by
    have hL : ∑ v ∈ s, lam v = 1 := by
      rw [Finset.sum_congr rfl (fun x hx =>
        show lam x = ((s.card : ℝ))⁻¹ by rw [hlam]; simp [hx])]
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp
    have hR : ∑ v ∈ s, ν' v = 1 := by
      rw [← Finset.sum_subset (s₁ := s ∩ t) (s₂ := s) Finset.inter_subset_left hzero_out,
        hcongr, hν1]
    rw [hL, hR]
  have hsum2 : ∑ v ∈ s, lam v • v = ∑ v ∈ s, ν' v • v := by
    have hL : ∑ v ∈ s, lam v • v = bary s := by
      have hstep : ∑ v ∈ s, lam v • v = ∑ v ∈ s, ((s.card : ℝ))⁻¹ • v :=
        Finset.sum_congr rfl (fun x hx => by rw [hlam]; simp [hx])
      rw [hstep, ← Finset.smul_sum, bary]
    have hR : ∑ v ∈ s, ν' v • v = bary s := by
      rw [← Finset.sum_subset (s₁ := s ∩ t) (s₂ := s) Finset.inter_subset_left
        (fun x hx hx' => by rw [hzero_out x hx hx', zero_smul])]
      rw [hcongr2, hν2]
    rw [hL, hR]
  intro v hv
  have hv' := AffineIndependent.eq_of_sum_eq_sum_subtype (K.indep hs) hsum1 hsum2 v hv
  have hpos : (0 : ℝ) < lam v := by
    have : lam v = ((s.card : ℝ))⁻¹ := by rw [hlam]; simp [hv]
    rw [this]
    exact inv_pos.2 (Nat.cast_pos.2 (Finset.card_pos.2 hsne))
  have hzero : lam v ≠ 0 := ne_of_gt hpos
  by_contra hvt
  apply hzero
  rw [hv', hν']
  simp [Finset.mem_inter, hv, hvt]

/-- **`simp_cover`**: a face of a complex covered by finitely many faces of the complex lies in one
of them. -/
theorem simp_cover {K : Cx N} {T : Finset (Finset (E N))} (hT : ∀ t ∈ T, t ∈ K.faces)
    {s : Finset (E N)} (hs : s ∈ K.faces) (hcov : simp s ⊆ ⋃ t ∈ T, simp t) :
    ∃ t ∈ T, simp s ⊆ simp t := by
  classical
  have hsne : s.Nonempty := K.nonempty_of_mem_faces hs
  have : bary s ∈ ⋃ t ∈ T, simp t := hcov (bary_mem_simp hsne)
  rw [mem_iUnion₂] at this
  obtain ⟨t, htT, hbt⟩ := this
  exact ⟨t, htT, (K.face_subset_face_iff hs (hT t htT)).2 (bary_mem_simp_subset hs (hT t htT) hbt)⟩

end Work.Engulf
