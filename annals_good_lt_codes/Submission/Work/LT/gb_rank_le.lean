import Mathlib
import Submission.Work.LT.good_base_defs
import Submission.Work.LT.gb_rank_defs
import Submission.Work.LT.gb_range_matVecLin
import Submission.Work.LT.gb_range_matVecLin_transpose
import Submission.Work.LT.gb_dot_matVec_transpose
import Submission.Work.LT.gb_ker_matVecLin_transpose
import Submission.Work.LT.gb_dot_matVec_eq_zero
import Submission.Work.LT.gb_finrank_map_add_finrank_inf_ker

namespace Work.LT

namespace GB

variable {D : ℕ}

/-- The transpose of a matrix `x = a + b ∈ CA ⊞ CB` maps the orthogonal complement of `CA`
(intersected with the domain) into `CB ∩ rowSpan x`: this is the pairing step of
Kalachev--Panteleev Lemma 8. -/
lemma map_orth_le {CA CB : Submodule (ZMod 2) (Fin D → ZMod 2)}
    {x a b : Fin D × Fin D → ZMod 2} (hx : x = a + b)
    (ha : IsColwise CA a) (hb : IsRowwise CB b) :
    ((dotForm D).orthogonal CA).map (matVecLin (matTranspose x)) ≤ CB ⊓ rowSpan x := by
  refine le_inf ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    intro u hu
    rw [Submodule.mem_comap]
    have hmem : matVecLin (matTranspose x) u ∈ (dotForm D).orthogonal ((dotForm D).orthogonal CB) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro v hv
      rw [dotForm_apply, matVecLin_apply, dot_comm, gb_dot_matVec_transpose]
      exact gb_dot_matVec_eq_zero hx ha hb hu hv
    rwa [LinearMap.BilinForm.orthogonal_orthogonal (dotForm_nondegenerate D) (dotForm_isRefl D)]
      at hmem
  · rw [← gb_range_matVecLin_transpose]
    refine Submodule.map_le_iff_le_comap.mpr ?_
    intro u _
    exact Submodule.mem_comap.mpr (LinearMap.mem_range.mpr ⟨u, rfl⟩)

/-- The dimension count of Kalachev--Panteleev Lemma 8: if `xᵀ` maps the orthogonal complement
of `CA` into `CB ∩ rowSpan x`, then
`matRank x ≤ dim (CA ∩ colSpan x) + dim (CB ∩ rowSpan x)`. -/
lemma rank_le_of_map_le {CA CB : Submodule (ZMod 2) (Fin D → ZMod 2)}
    (x : Fin D × Fin D → ZMod 2)
    (h : ((dotForm D).orthogonal CA).map (matVecLin (matTranspose x)) ≤ CB ⊓ rowSpan x) :
    matRank x ≤ frk (CA ⊓ colSpan x) + frk (CB ⊓ rowSpan x) := by
  have hle : frk (((dotForm D).orthogonal CA).map (matVecLin (matTranspose x)))
      ≤ frk (CB ⊓ rowSpan x) := Submodule.finrank_mono h
  have hrn : frk (((dotForm D).orthogonal CA).map (matVecLin (matTranspose x)))
      + frk ((dotForm D).orthogonal CA ⊓ LinearMap.ker (matVecLin (matTranspose x)))
      = frk ((dotForm D).orthogonal CA) :=
    gb_finrank_map_add_finrank_inf_ker (matVecLin (matTranspose x)) ((dotForm D).orthogonal CA)
  have hker : LinearMap.ker (matVecLin (matTranspose x)) = (dotForm D).orthogonal (colSpan x) :=
    gb_ker_matVecLin_transpose x
  have hsup : (dotForm D).orthogonal CA ⊓ (dotForm D).orthogonal (colSpan x)
      = (dotForm D).orthogonal (CA ⊔ colSpan x) :=
    (Submodule.orthogonalBilin_sup (B := dotForm D) CA (colSpan x)).symm
  have h1 : frk (((dotForm D).orthogonal CA).map (matVecLin (matTranspose x)))
      + frk ((dotForm D).orthogonal (CA ⊔ colSpan x))
      = frk ((dotForm D).orthogonal CA) := by
    rw [← hsup, ← hker]
    exact hrn
  have horth1 : frk ((dotForm D).orthogonal CA) + frk CA = D := by
    have hh : frk ((dotForm D).orthogonal CA) = D - frk CA := by
      have h2 := LinearMap.BilinForm.finrank_orthogonal (dotForm_nondegenerate D) CA
      rw [Module.finrank_fin_fun] at h2
      exact h2
    have hcD : frk CA ≤ D := by
      have h3 := Submodule.finrank_le (R := ZMod 2) (M := Fin D → ZMod 2) CA
      rw [Module.finrank_fin_fun] at h3
      exact h3
    omega
  have horth2 : frk ((dotForm D).orthogonal (CA ⊔ colSpan x)) + frk (CA ⊔ colSpan x) = D := by
    have hh : frk ((dotForm D).orthogonal (CA ⊔ colSpan x)) = D - frk (CA ⊔ colSpan x) := by
      have h2 := LinearMap.BilinForm.finrank_orthogonal (dotForm_nondegenerate D) (CA ⊔ colSpan x)
      rw [Module.finrank_fin_fun] at h2
      exact h2
    have hcD : frk (CA ⊔ colSpan x) ≤ D := by
      have h3 := Submodule.finrank_le (R := ZMod 2) (M := Fin D → ZMod 2) (CA ⊔ colSpan x)
      rw [Module.finrank_fin_fun] at h3
      exact h3
    omega
  have hgr : frk (CA ⊔ colSpan x) + frk (CA ⊓ colSpan x) = frk CA + frk (colSpan x) :=
    Submodule.finrank_sup_add_finrank_inf_eq CA (colSpan x)
  have hmono : frk (CA ⊓ colSpan x) ≤ frk (colSpan x) := Submodule.finrank_mono inf_le_right
  have hmono2 : frk CA ≤ frk (CA ⊔ colSpan x) := Submodule.finrank_mono le_sup_left
  have hfin : matRank x = frk (colSpan x) := rfl
  omega

end GB

variable {D : ℕ}

/-- Kalachev--Panteleev Lemma 8: for `x ∈ CA ⊞ CB` the rank of `x` is at most the dimension of `CA ∩ column space of x` plus the dimension of `CB ∩ row space of x`. -/
theorem gb_rank_le {D : ℕ} (CA CB : Submodule (ZMod 2) (Fin D → ZMod 2))
    (x : Fin D × Fin D → ZMod 2) (hx : x ∈ GB.prodSum CA CB) :
    GB.matRank x ≤ GB.frk (CA ⊓ GB.colSpan x) + GB.frk (CB ⊓ GB.rowSpan x) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (GB.mem_prodSum x).1 hx
  have hca : GB.IsColwise CA a := (GB.mem_colCode a).1 ha
  have hcb : GB.IsRowwise CB b := (GB.mem_rowCode b).1 hb
  exact GB.rank_le_of_map_le (a + b) (GB.map_orth_le rfl hca hcb)

end Work.LT
