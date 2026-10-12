import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseK15.hatChiSq_double_sum_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseK15

theorem hatChiSq_form_psd_guarded {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {F : Work.BoseB7.FockData Mode}
    {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode} {K₀ : ℝ}
    (h : Work.BoseK15.K15Input K₀ F T E) :
    ∀ (S : Finset Mode) (c : Mode → ℝ) (v : Mode → F.H),
      (∀ s ∈ S, c s ≠ 0 → E.fL s ≠ 0) →
      0 ≤ ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s) := by
  classical
  intro S c v hguard
  -- Only the modes with `c s ≠ 0` contribute; on those the guard gives `f_L s ≠ 0`,
  -- and the guarded additivity of the labels identifies `χ̂²(s' - s)` with
  -- `χ̂²(ℓ·kmom s' - ℓ·kmom s)`.
  set T : Finset Mode := S.filter (fun s => c s ≠ 0) with hT
  have hTsub : T ⊆ S := Finset.filter_subset _ _
  have hmem : ∀ s ∈ T, c s ≠ 0 := fun s hs => (Finset.mem_filter.mp hs).2
  have hfL : ∀ s ∈ T, E.fL s ≠ 0 := fun s hs => hguard s (hTsub hs) (hmem s hs)
  -- Drop the modes with `c s = 0` from the outer sum.
  have houter :
      (∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s))
        = ∑ s ∈ T, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s) := by
    refine (Finset.sum_subset hTsub ?_).symm
    intro s hsS hsT
    have hc : c s = 0 := by
      by_contra hc
      exact hsT (Finset.mem_filter.mpr ⟨hsS, hc⟩)
    simp [hc]
  -- Drop the modes with `c s' = 0` from the inner sum.
  have hinner : ∀ s ∈ T,
      (∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s))
        = ∑ s' ∈ T, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s) := by
    intro s _
    refine (Finset.sum_subset hTsub ?_).symm
    intro s' hs'S hs'T
    have hc : c s' = 0 := by
      by_contra hc
      exact hs'T (Finset.mem_filter.mpr ⟨hs'S, hc⟩)
    simp [hc]
  -- Replace `E.hatChiSq (s' - s)` by the corpus kernel at the momentum difference.
  have hrewrite :
      (∑ s ∈ T, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s))
        = ∑ s ∈ T, ∑ s' ∈ T,
            c s * c s' * corpusBox.hatChiSq ((E.ell • h.kmom s') - (E.ell • h.kmom s))
              * F.bp (v s') (v s) := by
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hinner s hs]
    refine Finset.sum_congr rfl fun s' hs' => ?_
    have hadd : h.kmom (s' - s) = h.kmom s' - h.kmom s :=
      h.kmom_add_inner s' s (hfL s' hs') (hfL s hs)
    rw [h.hatChiSq_eq (s' - s), hadd, smul_sub]
  rw [houter, hrewrite]
  exact hatChiSq_double_sum_nonneg F (fun s => E.ell • h.kmom s) T c v

end Work.BoseK15
