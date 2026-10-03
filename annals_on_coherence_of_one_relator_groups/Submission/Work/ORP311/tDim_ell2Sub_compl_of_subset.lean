import Mathlib
import Submission.Work.ORP311.LuckDim
import Submission.Work.ORP311.mem_ell2Sub_iff
import Submission.Work.ORP311.ell2Sub_orthogonal

set_option autoImplicit false

open scoped InnerProductSpace InnerProduct

namespace Work.ORP311

open Work.ORVonNeumann

/-- **The transversal dimension vanishes on the complement.**  If every point of the finite set
`s` lies in the window `Z`, then no vector `e_i ⊗ δ_g` (`g ∈ s`) has a component in the
"out-of-window" subspace `ell2Sub n Zᶜ`: each such vector belongs to `ell2Sub n Z`, which is the
orthogonal complement of `ell2Sub n Zᶜ` (`Work.ORP311.ell2Sub_orthogonal`).  Its orthogonal
projection onto `ell2Sub n Zᶜ` is therefore `0`, so every summand of `tDim` is `0`. -/
theorem tDim_ell2Sub_compl_of_subset {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (s : Finset G) (Z : Set G) [(Work.ORP311.ell2Sub (G := G) n (Zᶜ)).HasOrthogonalProjection] (hsub : ↑s ⊆ Z) : Work.ORP311.tDim (G := G) n s (Work.ORP311.ell2Sub (G := G) n (Zᶜ)) = 0 := by
  rw [tDim_apply]
  have hterm : ∀ g ∈ s, ∀ i : Fin n,
      ‖(ell2Sub (G := G) n (Zᶜ)).starProjection
        (Rep.hinclude (G := G) n i (Rep.deltaG g))‖ ^ 2 = 0 := by
    intro g hg i
    -- `e_i ⊗ δ_g` lies in `ell2Sub n Z` because `g ∈ s ⊆ Z`
    have hmem : Rep.hinclude (G := G) n i (Rep.deltaG g) ∈ ell2Sub (G := G) n Z := by
      apply Submodule.le_topologicalClosure
      apply Submodule.subset_span
      exact ⟨g, hsub (Finset.mem_coe.mpr hg), i, rfl⟩
    -- hence it is orthogonal to `ell2Sub n Zᶜ`
    have horth : Rep.hinclude (G := G) n i (Rep.deltaG g) ∈ (ell2Sub (G := G) n (Zᶜ))ᗮ := by
      rw [← ell2Sub_orthogonal (G := G) n Z]
      exact hmem
    have hzero : (ell2Sub (G := G) n (Zᶜ)).starProjection
        (Rep.hinclude (G := G) n i (Rep.deltaG g)) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff
        (K := ell2Sub (G := G) n (Zᶜ))).mpr horth
    rw [hzero]
    simp
  rw [Finset.sum_congr rfl (fun g hg => Finset.sum_congr rfl (fun i _ => hterm g hg i))]
  simp

end Work.ORP311
