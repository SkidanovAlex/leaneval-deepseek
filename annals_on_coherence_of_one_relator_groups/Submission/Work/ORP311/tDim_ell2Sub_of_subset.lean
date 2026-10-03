import Mathlib
import Submission.Work.ORP311.LuckDim
import Submission.Work.ORP311.mem_ell2Sub_iff

namespace Work.ORP311

open scoped InnerProductSpace InnerProduct

open Work.ORVonNeumann

/-- **The transversal dimension of a window-supported subspace, evaluated on a sub-window.**

If every point of the finite set `s` lies in the window `Z`, then the vectors `e_i ⊗ δ_g`
(`g ∈ s`, `i : Fin n`) already belong to `ell2Sub n Z`; the orthogonal projection onto
`ell2Sub n Z` therefore fixes them, and each contributes its squared norm `1`.  Hence

  `tDim n s (ell2Sub n Z) = n * s.card`.

This is the "basis evaluation" of the Følner/Lück inequality: on a window, `tDim` is the full
amplified dimension `n · #s`. -/
theorem tDim_ell2Sub_of_subset {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (s : Finset G) (Z : Set G) [(Work.ORP311.ell2Sub (G := G) n Z).HasOrthogonalProjection] (hsub : ↑s ⊆ Z) : Work.ORP311.tDim (G := G) n s (Work.ORP311.ell2Sub (G := G) n Z) = (n : ℝ) * (s.card : ℝ) := by
  rw [tDim_apply]
  have hterm : ∀ g ∈ s, ∀ i : Fin n,
      ‖(ell2Sub (G := G) n Z).starProjection
        (Rep.hinclude (G := G) n i (Rep.deltaG g))‖ ^ 2 = 1 := by
    intro g hg i
    have hgZ : g ∈ Z := hsub (Finset.mem_coe.mpr hg)
    have hmem : Rep.hinclude (G := G) n i (Rep.deltaG g) ∈ ell2Sub (G := G) n Z := by
      apply Submodule.le_topologicalClosure
      apply Submodule.subset_span
      exact ⟨g, hgZ, i, rfl⟩
    rw [Submodule.starProjection_eq_self_iff.mpr hmem]
    rw [show Rep.hinclude (G := G) n i (Rep.deltaG g) = PiLp.single 2 i (Rep.deltaG g) from rfl,
      PiLp.norm_single, Rep.norm_deltaG]
    norm_num
  rw [Finset.sum_congr rfl (fun g hg => Finset.sum_congr rfl (fun i _ => hterm g hg i))]
  simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

end Work.ORP311
