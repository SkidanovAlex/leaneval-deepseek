import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORP311.blk_comp_regBlk
import Submission.Work.ORP311.coset_subset_window

namespace Work.ORP311

/-- **The window projection of a solution lands in `Ewin`.**

`Ewin n N t m Z` is the subspace of the window `X_m = ⋃_{|j| ≤ m} N t^j` consisting of the vectors
`η` which are killed by the block projections of `Z` on every coset *inside* the window, i.e.
`blk n N t j (Z η) = 0` for `-m < j ≤ m`.

If `ξ` is a solution of `Z ξ = 0`, where `Z = S + C · λ(t)` and both `S` and `C` commute with
all the block projections `blk n N t j`, then `blk n N t j Z = S · blk n N t j + C · λ(t) ·
blk n N t (j-1)` (because `λ(t)` shifts the blocks, `blk j ∘ λ(t) = λ(t) ∘ blk (j-1)`,
`Work.ORP311.blk_comp_regBlk`).  As the window projection `P` satisfies
`blk n N t j ∘ P = blk n N t j` for every `j` with `coset N t j ⊆ window N t m`, this gives

  `blk n N t j (Z (P ξ)) = blk n N t j (Z ξ) = 0`

for every `-m < j ≤ m`, while `P ξ` lies in the window by construction. -/
theorem window_proj_mem_Ewin {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G} (h : Work.ORP311.P311.TwistData N t) (n m : ℕ) (S C : Work.ORVonNeumann.Rep.HSum (G := G) n →L[ℂ] Work.ORVonNeumann.Rep.HSum (G := G) n) (hSb : ∀ j, Work.ORP311.P311.blk n N t j ∘L S = S ∘L Work.ORP311.P311.blk n N t j) (hCb : ∀ j, Work.ORP311.P311.blk n N t j ∘L C = C ∘L Work.ORP311.P311.blk n N t j) {ξ : Work.ORVonNeumann.Rep.HSum (G := G) n} (hξ : Work.ORP311.twoTerm (G := G) n t S C ξ = 0) : (Work.ORP311.ell2Sub (G := G) n (Work.ORP311.window N t m)).starProjection ξ ∈ Work.ORP311.P311.Ewin n N t m (Work.ORP311.twoTerm (G := G) n t S C) := by
  rw [Work.ORP311.P311.Ewin]
  simp only [Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨Submodule.starProjection_apply_mem _ ξ, ?_⟩
  intro j hj
  rw [LinearMap.mem_ker]
  change (P311.blk n N t j ∘L Work.ORP311.twoTerm n t S C)
      ((ell2Sub (G := G) n (window N t m)).starProjection ξ) = 0
  -- `λ(t)` shifts the block index, so `blk j ∘ Z = S ∘ blk j + (C ∘ λ(t)) ∘ blk (j-1)`.
  have key : P311.blk n N t j ∘L Work.ORP311.twoTerm n t S C
      = S ∘L P311.blk n N t j
        + (C ∘L Work.ORP311.regBlk (G := G) n t) ∘L P311.blk n N t (j - 1) := by
    rw [Work.ORP311.twoTerm, ContinuousLinearMap.comp_add, ← ContinuousLinearMap.comp_assoc,
      hCb j, ContinuousLinearMap.comp_assoc, Work.ORP311.blk_comp_regBlk h n j,
      ← ContinuousLinearMap.comp_assoc, hSb j]
  -- the block projection extracts the window projection on the cosets inside the window
  have hPj : P311.blk n N t j ∘L (ell2Sub (G := G) n (window N t m)).starProjection
      = P311.blk n N t j :=
    Submodule.starProjection_comp_starProjection_of_le
      (ell2Sub_mono (coset_subset_window hj.1.le hj.2))
  have hPj1 : P311.blk n N t (j - 1) ∘L (ell2Sub (G := G) n (window N t m)).starProjection
      = P311.blk n N t (j - 1) :=
    Submodule.starProjection_comp_starProjection_of_le
      (ell2Sub_mono (coset_subset_window (by omega) (by omega)))
  have hPj_app : P311.blk n N t j ((ell2Sub (G := G) n (window N t m)).starProjection ξ)
      = P311.blk n N t j ξ := by
    have hh := congrArg (fun f : Work.ORVonNeumann.Rep.HSum (G := G) n →L[ℂ]
        Work.ORVonNeumann.Rep.HSum (G := G) n => f ξ) hPj
    simpa using hh
  have hPj1_app : P311.blk n N t (j - 1) ((ell2Sub (G := G) n (window N t m)).starProjection ξ)
      = P311.blk n N t (j - 1) ξ := by
    have hh := congrArg (fun f : Work.ORVonNeumann.Rep.HSum (G := G) n →L[ℂ]
        Work.ORVonNeumann.Rep.HSum (G := G) n => f ξ) hPj1
    simpa using hh
  -- so `blk j` of `Z` at the window projection equals `blk j` of `Z` at `ξ`, which vanishes
  have hZw : (P311.blk n N t j ∘L Work.ORP311.twoTerm n t S C)
        ((ell2Sub (G := G) n (window N t m)).starProjection ξ)
      = (P311.blk n N t j ∘L Work.ORP311.twoTerm n t S C) ξ := by
    rw [key]
    simp only [ContinuousLinearMap.comp_apply, add_apply]
    rw [hPj_app, hPj1_app]
  rw [hZw, ContinuousLinearMap.comp_apply, hξ, map_zero]

end Work.ORP311
