import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basin
import Submission.Work.Horn.locally_open_of_not_locally_const
import Submission.Work.Parab.basinEnters.zero_not_mem_basin

namespace Work.Repel

open Set Metric Filter

/-- **No point of the parabolic basin ever hits `0`** (for a germ which is nowhere locally
constant on `D`).

Forward invariance of the parabolic basin (`Work.Horn.MandelDim.basin_basic`) puts every iterate
`f^[n] z` of a basin point `z` back in the basin, so if `f^[n] z = 0` then `0` would itself belong
to the basin.  That is impossible for a parabolic germ (`f'(0) = 1` forces the iterates to converge
to `0` *non-uniformly* near `0`): `Work.Parab.basinEnters.zero_not_mem_parabolicBasin`.

The local-openness hypothesis is needed for forward invariance (a non-constant holomorphic map on
an open set is locally open), and it is exactly the `¬ (∀ᶠ w in nhds z, f w = f z)` input. -/
theorem orbit_ne_zero_of_nowhere_locally_const {f : ℂ → ℂ} {D : Set ℂ}
    (hg : MandelDim.IsParabolicGerm f D)
    (hnlc : ∀ z ∈ D, ¬ (∀ᶠ w in nhds z, f w = f z)) :
    ∀ z ∈ MandelDim.ParabolicBasin f D, ∀ n : ℕ, (f^[n]) z ≠ 0 := by
  have hD : IsOpen D := hg.1
  have hf : DifferentiableOn ℂ f D := hg.2.2.1
  -- `f` is locally open at every point of `D`.
  have hopen : ∀ w ∈ D, ∀ U ∈ nhds w, f '' U ∈ nhds (f w) :=
    fun w hw => Work.Horn.locally_open_of_not_locally_const hD hf hw (hnlc w hw)
  obtain ⟨_, hfwd, _⟩ := Work.Horn.MandelDim.basin_basic hD hf hopen
  intro z hz n hn
  -- every iterate of a basin point lies in the basin
  have hiter : ∀ k : ℕ, (f^[k]) z ∈ MandelDim.ParabolicBasin f D := by
    intro k
    induction k with
    | zero => simpa using hz
    | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact hfwd _ ih
  -- hence `0` itself lies in the basin, contradicting `zero_not_mem_parabolicBasin`
  have h0 : (0 : ℂ) ∈ MandelDim.ParabolicBasin f D := by
    have h := hiter n
    rwa [hn] at h
  exact Work.Parab.basinEnters.zero_not_mem_parabolicBasin hg h0

end Work.Repel
