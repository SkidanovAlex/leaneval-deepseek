import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.basin_basic
import Submission.Work.Analysis.PertCrux.basin_mem_of_iterate_mem

namespace Work.Analysis.PertCrux

/-- **Forward invariance of the basin at a `φ`-value whose orbit avoids `0`.**

`d : MandelDim.ParabData f₀ D₀` is Shishikura §4.1 data for the parabolic germ `f₀` on the open
`D₀ ∋ 0` (`MandelDim.IsParabolicGerm`, so `DifferentiableOn ℂ f₀ D₀`, `f₀ 0 = 0`, `f₀' 0 = 1`);
`MandelDim.ParabolicBasin f₀ D₀` is the *uniform* basin of `0` (some neighbourhood `U ∋ z` has all
iterates mapped into `D₀`, with `f₀^[n] → 0` uniformly on `U`).

Claim: if `z` is a basin point which is a value of the maximal-domain Fatou coordinate `d.φ`
(`z = d.φ u` for some `u ∈ d.Dφ`) and whose forward orbit avoids `0`, then `f₀ z` lies in the basin
again.  This is the single step iterated by `Work.Analysis.PertCrux.walk_mem_Dphi`: the walk there
gives `d.φ (w + j) = f₀^[j] (d.φ w)` with `w + j ∈ d.Dφ`, so each induction step is an instance with
`z = d.φ (w+j)`, `u = w + j`.

`Work.Parab.basin_forward` already gives the conclusion when `f₀` is analytic at `z` (free: `basin ⊆
D₀` by `n = 0` in the defining `MapsTo`, `D₀` open) and `f₀` is not locally constant at `z`.  So the
content is the locally-constant case.  Useful inputs: if `f₀ ≡ c` on a neighbourhood `V ⊆ D₀` of `z`
then `f₀^[n] (V) = {f₀^[n-1] c}`, so the defining neighbourhood conditions show `V ⊆ basin` and that
the orbit of `c = f₀ z` stays in `D₀` and converges to `0`; also `Φ_abel` at `z` gives
`Φ c = Φ z + 1`, `Φ` is constant on the component of `z` in the basin (identity theorem, `Φ_holo`),
and that component misses `Ωp` (`Φ_inj` on `Ωp`).

The proof carried out below needs none of that case analysis.  Two soft inputs suffice:

* `d.basin_enter` (the defining property that excludes orbits landing on `0`) gives an `m` with
  `f₀^[m] z ∈ Ωp ⊆ basin`;
* the basin is **backward invariant along the orbit**:
  `Work.Analysis.PertCrux.basin_mem_of_iterate_mem` says that if `f₀^[k] w` is a basin point and the
  orbit segment `w, f₀ w, …, f₀^[k-1] w` lies in the open `D₀` on which `f₀` is holomorphic, then
  `w` is a basin point — the `k`-fold iteration of `Work.Parab.basinBack.basin_backward`, whose
  analyticity hypothesis is met at every orbit point because `f₀` is differentiable on the open
  `D₀` and a basin point lies in every neighbourhood of itself in the defining condition.

Applying the second input with `w = f₀ z` and `k = m - 1` (`m ≥ 1`) transports
`f₀^[m] z ∈ basin` back to `f₀ z ∈ basin`; when `m = 0` we have `z ∈ Ωp` and `Ωp` maps into itself.
Neither `hzφ` (the Fatou-coordinate hypothesis) nor the locally-constant case analysis is needed. -/
theorem basin_fwd_at_phi {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) {z : ℂ}
    (hz : z ∈ MandelDim.ParabolicBasin f₀ D₀)
    (hzφ : ∃ u : ℂ, u ∈ d.Dφ ∧ d.φ u = z)
    (havoid : ∀ n : ℕ, f₀^[n] z ≠ 0) :
    f₀ z ∈ MandelDim.ParabolicBasin f₀ D₀ := by
  obtain ⟨hopen, _, hdiff, _, _, _⟩ := hd
  -- every point of the orbit of `z` stays in `D₀`
  have horbit : ∀ n : ℕ, f₀^[n] z ∈ D₀ := by
    obtain ⟨U, hU, hmap, _⟩ := hz
    exact fun n => hmap n (mem_of_mem_nhds hU)
  -- `Ωp` meets the orbit of `z` (this is where `havoid` is used)
  obtain ⟨m, hm⟩ := d.basin_enter z hz havoid
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- `m = 0`: `z` itself lies in the petal, which maps into itself
    subst hm0
    exact d.Ωp_sub (d.Ωp_maps hm)
  · -- `m ≥ 1`: pull the basin membership from time `m = k + 1` back to `f₀ z`
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k.succ := ⟨m - 1, by omega⟩
    refine basin_mem_of_iterate_mem hopen hdiff (w := f₀ z) (k := k) ?_ ?_
    · -- the orbit segment under `f₀ z` lies in `D₀` (it is the orbit of `z` from time `1` on)
      intro j _
      have h := horbit (j + 1)
      rwa [Function.iterate_succ_apply] at h
    · -- `f₀^[k] (f₀ z) = f₀^[k+1] z` lies in the petal, hence in the basin
      have h := d.Ωp_sub hm
      rwa [Function.iterate_succ_apply] at h

end Work.Analysis.PertCrux
