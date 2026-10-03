import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.basin_basic
import Submission.Work.Analysis.PertCrux.basin_fwd_at_phi

namespace Work.Analysis.PertCrux

/-- The uniform parabolic basin of `0` is contained in the domain of `f₀`: this is the `n = 0`
instance of the defining `MapsTo` (a neighbourhood of a point of the basin contains the point). -/
theorem basin_subset_D₀ {f₀ : ℂ → ℂ} {D₀ : Set ℂ} :
    MandelDim.ParabolicBasin f₀ D₀ ⊆ D₀ := by
  intro z hz
  obtain ⟨U, hU, hmap, _⟩ := hz
  exact hmap 0 (mem_of_mem_nhds hU)

/-- **The walk, given forward invariance of the basin at `φ`-values.**  Suppose every basin point
which is a value of `d.φ` and whose forward orbit avoids `0` has its image again in the basin.  Then
for `w ∈ d.DE` with the orbit of `d.φ w` avoiding `0` the translates `w + j` stay in `d.Dφ`,
`d.φ (w + j)` is the `f₀`-orbit of `d.φ w`, and every orbit point is again in the basin. -/
theorem walk_mem_Dphi_of_crux {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hcrux : ∀ z ∈ MandelDim.ParabolicBasin f₀ D₀,
      (∃ u : ℂ, u ∈ d.Dφ ∧ d.φ u = z) → (∀ n : ℕ, f₀^[n] z ≠ 0) →
      f₀ z ∈ MandelDim.ParabolicBasin f₀ D₀)
    {w : ℂ} (hw : w ∈ d.DE) (havoid : ∀ j : ℕ, f₀^[j] (d.φ w) ≠ 0) (n : ℕ) :
    w + (n : ℂ) ∈ d.Dφ ∧ d.φ (w + (n : ℂ)) = f₀^[n] (d.φ w) ∧
      ∀ j : ℕ, j ≤ n → f₀^[j] (d.φ w) ∈ MandelDim.ParabolicBasin f₀ D₀ := by
  induction n with
  | zero =>
      refine ⟨by simpa using hw.1, by simp, ?_⟩
      intro j hj
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      rw [hj0]
      simpa using hw.2
  | succ k ih =>
      obtain ⟨hwD, hφk, hbas⟩ := ih
      have hzk : f₀^[k] (d.φ w) ∈ MandelDim.ParabolicBasin f₀ D₀ := hbas k le_rfl
      have hzD : f₀^[k] (d.φ w) ∈ D₀ := basin_subset_D₀ hzk
      have hφD : d.φ (w + (k : ℂ)) ∈ D₀ := by rw [hφk]; exact hzD
      have hsucc : w + (k : ℂ) + 1 ∈ d.Dφ := (d.succ_iff (w + (k : ℂ)) hwD).mpr hφD
      have habel : d.φ (w + (k : ℂ) + 1) = f₀ (d.φ (w + (k : ℂ))) :=
        d.φ_abel (w + (k : ℂ)) hwD hsucc
      have hnext : f₀ (f₀^[k] (d.φ w)) ∈ MandelDim.ParabolicBasin f₀ D₀ :=
        hcrux (f₀^[k] (d.φ w)) hzk ⟨w + (k : ℂ), hwD, hφk⟩ (by
          intro m
          exact fun h => havoid (m + k) (by rwa [← Function.iterate_add_apply] at h))
      have hcast : w + ((k + 1 : ℕ) : ℂ) = w + (k : ℂ) + 1 := by push_cast; ring
      refine ⟨?_, ?_, ?_⟩
      · rw [hcast]; exact hsucc
      · rw [hcast, habel, hφk]
        exact (Function.iterate_succ_apply' f₀ k (d.φ w)).symm
      · intro j hj
        rcases Nat.lt_or_eq_of_le hj with h | h
        · exact hbas j (Nat.lt_succ_iff.mp h)
        · rw [h, Function.iterate_succ_apply']
          exact hnext

/-- **The walk is legal and is the orbit** (for orbits that avoid `0`).  For `w ∈ d.DE` with the
orbit of `d.φ w` avoiding `0`, the translates `w + j` stay in `d.Dφ`, `d.φ (w+j)` is the orbit of
`d.φ w`, and every orbit point is again in the basin (so that `d.Φ_abel` iterates:
`d.Φ (d.φ (w+n)) = d.E w + n`).

Proof: `ParabolicBasin f₀ D₀ ⊆ D₀` (`n = 0` in the defining neighbourhood condition).  Induction:
`d.φ (w+j) ∈ D₀` gives `w+j+1 ∈ d.Dφ` by `d.succ_iff` and `d.φ (w+j+1) = f₀ (d.φ (w+j))` by
`d.φ_abel`; the orbit point stays in the basin by `Work.Parab.basin_forward` (`AnalyticAt ℂ f₀`
comes from `hd`; the non-local-constancy at an orbit point follows from `havoid`: if `f₀ ≡ c` near
a basin orbit point then `c` is the uniform limit of the iterates on a neighbourhood, hence
`c = 0`, contradicting `havoid`).

CORRECTION (this session).  The last sentence of the sketch above is not the right route: `f₀ ≡ c`
on a neighbourhood of a basin point does **not** force `c = 0` -- it only forces the *orbit* of `c`
to stay in `D₀` and converge to `0`, and `c = 0` would need `f₀ (U) ⊆ U`.  What does give the step
is `Work.Analysis.PertCrux.basin_fwd_at_phi` (proved in the sibling file): the whole orbit of a
basin point stays in the open `D₀` (apply the defining `MapsTo` at the point itself, which lies in
its own basin neighbourhood), hence the basin is *backward* invariant along the orbit
(`Work.Parab.basinBack.basin_backward`, which needs only analyticity on a neighbourhood of each
orbit point); and since `havoid` lets `d.basin_enter` place some `f₀^[m] (d.φ w)` in `Ωp ⊆ basin`, a
descending induction (`Nat.decreasingInduction`) gives `f₀ z ∈ basin` for each basin point `z` of
the walk.  The statement below is then an immediate instance of `walk_mem_Dphi_of_crux` above. -/
theorem walk_mem_Dphi {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) {w : ℂ} (hw : w ∈ d.DE)
    (havoid : ∀ j : ℕ, f₀^[j] (d.φ w) ≠ 0) (n : ℕ) :
    w + (n : ℂ) ∈ d.Dφ ∧ d.φ (w + (n : ℂ)) = f₀^[n] (d.φ w) ∧
      ∀ j : ℕ, j ≤ n → f₀^[j] (d.φ w) ∈ MandelDim.ParabolicBasin f₀ D₀ :=
  walk_mem_Dphi_of_crux d
    (fun z hz hzφ havoid => Work.Analysis.PertCrux.basin_fwd_at_phi d hd hz hzφ havoid)
    hw havoid n

end Work.Analysis.PertCrux
