import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

/-- **Globalisation of a local `C^K` condition.**

If `Ψ : (Fin n → ℝ) → ℂ` is `C^K` (with `K : ℕ` a *finite* order) at the point `z`, then `Ψ`
agrees with a globally `C^K` function on a neighbourhood of `z`.

The proof multiplies `Ψ` by a `ContDiffBump` which is `1` on a ball around `z` and whose topological
support is contained in a neighbourhood of `z` on which `Ψ` is `C^K`: the product is `C^K` on that
neighbourhood and vanishes identically outside the (compact) support of the bump. -/
theorem exists_contDiff_eventuallyEq_of_contDiffAt {n K : ℕ} {z : Fin n → ℝ}
    {Ψ : (Fin n → ℝ) → ℂ} (hΨ : ContDiffAt ℝ (((K : ℕ)) : WithTop ℕ∞) Ψ z) :
    ∃ Ψ' : (Fin n → ℝ) → ℂ,
      ContDiff ℝ (((K : ℕ)) : WithTop ℕ∞) Ψ' ∧ Ψ' =ᶠ[nhds z] Ψ := by
  -- the level `K` is a finite one, so that a local Taylor expansion is available
  have hKne : (((K : ℕ)) : WithTop ℕ∞) ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  -- a neighbourhood `u` of `z` on which `Ψ` is `C^K`
  obtain ⟨u, hu_open, hzu, hu⟩ :=
    ContDiffWithinAt.contDiffOn' (f := Ψ) (s := Set.univ) (x := z)
      (m := (((K : ℕ)) : WithTop ℕ∞)) (n := (((K : ℕ)) : WithTop ℕ∞))
      le_rfl (fun h => absurd h hKne) hΨ
  have hu' : ContDiffOn ℝ (((K : ℕ)) : WithTop ℕ∞) Ψ u :=
    hu.mono (fun y hy => ⟨by simp, hy⟩)
  -- a closed ball around `z` contained in `u`
  obtain ⟨ε, hεpos, hεu⟩ := Metric.mem_nhds_iff.mp (hu_open.mem_nhds hzu)
  let c : ContDiffBump z := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hrOut : c.rOut = ε / 2 := rfl
  have hφ_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (⇑c) := c.contDiff
  -- the bump is supported in `u`
  have hφts : tsupport (⇑c) ⊆ u := by
    intro y hy
    have hy1 : y ∈ closure (Metric.ball z c.rOut) := by
      simpa [tsupport, c.support_eq] using hy
    have hy2 : y ∈ Metric.closedBall z c.rOut := Metric.closure_ball_subset_closedBall hy1
    refine hεu (Metric.closedBall_subset_ball ?_ hy2)
    rw [hrOut]; linarith
  -- the bump equals `1` near `z`
  have hφ1 : (⇑c) =ᶠ[nhds z] (fun _ => (1 : ℝ)) := by
    filter_upwards [Metric.closedBall_mem_nhds z c.rIn_pos] with y hy
    exact c.one_of_mem_closedBall hy
  have hφC : ContDiff ℝ (((K : ℕ)) : WithTop ℕ∞) (fun y => ((c y : ℝ) : ℂ)) := by
    have h1 : ContDiff ℝ (((K : ℕ)) : WithTop ℕ∞) (fun y => Complex.ofRealCLM (c y)) :=
      (ContinuousLinearMap.contDiff Complex.ofRealCLM).comp (hφ_smooth.of_le (by simp))
    simpa using h1
  refine ⟨fun y => ((c y : ℝ) : ℂ) * Ψ y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ u
    · -- inside `u` the product of `C^K` functions is `C^K`
      exact hφC.contDiffAt.mul (hu'.contDiffAt (hu_open.mem_nhds hx))
    · -- outside `u` the product vanishes identically near `x`
      have hx_ts : x ∉ tsupport (⇑c) := fun h => hx (hφts h)
      have h0 : (⇑c) =ᶠ[nhds x] (fun _ => (0 : ℝ)) :=
        notMem_tsupport_iff_eventuallyEq.mp hx_ts
      have hz : ContDiffAt ℝ (((K : ℕ)) : WithTop ℕ∞) (fun _ : Fin n → ℝ => (0 : ℂ)) x :=
        contDiff_const.contDiffAt
      refine hz.congr_of_eventuallyEq ?_
      filter_upwards [h0] with y hy
      simp [hy]
  · filter_upwards [hφ1] with y hy
    simp [hy]

end Work.Diff.STE.Lead
