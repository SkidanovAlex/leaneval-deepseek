import Mathlib

namespace Work.Horn.HB

open Set Metric Filter Topology

/-- **A holomorphic map whose components over a ball are proper over compacts is nowhere locally
constant there.**

Let `D ⊆ ℂ` be open, `g` holomorphic on `D`, `v ∈ ℂ`, `0 < r < ‖v‖`, and assume the *local
finiteness* (LF) condition: for every `x ∈ D` with `g x` in the ball `ball v r`, the component of
`D ∩ g ⁻¹' ball v r` through `x` meets `g ⁻¹' K` in a compact set, for every compact
`K ⊆ ball v r`.  Then `g` is not locally constant at any point `z ∈ D` with `g z ∈ ball v r`.

The proof uses only the LF condition (the covering hypothesis is not needed): if `g` were constant
equal to `g z` on a neighbourhood of `z`, then by the identity principle `g ≡ g z` on the whole
component `C` of `D ∩ g ⁻¹' ball v r` through `z`; LF with `K = {g z}` then makes `C` compact.
But `C` is a nonempty open subset of `ℂ` (it is a component of an open set), hence a clopen
nonempty subset of the connected space `ℂ`, so `C = univ` — impossible, since `univ` is not compact
in `ℂ`. -/
theorem not_locally_const_of_covering_LF {g : ℂ → ℂ} {D : Set ℂ} {v : ℂ} {r : ℝ}
    (hDo : IsOpen D) (hgd : DifferentiableOn ℂ g D) (hr : 0 < r) (hrv : r < ‖v‖)
    (hcov : IsCoveringMapOn (fun z : ↥D => g z) {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v})
    (hLF : ∀ x ∈ D, g x ∈ Metric.ball v r → ∀ K ⊆ Metric.ball v r, IsCompact K →
      IsCompact (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v r) x ∩ g ⁻¹' K))
    {z : ℂ} (hz : z ∈ D) (hgz : g z ∈ Metric.ball v r) :
    ¬ Filter.Eventually (fun w => g w = g z) (nhds z) := by
  intro hev
  -- the component `C` of `D ∩ g ⁻¹' ball v r` through `z`
  set C : Set ℂ := connectedComponentIn (D ∩ g ⁻¹' Metric.ball v r) z with hCdef
  have hzS : z ∈ D ∩ g ⁻¹' Metric.ball v r := ⟨hz, hgz⟩
  have hCmem : z ∈ C := hCdef ▸ mem_connectedComponentIn hzS
  have hCopen : IsOpen C := by
    rw [hCdef]
    exact (hgd.continuousOn.isOpen_inter_preimage hDo Metric.isOpen_ball).connectedComponentIn
  -- `g ≡ g z` on `C`, by the identity principle
  have hAn : AnalyticOnNhd ℂ g C := fun x hx =>
    hgd.analyticAt (hDo.mem_nhds ((connectedComponentIn_subset _ _ (hCdef ▸ hx)).1))
  have hEqC : EqOn g (fun _ => g z) C :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hAn analyticOnNhd_const
      (hCdef ▸ isPreconnected_connectedComponentIn) hCmem
      (show g =ᶠ[𝓝 z] (fun _ => g z) from hev)
  -- LF with `K = {g z}` makes `C` compact
  have hK : ({g z} : Set ℂ) ⊆ Metric.ball v r := by
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rwa [hw]
  have hcomp : IsCompact (C ∩ g ⁻¹' ({g z} : Set ℂ)) := by
    have h := hLF z hz hgz ({g z} : Set ℂ) hK isCompact_singleton
    rw [hCdef]
    exact h
  have hCcompact : IsCompact C := by
    have hcompC : C ∩ g ⁻¹' ({g z} : Set ℂ) = C := by
      ext w
      constructor
      · exact fun h => h.1
      · intro hw
        exact ⟨hw, by simpa using hEqC hw⟩
    rw [← hcompC]
    exact hcomp
  -- `C` is a nonempty clopen subset of the connected space `ℂ`, so `C = univ`; but then `univ`
  -- would be compact, hence bounded — impossible in `ℂ`.
  have hCuniv : C = Set.univ := IsClopen.eq_univ ⟨hCcompact.isClosed, hCopen⟩ ⟨z, hCmem⟩
  have hbdd : Bornology.IsBounded (Set.univ : Set ℂ) := hCuniv ▸ hCcompact.isBounded
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hbdd
  have hR0 : 0 ≤ R := by
    have := hR (Set.mem_univ (0 : ℂ))
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have hp : ‖(((R + 1 : ℝ)) : ℂ)‖ = R + 1 := by
    have hnormsq : ‖(((R + 1 : ℝ)) : ℂ)‖ ^ 2 = (R + 1) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
    nlinarith [norm_nonneg (((R + 1 : ℝ)) : ℂ)]
  have hle : ‖(((R + 1 : ℝ)) : ℂ)‖ ≤ R := by
    have := hR (Set.mem_univ (((R + 1 : ℝ)) : ℂ))
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  linarith

end Work.Horn.HB
