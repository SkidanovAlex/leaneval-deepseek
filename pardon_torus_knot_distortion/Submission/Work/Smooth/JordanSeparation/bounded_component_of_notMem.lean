import Mathlib

/-!
# Exactly one unbounded component of the complement of a compact set of `ℂ`

For a compact `K ⊆ ℂ` the complement `Kᶜ` has a *unique* unbounded connected component: since `K`
lies in some closed ball `B = closedBall 0 R`, the exterior region `E = {z : ℂ | R < ‖z‖}` is a
non-empty preconnected subset of `Kᶜ`, and any unbounded component contains a point of `E`, hence
contains `E` itself.  Consequently two distinct components cannot both be unbounded, which is the
statement proved here:

`Work.Smooth.JordanSeparation.bounded_component_of_notMem`: if `x, y ∈ Kᶜ` and `y` does not lie in
the component of `x`, then one of the two components is bounded.

The preconnectedness of the exterior `E` is obtained as the continuous image of the preconnected
product `Ioi R ×ˢ sphere 0 1` under the scalar-multiplication map `(r, w) ↦ r • w` (the sphere is
preconnected because `ℂ` has real dimension `2 > 1`).
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

set_option linter.unusedVariables false in

/-- **At most one unbounded complementary component.**  If `K ⊆ ℂ` is compact and two points
`x, y` of `Kᶜ` lie in different connected components of `Kᶜ`, then one of those two components is
bounded. -/
theorem bounded_component_of_notMem {K : Set ℂ} (hK : IsCompact K)
    {x y : ℂ} (hx : x ∈ Kᶜ) (hy : y ∈ Kᶜ) (hxy : y ∉ connectedComponentIn Kᶜ x) :
    Bornology.IsBounded (connectedComponentIn Kᶜ x) ∨
      Bornology.IsBounded (connectedComponentIn Kᶜ y) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hxb, hyb⟩ := hcon
  -- a closed ball containing `K`
  obtain ⟨R, hRpos, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  -- the exterior of that ball
  let E : Set ℂ := {z : ℂ | R < ‖z‖}
  -- `E` is the continuous image of `Ioi R ×ˢ sphere 0 1`
  have hEpre : IsPreconnected E := by
    have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
    have hsp : IsPreconnected (sphere (0 : ℂ) 1) := isPreconnected_sphere hrank 0 1
    have hprod : IsPreconnected (Ioi R ×ˢ sphere (0 : ℂ) 1) := isPreconnected_Ioi.prod hsp
    have hcont : ContinuousOn (fun p : ℝ × ℂ => p.1 • p.2) (Ioi R ×ˢ sphere (0 : ℂ) 1) :=
      (continuous_fst.smul continuous_snd).continuousOn
    have himg : (fun p : ℝ × ℂ => p.1 • p.2) '' (Ioi R ×ˢ sphere (0 : ℂ) 1) = E := by
      ext z
      constructor
      · rintro ⟨⟨r, w⟩, ⟨hp1, hp2⟩, rfl⟩
        change R < ‖r • w‖
        rw [Metric.mem_sphere, dist_zero_right] at hp2
        rw [norm_smul, Real.norm_of_nonneg (le_of_lt (lt_trans hRpos hp1)), hp2, mul_one]
        exact hp1
      · intro hz
        change R < ‖z‖ at hz
        have hzp : 0 < ‖z‖ := lt_trans hRpos hz
        refine ⟨(‖z‖, (‖z‖⁻¹ : ℝ) • z), ⟨hz, ?_⟩, ?_⟩
        · rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hzp), inv_mul_cancel₀ (ne_of_gt hzp)]
        · show ‖z‖ • ((‖z‖⁻¹ : ℝ) • z) = z
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hzp), one_smul]
    rw [← himg]
    exact hprod.image _ hcont
  have hKE : E ⊆ Kᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzK
    have h1 : z ∈ closedBall (0 : ℂ) R := hKR hzK
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    exact absurd (show R < ‖z‖ from hz) (not_lt.mpr h1)
  have hEne : E.Nonempty := ⟨(R + 1 : ℝ) • (1 : ℂ), by
    change R < ‖(R + 1 : ℝ) • (1 : ℂ)‖
    rw [norm_smul, Real.norm_of_nonneg (by linarith), norm_one, mul_one]
    linarith⟩
  -- an unbounded set meets the exterior
  have key : ∀ S : Set ℂ, ¬ Bornology.IsBounded S → ∃ a ∈ S, R < ‖a‖ := by
    intro S hS
    by_contra h
    apply hS
    rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
    refine ⟨R, fun z hz => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hc
    exact h ⟨z, hz, not_le.mp hc⟩
  obtain ⟨a, hac, haE⟩ := key _ hxb
  obtain ⟨b, hbc, hbE⟩ := key _ hyb
  -- the exterior lies in each of the two components
  have hEsubx : E ⊆ connectedComponentIn Kᶜ x := by
    have h1 : E ⊆ connectedComponentIn Kᶜ a := hEpre.subset_connectedComponentIn haE hKE
    rw [← connectedComponentIn_eq hac] at h1
    exact h1
  have hEsuby : E ⊆ connectedComponentIn Kᶜ y := by
    have h1 : E ⊆ connectedComponentIn Kᶜ b := hEpre.subset_connectedComponentIn hbE hKE
    rw [← connectedComponentIn_eq hbc] at h1
    exact h1
  obtain ⟨e, heE⟩ := hEne
  have hcx : connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ e :=
    connectedComponentIn_eq (hEsubx heE)
  have hcy : connectedComponentIn Kᶜ y = connectedComponentIn Kᶜ e :=
    connectedComponentIn_eq (hEsuby heE)
  exact hxy ((hcy.trans hcx.symm) ▸ mem_connectedComponentIn hy)

end Work.Smooth.JordanSeparation
