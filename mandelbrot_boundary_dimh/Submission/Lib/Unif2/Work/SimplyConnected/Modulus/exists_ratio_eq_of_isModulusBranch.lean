import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ModulusDefs
import Submission.Lib.Unif2.HolomorphicLog

namespace Work.SimplyConnected.Modulus

open LeanEval.Geometry
open scoped Manifold ContDiff Topology
open Filter Set

/-- **Two local branches of the modulus differ by a constant of modulus one.**

Let `Φ` and `Ψ` be local holomorphic branches of the modulus `exp (-E)` on open sets `U`, `V`
respectively (`Work.SC.IsModulusBranch`).  Off the pole `z₀` the ratio `Ψ / Φ` is then holomorphic
and has constant modulus `1`; on a preconnected piece of `U ∩ V` it is therefore constant, say
equal to `c : ℂ` with `‖c‖ = 1`, and `Ψ = c * Φ` there. -/
theorem exists_ratio_eq_of_isModulusBranch {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {z₀ : X} {E : X → ℝ} {U V : Set X}
    {Φ Ψ : X → ℂ} (hΦ : Work.SC.IsModulusBranch z₀ E U Φ) (hΨ : Work.SC.IsModulusBranch z₀ E V Ψ)
    (hconn : IsPreconnected ((U ∩ V) \ {z₀})) (hne : ((U ∩ V) \ {z₀}).Nonempty) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x ∈ (U ∩ V) \ {z₀}, Ψ x = c * Φ x := by
  have hSopen : IsOpen ((U ∩ V) \ {z₀}) :=
    (hΦ.1.inter hΨ.1).sdiff isClosed_singleton
  -- the ratio is holomorphic off the pole
  have hdiv : ∀ x ∈ (U ∩ V) \ {z₀},
      Submission.HolomorphicOnXAt (fun y => Ψ y / Φ y) x := by
    intro x hx
    obtain ⟨⟨hxU, hxV⟩, hxz⟩ := hx
    have h1 : Submission.HolomorphicOnXAt Ψ x := hΨ.holomorphic x hxV
    have h2 : Submission.HolomorphicOnXAt Φ x := hΦ.holomorphic x hxU
    have h3 : Φ x ≠ 0 := hΦ.ne_zero x hxU hxz
    rw [Submission.HolomorphicOnXAt] at h1 h2 ⊢
    have h3' : (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 := by
      rw [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
      exact h3
    have heq : (fun y : X => Ψ y / Φ y) ∘ (chartAt ℂ x).symm =
        (Ψ ∘ (chartAt ℂ x).symm) / (Φ ∘ (chartAt ℂ x).symm) := rfl
    rw [heq]
    exact h1.div h2 h3'
  -- and it has constant modulus one there
  have hnorm : ∀ x ∈ (U ∩ V) \ {z₀}, ‖Ψ x / Φ x‖ = 1 := by
    intro x hx
    obtain ⟨⟨hxU, hxV⟩, hxz⟩ := hx
    rw [norm_div, hΨ.norm_eq x hxV hxz, hΦ.norm_eq x hxU hxz]
    exact div_self (ne_of_gt (Real.exp_pos _))
  -- hence it is locally constant on that open set
  have hlocconst : ∀ x ∈ (U ∩ V) \ {z₀}, ∀ᶠ y in 𝓝 x, Ψ y / Φ y = Ψ x / Φ x := by
    intro x hx
    refine Submission.HolomorphicOnXAt.eventually_eq_const_of_eventually_norm_eq
      (c := 1) (hdiv x hx) ?_
    filter_upwards [hSopen.mem_nhds hx] with y hy
    rw [hnorm y hy]
  -- as that set is preconnected, a locally constant function on it is constant
  haveI : PreconnectedSpace ↥((U ∩ V) \ {z₀}) := isPreconnected_iff_preconnectedSpace.mp hconn
  have hlc : IsLocallyConstant (fun p : ↥((U ∩ V) \ {z₀}) => Ψ p.1 / Φ p.1) := by
    intro s
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hev : {y : X | Ψ y / Φ y = Ψ p.1 / Φ p.1} ∈ 𝓝 (p.1 : X) := hlocconst p.1 p.2
    refine Filter.mem_of_superset
      ((continuous_subtype_val.continuousAt).preimage_mem_nhds hev) ?_
    intro q hq
    show Ψ q.1 / Φ q.1 ∈ s
    rw [hq]
    exact hp
  obtain ⟨x₁, hx₁⟩ := hne
  have key : ∀ x ∈ (U ∩ V) \ {z₀}, Ψ x / Φ x = Ψ x₁ / Φ x₁ := by
    intro x hx
    exact hlc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ ⟨x, hx⟩)
      (mem_univ ⟨x₁, hx₁⟩)
  refine ⟨Ψ x₁ / Φ x₁, hnorm x₁ hx₁, ?_⟩
  intro x hx
  have hFx : Φ x ≠ 0 := hΦ.ne_zero x hx.1.1 hx.2
  rw [← key x hx]
  exact (div_mul_cancel₀ (Ψ x) hFx).symm

end Work.SimplyConnected.Modulus
