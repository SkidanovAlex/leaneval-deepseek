import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

namespace Commons.Topology.Plane

open scoped RealInnerProductSpace InnerProductSpace

/-- Every nonempty closed convex subset of the plane is a (continuous) retract of
the plane: the nearest-point projection is a retraction. -/
theorem convex_retract {K : Set ℂ} (hK : Convex ℝ K) (hc : IsClosed K) (hne : K.Nonempty) :
    ∃ r : C(ℂ, ↥K), ∀ x : ↥K, r (x : ℂ) = x := by
  classical
  have hNe : Nonempty ↥K := hne.to_subtype
  -- Existence of a nearest point in `K` (Hilbert projection theorem).
  have hex : ∀ x : ℂ, ∃ v ∈ K, ‖x - v‖ = ⨅ w : ↥K, ‖x - (w : ℂ)‖ :=
    fun x => exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hK x
  -- The nearest-point projection, defined by choice.
  let p : ℂ → ↥K := fun x =>
    ⟨Classical.choose (hex x), (Classical.choose_spec (hex x)).1⟩
  have hp_min : ∀ x : ℂ, ‖x - (p x : ℂ)‖ = ⨅ w : ↥K, ‖x - (w : ℂ)‖ :=
    fun x => (Classical.choose_spec (hex x)).2
  -- Variational characterisation of the nearest point.
  have hp_char : ∀ (x : ℂ) (w : ↥K),
      ⟪x - (p x : ℂ), (w : ℂ) - (p x : ℂ)⟫_ℝ ≤ 0 :=
    fun x w => (norm_eq_iInf_iff_real_inner_le_zero hK (p x).2).1 (hp_min x) (w : ℂ) w.2
  -- Uniqueness of the minimiser.
  have huniq : ∀ (x : ℂ) (u v : ↥K),
      ‖x - (u : ℂ)‖ = ⨅ w : ↥K, ‖x - (w : ℂ)‖ →
      ‖x - (v : ℂ)‖ = ⨅ w : ↥K, ‖x - (w : ℂ)‖ → u = v := by
    intro x u v hu hv
    have h1 : ⟪x - (u : ℂ), (v : ℂ) - (u : ℂ)⟫_ℝ ≤ 0 :=
      (norm_eq_iInf_iff_real_inner_le_zero hK u.2).1 hu (v : ℂ) v.2
    have h2 : ⟪x - (v : ℂ), (u : ℂ) - (v : ℂ)⟫_ℝ ≤ 0 :=
      (norm_eq_iInf_iff_real_inner_le_zero hK v.2).1 hv (u : ℂ) u.2
    have h2' : 0 ≤ ⟪x - (v : ℂ), (v : ℂ) - (u : ℂ)⟫_ℝ := by
      rw [show (u : ℂ) - (v : ℂ) = -((v : ℂ) - (u : ℂ)) by ring, inner_neg_right] at h2
      linarith
    have h3 : ⟪(x - (u : ℂ)) - (x - (v : ℂ)), (v : ℂ) - (u : ℂ)⟫_ℝ ≤ 0 := by
      rw [inner_sub_left]
      linarith
    have h4 : (x - (u : ℂ)) - (x - (v : ℂ)) = (v : ℂ) - (u : ℂ) := by ring
    rw [h4] at h3
    have h5 : ⟪(v : ℂ) - (u : ℂ), (v : ℂ) - (u : ℂ)⟫_ℝ = 0 :=
      le_antisymm h3 real_inner_self_nonneg
    have h6 : (v : ℂ) - (u : ℂ) = 0 := inner_self_eq_zero.1 h5
    exact Subtype.ext (sub_eq_zero.1 h6).symm
  -- The projection fixes `K` pointwise.
  have hp_fix : ∀ x : ↥K, p (x : ℂ) = x := by
    intro x
    have hx_min : ‖(x : ℂ) - (x : ℂ)‖ = ⨅ w : ↥K, ‖(x : ℂ) - (w : ℂ)‖ := by
      rw [sub_self, norm_zero]
      refine le_antisymm (le_ciInf fun w => norm_nonneg _) ?_
      have h := ciInf_le (f := fun w : ↥K => ‖(x : ℂ) - (w : ℂ)‖)
        ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ x
      simpa using h
    exact huniq (x : ℂ) (p (x : ℂ)) x (hp_min (x : ℂ)) hx_min
  -- The projection is nonexpansive.
  have hlip : ∀ x y : ℂ, ‖(p x : ℂ) - (p y : ℂ)‖ ≤ ‖x - y‖ := by
    intro x y
    have h1 : ⟪x - (p x : ℂ), (p y : ℂ) - (p x : ℂ)⟫_ℝ ≤ 0 := hp_char x (p y)
    have h2 : ⟪y - (p y : ℂ), (p x : ℂ) - (p y : ℂ)⟫_ℝ ≤ 0 := hp_char y (p x)
    have h2' : 0 ≤ ⟪y - (p y : ℂ), (p y : ℂ) - (p x : ℂ)⟫_ℝ := by
      rw [show (p x : ℂ) - (p y : ℂ) = -((p y : ℂ) - (p x : ℂ)) by ring, inner_neg_right] at h2
      linarith
    have h3 : ⟪(x - (p x : ℂ)) - (y - (p y : ℂ)), (p y : ℂ) - (p x : ℂ)⟫_ℝ ≤ 0 := by
      rw [inner_sub_left]
      linarith
    have h4 : (x - (p x : ℂ)) - (y - (p y : ℂ))
        = (x - y) + ((p y : ℂ) - (p x : ℂ)) := by ring
    rw [h4, inner_add_left] at h3
    have h5 : ‖(p y : ℂ) - (p x : ℂ)‖ ^ 2 ≤ ‖x - y‖ * ‖(p y : ℂ) - (p x : ℂ)‖ := by
      have h6 : ⟪(p y : ℂ) - (p x : ℂ), (p y : ℂ) - (p x : ℂ)⟫_ℝ
          = ‖(p y : ℂ) - (p x : ℂ)‖ ^ 2 := real_inner_self_eq_norm_sq _
      rw [h6] at h3
      have h7 : -⟪x - y, (p y : ℂ) - (p x : ℂ)⟫_ℝ
          ≤ ‖x - y‖ * ‖(p y : ℂ) - (p x : ℂ)‖ :=
        le_trans (neg_le_abs _) (abs_real_inner_le_norm _ _)
      linarith
    have h8 : ‖(p y : ℂ) - (p x : ℂ)‖ ≤ ‖x - y‖ := by
      by_cases hz : ‖(p y : ℂ) - (p x : ℂ)‖ = 0
      · rw [hz]; exact norm_nonneg _
      · have hpos : 0 < ‖(p y : ℂ) - (p x : ℂ)‖ :=
          lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
        have hmul : ‖(p y : ℂ) - (p x : ℂ)‖ * ‖(p y : ℂ) - (p x : ℂ)‖
            ≤ ‖x - y‖ * ‖(p y : ℂ) - (p x : ℂ)‖ := by
          simpa [pow_two] using h5
        exact le_of_mul_le_mul_right hmul hpos
    rw [show (p x : ℂ) - (p y : ℂ) = -((p y : ℂ) - (p x : ℂ)) by ring, norm_neg]
    exact h8
  have hcont : Continuous p :=
    (LipschitzWith.of_dist_le_mul (f := p) (K := 1) fun x y => by
      rw [Subtype.dist_eq, dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
      exact hlip x y).continuous
  exact ⟨⟨p, hcont⟩, fun x => hp_fix x⟩

end Commons.Topology.Plane