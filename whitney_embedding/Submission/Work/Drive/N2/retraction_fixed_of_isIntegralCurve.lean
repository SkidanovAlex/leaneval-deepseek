import Mathlib
import Submission.Work.ODE.CompactSupportBounds

namespace Work.Drive.N2

/-- Auxiliary general form of `retraction_fixed_of_isIntegralCurve`, stated for a general real inner
product space `E`. Working in the abstract space avoids the `EuclideanSpace` instance diamond
(`PiLp` vs `WithLp`) that otherwise obstructs the differential manipulations inside the proof.

If `F` is a smooth map of `E`, `G` a compactly supported vector field whose values lie in the range
of `fderiv F` everywhere, and which is orthogonal to `y - F y` on its own (topological) support,
then any integral curve `γ` of `G` starting at a fixed point of `F` remains in the fixed point set
of `F`. -/
theorem retraction_fixed_of_isIntegralCurve_general {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F G : E → E) (γ : ℝ → E)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hYrange : ∀ y, G y ∈ (fderiv ℝ F y).range)
    (horth : ∀ y, y ∈ tsupport G → y - F y ∈ (fderiv ℝ F y).rangeᗮ)
    (hγ : IsIntegralCurve γ (fun _ z => G z))
    (h0 : F (γ 0) = γ 0) :
    ∀ t, F (γ t) = γ t := by
  have hFdiff : Differentiable ℝ F := hF.differentiable (by simp)
  -- The derivative of `‖F (γ t) - γ t‖ ^ 2` vanishes: the tangent direction
  -- `fderiv F (γ t) (G (γ t)) - G (γ t)` lies in the range of `fderiv F (γ t)`, while
  -- `F (γ t) - γ t` is orthogonal to that range (either because `γ t` lies in the support, or
  -- because then `G (γ t) = 0`).
  have key : ∀ t, inner ℝ ((F ∘ γ - γ) t) ((fderiv ℝ F (γ t)) (G (γ t)) - G (γ t)) = 0 := by
    intro t
    by_cases ht : γ t ∈ tsupport G
    · have hd : F (γ t) - γ t ∈ (fderiv ℝ F (γ t)).rangeᗮ := by
        have h1 := horth (γ t) ht
        simpa [neg_sub] using neg_mem h1
      have hu1 : (fderiv ℝ F (γ t)) (G (γ t)) ∈ (fderiv ℝ F (γ t)).range :=
        LinearMap.mem_range.mpr ⟨G (γ t), rfl⟩
      exact Submodule.inner_left_of_mem_orthogonal (sub_mem hu1 (hYrange (γ t))) hd
    · have hG0 : G (γ t) = 0 := Function.notMem_support.mp fun h => ht (subset_closure h)
      simp [hG0]
  have hgd : ∀ t, HasDerivAt (fun s => ‖(F ∘ γ - γ) s‖ ^ 2)
      (2 * inner ℝ ((F ∘ γ - γ) t) ((fderiv ℝ F (γ t)) (G (γ t)) - G (γ t))) t := by
    intro t
    have h1 : HasDerivAt (F ∘ γ) ((fderiv ℝ F (γ t)) (G (γ t))) t :=
      (hFdiff (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t)
    exact (h1.sub (hγ t)).norm_sq
  have hderiv0 : ∀ t, deriv (fun s => ‖(F ∘ γ - γ) s‖ ^ 2) t = 0 := fun t => by
    rw [(hgd t).deriv, key t, mul_zero]
  have hdiff : Differentiable ℝ (fun s => ‖(F ∘ γ - γ) s‖ ^ 2) :=
    fun t => (hgd t).differentiableAt
  intro t
  have hconst := is_const_of_deriv_eq_zero hdiff hderiv0 t 0
  have hzero : ‖(F ∘ γ - γ) t‖ ^ 2 = 0 := by
    rw [hconst]
    have : (F ∘ γ - γ) 0 = 0 := by
      simp only [Pi.sub_apply, Function.comp_apply, h0, sub_self]
    rw [this]; simp
  have hw0 : (F ∘ γ - γ) t = 0 := by
    have hnorm : ‖(F ∘ γ - γ) t‖ = 0 := sq_eq_zero_iff.mp hzero
    exact norm_eq_zero.mp hnorm
  exact sub_eq_zero.mp hw0

theorem retraction_fixed_of_isIntegralCurve {N : ℕ}
    (E Y : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (γ : ℝ → EuclideanSpace ℝ (Fin N))
    (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E)
    (hY : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Y)
    (hc : HasCompactSupport Y)
    (hYrange : ∀ y, Y y ∈ (fderiv ℝ E y).range)
    (horth : ∀ y, y ∈ tsupport Y → y - E y ∈ (fderiv ℝ E y).rangeᗮ)
    (hγ : IsIntegralCurve γ (fun _ z => Y z))
    (h0 : E (γ 0) = γ 0) :
    ∀ t, E (γ t) = γ t :=
  retraction_fixed_of_isIntegralCurve_general E Y γ hE hYrange horth hγ h0

end Work.Drive.N2
