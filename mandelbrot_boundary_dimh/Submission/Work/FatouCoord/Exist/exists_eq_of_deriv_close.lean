import Mathlib

set_option linter.style.haveILetI false

open scoped Topology

namespace Work.FatouCoord.Exist

/-- Quantitative surjectivity of a map `ψ` whose derivative is close to `1` on a closed disk.

If `ψ` is complex-differentiable on the closed disk of radius `ρ > 0` around `τ`, and
`‖deriv ψ w - 1‖ ≤ q` there for some `q ∈ [0,1)`, and `ψ τ` lies within `(1 - q) ρ` of `τ`,
then `τ` is in the image of the closed disk.

The proof builds the contraction `T w = w - ψ w + τ`; the hypothesis on the derivative,
through the mean value inequality, makes `T` a `q`-contraction mapping the closed disk
into itself, and Banach's fixed point theorem furnishes `w` with `ψ w = τ`. -/
theorem exists_eq_of_deriv_close {ψ : ℂ → ℂ} {τ : ℂ} {ρ q : ℝ} (hρ : 0 < ρ) (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hdiff : ∀ w : ℂ, dist w τ ≤ ρ → DifferentiableAt ℂ ψ w)
    (hbound : ∀ w : ℂ, dist w τ ≤ ρ → ‖deriv ψ w - 1‖ ≤ q)
    (hclose : dist (ψ τ) τ ≤ (1 - q) * ρ) : ∃ w : ℂ, dist w τ ≤ ρ ∧ ψ w = τ := by
  set S : Set ℂ := Metric.closedBall τ ρ with hSdef
  have hSmem : ∀ w, w ∈ S ↔ dist w τ ≤ ρ := by
    intro w; rw [hSdef]; exact Metric.mem_closedBall
  have hSconv : Convex ℝ S := convex_closedBall τ ρ
  have hSclosed : IsClosed S := Metric.isClosed_closedBall
  -- the auxiliary map `g w = w - ψ w`, whose derivative `1 - deriv ψ w` is bounded by `q`
  set g : ℂ → ℂ := fun w => w - ψ w with hgdef
  have hgdiff : ∀ w ∈ S, DifferentiableAt ℂ g w := by
    intro w hw
    have hw' : dist w τ ≤ ρ := (hSmem w).mp hw
    show DifferentiableAt ℂ (fun w : ℂ => w - ψ w) w
    exact differentiableAt_id.sub (hdiff w hw')
  have hgderiv : ∀ w ∈ S, deriv g w = 1 - deriv ψ w := by
    intro w hw
    have hw' : dist w τ ≤ ρ := (hSmem w).mp hw
    show deriv (fun w : ℂ => w - ψ w) w = 1 - deriv ψ w
    have h2 : deriv (fun w : ℂ => w - ψ w) w = deriv (fun w : ℂ => w) w - deriv ψ w := by
      rw [show (fun w : ℂ => w - ψ w) = (fun w : ℂ => w) - ψ from rfl]
      exact deriv_sub differentiableAt_id (hdiff w hw')
    rw [h2]; simp
  have hgbound : ∀ w ∈ S, ‖deriv g w‖ ≤ q := by
    intro w hw
    rw [hgderiv w hw, norm_sub_rev]
    exact hbound w ((hSmem w).mp hw)
  have hglip : ∀ x ∈ S, ∀ y ∈ S, ‖g y - g x‖ ≤ q * ‖y - x‖ :=
    fun x hx y hy => Convex.norm_image_sub_le_of_norm_deriv_le hgdiff hgbound hSconv hx hy
  -- the contraction `T w = g w + τ = w - ψ w + τ`
  set T : ℂ → ℂ := fun w => g w + τ with hTdef
  have hτS : τ ∈ S := by rw [hSmem]; rw [dist_self]; exact hρ.le
  have hmaps : Set.MapsTo T S S := by
    intro w hw
    have hw' : dist w τ ≤ ρ := (hSmem w).mp hw
    have h1 : ‖g w - g τ‖ ≤ q * ρ := by
      have h := hglip τ hτS w hw
      have hwρ : ‖w - τ‖ ≤ ρ := by rwa [dist_eq_norm] at hw'
      exact le_trans h (mul_le_mul_of_nonneg_left hwρ hq0)
    have h2 : ‖g τ‖ ≤ (1 - q) * ρ := by
      show ‖τ - ψ τ‖ ≤ (1 - q) * ρ
      rw [show τ - ψ τ = -(ψ τ - τ) from by ring, norm_neg, ← dist_eq_norm]
      exact hclose
    rw [hSmem]
    show dist (g w + τ) τ ≤ ρ
    have h3 : dist (g w + τ) τ = ‖g w‖ := by rw [dist_eq_norm]; simp
    rw [h3]
    calc ‖g w‖ = ‖g τ + (g w - g τ)‖ := by rw [add_sub_cancel]
      _ ≤ ‖g τ‖ + ‖g w - g τ‖ := norm_add_le _ _
      _ ≤ (1 - q) * ρ + q * ρ := add_le_add h2 h1
      _ = ρ := by ring
  have hKlt : (⟨q, hq0⟩ : NNReal) < 1 := by show (q : ℝ) < 1; exact hq1
  have hcontr : ContractingWith (⟨q, hq0⟩ : NNReal) (hmaps.restrict T S S) := by
    refine ⟨hKlt, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    have hxy : dist (T (x : ℂ)) (T (y : ℂ)) ≤ q * dist (x : ℂ) (y : ℂ) := by
      have hTsub : T (x : ℂ) - T (y : ℂ) = g (x : ℂ) - g (y : ℂ) := by
        show g (x : ℂ) + τ - (g (y : ℂ) + τ) = g (x : ℂ) - g (y : ℂ); ring
      rw [dist_eq_norm, dist_eq_norm, hTsub]
      have h := hglip (x : ℂ) x.2 (y : ℂ) y.2
      simpa only [norm_sub_rev] using h
    rw [Subtype.dist_eq, Subtype.dist_eq]
    show dist (T (x : ℂ)) (T (y : ℂ)) ≤ q * dist (x : ℂ) (y : ℂ)
    exact hxy
  haveI : CompleteSpace ↥S := hSclosed.completeSpace_coe
  obtain ⟨y, hyfix, _⟩ := hcontr.exists_fixedPoint ⟨τ, hτS⟩ (edist_ne_top _ _)
  refine ⟨(y : ℂ), (hSmem y).mp y.2, ?_⟩
  have hTy : T (y : ℂ) = (y : ℂ) := by
    have := congrArg Subtype.val hyfix
    simpa [Set.MapsTo.val_restrict_apply] using this
  have hty : (y : ℂ) - ψ (y : ℂ) + τ = (y : ℂ) := by
    show g (y : ℂ) + τ = (y : ℂ)
    exact hTy
  linear_combination -hty

end Work.FatouCoord.Exist
