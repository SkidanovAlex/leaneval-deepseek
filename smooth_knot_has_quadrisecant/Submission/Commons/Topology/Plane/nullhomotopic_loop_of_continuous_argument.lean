import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Circle

namespace Commons.Topology.Plane

open Set

/-- If `exp (θ * I) = z / ‖z‖` then the number `‖z‖ * exp (θ * I)` is `z`. -/
private lemma norm_mul_exp_eq {z : ℂ} (hz : z ≠ 0) {θ : ℝ}
    (h : Complex.exp ((θ : ℂ) * Complex.I) = z / (‖z‖ : ℂ)) :
    (‖z‖ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = z := by
  rw [h, mul_div_assoc']
  exact mul_div_cancel_left₀ z (by exact_mod_cast (ne_of_gt (norm_pos_iff.mpr hz)))

/-- **A continuous argument on `Kᶜ` kills the fundamental group.**  If `K ⊆ ℂ` is closed,
`0 ∈ K`, and `θ` is a continuous argument on `Kᶜ` (`exp (θ z * I) = z / ‖z‖` for `z ∈ Kᶜ`),
then every loop in `Kᶜ` is null-homotopic inside `ℂ \ {0}`: there is a homotopy from the loop
to the constant loop at any of its points, whose values never vanish.

Suggested proof: the map `z ↦ z` and the radial map `z ↦ z / ‖z‖` on `Kᶜ` are homotopic
through radial scaling, and `(s, t) ↦ ‖γ t‖ ^ (1 - s) * exp ((1 - s) * θ (γ t) * I)` is a
null-homotopy of the radial map (at `s = 1` it is constantly `1`); finally join the constants
`1` and `γ t₀` inside `ℂ \ {0}`.

This is the easy half of `no_continuous_argument_of_bounded_component`; it is independent of
the geometric core. -/
theorem nullhomotopic_loop_of_continuous_argument {K : Set ℂ} (hK : IsClosed K)
    (h0 : (0 : ℂ) ∈ K)
    (hθ : ∃ θ : C({z : ℂ // z ∈ Kᶜ}, ℝ),
      ∀ z, Complex.exp ((θ z : ℝ) * Complex.I) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)))
    (γ : C(Circle, ℂ)) (hγ : ∀ t, γ t ∈ Kᶜ) (t₀ : Circle) :
    ∃ H : C(Circle × Set.Icc (0 : ℝ) 1, ℂ),
      (∀ t, H (t, (0 : Set.Icc (0 : ℝ) 1)) = γ t) ∧
      (∀ t, H (t, (1 : Set.Icc (0 : ℝ) 1)) = γ t₀) ∧
      ∀ p : Circle × Set.Icc (0 : ℝ) 1, H p ≠ (0 : ℂ) := by
  have _hK := hK
  obtain ⟨θ, hθ⟩ := hθ
  have hsub : Continuous fun t : Circle => (⟨γ t, hγ t⟩ : {z : ℂ // z ∈ Kᶜ}) :=
    Continuous.subtype_mk γ.continuous hγ
  have hθγ : Continuous fun t : Circle => θ ⟨γ t, hγ t⟩ := θ.continuous.comp hsub
  have hne : ∀ t : Circle, γ t ≠ 0 := by
    intro t h
    exact (hγ t) (by rw [h]; exact h0)
  have hkey : ∀ t : Circle,
      (‖γ t‖ : ℂ) * Complex.exp (((θ ⟨γ t, hγ t⟩ : ℝ) : ℂ) * Complex.I) = γ t := by
    intro t
    exact norm_mul_exp_eq (hne t) (hθ ⟨γ t, hγ t⟩)
  -- The null-homotopy: interpolate linearly between `γ t` and `γ t₀` in the "logarithmic"
  -- coordinates `‖z‖` and `θ z`.
  let F : Circle × Set.Icc (0 : ℝ) 1 → ℂ := fun p =>
    ((((1 - (p.2 : ℝ)) * ‖γ p.1‖ + (p.2 : ℝ) * ‖γ t₀‖ : ℝ)) : ℂ) *
      Complex.exp (((((1 - (p.2 : ℝ)) * θ ⟨γ p.1, hγ p.1⟩
        + (p.2 : ℝ) * θ ⟨γ t₀, hγ t₀⟩ : ℝ)) : ℂ) * Complex.I)
  have hs : Continuous fun p : Circle × Set.Icc (0 : ℝ) 1 => (p.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have h1s : Continuous fun p : Circle × Set.Icc (0 : ℝ) 1 => (1 : ℝ) - (p.2 : ℝ) :=
    continuous_const.sub hs
  have hγc : Continuous fun p : Circle × Set.Icc (0 : ℝ) 1 => γ p.1 :=
    γ.continuous.comp continuous_fst
  have hθc : Continuous fun p : Circle × Set.Icc (0 : ℝ) 1 => θ ⟨γ p.1, hγ p.1⟩ :=
    hθγ.comp continuous_fst
  have hM : Continuous fun p : Circle × Set.Icc (0 : ℝ) 1 =>
      ((1 - (p.2 : ℝ)) * ‖γ p.1‖ + (p.2 : ℝ) * ‖γ t₀‖ : ℝ) :=
    (h1s.mul hγc.norm).add (hs.mul continuous_const)
  have hA : Continuous fun p : Circle × Set.Icc (0 : ℝ) 1 =>
      ((1 - (p.2 : ℝ)) * θ ⟨γ p.1, hγ p.1⟩ + (p.2 : ℝ) * θ ⟨γ t₀, hγ t₀⟩ : ℝ) :=
    (h1s.mul hθc).add (hs.mul continuous_const)
  have hF : Continuous F := by
    rw [show F = fun p : Circle × Set.Icc (0 : ℝ) 1 =>
      ((fun p => ((1 - (p.2 : ℝ)) * ‖γ p.1‖ + (p.2 : ℝ) * ‖γ t₀‖ : ℝ)) p : ℂ) *
        Complex.exp (((fun p => ((1 - (p.2 : ℝ)) * θ ⟨γ p.1, hγ p.1⟩
          + (p.2 : ℝ) * θ ⟨γ t₀, hγ t₀⟩ : ℝ)) p : ℂ) * Complex.I) from rfl]
    exact (Complex.continuous_ofReal.comp hM).mul
      (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hA).mul continuous_const))
  let H : C(Circle × Set.Icc (0 : ℝ) 1, ℂ) := ⟨F, hF⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · intro t
    change F (t, (0 : Set.Icc (0 : ℝ) 1)) = γ t
    have : F (t, (0 : Set.Icc (0 : ℝ) 1)) =
        (‖γ t‖ : ℂ) * Complex.exp (((θ ⟨γ t, hγ t⟩ : ℝ) : ℂ) * Complex.I) := by
      simp [F]
    rw [this]
    exact hkey t
  · intro t
    change F (t, (1 : Set.Icc (0 : ℝ) 1)) = γ t₀
    have : F (t, (1 : Set.Icc (0 : ℝ) 1)) =
        (‖γ t₀‖ : ℂ) * Complex.exp (((θ ⟨γ t₀, hγ t₀⟩ : ℝ) : ℂ) * Complex.I) := by
      simp [F]
    rw [this]
    exact hkey t₀
  · intro p
    change F p ≠ 0
    have hpos : 0 < (1 - (p.2 : ℝ)) * ‖γ p.1‖ + (p.2 : ℝ) * ‖γ t₀‖ := by
      have hs0 : (0 : ℝ) ≤ p.2 := p.2.2.1
      have hs1 : (p.2 : ℝ) ≤ 1 := p.2.2.2
      have ha : 0 < ‖γ p.1‖ := norm_pos_iff.mpr (hne p.1)
      have hb : 0 < ‖γ t₀‖ := norm_pos_iff.mpr (hne t₀)
      rcases le_total (‖γ p.1‖) (‖γ t₀‖) with h | h
      · nlinarith [mul_le_mul_of_nonneg_left h hs0]
      · nlinarith [mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hs1)]
    have : F p = (((1 - (p.2 : ℝ)) * ‖γ p.1‖ + (p.2 : ℝ) * ‖γ t₀‖ : ℝ) : ℂ) *
        Complex.exp ((((1 - (p.2 : ℝ)) * θ ⟨γ p.1, hγ p.1⟩
          + (p.2 : ℝ) * θ ⟨γ t₀, hγ t₀⟩ : ℝ) : ℂ) * Complex.I) := rfl
    rw [this]
    exact mul_ne_zero (by exact_mod_cast (ne_of_gt hpos)) (Complex.exp_ne_zero _)

end Commons.Topology.Plane