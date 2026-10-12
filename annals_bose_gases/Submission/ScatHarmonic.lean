import ChallengeDeps
import Submission.PotSupport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Exterior weak harmonicity of the scattering solution

If the potential `v` vanishes on the exterior region `{x | R ≤ ‖x‖}` (which
follows from `tsupport v ⊆ ball 0 R`), then the scattering equation
`−Δω = v(1−ω)/2` has zero right-hand side there, so any scattering solution
`w` is weakly harmonic on that region:

    ∀ φ ∈ C∞c with tsupport φ ⊆ {x | R ≤ ‖x‖} :  ∫ w · Δφ = 0 .

This is a pure consequence of the axioms of `IsScatteringSolution` plus the
support hypothesis on `v` (the pointwise vanishing of `v` on the exterior
kills the right-hand side of the weak equation for such test functions).  It
is the first step toward the Layer-3 fact `ω(x) = a/‖x‖` for `‖x‖ ≥ R`
(radial weakly-harmonic functions with decay at infinity are `c/‖x‖`).
-/

noncomputable section

open _root_.BoseGases
open _root_.BoseGases.IsScatteringSolution
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real
open Laplacian

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Membership of the (topological) support forces the value to be non-zero
(classical fact, stated here for convenience). -/
lemma tsupport_eq_zero_of_not_mem {α : Type*} [Zero α] {f : ℝ³ → α} {x : ℝ³}
    (hx : x ∉ tsupport f) : f x = 0 := by
  by_contra h
  exact hx (subset_tsupport f (by simpa [Function.support] using h))

/-- The exterior region is where the potential vanishes, so the right-hand
side of the scattering weak equation is zero for exterior test functions: on
`{x | R ≤ ‖x‖}` the factor `v x` vanishes and inside the ball the factor
`φ x` vanishes (as `x ∉ tsupport φ`), so the integrand is pointwise zero. -/
lemma exterior_rhs_zero {v w : ℝ³ → ℝ} {R : ℝ}
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    {φ : ℝ³ → ℝ} (hφsupp : tsupport φ ⊆ {x : ℝ³ | R ≤ ‖x‖}) :
    (fun x : ℝ³ => v x * (1 - w x) * φ x) = 0 := by
  funext x
  by_cases hge : R ≤ ‖x‖
  · have hvx : v x = 0 := v_eq_zero_of_norm_ge hsupp hge
    simp [hvx]
  · have hlt : ‖x‖ < R := lt_of_not_ge hge
    have hxnot : x ∉ {y : ℝ³ | R ≤ ‖y‖} := by
      intro hxmem
      exact (not_le_of_gt hlt) hxmem
    have hxφ : x ∉ tsupport φ := by
      intro h
      exact hxnot (hφsupp h)
    have hφx : φ x = 0 := tsupport_eq_zero_of_not_mem (f := φ) hxφ
    simp [hφx]

/-- Exterior weak harmonicity: test functions whose (topological) support
lies in the exterior region `{x | R ≤ ‖x‖}` annihilate `w` under the
Laplacian pairing. -/
lemma scattering_harmonic_exterior {v w : ℝ³ → ℝ} {R : ℝ}
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) (hw : IsScatteringSolution w v)
    {φ : ℝ³ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcomp : HasCompactSupport φ)
    (hφsupp : tsupport φ ⊆ {x : ℝ³ | R ≤ ‖x‖}) :
    ∫ x : ℝ³, w x * (Δ φ) x = 0 := by
  have hB : (∫ x : ℝ³, v x * (1 - w x) * φ x) = 0 := by
    have hpoint : (fun x : ℝ³ => v x * (1 - w x) * φ x) = 0 :=
      exterior_rhs_zero hsupp hφsupp
    rw [hpoint]
    simp
  have heq := hw.eq φ ⟨hφ, hcomp⟩
  have hneg : -∫ x : ℝ³, w x * (Δ φ) x = 0 := by
    rw [heq, hB]
    norm_num
  exact neg_eq_zero.mp hneg

end Submission.BoseGases
