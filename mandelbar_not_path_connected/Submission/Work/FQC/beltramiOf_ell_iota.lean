import Mathlib
import Submission.Work.FQC.Defs
import Submission.Work.FQC.saw_add_half
import Submission.Work.FQC.ell_beltrami_conj
import Submission.Work.MRMT.Wirtinger.beltramiOf_comp_antiholo

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `μ_{ℓ_t}(conj w + 1/2) = conj (μ_{ℓ_t} w)`, everywhere

The MNS twist `ℓ_t` commutes with the reflection `σ w = conj w + 1/2` of the Écalle cylinder
(`Work.FQC.ell_sigmaCyl`), which gives the conjugation identity for the complex dilatation at
every point where `ℓ_t` is real differentiable (`Work.FQC.beltramiOf_sigmaCyl_conj`).  The
a.e. version is `Work.FQC.ell_beltrami_conj`.

This file removes the "a.e.": the only missing ingredient is that `ℓ_t` is real differentiable
at `w` if and only if it is real differentiable at `σ w`.  That is a formal consequence of the
commutation `ℓ_t ∘ σ = σ ∘ ℓ_t` together with the fact that `σ` is a diffeomorphism of `ℂ`
(with inverse `σ⁻¹ w = conj w - 1/2`): if `F` commutes with a diffeomorphism `σ`, then
`F = (F ∘ σ) ∘ σ⁻¹`, so differentiability of `F ∘ σ` at a point transports back to `F`, while
`F ∘ σ = σ ∘ F` transports differentiability of `F` forward.  Where `ℓ_t` is not
differentiable both Wirtinger derivatives vanish (junk values of `fderiv`), so the complex
dilatation is `0` there and the identity holds trivially.
-/

open scoped ComplexConjugate

noncomputable section

namespace Work.FQC

/-! ## 1. The inverse reflection `σ⁻¹ w = conj w - 1/2` -/

/-- The inverse of the reflection `σ w = conj w + 1/2` of the Écalle cylinder:
`σ⁻¹ u = conj u - 1/2`. -/
def sigmaCylInv (u : ℂ) : ℂ := star u - 1/2

@[simp] theorem sigmaCylInv_apply (u : ℂ) : sigmaCylInv u = star u - 1/2 := rfl

theorem sigmaCyl_sigmaCylInv (u : ℂ) : sigmaCyl (sigmaCylInv u) = u := by
  simp only [sigmaCyl, sigmaCylInv, star_sub, star_star]
  rw [show star ((1 : ℂ)/2) = (1 : ℂ)/2 from by norm_num [Complex.star_def]]
  ring

theorem sigmaCylInv_sigmaCyl (u : ℂ) : sigmaCylInv (sigmaCyl u) = u := by
  rw [sigmaCyl_apply]
  simp only [sigmaCylInv, star_add, star_star]
  rw [show star ((1 : ℂ)/2) = (1 : ℂ)/2 from by norm_num [Complex.star_def]]
  ring

theorem differentiableAt_sigmaCylInv (u : ℂ) : DifferentiableAt ℝ sigmaCylInv u := by
  have h1 : DifferentiableAt ℝ (fun z : ℂ => star z - 1/2) u :=
    (Work.MRMT.Wirtinger.differentiableAt_star u).sub_const (1/2 : ℂ)
  exact h1

/-- The twist commutes with the inverse reflection `σ⁻¹` as well. -/
theorem ell_sigmaCylInv (t : ℝ) (u : ℂ) : ell t (sigmaCylInv u) = sigmaCylInv (ell t u) := by
  have hre : (sigmaCylInv u).re = u.re - 1/2 := by simp [sigmaCylInv]
  have hs : saw ((sigmaCylInv u).re) = - saw u.re := by
    rw [hre]
    have h := saw_add_half (u.re - 1/2)
    rw [show u.re - 1/2 + 1/2 = u.re by ring] at h
    linarith [h]
  rw [ell_apply, ell_apply, hs, sigmaCylInv_apply, sigmaCylInv_apply, star_add, star_mul]
  have hI : star (Complex.I : ℂ) = -Complex.I := by simp
  have hA : star (((t * saw u.re : ℝ)) : ℂ) = ((t * saw u.re : ℝ) : ℂ) := by simp
  rw [hI, hA]
  push_cast
  ring

/-! ## 2. Symmetry of differentiability under the reflection -/

/-- `ℓ_t` is real differentiable at `w` if and only if it is real differentiable at `σ w`. -/
theorem differentiableAt_ell_sigmaCyl_iff (t : ℝ) (w : ℂ) :
    DifferentiableAt ℝ (ell t) w ↔ DifferentiableAt ℝ (ell t) (sigmaCyl w) := by
  constructor
  · intro h
    have h1 : DifferentiableAt ℝ (sigmaCyl ∘ (ell t)) w :=
      (differentiableAt_sigmaCyl (ell t w)).comp w h
    have h2 : DifferentiableAt ℝ ((ell t) ∘ sigmaCyl) w := by
      rw [show (ell t) ∘ sigmaCyl = sigmaCyl ∘ (ell t) from funext (ell_sigmaCyl t)]
      exact h1
    have h2' : DifferentiableAt ℝ ((ell t) ∘ sigmaCyl) (sigmaCylInv (sigmaCyl w)) := by
      rwa [sigmaCylInv_sigmaCyl w]
    have h3 : DifferentiableAt ℝ (((ell t) ∘ sigmaCyl) ∘ sigmaCylInv) (sigmaCyl w) :=
      h2'.comp (sigmaCyl w) (differentiableAt_sigmaCylInv (sigmaCyl w))
    rwa [show ((ell t) ∘ sigmaCyl) ∘ sigmaCylInv = ell t from
      funext (fun u => by rw [Function.comp_apply, Function.comp_apply, sigmaCyl_sigmaCylInv u])
      ] at h3
  · intro h
    have h1 : DifferentiableAt ℝ (sigmaCylInv ∘ (ell t)) (sigmaCyl w) :=
      (differentiableAt_sigmaCylInv (ell t (sigmaCyl w))).comp (sigmaCyl w) h
    have h2 : DifferentiableAt ℝ ((ell t) ∘ sigmaCylInv) (sigmaCyl w) := by
      rw [show (ell t) ∘ sigmaCylInv = sigmaCylInv ∘ (ell t)
        from funext (ell_sigmaCylInv t)]
      exact h1
    have h3 : DifferentiableAt ℝ (((ell t) ∘ sigmaCylInv) ∘ sigmaCyl) w :=
      h2.comp w (differentiableAt_sigmaCyl w)
    rwa [show ((ell t) ∘ sigmaCylInv) ∘ sigmaCyl = ell t from
      funext (fun u => by rw [Function.comp_apply, Function.comp_apply, sigmaCylInv_sigmaCyl u])
      ] at h3

/-! ## 3. Where `ℓ_t` is not differentiable, its dilatation vanishes -/

/-- A map that is not real differentiable at `z` has complex dilatation `0`: both Wirtinger
derivatives, being computed from `fderiv ℝ`, vanish there. -/
theorem beltramiOf_eq_zero_of_not_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (h : ¬ DifferentiableAt ℝ f z) : Work.MRMT.beltramiOf f z = 0 := by
  have hf : fderiv ℝ f z = 0 := fderiv_zero_of_not_differentiableAt h
  simp [Work.MRMT.beltramiOf, Work.MRMT.dz, Work.MRMT.dzbar, hf]

/-! ## 4. The theorem -/

theorem beltramiOf_ell_iota (t : ℝ) (w : ℂ) :
    Work.MRMT.beltramiOf (Work.FQC.ell t) (star w + 1 / 2) =
      star (Work.MRMT.beltramiOf (Work.FQC.ell t) w) := by
  have hcomm : (ell t) ∘ sigmaCyl = sigmaCyl ∘ (ell t) := funext (ell_sigmaCyl t)
  by_cases hw : DifferentiableAt ℝ (ell t) w
  · have hσw : DifferentiableAt ℝ (ell t) (sigmaCyl w) :=
      (differentiableAt_ell_sigmaCyl_iff t w).mp hw
    have h := beltramiOf_sigmaCyl_conj hw hσw hcomm
    simpa only [sigmaCyl_apply] using h
  · have hσw : ¬ DifferentiableAt ℝ (ell t) (sigmaCyl w) :=
      fun h => hw ((differentiableAt_ell_sigmaCyl_iff t w).mpr h)
    rw [show star w + 1 / 2 = sigmaCyl w from rfl,
      beltramiOf_eq_zero_of_not_differentiableAt hσw,
      beltramiOf_eq_zero_of_not_differentiableAt hw, star_zero]

end Work.FQC
