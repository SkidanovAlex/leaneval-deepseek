/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W/slot11_aux`: the shifted-slice vocabulary for `slot11_bound`

Definitions and elementary (pointwise / slicewise) facts behind the proof of
`Work.FTS.EllipticEst.H2W.slot11_bound`, the `(1,1)`-mixed slot of `∂_θθΨ`:

  `L2Sq (fun z θ => mixed 1 1 (∂_θθΨ) z θ * Wt α z θ)`
    `= ∫_z w(z)² ∫_θ (∂_θ³(D_zΨ))² sin(2θ)^{2-γ}`,

i.e. the Step-4 quantity of the **shifted** slice `u = D_zΨ`, whose source is
`Gsrc α (D_zF) (D_zΨ)`.

* `slot11Sh`, `slot11A` — the shifted slice `D_zΨ` and the radial field `A = z²∂_z²Ψ`;
* `slot11_mixed_eq` — `mixed 1 1 (∂_θθΨ) = sin(2θ)·∂_θ³(D_zΨ)` on the open quadrant;
* `slot11_slice_eqn` — `Lzero1 (D_zΨ-slice) = Gsrc α (D_zF) (D_zΨ)` on the open quadrant;
* `slot11_z_identities` — `D_z(A) = z²∂_z²(D_zΨ)` and `D_z²Ψ = z∂_z(D_zΨ)`;
* `slot11_Lzero1_form` — `Gsrc α (D_zF) (D_zΨ) = D_zF + α²D_z(A) + α(5+α)D_z²Ψ`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.remov.Dz_slice_identities
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-- The shifted slice of `Ψ`: `z·∂_zΨ`. -/
def slot11Sh (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.DzIter 1 Ψ z θ

/-- The radial quantity `A = z²∂_z²Ψ` (`z²∂_z² = D_z² − D_z`). -/
def slot11A (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-- `mixed 1 1 (∂_θθΨ) = sin(2θ)·∂_θ³(D_zΨ)` on the open quadrant: Clairaut across the `z`- and
`θ`-derivatives. -/
theorem slot11_mixed_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed 1 1 (Work.Spaces.pthIter 2 Ψ) z θ
        = Real.sin (2 * θ) * Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ := by
  intro z θ hz hθ hθ'
  have hcl : Work.Spaces.pz (Work.Spaces.pthIter 3 Ψ) z θ
      = Work.Spaces.pthIter 3 (Work.Spaces.pz Ψ) z θ :=
    Work.FTS.EllipticEst.remov.pz_pthIter_comm_open Ψ hΨ 3 z θ hz hθ hθ'
  have hmul : Work.Spaces.pthIter 3 (fun z θ => z * Work.Spaces.pz Ψ z θ) z θ
      = z * Work.Spaces.pthIter 3 (Work.Spaces.pz Ψ) z θ := by
    simpa using congrFun (congrFun
      (Work.FTS.EllipticEst.remov.pthIter_mul_fst (Work.Spaces.pz Ψ) 3) z) θ
  have hDz : Work.Spaces.DzIter 1 Ψ = fun z θ => z * Work.Spaces.pz Ψ z θ := by
    rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
    rfl
  -- (1) `mixed 1 1 (∂_θθΨ) = sin(2θ) · D_z(∂_θ³Ψ)`
  have h1 : Work.Spaces.mixed 1 1 (Work.Spaces.pthIter 2 Ψ) z θ
      = Real.sin (2 * θ) * Work.Spaces.Dz (Work.Spaces.pthIter 3 Ψ) z θ := by
    show Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.pthIter 2 Ψ)) z θ = _
    have hfun : Work.Spaces.Dth (Work.Spaces.pthIter 2 Ψ)
        = fun z θ => Real.sin (2 * θ) * Work.Spaces.pthIter 3 Ψ z θ := rfl
    have hfun2 : Work.Spaces.Dz (fun z θ => Real.sin (2 * θ) * Work.Spaces.pthIter 3 Ψ z θ)
        = fun z θ => Real.sin (2 * θ) * Work.Spaces.Dz (Work.Spaces.pthIter 3 Ψ) z θ := by
      funext z' θ'
      show z' * deriv (fun z'' => Real.sin (2 * θ') * Work.Spaces.pthIter 3 Ψ z'' θ') z'
        = Real.sin (2 * θ') * (z' * deriv (fun z'' => Work.Spaces.pthIter 3 Ψ z'' θ') z')
      rw [deriv_const_mul_field]
      ring
    rw [hfun, hfun2]
  -- (2) `D_z(∂_θ³Ψ) = ∂_θ³(D_zΨ)`
  have h2 : Work.Spaces.Dz (Work.Spaces.pthIter 3 Ψ) z θ
      = Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ := by
    show z * Work.Spaces.pz (Work.Spaces.pthIter 3 Ψ) z θ = _
    rw [hcl, hDz, hmul]
  rw [h1, h2]

/-- The `Lzero1`-equation of the shifted slice: the shifted datum `(D_zF, D_zΨ)` again satisfies
the slice equation, with source `Gsrc α (D_zF) (D_zΨ)`. -/
theorem slot11_slice_eqn {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.DzIter 1 Ψ z t) θ
        = Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
            (Work.Spaces.DzIter 1 Ψ) z θ := by
  intro z hz θ hθ hθ'
  refine Work.FTS.EllipticEst.Mine.Lzero1_slice_eq_Gsrc
    (F := Work.Spaces.DzIter 1 F) (Ψ := Work.Spaces.DzIter 1 Ψ)
    (fun z' hz' θ' hθ1 hθ2 => ?_) hz hθ hθ'
  exact Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 hsm heq z' hz' θ' hθ1 hθ2

/-- The two `z`-identities relating the shifted slice to `A = z²∂_z²Ψ` and to `D_z²Ψ`. -/
theorem slot11_z_identities {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter 1 (slot11A Ψ) z θ
        = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
    ∧ (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z θ
        = Work.Spaces.DzIter 2 Ψ z θ) := by
  constructor
  · intro z θ hz hθ hθ'
    exact (Work.FTS.EllipticEst.remov.Dz_slice_identities Ψ hΨ).1 z θ hz hθ hθ'
  · intro z θ hz hθ hθ'
    rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
    rfl

/-- The `D_z`-form of the source of the shifted slice. -/
theorem slot11_Lzero1_form {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
          (Work.Spaces.DzIter 1 Ψ) z θ
        = Work.Spaces.DzIter 1 F z θ
          + α ^ 2 * Work.Spaces.DzIter 1 (slot11A Ψ) z θ
          + (α * (5 + α)) * Work.Spaces.DzIter 2 Ψ z θ := by
  intro z θ hz hθ hθ'
  obtain ⟨h1, h2⟩ := slot11_z_identities hΨ
  rw [Work.FTS.EllipticEst.Mine.Gsrc, ← h1 z θ hz hθ hθ', h2 z θ hz hθ hθ']

/-! ## The algebra of the two weights

The `(1,1)`-mixed slot of `∂_θθ f` carries the weight `Wt = w·sin(2θ)^{-γ/2}`, and the third
`θ`-derivative of the shifted slice carries `w·sin(2θ)^{(2-γ)/2}`; the pointwise identity
`mixed 1 1 (∂_θθf) = sin(2θ)·∂_θ³(D_zf)` therefore converts one into the other. -/

/-- The elementary real-power identity behind the conversion. -/
theorem slot11_rpow_alg {γ s Y w : ℝ} (hs : 0 < s) :
    (s * Y * (w * s ^ (-(γ / 2)))) ^ 2 = w ^ 2 * Y ^ 2 * s ^ (2 - γ) := by
  have hs0 : 0 ≤ s := le_of_lt hs
  have hX : (s ^ (-(γ / 2))) ^ 2 = s ^ (-γ) := by
    rw [← Real.rpow_two (s ^ (-(γ / 2))), ← Real.rpow_mul hs0 (-(γ / 2)) 2]
    congr 1
    ring
  have hY : s ^ 2 * s ^ (-γ) = s ^ (2 - γ) := by
    rw [← Real.rpow_two s, ← Real.rpow_add hs 2 (-γ)]
    congr 1
  calc (s * Y * (w * s ^ (-(γ / 2)))) ^ 2
      = (s ^ 2 * Y ^ 2) * (w ^ 2 * (s ^ (-(γ / 2))) ^ 2) := by ring
    _ = (s ^ 2 * Y ^ 2) * (w ^ 2 * s ^ (-γ)) := by rw [hX]
    _ = w ^ 2 * Y ^ 2 * (s ^ 2 * s ^ (-γ)) := by ring
    _ = w ^ 2 * Y ^ 2 * s ^ (2 - γ) := by rw [hY]

/-- **The integrand identity of the `(1,1)`-slot.**  On the open quadrant, the squared weighted
`(1,1)`-slot of `∂_θθf` is `w²·(∂_θ³(D_zf))²·sin(2θ)^{2-γ}`. -/
theorem slot11_sq_eq {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed 1 1 (Work.Spaces.pthIter 2 f) z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2
            * (Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 f) z θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α) := by
  intro z θ hz hθ hθ'
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ', Real.pi_pos])
  have hkey := slot11_rpow_alg (γ := Work.Spaces.gam α) (s := Real.sin (2 * θ))
    (Y := Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 f) z θ) (w := Work.Spaces.w z) hs
  rw [slot11_mixed_eq hf z θ hz hθ hθ']
  rw [show Work.Spaces.Wt α z θ
      = Work.Spaces.w z * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.gam α / 2)) from rfl]
  exact hkey

end Work.FTS.EllipticEst.H2W
