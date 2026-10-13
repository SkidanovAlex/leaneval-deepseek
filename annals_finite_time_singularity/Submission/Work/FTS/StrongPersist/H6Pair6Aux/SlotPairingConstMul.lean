import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.Slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Scalar multiples in the elementary slot pairing

The elementary slot pairing
`slotPairing ρ a b u v = ∫_z ∫_θ ρ · (D_z^bD_θ^a u) · (D_z^bD_θ^a v)`
(`Work.FTS.TransportS.slotPairing`) is `ℝ`-linear in its first slot *whenever the other
factors are fixed only by the weight `ρ` and the second slot*: for every constant `c : ℝ`,

`slotPairing ρ a b (c·v) f = c · slotPairing ρ a b v f`.

The whole content is that the iterated operators `D_z^b`, `D_θ^a` (and hence `mixed b a`)
commute with multiplication by a *constant* scalar factor, and that a constant is pulled out
of the iterated integral.  Both are unconditional (no smoothness of `v` is needed): the
`deriv` of a constant multiple is the constant multiple of the `deriv` — `deriv_const_mul_field`
holds for the totalised `deriv` as well, because `λ·v` is differentiable exactly where `v` is,
and elsewhere both sides vanish.

This is the linearity step used to reduce a pairing of a scalar multiple of the vorticity to
the pairing of the vorticity itself.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The iterated operators commute with constant scalar factors -/

/-- `∂_z^k(c·f) = c·∂_z^k f`, unconditionally (pointwise in `(z,θ)`). -/
theorem pzIter_const_mul_pure (c : ℝ) (f : ℝ → ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pzIter k f z θ := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.pz]
    exact deriv_const_mul_field c

/-- `D_θ^i(c·f) = c·D_θ^i f`, unconditionally (pointwise in `(z,θ)`). -/
theorem DthIter_const_mul_pure (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [deriv_const_mul_field c]
    ring

/-- `D_z^j(c·f) = c·D_z^j f`, unconditionally (pointwise in `(z,θ)`). -/
theorem DzIter_const_mul_pure (c : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter j f z θ := by
  induction j with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [deriv_const_mul_field c]
    ring

/-- `D_z^jD_θ^i(c·f) = c·D_z^jD_θ^i f`, unconditionally (pointwise in `(z,θ)`). -/
theorem mixed_const_mul_pure (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  rw [Work.Spaces.mixed, Work.Spaces.mixed, DthIter_const_mul_pure, DzIter_const_mul_pure]

/-! ## The pairing -/

/-- **The elementary slot pairing is `ℝ`-homogeneous in its first slot**: multiplying the
first argument by a constant multiplies the pairing by that constant. -/
theorem SlotPairingConstMul {ρ : ℝ → ℝ → ℝ} (a b : ℕ) (c : ℝ) {v f : ℝ → ℝ → ℝ}
      (hv : Work.FTS.EllipticEst.SmoothOpen v) :
      Work.FTS.TransportS.slotPairing ρ a b (fun z θ => c * v z θ) f
        = c * Work.FTS.TransportS.slotPairing ρ a b v f := by
  unfold Work.FTS.TransportS.slotPairing
  rw [mixed_const_mul_pure c v b a]
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ,
          ρ z θ * (c * Work.Spaces.mixed b a v z θ) * Work.Spaces.mixed b a f z θ)
        = c * ∫ θ in Work.Spaces.Iθ,
            ρ z θ * Work.Spaces.mixed b a v z θ * Work.Spaces.mixed b a f z θ := by
    intro z
    rw [show (fun θ => ρ z θ * (c * Work.Spaces.mixed b a v z θ)
            * Work.Spaces.mixed b a f z θ)
          = fun θ => c * (ρ z θ * Work.Spaces.mixed b a v z θ
            * Work.Spaces.mixed b a f z θ) from funext fun θ => by ring]
    rw [MeasureTheory.integral_const_mul]
  rw [show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * (c * Work.Spaces.mixed b a v z θ) * Work.Spaces.mixed b a f z θ)
      = ∫ z in Work.Spaces.Iz, c * (∫ θ in Work.Spaces.Iθ,
          ρ z θ * Work.Spaces.mixed b a v z θ * Work.Spaces.mixed b a f z θ) from
    integral_congr_ae (Filter.Eventually.of_forall hinner)]
  rw [MeasureTheory.integral_const_mul]

end Work.FTS.StrongPersist.H6Pair6Aux
