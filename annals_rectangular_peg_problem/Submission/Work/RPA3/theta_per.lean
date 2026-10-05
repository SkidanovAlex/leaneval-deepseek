import Mathlib
import Submission.Work.RPA3.TubularDefs
import Submission.Work.RPA3.Symp

namespace Work.RPA3

/-- The tubular map inherits the `2π`-periodicity of the family in the angle `t`:
`θ(τ,x,t+2π,ξ) = Tk 1 (θ(τ,x,t,ξ))`.

Proof: `ℓ` is `Tk 1`-equivariant in `t` (`LagFamilyAll.per`), `Tk 1` is the translation by
`(0,2π)` in `q₂` (so it is additive and its derivative is the identity), and `J` is linear
(`Work.RPA3.J_add`, `Work.RPA3.J_smul`); hence the slice derivatives `∂_xℓ(·,t+2π)` and
`∂_tℓ(·,t+2π)` equal the ones at `t`. -/
theorem theta_per (L : Work.RPA3.LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ) :
    Work.RPA3.theta L τ x (t + 2 * Real.pi) ξ = Work.RPA3.Tk 1 (Work.RPA3.theta L τ x t ξ) := by
  -- `Tk 1` is the translation by `c = (0,2π)` in the second position of `q`.
  have hTk : ∀ a : PS, Tk (1 : ℤ) a = a + ((0, 2 * Real.pi), (0, 0)) := by
    intro a
    ext <;> simp [Tk]
  -- hence `ℓ` is equivariant: `ℓ τ (y, t+2π) = ℓ τ (y,t) + c`.
  have hper : ∀ y : ℝ, L.ℓ τ (y, t + 2 * Real.pi)
      = L.ℓ τ (y, t) + ((0, 2 * Real.pi), (0, 0)) := by
    intro y
    rw [L.per τ y t, hTk]
  -- the `x`-slice derivative is unchanged by the constant translation.
  have hdx : deriv (fun y => L.ℓ τ (y, t + 2 * Real.pi)) x
      = deriv (fun y => L.ℓ τ (y, t)) x := by
    rw [show (fun y => L.ℓ τ (y, t + 2 * Real.pi))
          = (fun y => L.ℓ τ (y, t) + ((0, 2 * Real.pi), (0, 0))) from funext hper,
        deriv_add_const]
  -- the `t`-slice derivative is periodic (up to the constant translation).
  have hdt : deriv (fun s => L.ℓ τ (x, s)) (t + 2 * Real.pi)
      = deriv (fun s => L.ℓ τ (x, s)) t := by
    have h1 : deriv (fun s => L.ℓ τ (x, s + 2 * Real.pi)) t
        = deriv (fun s => L.ℓ τ (x, s)) t := by
      rw [show (fun s => L.ℓ τ (x, s + 2 * Real.pi))
            = (fun s => L.ℓ τ (x, s) + ((0, 2 * Real.pi), (0, 0))) from
              funext (fun s => by rw [L.per τ x s, hTk]),
          deriv_add_const]
    have h2 : deriv (fun s => L.ℓ τ (x, s + 2 * Real.pi)) t
        = deriv (fun s => L.ℓ τ (x, s)) (t + 2 * Real.pi) := by
      have := deriv_comp_add_const (fun s : ℝ => L.ℓ τ (x, s)) (2 * Real.pi) t
      simpa using this
    exact h2.symm.trans h1
  unfold theta
  rw [hdx, hdt, hper x, hTk]
  abel

end Work.RPA3
