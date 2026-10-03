import Mathlib
import Submission.Work.Analysis.Paraproduct.CrtFactor

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Analysis.Paraproduct

/-! ## Transport of the `L^p` norm along the Chinese-remainder isomorphism

The Chinese-remainder isomorphism `ZMod (m * n) ≃+* ZMod m × ZMod n` is measure-preserving
between the two Haar probability spaces, so the normalised `L^p` norm is invariant under
transport along it.  This is the continuity step of the `crt` factorisation of Section 10 of
Krause--Mirek--Tao: norms computed on `ZMod m × ZMod n` (the tensor-product side, `ttensor-bil`)
coincide with norms computed on `ZMod (m * n)` (`LpNormZMod`). -/

/-- The transport of `LpNormZMod` along the inverse Chinese-remainder isomorphism:
pulling a function `F : ZMod (m * n) → ℂ` back to `ZMod m × ZMod n` and computing the
normalised `L^p` norm there (via `lpNormFin`) gives the norm of `F` on `ZMod (m * n)`. -/
theorem LpNormZMod_crtTransport {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (p : ℝ) (F : ZMod (m * n) → ℂ) :
    lpNormFin (ZMod m × ZMod n) p (fun z => F ((ZMod.chineseRemainder h).symm z))
      = Work.Analysis.Concentration.LpNormZMod (m * n) p F := by
  -- Both norms are `(card⁻¹ * ∑ ‖·‖ ^ p) ^ (1/p)`.
  simp only [lpNormFin, Work.Analysis.Concentration.LpNormZMod]
  -- The Haar probability measures agree: `#(ZMod m × ZMod n) = m * n`.
  have hcard : Fintype.card (ZMod m × ZMod n) = m * n := by
    rw [Fintype.card_prod, ZMod.card m, ZMod.card n]
  -- The inverse CRT map is a bijection, so it transports the sum.
  have hsum : ∑ z : ZMod m × ZMod n, ‖F ((ZMod.chineseRemainder h).symm z)‖ ^ p
      = ∑ x : ZMod (m * n), ‖F x‖ ^ p :=
    Equiv.sum_comp ((ZMod.chineseRemainder h).symm : ZMod m × ZMod n ≃ ZMod (m * n))
      (fun x : ZMod (m * n) => ‖F x‖ ^ p)
  rw [hcard, hsum]

end Work.Analysis.Paraproduct
