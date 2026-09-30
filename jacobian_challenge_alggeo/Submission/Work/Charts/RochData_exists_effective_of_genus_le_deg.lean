import Mathlib
import Submission.Work.Charts.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.Charts

universe u

/- RR7, in the form consumed by area `CH`.  A divisor `D` on `C_F` whose degree is at least the
genus `g` of `C` is linearly equivalent to an *effective* divisor: since `1 ≤ ℓ(D)`
(`RochData.ell_pos_of_genus_le_deg`), the Riemann-Roch space `L(D)` is nonzero, and a nonzero
`f ∈ L(D)` has `div f + D` effective, with `D - (div f + D) = div f⁻¹`. -/
open CategoryTheory in
theorem RochData_exists_effective_of_genus_le_deg {K : Type u} [Field K]
    {C : Work.CurveBasics.Curve K} [Work.SpecLin.DivBase C] (R : Work.Charts.RochData C)
    {F : Type u} [Field F] [Algebra K F] (D : Work.GCBasics.Dv C F)
    (h : (R.g : ℤ) ≤ Work.GCBasics.Ddeg C F D) :
    ∃ D' : Work.GCBasics.Dv C F,
      D'.IsEffective ∧ Work.GCBasics.LinEquiv C D D' := by
  have h1 : 1 ≤ Work.GCBasics.ell C D := R.ell_pos_of_genus_le_deg D h
  have hne : (Work.CurveBasics.Curve.baseChange C F).L D ≠ ⊥ := by
    intro hb
    rw [Work.GCBasics.ell, hb, finrank_bot] at h1
    omega
  obtain ⟨f, hfm, hfne⟩ := Submodule.ne_bot_iff _ |>.mp hne
  rw [Work.CurveBasics.Curve.mem_L_iff] at hfm
  rcases hfm with h0 | heff
  · exact absurd h0 hfne
  · refine ⟨(Work.CurveBasics.Curve.baseChange C F).div f + D, heff, ?_⟩
    refine ⟨f⁻¹, inv_ne_zero hfne, ?_⟩
    rw [Work.CurveBasics.Order.div_inv _ hfne]
    abel

end Work.Charts
