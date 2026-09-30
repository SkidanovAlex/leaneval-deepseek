import Mathlib
import Submission.Work.SymQuot.DivOf.AffineCurve
import Submission.Work.SymQuot.DivOf.placeIdeal_isMaximal
import Submission.Work.SymQuot.DivOf.isDedekindDomain_sections
import Submission.Work.SymQuot.DivOf.heightOneSpectrum_equiv_place
import Submission.Work.SpecLin.Core.ord_germ_eq_iff_mem_pow

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

namespace Work.SymQuot.DivOf

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

theorem exists_mem_placeIdeal_notMem_sq {F : Type u} [Field F] {C : Work.CurveBasics.Curve F}
    (W : C.left.Opens) (hW : IsAffineOpen W) (z : C.Place) (hz : z.point ∈ W) :
    ∃ a : C.left.presheaf.obj (Opposite.op W),
      a ∈ Work.SymQuot.DivOf.placeIdeal C W z hz ∧
        a ∉ (Work.SymQuot.DivOf.placeIdeal C W z hz) ^ 2 := by
  haveI : Nonempty W := ⟨⟨z.point, hz⟩⟩
  haveI : IsDedekindDomain ↥(C.left.presheaf.obj (Opposite.op W)) :=
    isDedekindDomain_sections hW
  -- The maximal ideal `𝔪_z` of `z` in `Γ(C,W)` is nonzero: `z` is a closed point, so the prime
  -- of `Spec Γ(C,W)` it defines is not the zero ideal.
  have hp0 : Work.SymQuot.DivOf.placeIdeal C W z hz ≠ ⊥ := by
    rw [placeIdeal_eq_primeIdealOf hW z hz]
    exact heightOne_primeIdealOf_asIdeal_ne_bot_of_place hW z hz
  -- and it is proper, being maximal.
  have hp1 : Work.SymQuot.DivOf.placeIdeal C W z hz ≠ ⊤ :=
    (placeIdeal_isMaximal hW z hz).ne_top
  -- In a Dedekind domain a nonzero proper ideal is strictly bigger than its square.
  obtain ⟨a, ha, ha2⟩ :=
    Ideal.exists_mem_pow_notMem_pow_succ
      (Work.SymQuot.DivOf.placeIdeal C W z hz) hp0 hp1 1
  exact ⟨a, by simpa using ha, by simpa using ha2⟩

end Work.SymQuot.DivOf
