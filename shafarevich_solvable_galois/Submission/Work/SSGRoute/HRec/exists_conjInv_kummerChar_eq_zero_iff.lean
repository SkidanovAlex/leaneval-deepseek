import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.HRec.exists_involution_conj_comp
import Submission.Work.SSGRoute.HRec.kummerChar_eq_zero_iff_not_isNegAt
import Submission.Work.SSGRoute.HRec.ne_one_of_star_comp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The reverse Artin–Schreier dictionary: real places come from involutions

For every real infinite place `w` of `k` there is a nontrivial involution `c` of `G_k = Ω ≃ₐ[k] Ω`
(the complex conjugation at `w`) whose Kummer character on `kˣ` is the negativity predicate at `w`:
`kummerChar a c = 0 ↔ ¬ IsNegAt w a`.

This is the reverse of `ZDataTwo.exists_realPlace_of_involution`; together with
`HRec.realPlace_eq_of_isNegAt_iff` it makes the correspondence between conjugacy classes of
involutions and real places a bijection, which is what clause 2 of
`Work.SSGRoute.HRec.cupKummer_archMatchK` (injectivity of `vOf`) needs.
-/

open NumberField

noncomputable section

namespace Work.SSGRoute.HRec

theorem exists_conjInv_kummerChar_eq_zero_iff {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (w : NumberField.InfinitePlace k) (hw : w.IsReal) :
    ∃ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 ∧ c ≠ 1 ∧
      ∀ a : kˣ, Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c = 0 ↔
        ¬ Work.SSGRoute.ZDataTwo.IsNegAt w a := by
  obtain ⟨Ψ, c, hΨ, hc2, hc⟩ := exists_involution_conj_comp (Ω := Ω) w hw
  refine ⟨c, hc2, ne_one_of_star_comp hc, ?_⟩
  intro a
  exact kummerChar_eq_zero_iff_not_isNegAt ζ hζ w hw hc2 hΨ hc a

end Work.SSGRoute.HRec
