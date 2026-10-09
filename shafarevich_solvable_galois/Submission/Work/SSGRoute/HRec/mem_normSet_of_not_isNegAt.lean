import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.ArchDefs
import Submission.Work.SSGRoute.HRec.exists_sq_eq_of_ne_zero
import Submission.Work.SSGRoute.HRec.star_eq_self_of_mul_self_eq_ofReal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `⟸` branch of the reverse Artin–Schreier characterisation

If `a : kˣ` is **not** negative at the real place `w`, then `a` is a norm (`m * c m`) for the
involution `c` attached to `w` (`HRec.exists_involution_conj_comp`).

Chain: `¬ IsNegAt w a` gives `0 < φ a` (`ArchDefs.not_isNegAt_iff`); pick `x` with
`x * x = a` (`HRec.exists_sq_eq_of_ne_zero`); `Ψ x * Ψ x = ((φ a : ℝ) : ℂ)` is then a positive real,
so `star (Ψ x) = Ψ x` (`HRec.star_eq_self_of_mul_self_eq_ofReal`); `Ψ (c x) = star (Ψ x)` (the
involution's defining property) therefore gives `c x = x` by injectivity of `Ψ`; and finally
`x * c x = x * x = a`.  No choice of square root is needed: *every* root of `a` behaves this way.

`normSet` is `{y | ∃ x, x ≠ 0 ∧ y = x * c x}`, hence the witness shape at the end.
-/

open NumberField

noncomputable section

namespace Work.SSGRoute.HRec

theorem mem_normSet_of_not_isNegAt {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω] (w : NumberField.InfinitePlace k) (hw : w.IsReal)
    {Ψ : Ω →+* ℂ} {c : Ω ≃ₐ[k] Ω}
    (hΨ : ∀ a : k, Ψ (algebraMap k Ω a) =
      (((NumberField.InfinitePlace.embedding_of_isReal hw) a : ℝ) : ℂ))
    (hc : ∀ x : Ω, Ψ (c x) = starRingEnd ℂ (Ψ x))
    (a : kˣ) (ha : ¬ Work.SSGRoute.ZDataTwo.IsNegAt w a) :
    (algebraMap k Ω (a : k)) ∈ Work.SSGRoute.TwoTorsion.normSet c.toRingEquiv := by
  have hpos : 0 < (NumberField.InfinitePlace.embedding_of_isReal hw) (a : k) :=
    (Work.SSGRoute.ZDataTwo.not_isNegAt_iff hw a).mp ha
  have ha0 : algebraMap k Ω (a : k) ≠ 0 := by
    intro h0
    exact a.ne_zero ((algebraMap k Ω).injective (by rw [h0, map_zero]))
  obtain ⟨x, hx⟩ := exists_sq_eq_of_ne_zero ha0
  have hval : Ψ x * Ψ x =
      (((NumberField.InfinitePlace.embedding_of_isReal hw) (a : k) : ℝ) : ℂ) := by
    rw [← map_mul, hx, hΨ (a : k)]
  have hreal : starRingEnd ℂ (Ψ x) = Ψ x :=
    star_eq_self_of_mul_self_eq_ofReal hpos hval
  have hcx : c x = x := by
    apply RingHom.injective Ψ
    rw [hc x, hreal]
  refine ⟨x, ?_, ?_⟩
  · intro h0
    exact ha0 (by rw [← hx, h0, zero_mul])
  · show algebraMap k Ω (a : k) = x * c x
    rw [hcx, hx]

end Work.SSGRoute.HRec
