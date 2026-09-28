import Mathlib
import Submission.Work.HP.ConicsDefs
import Submission.Work.HP.ConicsLiftDefs
import Submission.Work.HP.ConicFail.red_unit

/-!
# Bad conics mod `p²` have no primitive zero

This file proves `Work.HP.conics_fail`: a ternary quadratic form over `ℤ` whose reduction
modulo `p` (for `p` an odd prime) is "sharp" on some line `⟨v⟩` — the reduction has `v` in the
radical of its polar form and its zero set is exactly that line — and which does not vanish on
the lifts of `v`, has no primitive zero modulo `p²`.

The argument is in two steps.

* Over `ZMod (p^2)`: if `A` satisfies `BadForm p A` and `x` has a coordinate whose reduction
  modulo `p` is nonzero, then `qf A x ≠ 0` (`ConicFailAux.qf_ne_zero_of_badForm`).  Reducing
  `qf A x = 0` mod `p` shows the reduction of `x` lies on the sharp conic, hence is `t • v`
  with `t ≠ 0`; choosing a lift `T` of `t` and the witness lift `v'` of `v`, one writes
  `x = T • v' + p • z` and the expansion
  `qf A (T • v' + p • z) = T² qf A v'` (`ConicFailAux.qf_lift_expansion`, whose cross term dies
  because `v` is in the radical) shows `qf A x = T² qf A v'`; `T` is a unit and `qf A v' ≠ 0`.
* Transfer: an integer vector with a coordinate prime to `p` maps to a vector of `ZMod (p²)`
  with nonzero reduction, and `qf (fun m => (a m : ZMod (p²))) x̃ = 0` whenever
  `(p : ℤ)² ∣ formEval 2 2 a x` (`ConicFailAux.formEval_intCast`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Work.HP

namespace Work.HP

namespace ConicFailAux

open Conics

/-- `formEval` is natural in the coefficient ring: casting the integer vector `x` into
`ZMod (p^2)` and evaluating there is the same as evaluating over `ℤ` and then casting. -/
theorem formEval_intCast (p : ℕ) (a : Mon 2 2 → ℤ) (x : Fin 3 → ℤ) :
    formEval 2 2 a (fun i => (x i : ZMod (p ^ 2)))
      = ((formEval 2 2 a x : ℤ) : ZMod (p ^ 2)) := by
  simp only [formEval, veronese]
  push_cast
  rfl

/-- An element of `ZMod (p^2)` whose reduction modulo `p` vanishes is annihilated by `p`. -/
theorem red_zero_mul (p : ℕ) [Fact p.Prime] (y : ZMod (p ^ 2)) (h : Conics.red p y = 0) :
    (p : ZMod (p ^ 2)) * y = 0 := by
  rw [Conics.p_mul_eq_p_mul_lif_red p y, h]
  simp [Conics.lif]

/-- **Expansion along the sharp line.**  If `v'` is a lift of `v`, the reduction of `A` has `v`
in the radical of its polar form, and `T` is arbitrary, then

`qf A (T • v' + p • z) = T² · qf A v'`.

Indeed `qf A (T•v' + p•z) = T² qf A v' + p·T·pol A v' z + p² qf A z`; the last term vanishes
because `p² = 0` in `ZMod (p^2)`, and the middle one because `red p (pol A v' z) =
pol (redC p A) v (red ∘ z) = 0` puts `pol A v' z` in the kernel of the reduction. -/
theorem qf_lift_expansion (p : ℕ) [Fact p.Prime] (A : Mon 2 2 → ZMod (p ^ 2))
    (v : Fin 3 → ZMod p) (v' z : Fin 3 → ZMod (p ^ 2))
    (hvlift : Conics.IsLift p v' v)
    (hrad : ∀ y, Conics.pol (Conics.redC p A) v y = 0)
    (T : ZMod (p ^ 2)) :
    Conics.qf A (T • v' + (p : ZMod (p ^ 2)) • z) = T ^ 2 * Conics.qf A v' := by
  rw [Conics.qf_add_smul, Conics.qf_smul, Conics.pol_smul_left]
  have hredpol : Conics.red p (Conics.pol A v' z) = 0 := by
    rw [Conics.red_pol]
    have hv : (fun i => Conics.red p (v' i)) = v := funext hvlift
    rw [hv]
    exact hrad _
  have hpol : (p : ZMod (p ^ 2)) * Conics.pol A v' z = 0 := red_zero_mul p _ hredpol
  have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self (p ^ 2)
  have h1 : (p : ZMod (p ^ 2)) * (T * Conics.pol A v' z) = 0 := by
    rw [← mul_assoc, mul_comm (p : ZMod (p ^ 2)) T, mul_assoc, hpol, mul_zero]
  have h2 : (p : ZMod (p ^ 2)) ^ 2 * Conics.qf A z = 0 := by rw [hp2, zero_mul]
  rw [h1, h2, add_zero, add_zero]

/-- **Main auxiliary statement over `ZMod (p^2)`.**  If the reduction of `A` is sharp on the
line `⟨v⟩` and the lifted form does not vanish on the lifts of `v`, then `qf A` has no zero
whose reduction modulo `p` is nonzero. -/
theorem qf_ne_zero_of_badForm (p : ℕ) [Fact p.Prime] (A : Mon 2 2 → ZMod (p ^ 2))
    (hbad : Conics.BadForm p A) (x : Fin 3 → ZMod (p ^ 2))
    (hx : ∃ i, Conics.red p (x i) ≠ 0) : Conics.qf A x ≠ 0 := by
  obtain ⟨v, hv, hII⟩ := hbad
  obtain ⟨hv_ne, hv_rad, hv_zero⟩ := hv
  obtain ⟨v', hvlift, hv'ne⟩ := hII
  intro hqx
  -- the reduction of `x` is nonzero
  have hxbar_ne : (fun i => Conics.red p (x i)) ≠ 0 := by
    rintro h
    obtain ⟨i, hi⟩ := hx
    exact hi (congrFun h i)
  -- reducing `qf A x = 0` modulo `p` puts the reduction of `x` on the sharp conic
  have hredqf : Conics.qf (Conics.redC p A) (fun i => Conics.red p (x i)) = 0 := by
    have h := Conics.red_qf p A x
    rw [hqx, map_zero] at h
    exact h.symm
  obtain ⟨t, ht⟩ := hv_zero _ hredqf
  -- ... so it is a nonzero multiple of `v`
  have ht_ne : t ≠ 0 := by
    rintro rfl
    refine hxbar_ne ?_
    rw [ht]
    simp
  have hti : ∀ i, Conics.red p (x i) = t * v i := fun i => by
    simpa [Pi.smul_apply] using congrFun ht i
  -- a lift `T` of `t` is a unit
  set T : ZMod (p ^ 2) := Conics.lif p t with hTdef
  have hT : Conics.red p T = t := Conics.red_lif p t
  have hTunit : IsUnit T := ConicFail.red_unit p T (by rw [hT]; exact ht_ne)
  -- `x - T • v'` has zero reduction, hence is `p • z`
  have hdiff : ∀ i, Conics.red p (x i - (T • v') i) = 0 := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, map_sub, map_mul, hT, hvlift i, hti i, sub_self]
  choose z hz using fun i =>
    (Conics.red_eq_zero_iff_exists_lif p (x i - (T • v') i)).mp (hdiff i)
  have hzsum : (p : ZMod (p ^ 2)) • (fun i => Conics.lif p (z i)) = x - T • v' := by
    funext i
    simp only [Pi.smul_apply, Pi.sub_apply]
    exact (hz i).symm
  have hdecomp : x = T • v' + (p : ZMod (p ^ 2)) • (fun i => Conics.lif p (z i)) := by
    rw [hzsum]
    abel
  -- evaluate
  have hqfx : Conics.qf A x = T ^ 2 * Conics.qf A v' := by
    conv_lhs => rw [hdecomp]
    exact qf_lift_expansion p A v v' (fun i => Conics.lif p (z i)) hvlift hv_rad T
  rw [hqfx] at hqx
  exact hv'ne ((hTunit.pow 2).mul_right_eq_zero.mp hqx)

end ConicFailAux

/-- `Work.HP.Conics.BadForm p A` (see `Submission/Work/HP/ConicsDefs.lean`) says: there is
`v ≠ 0` such that the reduction `redC p A` is `SharpAt v` (i.e. `v` is in the radical of its
polar form and its zero set is the line `⟨v⟩`) and `II p A v` holds (the lifted form does not
vanish on the lifts of `v`).  Then `A` has no primitive zero mod `p^2`: this is
`Work.HP.PrimModZero 2 2 a p 2` for `A = fun m => (a m : ZMod (p^2))`.

Suggested route.  First show the auxiliary statement over `ZMod (p^2)`: if `BadForm p A` and
`x : Fin 3 → ZMod (p^2)` satisfies `∃ i, red p (x i) ≠ 0`, then `qf A x ≠ 0`.  Reduce
`qf A x = 0` mod `p` using `Work.HP.Conics.red_qf`: `qf (redC p A) x̄ = 0` with `x̄ ≠ 0`, so by
sharpness `x̄ = t • v` with `t ≠ 0`; pick `T` with `red T = t` and the witness lift `v'` of `v`
with `qf A v' ≠ 0` (from `II`); then `x = T • v' + p • z`, and `qf_add_smul`/`qf_smul` give
`qf A x = T^2 qf A v' + T p pol A v' z`; `red (pol A v' z) = pol (redC p A) v (red z) = 0` by
the radical condition, so the second term vanishes in `ZMod (p^2)`; `T` is a unit and
`qf A v' ≠ 0`, so `qf A x ≠ 0`.
Then transfer: given `x : Fin 3 → ℤ` with `¬ p ∣ x i` and
`(p:ℤ)^2 ∣ formEval 2 2 a x`, its image `x̃ i = (x i : ZMod (p^2))` has `red (x̃ i) ≠ 0`
(`ZMod.intCast_zmod_eq_zero_iff_dvd`) and `qf (fun m => (a m : ZMod (p^2))) x̃ = 0`
(`Work.HP.Conics.qf_formEval`), contradiction. -/
theorem conics_fail (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a : Mon 2 2 → ℤ)
    (hbad : Work.HP.Conics.BadForm p (fun m => (a m : ZMod (p^2)))) :
    ¬ Work.HP.PrimModZero 2 2 a p 2 := by
  rintro ⟨x, hx, hdiv⟩
  -- the image of `x` in `ZMod (p^2)` still has a nonzero coordinate modulo `p`
  have hx' : ∃ i, Conics.red p ((x i : ZMod (p^2))) ≠ 0 := by
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, by
      rw [map_intCast, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hi⟩
  -- and it is a zero of the reduction of `a` modulo `p^2`
  have hqf0 : Conics.qf (fun m => (a m : ZMod (p^2))) (fun i => (x i : ZMod (p^2))) = 0 := by
    rw [Conics.qf_formEval, ConicFailAux.formEval_intCast]
    obtain ⟨k, hk⟩ := hdiv
    rw [hk]
    have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
      rw [← Nat.cast_pow]; exact ZMod.natCast_self (p ^ 2)
    push_cast
    rw [hp2, zero_mul]
  exact (ConicFailAux.qf_ne_zero_of_badForm p (fun m => (a m : ZMod (p^2))) hbad
    (fun i => (x i : ZMod (p^2))) hx') hqf0

end Work.HP
