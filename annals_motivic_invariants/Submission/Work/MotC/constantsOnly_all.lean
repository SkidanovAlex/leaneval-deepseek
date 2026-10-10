import Mathlib
import ChallengeDeps
import Submission.Work.TorsorExistence.Defs
import Submission.Work.Genus.Main.constantsOnly_ratFunc
import Submission.Work.MotC.WireU.RatFuncCharPUniv
import Submission.Work.MotC.WireU.RatFuncCharTwoUniv

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotC

noncomputable section

/-- **One-variable Weierstrass rigidity, in every characteristic.**

Every solution of a non-singular Weierstrass equation over the rational function field `F(t)` has
constant coordinates, for an *arbitrary* field `F` — no hypothesis on the characteristic, on
perfectness, or on infinitude.

This is the union of the three cases that are established separately:

* `Work.Genus.Main.exists_algebraMap_of_weierstrass` (characteristic `0`);
* `Work.MotC.WireU.exists_algebraMap_of_weierstrass_ratFunc_charP` (characteristic `p ≠ 2`,
  arbitrary `F`, via the algebraic closure and the perfect-field theorem
  `Work.MotC.WireU.exists_algebraMap_of_weierstrass_charP`);
* `Work.MotC.WireU.exists_algebraMap_of_weierstrass_ratFunc_charTwo` (characteristic `2`, where the
  completion of the square degenerates and the divisor `dx / (a₁x + a₃)` takes over).

The last two are universe-polymorphic versions (in `Type*`) of the corresponding results of
`Work.Wire123`, which carried an explicit `Type` binder. -/
theorem exists_algebraMap_of_weierstrass_ratFunc_all {F : Type*} [Field F] (E : WeierstrassCurve F)
    (hΔ : E.Δ ≠ 0) {x y : RatFunc F}
    (h : y ^ 2 + algebraMap F (RatFunc F) E.a₁ * x * y + algebraMap F (RatFunc F) E.a₃ * y
      = x ^ 3 + algebraMap F (RatFunc F) E.a₂ * x ^ 2 + algebraMap F (RatFunc F) E.a₄ * x
        + algebraMap F (RatFunc F) E.a₆) :
    (∃ x₀ : F, x = algebraMap F (RatFunc F) x₀) ∧
      (∃ y₀ : F, y = algebraMap F (RatFunc F) y₀) := by
  rcases CharP.exists' F with h0 | ⟨p, ⟨hp⟩, hchar⟩
  · haveI : CharZero F := h0
    exact Work.Genus.Main.exists_algebraMap_of_weierstrass E hΔ h
  · rcases eq_or_ne p 2 with rfl | hp2
    · haveI : CharP F 2 := hchar
      exact Work.MotC.WireU.exists_algebraMap_of_weierstrass_ratFunc_charTwo E hΔ h
    · have h2 : (2 : F) ≠ 0 := by
        intro hz
        have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp hz
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
      haveI : Fact p.Prime := ⟨hp⟩
      exact Work.MotC.WireU.exists_algebraMap_of_weierstrass_ratFunc_charP (K := F) (p := p) h2 E hΔ h

/-- **`(E⁄F)(F(t)) = (E⁄F)(F)` for every `𝕜`-algebra `F`.**  Every point of the base change of a
non-singular Weierstrass curve `E/𝕜` to the rational function field `F(t)` is the base change of a
point of `E⁄F`.  This is the point-level form of `exists_algebraMap_of_weierstrass_ratFunc_all`,
stated relative to the base ring `𝕜` of `E` (so that it applies with `E := D.E/𝕜` and `F := M`). -/
theorem exists_baseChange_eq_of_point_ratFunc_all {𝕜 F : Type*} [Field 𝕜] [Field F] [Algebra 𝕜 F]
    [DecidableEq F] [DecidableEq (RatFunc F)] (E : WeierstrassCurve 𝕜)
    (hΔ : (E.baseChange F).Δ ≠ 0)
    (R : WeierstrassCurve.Affine.Point (E.baseChange (RatFunc F))) :
    ∃ Q : WeierstrassCurve.Affine.Point (E.baseChange F),
      WeierstrassCurve.Affine.Point.baseChange (W' := E) F (RatFunc F) Q = R := by
  classical
  rcases R with _ | ⟨x, y, hns⟩
  · exact ⟨0, WeierstrassCurve.Affine.Point.map_zero (W' := E) (f := Algebra.ofId F (RatFunc F))⟩
  · have heq : y ^ 2 + algebraMap F (RatFunc F) (E.baseChange F).a₁ * x * y
          + algebraMap F (RatFunc F) (E.baseChange F).a₃ * y
        = x ^ 3 + algebraMap F (RatFunc F) (E.baseChange F).a₂ * x ^ 2
          + algebraMap F (RatFunc F) (E.baseChange F).a₄ * x
          + algebraMap F (RatFunc F) (E.baseChange F).a₆ := by
      have h1 := (WeierstrassCurve.Affine.equation_iff (W := E.baseChange (RatFunc F)) x y).mp
        hns.1
      simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
        WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
        ← IsScalarTower.algebraMap_apply 𝕜 F (RatFunc F)] using h1
    obtain ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩ :=
      exists_algebraMap_of_weierstrass_ratFunc_all (E.baseChange F) hΔ heq
    have hns' : WeierstrassCurve.Affine.Nonsingular (E.baseChange (RatFunc F))
        (algebraMap F (RatFunc F) x₀) (algebraMap F (RatFunc F) y₀) := by
      rw [← hx₀, ← hy₀]; exact hns
    have hq : WeierstrassCurve.Affine.Nonsingular (E.baseChange F) x₀ y₀ :=
      (WeierstrassCurve.Affine.baseChange_nonsingular E (f := Algebra.ofId F (RatFunc F))
        (Algebra.ofId F (RatFunc F)).injective x₀ y₀).mp hns'
    refine ⟨WeierstrassCurve.Affine.Point.some x₀ y₀ hq, ?_⟩
    refine (WeierstrassCurve.Affine.Point.map_some (W' := E) (f := Algebra.ofId F (RatFunc F))
      (x := x₀) (y := y₀) hq).trans ?_
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨by rw [Algebra.ofId_apply, hx₀], by rw [Algebra.ofId_apply, hy₀]⟩

theorem constantsOnly_all {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.FiveTorsionCurve 𝕜)
    (M : Type*) [Field M] [DecidableEq M] [Algebra 𝕜 M] [DecidableEq (RatFunc M)]
    (R : WeierstrassCurve.Affine.Point (D.E.baseChange (RatFunc M))) :
    ∃ Q : WeierstrassCurve.Affine.Point (D.E.baseChange M),
      WeierstrassCurve.Affine.Point.baseChange M (RatFunc M) Q = R := by
  have hΔ : (D.E.baseChange M).Δ ≠ 0 := by
    have h2 : (D.E.baseChange M).Δ = algebraMap 𝕜 M D.E.Δ := by
      simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    rw [h2]
    exact fun h => (isUnit_iff_ne_zero.mp (WeierstrassCurve.isUnit_Δ D.E))
      ((algebraMap 𝕜 M).injective (by rw [h, map_zero]))
  exact exists_baseChange_eq_of_point_ratFunc_all (E := D.E) hΔ R

end

end Work.MotC
