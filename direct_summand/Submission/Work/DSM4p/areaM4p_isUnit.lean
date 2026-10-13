import Mathlib
import Submission.Work.DSM4p.Plan
import Submission.Work.DSM4p.Basic

set_option linter.unusedVariables false

namespace Work.DSM4p

universe a

/-!
# `area_M4p` when `p` is a unit

If `(p : B)` is a unit, then the ideal it generates is the whole ring, so the `Ideal.span {p}`
topology on `B` is the indiscrete one.  Since `B` carries a `PerfectoidData` structure, it is
in particular complete for that topology, i.e. Hausdorff, which forces `B` to be a subsingleton.
In a subsingleton every candidate tower works: the stationary tower `D n = B` with the identity
transitions is perfectoid, satisfies the `ϖ`-compatibility by reflexivity, admits a solution of
`g · y = p ^ n` vacuously, and satisfies `IsQRETp` by `isQRETp_self`.
-/

/-- If `x` is a unit then the principal ideal it generates is the whole ring. -/
theorem span_singleton_eq_top_of_isUnit {R : Type a} [CommRing R] {x : R} (hx : IsUnit x) :
    Ideal.span ({x} : Set R) = ⊤ :=
  Ideal.span_singleton_eq_top.mpr hx

/-- A ring which is `⊤`-adically complete is a subsingleton. -/
theorem subsingleton_of_isAdicComplete_top (R : Type a) [CommRing R]
    [IsAdicComplete (⊤ : Ideal R) R] : Subsingleton R :=
  (IsAdicComplete.toIsHausdorff (I := (⊤ : Ideal R)) (M := R)).subsingleton

theorem areaM4p_isUnit {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    (Q : DSMap.PerfectoidData p B) (gr : ℕ → B) (hgr : Work.DSM4p.IsRootSystem p gr)
    (hunit : IsUnit (p : B)) : Work.DSM4p.AreaM4p p B Q gr := by
  have htop : Ideal.span ({(p : B)} : Set B) = ⊤ := span_singleton_eq_top_of_isUnit hunit
  have hH : IsHausdorff (⊤ : Ideal B) B := htop ▸ Q.complete.toIsHausdorff
  have hsub : Subsingleton B := hH.subsingleton
  refine ⟨fun _ => B, fun _ => ‹CommRing B›, fun _ => Algebra.id B, fun _ => Q,
    fun _ => AlgHom.id B B, ?_, ?_, ?_⟩
  · intro n k
    exact hsub.allEq _ _
  · intro n
    exact ⟨0, hsub.allEq _ _⟩
  · exact isQRETp_self p B Q.ϖ gr

end Work.DSM4p
