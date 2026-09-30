import Mathlib
import Submission.Work.RiemannRoch.Differentials
import Submission.Work.RiemannRoch.RRLib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

universe u

namespace Work.RiemannRoch.Duality

open scoped Classical

/-- **There is a nonzero Weil differential.**  The space `Ω` of Weil differentials is the
union of the dual annihilators `WD D = (A(D) + K)ᗮ`; by Serre duality `dim WD D = i D`, and
Riemann–Roch gives `i D ≥ g - 1 - deg D`, which is positive as soon as `deg D ≤ g - 2`.
Such a divisor exists: a negative multiple of a single place. -/
theorem exists_ne_zero_mem_Omega {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) :
    ∃ ω ∈ Work.RiemannRoch.Curve.Omega C, ω ≠ 0 := by
  classical
  obtain ⟨Q⟩ := Work.RiemannRoch.Curve.nonempty_place C
  set D : C.Div :=
    Work.CurveBasics.Curve.Div.single Q (-((Work.RiemannRoch.Curve.genus C : ℤ) + 2)) with hD
  -- The divisor `D` has degree at most `g - 2`.
  have hdeg : C.deg D ≤ (Work.RiemannRoch.Curve.genus C : ℤ) - 2 := by
    have hd : C.deg D
        = -((Work.RiemannRoch.Curve.genus C : ℤ) + 2) * (Q.degree : ℤ) := by
      rw [hD, Work.CurveBasics.Curve.deg_single]
    have hg0 : (0 : ℤ) ≤ (Work.RiemannRoch.Curve.genus C : ℤ) := Int.natCast_nonneg _
    have hpos : (1 : ℤ) ≤ (Q.degree : ℤ) := by
      have h : 0 < Q.degree := Work.CurveBasics.Place.residueDegree_pos Q
      have h1 : 1 ≤ Q.degree := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
      exact_mod_cast h1
    have hle : -((Work.RiemannRoch.Curve.genus C : ℤ) + 2) ≤ 0 := by linarith
    have hmul : -((Work.RiemannRoch.Curve.genus C : ℤ) + 2) * (Q.degree : ℤ)
        ≤ -((Work.RiemannRoch.Curve.genus C : ℤ) + 2) * 1 :=
      mul_le_mul_of_nonpos_left hpos hle
    rw [hd]
    linarith
  -- Hence `i D ≥ 1`.
  have hi : 1 ≤ Work.RiemannRoch.Curve.i C D := by
    have hrr := Work.RiemannRoch.Curve.riemannRoch C D
    have hl : (0 : ℤ) ≤ (C.l D : ℤ) := Int.natCast_nonneg _
    have h1 : (1 : ℤ) ≤ (Work.RiemannRoch.Curve.i C D : ℤ) := by linarith
    exact_mod_cast h1
  -- So `H1 C D` is nontrivial, i.e. `A(D) + K ≠ ⊤`.
  have hne : Work.RiemannRoch.Curve.WD C D ≠ ⊥ := by
    intro hbot
    -- `WD C D = (A(D) + K)ᗮ` is the dual of `H1 C D`.
    have hdual : Subsingleton (Module.Dual k (Work.RiemannRoch.Curve.H1 C D)) :=
      Submodule.dualAnnihilator_eq_bot_iff'.mp hbot
    haveI hsub : Subsingleton (Work.RiemannRoch.Curve.H1 C D) :=
      (Module.subsingleton_dual_iff k).mp hdual
    have hi0 : Work.RiemannRoch.Curve.i C D = 0 := by
      rw [Work.RiemannRoch.Curve.i]
      exact finrank_zero_iff_forall_zero.mpr (fun x => Subsingleton.elim x 0)
    omega
  obtain ⟨ω, hω, hωne⟩ :=
    (Submodule.ne_bot_iff (Work.RiemannRoch.Curve.WD C D)).mp hne
  exact ⟨ω, Work.RiemannRoch.Curve.le_Omega C D hω, hωne⟩

end Work.RiemannRoch.Duality
