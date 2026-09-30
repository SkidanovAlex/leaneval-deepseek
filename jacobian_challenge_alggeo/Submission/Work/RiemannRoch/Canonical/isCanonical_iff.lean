import Mathlib
import Submission.Work.RiemannRoch.Canonical
import Submission.Work.RiemannRoch.Canonical.Properties
import Submission.Work.RiemannRoch.Duality.Basic
import Submission.Work.RiemannRoch.Duality.finrank_WD
import Submission.Work.RiemannRoch.Duality.sum_l_le_finrank_WD
import Submission.Work.RiemannRoch.RR.smulW_mem_WD
import Submission.Work.RiemannRoch.RR.smulW_eq_zero_iff
import Submission.Work.RiemannRoch.RRLib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

namespace Work.RiemannRoch.Canonical

/-
# Canonical divisors are exactly the divisors of degree `2g - 2` with `l = g`

A divisor `W` is canonical when `i D = l (W - D)` for all `D`
(`Work.RiemannRoch.Curve.IsCanonical`).  Here we prove the numerical characterisation

  `IsCanonical C W ↔ deg W = 2 * g - 2 ∧ l W = g`,

where `g = genus C`.  The forward implication is `IsCanonical.deg` / `IsCanonical.l_eq`.

For the converse, the point is that `i W = 1` (Riemann–Roch), so `WD C W` is a nonzero
`k`-vector space: pick `0 ≠ ω ∈ WD C W`.  For every divisor `D` the map
`L (W - D) → WD D`, `f ↦ f ω` is injective (multiplication by a nonzero function is
injective on differentials), so `l (W - D) ≤ i D`; applying this with `D` replaced by
`W - D` gives `l D ≤ i (W - D)`.  Two applications of Riemann–Roch squeeze these into an
equality `l (W - D) = i D`, i.e. `W` is canonical.  No duality theorem is needed.
-/

theorem isCanonical_iff {k : Type*} [Field k] (C : Work.CurveBasics.Curve k) (W : C.Div) :
    Work.RiemannRoch.Curve.IsCanonical C W ↔
      C.deg W = 2 * (Work.RiemannRoch.Curve.genus C : ℤ) - 2
        ∧ C.l W = Work.RiemannRoch.Curve.genus C := by
  constructor
  · intro hW
    exact ⟨hW.deg, hW.l_eq⟩
  · rintro ⟨hdeg, hl⟩
    -- Riemann–Roch for `W` gives `i W = 1`.
    have hiW : Work.RiemannRoch.Curve.i C W = 1 := by
      have hRR := Work.RiemannRoch.Curve.riemannRoch C W
      rw [hl, hdeg] at hRR
      have h1 : (Work.RiemannRoch.Curve.i C W : ℤ) = 1 := by linarith
      exact_mod_cast h1
    -- Hence `WD C W` is a nonzero `k`-vector space.
    have hne : Work.RiemannRoch.Curve.WD C W ≠ ⊥ := by
      intro hbot
      have h0 : Module.finrank k ↥(Work.RiemannRoch.Curve.WD C W) = 0 := by
        rw [hbot]
        exact finrank_bot k _
      rw [Work.RiemannRoch.Duality.finrank_WD C W, hiW] at h0
      exact one_ne_zero h0
    obtain ⟨ω, hω, hω0⟩ := (Submodule.ne_bot_iff _).mp hne
    -- The elementary embedding `L (W - D) ↪ WD D`, `f ↦ f ω`.
    have hle : ∀ D : C.Div, C.l (W - D) ≤ Work.RiemannRoch.Curve.i C D := by
      intro D
      haveI : Module.Finite k ↥(Work.RiemannRoch.Curve.WD C D) := by
        haveI : Module.Finite k (Module.Dual k (Work.RiemannRoch.Curve.H1 C D)) :=
          inferInstance
        exact Module.Finite.equiv (Work.RiemannRoch.Curve.WDequiv C D)
      have hmaps : ∀ f : ↥(C.L (W - D)),
          ((Work.RiemannRoch.Curve.smulWLin C ω).comp (C.L (W - D)).subtype) f
            ∈ Work.RiemannRoch.Curve.WD C D := by
        intro f
        rw [LinearMap.comp_apply, Submodule.subtype_apply,
          Work.RiemannRoch.Curve.smulWLin_apply]
        exact Work.RiemannRoch.Duality.smulW_mem_WD_of_mem_L C (D := W) (E := D) f.2 hω
      let Φ : ↥(C.L (W - D)) →ₗ[k] ↥(Work.RiemannRoch.Curve.WD C D) :=
        LinearMap.codRestrict (Work.RiemannRoch.Curve.WD C D)
          ((Work.RiemannRoch.Curve.smulWLin C ω).comp (C.L (W - D)).subtype) hmaps
      have hΦ : ∀ f : ↥(C.L (W - D)),
          ((Φ f : ↥(Work.RiemannRoch.Curve.WD C D))
              : Work.RiemannRoch.Curve.WeilDifferential C)
            = Work.RiemannRoch.Curve.smulW C (f : C.functionField) ω := fun f => rfl
      have hinj : Function.Injective Φ := by
        intro f g hfg
        have hfg' : Work.RiemannRoch.Curve.smulW C (f : C.functionField) ω
            = Work.RiemannRoch.Curve.smulW C (g : C.functionField) ω := by
          rw [← hΦ f, ← hΦ g, hfg]
        by_cases h0 : (f : C.functionField) - (g : C.functionField) = 0
        · exact Subtype.ext (sub_eq_zero.mp h0)
        · have hdiff : Work.RiemannRoch.Curve.smulW C
              ((f : C.functionField) - (g : C.functionField)) ω = 0 := by
            rw [← Work.RiemannRoch.Curve.smulWLin_apply, map_sub,
              Work.RiemannRoch.Curve.smulWLin_apply, Work.RiemannRoch.Curve.smulWLin_apply,
              hfg', sub_self]
          exact absurd ((Work.RiemannRoch.RR.smulW_eq_zero_iff C h0 ω).mp hdiff) hω0
      have hfin := LinearMap.finrank_le_finrank_of_injective hinj
      rw [Work.RiemannRoch.Duality.finrank_WD C D] at hfin
      exact hfin
    -- Squeeze with Riemann–Roch.
    intro D
    have hRRd := Work.RiemannRoch.Curve.riemannRoch C D
    have hRRw := Work.RiemannRoch.Curve.riemannRoch C (W - D)
    have hA : (C.l (W - D) : ℤ) ≤ (Work.RiemannRoch.Curve.i C D : ℤ) := by
      exact_mod_cast hle D
    have hB : (C.l D : ℤ) ≤ (Work.RiemannRoch.Curve.i C (W - D) : ℤ) := by
      have h := hle (W - D)
      have hsub : W - (W - D) = D := by abel
      rw [hsub] at h
      exact_mod_cast h
    have hdegWD : C.deg (W - D)
        = 2 * (Work.RiemannRoch.Curve.genus C : ℤ) - 2 - C.deg D := by
      rw [C.deg_sub, hdeg]
    rw [hdegWD] at hRRw
    have : (Work.RiemannRoch.Curve.i C D : ℤ) = (C.l (W - D) : ℤ) := by linarith
    exact_mod_cast this

end Work.RiemannRoch.Canonical
