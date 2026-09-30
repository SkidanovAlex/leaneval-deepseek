import Mathlib
import Submission.Work.RiemannRoch.Canonical
import Submission.Work.RiemannRoch.Duality.Basic
import Submission.Work.RiemannRoch.Duality.exists_isDivW
import Submission.Work.RiemannRoch.Duality.smulW_divW
import Submission.Work.RiemannRoch.Duality.exists_smulW_eq
import Submission.Work.RiemannRoch.Duality.finrank_WD
import Submission.Work.RiemannRoch.RR.smulW_mem_WD
import Submission.Work.RiemannRoch.RR.smulW_eq_zero_iff
import Submission.Work.CurveBasics.Linear.finiteDimensional_L

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Classical

namespace Work.RiemannRoch.Duality

/-- **Serre duality**: the divisor of a nonzero Weil differential is canonical.

Let `ω ∈ Ω C` be a nonzero Weil differential and `W = divW C ω` its divisor (the largest
divisor with `ω ∈ WD C W`, which exists by `exists_isDivW`).  We show
`i C D = l (W - D)` for every divisor `D`.

The `k`-linear map `L(W - D) → WD D`, `f ↦ f ω`, is well defined (a function of `L(W-D)`
multiplied into `ω ∈ WD W` still vanishes on `K + A(D)`, `smulW_mem_WD_of_mem_L`), injective
(`f ω = 0` with `f ≠ 0` forces `ω = 0`), and surjective: any `η ∈ WD D` is
`η = g ω` for some `g ∈ K` because `dim_K Ω = 1` (`exists_smulW_eq`); from `η ∈ WD D` and
`divW η = divW ω + div g = W + div g` (`smulW_divW`) we get `D ≤ W + div g`, i.e.
`g ∈ L(W - D)`.  Hence `l (W - D) = finrank (WD D) = i D`. -/
theorem isCanonical_divW {k : Type*} [Field k] (C : Work.CurveBasics.Curve k)
    {ω : Module.Dual k (Work.RiemannRoch.Curve.Adeles C)}
    (hω : ω ∈ Work.RiemannRoch.Curve.Omega C) (hω0 : ω ≠ 0) :
    Work.RiemannRoch.Curve.IsCanonical C (Work.RiemannRoch.Curve.divW C ω) := by
  classical
  intro D
  obtain ⟨W₀, hW₀⟩ := exists_isDivW C hω hω0
  set W : C.Div := Work.RiemannRoch.Curve.divW C ω with hWdef
  have hW : Work.RiemannRoch.Curve.IsDivW C ω W := by
    rw [hWdef]; exact Work.RiemannRoch.Curve.divW_spec C ⟨W₀, hW₀⟩
  -- The map `f ↦ f ω`, `L(W - D) → WD D`.
  have hmaps : ∀ f : ↥(C.L (W - D)),
      ((Work.RiemannRoch.Curve.smulWLin C ω).comp (C.L (W - D)).subtype) f
        ∈ Work.RiemannRoch.Curve.WD C D := by
    intro f
    rw [LinearMap.comp_apply, Submodule.subtype_apply, Work.RiemannRoch.Curve.smulWLin_apply]
    exact Work.RiemannRoch.Curve.smulW_mem_WD_of_mem_L C (D := W) (E := D) f.2 hW.1
  let Φ : ↥(C.L (W - D)) →ₗ[k] ↥(Work.RiemannRoch.Curve.WD C D) :=
    LinearMap.codRestrict (Work.RiemannRoch.Curve.WD C D)
      ((Work.RiemannRoch.Curve.smulWLin C ω).comp (C.L (W - D)).subtype) hmaps
  have Φ_apply : ∀ f : ↥(C.L (W - D)),
      ((Φ f : ↥(Work.RiemannRoch.Curve.WD C D)) : Work.RiemannRoch.Curve.WeilDifferential C)
        = Work.RiemannRoch.Curve.smulW C (f : C.functionField) ω := fun f => rfl
  have hinj : Function.Injective Φ := by
    intro f g hfg
    have hfg' : Work.RiemannRoch.Curve.smulW C (f : C.functionField) ω
        = Work.RiemannRoch.Curve.smulW C (g : C.functionField) ω := by
      rw [← Φ_apply f, ← Φ_apply g, hfg]
    have hdiff : Work.RiemannRoch.Curve.smulW C
        ((f : C.functionField) - (g : C.functionField)) ω = 0 := by
      rw [sub_eq_add_neg, Work.RiemannRoch.Curve.smulW_add,
        Work.RiemannRoch.Curve.smulW_neg_left, hfg', add_neg_cancel]
    by_cases h0 : (f : C.functionField) - (g : C.functionField) = 0
    · exact Subtype.ext (sub_eq_zero.mp h0)
    · exact absurd ((Work.RiemannRoch.RR.smulW_eq_zero_iff C h0 ω).mp hdiff) hω0
  have hsurj : Function.Surjective Φ := by
    intro η
    have hηOmega : (η : Work.RiemannRoch.Curve.WeilDifferential C)
        ∈ Work.RiemannRoch.Curve.Omega C :=
      Work.RiemannRoch.Curve.le_Omega C D η.2
    obtain ⟨g, hg⟩ := exists_smulW_eq C hω hω0 hηOmega
    by_cases hg0 : g = 0
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      rw [Φ_apply]
      have hz : (η : Work.RiemannRoch.Curve.WeilDifferential C) = 0 := by
        rw [hg, hg0, Work.RiemannRoch.Curve.smulW_zero_left]
      rw [hz]
      simp only [Submodule.coe_zero, Work.RiemannRoch.Curve.smulW_zero_left]
    · have hη0ne : (η : Work.RiemannRoch.Curve.WeilDifferential C) ≠ 0 := by
        rw [hg]; exact Work.RiemannRoch.Curve.smulW_ne_zero C hg0 hω0
      have hex : ∃ W' : C.Div, Work.RiemannRoch.Curve.IsDivW C
          (η : Work.RiemannRoch.Curve.WeilDifferential C) W' :=
        exists_isDivW C hηOmega hη0ne
      have hle : D ≤ Work.RiemannRoch.Curve.divW C
          (η : Work.RiemannRoch.Curve.WeilDifferential C) :=
        Work.RiemannRoch.Curve.le_divW C hex η.2
      have hdivw : Work.RiemannRoch.Curve.divW C
          (η : Work.RiemannRoch.Curve.WeilDifferential C) = W + C.div g := by
        rw [hg]
        exact smulW_divW C hω hω0 hg0
      have hle' : D ≤ W + C.div g := by rw [hdivw] at hle; exact hle
      have hmem : g ∈ C.L (W - D) := by
        rw [Work.CurveBasics.Curve.mem_L_iff]
        refine Or.inr fun Q => ?_
        have hQ : D Q ≤ (W + C.div g) Q := (Finsupp.le_def.mp hle') Q
        rw [Finsupp.add_apply] at hQ
        simp only [Finsupp.add_apply, Finsupp.sub_apply]
        linarith
      refine ⟨⟨g, hmem⟩, ?_⟩
      apply Subtype.ext
      rw [Φ_apply]
      exact hg.symm
  have hfin : Module.finrank k ↥(C.L (W - D))
      = Module.finrank k ↥(Work.RiemannRoch.Curve.WD C D) :=
    (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).finrank_eq
  have hmain : Work.RiemannRoch.Curve.i C D = C.l (W - D) := by
    rw [← finrank_WD C D]
    exact hfin.symm
  exact hmain

end Work.RiemannRoch.Duality
