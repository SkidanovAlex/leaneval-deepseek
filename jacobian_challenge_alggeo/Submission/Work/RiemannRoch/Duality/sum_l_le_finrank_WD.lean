import Mathlib
import Submission.Work.RiemannRoch.Duality.Basic
import Submission.Work.RiemannRoch.RR.smulW_mem_WD
import Submission.Work.RiemannRoch.RR.smulW_eq_zero_iff
import Submission.Work.CurveBasics.Linear.finiteDimensional_L

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

set_option linter.style.haveILetI false

namespace Work.RiemannRoch.Duality

/-- A Weil differential in `WD C D` multiplied by a function of `L(D - E)` lands in `WD C E`:
`smulW C f ω ∈ WD C (D + div f)`, and `D + div f ≥ E` because `div f + (D - E) ≥ 0`. -/
theorem smulW_mem_WD_of_mem_L {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    {D E : C.Div} {f : C.functionField} (hf : f ∈ C.L (D - E))
    {ω : Module.Dual k (Work.RiemannRoch.Curve.Adeles C)}
    (hω : ω ∈ Work.RiemannRoch.Curve.WD C D) :
    Work.RiemannRoch.Curve.smulW C f ω ∈ Work.RiemannRoch.Curve.WD C E := by
  by_cases h0 : f = 0
  · subst h0
    rw [Work.RiemannRoch.Curve.smulW_zero_left]
    exact Submodule.zero_mem _
  · refine Work.RiemannRoch.Curve.WD_anti C ?_ (Work.RiemannRoch.RR.smulW_mem_WD C h0 hω)
    rw [Finsupp.le_def]
    intro Q
    rw [Work.CurveBasics.Curve.mem_L_iff] at hf
    rcases hf with h | h
    · exact absurd h h0
    · have hQ := h Q
      simp only [Finsupp.add_apply, Finsupp.sub_apply] at hQ ⊢
      linarith

/-- **The counting lemma.** Given Weil differentials `ω i ∈ WD C (D i)` such that the `k`-linear
map `(f i) ↦ ∑ i, f i · ω i` is injective on `∏ i, L (D i - E)`, the sum of the dimensions of
the Riemann–Roch spaces is bounded by `dim WD C E = i E`.

The map `∏ i, L (D i - E) → WD C E`, `(f i) ↦ ∑ i, smulW C (f i) (ω i)`, is `k`-linear and lands
in `WD C E` (previous lemma); injectivity plus `finrank`-additivity of a finite product gives
`∑ i, l (D i - E) = finrank (∏ i, L (D i - E)) ≤ finrank (WD C E)`. -/
theorem sum_l_le_finrank_WD {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) {ι : Type*}
    [Fintype ι] (D : ι → C.Div) (ω : ι → Module.Dual k (Work.RiemannRoch.Curve.Adeles C))
    (E : C.Div) (hω : ∀ i, ω i ∈ Work.RiemannRoch.Curve.WD C (D i))
    (hind : ∀ f : ι → C.functionField, (∀ i, f i ∈ C.L (D i - E)) →
      (∑ i, Work.RiemannRoch.Curve.smulW C (f i) (ω i)) = 0 → ∀ i, f i = 0) :
    (∑ i, C.l (D i - E)) ≤ Module.finrank k ↥(Work.RiemannRoch.Curve.WD C E) := by
  classical
  haveI : FiniteDimensional k ↥(Work.RiemannRoch.Curve.WD C E) :=
    Module.Finite.equiv (Work.RiemannRoch.Curve.WDequiv C E)
  let ψ : ((i : ι) → ↥(C.L (D i - E))) →ₗ[k] ↥(Work.RiemannRoch.Curve.WD C E) :=
    { toFun := fun f => ⟨∑ i, Work.RiemannRoch.Curve.smulW C ((f i : C.functionField)) (ω i),
        Submodule.sum_mem _ (fun i _ => smulW_mem_WD_of_mem_L C (f i).2 (hω i))⟩
      map_add' := fun f g => by
        apply Subtype.ext
        simp only [Submodule.coe_add, Pi.add_apply, Work.RiemannRoch.Curve.smulW_add,
          Finset.sum_add_distrib]
      map_smul' := fun c f => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, Pi.smul_apply, Work.RiemannRoch.Curve.smulW_smul_k,
          Finset.smul_sum, RingHom.id_apply] }
  have hψ : ∀ f : (i : ι) → ↥(C.L (D i - E)),
      (ψ f : Module.Dual k (Work.RiemannRoch.Curve.Adeles C))
        = ∑ i, Work.RiemannRoch.Curve.smulW C (f i : C.functionField) (ω i) := fun f => rfl
  have hinj : Function.Injective ψ := by
    intro f g hfg
    have h0 : ψ (f - g) = 0 := by rw [map_sub, hfg, sub_self]
    have hsum : (∑ i, Work.RiemannRoch.Curve.smulW C (((f - g) i) : C.functionField) (ω i))
        = 0 := by
      have hh := hψ (f - g)
      rw [h0] at hh
      simpa using hh.symm
    have hall := hind (fun i => (((f - g) i) : C.functionField))
      (fun i => ((f - g) i).2) hsum
    have : f - g = 0 := funext (fun i => Subtype.ext (hall i))
    exact sub_eq_zero.mp this
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  calc
    (∑ i, C.l (D i - E)) = ∑ i, Module.finrank k ↥(C.L (D i - E)) := by
      simp only [Work.CurveBasics.Curve.l]
    _ = Module.finrank k ((i : ι) → ↥(C.L (D i - E))) :=
      (Module.finrank_pi_fintype k (M := fun i => ↥(C.L (D i - E)))).symm
    _ ≤ Module.finrank k ↥(Work.RiemannRoch.Curve.WD C E) := hle

end Work.RiemannRoch.Duality
