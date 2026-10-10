import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Normed.Field.Krasner
import Submission.Commons.FieldTheory.IntegralClosure.isIntegral_of_aeval_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.Polynomial

open _root_.Polynomial

/-- **Krasner's lemma, root-closeness form.**  Let `K` be a complete nontrivially
normed field with ultrametric norm, and `L` a normed algebraic extension of `K`.
If `α` is a root of a separable `f₁ ≠ 0`, `β` a root of `f₂ ≠ 0`, the minimal
polynomial of `α` splits over `L`, and `β` is closer to `α` than every other
root `γ ≠ α` of `f₁`, then `α ∈ K⟮β⟯`. -/
theorem mem_adjoin_of_close {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L]
    {f₁ f₂ : Polynomial K} (hf₁ : f₁.Separable) (hf₁0 : f₁ ≠ 0) (hf₂0 : f₂ ≠ 0)
    {α β : L} (hα : (Polynomial.aeval α) f₁ = 0)
    (hβ : β ∈ (f₂.map (algebraMap K L)).roots)
    (hsp : ((minpoly K α).map (algebraMap K L)).Splits)
    (hclose : ∀ γ ∈ f₁.rootSet L, γ ≠ α → ‖α - β‖ < ‖α - γ‖) :
    α ∈ IntermediateField.adjoin K ({β} : Set L) := by
  have hxint : IsIntegral K α :=
    Commons.FieldTheory.IntegralClosure.isIntegral_of_aeval_eq_zero hf₁0 hα
  have hx : (minpoly K α).Separable :=
    Polynomial.Separable.of_dvd hf₁ (minpoly.dvd K α hα)
  have hβroot : (Polynomial.aeval β) f₂ = 0 := by
    have h := (Polynomial.mem_roots (Polynomial.map_ne_zero hf₂0)).mp hβ
    have h2 : eval β (f₂.map (algebraMap K L)) = 0 := Polynomial.IsRoot.def.mp h
    rw [Polynomial.eval_map] at h2
    rw [Polynomial.aeval_def]
    exact h2
  have hy : IsIntegral K β :=
    Commons.FieldTheory.IntegralClosure.isIntegral_of_aeval_eq_zero hf₂0 hβroot
  refine IsKrasner.krasner hx hsp hy ?_
  intro x' hconj hne
  refine hclose x' ?_ (Ne.symm hne)
  have hmem : x' ∈ (minpoly K α).rootSet L :=
    (isConjRoot_iff_mem_minpoly_rootSet hxint).mp hconj
  obtain ⟨m, hm⟩ := minpoly.dvd K α hα
  rw [Polynomial.mem_rootSet] at hmem ⊢
  obtain ⟨_, hroot⟩ := hmem
  refine ⟨hf₁0, ?_⟩
  rw [hm, map_mul, hroot, zero_mul]

end Commons.FieldTheory.Polynomial