import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.Polynomial.Norm
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Analysis.Polynomial.exists_root_close_of_eval_lt
import Submission.Commons.Analysis.Polynomial.value_lt_leadingCoeff_mul_pow
import Submission.Commons.FieldTheory.Polynomial.factorization_of_splits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Polynomial

/-- **Root closeness with prescribed separation `δ` (uniform in `f₂`).**  If
`f₁` has degree ≥ 1 over the normed field `K` and `δ > 0`, then there is a
threshold `ε > 0`, depending only on `f₁`, `δ` and the extension `L/K`, such
that for every nonzero `f₂ : K[X]` of degree at most that of `f₁` whose image in
`L[X]` splits and which is `ε`-close to `f₁` in the sup-norm, every root `α ∈ L`
of `f₁` has a root `β ∈ L` of `f₂` with `‖α - β‖ < δ`. -/
theorem exists_root_close_with_delta {K L : Type*} [NormedField K] [NormedField L] [Algebra K L]
    (h_ext : ∀ k : K, ‖algebraMap K L k‖ = ‖k‖)
    {f₁ : Polynomial K} (hf₁1 : 1 ≤ f₁.natDegree) {δ : ℝ} (hδpos : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (f₂ : Polynomial K), f₂.natDegree ≤ f₁.natDegree → f₂ ≠ 0 →
      (f₂.map (algebraMap K L)).Splits → (f₂ - f₁).supNorm < ε →
      ∀ {α : L}, α ∈ f₁.rootSet L →
        ∃ β : L, β ∈ (f₂.map (algebraMap K L)).roots ∧ ‖α - β‖ < δ := by
  obtain ⟨ε, hεpos, _hεle, hεmain⟩ :=
    value_lt_leadingCoeff_mul_pow h_ext f₁ hf₁1 δ hδpos
  refine ⟨ε, hεpos, ?_⟩
  intro f₂ hf₂ hf₂0 hsplits hclose α hαroot
  -- `f₁(α) = 0`, and `ε`-closeness bounds `‖f₂(α)‖` by `‖lc f₂‖ * δ ^ deg f₂`.
  have hα : (Polynomial.aeval α) f₁ = 0 :=
    Polynomial.aeval_eq_zero_of_mem_rootSet hαroot
  have hval : ‖(Polynomial.aeval α) f₂‖ < ‖f₂.coeff f₂.natDegree‖ * δ ^ f₂.natDegree :=
    hεmain f₂ hf₂ hclose hα
  -- move to `L[X]`, where `f₂` splits and factors over its roots
  have hg0 : f₂.map (algebraMap K L) ≠ 0 := Polynomial.map_ne_zero hf₂0
  obtain ⟨hfac, hcard⟩ := Commons.FieldTheory.Polynomial.factorization_of_splits (f₂.map (algebraMap K L)) hg0 hsplits
  have hval' : ‖(f₂.map (algebraMap K L)).eval α‖ <
      ‖(f₂.map (algebraMap K L)).leadingCoeff‖ * δ ^ (f₂.map (algebraMap K L)).roots.card := by
    have h1 : Polynomial.eval α (f₂.map (algebraMap K L)) = (Polynomial.aeval α) f₂ := by
      rw [Polynomial.eval_map, Polynomial.aeval_def]
    have h2 : (f₂.map (algebraMap K L)).leadingCoeff =
        algebraMap K L (f₂.coeff f₂.natDegree) := by
      rw [Polynomial.leadingCoeff_map, Polynomial.coeff_natDegree]
    have h3 : (f₂.map (algebraMap K L)).roots.card = f₂.natDegree := by
      rw [hcard, Polynomial.natDegree_map]
    rw [h1, h2, h_ext (f₂.coeff f₂.natDegree), h3]
    exact hval
  -- the elementary factorisation argument produces a close root
  obtain ⟨β, hβmem, hβclose⟩ := exists_root_close_of_eval_lt (f₂.map (algebraMap K L)) hδpos
    (f₂.map (algebraMap K L)).roots hfac hval'
  exact ⟨β, hβmem, hβclose⟩

end Commons.Analysis.Polynomial
