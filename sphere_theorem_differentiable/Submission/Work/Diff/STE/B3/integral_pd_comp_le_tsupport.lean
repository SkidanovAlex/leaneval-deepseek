import Mathlib
import Submission.Work.Diff.STE.B3.integral_pd_comp_le_compact
import Submission.Work.Diff.STE.B3.SymCalcStep8.integral_pd_comp_le_nodim_of_support

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-!
# `integral_pd_comp_le_tsupport`

The `L²` bound for the top derivative of `f · (u ∘ T)`,

  `∫_{ℝ^ι} ‖∂^m_l (f · (u ∘ T))‖² ≤ C * Σ_{j ≤ m} Σ_{l'} ∫_{unitCube} ‖∂^{l'} u‖²`,

with a constant `C ≥ 0` depending only on `T`, `f`, `m`, `l` (never on `u`), under the
hypothesis-minimal packaging

* `f` is smooth with compact support (`HasCompactSupport f`), and
* `T` is smooth, injective on `tsupport f`, and `det (fderiv T) ≠ 0` on `tsupport f`.

This is the form in which the hypothesis is actually available in the STE application: `T` is the
periodisation map, which is invertible only in a neighbourhood of `supp f`, and the determinant is
nonvanishing only there; there is no need to produce a *global* open set `U ⊇ tsupport f` on which
`T` is injective (`integral_pd_comp_le_compact` assumes such a `U`).

The mathematics is the change of variables along `T` (`Work.Diff.STE.B3.integralCompPeriodicLe`,
which already takes the injectivity and the determinant hypothesis on the compact set `K` on which
one integrates, followed by the periodicity of `u`) combined with the Leibniz expansion
`pdVecMulCompExpansion` of `∂^m_l (f · (u ∘ T))` and the elementary `‖Σ a_i‖² ≤ (card α) Σ ‖a_i‖²`.

The statement is available verbatim as
`Work.Diff.STE.B3.SymCalcStep8.integral_pd_comp_le_nodim_of_support`; we expose it here under the
name by which the STE chain refers to it.
-/

theorem integral_pd_comp_le_tsupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f)
    (hinj : Set.InjOn T (tsupport f)) (hdet : ∀ z ∈ tsupport f, (fderiv ℝ T z).det ≠ 0)
    (m : ℕ) (l : Fin m → ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : (ι → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
      ∫ z : ι → ℝ, ‖Work.Diff.STE.pdVec m l (fun z => f z * u (T z)) z‖ ^ 2
        ≤ C * ∑ j ∈ Finset.range (m+1), ∑ l' : Fin j → ι,
            ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec j l' u x‖ ^ 2 :=
  Work.Diff.STE.B3.SymCalcStep8.integral_pd_comp_le_nodim_of_support
    T hT f hf hcs hinj hdet m l

end Work.Diff.STE.B3
