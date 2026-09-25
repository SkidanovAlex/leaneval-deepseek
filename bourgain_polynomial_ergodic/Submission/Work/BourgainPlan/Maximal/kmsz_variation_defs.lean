import Mathlib
import Submission.Work.BourgainPlan.Maximal.rhoVarReductions
import Submission.Work.BourgainPlan.Maximal.minor_arc_lp
import Submission.Work.BourgainPlan.Maximal.subtwo_of_dyadic_z

/-!
# The KMSZ (6.5) interface: the variational inequality on the lacunary family

Kosz–Mirek–Słomian–Zhang (arXiv:2606.12663), Theorem 6.4 / inequality (6.5), specialised to the
**`ℤ`-shift system** and to the lacunary family `D_2 = {2^{k+1} : k ≥ 0}` (the case the dyadic
reduction consumes):

`‖V^ρ_{ℤ,p}(A_N f : N ∈ D_2)‖_{ℓᵖ(ℤ)} ≲_{ρ,p,P} ‖f‖_{ℓᵖ(ℤ)}`   for every `ρ > 1`, `p ∈ (1,∞)`,

where `A_N f (m) = N⁻¹ Σ_{i<N} f (m + P(i))` is `discAvgZC` and `V^ρ_{ℤ,p}` is the `ℓᵖ`-norm of the
pointwise `ρ`-variation along the scale family.  This is the single analytic input of the
`1 < p < 2` half of Bourgain's maximal inequality in the KMSZ route: it implies the maximal
inequality for the lacunary scales (KMSZ (6.9), the landed
`eLpNorm_iSup_le_base_add_varRho`), which is the dyadic `ℤ`-form, which is `SubTwoStatement`
(`subtwo_of_dyadic_z`).

`KMSZVariationStatement ρ P p` is that inequality as a named `Prop`; the reduction
"`KMSZVariationStatement` for all `P` and all `1 < p < 2` ⟹ `SubTwoStatement`" is the (elementary)
content of the companion module.
-/

open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The **full `ρ`-variation** of a sequence: the supremum, over all index windows `[0, K]`, of the
windowed `ρ`-variation `varRho ρ 0 K`. -/
def varRhoAll (ρ : ℝ) (a : ℕ → E) : ℝ≥0∞ := ⨆ K : ℕ, varRho ρ 0 K a

lemma varRho_le_varRhoAll (ρ : ℝ) (a : ℕ → E) (K : ℕ) :
    varRho ρ 0 K a ≤ varRhoAll ρ a := le_iSup (fun K : ℕ => varRho ρ 0 K a) K

/-- **KMSZ (6.5) on the lacunary family `{2^{k+1}}`** for the `ℤ`-shift system: the `ℓᵖ(ℤ)` norm of
the pointwise `ρ`-variation of the polynomial averages along the scales `N = 2^{k+1}` is bounded by
`C‖f‖_{ℓᵖ(ℤ)}`. -/
def KMSZVariationStatement (ρ : ℝ) (P : Polynomial ℤ) (p : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℤ → ℂ), (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
    ∫⁻ m : ℤ, (varRhoAll ρ (fun k : ℕ => discAvgZC P (2 ^ (k + 1)) g m)) ^ p
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C ^ p) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂MeasureTheory.Measure.count

end

end Work.BourgainPlan.Maximal
