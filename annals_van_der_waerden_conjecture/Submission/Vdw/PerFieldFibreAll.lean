import Mathlib
import Submission.Vdw.PerFieldFibre
import Submission.Vdw.PrimitiveCase
import Submission.Vdw.FourImprimitive
import Submission.Vdw.ImprimitiveInput
import Submission.Commons.NumberTheory.NumberField.exists_nontrivial_block_of_intermediate

open Polynomial Filter Asymptotics
open scoped BigOperators
open scoped Pointwise
open Function
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The Lemke Oliver–Thorne per-field fibre bound for primitive Galois groups

`PerFieldFibre.perFieldFibreBound_of_region_gen` proves the per-field fibre
bound from the hypothesis that every non-rational element of the field of a
region member generates that field.  In prime degree this is automatic
(`adjoin_eq_top_of_prime_finrank`), giving `perFieldFibreBound_prime`.  Here we
supply the composite-degree input: for a member `f` of the Case-II region the
Galois group `Gal(f)` is **primitive** (`SubcaseI_P2 ⊆ SubcaseI` and
`SubcaseI ⊆ PrimitiveBad`), and a primitive Galois group has no proper
subextension — a proper intermediate field `ℚ ⊆ F ⊊ K_f` yields a nontrivial
block system for the action of `Gal(f)` on the roots of `f`
(`Commons.NumberTheory.NumberField.exists_nontrivial_block_of_intermediate`),
contradicting primitivity.

Consequently `perFieldFibreBound_all` holds for **every** `n ≥ 3`, and the
Lemke Oliver–Thorne input is no longer an input in any degree.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-! ## Primitivity ⟹ every non-rational element generates -/

/-- **The block-system argument.**  If the Galois group of a monic irreducible
`f : ℤ[X]` acts primitively on the roots, then every non-rational element of
`K_f = AdjoinRoot (f.map φℚ)` generates `K_f`.

Indeed, if `α` is non-rational and `ℚ(α) ≠ K_f`, the common eigenspace
`{x : ψ_x(α) = ψ_{x₀}(α)}` of the classical proof is a nontrivial block of the
Galois action on the roots (`exists_nontrivial_block_of_intermediate`), which
primitivity forbids. -/
theorem adjoin_eq_top_of_galPrimitive {f : ℤ[X]} (h : Irreducible (f.map φℚ))
    (hprim : galPrimitive f h) {α : Kpoly f}
    (hα : α ∉ Set.range (algebraMap ℚ (Kpoly f))) :
    Algebra.adjoin ℚ ({α} : Set (Kpoly f)) = ⊤ := by
  classical
  by_contra hne
  haveI hFact : Fact (Irreducible (f.map φℚ)) := ⟨h⟩
  have hsep : (f.map φℚ).Separable := separable_of_irreducible_rat h
  haveI hsplit : Fact (((f.map φℚ).map (algebraMap ℚ (f.map φℚ).SplittingField)).Splits) :=
    ⟨Polynomial.SplittingField.splits (f.map φℚ)⟩
  obtain ⟨B, hBsub, hBuniv, hBdisj⟩ :=
    Commons.NumberTheory.NumberField.exists_nontrivial_block_of_intermediate
      (p := f.map φℚ) h hsep (rootFinEquiv (f.map φℚ) hsep) hne hα
  have hblock : MulAction.IsBlock ((irrGalFinHom f).range) B := by
    rintro ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩ hne'
    obtain ⟨σ, rfl⟩ := hg₁
    obtain ⟨τ, rfl⟩ := hg₂
    exact hBdisj σ τ hne'
  exact (hprim.isTrivialBlock_of_isBlock hblock).elim hBsub hBuniv

/-! ## The per-field fibre bound in every degree -/

/-- **The Lemke Oliver–Thorne per-field fibre bound is a theorem in every
degree `n ≥ 3`.** -/
theorem perFieldFibreBound_all (n : ℕ) (hn : 3 ≤ n) :
    PerFieldFibreBound n (by omega : 1 ≤ n) :=
  perFieldFibreBound_of_region_gen n hn fun H f α hα => by
    obtain ⟨h, hprim, -⟩ := f.2.1.2
    exact adjoin_eq_top_of_galPrimitive h hprim hα

/-- The prime-degree form, re-derived from the general one. -/
theorem perFieldFibreBound_prime' (n : ℕ) (hn : 3 ≤ n) (hp : Nat.Prime n) :
    PerFieldFibreBound n (by omega : 1 ≤ n) :=
  perFieldFibreBound_prime n hn hp

/-! ## Endpoints with the per-field input discharged in every degree -/

/-- **The challenge statement from the field count and the imprimitive bound
alone.**  The Lemke Oliver–Thorne per-field fibre bound is no longer an input,
in any degree. -/
theorem theorem_1_of_fieldCountBound (n : ℕ) (hn : 3 ≤ n) (β : ℝ)
    (hβ : 1 / ((n : ℝ) * ((n : ℝ) - 1)) < β)
    (hexp : 1 + (2 + 4 / (weylM n : ℝ)) * (β - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
      < (n : ℝ) - 1)
    (hSC : FieldCountBound n (by omega : 1 ≤ n) β)
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_field_inputs n hn β hβ hexp (perFieldFibreBound_all n hn) hSC h4

/-- **Degree 3**: the challenge theorem from the count of cyclic cubic fields
(`β = 1/2`) alone — no Lemke Oliver–Thorne input, and the imprimitive bound is
vacuous. -/
theorem theorem_1_of_cubic_fieldCount_all
    (hSC : FieldCountBound 3 (by omega : 1 ≤ 3) (1 / 2)) :
    (fun H : ℕ => (E 3 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (3 - 1) : ℝ)) :=
  theorem_1_of_field_inputs 3 (by omega) (1 / 2) (by norm_num) weylM_exponent_three
    (perFieldFibreBound_all 3 (by omega)) hSC (ImprimitiveBad_isBigO_of_prime 3 (by norm_num))

/-- **Degree 4**: the challenge theorem from the exact quartic field count
(`β = 1`) — the imprimitive input is the machine-checked
`ImprimitiveBad_four_isBigO`. -/
theorem theorem_1_of_quartic_fieldCount_all
    (hSC : FieldCountBound 4 (by omega : 1 ≤ 4) 1) :
    (fun H : ℕ => (E 4 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (4 - 1) : ℝ)) :=
  theorem_1_of_field_inputs 4 (by omega) 1 (by norm_num) weylM_exponent_four
    (perFieldFibreBound_all 4 (by omega)) hSC ImprimitiveBad_four_isBigO

/-- **Degree 5**: the challenge theorem from the exact quintic field count
(`β = 1`). -/
theorem theorem_1_of_quintic_fieldCount_all
    (hSC : FieldCountBound 5 (by omega : 1 ≤ 5) 1) :
    (fun H : ℕ => (E 5 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (5 - 1) : ℝ)) :=
  theorem_1_of_field_inputs 5 (by omega) 1 (by norm_num) weylM_exponent_five
    (perFieldFibreBound_all 5 (by omega)) hSC (ImprimitiveBad_isBigO_of_prime 5 (by norm_num))

/-- **Degrees `n ≥ 6`**: the challenge theorem from Schmidt's field count and
Widmer's imprimitive bound. -/
theorem theorem_1_of_schmidt_and_widmer (n : ℕ) (hn : 6 ≤ n)
    (hSC : FieldCountBound n (by omega : 1 ≤ n) (((n : ℝ) + 2) / 4))
    (hw : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ ((n : ℝ) / 2 + 2))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hβ : 1 / ((n : ℝ) * ((n : ℝ) - 1)) < ((n : ℝ) + 2) / 4 := by
    have hnR : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    rw [div_lt_iff₀ hden]
    nlinarith
  exact theorem_1_of_field_inputs n (by omega) (((n : ℝ) + 2) / 4) hβ
    (weylM_exponent_schmidt n hn) (perFieldFibreBound_all n (by omega)) hSC
    (ImprimitiveBad_isBigO_of_widmer n hn hw)

end

end Submission.Vdw
