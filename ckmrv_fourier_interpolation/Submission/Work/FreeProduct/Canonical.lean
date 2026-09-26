import Mathlib
import Submission.Work.FreeProduct.Bridge

/-!
# Canonicalising the support for the ideal `μ ⋅ ℂ[FP]`

Since `μ = 1 + y + y²` satisfies `μ * y = μ * y² = μ`, left multiplication by `μ` only sees the
`⟨y⟩`-coset of an element.  Consequently every element of `μ ⋅ ℂ[FP]` has a representative whose
support consists of elements that are `1` or start with `x` (`XF`).

This is the "without loss of generality" step in the paper's proof that `ℐ_-` is a direct sum.
-/

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

/-- `y` as a letter of `Cyc true`. -/
theorem of_C3_one :
    Monoid.CoprodI.of (M := Cyc) (i := true) (Multiplicative.ofAdd 1 : C3) = y := by
  exact of_Ly

/-- `y²` as a letter of `Cyc true`. -/
theorem of_C3_two :
    Monoid.CoprodI.of (M := Cyc) (i := true) (Multiplicative.ofAdd 2 : C3) = y2 := by
  exact of_Ly2

/-- For `m ≠ 1` in the `ℤ/3` factor, `μ * m = μ`. -/
theorem MU_mul_of_C3 {m : Cyc true} (hm : m ≠ 1) :
    MU * (MonoidAlgebra.of ℂ FP) (Monoid.CoprodI.of (M := Cyc) (i := true) m) = MU := by
  have h : m = Multiplicative.ofAdd 1 ∨ m = Multiplicative.ofAdd 2 := by revert m hm; decide
  rcases h with h | h
  · subst h
    have h1 : MonoidAlgebra.of ℂ FP
        (Monoid.CoprodI.of (M := Cyc) (i := true) (Multiplicative.ofAdd 1 : C3)) = Y := by
      rw [Y, of_C3_one]
    rw [h1, MU_mul_Y]
  · subst h
    have h2 : MonoidAlgebra.of ℂ FP
        (Monoid.CoprodI.of (M := Cyc) (i := true) (Multiplicative.ofAdd 2 : C3)) = Y2 := by
      rw [Y2, of_C3_two]
    rw [h2, MU_mul_Y2]

/-- Every group element has a canonicalised version, with the same image under left
multiplication by `μ`, whose reduced word does not start with a `ℤ/3`-letter. -/
theorem exists_canon (γ : FP) :
    ∃ γ' : FP, MU * MonoidAlgebra.of ℂ FP γ = MU * MonoidAlgebra.of ℂ FP γ' ∧ XF γ' := by
  by_cases h : XF γ
  · exact ⟨γ, rfl, h⟩
  · rw [XF] at h
    push_neg at h
    obtain ⟨m, t, h1, h2, hw⟩ := exists_cons_of_fstIdx_eq (i := true) h
    refine ⟨t.prod, ?_, ?_⟩
    · have hγ : MonoidAlgebra.of ℂ FP γ =
          MonoidAlgebra.of ℂ FP (Monoid.CoprodI.of (M := Cyc) (i := true) m) *
            MonoidAlgebra.of ℂ FP t.prod := by
        rw [← map_mul, ← Monoid.CoprodI.Word.prod_cons (i := true) m t h2 h1, ← hw, prod_equiv]
      rw [hγ, ← mul_assoc, MU_mul_of_C3 h2]
    · rw [XF, equiv_prod]; exact h1

end

end Work.FreeProduct

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

/-- **Canonicalisation for `μ ⋅ ℂ[FP]`.**  Every element of `μ ⋅ ℂ[FP]` is `μ * r'` for some `r'`
whose support consists of elements that are `1` or start with `x`. -/
theorem exists_MU_canonical (r : RR) :
    ∃ r' : RR, MU * r' = MU * r ∧ ∀ γ ∈ (MonoidAlgebra.coeff r').support, XF γ := by
  classical
  choose f hf hfX using exists_canon
  refine MonoidAlgebra.induction_on (R := ℂ) (M := FP)
    (motive := fun y => ∃ y' : RR, MU * y' = MU * y ∧
      ∀ γ ∈ (MonoidAlgebra.coeff y').support, XF γ) r ?_ ?_ ?_
  · intro m
    refine ⟨MonoidAlgebra.single (f m) 1, ?_, ?_⟩
    · exact (hf m).symm
    · intro γ hγ
      have h : γ = f m := by simpa using Finsupp.support_single_subset hγ
      rw [h]; exact hfX m
  · intro a b ha hb
    obtain ⟨a', ha', haX⟩ := ha
    obtain ⟨b', hb', hbX⟩ := hb
    refine ⟨a' + b', ?_, ?_⟩
    · rw [mul_add, ha', hb', mul_add]
    · intro γ hγ
      have h : MonoidAlgebra.coeff (a' + b') γ =
          MonoidAlgebra.coeff a' γ + MonoidAlgebra.coeff b' γ := by
        rw [MonoidAlgebra.coeff_add]; rfl
      rw [Finsupp.mem_support_iff] at hγ
      rw [h] at hγ
      by_cases h0 : MonoidAlgebra.coeff a' γ = 0
      · refine hbX γ ?_
        rw [Finsupp.mem_support_iff]
        intro hb0
        exact hγ (by rw [h0, hb0, add_zero])
      · exact haX γ (Finsupp.mem_support_iff.mpr h0)
  · intro c a ha
    obtain ⟨a', ha', haX⟩ := ha
    refine ⟨c • a', ?_, ?_⟩
    · rw [mul_smul_comm, mul_smul_comm, ha']
    · intro γ hγ
      refine haX γ (Finsupp.mem_support_iff.mpr ?_)
      intro h0
      rw [Finsupp.mem_support_iff] at hγ
      refine hγ ?_
      simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, h0, smul_zero]

end

end Work.FreeProduct
