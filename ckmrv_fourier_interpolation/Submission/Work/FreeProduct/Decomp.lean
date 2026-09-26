import Mathlib
import Submission.Work.FreeProduct.Bridge
import Submission.Work.FreeProduct.Canonical

/-!
# Decomposing `μ ⋅ ℂ[FP]` and the length facts on the two families of prefixes

An element `γ` whose reduced word starts with `x` is `x * γ'` with `γ'` not starting with `x`;
this gives the decomposition `μ * r = μ * (r_0 + x * r_1)` used in the CKMRV proof that `ℐ_-` is
a direct sum.

The second half records the effect on the length of the reduced word of left multiplication by
the prefixes `x`, `y x`, `y² x`, `x y x`, `x y² x` (whose last letter is `x`, so no cancellation
occurs when the word does not start with `x`).
-/

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

/-- `x` is the only nontrivial element of the `ℤ/2` factor. -/
theorem of_C2_eq {m : Cyc false} (hm : m ≠ 1) : Monoid.CoprodI.of (M := Cyc) (i := false) m = x := by
  have h : m = Multiplicative.ofAdd 1 := by revert m hm; decide
  subst h
  exact of_Lx

/-- **Stripping a leading `x`.**  If the reduced word of `γ` starts with `x`, then `γ = x * γ'`
with `γ'` not starting with `x`. -/
theorem exists_X_dcomp (γ : FP) (h : (Monoid.CoprodI.Word.equiv γ).fstIdx = some false) :
    ∃ γ' : FP, γ = x * γ' ∧ NX γ' := by
  obtain ⟨m, t, h1, h2, hw⟩ := exists_cons_of_fstIdx_eq (i := false) h
  refine ⟨t.prod, ?_, ?_⟩
  · have hm : Monoid.CoprodI.of (M := Cyc) (i := false) m = x := of_C2_eq h2
    rw [← hm, ← (Monoid.CoprodI.Word.prod_cons (i := false) m t h2 h1), ← hw, prod_equiv]
  · rw [NX, equiv_prod]; exact h1

/-- **The decomposition underlying the direct sum `ℐ_-`.**  For every `r` there are `r_0 : ℂ` and
`r_1` with `μ * (r_0 + x * r_1) = μ * r`, where all the terms of `r_1` are `1` or start with a
`ℤ/3`-letter. -/
theorem exists_decomp (r : RR) :
    ∃ (r₀ : ℂ) (r₁ : RR),
      MU * (MonoidAlgebra.single (1 : FP) r₀ + X * r₁) = MU * r ∧
      ∀ γ ∈ (MonoidAlgebra.coeff r₁).support, NX γ := by
  classical
  choose f hf hfX using exists_canon
  refine MonoidAlgebra.induction_on (R := ℂ) (M := FP)
    (motive := fun y => ∃ (r₀ : ℂ) (r₁ : RR),
      MU * (MonoidAlgebra.single (1 : FP) r₀ + X * r₁) = MU * y ∧
      ∀ γ ∈ (MonoidAlgebra.coeff r₁).support, NX γ) r ?_ ?_ ?_
  · intro m
    by_cases hm : f m = 1
    · refine ⟨1, 0, ?_, ?_⟩
      · rw [mul_zero, add_zero, show MonoidAlgebra.single (1 : FP) (1 : ℂ) = (1 : RR) from
          MonoidAlgebra.one_def.symm, mul_one, hf m, hm, map_one, mul_one]
      · intro γ hγ
        simp at hγ
    · have hXF : XF (f m) := hfX m
      rw [XF] at hXF
      have hne : Monoid.CoprodI.Word.equiv (f m) ≠ Monoid.CoprodI.Word.empty := by
        intro h
        exact hm (by rw [← prod_equiv (f m), h, Monoid.CoprodI.Word.prod_empty])
      have hnil : (Monoid.CoprodI.Word.equiv (f m)).toList ≠ [] := by
        intro h
        exact hne (Monoid.CoprodI.Word.ext h)
      have hst : (Monoid.CoprodI.Word.equiv (f m)).fstIdx = some false := by
        cases hh : (Monoid.CoprodI.Word.equiv (f m)).fstIdx with
        | none =>
          exfalso
          apply hnil
          cases hlt : (Monoid.CoprodI.Word.equiv (f m)).toList with
          | nil => rfl
          | cons a l => simp [Monoid.CoprodI.Word.fstIdx, hlt] at hh
        | some b =>
          cases b
          · rfl
          · exact absurd hh hXF
      obtain ⟨γ', hγ', hNX⟩ := exists_X_dcomp (f m) hst
      refine ⟨0, MonoidAlgebra.single γ' 1, ?_, ?_⟩
      · rw [MonoidAlgebra.single_zero, zero_add]
        have h1 : X * MonoidAlgebra.single γ' (1 : ℂ) = MonoidAlgebra.of ℂ FP (f m) := by
          rw [hγ']
          show MonoidAlgebra.single x 1 * MonoidAlgebra.single γ' 1 =
            MonoidAlgebra.single (x * γ') 1
          rw [MonoidAlgebra.single_mul_single, mul_one]
        rw [h1, ← hf m, MonoidAlgebra.of_apply]
      · intro γ hγ
        have h : γ = γ' := by simpa using Finsupp.support_single_subset hγ
        rw [h]; exact hNX
  · intro a b ha hb
    obtain ⟨ra, ra', ha1, ha2⟩ := ha
    obtain ⟨rb, rb', hb1, hb2⟩ := hb
    refine ⟨ra + rb, ra' + rb', ?_, ?_⟩
    · rw [show MonoidAlgebra.single (1 : FP) (ra + rb) + X * (ra' + rb') =
          (MonoidAlgebra.single (1 : FP) ra + X * ra') +
            (MonoidAlgebra.single (1 : FP) rb + X * rb') from by
        rw [MonoidAlgebra.single_add, mul_add]; abel,
        mul_add, ha1, hb1, mul_add]
    · intro γ hγ
      have h : MonoidAlgebra.coeff (ra' + rb') γ =
          MonoidAlgebra.coeff ra' γ + MonoidAlgebra.coeff rb' γ := by
        rw [MonoidAlgebra.coeff_add]; rfl
      rw [Finsupp.mem_support_iff] at hγ
      rw [h] at hγ
      by_cases h0 : MonoidAlgebra.coeff ra' γ = 0
      · refine hb2 γ (Finsupp.mem_support_iff.mpr ?_)
        intro hb0
        exact hγ (by rw [h0, hb0, add_zero])
      · exact ha2 γ (Finsupp.mem_support_iff.mpr h0)
  · intro c a ha
    obtain ⟨ra, ra', ha1, ha2⟩ := ha
    refine ⟨c * ra, c • ra', ?_, ?_⟩
    · rw [show MonoidAlgebra.single (1 : FP) (c * ra) =
          c • MonoidAlgebra.single (1 : FP) ra from
            (MonoidAlgebra.smul_single c (1 : FP) ra).symm]
      rw [mul_smul_comm, ← smul_add, mul_smul_comm, ha1, mul_smul_comm]
    · intro γ hγ
      refine ha2 γ (Finsupp.mem_support_iff.mpr ?_)
      intro h0
      rw [Finsupp.mem_support_iff] at hγ
      exact hγ (by simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, h0, smul_zero])

end

end Work.FreeProduct
