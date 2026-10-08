import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.Defs
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.isVChar_iff_exists_int_coeffs
import Submission.Work.CharCore.vchar_norm_one
import Submission.Work.CharCore.principalChar_mem_Irr
import Submission.Work.BrauerSuzuki.Characters.sum_sq_three_coeffs
import Submission.Work.BrauerSuzuki.Characters.cfInner_vchar_eq_coeff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A virtual character of norm `3` with trivial multiplicity `1` is `1 + ε₁ Λ - ε₂ Θ`

Let `ν` be a virtual (integral) character of a finite group `G` whose self-inner-product is
`3` and whose inner product with the principal character is `1`.  Writing
`ν = ∑_{χ ∈ Irr G} c χ • χ` with integer coefficients `c`
(`Work.CharCore.isVChar_iff_exists_int_coeffs`) and using orthonormality of `Irr G`
(`Work.CharCore.irr_orthonormal`),

* the norm identity `cfInner ν ν = 3` becomes `∑_χ (c χ)^2 = 3`
  (`Work.CharCore.cfInner_eq_sum_sq`), and
* the identity `cfInner ν 1 = 1` says that the coefficient of the principal character `1`
  is `1` (`Work.BrauerSuzuki.Characters.cfInner_vchar_eq_coeff`).

A sum of integer squares equal to `3` with one coefficient equal to `1` then consists of
exactly three nonzero coefficients `1, ±1, ±1`
(`Work.BrauerSuzuki.Characters.sum_sq_three_coeffs`): the principal character and two further
distinct non-principal irreducible characters `Λ, Θ`, so that `ν = 1 + ε₁ Λ - ε₂ Θ` with
`ε₁, ε₂ ∈ {1, -1}`.
-/

namespace Work.BrauerSuzuki.Characters

open Classical

theorem vchar_of_norm_three {G : Type*} [Group G] [Fintype G] {ν : G → ℂ}
    (hν : Work.CharCore.IsVChar ν) (hnorm : Work.CharCore.cfInner ν ν = 3)
    (h1 : Work.CharCore.cfInner ν (fun _ => (1 : ℂ)) = 1) :
    ∃ (Λ Θ : G → ℂ) (ε₁ ε₂ : ℂ),
      Λ ∈ Work.CharCore.Irr G ∧ Θ ∈ Work.CharCore.Irr G ∧
      Λ ≠ (fun _ => (1 : ℂ)) ∧ Θ ≠ (fun _ => (1 : ℂ)) ∧ Λ ≠ Θ ∧
      (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧
      ν = (fun _ => (1 : ℂ)) + ε₁ • Λ - ε₂ • Θ := by
  obtain ⟨c, hc⟩ := Work.CharCore.isVChar_iff_exists_int_coeffs.mp hν
  -- the index of the principal (trivial) character in `Irr G`
  let iP : ↥(Work.CharCore.Irr G) :=
    ⟨fun _ => (1 : ℂ), Work.CharCore.principalChar_mem_Irr⟩
  have hiP : (iP : G → ℂ) = (fun _ => (1 : ℂ)) := rfl
  -- the multiplicity of the principal character is `1`
  have hcoeff : (c iP : ℂ) = 1 := by
    have h := cfInner_vchar_eq_coeff c iP
    rw [← hc] at h
    rw [← h]
    exact h1
  have hcint : c iP = 1 := by exact_mod_cast hcoeff
  -- the norm identity turns into a sum of squares of the coefficients
  have hsum3 : ∑ χ : ↥(Work.CharCore.Irr G), (c χ) ^ 2 = 3 := by
    have hsq := Work.CharCore.cfInner_eq_sum_sq (s := Work.CharCore.Irr G)
      (fun _ hx => hx) c
    rw [← hc] at hsq
    rw [hnorm] at hsq
    have : ((∑ χ : ↥(Work.CharCore.Irr G), (c χ) ^ 2 : ℤ) : ℂ) = ((3 : ℤ) : ℂ) := by
      push_cast
      exact hsq.symm
    exact Int.cast_injective this
  obtain ⟨i₁, i₂, hi₁₀, hi₂₀, hi₁₂, hc₁, hc₂, hzero⟩ :=
    sum_sq_three_coeffs c hsum3 iP hcint
  -- only the three coefficients at `iP`, `i₁`, `i₂` survive, and the one at `iP` is `1`
  have key : ν = (fun _ => (1 : ℂ)) + (c i₁ : ℂ) • (i₁ : G → ℂ)
      + (c i₂ : ℂ) • (i₂ : G → ℂ) := by
    rw [hc]
    have hrestrict : (∑ χ : ↥(Work.CharCore.Irr G), (c χ : ℂ) • (χ : G → ℂ))
        = ∑ χ ∈ ({iP, i₁, i₂} : Finset ↥(Work.CharCore.Irr G)),
            (c χ : ℂ) • (χ : G → ℂ) := by
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro χ _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      rw [hzero χ hx.1 hx.2.1 hx.2.2]
      simp
    have htriple : (∑ χ ∈ ({iP, i₁, i₂} : Finset ↥(Work.CharCore.Irr G)),
          (c χ : ℂ) • (χ : G → ℂ))
        = (c iP : ℂ) • (iP : G → ℂ) + (c i₁ : ℂ) • (i₁ : G → ℂ)
          + (c i₂ : ℂ) • (i₂ : G → ℂ) := by
      rw [show ({iP, i₁, i₂} : Finset ↥(Work.CharCore.Irr G))
          = insert iP (insert i₁ (insert i₂ ∅)) from rfl]
      rw [Finset.sum_insert (by simp [Ne.symm hi₁₀, Ne.symm hi₂₀]),
          Finset.sum_insert (by simp [hi₁₂]),
          Finset.sum_insert (by simp),
          Finset.sum_empty]
      abel
    rw [hrestrict, htriple, hcoeff, hiP]
    simp
  refine ⟨(i₁ : G → ℂ), (i₂ : G → ℂ), (c i₁ : ℂ), -(c i₂ : ℂ),
    i₁.2, i₂.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hh; exact hi₁₀ (Subtype.ext hh)
  · intro hh; exact hi₂₀ (Subtype.ext hh)
  · intro hh; exact hi₁₂ (Subtype.ext hh)
  · rcases hc₁ with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num
  · rcases hc₂ with h | h
    · right; rw [h]; norm_num
    · left; rw [h]; norm_num
  · rw [key, sub_eq_add_neg, neg_smul, neg_neg]

end Work.BrauerSuzuki.Characters
