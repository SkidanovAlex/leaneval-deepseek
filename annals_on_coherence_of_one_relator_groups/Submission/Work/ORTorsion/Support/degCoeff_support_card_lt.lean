/-
# The support of the degree-`b` coefficient is strictly smaller when `x` has a term of
# degree `≠ b`

For `x : K[H]` and `Lb : LaurentBase K U G gen D H φ`, the degree-`b` coefficient
`degCoeff Lb b x` keeps the terms of `x` of degree `b` and shifts each of them back to degree
`0` by the generator `s ^ (-b)`; the terms of other degrees are dropped.  Since `h ↦ h * s ^ (-b)`
is injective, the support of `degCoeff Lb b x` is no larger than the support of `x` (this is
`Support.degCoeff_support_card_le`).  If in addition `x` has a term of degree different from `b`,
then this support is *strictly* smaller:

`(degCoeff Lb b x).coeff.support.card < x.coeff.support.card`.

Indeed, `degCoeff Lb b x` is supported in the image of the *degree-`b` part* of the support of
`x`, which is a proper subset of the support of `x` because of the term of degree `≠ b`.  This is
the "the degree-`b` part has strictly fewer terms" ingredient in the induction of the torsion
crux (`N8_TORSION_LEAD.md`, step 7 of L6).
-/
import Mathlib
import Submission.Work.ORTorsion.Defs

namespace Work.ORTorsion.Support

open scoped TensorProduct
open Work.ORTorsion
open Work.ORTorsion.LaurentBase

theorem degCoeff_support_card_lt {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Algebra K U] (L : TorsionData K G U) {H : Subgroup G}
    {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ) (x : MonoidAlgebra K H)
    (b : ℤ) (hb : ∃ h ∈ x.coeff.support, deg φ h ≠ b) :
    (LaurentBase.degCoeff Lb b x).coeff.support.card < x.coeff.support.card := by
  classical
  -- The terms of `x` of degree `b`, the only ones contributing to `degCoeff Lb b x`.
  set S : Finset H := x.coeff.support.filter (fun h => φ h = Multiplicative.ofAdd b) with hS
  -- The degree-`b` part of `x`, as a family of `Finsupp`s on the kernel `N`.
  set F : H → (↥Lb.N →₀ K) := fun h =>
    if hh : φ h = Multiplicative.ofAdd b then
      Finsupp.single ⟨(h * Lb.s ^ (-b) : H),
        Lb.mem_N_of_mem_ker (Lb.mem_ker_mul_zpow hh)⟩ (x.coeff h)
    else 0 with hFdef
  -- The total map `h ↦ h * s ^ (-deg φ h)`, which maps `H` into the kernel `N`.
  set f : H → ↥Lb.N := fun h =>
    ⟨h * Lb.s ^ (-(deg φ h)), Lb.mem_N_of_mem_ker (Lb.mem_ker_mul_zpow (deg_apply φ h))⟩
    with hfdef
  have hdeg : (LaurentBase.degCoeff Lb b x).coeff = ∑ h ∈ x.coeff.support, F h := by
    rw [LaurentBase.degCoeff, MonoidAlgebra.coeff_ofCoeff, hFdef]
  -- Terms outside `S` contribute nothing.
  have hsum : ∑ h ∈ S, F h = ∑ h ∈ x.coeff.support, F h := by
    refine Finset.sum_subset ?_ ?_
    · rw [hS]; exact Finset.filter_subset _ _
    · intro h hhS0 hhnotS
      by_cases hb' : φ h = Multiplicative.ofAdd b
      · exact absurd (by rw [hS]; exact Finset.mem_filter.mpr ⟨hhS0, hb'⟩) hhnotS
      · simp [hFdef, hb']
  -- Every element of the support of `degCoeff Lb b x` is the image of a degree-`b` term of `x`.
  have himg : (∑ h ∈ S, F h).support ⊆ S.image f := by
    intro g hg
    obtain ⟨h, hhS, hgh⟩ := Finsupp.mem_support_finsetSum g hg
    rw [Finset.mem_filter] at hhS
    obtain ⟨hhS0, hb'⟩ := hhS
    refine Finset.mem_image.mpr ⟨h, ?_, ?_⟩
    · rw [hS]; exact Finset.mem_filter.mpr ⟨hhS0, hb'⟩
    have hgh' : g ∈ (Finsupp.single ⟨(h * Lb.s ^ (-b) : H),
        Lb.mem_N_of_mem_ker (Lb.mem_ker_mul_zpow hb')⟩ (x.coeff h) : ↥Lb.N →₀ K).support := by
      simpa [hFdef, hb'] using hgh
    have h1 : g = ⟨(h * Lb.s ^ (-b) : H), Lb.mem_N_of_mem_ker (Lb.mem_ker_mul_zpow hb')⟩ := by
      simpa using Finsupp.support_single_subset hgh'
    -- on the terms of degree `b` the total map `f` is `h ↦ h * s ^ (-b)`
    have hdegb : deg φ h = b := by
      have h2 := deg_apply φ h
      rw [hb'] at h2
      exact Multiplicative.ofAdd.injective h2.symm
    have hfh : f h
        = ⟨(h * Lb.s ^ (-b) : H), Lb.mem_N_of_mem_ker (Lb.mem_ker_mul_zpow hb')⟩ := by
      rw [hfdef]
      refine Subtype.ext ?_
      simp only [hdegb]
      simp
    rw [hfh, h1]
  -- The degree-`b` part of the support is a proper subset of the support.
  have hstrict : S.card < x.coeff.support.card := by
    obtain ⟨h0, h0mem, h0deg⟩ := hb
    have h0notS : h0 ∉ S := by
      rw [hS, Finset.mem_filter]
      rintro ⟨-, hc⟩
      exact h0deg (by
        have h2 := deg_apply φ h0
        rw [hc] at h2
        exact Multiplicative.ofAdd.injective h2.symm)
    have hne : S ≠ x.coeff.support := fun heq => h0notS (heq.symm ▸ h0mem)
    exact Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr
        ⟨by rw [hS]; exact Finset.filter_subset _ _, hne⟩)
  -- Assemble the two bounds.
  have hle : (LaurentBase.degCoeff Lb b x).coeff.support.card ≤ S.card := by
    rw [hdeg, ← hsum]
    exact le_trans (Finset.card_le_card himg) Finset.card_image_le
  exact lt_of_le_of_lt hle hstrict

end Work.ORTorsion.Support
