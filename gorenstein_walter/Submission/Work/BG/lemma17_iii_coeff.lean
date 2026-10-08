import Mathlib
import Submission.Work.BG.Defs
import Submission.Work.BG.Lambda
import Submission.Work.BG.H0Conj
import Submission.Work.BG.CharBridge
import Submission.Work.BG.conjByH_basic
import Submission.Work.BG.lemma17_ii_aux
import Submission.Work.BG.lemma17_iii_aux

/-!
# Area BG: the coefficient identity of Bender–Glauberman 1981, Lemma 1.7(iii)

This module proves `Work.BG.lemma17_iii_coeff`, the class-function identity that converts the
coefficient `(χ, (ν - λ₂ν^s)^G)_G` of Lemma 1.7(iii) into the two explicit coefficients
`(χ|_{H₀}, ν)_{H₀}` and `(χ|_{H₀}, λ₂ν)_{H₀}` appearing in the regrouped expansion of
`χ|_{H₀}` (`Work.BG.lemma17_iii_regroup`).

The mathematical content is

* Frobenius reciprocity `⟨χ, θ^G⟩_G = ⟨χ|_{H₀}, θ⟩_{H₀}`,
* additivity of `inner` in the second argument,
* and the two invariance facts: `χ|_{H₀}` is fixed by `ν ↦ ν^s`, and `λ₂^s = λ₂`.

The latter follows from `|H₀/U| = 2`: conjugation by `s ∈ H` induces an automorphism of the
two-element group `H₀/U`, and such an automorphism is trivial.

## Helper lemmas

* `Work.BG.eq_of_ne_one_of_card_two` — in a group of order two any two non-identity
  elements coincide (used to see that the induced action on `H₀/U` is trivial);
* `Work.BG.conjByH_map_mul` — `conjByH` is multiplicative (it is `compHom` of a group
  isomorphism);
* `Work.BG.conjByH_restrict_eq_self` — a class function of `G` restricted to `H₀` is fixed
  by `ν ↦ ν^s`;
* `Work.BG.conjByH_lambdaInf_eq_self` — the inflation `λ₂ = Inf(lam2)` is fixed by
  `ν ↦ ν^s` because `H₀/U` has order two.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-- In a group of cardinality two, any two non-identity elements coincide.  (A group of
order two has a unique involution; here we only use the underlying set of size two.) -/
theorem eq_of_ne_one_of_card_two {A : Type*} [Group A] [Finite A] (h : Nat.card A = 2)
    {a b : A} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  classical
  have hfin : Fintype A := Fintype.ofFinite A
  have hcard : Fintype.card A = 2 := by
    rw [← Nat.card_eq_fintype_card]; exact h
  have hne : (1 : A) ≠ a := (Ne.symm ha)
  have hpair : ({1, a} : Finset A).card = 2 := Finset.card_pair hne
  have huniv : ({1, a} : Finset A) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hpair, hcard])
  have hb_mem : b ∈ ({1, a} : Finset A) := by rw [huniv]; exact Finset.mem_univ b
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb_mem
  rcases hb_mem with hb1 | hba
  · exact absurd hb1 hb
  · exact hba.symm

/-- `ν ↦ ν^s` is multiplicative: it is `ClassFunction.compHom` along the group isomorphism
`conjMulEquiv P s`. -/
theorem conjByH_map_mul (P : Hyp12 G) (s : ↥P.H) (a b : ClassFunction ↥P.H0 ℂ) :
    conjByH P s (a * b) = conjByH P s a * conjByH P s b := by
  ext h
  rw [conjByH_apply, ClassFunction.mul_apply, ClassFunction.mul_apply]
  rw [conjByH_apply, conjByH_apply]

/-- The restriction to `H₀` of a class function of `G` is fixed by `ν ↦ ν^s` (for any
`s ∈ H`), because a class function is conjugation invariant. -/
theorem conjByH_restrict_eq_self (P : Hyp12 G) (s : ↥P.H) (χ : ClassFunction G ℂ) :
    conjByH P s (ClassFunction.restrict P.H0 χ) = ClassFunction.restrict P.H0 χ := by
  ext h
  rw [conjByH_apply, ClassFunction.restrict_apply, conjMulEquiv_apply,
    ClassFunction.restrict_apply]
  exact χ.conj_eq (h : G) (s : G)

/-- **`λ` is `s`-invariant.**  For `|H₀/U| = 2`, the conjugation automorphism of `H₀/U`
induced by any `s ∈ H` is trivial (a two-element group has no non-trivial automorphism), so
the inflation of a linear character of `H₀/U` is fixed by `ν ↦ ν^s`.

The proof compares the two quotient classes `quotMk P (s h s⁻¹)` and `quotMk P h`: they are
trivial simultaneously (`s` normalises `U`), and `H₀/U` has a unique non-identity element
(`eq_of_ne_one_of_card_two`). -/
theorem conjByH_lambdaInf_eq_self (P : Hyp12 G) [(P.U.subgroupOf P.H0).Normal]
    (h2 : Nat.card (quotGroup P) = 2) (s : ↥P.H) (β : quotGroup P →* ℂˣ) :
    conjByH P s (lambdaInf P β) = lambdaInf P β := by
  classical
  ext h
  rw [conjByH_apply, lambdaInf_apply, lambdaInf_apply]
  suffices quotMk P (conjMulEquiv P s h) = quotMk P h by rw [this]
  have hmem : conjMulEquiv P s h ∈ P.U.subgroupOf P.H0 ↔ h ∈ P.U.subgroupOf P.H0 := by
    show ((conjMulEquiv P s h : ↥P.H0) : G) ∈ P.U ↔ (h : G) ∈ P.U
    rw [conjMulEquiv_apply]
    exact mem_U_conj_iff P s (h : G)
  by_cases hU : h ∈ P.U.subgroupOf P.H0
  · have hx : quotMk P (conjMulEquiv P s h) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hmem.mpr hU)
    have hy : quotMk P h = 1 := (QuotientGroup.eq_one_iff _).mpr hU
    rw [hx, hy]
  · have hx : quotMk P (conjMulEquiv P s h) ≠ 1 := fun hh =>
      hU (hmem.mp ((QuotientGroup.eq_one_iff _).mp hh))
    have hy : quotMk P h ≠ 1 := fun hh => hU ((QuotientGroup.eq_one_iff _).mp hh)
    exact eq_of_ne_one_of_card_two h2 hx hy

/-- **Bender–Glauberman 1981, Lemma 1.7(iii), coefficient form.**

`(χ, (μ - λ₂·μ^s)^G)_G = (χ|_{H₀}, μ)_{H₀} - (χ|_{H₀}, λ₂·μ)_{H₀}`, where `λ₂` is the
inflation to `H₀` of a linear character of `H₀/U`.

By Frobenius reciprocity the left side is `(χ|_{H₀}, μ - λ₂·μ^s)_{H₀}`; additivity reduces it
to the statement that `(χ|_{H₀}, λ₂·μ^s) = (χ|_{H₀}, λ₂·μ)`.  Since `λ₂^s = λ₂` and `χ|_{H₀}`
is fixed by `ν ↦ ν^s`, both sides are `inner` of a common class function with an invariant
one, and `Work.BG.inner_conjByH_eq` finishes. -/
theorem lemma17_iii_coeff {G : Type} [Group G] [Finite G] [Fintype G] (P : Work.BG.Hyp12 G)
    [(P.U.subgroupOf P.H0).Normal] [Fintype ↥P.H0] [Invertible (Nat.card ↥P.H0 : ℂ)]
    [Invertible (Nat.card G : ℂ)]
    (h2 : Nat.card (Work.BG.quotGroup P) = 2) (s : ↥P.H)
    {lam2 : Work.BG.quotGroup P →* ℂˣ} (hlam2 : lam2 ≠ 1)
    (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (μ : OddOrder.RepresentationTheory.ClassFunction ↥P.H0 ℂ) :
    OddOrder.RepresentationTheory.ClassFunction.inner χ
        (OddOrder.RepresentationTheory.ClassFunction.induce P.H0
          (μ - OddOrder.RepresentationTheory.ClassFunction.compHom (Work.BG.quotMk P)
            (OddOrder.RepresentationTheory.linearClassFunction lam2) *
            Work.BG.conjByH P s μ)) =
      OddOrder.RepresentationTheory.ClassFunction.inner
          (OddOrder.RepresentationTheory.ClassFunction.restrict P.H0 χ) μ
        - OddOrder.RepresentationTheory.ClassFunction.inner
          (OddOrder.RepresentationTheory.ClassFunction.restrict P.H0 χ)
          (OddOrder.RepresentationTheory.ClassFunction.compHom (Work.BG.quotMk P)
            (OddOrder.RepresentationTheory.linearClassFunction lam2) * μ) := by
  classical
  rw [inner_induce_eq_inner_restrict_flip P.H0
        (μ - ClassFunction.compHom (quotMk P) (linearClassFunction lam2) * conjByH P s μ) χ]
  rw [ClassFunction.inner_sub_right]
  congr 1
  have hA : conjByH P s⁻¹ (ClassFunction.restrict P.H0 χ) = ClassFunction.restrict P.H0 χ :=
    conjByH_restrict_eq_self P s⁻¹ χ
  have hmul : ClassFunction.compHom (quotMk P) (linearClassFunction lam2) * conjByH P s μ =
      conjByH P s (ClassFunction.compHom (quotMk P) (linearClassFunction lam2) * μ) := by
    rw [show ClassFunction.compHom (quotMk P) (linearClassFunction lam2) = lambdaInf P lam2
          from rfl]
    rw [conjByH_map_mul, conjByH_lambdaInf_eq_self P h2 s lam2]
  rw [hmul]
  exact inner_conjByH_eq P s hA _

end Work.BG
