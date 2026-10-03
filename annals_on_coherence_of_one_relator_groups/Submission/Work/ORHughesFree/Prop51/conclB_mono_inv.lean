import Mathlib
import Submission.Work.ORHughesFree.Prop51.ratOp_aux
import Submission.Work.ORHughesFree.Prop51.ConclB
import Submission.Work.ORHughesFree.Prop51.ratOp_eq_laurentEmbed_inv
import Submission.Work.ORHughesFree.SkewLaurentSeries.isDivisionRing_skewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeries.VanishesBelow
import Submission.Work.ORHughesFree.SkewLaurentSeries.inv_coeff

namespace Work.ORHughesFree.Prop51

/-- **The `⋄`-step of [JZLA20, Proposition 5.1] for a monomial.**  Let `x = laurentEmbed (a·tᵐ)`
for a nonzero `a ∈ D_{N,P}` (so `x = a·Φ(tᵐ)` is a monomial of `D_{N,P}((t;τ)) ⊆ P`).  Then the
`⋄`-inverse of `x` inside `D_{H,P}` satisfies the conclusion `ConclB` with the bound
`exp (exp (Tree_H a))`.

Since `a` is a unit of `D_{N,P}` (hypothesis `hAunit`; in the intended instantiation this comes
from `Prop51Inv` and `Prop51Data.DN_inv_closed`),
and the inverse of the monomial `a·tᵐ` in `D_{N,P}((t;τ))` is again a monomial, namely
`b·t^{-m}` with `b = (-m) • a⁻¹` (`SkewLaurentSeries.mono_mul`: the skew factor `m • b` must equal
`a⁻¹`, which for `b = (-m) • a⁻¹` is exactly `m • ((-m) • a⁻¹) = a⁻¹`).  Hence, by
`ratOp_eq_laurentEmbed_inv`, the `⋄`-inverse of `x` in `D_{H,P}` is `laurentEmbed` of that
monomial, which is the required witness for `ConclB`:

* the coefficients of `b·t^{-m}` are `0` away from `-m`, and `Tree_H 0 = 0 ≤ exp (exp (Tree_H a))`;
* at `-m` the coefficient is `b = (-m) • a⁻¹`, whose complexity equals that of `a⁻¹`
  (`treeH_conj_coeffToP`), which is at most `exp (exp (Tree_H a))` because `a` and `a⁻¹` are
  mutually inverse elements of `D_{H,P}` (`treeH_inv_le`);
* the "uniqueness" clause is vacuous, since a monomial has at most one nonzero coefficient. -/
theorem conclB_mono_inv {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Work.ORHughesFree.Prop51Data Γ P DN)
    (m : ℤ) {A : ↥DN} (hA : A ≠ 0) (hAunit : IsUnit A) {x : P} (hx : x ∈ d.DH)
    (hf : d.laurentEmbed (Work.ORHughesFree.SkewLaurentSeries.mono m A) = x) :
    Work.ORHughesFree.Prop51.ConclB d ((d.rDH.ratOp ⟨x, hx⟩ : ↥d.DH) : P)
      (Work.ORHughesFree.Tree.exp (Work.ORHughesFree.Tree.exp (d.treeH (d.coeffToP A)))) := by
  -- `A` is a unit of `D_{N,P}` (in the intended instantiation this comes from `Prop51Inv` and
  -- `Prop51Data.DN_inv_closed`; see the README, gap item 10).
  obtain ⟨U, hU⟩ := hAunit
  have hA1 : A * ((U⁻¹ : (↥DN)ˣ) : ↥DN) = 1 := by rw [← hU]; exact Units.mul_inv U
  have h1A : ((U⁻¹ : (↥DN)ˣ) : ↥DN) * A = 1 := by rw [← hU]; exact Units.inv_mul U
  have hcoeff : ∀ (a b : ↥DN), d.coeffToP (a * b) = d.coeffToP a * d.coeffToP b :=
    fun a b => rfl
  have hA1' : d.coeffToP A * d.coeffToP ((U⁻¹ : (↥DN)ˣ) : ↥DN) = 1 := by
    rw [← hcoeff, hA1]; rfl
  have h1A' : d.coeffToP ((U⁻¹ : (↥DN)ˣ) : ↥DN) * d.coeffToP A = 1 := by
    rw [← hcoeff, h1A]; rfl
  -- The inverse monomial: `B·t^{-m}` with `B = (-m) • A⁻¹`.
  set B : ↥DN := (Multiplicative.ofAdd (-m)) • ((U⁻¹ : (↥DN)ˣ) : ↥DN) with hBdef
  have hmB : (Multiplicative.ofAdd m) • B = ((U⁻¹ : (↥DN)ˣ) : ↥DN) := by
    rw [hBdef, smul_smul, ← ofAdd_add, show m + -m = 0 from by ring, ofAdd_zero, one_smul]
  -- `mono m A` and `mono (-m) B` are mutually inverse.
  have hfu : SkewLaurentSeries.mono m A * SkewLaurentSeries.mono (-m) B = 1 := by
    rw [SkewLaurentSeries.mono_mul, show m + -m = 0 from by ring, hmB, hA1]
    exact SkewLaurentSeries.mono_zero_one
  have huf : SkewLaurentSeries.mono (-m) B * SkewLaurentSeries.mono m A = 1 := by
    rw [SkewLaurentSeries.mono_mul, show -m + m = 0 from by ring]
    have hB1 : B * ((Multiplicative.ofAdd (-m)) • A) = 1 := by
      rw [hBdef, ← MulSemiringAction.smul_mul, h1A, MulSemiringAction.smul_one]
    rw [hB1]
    exact SkewLaurentSeries.mono_zero_one
  -- Hence the `⋄`-inverse of `x` is `laurentEmbed` of the inverse monomial.
  have hrat : ((d.rDH.ratOp ⟨x, hx⟩ : ↥d.DH) : P) =
      d.laurentEmbed (SkewLaurentSeries.mono (-m) B) :=
    ratOp_eq_laurentEmbed_inv d hx hf hfu huf
  refine ⟨SkewLaurentSeries.mono (-m) B, hrat.symm, ?_, ?_⟩
  · -- The complexity bound on the coefficients.
    intro k
    rw [SkewLaurentSeries.mono_apply]
    by_cases hk : k = -m
    · rw [if_pos hk, hBdef, treeH_conj_coeffToP]
      exact treeH_inv_le d (d.coeffToP_mem A) (d.coeffToP_mem _) hA1' h1A'
    · rw [if_neg hk]
      have hc0 : d.coeffToP (0 : ↥DN) = 0 := rfl
      rw [hc0, treeH_zero d]
      exact Tree.le_zero _
  · -- The uniqueness clause: `mono (-m) B` has a single possibly nonzero coefficient.
    intro k hk j hj
    have hk' : k = -m := by
      by_contra hkne
      have h0 : (SkewLaurentSeries.mono (-m) B).1 k = 0 := by
        rw [SkewLaurentSeries.mono_apply, if_neg hkne]
      rw [h0] at hk
      have hc0 : d.coeffToP (0 : ↥DN) = 0 := rfl
      rw [hc0, treeH_zero d] at hk
      exact Tree.exp_ne_zero (Tree.exp (d.treeH (d.coeffToP A))) hk.symm
    rw [SkewLaurentSeries.mono_apply, if_neg (fun h => hj (h.trans hk'.symm))]

end Work.ORHughesFree.Prop51
