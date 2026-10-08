import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.CharCore.Main
import Submission.Work.Induction.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausTwoGroup

/-!
# An irreducible constituent of `Ind_Q^G ζ₁` is exceptional

Let `χ₀` attach to every character `ζ` of `Q` a (candidate exceptional) class function
`χ₀ ζ` on `G`, and suppose every *non-exceptional* irreducible character of `G` — an
irreducible `φ` that is different from all `χ₀ ζ` with `1 ≠ ζ ∈ Irr Q` — is constant on
`Q ∖ 1` (`hχconst`, Feit 1960, Corollary 2.4).  If the induced character `Ind_Q^G ζ₁` is
*not* constant on `Q ∖ 1` (`hnonconst`), then some exceptional character `χ₀ κ`
(`κ ∈ Irr Q`, `κ ≠ 1`) is a genuine constituent of `Ind_Q^G ζ₁`.

The proof is the contrapositive.  `Ind_Q^G ζ₁` is a class function, hence
`Ind_Q^G ζ₁ = ∑_{χ ∈ Irr G} ⟨Ind ζ₁, χ⟩ • χ` (`Work.CharCore.classFun_eq_sum_irr`).  If no
exceptional character is a constituent, then for every `χ` occurring with non-zero coefficient
one has `cfInner (χ₀ ζ) (Ind ζ₁) = 0` for all `1 ≠ ζ ∈ Irr Q`; by conjugate symmetry of
`cfInner` this gives `cfInner (Ind ζ₁) χ = 0` whenever `χ = χ₀ ζ`, so `χ` is not of the form
`χ₀ ζ` and `hχconst` makes it constant on `Q ∖ 1`.  A `ℂ`-linear combination of functions
constant on `Q ∖ 1` is constant on `Q ∖ 1`, contradicting `hnonconst`.
-/

theorem exists_exceptional_constituent {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    {H Q : Subgroup G} [Fintype ↥Q] {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    {ζ₁ : ↥Q → ℂ} (hζ : ζ₁ ∈ Work.CharCore.Irr ↥Q) (hζ1 : ζ₁ ≠ 1) (hlin : ζ₁ 1 = 1)
    {χ₀ : (↥Q → ℂ) → G → ℂ}
    (hχconst : ∀ φ ∈ Work.CharCore.Irr G, (∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → φ ≠ χ₀ ζ) →
      ∀ y : G, y ∈ Q → y ≠ 1 → ∀ y' : G, y' ∈ Q → y' ≠ 1 → φ y = φ y')
    (hnonconst : ∃ y y' : ↥Q, y ≠ 1 ∧ y' ≠ 1 ∧
      Work.Induction.indFun Q ζ₁ (y : G) ≠ Work.Induction.indFun Q ζ₁ (y' : G)) :
    ∃ κ ∈ Work.CharCore.Irr ↥Q, κ ≠ 1 ∧
      Work.CharCore.cfInner (χ₀ κ) (Work.Induction.indFun Q ζ₁) ≠ 0 := by
  by_contra hcon
  -- `hcon` : no exceptional character is orthogonal-nonzero against `Ind_Q^G ζ₁`.
  push_neg at hcon
  set f : G → ℂ := Work.Induction.indFun Q ζ₁ with hf_def
  -- `f` is a class function, hence the sum of its `Irr G`-components.
  have hfclass : Work.CharCore.IsClassFun f := Work.Induction.isClassFun_indFun Q ζ₁
  have hdecomp : f = ∑ χ ∈ Work.CharCore.Irr G, (Work.CharCore.cfInner f χ) • χ :=
    Work.CharCore.classFun_eq_sum_irr hfclass
  -- Pointwise form of the expansion.
  have hval : ∀ y : G, f y = ∑ χ ∈ Work.CharCore.Irr G, Work.CharCore.cfInner f χ * χ y := by
    intro y
    conv_lhs => rw [hdecomp]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  -- Under the contradiction hypothesis, `f` is constant on `Q ∖ 1`.
  have hconst : ∀ y y' : G, y ∈ Q → y ≠ 1 → y' ∈ Q → y' ≠ 1 → f y = f y' := by
    intro y y' hy hy1 hy' hy'1
    rw [hval y, hval y']
    refine Finset.sum_congr rfl fun χ hχ => ?_
    by_cases hc : Work.CharCore.cfInner f χ = 0
    · rw [hc, zero_mul, zero_mul]
    · -- `χ` is not exceptional, so `hχconst` makes it constant on `Q ∖ 1`.
      have hne : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → χ ≠ χ₀ ζ := by
        intro ζ hζ' hζ1' heq
        apply hc
        rw [heq, Work.CharCore.cfInner_conj_symm, hcon ζ hζ' hζ1', map_zero]
      rw [hχconst χ hχ hne y hy hy1 y' hy' hy'1]
  -- Contradiction with the non-constancy of `Ind_Q^G ζ₁` on `Q ∖ 1`.
  obtain ⟨y, y', hy1, hy'1, hne⟩ := hnonconst
  have hy1' : (y : G) ≠ 1 := fun hh => hy1 (Subtype.ext hh)
  have hy'1' : (y' : G) ≠ 1 := fun hh => hy'1 (Subtype.ext hh)
  exact hne (hconst (y : G) (y' : G) y.2 hy1' y'.2 hy'1')

end Work.ZassenhausTwoGroup
