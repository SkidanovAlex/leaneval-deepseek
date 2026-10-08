import Mathlib
import Submission.Work.ThmG.Defs
import Submission.Work.CharCore.Main
import Submission.Work.Induction.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmG.trivial_on_Q1_of_orthogonal`

Let `f` be an irreducible complex character of a finite group `G` and let `H ≤ G`,
`Q₁ ≤ G`.  `Submission.Blueprint.excludingKernel H Q₁ = {χ ∈ Irr H | Q₁ ⊄ ker χ}` is the
set `𝒮` of Peterfalvi II App. XII.  If `Res_H^G f` is orthogonal to every member of `𝒮`,
then every irreducible constituent `χ` of `Res_H^G f` satisfies `Q₁ ∩ H ≤ ker χ`, hence
`f` is constant on `H ∩ Q₁`:

`Work.ThmG.trivial_on_Q1_of_orthogonal : ∀ x : ↥H, (x : G) ∈ Q₁ → f x = f 1`.

The proof is the classical one: `Res_H^G f` is a class function on `H`
(`Work.Induction.isClassFun_resFun`), so it expands in the orthonormal basis `Irr H`
(`Work.CharCore.classFun_eq_sum_irr`); the coefficient of `χ` is
`⟨Res_H^G f, χ⟩_H`, which vanishes for `χ ∈ 𝒮` by hypothesis and whose `χ` has
`χ x = χ 1` for `x ∈ H ∩ Q₁` when `χ ∉ 𝒮`.  Evaluating the expansion at `x` and at `1`
and subtracting gives `f x - f 1 = 0`.

**Instance remark.**  `Submission.Blueprint.excludingKernel` was elaborated with the
`Fintype` instance on `↥H` derived from `[Fintype G]` (`Subgroup.instFintypeSubtypeMemOfDecidablePred`),
whereas the statement of `trivial_on_Q1_of_orthogonal` carries an explicit `[Fintype ↥H]`;
since `Fintype ↥H` is a subsingleton these agree, and the lemma
`trivial_on_Q1_of_orthogonal_aux` (proved at the derived instance, matched by
`excludingKernel`) is transported to the explicit one at the end of the file.
-/

open Classical

namespace Work.ThmG

/-- `trivial_on_Q1_of_orthogonal`, with the `Fintype` instance on `↥H` left to instance
search (so that it agrees definitionally with the instance used inside
`Submission.Blueprint.excludingKernel`). -/
theorem trivial_on_Q1_of_orthogonal_aux {G : Type} [Group G] [Fintype G]
    {H Q₁ : Subgroup G}
    {f : G → ℂ} (hf : f ∈ Work.CharCore.Irr G)
    (h : ∀ χ ∈ Submission.Blueprint.excludingKernel H Q₁,
        Work.CharCore.cfInner (Work.Induction.resFun H f) χ = 0) :
    ∀ x : ↥H, (x : G) ∈ Q₁ → f x = f 1 := by
  -- `Res_H^G f` is a class function on `H`.
  have hcf : Work.CharCore.IsClassFun (Work.Induction.resFun H f) :=
    Work.Induction.isClassFun_resFun (Work.CharCore.isClassFun_of_mem_Irr hf)
  -- Expansion of `Res_H^G f` in the orthonormal basis `Irr H`.
  have hexp := Work.CharCore.classFun_eq_sum_irr (G := ↥H) hcf
  intro x hx
  have hxval : Work.Induction.resFun H f x = ∑ χ ∈ Work.CharCore.Irr ↥H,
      Work.CharCore.cfInner (Work.Induction.resFun H f) χ * χ x := by
    conv_lhs => rw [hexp]
    simp [Finset.sum_apply, smul_eq_mul]
  have h1val : Work.Induction.resFun H f 1 = ∑ χ ∈ Work.CharCore.Irr ↥H,
      Work.CharCore.cfInner (Work.Induction.resFun H f) χ * χ 1 := by
    conv_lhs => rw [hexp]
    simp [Finset.sum_apply, smul_eq_mul]
  -- Every summand of the difference vanishes: either the coefficient does (`χ ∈ 𝒮`),
  -- or `χ x = χ 1` (`χ ∉ 𝒮`, because `x ∈ H ∩ Q₁` and `χ` has `Q₁ ∩ H` in its kernel).
  have hdiff : Work.Induction.resFun H f x - Work.Induction.resFun H f 1 = 0 := by
    rw [hxval, h1val, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro χ hχ
    rw [← mul_sub]
    by_cases hker : χ ∈ Submission.Blueprint.excludingKernel H Q₁
    · rw [h χ hker, zero_mul]
    · have hxe : χ x = χ 1 := by
        by_contra hne
        exact hker (Finset.mem_filter.mpr ⟨hχ, x, hx, hne⟩)
      rw [hxe, sub_self, mul_zero]
  have hfin : Work.Induction.resFun H f x = Work.Induction.resFun H f 1 := sub_eq_zero.mp hdiff
  simpa using hfin

theorem trivial_on_Q1_of_orthogonal {G : Type} [Group G] [Fintype G]
    {H Q₁ : Subgroup G} [Fintype ↥H]
    {f : G → ℂ} (hf : f ∈ Work.CharCore.Irr G)
    (h : ∀ χ ∈ Submission.Blueprint.excludingKernel H Q₁,
        Work.CharCore.cfInner (Work.Induction.resFun H f) χ = 0) :
    ∀ x : ↥H, (x : G) ∈ Q₁ → f x = f 1 := by
  -- The `Fintype` instance on `↥H` is a subsingleton: the explicit one in the statement
  -- and the one derived from `[Fintype G]` (used inside `excludingKernel`) are equal.
  have hinst : Subgroup.instFintypeSubtypeMemOfDecidablePred (G := G) H =
      (inferInstanceAs (Fintype ↥H)) := Subsingleton.elim _ _
  refine trivial_on_Q1_of_orthogonal_aux (G := G) (H := H) (Q₁ := Q₁) hf ?_
  intro χ hχ
  have h1 := h χ hχ
  -- `Work.CharCore.cfInner` only depends on `Fintype.card` (and `Finset.univ`) through the
  -- `Fintype` instance, so transporting the instance along `hinst` identifies the two
  -- inner products.
  rw [show @Work.CharCore.cfInner ↥H (Subgroup.instFintypeSubtypeMemOfDecidablePred (G := G) H)
        (Work.Induction.resFun H f) χ
      = @Work.CharCore.cfInner ↥H (inferInstanceAs (Fintype ↥H))
        (Work.Induction.resFun H f) χ from by rw [hinst]]
  exact h1

end Work.ThmG
