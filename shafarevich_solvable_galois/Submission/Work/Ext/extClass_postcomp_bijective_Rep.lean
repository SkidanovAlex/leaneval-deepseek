import Mathlib
import Submission.Work.SSGRoute.ExtOneAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Ext

open CategoryTheory

/-- The connecting map `δ = hS.extClass.postcomp X h` of
`0 → S.X₁ → S.X₂ → S.X₃ → 0` in the covariant long exact sequence
`Ext X S.X₁ n₀ → Ext X S.X₂ n₀ → Ext X S.X₃ n₀ → Ext X S.X₁ n₁ → Ext X S.X₂ n₁ → …`
(`n₀ + 1 = n₁`) is bijective as soon as the middle groups vanish at `n₀` and at `n₁`.

Injectivity uses exactness at `Ext X S.X₃ n₀` (the kernel of `δ` is the image of
`Ext X S.X₂ n₀ → Ext X S.X₃ n₀`); surjectivity uses exactness at `Ext X S.X₁ n₁`
(the image of `δ` is the kernel of `Ext X S.X₁ n₁ → Ext X S.X₂ n₁`). -/
lemma extClass_postcomp_bijective_Rep {G : Type} [Group G] (X : Rep.{0} SSGRoute.PTExt.Coeff G)
    (S : CategoryTheory.ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G)) (hS : S.ShortExact)
    {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    (h₀ : Subsingleton (CategoryTheory.Abelian.Ext X S.X₂ n₀))
    (h₁ : Subsingleton (CategoryTheory.Abelian.Ext X S.X₂ n₁)) :
    Function.Bijective (hS.extClass.postcomp X h) := by
  refine ⟨?_, ?_⟩
  · rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
    intro x hx
    rw [AddMonoidHom.mem_ker, Work.SSGRoute.ext_postcomp_apply hS.extClass X h x] at hx
    obtain ⟨x₂, hx₂⟩ := Abelian.Ext.covariant_sequence_exact₃ X hS x h hx
    have h2 : x₂ = 0 := h₀.elim x₂ 0
    rw [← hx₂, h2]
    exact Abelian.Ext.zero_comp _ _ _ _ _
  · intro x₁
    have hzero : x₁.comp (Abelian.Ext.mk₀ S.f) (add_zero n₁) = 0 := h₁.elim _ _
    obtain ⟨x₃, hx₃⟩ := Abelian.Ext.covariant_sequence_exact₁ X hS x₁ hzero h
    exact ⟨x₃, by rw [Work.SSGRoute.ext_postcomp_apply hS.extClass X h x₃, hx₃]⟩

end Work.Ext
