import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.E7cOmega.intSES
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E7cOmega

open CategoryTheory SSGRoute.PTExt

/-- **Nonvanishing of the Yoneda pairing with the class of `0 → ℤ --p--> ℤ → ℤ/p → 0`.**

Let `h ∈ H¹(G, ℤ/p) = Ext¹_G(ℤ, ℤ/p)` and let
`φ₀ = (intSES p).extClass ∈ Ext¹_G(ℤ/p, ℤ)` be the class of the trivial-coefficient sequence
`0 → ℤ --p--> ℤ --π--> ℤ/p → 0`.  If `H¹(G, ℤ) = Ext¹_G(ℤ, ℤ)` is trivial (the hypothesis `hsub`),
then `h ≠ 0` forces `h ∘ φ₀ ∈ H²(G, ℤ) = Ext²_G(ℤ, ℤ)` to be nonzero.

This is exactly the injectivity of the connecting map `δ : H¹(G, ℤ/p) → H²(G, ℤ)` of the long exact
sequence of `intSES`: the long exact sequence in the second variable gives
`… → Ext¹_G(ℤ, ℤ) --π_*--> Ext¹_G(ℤ, ℤ/p) --δ--> Ext²_G(ℤ, ℤ) → …`,
`δ = (·.comp hS.extClass)`, and its kernel is the image of `Ext¹_G(ℤ, ℤ)`, which vanishes by
`hsub`.  Formally we use `Ext.covariant_sequence_exact₃`: if the pairing vanished, `h` would be the
image under `Ext.mk₀ π` of some `x₂ ∈ Ext¹_G(ℤ, ℤ)`, and `x₂ = 0` by `hsub`. -/
theorem comp_intSES_extClass_ne_zero (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (hsub : Subsingleton (SSGRoute.PTExt.extH (SSGRoute.PTExt.unitRep G) 1))
    (h : SSGRoute.PTExt.extH (Rep.trivial SSGRoute.PTExt.Coeff G (ZMod p)) 1) (hne : h ≠ 0) :
    h.comp (CategoryTheory.ShortComplex.ShortExact.extClass
        (Work.SSGRoute.E7cOmega.intSES_shortExact (G := G) p (Fact.out : p.Prime).ne_zero))
      (by norm_num : 1 + 1 = 2) ≠ 0 := by
  intro hzero
  -- `hS` is the short exactness of the coefficient sequence `0 → ℤ → ℤ → ℤ/p → 0`.
  have hS : (intSES (G := G) p).ShortExact :=
    intSES_shortExact (G := G) p (Fact.out : p.Prime).ne_zero
  -- Exactness at `Ext¹_G(ℤ, ℤ/p)`: if `h ∘ φ₀ = 0` then `h = x₂.comp (mk₀ π)` for some
  -- `x₂ ∈ Ext¹_G(ℤ, ℤ)` (here `π = hS.g` is the reduction `ℤ → ℤ/p`).
  obtain ⟨x₂, hx₂⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₃
    (unitRep G) hS h (n₁ := 2) (by norm_num) hzero
  -- `Ext¹_G(ℤ, ℤ)` is a subsingleton by hypothesis, so `x₂ = 0`.
  have hx2zero : x₂ = 0 := @Subsingleton.elim _ hsub x₂ 0
  rw [hx2zero, CategoryTheory.Abelian.Ext.zero_comp] at hx₂
  exact hne hx₂.symm

end Work.SSGRoute.E7cOmega
