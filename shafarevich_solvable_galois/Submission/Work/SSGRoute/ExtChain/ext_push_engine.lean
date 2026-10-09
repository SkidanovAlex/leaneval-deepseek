import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_corestriction
import Submission.Work.SSGRoute.ExtOneAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `Ext`-theoretic engine of `(PUSH)`: coefficients with uniquely `p`-divisible quotient

This file isolates the *formal* half of the level-change input `(PUSH)` that the lead's
`_lead_design/flags_0030/NOTE.md` §2/§4 identifies as one of the two inputs of
`ExtChain.himgIdelesInput_fin` and of the archimedean `SSGStage.archimedeanLocalDictionary` at
`p = 2`:

> For a finite `p`-torsion `D`-module `N` and every `i`, the map
> `Ext^i_D(N, (K^h)ˣ) → Ext^i_D(N, K_qˣ)` is an isomorphism.

Here `(K^h)ˣ ↪ K_qˣ` is a sub-representation whose quotient `Q = K_qˣ/(K^h)ˣ` is *uniquely*
`p`-divisible (that is the arithmetic input, not formalised here).

## The two formal statements

* `subsingleton_ext_of_ptorsion_uniqueDivisible` — **the engine**.  If `N` is annihilated by `p`
  (`p • x = 0` for all `x`) and multiplication by `p` is a bijection of `Q`, then every
  `Ext^i_G(N, Q)` is a subsingleton.  Proof: `Ext^i(N,Q)` is killed by `p` (functoriality of
  `Ext^i(-,Q)` applied to the zero endomorphism `p • 𝟙 N = 0`) and `p`-divisible (functoriality
  of `Ext^i(N,-)` applied to the automorphism `p • 𝟙 Q`); a group killed by `p` and `p`-divisible
  is trivial.  No number theory, no first-variable hypotheses, no finiteness.

* `postcomp_mk₀_bijective_of_subsingleton` / `..._of_ptorsion_uniqueDivisible` — **the push**.
  For a short exact sequence `S : 0 → U → V → Q → 0` in `Rep ℤ G`, the coefficient push
  `Ext^i_G(N,U) → Ext^i_G(N,V)` (the additive map `postcomp (mk₀ S.f) N _`) is bijective as soon as
  `Ext^{i-1}_G(N,Q)` and `Ext^i_G(N,Q)` are subsingletons.  The proof uses Mathlib's covariant long
  exact sequence `Abelian.Ext.covariant_sequence_exact₁/₂`.

Combining the two, `..._of_ptorsion_uniqueDivisible` is exactly `(PUSH)` once the quotient
`S.X₃` is identified with `K_qˣ/(K^h)ˣ` and proved uniquely `p`-divisible.

Everything here is `sorry`-free and uses only `propext, Classical.choice, Quot.sound`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.ExtChain

open CategoryTheory CategoryTheory.Limits

open SSGRoute.PTExt

noncomputable section

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

variable {G : Type} [Group G]

/-- `ℕ`-linearity of `Abelian.Ext.comp` in its *second* argument (the companion of
`Work.SSGRoute.nsmul_comp_aux`).  Local copy, so that this module depends on no other `ExtChain`
file. -/
private lemma comp_nsmul_ext {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y Z : C} {a b c : ℕ} (n : ℕ) (α : Abelian.Ext X Y a) (β : Abelian.Ext Y Z b)
    (h : a + b = c) : α.comp (n • β) h = n • (α.comp β h) := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, Abelian.Ext.comp_zero]
  | succ k ih => rw [succ_nsmul', succ_nsmul', Abelian.Ext.comp_add, ih]

/-- **The engine of `(PUSH)`.**  If the `G`-module `N` is annihilated by `p` and multiplication by
`p` on the `G`-module `Q` is a bijection, then `Ext^i_G(N, Q)` is a subsingleton, for every `i`.

The two halves are:
* `Ext^i(N,Q)` is killed by `p`: the endomorphism `p • 𝟙 N` is zero, hence so is its image under
  the (additive) functor `Ext^i(-,Q)`, which is multiplication by `p`;
* `Ext^i(N,Q)` is `p`-divisible: `p • 𝟙 Q` is an isomorphism, hence so is its image under
  `Ext^i(N,-)`, which is again multiplication by `p`. -/
theorem subsingleton_ext_of_ptorsion_uniqueDivisible (p : ℕ) (N Q : Rep.{0} Coeff G) (i : ℕ)
    (hN : ∀ x : N.V, p • x = 0)
    (hQ : Function.Bijective (fun q : Q.V => p • q)) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0} N Q i) := by
  have hmorph : ∀ (A : Rep.{0} Coeff G) (a : A.V),
      (Rep.Hom.hom (p • (𝟙 A) : A ⟶ A)) a = p • a := by
    intro A a; rw [Rep.nsmul_hom, Rep.hom_id]; rfl
  haveI : Mono (p • (𝟙 Q)) := by
    rw [Rep.mono_iff_injective]
    intro a b hab
    rw [hmorph Q a, hmorph Q b] at hab
    exact hQ.1 hab
  haveI : Epi (p • (𝟙 Q)) := by
    rw [Rep.epi_iff_surjective]
    intro a
    obtain ⟨b, hb⟩ := hQ.2 a
    exact ⟨b, by rw [hmorph Q b]; exact hb⟩
  haveI : IsIso (p • (𝟙 Q)) := isIso_of_mono_of_epi _
  have hyN : ∀ y : CategoryTheory.Abelian.Ext.{0} N Q i,
      p • y = (Abelian.Ext.mk₀ (p • (𝟙 N))).comp y (zero_add i) := by
    intro y
    rw [Work.SSGRoute.mk₀_nsmul_aux p (𝟙 N),
      Work.SSGRoute.nsmul_comp_aux p (Abelian.Ext.mk₀ (𝟙 N)) y (zero_add i),
      Abelian.Ext.mk₀_id_comp]
  have hyQ : ∀ y : CategoryTheory.Abelian.Ext.{0} N Q i,
      p • y = y.comp (Abelian.Ext.mk₀ (p • (𝟙 Q))) (add_zero i) := by
    intro y
    rw [Work.SSGRoute.mk₀_nsmul_aux p (𝟙 Q),
      comp_nsmul_ext p y (Abelian.Ext.mk₀ (𝟙 Q)) (add_zero i)]
    rw [Abelian.Ext.comp_mk₀_id]
  have hN0 : p • (𝟙 N) = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change (Rep.Hom.hom (p • (𝟙 N) : N ⟶ N)) x = (Rep.Hom.hom (0 : N ⟶ N)) x
    rw [hmorph N x, hN x]
    simp
  have hkill : ∀ y : CategoryTheory.Abelian.Ext.{0} N Q i, p • y = 0 := by
    intro y
    rw [hyN y, hN0, Abelian.Ext.mk₀_zero]
    exact Abelian.Ext.zero_comp N 0 y i (zero_add i)
  have hdiv : ∀ y : CategoryTheory.Abelian.Ext.{0} N Q i, ∃ y', p • y' = y := by
    intro y
    refine ⟨y.comp (Abelian.Ext.mk₀ (inv (p • (𝟙 Q)))) (add_zero i), ?_⟩
    rw [show p • (y.comp (Abelian.Ext.mk₀ (inv (p • (𝟙 Q)))) (add_zero i))
        = (p • y).comp (Abelian.Ext.mk₀ (inv (p • (𝟙 Q)))) (add_zero i) from
          (Work.SSGRoute.nsmul_comp_aux p y (Abelian.Ext.mk₀ (inv (p • (𝟙 Q)))) (add_zero i)).symm]
    rw [hyQ y]
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero y (Abelian.Ext.mk₀ (p • (𝟙 Q)))
      (Abelian.Ext.mk₀ (inv (p • (𝟙 Q)))) (add_zero i)]
    rw [Abelian.Ext.mk₀_comp_mk₀]
    rw [IsIso.hom_inv_id, Abelian.Ext.comp_mk₀_id]
  refine ⟨fun y z => ?_⟩
  obtain ⟨y', hy'⟩ := hdiv y
  obtain ⟨z', hz'⟩ := hdiv z
  rw [← hy', ← hz', hkill y', hkill z']

/-- **`(PUSH)`, abstract form.**  For a short exact sequence `S : 0 → S.X₁ → S.X₂ → S.X₃ → 0` whose
cokernel `S.X₃` has `Ext^{n₀}` and `Ext^{n₀+1}` vanishing against `N`, the coefficient push
`Ext^{n₀+1}_G(N, S.X₁) → Ext^{n₀+1}_G(N, S.X₂)` is a bijection.

Both halves are Mathlib's covariant long exact sequence: surjectivity is
`Abelian.Ext.covariant_sequence_exact₂` (any `x₂` is killed by `S.g` because the target is a
subsingleton), and injectivity is `Abelian.Ext.covariant_sequence_exact₁` (an `x₁` killed by `S.f`
comes from the connecting map, whose source is a subsingleton). -/
theorem postcomp_mk₀_bijective_of_subsingleton (N : Rep.{0} Coeff G)
    {S : ShortComplex (Rep.{0} Coeff G)} (hS : S.ShortExact) (n₀ : ℕ)
    (h0 : Subsingleton (CategoryTheory.Abelian.Ext.{0} N S.X₃ n₀))
    (h1 : Subsingleton (CategoryTheory.Abelian.Ext.{0} N S.X₃ (n₀ + 1))) :
    Function.Bijective ((Abelian.Ext.mk₀ S.f).postcomp N (add_zero (n₀ + 1)) :
      CategoryTheory.Abelian.Ext.{0} N S.X₁ (n₀ + 1) →+
        CategoryTheory.Abelian.Ext.{0} N S.X₂ (n₀ + 1)) := by
  refine ⟨fun x y hxy => ?_, fun x₂ => ?_⟩
  · have h0' : ((Abelian.Ext.mk₀ S.f).postcomp N (add_zero (n₀ + 1))) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have h0'' : (x - y).comp (Abelian.Ext.mk₀ S.f) (add_zero (n₀ + 1)) = 0 := h0'
    obtain ⟨x₃, hx₃⟩ := Abelian.Ext.covariant_sequence_exact₁ N hS (x - y) h0'' (n₀ := n₀) rfl
    have hx30 : x₃ = 0 := Subsingleton.elim _ _
    rw [hx30] at hx₃
    have hxy0 : (x - y) = 0 := by
      rw [← hx₃]
      exact Abelian.Ext.zero_comp N n₀ hS.extClass (n₀ + 1) rfl
    exact sub_eq_zero.mp hxy0
  · have hnull : x₂.comp (Abelian.Ext.mk₀ S.g) (add_zero (n₀ + 1)) = 0 := Subsingleton.elim _ _
    obtain ⟨x₁, hx₁⟩ := Abelian.Ext.covariant_sequence_exact₂ N hS x₂ hnull
    exact ⟨x₁, hx₁⟩

/-- **`(PUSH)`, abstract form, with the arithmetic input supplied as `p`-torsion and unique
`p`-divisibility.**  For `N` annihilated by `p` and a short exact sequence
`S : 0 → S.X₁ → S.X₂ → S.X₃ → 0` whose cokernel is uniquely `p`-divisible, the push
`Ext^{n₀+1}_G(N, S.X₁) → Ext^{n₀+1}_G(N, S.X₂)` is a bijection.

This is the exact shape of the lead's `(PUSH)` (`E1aClean.ext_push_completion`): instantiate at
`S : 0 → (K^h)ˣ → K_qˣ → Q → 0`, `N` the `p`-torsion syzygy, and `n₀ + 1 = i`. -/
theorem postcomp_mk₀_bijective_of_ptorsion_uniqueDivisible (p : ℕ) (N : Rep.{0} Coeff G)
    (hN : ∀ x : N.V, p • x = 0)
    {S : ShortComplex (Rep.{0} Coeff G)} (hS : S.ShortExact) (n₀ : ℕ)
    (hQ : Function.Bijective (fun q : S.X₃.V => p • q)) :
    Function.Bijective ((Abelian.Ext.mk₀ S.f).postcomp N (add_zero (n₀ + 1)) :
      CategoryTheory.Abelian.Ext.{0} N S.X₁ (n₀ + 1) →+
        CategoryTheory.Abelian.Ext.{0} N S.X₂ (n₀ + 1)) :=
  postcomp_mk₀_bijective_of_subsingleton N hS n₀
    (subsingleton_ext_of_ptorsion_uniqueDivisible p N S.X₃ n₀ hN hQ)
    (subsingleton_ext_of_ptorsion_uniqueDivisible p N S.X₃ (n₀ + 1) hN hQ)

end

end Work.SSGRoute.ExtChain
