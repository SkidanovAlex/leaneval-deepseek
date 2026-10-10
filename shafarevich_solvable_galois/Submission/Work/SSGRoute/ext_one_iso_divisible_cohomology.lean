import Mathlib.RepresentationTheory.Coinduced
import Mathlib.Algebra.Module.Injective
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ExtOneAux
import Submission.Work.SSGRoute.ext_one_homRepFree_subsingleton
import Submission.Work.SSGRoute.freeLift_id_epi
import Submission.Work.SSGRoute.homRepFree_coind_iso
import Submission.Work.SSGRoute.homRepShortComplex_shortExact
import Submission.Work.SSGRoute.moduleInjective_coeff_of_divisible
import Submission.Work.SSGRoute.unitHomEquiv_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {G : Type} [Group G]

/-! ## The `unitRep`-`Hom` identification and the `Ext⁰`-transport

The proof of the main theorem compares two long exact sequences through the additive equivalence
`Ext⁰_G(ℤ, Hom_ℤ(X,N)) ≃+ Ext⁰_G(X,N)` obtained by composing evaluation at `1` with
`Ext.addEquiv₀`.  The naturality of this comparison with respect to the precomposition morphism
`homRepPre u` is what the lemmas below record. -/

/-- The identification `(unitRep G ⟶ Hom_ℤ(X,N)) ≃+ (X ⟶ N)`, chosen from `unitHomEquiv_exists`
(it is evaluation at `1`). -/
def unitHomEquiv (X N : Rep.{0} Coeff G) :
    (unitRep G ⟶ homRep X N) ≃+ (X ⟶ N) :=
  Classical.choose (unitHomEquiv_exists G X N)

lemma unitHomEquiv_apply (X N : Rep.{0} Coeff G) (φ : unitRep G ⟶ homRep X N) (x : X.V) :
    (unitHomEquiv X N φ).hom x =
      (show X.V →ₗ[Coeff] N.V from φ.hom (1 : Coeff)) x :=
  Classical.choose_spec (unitHomEquiv_exists G X N) φ x

/-- Naturality of `unitHomEquiv`: it is determined by evaluation at `1`. -/
lemma unitHomEquiv_natural (X X' N : Rep.{0} Coeff G) (u : X' ⟶ X)
    (φ : unitRep G ⟶ homRep X N) :
    unitHomEquiv X' N (φ ≫ homRepPre X X' N u) = u ≫ unitHomEquiv X N φ := by
  apply Rep.hom_ext
  apply DFunLike.coe_injective
  funext x
  rw [unitHomEquiv_apply X' N (φ ≫ homRepPre X X' N u) x,
      ConcreteCategory.comp_apply φ (homRepPre X X' N u) (1 : Coeff),
      homRepPre_apply X X' N u (φ.hom (1 : Coeff)) x,
      ConcreteCategory.comp_apply u (unitHomEquiv X N φ) x,
      unitHomEquiv_apply X N φ (u.hom x)]

/-- The identification `Ext⁰_G(ℤ, Hom_ℤ(X,N)) ≃+ Ext⁰_G(X,N)`. -/
def unitHomExtEquiv (X N : Rep.{0} Coeff G) :
    Abelian.Ext (unitRep G) (homRep X N) 0 ≃+ Abelian.Ext X N 0 :=
  (Abelian.Ext.addEquiv₀ (X := unitRep G) (Y := homRep X N)).trans
    ((unitHomEquiv X N).trans (Abelian.Ext.addEquiv₀ (X := X) (Y := N)).symm)

lemma unitHomExtEquiv_apply (X N : Rep.{0} Coeff G)
    (b : Abelian.Ext (unitRep G) (homRep X N) 0) :
    unitHomExtEquiv X N b
      = Abelian.Ext.mk₀ (unitHomEquiv X N (Abelian.Ext.addEquiv₀ b)) := by
  simp only [unitHomExtEquiv, AddEquiv.trans_apply, Abelian.Ext.addEquiv₀_symm_apply]

lemma unitHomExtEquiv_symm_mk₀ (X N : Rep.{0} Coeff G) (w : X ⟶ N) :
    (unitHomExtEquiv X N).symm (Abelian.Ext.mk₀ w)
      = Abelian.Ext.mk₀ ((unitHomEquiv X N).symm w) := by
  apply (unitHomExtEquiv X N).injective
  rw [AddEquiv.apply_symm_apply, unitHomExtEquiv_apply, ext_addEquiv₀_mk₀,
    AddEquiv.apply_symm_apply]

/-- `η.symm ∘ precomp = postcomp ∘ η.symm`: the naturality of `unitHomExtEquiv` in the first
variable of the internal hom. -/
lemma unitHomExtEquiv_symm_precomp (X X' N : Rep.{0} Coeff G) (u : X' ⟶ X)
    (z : Abelian.Ext X N 0) :
    (unitHomExtEquiv X' N).symm ((Abelian.Ext.mk₀ u).precomp N (zero_add 0) z)
      = (Abelian.Ext.mk₀ (homRepPre X X' N u)).postcomp (unitRep G) (add_zero 0)
          ((unitHomExtEquiv X N).symm z) := by
  rw [ext_eq_mk₀_addEquiv₀ ((Abelian.Ext.mk₀ u).precomp N (zero_add 0) z),
      ext_addEquiv₀_precomp u z]
  rw [unitHomExtEquiv_symm_mk₀ X' N (u ≫ Abelian.Ext.addEquiv₀ z),
      show (unitHomExtEquiv X N).symm z
        = Abelian.Ext.mk₀ ((unitHomEquiv X N).symm (Abelian.Ext.addEquiv₀ z)) from by
        conv_lhs => rw [ext_eq_mk₀_addEquiv₀ z]
        exact unitHomExtEquiv_symm_mk₀ X N (Abelian.Ext.addEquiv₀ z)]
  rw [ext_postcomp_apply, Abelian.Ext.mk₀_comp_mk₀]
  congr 1
  conv_lhs =>
    rw [show Abelian.Ext.addEquiv₀ z
          = unitHomEquiv X N ((unitHomEquiv X N).symm (Abelian.Ext.addEquiv₀ z)) from
        (AddEquiv.apply_symm_apply (unitHomEquiv X N) (Abelian.Ext.addEquiv₀ z)).symm]
  rw [← unitHomEquiv_natural X X' N u ((unitHomEquiv X N).symm (Abelian.Ext.addEquiv₀ z)),
    AddEquiv.symm_apply_apply]

end

/-- **The `Ext¹ ↔ H¹` dictionary with divisible coefficients.**  For a group `G`, an arbitrary
`G`-module `M` and a `G`-module `N` whose underlying abelian group is divisible
(`hdiv : ∀ n > 0, ∀ y, ∃ x, n • x = y`, i.e. `N.V` is injective as a `ℤ`-module), there is an
additive equivalence `Ext¹_G(M,N) ≃+ Ext¹_G(ℤ, Hom_ℤ(M,N))`, the right side being
`H¹(G, Hom_ℤ(M,N))`, and `Hom_ℤ(M,N) = homRep M N` carries the conjugation action
`(g·f)(x) = g · f (g⁻¹ · x)`.

**Route (needs no spectral sequence).**  Fix a surjection `F = ℤ[G]^r ↠ M` from a free module and
put `R = ker`; `F` is projective, so the long exact sequence of `0 → R → F → M → 0` under
`Hom_G(-,N)` gives `Ext¹_G(M,N) ≅ coker(Hom_G(F,N) → Hom_G(R,N))`.  Divisibility of `N`
makes `Hom_ℤ(-,N)` an exact functor (a `ℤ`-module is injective iff divisible), so
`0 → Hom_ℤ(M,N) → Hom_ℤ(F,N) → Hom_ℤ(R,N) → 0` is a *short* exact sequence; its long exact
sequence in group cohomology starts
`Hom_G(F,N) → Hom_G(R,N) → H¹(G,Hom_ℤ(M,N)) → H¹(G,Hom_ℤ(F,N))`,
and the last term vanishes by Shapiro: `Hom_ℤ(ℤ[G],N) ≅ Coind_1^G(N)` and `H¹(G, Coind_1^G N)
= H¹(1,N) = 0`.  Hence the cokernel is `H¹(G,Hom_ℤ(M,N)) = Ext¹_G(ℤ, Hom_ℤ(M,N))`.

**Both hypotheses are sharp in different directions — do not "repair" the statement.**
* Divisibility of `N` is *not* superfluous: dropping it makes the middle sequence fail to be
  short exact.  (The *other* sibling form, `Ext²_G(R,X) ≅ H²(G,Hom_ℤ(R,X))`, is the one that
  needs `R` a `ℤ`-lattice; that is a different statement, valid with no divisibility of `X`.)
* `M` need *not* be a `ℤ`-lattice, and must not be assumed to be one: the call site uses a
  finite `𝔽_p`-module `M = E^∨(1)` together with the divisible `N = Ω̄ˣ`.
* Two candidate counterexamples that *fail* (both sides agree): with `G = ℤ/2`, `M = 𝔽₂` trivial
  and `N = ℤ[1/2]/ℤ` (Prüfer, divisible) both sides are `ℤ/2` — note the left side is
  `Ext¹_{ℤ[ℤ/2]}`, not `Ext¹_ℤ`, and `ℤ[ℤ/2] ≇ ℤ × ℤ`; with `G = 1`, `M = ℤ/2`, `N = ℚ` both
  sides are `0` because `ℚ/2ℚ = 0`. -/
theorem ext_one_iso_divisible_cohomology (G : Type) [Group G]
    (M N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hdiv : ∀ (n : ℕ), 0 < n → ∀ y : N.V, ∃ x : N.V, n • x = y) :
    Nonempty (CategoryTheory.Abelian.Ext M N 1 ≃+
      CategoryTheory.Abelian.Ext (SSGRoute.PTExt.unitRep G)
        (Work.SSGRoute.homRep M N) 1)         := by
  classical
  have hInj : Module.Injective Coeff N.V := moduleInjective_coeff_of_divisible N.V hdiv
  have hp : Epi (Rep.freeLift Coeff G M (fun m : M.V => m)) := freeLift_id_epi G M
  let p : Rep.free Coeff G M.V ⟶ M := Rep.freeLift Coeff G M (fun m : M.V => m)
  haveI hp' : Epi p := hp
  let S : ShortComplex (Rep.{0} Coeff G) :=
    ShortComplex.mk (Limits.kernel.ι p) p (Limits.kernel.condition p)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) inferInstance inferInstance
  have hProj : Projective S.X₂ := Rep.free_projective
  haveI := hProj
  obtain ⟨e₁⟩ := ext_coker_LES hS N
  have e₁' : Abelian.Ext M N 1 ≃+
      (Abelian.Ext S.X₁ N 0 ⧸
        ((Abelian.Ext.mk₀ S.f).precomp N (zero_add 0)).range) := e₁
  have hS' : (homRepShortComplex S N).ShortExact := homRepShortComplex_shortExact G S hS N hInj
  obtain ⟨X, hXiso⟩ := homRepFree_coind_iso G M.V N
  haveI : Subsingleton (Abelian.Ext (unitRep G) (homRepShortComplex S N).X₂ 1) :=
    ext_one_homRepFree_subsingleton G M.V N X hXiso
  obtain ⟨e₂⟩ := ext_coker_LES_covariant hS' (unitRep G)
  have e₂' : Abelian.Ext (unitRep G) (homRep M N) 1 ≃+
      (Abelian.Ext (unitRep G) (homRep S.X₁ N) 0 ⧸
        ((Abelian.Ext.mk₀ (homRepPre S.X₂ S.X₁ N S.f)).postcomp (unitRep G)
          (add_zero 0)).range) := e₂
  have hmap : AddSubgroup.map (unitHomExtEquiv S.X₁ N).symm.toAddMonoidHom
      (((Abelian.Ext.mk₀ S.f).precomp N (zero_add 0))).range
      = ((Abelian.Ext.mk₀ (homRepPre S.X₂ S.X₁ N S.f)).postcomp (unitRep G)
          (add_zero 0)).range := by
    apply le_antisymm
    · intro b hb
      rw [AddSubgroup.mem_map] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      rw [AddMonoidHom.mem_range] at ha ⊢
      obtain ⟨z, rfl⟩ := ha
      refine ⟨(unitHomExtEquiv S.X₂ N).symm z, ?_⟩
      exact (unitHomExtEquiv_symm_precomp S.X₂ S.X₁ N S.f z).symm
    · intro b hb
      rw [AddMonoidHom.mem_range] at hb
      obtain ⟨y, rfl⟩ := hb
      rw [AddSubgroup.mem_map]
      refine ⟨((Abelian.Ext.mk₀ S.f).precomp N (zero_add 0))
          ((unitHomExtEquiv S.X₂ N) y), ⟨(unitHomExtEquiv S.X₂ N) y, rfl⟩, ?_⟩
      have h := unitHomExtEquiv_symm_precomp S.X₂ S.X₁ N S.f ((unitHomExtEquiv S.X₂ N) y)
      rw [AddEquiv.symm_apply_apply] at h
      exact h
  exact ⟨e₁'.trans ((QuotientAddGroup.congr _ _ (unitHomExtEquiv S.X₁ N).symm hmap).trans e₂'.symm)⟩

end Work.SSGRoute
