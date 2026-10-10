import Mathlib.Tactic.Have
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.ext_idele_shapiro
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `h ∘ z = 0` for `z` from the idèles and `h` locally trivial

If `h ∈ H¹(Gal(K/k), M)` is locally trivial (its restriction to the decomposition group of every
place of `K` vanishes) and `z ∈ Ext¹_{Gal(K/k)}(M, 𝕀_K)` is a class with idèle coefficients, then
the Yoneda product of `h` with the push-forward of `z` to the idèle class group `C_K` vanishes in
`H²(Gal(K/k), C_K)`.

The proof is the idèle Shapiro (localisation) theorem: `z ↦ (extLoc w z)_w` is injective on
`Ext²_{Gal(K/k)}(ℤ, 𝕀_K)` (E2, `Work.SSGRoute.ext_idele_shapiro_aux` at `M = ℤ`), and localisation
is compatible with the Yoneda pairing, so the localisation of `h ∘ z` at `w` is
`(res_{D_w} h) ∘ (extLoc w z) = 0`.

The mathematical content is exactly the obvious one: since `𝕀_K` is induced from the decomposition
groups, a class that dies locally dies on `𝕀_K`.
-/

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute.Sha2Lib

open NK.GlobalCFT

/-- **A transversal of the orbits of a group action**: there is a subset of `α` meeting every
`G`-orbit in exactly one point.  (Classical choice of a representative of each orbit.) -/
theorem exists_transversal_of_mulAction (G α : Type) [Group G] [MulAction G α] :
    ∃ R : Set α, ∀ w : α, ∃! w' : R, ∃ σ : G, σ • w = w'.1 := by
  refine ⟨Set.range (fun w : α =>
    Quotient.out (Quotient.mk'' w : Quotient (MulAction.orbitRel G α))), ?_⟩
  intro w
  refine ⟨⟨Quotient.out (Quotient.mk'' w), w, rfl⟩, ?_, ?_⟩
  · have h1 : (Quotient.mk'' (Quotient.out (Quotient.mk'' w : Quotient (MulAction.orbitRel G α)))
        : Quotient (MulAction.orbitRel G α)) = Quotient.mk'' w := Quotient.out_eq _
    have h2 : (MulAction.orbitRel G α)
        (Quotient.out (Quotient.mk'' w : Quotient (MulAction.orbitRel G α))) w :=
      Quotient.exact h1
    rw [MulAction.orbitRel_apply] at h2
    exact h2
  · rintro ⟨y, hy⟩ ⟨σ, hσ⟩
    obtain ⟨w₀, hw₀⟩ := hy
    have hrel : (MulAction.orbitRel G α) y w := by
      rw [MulAction.orbitRel_apply]
      exact ⟨σ, hσ⟩
    have hq : (Quotient.mk'' y : Quotient (MulAction.orbitRel G α)) = Quotient.mk'' w :=
      Quotient.sound hrel
    have hq' : (Quotient.mk'' w₀ : Quotient (MulAction.orbitRel G α)) = Quotient.mk'' y := by
      rw [← hw₀]
      exact (Quotient.out_eq (Quotient.mk'' w₀)).symm
    apply Subtype.ext
    exact hw₀.symm.trans (congrArg Quotient.out (hq'.trans hq))

/-- **Restriction to a subgroup needs no change of the coefficient module.**  If the restriction of
a cohomology class to `D ≤ G` vanishes, then so does its image under the exact functor
`Rep.resFunctor D.subtype`: the two differ only by the `mk₀ (unitRes D.subtype)` factor, which is
the identity because `unitRes D.subtype = 𝟙 (unitRep D)` definitionally. -/
theorem extRes_eq_zero_of_extHRestrict_eq_zero {G : Type} [Group G] (D : Subgroup G)
    {A : Rep.{0} Coeff G} {n : ℕ} (x : extH A n)
    (h : extHRestrict D x = 0) : extRes D.subtype x = 0 := by
  have h' : extHRestrict D x = extRes D.subtype x := by
    rw [extHRestrict, extHMap]
    have h2 : (extRes D.subtype x).comp
        (Abelian.Ext.mk₀ (𝟙 (Rep.res D.subtype A))) (add_zero n) = extRes D.subtype x :=
      Abelian.Ext.comp_mk₀_id _
    rw [h2]
    exact Abelian.Ext.mk₀_id_comp _
  exact h'.symm.trans h

theorem yonedaPair_extToClasses_eq_zero_of_locTrivial
    (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)}
    (z : CategoryTheory.Abelian.Ext.{0} M (SSGRoute.PTExt.idelesK k K) 1)
    (h : SSGRoute.PTExt.extH M 1)
    (hh : SSGRoute.PTExt.IsLocTrivial (k := k) (K := K) h) :
    SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extToClasses (k := k) (K := K) z) h = 0 := by
  -- a transversal of the `Gal(K/k)`-orbits of the places of `K`
  obtain ⟨R, hR⟩ := exists_transversal_of_mulAction (K ≃ₐ[k] K) (Place K)
  -- E2 at `M = ℤ`: localisation at the places of `R` is injective on `Ext²(ℤ, 𝕀_K)`
  have hinj := (Work.SSGRoute.ext_idele_shapiro_aux (k := k) (K := K)
      (unitRep (K ≃ₐ[k] K)) (by infer_instance) 2 R hR).1
  -- localisation is compatible with the Yoneda pairing: the `w`-component of `h ∘ z` is the
  -- product of the restriction of `h` to `D_w` with the `w`-component of `z`
  have hloc : ∀ w : Place K, extLoc (k := k) w (yonedaPair z h) =
      (extRes (decompK (k := k) w).subtype h).comp (extLoc (k := k) w z) rfl := by
    intro w
    rw [yonedaPair, extLoc, extRes, Abelian.Ext.mapExactFunctor_comp]
    exact Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ _
  -- so `h ∘ z = 0` follows from the vanishing of all its localisations
  have hzero : yonedaPair z h = 0 := by
    refine hinj (yonedaPair z h) (fun w _hw => ?_)
    rw [hloc w, extRes_eq_zero_of_extHRestrict_eq_zero (D := decompK (k := k) w) h (hh w)]
    simp
  have hzero' : h.comp z rfl = 0 := by
    simpa only [yonedaPair] using hzero
  -- push forward to the idèle class group
  rw [show yonedaPair (extToClasses (k := k) (K := K) z) h
      = (h.comp z rfl).comp
          (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k K)) (add_zero 2) from
      (Abelian.Ext.comp_assoc_of_third_deg_zero h z _ (rfl : 1 + 1 = 2)).symm,
    hzero']
  simp

end Work.SSGRoute.Sha2Lib
