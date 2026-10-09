import Mathlib
import Submission.Work.SSGRoute.ArchNat.eOfConnMapCocycleHz
import Submission.Work.SSGRoute.ArchNat.eCohZeroUnitHomSign
import Submission.Work.SSGRoute.ArchDictionary.eOfConnMap
import Submission.Work.SSGRoute.eCoh_delta
import Submission.Work.SSGRoute.PT.gammaHom_H1pi_eq_eCoh_or_neg
import Submission.Work.SSGRoute.ext_one_homRepFree_subsingleton
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cochain formula for `NatH1.eOf` on a connecting-map class (`eOf_connMap_cocycle`)

This file proves, in the namespace `Work.SSGRoute.ArchNat`, a **second, self-contained proof of the
statement that the lead dispatched as D3** (`Work.SSGRoute.ArchDictionary.eOf_connMap_cocycle`,
`ARCHP2_PLAN.md` §B/§3): the cochain formula

    `NatH1.eOf N hInj X hX M (CokerNat.connMap (ses_shortExact M) N a) = ± H¹π ⟨ψ, hz⟩`

for a `1`-cochain `ψ` presented as the "coboundary of the lift `atil`" of `a`.  It is the piece
that the D2 lane (`ArchDictionary/archPhiSeam_square`, step 5 of `ARCHP2_PLAN.md` §3) needs; it is
*not* declared in `ArchDictionary`, so that the two statements can coexist and the D2 prover may
cite whichever lands first.  (The name is `Work.SSGRoute.ArchNat.eOf_connMap_cocycle`.)

## The route (identical to the lead's plan, made to compile)

1. `Work.SSGRoute.ArchDictionary.eOf_connMap` unfolds `eOf` on a connecting-map class into
   `(NatH1.gammaIso N M).symm (CokerNat.connMapCov (NatH1.dpres_shortExact N hInj M) (unitRep G)
   (NatH1.cEq N M a))`.
2. `Work.SSGRoute.PT.gammaHom_H1pi_eq_eCoh_or_neg` computes the `gammaHom` of
   `H¹π ⟨ψ, hz⟩` as `± eCoh 1 G (modRep G (M.V →ₗ N.V)) (H¹π ⟨ψ, hz⟩)`.
3. `groupCohomology.δ₀_apply` (Mathlib) computes the connecting map of the *dual* presentation
   `NatH1.dpres N M` on the canonical invariant `z = eZeroToInv G (dpres N M).X₃ φ`
   (`φ = (unitHomEquiv (pres M).X₁ N)⁻¹ (addEquiv₀ a)`) as the class of `ψ` itself; the two
   hypotheses of `δ₀_apply` are exactly `hatil` (the lift relation on the syzygy) and `hψ` (the
   lift relation on the free cover).
4. `Work.SSGRoute.eCoh_delta` at `n = 0` and the *degree-zero* comparison
   `Work.SSGRoute.ArchNat.eCoh_zero_invOfExt0_eq_pm_cEq` (this file's sibling
   `eCohZeroUnitHomSign.lean`) identify the resulting class with `± CokerNat.connMapCov …`,
   which is the right-hand side of step 1.

The sign is unavoidable (it is fixed by the `Classical.choose`s inside `eCoh` and `H0Iso`) and
irrelevant: the consumer is at `p = 2`.

Implementation notes (the traps of this chapter, all encountered here):

* `Rep.V`-typed terms (`↑A`, `(homRep X N).V`, …) are **not** seen as function types by the
  elaborator: every application of such a term must go through
  `(show X.V →ₗ[Coeff] N.V from t) x` (the idiom of `Work.SSGRoute.homRepPre_apply` itself).
* `rw` matches at *reducible* transparency, so `↑(homRep M N)` and `↑(modRep G (M.V →ₗ N.V))`
  do not match each other (`homRep` is a plain `def`); the sign bookkeeping at the end therefore
  binds the `gammaHom`-term as a `let` `GH` with the `homRep`-typing forced by an ascription.
* `CokerNat.connMapCov_apply`'s proof argument is `add_zero 1` while `eCoh_delta` produces `rfl`;
  the two are definitionally equal (both reduce to `1 = 1`), so `rw` accepts the rewrite.
-/

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt

namespace Work.SSGRoute.ArchNat

variable {G : Type} [Group G]

/-- An additive map into the carrier of a representation, as a `Coeff`-linear map.  (`ULift ℤ`-linearity
is definitionally the `ℤ`-linearity of `ulift_up_int_smul_eq`.) -/
def toCoeffLinear (X N : Rep.{0} Coeff G) (f : X.V →+ N.V) : X.V →ₗ[Coeff] N.V where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    obtain ⟨k⟩ := c
    simp only [RingHom.id_apply, Work.SSGRoute.ulift_up_int_smul_eq]
    exact map_zsmul f k x

/-- Transitivity of a `±`-statement. -/
theorem pm_trans {A : Type} [AddCommGroup A] {x y z : A}
    (h1 : x = y ∨ x = -y) (h2 : y = z ∨ y = -z) : x = z ∨ x = -z := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (h1.trans h2)
  · exact Or.inr (by rw [h1, h2])
  · exact Or.inr (by rw [h1, h2])
  · exact Or.inl (by rw [h1, h2, neg_neg])

/-- Composition with a fixed class preserves `±`. -/
theorem pm_comp {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y Z : C} {n : ℕ} {x y : Abelian.Ext X Y n} (h : x = y ∨ x = -y)
    {m : ℕ} (β : Abelian.Ext Y Z m) {p : ℕ} (hp : n + m = p) :
    x.comp β hp = y.comp β hp ∨ x.comp β hp = -(y.comp β hp) := by
  rcases h with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h, Abelian.Ext.neg_comp])

/-- Symmetry of a `±`-statement. -/
theorem pm_symm {A : Type} [AddCommGroup A] {x y : A} (h : x = y ∨ x = -y) :
    y = x ∨ y = -x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

/-- **The cochain formula for `eOf` on a connecting-map class.**  See the file header. -/
theorem eOf_connMap_cocycle
    (N : Rep.{0} Coeff G) (hInj : Module.Injective Coeff N.V)
    (X : ∀ M : Rep.{0} Coeff G, Rep.{0} Coeff (⊥ : Subgroup G))
    (hX : ∀ M, Nonempty (Work.SSGRoute.homRep (Rep.free Coeff G M.V) N ≅
      Rep.coind (⊥ : Subgroup G).subtype (X M)))
    (M : Rep.{0} Coeff G)
    (a : CategoryTheory.Abelian.Ext (Work.SSGRoute.ArchDictionary.NatH1.pres M).X₁ N 0)
    (atil : (Rep.free Coeff G M.V).V →+ N.V)
    (hatil : ∀ r, atil (Rep.Hom.hom (Limits.kernel.ι (Work.SSGRoute.freeCover M)) r)
      = Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ a) r)
    (ψ : G → (M.V →ₗ[Coeff] N.V))
    (hψ : ∀ g f, ψ g (Rep.Hom.hom (Work.SSGRoute.freeCover M) f)
      = N.ρ g (atil ((Rep.free Coeff G M.V).ρ g⁻¹ f)) - atil f) :
    ∃ hz : ψ ∈ @Work.GroupCohomology.Z1 G (M.V →ₗ[Coeff] N.V) _ _
        (Work.SSGRoute.homRepDistribMulAction M N),
      Work.SSGRoute.ArchDictionary.NatH1.eOf N hInj X hX M
          (Work.SSGRoute.CokerNat.connMap (Work.SSGRoute.ses_shortExact M) N a)
        = @Work.GroupCohomology.H1π G (M.V →ₗ[Coeff] N.V) _ _
            (Work.SSGRoute.homRepDistribMulAction M N) ⟨ψ, hz⟩ ∨
      Work.SSGRoute.ArchDictionary.NatH1.eOf N hInj X hX M
          (Work.SSGRoute.CokerNat.connMap (Work.SSGRoute.ses_shortExact M) N a)
        = -@Work.GroupCohomology.H1π G (M.V →ₗ[Coeff] N.V) _ _
            (Work.SSGRoute.homRepDistribMulAction M N) ⟨ψ, hz⟩ := by
  classical
  haveI hsub : Subsingleton (CategoryTheory.Abelian.Ext (unitRep G)
      (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₂ 1) :=
    Work.SSGRoute.ext_one_homRepFree_subsingleton G M.V N (X M) (hX M)
  have hz : ψ ∈ @Work.GroupCohomology.Z1 G (M.V →ₗ[Coeff] N.V) _ _
      (Work.SSGRoute.homRepDistribMulAction M N) := eOf_connMap_cocycle_hz M N atil ψ hψ
  refine ⟨hz, ?_⟩
  rw [Work.SSGRoute.ArchDictionary.eOf_connMap N hInj X hX M a]
  -- ## the degree-one side via `gammaHom`
  have hψc : (show G → ↑(Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₁ from
        (⟨ψ, hz⟩ : ↥(Work.GroupCohomology.Z1 G (M.V →ₗ[Coeff] N.V))).1) ∈
      groupCohomology.cocycles₁ (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₁ := by
    rw [groupCohomology.mem_cocycles₁_iff]
    intro g h
    exact hz g h
  have hγ := Work.SSGRoute.PT.gammaHom_H1pi_eq_eCoh_or_neg G (M.V →ₗ[Coeff] N.V) ⟨ψ, hz⟩ hψc
  -- ## the canonical invariant `z` and the lift `y₀`
  let z : (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₃.ρ.invariants :=
    Work.SSGRoute.eZeroToInv G (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₃
      ((Work.SSGRoute.unitHomEquiv
          (Work.SSGRoute.ArchDictionary.NatH1.pres M).X₁ N).symm
        (CategoryTheory.Abelian.Ext.addEquiv₀ a))
  let z' : (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₃.V := ↑z
  have hzval : ∀ r : (Work.SSGRoute.ArchDictionary.NatH1.pres M).X₁.V,
      (show (Work.SSGRoute.ArchDictionary.NatH1.pres M).X₁.V →ₗ[Coeff] N.V from z') r
        = (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ a)) r := by
    intro x
    show (show (Work.SSGRoute.ArchDictionary.NatH1.pres M).X₁.V →ₗ[Coeff] N.V from
        ((Rep.Hom.hom ((Work.SSGRoute.unitHomEquiv
          (Work.SSGRoute.ArchDictionary.NatH1.pres M).X₁ N).symm
            (CategoryTheory.Abelian.Ext.addEquiv₀ a))) 1)) x = _
    rw [← Work.SSGRoute.unitHomEquiv_apply
        (Work.SSGRoute.ArchDictionary.NatH1.pres M).X₁ N
        ((Work.SSGRoute.unitHomEquiv
            (Work.SSGRoute.ArchDictionary.NatH1.pres M).X₁ N).symm
          (CategoryTheory.Abelian.Ext.addEquiv₀ a)) x]
    rw [AddEquiv.apply_symm_apply]
  let y₀ : (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₂.V :=
    toCoeffLinear (Rep.free Coeff G M.V) N atil
  have hy : (Rep.Hom.hom (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).g) y₀ = ↑z := by
    change (Rep.Hom.hom (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).g) y₀
      = (show (Work.SSGRoute.ArchDictionary.NatH1.pres M).X₁.V →ₗ[Coeff] N.V from z')
    apply LinearMap.ext
    intro r
    show (show (Work.SSGRoute.ArchDictionary.NatH1.pres M).X₁.V →ₗ[Coeff] N.V from
        (Rep.Hom.hom (Work.SSGRoute.homRepPre (Rep.free Coeff G M.V)
          (Limits.kernel (Work.SSGRoute.freeCover M)) N
          (Limits.kernel.ι (Work.SSGRoute.freeCover M))) y₀)) r
      = (show (Work.SSGRoute.ArchDictionary.NatH1.pres M).X₁.V →ₗ[Coeff] N.V from z') r
    rw [Work.SSGRoute.homRepPre_apply]
    show atil (Rep.Hom.hom (Limits.kernel.ι (Work.SSGRoute.freeCover M)) r) = _
    rw [hatil r]
    exact (hzval r).symm
  let x : G → ↑(Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₁ := fun g => ψ g
  have hx : ⇑(Rep.Hom.hom (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).f) ∘ x
      = (ConcreteCategory.hom (groupCohomology.d₀₁
          (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₂)) y₀ := by
    funext g
    apply LinearMap.ext
    intro f
    show (show (Rep.free Coeff G M.V).V →ₗ[Coeff] N.V from
        (Rep.Hom.hom (Work.SSGRoute.homRepPre M (Rep.free Coeff G M.V) N
          (Work.SSGRoute.freeCover M)) (x g))) f
      = N.ρ g (atil ((Rep.free Coeff G M.V).ρ g⁻¹ f)) - atil f
    rw [Work.SSGRoute.homRepPre_apply]
    show ψ g (Rep.Hom.hom (Work.SSGRoute.freeCover M) f) = _
    rw [hψ g f]
  -- ## `δ₀_apply` and `eCoh_delta`
  have hδ := groupCohomology.δ₀_apply (X := Work.SSGRoute.ArchDictionary.NatH1.dpres N M)
    (Work.SSGRoute.ArchDictionary.NatH1.dpres_shortExact N hInj M) z y₀ hy x hx
  have hΔ := Work.SSGRoute.eCoh_delta 0 G (Work.SSGRoute.ArchDictionary.NatH1.dpres N M)
    (Work.SSGRoute.ArchDictionary.NatH1.dpres_shortExact N hInj M)
    ((groupCohomology.H0Iso (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₃).inv z)
  rw [hδ] at hΔ
  have h0 := eCoh_zero_invOfExt0_eq_pm_cEq N M a
  have h0' := pm_comp h0 (Work.SSGRoute.ArchDictionary.NatH1.dpres_shortExact N hInj M).extClass rfl
  have hE1 : SSGRoute.PTExt.eCoh 1 G (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₁
      ((groupCohomology.H1π (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₁).hom
        ⟨x, groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁
          (Work.SSGRoute.ArchDictionary.NatH1.dpres_shortExact N hInj M) hx⟩)
      = Work.SSGRoute.CokerNat.connMapCov
          (Work.SSGRoute.ArchDictionary.NatH1.dpres_shortExact N hInj M)
          (unitRep G) (Work.SSGRoute.ArchDictionary.NatH1.cEq N M a) ∨
      SSGRoute.PTExt.eCoh 1 G (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₁
      ((groupCohomology.H1π (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₁).hom
        ⟨x, groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁
          (Work.SSGRoute.ArchDictionary.NatH1.dpres_shortExact N hInj M) hx⟩)
      = -Work.SSGRoute.CokerNat.connMapCov
          (Work.SSGRoute.ArchDictionary.NatH1.dpres_shortExact N hInj M)
          (unitRep G) (Work.SSGRoute.ArchDictionary.NatH1.cEq N M a) := by
    have hca := pm_trans hΔ h0'
    rwa [← Work.SSGRoute.CokerNat.connMapCov_apply
      (Work.SSGRoute.ArchDictionary.NatH1.dpres_shortExact N hInj M) (unitRep G)
      (Work.SSGRoute.ArchDictionary.NatH1.cEq N M a)] at hca
  let GH : SSGRoute.PTExt.extH (Work.SSGRoute.homRep M N) 1 :=
    Work.SSGRoute.ExtH1.gammaHom G (M.V →ₗ[Coeff] N.V) (Work.SSGRoute.augSES_shortExact G)
      (@Work.GroupCohomology.H1π G (M.V →ₗ[Coeff] N.V) _ _
        (Work.SSGRoute.homRepDistribMulAction M N) ⟨ψ, hz⟩)
  have hγ' : GH = SSGRoute.PTExt.eCoh 1 G (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₁
        ((groupCohomology.H1π (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₁).hom
          ⟨x, groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁
            (Work.SSGRoute.ArchDictionary.NatH1.dpres_shortExact N hInj M) hx⟩) ∨
      GH = -SSGRoute.PTExt.eCoh 1 G (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₁
        ((groupCohomology.H1π (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₁).hom
          ⟨x, groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁
            (Work.SSGRoute.ArchDictionary.NatH1.dpres_shortExact N hInj M) hx⟩) := hγ
  have hsign := pm_trans hγ' hE1
  have hg : (Work.SSGRoute.ArchDictionary.NatH1.gammaIso N M)
      (@Work.GroupCohomology.H1π G (M.V →ₗ[Coeff] N.V) _ _
        (Work.SSGRoute.homRepDistribMulAction M N) ⟨ψ, hz⟩) = GH := rfl
  rcases hsign with hs | hs
  · left
    rw [← hs, ← hg]
    exact AddEquiv.symm_apply_apply _ _
  · right
    have hs' : Work.SSGRoute.CokerNat.connMapCov
          (Work.SSGRoute.ArchDictionary.NatH1.dpres_shortExact N hInj M)
          (unitRep G) (Work.SSGRoute.ArchDictionary.NatH1.cEq N M a) = -GH := by
      have h2 : -GH = Work.SSGRoute.CokerNat.connMapCov
          (Work.SSGRoute.ArchDictionary.NatH1.dpres_shortExact N hInj M)
          (unitRep G) (Work.SSGRoute.ArchDictionary.NatH1.cEq N M a) := by
        have h3 := congrArg Neg.neg hs
        rwa [neg_neg] at h3
      exact h2.symm
    have hkey : (Work.SSGRoute.ArchDictionary.NatH1.gammaIso N M).symm GH
        = (@Work.GroupCohomology.H1π G (M.V →ₗ[Coeff] N.V) _ _
            (Work.SSGRoute.homRepDistribMulAction M N) ⟨ψ, hz⟩) := by
      rw [← hg]
      exact AddEquiv.symm_apply_apply _ _
    rw [hs', map_neg, hkey]

end Work.SSGRoute.ArchNat
