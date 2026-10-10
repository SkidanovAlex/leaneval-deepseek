import Mathlib.Tactic.Have
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.pt_pairing_ext
import Submission.Work.SSGRoute.bridgeE_map_group
import Submission.Work.SSGRoute.phiAt_level_infl
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

set_option linter.unusedVariables false

/-! ## Conjugation transfer of restriction to a subgroup

Everything `lam_local_determination` needs beyond the bookkeeping of places: if a degree-one
class in `H¹(G, A)` restricts to zero on a subgroup `D ≤ G`, then it restricts to zero on every
conjugate subgroup `g D g⁻¹`.  The proof goes through the comparison
`bridgeE : Hⁿ(G, A) ≃+ extH A n` with Mathlib's `groupCohomology`, where the statement is a
computation with inhomogeneous `1`-cocycles: a `1`-cocycle that is a coboundary on `D` with
primitive `m` is a coboundary on `g D g⁻¹` with primitive `ρ(g) m - c g`. -/

/-- **Algebraic core of the conjugation transfer.**  If the restriction of a `1`-cocycle `c` to a
subgroup containing `s` is a coboundary with primitive `m` (i.e. `c s = ρ(s) m - m`), then the
restriction of `c` to the conjugate subgroup `g·s·g⁻¹` is a coboundary with primitive
`ρ(g) m - c g`: `c (g s g⁻¹) = ρ (g s g⁻¹) (ρ g m - c g) - (ρ g m - c g)`. -/
lemma cocycle_conj_primitive {k : Type} [CommRing k] {G : Type} [Group G] (A : Rep k G)
    (c : groupCohomology.cocycles₁ A) (g s : G) (m : A)
    (hm : A.ρ s m - m = c s) :
    A.ρ (g * s * g⁻¹) (A.ρ g m - c g) - (A.ρ g m - c g) = c (g * s * g⁻¹) := by
  have hcoc := (groupCohomology.mem_cocycles₁_iff (↑c : G → A)).1 c.2
  have hselfm : A.ρ g⁻¹ (A.ρ g m) = m := by
    simp
  have hselfc : A.ρ g⁻¹ (A.ρ g (c g⁻¹)) = c g⁻¹ := by
    simpa using Representation.self_inv_apply A.ρ (g⁻¹) (c g⁻¹)
  have hcg : c g⁻¹ = - A.ρ g⁻¹ (c g) := by
    have h := congrArg (A.ρ g⁻¹) (groupCohomology.cocycles₁_map_inv c g)
    rw [map_neg] at h
    rwa [hselfc] at h
  have h1 : c (g * s * g⁻¹) = A.ρ g (c (s * g⁻¹)) + c g := by
    rw [mul_assoc]
    exact hcoc g (s * g⁻¹)
  have h2 : c (s * g⁻¹) = A.ρ s (c g⁻¹) + c s := hcoc s g⁻¹
  rw [h1, h2, hcg, ← hm]
  simp only [map_sub, map_neg, map_add, map_mul, Module.End.mul_apply, hselfm]
  abel_nf

/-- Evaluation of the restricted `1`-cocycle: the underlying function of
`mapCocycles₁ D.subtype 𝟙 c` is `fun t : D => c t`. -/
lemma mapCocycles₁_subtype_apply {k : Type} [CommRing k] {G : Type} [Group G] (A : Rep k G)
    (D : Subgroup G) (c : groupCohomology.cocycles₁ A) (t : D) :
    (⇑(groupCohomology.mapCocycles₁ D.subtype (𝟙 (Rep.res D.subtype A)) c) : D → A) t
      = c t.1 := by
  rw [groupCohomology.coe_mapCocycles₁]
  rfl

/-- **Conjugation transfer of restriction to a subgroup** for Mathlib's `groupCohomology` in
degree one: if `x : H¹(G, A)` restricts to zero on `D ≤ G`, then it restricts to zero on the
conjugate subgroup `g D g⁻¹`. -/
theorem gc_map_subtype_conj_eq_zero {k : Type} [CommRing k] {G : Type} [Group G]
    (A : Rep k G) (D : Subgroup G) (g : G) (x : groupCohomology A 1)
    (hx : (ConcreteCategory.hom (groupCohomology.map D.subtype (𝟙 (Rep.res D.subtype A)) 1)) x
      = 0) :
    (ConcreteCategory.hom (groupCohomology.map (D.map (MulAut.conj g).toMonoidHom).subtype
      (𝟙 (Rep.res (D.map (MulAut.conj g).toMonoidHom).subtype A)) 1)) x = 0 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : groupCohomology.cocycles₁ A,
      (ConcreteCategory.hom (groupCohomology.H1π A)) c = x :=
    (ModuleCat.epi_iff_surjective (groupCohomology.H1π A)).mp inferInstance x
  rw [← hc] at hx ⊢
  have hz : (groupCohomology.H1π (Rep.res D.subtype A))
      (groupCohomology.mapCocycles₁ D.subtype (𝟙 (Rep.res D.subtype A)) c) = 0 := by
    rw [← groupCohomology.H1π_comp_map_apply D.subtype (𝟙 (Rep.res D.subtype A)) c]
    exact hx
  rw [groupCohomology.H1π_eq_zero_iff] at hz
  rw [groupCohomology.coboundaries₁, LinearMap.mem_range] at hz
  obtain ⟨m, hm⟩ := hz
  have hm' : ∀ s : G, s ∈ D → A.ρ s m - m = c s := by
    intro s hs
    have h := congr_fun hm ⟨s, hs⟩
    rw [groupCohomology.d₀₁_hom_apply, mapCocycles₁_subtype_apply A D c ⟨s, hs⟩] at h
    change A.ρ s m - m = c s at h
    exact h
  rw [groupCohomology.H1π_comp_map_apply (D.map (MulAut.conj g).toMonoidHom).subtype
    (𝟙 (Rep.res (D.map (MulAut.conj g).toMonoidHom).subtype A)) c]
  rw [groupCohomology.H1π_eq_zero_iff]
  rw [groupCohomology.coboundaries₁, LinearMap.mem_range]
  refine ⟨A.ρ g m - c g, ?_⟩
  funext t
  obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.mp t.2
  have hst' : (↑t : G) = g * s * g⁻¹ := by
    rw [← hst, MulEquiv.toMonoidHom_eq_coe]
    exact MulAut.conj_apply g s
  have hmap := mapCocycles₁_subtype_apply A (D.map (MulAut.conj g).toMonoidHom) c t
  rw [groupCohomology.d₀₁_hom_apply, hmap]
  change A.ρ (↑t) (A.ρ g m - c g) - (A.ρ g m - c g) = c (↑t)
  rw [hst']
  exact cocycle_conj_primitive A c g s m (hm' s hs)

/-! ## The same statement on the `Ext` core -/

/-- **Conjugation transfer of `extHRestrict`.**  If a class `y ∈ H¹(G, A) = extH A 1` restricts
to zero on a subgroup `D ≤ G`, then it restricts to zero on every conjugate subgroup
`g D g⁻¹ = D.map (MulAut.conj g).toMonoidHom`. -/
theorem extHRestrict_conj_eq_zero {G : Type} [Group G] (D : Subgroup G) (g : G)
    {A : Rep.{0} Coeff G} (y : extH A 1) (hy : extHRestrict D y = 0) :
    extHRestrict (D.map (MulAut.conj g).toMonoidHom) y = 0 := by
  -- send both sides along the bridge to Mathlib's group cohomology
  have key : ∀ E : Subgroup G, extHRestrict E y = 0 →
      (ConcreteCategory.hom (groupCohomology.map E.subtype (𝟙 (Rep.res E.subtype A)) 1))
        ((bridgeE G A 1).symm y) = 0 := by
    intro E hE
    have h := bridgeE_map_group E.subtype A 1 ((bridgeE G A 1).symm y)
    rw [(bridgeE G A 1).apply_symm_apply y] at h
    have hzero : bridgeE E (Rep.res E.subtype A) 1
        ((ConcreteCategory.hom (groupCohomology.map E.subtype (𝟙 (Rep.res E.subtype A)) 1))
          ((bridgeE G A 1).symm y)) = 0 := by
      rw [h]
      exact hE
    refine (bridgeE E (Rep.res E.subtype A) 1).injective ?_
    rw [hzero, map_zero]
  have hD := key D hy
  have hconj := gc_map_subtype_conj_eq_zero A D g ((bridgeE G A 1).symm y) hD
  have h := bridgeE_map_group (D.map (MulAut.conj g).toMonoidHom).subtype A 1
    ((bridgeE G A 1).symm y)
  rw [(bridgeE G A 1).apply_symm_apply y, hconj, map_zero] at h
  exact h.symm

/-- **Step 1 of E7cΩ: `lam` is determined by the local restriction at `w`.**

Let `λ` be a family of functionals over the levels `K ≤ L ≤ Ω` which is *local at `w`* in the sense
of `hloc` (at every level there is a place over `w` such that every class whose restriction to the
decomposition group of that place vanishes is killed).  Then in fact `λ_L(h)` depends only on the
restriction of `h` to the decomposition group of *any* place `w'` over `w`.

Hint on the proof.  The places over `w` at a Galois level `L` are `Gal(L/k)`-conjugate
(`NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver`); the stabilisers are therefore
conjugate subgroups (`MulAction.stabilizer_smul_eq_stabilizer_map_conj`).  For conjugate subgroups
`S' = gSg⁻¹`, restriction maps differ by the conjugation isomorphism, so `res_S t = res_S t'` if
and only if `res_{S'} t = res_{S'} t'`; concretely on 1-cocycles, if `d|_{S'} = 0` and `t = ghg⁻¹`,
then `d(t) = d(g) - t·d(g)` is a coboundary, so `res_S d = 0`.  Hence `h₁ - h₂`, whose restriction to
the `hloc`-witness `D_{w''}` is 0, has vanishing restriction to every `D_{w'}`; `hloc` kills it and
additivity of `lam L` gives the conclusion.  No `hcompat` is needed. -/
theorem lam_local_determination (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep Coeff (K ≃ₐ[k] K))
    (w : NK.GlobalCFT.Place K)
    (lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      extH (Rep.res (galRes k K L) M) 1 →+ extH (classesK k L) 2)
    (hloc : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      ∃ w' : NK.GlobalCFT.Place L, NK.GlobalCFT.Place.LiesOver w' w ∧
        ∀ h : extH (Rep.res (galRes k K L) M) 1,
          extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h = 0 → lam L h = 0) :
    ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
      (h₁ h₂ : extH (Rep.res (galRes k K L) M) 1),
      extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h₁
        = extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h₂ →
      lam L h₁ = lam L h₂ := by
  intro L _instNF _instFD _instGal w' hw' h₁ h₂ hres
  -- the `hloc` witness at the level `L`
  obtain ⟨w'', hw'', hkill⟩ := hloc L
  -- a place of `k` below `w`; `w'` and `w''` lie over it, hence are conjugate
  obtain ⟨v, hwv⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := k) (L := K) w
  have hw'v : NK.GlobalCFT.Place.LiesOver w' v :=
    place_liesOver_trans (K := k) (L := K) (M := ↥L) hw' hwv
  have hw''v : NK.GlobalCFT.Place.LiesOver w'' v :=
    place_liesOver_trans (K := k) (L := K) (M := ↥L) hw'' hwv
  obtain ⟨g, hg⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver (K := k) (L := ↥L) hw'v hw''v
  have hstab : MulAction.stabilizer (L ≃ₐ[k] L) w'' =
      (MulAction.stabilizer (L ≃ₐ[k] L) w').map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g w'
  -- `h₁ - h₂` restricts to `0` on the stabiliser of `w'`
  have hkey : extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') (h₁ - h₂) = 0 := by
    have hh : extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') ((h₁ - h₂) + h₂)
        = extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h₂ := by
      rw [sub_add_cancel]
      exact hres
    rw [extHRestrict_add] at hh
    have h2 : extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') (h₁ - h₂)
        = extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h₂
          - extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h₂ :=
      eq_sub_iff_add_eq.mpr hh
    rwa [sub_self] at h2
  -- hence also on the stabiliser of `w''`
  have hkey'' : extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w'') (h₁ - h₂) = 0 := by
    rw [hstab]
    exact extHRestrict_conj_eq_zero (MulAction.stabilizer (L ≃ₐ[k] L) w') g (h₁ - h₂) hkey
  -- `hloc` kills `h₁ - h₂`, and additivity of `lam L` finishes
  have hz : lam L (h₁ - h₂) = 0 := hkill (h₁ - h₂) hkey''
  have hsum : lam L h₁ = lam L (h₁ - h₂) + lam L h₂ := by
    have h := map_add (lam L) (h₁ - h₂) h₂
    rw [sub_add_cancel] at h
    exact h
  rw [hsum, hz, zero_add]

end Work.SSGRoute
