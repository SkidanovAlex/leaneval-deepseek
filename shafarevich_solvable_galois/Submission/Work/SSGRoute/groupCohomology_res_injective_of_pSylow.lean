import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

universe u

section Aux

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]

/-- The naive restriction of a `1`-cocycle along the inclusion of a subgroup. -/
noncomputable def resCocycle₁ (S : Subgroup G) (M : Rep k G)
    (f : groupCohomology.cocycles₁ M) :
    groupCohomology.cocycles₁ (Rep.res S.subtype M) :=
  ⟨fun s => f s.1, by
    rw [groupCohomology.mem_cocycles₁_iff]
    intro a b
    have h := (groupCohomology.mem_cocycles₁_iff (A := M) f).1 f.2 a.1 b.1
    simpa [Rep.res_obj_ρ, MonoidHom.comp_apply] using h⟩

lemma resCocycle₁_apply (S : Subgroup G) (M : Rep k G) (f : groupCohomology.cocycles₁ M)
    (s : ↥S) : resCocycle₁ S M f s = f s.1 := rfl

/-- The cocycle-level restriction map `mapCocycles₁` along the inclusion of a subgroup `S ≤ G`,
applied to the identity representation morphism, is the naive restriction of a `1`-cocycle. -/
lemma mapCocycles1_subtype_id_apply (S : Subgroup G) (M : Rep k G)
    (f : groupCohomology.cocycles₁ M) (s : ↥S) :
    (groupCohomology.mapCocycles₁ S.subtype (𝟙 (Rep.res S.subtype M)) f) s = f s.1 := by
  rw [groupCohomology.coe_mapCocycles₁]
  simp [groupCohomology.cochainsMap₁, LinearMap.compLeft_apply]

/-- The restriction map `H¹(G, M) → H¹(S, M)` computed on cocycles. -/
lemma resNatTrans_H1π_subtype (S : Subgroup G) (M : Rep k G)
    (f : groupCohomology.cocycles₁ M) :
    (groupCohomology.resNatTrans k (G := ↥S) (H := G) S.subtype 1).app M
        (groupCohomology.H1π M f)
      = groupCohomology.H1π (Rep.res S.subtype M) (resCocycle₁ S M f) := by
  have h := groupCohomology.H1π_comp_map_apply (A := M) (B := Rep.res S.subtype M)
    S.subtype (𝟙 (Rep.res S.subtype M)) f
  have h2 : groupCohomology.mapCocycles₁ S.subtype (𝟙 (Rep.res S.subtype M)) f
      = resCocycle₁ S M f := by
    apply Subtype.ext
    funext s
    exact mapCocycles1_subtype_id_apply S M f s
  rw [h2] at h
  exact h

/-- **The transfer identity in degree one, at the level of cocycles.**

A `1`-cocycle `f` on `G` with values in a `k`-representation `M` that vanishes on a subgroup
`S ≤ G` whose index is a unit of `k` is a coboundary.

`f` is constant on the right cosets of `S`.  Summing the cocycle identity
`f (g * x) = ρ g (f x) + f g` over a transversal `x` of the coset space `G ⧸ S` and reindexing by
the permutation `x ↦ g • x` of the coset space gives `[G : S] • f g = Σ - ρ g Σ`, where
`Σ = ∑ x, f x`; since the index is a unit of `k`, `f` is the coboundary of `-u • Σ`, where
`u * [G : S] = 1`. -/
theorem cocycle_vanishes_on_subgroup_mem_coboundaries (S : Subgroup G) (M : Rep k G)
    (hu : IsUnit ((S.index : k))) (f : groupCohomology.cocycles₁ M)
    (hvan : ∀ s : ↥S, f s.1 = 0) :
    ⇑f ∈ groupCohomology.coboundaries₁ M := by
  classical
  haveI : Fintype (G ⧸ S) := Fintype.ofFinite _
  obtain ⟨u, hu1⟩ := hu.exists_left_inv
  -- `f` is constant on the right cosets of `S`.
  have hright : ∀ (x : G) (p : G), p ∈ S → f (x * p) = f x := by
    intro x p hp
    rw [(groupCohomology.mem_cocycles₁_iff f).1 f.2 x p, hvan ⟨p, hp⟩, map_zero, zero_add]
  -- the sum of `f` over a transversal of the coset space
  set T : M := ∑ c : G ⧸ S, f (Quotient.out c) with hTdef
  -- `g * out c` and `out (g • c)` lie in the same right coset of `S`
  have hcos : ∀ (g : G) (c : G ⧸ S), (Quotient.out (g • c))⁻¹ * (g * Quotient.out c) ∈ S := by
    intro g c
    have h1 : QuotientGroup.mk (g * Quotient.out c) = g • c := by
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rfl
    rw [← QuotientGroup.eq, QuotientGroup.out_eq' (g • c), ← h1]
  have hstep : ∀ (g : G) (c : G ⧸ S), f (g * Quotient.out c) = f (Quotient.out (g • c)) := by
    intro g c
    rw [show g * Quotient.out c
        = Quotient.out (g • c) * ((Quotient.out (g • c))⁻¹ * (g * Quotient.out c)) from by
      group]
    exact hright _ _ (hcos g c)
  -- summing the cocycle identity and reindexing
  have hA : ∀ g : G, (∑ c : G ⧸ S, f (g * Quotient.out c)) = T := by
    intro g
    rw [hTdef]
    rw [show (∑ c : G ⧸ S, f (g * Quotient.out c))
        = ∑ c : G ⧸ S, f (Quotient.out (g • c)) from
      Finset.sum_congr rfl (fun c _ => hstep g c)]
    exact Fintype.sum_bijective (fun c : G ⧸ S => g • c) (MulAction.bijective g) _ _
      (fun c => rfl)
  have hcard : Fintype.card (G ⧸ S) = S.index := by
    rw [Fintype.card_eq_nat_card, ← Subgroup.index_eq_card]
  have hB : ∀ g : G, (∑ c : G ⧸ S, f (g * Quotient.out c))
      = M.ρ g T + (S.index : k) • f g := by
    intro g
    rw [hTdef]
    rw [show (∑ c : G ⧸ S, f (g * Quotient.out c))
        = ∑ c : G ⧸ S, (M.ρ g (f (Quotient.out c)) + f g) from
      Finset.sum_congr rfl
        (fun c _ => (groupCohomology.mem_cocycles₁_iff f).1 f.2 g (Quotient.out c))]
    rw [Finset.sum_add_distrib, map_sum]
    congr 1
    rw [Finset.sum_const, Finset.card_univ, hcard, Nat.cast_smul_eq_nsmul]
  have hmain : ∀ g : G, (S.index : k) • f g = T - M.ρ g T := by
    intro g
    have hunion : T = M.ρ g T + (S.index : k) • f g := (hA g).symm.trans (hB g)
    have : T - M.ρ g T = (S.index : k) • f g := by
      rw [sub_eq_iff_eq_add, add_comm]
      exact hunion
    exact this.symm
  refine LinearMap.mem_range.mpr ⟨-u • T, funext fun g => ?_⟩
  rw [groupCohomology.d₀₁_hom_apply]
  have key : M.ρ g T - T = -((S.index : k) • f g) := by rw [hmain g]; abel
  calc M.ρ g (-u • T) - (-u • T)
      = (-u) • (M.ρ g T - T) := by rw [map_smul, smul_sub]
    _ = (-u) • (-((S.index : k) • f g)) := by rw [key]
    _ = f g := by rw [smul_neg, neg_smul, neg_neg, smul_smul, hu1, one_smul]

end Aux

/-- **The `p`-Sylow reduction for `H¹` with `𝔽_p`-coefficients.**

For a finite group `G`, a prime `p`, a `p`-Sylow subgroup `P ≤ G` and **any** `𝔽_p`-representation
`M` of `G`, the restriction map `H¹(G, M) → H¹(P, M)` is injective.

Proof: the corestriction `cor` satisfies `cor ∘ res = [G : P] · id`
(`Commons.RepresentationTheory.TateCohomology.cor_resNatTrans_comp_apply` in
`Submission/Commons/RepresentationTheory/TateCohomology/natCard_tateCohomology_eq_of_fundamental_class.lean`),
the index `[G : P]` is a unit of `𝔽_p` because `P` is a `p`-Sylow, and `H¹(G, M)` is an
`𝔽_p`-module, so multiplication by `[G : P]` is injective; hence `res` is injective.

Implementation note: the workspace's `cor`/`coindTrace` are written for `M : Rep ℤ G`.  For a
`ZMod p`-representation one may either redo the (coefficient-agnostic) construction over a general
commutative ring `k`, or transport: for a `ZMod p`-module `M` regarded as a `ℤ`-module the
group `H¹(G, M)` (crossed homomorphisms modulo coboundaries) is the same in both spellings, so the
`ℤ`-version of `cor ∘ res = [G : P] · id` transfers.  Either route is acceptable.

This is the first reduction of the Poitou–Tate workshop used by `Work.SSGRoute.coker_obstruction`
(and its sibling `sha2_image_of_Hm2`): it reduces the arithmetic to the case where the relevant
Galois quotient is a `p`-group (the fixed field of a `p`-Sylow of `Gal(K/k)`), where the modules
become unipotent and the Sylow/`p`-group machinery applies. -/
theorem groupCohomology_res_injective_of_pSylow (p : ℕ) [Fact p.Prime] (G : Type) [Group G]
    [Fintype G] (P : Sylow p G) (M : Rep (ZMod p) G) :
    Function.Injective
      ((groupCohomology.resNatTrans (ZMod p) (G := ↥(P : Subgroup G)) (H := G)
        (P : Subgroup G).subtype 1).app M) := by
  classical
  set S : Subgroup G := (P : Subgroup G) with hS
  have hu : IsUnit ((S.index : ZMod p)) := by
    have hndvd : ¬ p ∣ S.index := by
      rw [hS]
      exact Sylow.not_dvd_index P
    refine IsUnit.mk0 _ (fun hzero => hndvd ?_)
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at hzero
    exact hzero
  rw [injective_iff_map_eq_zero]
  intro x hx
  revert hx
  refine groupCohomology.H1_induction_on (A := M)
    (C := fun y => ⇑((groupCohomology.resNatTrans (ZMod p) (G := ↥S) (H := G) S.subtype 1).app M)
      y = 0 → y = 0) x ?_
  intro f hf
  rw [show (groupCohomology.resNatTrans (ZMod p) (G := ↥S) (H := G) S.subtype 1).app M
      (groupCohomology.H1π M f)
      = groupCohomology.H1π (Rep.res S.subtype M) (resCocycle₁ S M f) from
    resNatTrans_H1π_subtype S M f] at hf
  rw [groupCohomology.H1π_eq_zero_iff] at hf
  obtain ⟨b, hb⟩ := hf
  -- `b` is a primitive of the restriction of `f` to `S`
  have hb' : ∀ s : ↥S, M.ρ s.1 b - b = f s.1 := by
    intro s
    have h : ((Rep.res S.subtype M).ρ s) b - b = (resCocycle₁ S M f) s := by
      have h := congrFun hb s
      rwa [groupCohomology.d₀₁_hom_apply] at h
    simpa [resCocycle₁_apply, Rep.res_obj_ρ, MonoidHom.comp_apply] using h
  -- `f - δ(b)` is a cocycle vanishing on `S`
  set f' : G → M := fun g => f g - (M.ρ g b - b) with hf'def
  have hcoc : f' ∈ groupCohomology.cocycles₁ M := by
    have h1 : ⇑f ∈ groupCohomology.cocycles₁ M := f.2
    have h2 : (groupCohomology.d₀₁ M).hom b ∈ groupCohomology.cocycles₁ M :=
      groupCohomology.d₀₁_apply_mem_cocycles₁ b
    have h3 : f' = ⇑f - (groupCohomology.d₀₁ M).hom b := by
      funext g
      show f g - (M.ρ g b - b) = (⇑f - (groupCohomology.d₀₁ M).hom b) g
      rw [Pi.sub_apply, groupCohomology.d₀₁_hom_apply]
    have h4 : ⇑f - (groupCohomology.d₀₁ M).hom b ∈ groupCohomology.cocycles₁ M :=
      sub_mem h1 h2
    exact h3.symm ▸ h4
  have hvan' : ∀ s : ↥S, (⟨f', hcoc⟩ : groupCohomology.cocycles₁ M) s.1 = 0 := by
    intro s
    change f' s.1 = 0
    rw [hf'def]
    exact sub_eq_zero.mpr (hb' s).symm
  have hmem := cocycle_vanishes_on_subgroup_mem_coboundaries S M hu ⟨f', hcoc⟩ hvan'
  rw [groupCohomology.H1π_eq_zero_iff]
  have hfmem : ⇑f ∈ groupCohomology.coboundaries₁ M := by
    have h1 : ⇑f = f' + (groupCohomology.d₀₁ M).hom b := by
      funext g
      show f g = f' g + ((groupCohomology.d₀₁ M).hom b) g
      rw [hf'def, groupCohomology.d₀₁_hom_apply]
      exact (sub_add_cancel _ _).symm
    rw [h1]
    exact add_mem hmem (LinearMap.mem_range.mpr ⟨b, rfl⟩)
  exact hfmem

end Work.SSGRoute
