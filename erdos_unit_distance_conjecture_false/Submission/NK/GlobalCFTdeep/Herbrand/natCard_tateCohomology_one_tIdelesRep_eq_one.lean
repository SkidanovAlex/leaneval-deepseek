/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Shared
import Submission.NK.GlobalCFTdeep.Herbrand.hOne_fiberIdelesRep_eq_one
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_fiberUnitsRep_eq_one
import Submission.NK.GlobalCFTdeep.Herbrand.hZero_hOne_unitIdelesOutsideRep_eq_one
import Submission.NK.GlobalCFTdeep.Herbrand.hZero_localUnitSubRep_of_ramificationIdx_eq_one
import Submission.NK.GlobalCFTdeep.Herbrand.hOne_localUnitSubRep_of_ramificationIdx_eq_one
import Submission.NK.HassePrinciple.subsingleton_classGroupRep_one

/-!
# `Ĥ¹(𝕀_{L,T}) = 0`: the first Tate cohomology of the `T`-idèles vanishes

For a finite cyclic Galois extension `L / K` of number fields, a finite set `S` of places of `K`
containing the archimedean ones and with `T` the set of places of `L` above `S`, the `T`-idèles

  `𝕀_{L,T} = {x ∈ 𝕀_L | x_w ∈ U_w for all w ∉ T}`

have trivial first Tate cohomology.  This is the `Ĥ¹` half of Milne's computation
`h(𝕀_{L,T}) = ∏_{v ∈ S} [L_w : K_v]` (`h = |Ĥ⁰| / |Ĥ¹|`), and the vanishing is *not* a formal
consequence of that quotient identity: it needs the honest arithmetic that
`Ĥ¹(Gal(L/K), 𝕀_{L,T}) = ∏_{v} Ĥ¹(G_v, ...)` and that each local factor vanishes.

## The mathematics

The `T`-idèles split, as `ℤ[Gal(L/K)]`-modules, as

  `𝕀_{L,T} ≅ (∏_{v ∈ S} ∏_{w | v} L_wˣ) × (∏_{v ∉ S} ∏_{w | v} U_w)`,

"keep the components on `T`" times "keep the components outside `T`".  The first factor is the
idèles supported on `T`, whose `Ĥ¹` vanishes because at every place the local field is the
cohomological input of Hilbert's theorem 90 (`hOne_fiberIdelesRep_eq_one`); the second factor is
the unit idèles outside `T`, whose `Ĥ¹` vanishes because every place outside `S` is unramified —
that is hypothesis `hunr` below — and the local units of an unramified local extension have
trivial `Ĥ¹` (`hOne_localUnitSubRep_of_ramificationIdx_eq_one`).

The proof below avoids constructing the isomorphism of `ℤ[G]`-modules and instead decomposes a
multiplicative `1`-cocycle `c : G → 𝕀_{L,T}` into its two projections
`c₁ = «keep on T» ∘ c` and `c₂ = «keep outside T» ∘ c`.  Both are again `1`-cocycles (the two
projections are `G`-equivariant), both are coboundaries by the two vanishing statements, and their
witnesses multiply to a witness for `c`: the whole content of the split decomposition at the level
of `H¹`.  (This is precisely where `H¹` is better behaved than `H²`: the cocycle condition is
componentwise.)

## Main statements

* `NK.GlobalCFTdeep.Herbrand.tdKeepOut`, `...tdKeepOutSub` — the projection "keep the components
  outside `T`", and the identity `tdKeep T x * tdKeepOut T x = x`.
* `NK.GlobalCFTdeep.Herbrand.subsingleton_groupCohomology_one_tIdelesRep` — the decomposition
  argument: `Ĥ¹` of the `T`-idèles vanishes as soon as `Ĥ¹` of the two factors does.
* `NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_one_supportedIdelesRep` and
  `...natCard_tateCohomology_one_unitIdelesOutsideRep` — the two factor computations.
* `NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_one_tIdelesRep_eq_one` — the target.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT
open NK.GlobalCFTdeep
open Additive

/-! ## Transfer between `Ĥ¹` and `H¹`

In degree one the Tate cohomology of a finite group is the ordinary group cohomology, and the two
carry the same subsingleton instances.  Both directions are recorded here so that vanishing
statements can be moved freely between the two languages. -/

section Transfer

variable {G : Type} [Group G] [Fintype G]

/-- Vanishing of `Ĥ¹` implies vanishing of `H¹` in degree one. -/
theorem subsingleton_groupCohomology_one_of_subsingleton_tateCohomology {M : Rep ℤ G}
    (h : Subsingleton (tateCohomology M 1)) : Subsingleton (groupCohomology M 1) := by
  haveI : Subsingleton (tateCohomology M 1) := h
  have e := ((TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 1).app M).toLinearEquiv.toEquiv
  exact ⟨fun a b => e.symm.injective (Subsingleton.elim (e.symm a) (e.symm b))⟩

/-- Vanishing of `H¹` implies vanishing of `Ĥ¹` in degree one. -/
theorem subsingleton_tateCohomology_one_of_subsingleton_groupCohomology {M : Rep ℤ G}
    (h : Subsingleton (groupCohomology M 1)) : Subsingleton (tateCohomology M 1) := by
  haveI : Subsingleton ((groupCohomology.functor ℤ G 1).obj M) := h
  have e := ((TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 1).app M).toLinearEquiv.toEquiv
  exact ⟨fun a b => e.injective (Subsingleton.elim (e a) (e b))⟩

/-- **`Ĥ¹` vanishes iff every multiplicative `1`-cocycle is a coboundary.**  This is the reverse
direction of `NK.HassePrinciple.mulCoboundary_of_subsingleton_groupCohomology_one`: the low
degree API identifies `H¹` with the cocycles modulo the coboundaries, so a statement about all
cocycles is a statement about `H¹`. -/
theorem subsingleton_groupCohomology_one_of_mulCoboundary {G M : Type} [Group G] [CommGroup M]
    [MulDistribMulAction G M]
    (h : ∀ c : G → M, groupCohomology.IsMulCocycle₁ c →
      groupCohomology.IsMulCoboundary₁ (M := M) c) :
    Subsingleton (groupCohomology (Rep.ofMulDistribMulAction G M) 1) := by
  have key : ∀ a : groupCohomology (Rep.ofMulDistribMulAction G M) 1, a = 0 := by
    intro a
    refine groupCohomology.H1_induction_on a (fun x => ?_)
    refine (groupCohomology.H1π_eq_zero_iff x).2 ?_
    let y : G → Additive M := fun g => x.1 g
    have hy : y ∈ groupCohomology.cocycles₁ (Rep.ofMulDistribMulAction G M) := x.2
    have hcoc : groupCohomology.IsMulCocycle₁ (M := M) (fun g => Additive.toMul (y g)) :=
      groupCohomology.isMulCocycle₁_of_mem_cocycles₁ (M := M) (f := y) hy
    obtain ⟨β, hβ⟩ := h _ hcoc
    have hmem : (fun g => Additive.ofMul (Additive.toMul (y g))) ∈
        groupCohomology.coboundaries₁ (Rep.ofMulDistribMulAction G M) :=
      (groupCohomology.coboundariesOfIsMulCoboundary₁
        (f := fun g => Additive.toMul (y g)) ⟨β, hβ⟩).2
    have hfun : (fun g => Additive.ofMul (Additive.toMul (y g))) = x.1 := by
      funext g
      exact ofMul_toMul (y g)
    rwa [hfun] at hmem
  exact ⟨fun a b => by rw [key a, key b]⟩

end Transfer

/-! ## The projection "keep the components outside `T`" -/

section KeepOut

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The underlying function of `tdKeepOut T x`: the components outside `T` of `x`, and `1` on
`T`. -/
def tdKeepOutFun (T : Set (Place L)) (x : Idele L) :
    ∀ w : Place L, (Place.localField L w)ˣ := by
  intro w
  classical
  exact if w ∈ T then 1 else x w

theorem tdKeepOutFun_apply_of_mem {T : Set (Place L)} {w : Place L} (h : w ∈ T)
    (x : Idele L) : tdKeepOutFun T x w = 1 := by
  classical
  exact if_pos h

theorem tdKeepOutFun_apply_of_notMem {T : Set (Place L)} {w : Place L} (h : w ∉ T)
    (x : Idele L) : tdKeepOutFun T x w = x w := by
  classical
  exact if_neg h

/-- The idèle obtained from `x` by putting `1` on `T` and keeping the components outside `T`. -/
def tdKeepOut (T : Set (Place L)) (x : Idele L) : Idele L := by
  classical
  refine ⟨tdKeepOutFun T x, ?_⟩
  rw [Filter.eventually_cofinite]
  refine (Filter.eventually_cofinite.mp x.2).subset ?_
  intro w hw
  rw [Set.mem_ofPred_eq] at hw
  by_cases h : w ∈ T
  · rw [show tdKeepOutFun T x w = 1 from tdKeepOutFun_apply_of_mem h x] at hw
    exact absurd (one_mem (Place.localUnits L w)) hw
  · rw [show tdKeepOutFun T x w = x w from tdKeepOutFun_apply_of_notMem h x] at hw
    exact hw

theorem tdKeepOut_apply_of_mem {T : Set (Place L)} {w : Place L} (h : w ∈ T) (x : Idele L) :
    tdKeepOut T x w = 1 := by
  classical
  change tdKeepOutFun T x w = 1
  exact tdKeepOutFun_apply_of_mem h x

theorem tdKeepOut_apply_of_notMem {T : Set (Place L)} {w : Place L} (h : w ∉ T)
    (x : Idele L) : tdKeepOut T x w = x w := by
  classical
  change tdKeepOutFun T x w = x w
  exact tdKeepOutFun_apply_of_notMem h x

/-- `tdKeepOut T` is a group homomorphism. -/
def tdKeepOutHom (T : Set (Place L)) : Idele L →* Idele L where
  toFun := tdKeepOut T
  map_one' := by
    ext w
    by_cases h : w ∈ T
    · simp only [tdKeepOut_apply_of_mem h, Idele.one_apply]
    · simp only [tdKeepOut_apply_of_notMem h, Idele.one_apply]
  map_mul' := by
    intro x y
    ext w
    by_cases h : w ∈ T
    · simp only [tdKeepOut_apply_of_mem h, Idele.mul_apply, mul_one]
    · simp only [tdKeepOut_apply_of_notMem h, Idele.mul_apply]

/-- `tdKeepOut` is `Gal(L/K)`-equivariant for a `Gal(L/K)`-stable `T`. -/
theorem tdKeepOut_smul {T : Set (Place L)}
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (σ : L ≃ₐ[K] L) (x : Idele L) :
    tdKeepOut T (σ • x) = σ • tdKeepOut T x := by
  ext w
  rw [Idele.smul_apply]
  by_cases h : w ∈ T
  · rw [tdKeepOut_apply_of_mem h, tdKeepOut_apply_of_mem (hT (σ := σ⁻¹) h), map_one]
  · rw [tdKeepOut_apply_of_notMem h,
      tdKeepOut_apply_of_notMem (fun hh => h (by simpa using hT (σ := σ) hh)),
      Idele.smul_apply]

/-- The kept-outside components of a `T`-idèle are local units outside `T`. -/
theorem mem_unitIdelesOutside_tdKeepOut {T : Set (Place L)} {x : Idele L}
    (hx : x ∈ TIdeles T) : tdKeepOut T x ∈ unitIdelesOutside (L := L) T := by
  refine mem_unitIdelesOutside.mpr ⟨fun w hw => tdKeepOut_apply_of_mem hw x, fun w => ?_⟩
  by_cases h : w ∈ T
  · rw [tdKeepOut_apply_of_mem h]
    exact one_mem _
  · rw [tdKeepOut_apply_of_notMem h]
    exact hx w h

/-- **The two projections multiply to the identity**: `x = (x on T) · (x outside T)`. -/
theorem tdKeep_mul_tdKeepOut (T : Set (Place L)) (x : Idele L) :
    NatCardSES.tdKeep T x * tdKeepOut T x = x := by
  ext w
  rw [Idele.mul_apply]
  by_cases h : w ∈ T
  · rw [NatCardSES.tdKeep_apply_of_mem h, tdKeepOut_apply_of_mem h, mul_one]
  · rw [NatCardSES.tdKeep_apply_of_notMem h, tdKeepOut_apply_of_notMem h, one_mul]

/-- The "keep the components outside `T`" projection, as a homomorphism on the `T`-idèles. -/
def tdKeepOutSub (T : Set (Place L)) :
    ↥(TIdeles T) →* ↥(unitIdelesOutside (L := L) T) where
  toFun x := ⟨tdKeepOut T (x : Idele L), mem_unitIdelesOutside_tdKeepOut x.2⟩
  map_one' := Subtype.ext (map_one (tdKeepOutHom T))
  map_mul' x y := Subtype.ext (map_mul (tdKeepOutHom T) (x : Idele L) (y : Idele L))

/-- Equivariance of the projection onto the idèles supported on `T`, in the explicit form in
which it is applied below. -/
theorem tdProjHom_smul {T : Set (Place L)}
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (σ : L ≃ₐ[K] L) (x : ↥(TIdeles T)) :
    NatCardSES.tdProjHom (L := L) T ⟨σ • (x : Idele L), smul_mem_TIdeles hT x.2⟩ =
      ⟨σ • ((NatCardSES.tdProjHom (L := L) T x : ↥(supportedIdeles (L := L) T)) : Idele L),
        smul_mem_supportedIdeles hT (NatCardSES.tdProjHom (L := L) T x).2⟩ := by
  refine Subtype.ext ?_
  exact NatCardSES.tdKeep_smul hT σ (x : Idele L)

/-- Equivariance of the projection "keep the components outside `T`", in the explicit form in
which it is applied below. -/
theorem tdKeepOutSub_smul {T : Set (Place L)}
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (σ : L ≃ₐ[K] L) (x : ↥(TIdeles T)) :
    tdKeepOutSub (L := L) T ⟨σ • (x : Idele L), smul_mem_TIdeles hT x.2⟩ =
      ⟨σ • ((tdKeepOutSub (L := L) T x : ↥(unitIdelesOutside (L := L) T)) : Idele L),
        smul_mem_unitIdelesOutside hT (tdKeepOutSub (L := L) T x).2⟩ := by
  refine Subtype.ext ?_
  exact tdKeepOut_smul hT σ (x : Idele L)

end KeepOut

/-! ## The decomposition of a cocycle

Every multiplicative `1`-cocycle of the `T`-idèles is a coboundary as soon as the same holds for
the idèles supported on `T` and for the unit idèles outside `T`. -/

section Decomposition

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The cocycle decomposition**: `Ĥ¹` of the `T`-idèles vanishes as soon as `Ĥ¹` of the idèles
supported on `T` and `Ĥ¹` of the unit idèles outside `T` do. -/
theorem subsingleton_groupCohomology_one_tIdelesRep (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hA : Subsingleton (groupCohomology (supportedIdelesRep (L := L) T hT) 1))
    (hB : Subsingleton (groupCohomology (unitIdelesOutsideRep (L := L) T hT) 1)) :
    Subsingleton (groupCohomology (tIdelesRep (L := L) T hT) 1) := by
  letI : MulDistribMulAction (L ≃ₐ[K] L) ↥(TIdeles T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (TIdeles T) (fun σ x hx => smul_mem_TIdeles hT hx)
  letI : MulDistribMulAction (L ≃ₐ[K] L) ↥(supportedIdeles (L := L) T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (supportedIdeles (L := L) T)
      (fun σ x hx => smul_mem_supportedIdeles hT hx)
  letI : MulDistribMulAction (L ≃ₐ[K] L) ↥(unitIdelesOutside (L := L) T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (unitIdelesOutside (L := L) T)
      (fun σ x hx => smul_mem_unitIdelesOutside hT hx)
  -- the two vanishing statements, in the language of multiplicative cocycles
  have hAc : ∀ c : (L ≃ₐ[K] L) → ↥(supportedIdeles (L := L) T),
      groupCohomology.IsMulCocycle₁ c →
        groupCohomology.IsMulCoboundary₁ (M := ↥(supportedIdeles (L := L) T)) c :=
    NK.HassePrinciple.mulCoboundary_of_subsingleton_groupCohomology_one hA
  have hBc : ∀ c : (L ≃ₐ[K] L) → ↥(unitIdelesOutside (L := L) T),
      groupCohomology.IsMulCocycle₁ c →
        groupCohomology.IsMulCoboundary₁ (M := ↥(unitIdelesOutside (L := L) T)) c :=
    NK.HassePrinciple.mulCoboundary_of_subsingleton_groupCohomology_one hB
  -- the two projections are equivariant
  have hE1 : ∀ (σ : L ≃ₐ[K] L) (x : ↥(TIdeles T)),
      NatCardSES.tdProjHom (L := L) T (σ • x) =
        σ • NatCardSES.tdProjHom (L := L) T x :=
    fun σ x => tdProjHom_smul (K := K) (L := L) hT σ x
  have hE2 : ∀ (σ : L ≃ₐ[K] L) (x : ↥(TIdeles T)),
      tdKeepOutSub (L := L) T (σ • x) = σ • tdKeepOutSub (L := L) T x :=
    fun σ x => tdKeepOutSub_smul (K := K) (L := L) hT σ x
  -- the decomposition of a cocycle
  have key : ∀ c : (L ≃ₐ[K] L) → ↥(TIdeles T), groupCohomology.IsMulCocycle₁ c →
      groupCohomology.IsMulCoboundary₁ (M := ↥(TIdeles T)) c := by
    intro c hc
    have hc1 : groupCohomology.IsMulCocycle₁
        (fun g => NatCardSES.tdProjHom (L := L) T (c g)) := by
      intro g h
      show NatCardSES.tdProjHom (L := L) T (c (g * h))
        = g • NatCardSES.tdProjHom (L := L) T (c h) * NatCardSES.tdProjHom (L := L) T (c g)
      rw [hc g h, map_mul, hE1]
    have hc2 : groupCohomology.IsMulCocycle₁ (fun g => tdKeepOutSub (L := L) T (c g)) := by
      intro g h
      show tdKeepOutSub (L := L) T (c (g * h))
        = g • tdKeepOutSub (L := L) T (c h) * tdKeepOutSub (L := L) T (c g)
      rw [hc g h, map_mul, hE2]
    obtain ⟨x1, hx1⟩ := hAc _ hc1
    obtain ⟨x2, hx2⟩ := hBc _ hc2
    have hx1' : ∀ g : L ≃ₐ[K] L,
        g • x1 / x1 = NatCardSES.tdProjHom (L := L) T (c g) := fun g => hx1 g
    have hx2' : ∀ g : L ≃ₐ[K] L,
        g • x2 / x2 = tdKeepOutSub (L := L) T (c g) := fun g => hx2 g
    refine ⟨⟨(x1 : Idele L) * (x2 : Idele L),
      mul_mem (supportedIdeles_le_TIdeles T x1.2) (unitIdelesOutside_le_TIdeles T x2.2)⟩, ?_⟩
    intro g
    -- the two witnesses are coboundaries of the two projections
    have hcoe1 : ((g • x1 / x1 : ↥(supportedIdeles (L := L) T)) : Idele L)
        = g • (x1 : Idele L) / (x1 : Idele L) := rfl
    have hcoe2 : ((g • x2 / x2 : ↥(unitIdelesOutside (L := L) T)) : Idele L)
        = g • (x2 : Idele L) / (x2 : Idele L) := rfl
    have h1 : g • (x1 : Idele L) / (x1 : Idele L)
        = (NatCardSES.tdProjHom (L := L) T (c g) : Idele L) := by
      have h := congrArg (fun y : ↥(supportedIdeles (L := L) T) => (y : Idele L)) (hx1' g)
      rw [hcoe1] at h
      exact h
    have h2 : g • (x2 : Idele L) / (x2 : Idele L)
        = (tdKeepOutSub (L := L) T (c g) : Idele L) := by
      have h := congrArg (fun y : ↥(unitIdelesOutside (L := L) T) => (y : Idele L)) (hx2' g)
      rw [hcoe2] at h
      exact h
    -- and the two projections of `c g` multiply to `c g`
    have h3 : (NatCardSES.tdProjHom (L := L) T (c g) : Idele L)
        * (tdKeepOutSub (L := L) T (c g) : Idele L) = (c g : Idele L) := by
      show NatCardSES.tdKeep T (c g : Idele L) * tdKeepOut T (c g : Idele L)
        = (c g : Idele L)
      exact tdKeep_mul_tdKeepOut T (c g : Idele L)
    refine Subtype.ext ?_
    show g • ((x1 : Idele L) * (x2 : Idele L)) / ((x1 : Idele L) * (x2 : Idele L))
      = (c g : Idele L)
    rw [MulDistribMulAction.smul_mul, ← div_mul_div_comm, h1, h2, h3]
  exact subsingleton_groupCohomology_one_of_mulCoboundary (G := L ≃ₐ[K] L)
    (M := ↥(TIdeles T)) key

end Decomposition

/-! ## The two factors have trivial `Ĥ¹` -/

section Factors

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

/-- **The idèles supported on `T` have trivial `Ĥ¹`**: they are the product over `v ∈ S` of the
fibres `∏_{w | v} L_wˣ`, and each fibre has trivial `Ĥ¹` by Hilbert's theorem 90. -/
theorem natCard_tateCohomology_one_supportedIdelesRep
    (S : Finset (NK.GlobalCFT.Place K)) (T : Set (NK.GlobalCFT.Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : NK.GlobalCFT.Place L, w ∈ T ↔ ∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w v) :
    Nat.card (tateCohomology (NK.GlobalCFTdeep.supportedIdelesRep (L := L) T hT) 1) = 1 := by
  rw [natCard_tateCohomology_supportedIdelesRep (K := K) (L := L) S T hT hTS 1, Nat.card_pi]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [← hOne_def]
  exact hOne_fiberIdelesRep_eq_one (K := K) (L := L) (v : NK.GlobalCFT.Place K)

/-- **The unit part of the fibre of a place outside `S` has trivial `Ĥ⁰` and `Ĥ¹`**: such a place
is finite (the archimedean places lie in `S`) and unramified (hypothesis `hunr`), and the local
units of an unramified local extension have trivial `Ĥ⁰` and `Ĥ¹`. -/
theorem natCard_fiberUnitsRep_eq_one_of_notMem
    (S : Finset (NK.GlobalCFT.Place K)) (T : Set (NK.GlobalCFT.Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : NK.GlobalCFT.Place L, w ∈ T ↔ ∃ v ∈ S,
      NK.GlobalCFT.Place.LiesOver w v)
    (hSinf : ∀ a : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite a ∈ S)
    (hunr : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      (∀ v ∈ S, ¬ NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q) v) →
        q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (v : NK.GlobalCFT.Place K) (hv : v ∉ S) :
    Nat.card (tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v) 0) = 1 ∧
      Nat.card (tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v) 1) = 1 := by
  -- the place is nonarchimedean, since the archimedean places lie in `S`
  have hvf : v.IsFinite := by
    rcases v with w | Q
    · exact absurd (hSinf w) hv
    · exact Place.isFinite_ofFinite Q
  obtain ⟨Q, rfl⟩ := Place.isFinite_iff.mp hvf
  -- a place of `L` above `Q`, which is then a finite place
  obtain ⟨w₀, hw₀⟩ := Inclusion.exists_place_liesOver (K := K) (L := L) (Place.ofFinite Q)
  have hw₀f : w₀.IsFinite :=
    (Place.isFinite_of_liesOver hw₀).mpr (Place.isFinite_ofFinite Q)
  obtain ⟨q, rfl⟩ := Place.isFinite_iff.mp hw₀f
  have hqQ : q.asIdeal.LiesOver Q.asIdeal :=
    (Galois.globalCFT_liesOver_ofFinite_iff q Q).mp hw₀
  -- `q` is unramified, since it does not lie above any place of `S`
  have hqT : Place.ofFinite q ∉ T := by
    intro hmem
    obtain ⟨v', hv'S, hv'⟩ := (hTS (Place.ofFinite q)).mp hmem
    have hvu : v' = Place.ofFinite Q := Inclusion.globalCFT_liesOver_unique hv' hw₀
    exact hv (hvu ▸ hv'S)
  have hunrq : q.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    hunr q fun v' hv'S hLies =>
      hqT ((hTS (Place.ofFinite q)).mpr ⟨v', hv'S, hLies⟩)
  haveI : q.asIdeal.LiesOver Q.asIdeal := hqQ
  haveI : Fintype (decompositionSubgroup (K := K) (L := L) (Place.ofFinite q)) :=
    Fintype.ofFinite _
  exact natCard_tateCohomology_fiberUnitsRep_eq_one (K := K) (L := L) (Place.ofFinite Q) q hw₀
    (hZero_localUnitSubRep_of_ramificationIdx_eq_one Q q hunrq)
    (hOne_localUnitSubRep_of_ramificationIdx_eq_one Q q hunrq)

/-- **The unit idèles outside `T` have trivial `Ĥ¹`**: they are the product over the places
`v ∉ S` of the unit parts of the fibres, and every place outside `S` is unramified. -/
theorem natCard_tateCohomology_one_unitIdelesOutsideRep
    (S : Finset (NK.GlobalCFT.Place K)) (T : Set (NK.GlobalCFT.Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : NK.GlobalCFT.Place L, w ∈ T ↔ ∃ v ∈ S,
      NK.GlobalCFT.Place.LiesOver w v)
    (hSinf : ∀ a : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite a ∈ S)
    (hunr : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      (∀ v ∈ S, ¬ NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q) v) →
        q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    Nat.card (tateCohomology (NK.GlobalCFTdeep.unitIdelesOutsideRep (L := L) T hT) 1) = 1 := by
  rw [← hOne_def]
  exact (hZero_hOne_unitIdelesOutsideRep_eq_one (K := K) (L := L) S T hT hTS hSinf
    (fun v hv => natCard_fiberUnitsRep_eq_one_of_notMem S T hT hTS hSinf hunr v hv)).2

end Factors

/-! ## The target -/

theorem natCard_tateCohomology_one_tIdelesRep_eq_one {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (S : Finset (NK.GlobalCFT.Place K)) (T : Set (NK.GlobalCFT.Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : NK.GlobalCFT.Place L, w ∈ T ↔ ∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w v)
    (hSinf : ∀ a : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite a ∈ S)
    (hunr : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      (∀ v ∈ S, ¬ NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q) v) →
        q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    Nat.card (tateCohomology (NK.GlobalCFTdeep.tIdelesRep (L := L) T hT) 1) = 1 := by
  have hSup : Nat.card
      (tateCohomology (NK.GlobalCFTdeep.supportedIdelesRep (L := L) T hT) 1) = 1 :=
    natCard_tateCohomology_one_supportedIdelesRep S T hT hTS
  have hOut : Nat.card
      (tateCohomology (NK.GlobalCFTdeep.unitIdelesOutsideRep (L := L) T hT) 1) = 1 :=
    natCard_tateCohomology_one_unitIdelesOutsideRep S T hT hTS hSinf hunr
  have hSubG : Subsingleton
      (groupCohomology (NK.GlobalCFTdeep.tIdelesRep (L := L) T hT) 1) :=
    subsingleton_groupCohomology_one_tIdelesRep T hT
      (subsingleton_groupCohomology_one_of_subsingleton_tateCohomology
        (Nat.card_eq_one_iff_unique.mp hSup).1)
      (subsingleton_groupCohomology_one_of_subsingleton_tateCohomology
        (Nat.card_eq_one_iff_unique.mp hOut).1)
  exact Nat.card_eq_one_iff_unique.mpr
    ⟨subsingleton_tateCohomology_one_of_subsingleton_groupCohomology hSubG, ⟨0⟩⟩

end NK.GlobalCFTdeep.Herbrand
