import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.Work.SSGRoute.sha2_defs
import Submission.Work.SSGRoute.sha2_level.exists_level_of_locallyConstant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
## The remaining piece: the local conditions (strategy)

The two lemmas below (`locUnits_levelClass_eq_zero_finitePlace`,
`locUnits_levelClass_eq_zero_infinitePlace`, in the sibling modules
`Submission/Work/SSGRoute/sha2_hasse/localConditionsFinite.lean` and `...Infinite.lean`) are the
missing **local comparison**: from the `D_A`-conditions at the finite places and the involution
conditions, one deduces that the class at the level `L` is locally trivial at every place of `L`.

Route (finite places).  Let `w` be a finite place of `L`, `A` a place of `k̄` over `w` (so that
`D_A = decomp k A` is the decomposition group of `A`), and let `E/k` be a finite Galois level
inside `k̄` containing `L` and *the values of a local witness*.  The local witness `b_A : D_A → k̄ˣ`
is locally constant, hence right-invariant under `D_A ∩ G_E` for a suitable finite `E`, and its
values generate a finite extension of `k`; enlarging `E` (taking a Galois closure inside `k̄`) makes
the coboundary identity `d = d¹ b_A` on `D_A` **descend** to the quotient
`Γ^E = D_A/(D_A ∩ G_E) = Stab_{Gal(E/k)}(w_E)`, i.e. `d`, viewed as a cocycle on the decomposition
group of a place `w_E` of `E`, is a coboundary with values in `Eˣ`.  Consequently
`(locUnits k E w_E)([d]_E) = 0` (apply the coefficient map `Eˣ → E_{w_E}ˣ` to the witness).

Since `L ⊆ E`, the tower square `NK.NUV2.ARL.HR.locUnits_inflation_eq` gives
`(locUnits k E w_E)([d]_E) = localLevelMap ((locUnits k L w)([d]_L))`, and
`NK.CFTLib.HR.TransferAux.localLevelMap_injective_vanishing` says that `localLevelMap` is
**injective**.  Hence `(locUnits k L w)([d]_L) = 0`.

Route (archimedean places).  At an infinite place `w` of `L` over an infinite place of `k`, the
decomposition group `Γ_w ≤ Gal(L/k)` has order dividing `2`; when it is trivial the statement is
trivial (`H²(1, L_wˣ) = 0`).  When it has order `2` the relevant involution `σ` of `G_k` is the
complex conjugation at a real place of `k`; the hypothesis `hinv` provides a local witness on
`⟨σ⟩`, and the same "descend to a finite level + tower square + injectivity of `localLevelMap`"
argument applies, with `E_W ∈ {ℝ, ℂ}`.

The library inputs are:

* `NK.NUV2.ARL.HR.locUnits_inflation_eq` (tower square for `locUnits`) and its corollary
  `NK.NUV2.LC.RouteB.locUnits_tower_eq_zero`;
* `NK.CFTLib.HR.TransferAux.localLevelMap_injective_vanishing` (injectivity of the local level map);
* the places of a number field as valuation subrings:
  `Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime`;
* the identification of the decomposition group of a place of `k̄` with the local Galois group:
  `NK.Mine.localGaloisEquiv`, `NK.Mine.adjoinLocalEquiv`.

-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical

namespace Work.SSGRoute.sha2_hasse

open Work.AbsoluteKummer
open CategoryTheory

universe u

/-! ## The explicit cocycle condition and the bridge to Mathlib's `groupCohomology` -/

/-- The explicit (inhomogeneous) `2`-cocycle condition in the convention of
`Work.GroupCohomology` / `Work.AbsoluteKummer.Z2`. -/
def IsCocycle2 {Γ M : Type*} [Group Γ] [AddCommGroup M] [DistribMulAction Γ M]
    (c : Γ × Γ → M) : Prop :=
  ∀ g h l : Γ, c (g * h, l) + c (g, h) = g • c (h, l) + c (g, h * l)

section Bridge

variable {𝕜 Γ : Type u} [CommRing 𝕜] [Group Γ] {A : Rep.{u, u, u} 𝕜 Γ}

/-- Mathlib's `groupCohomology.cocycles₂` is the explicit cocycle condition. -/
theorem mem_cocycles₂_iff (c : Γ × Γ → A.V) :
    c ∈ groupCohomology.cocycles₂ A ↔
      ∀ g h l : Γ, A.ρ g (c (h, l)) - c (g * h, l) + c (g, h * l) - c (g, h) = 0 := by
  rw [groupCohomology.cocycles₂, LinearMap.mem_ker]
  constructor
  · intro h g h' l
    have hh : (ModuleCat.Hom.hom (groupCohomology.d₂₃ A)) c = 0 := h
    have := congrFun hh (g, h', l)
    rw [groupCohomology.d₂₃_hom_apply, Pi.zero_apply] at this
    exact this
  · intro h
    funext p
    obtain ⟨g, h', l⟩ := p
    rw [groupCohomology.d₂₃_hom_apply, Pi.zero_apply]
    exact h g h' l

/-- **The class of an explicit cocycle** in Mathlib's `groupCohomology`. -/
noncomputable def mkClass (A : Rep.{u, u, u} 𝕜 Γ) (c : Γ × Γ → A.V)
    (hc : c ∈ groupCohomology.cocycles₂ A) : groupCohomology A 2 :=
  (ConcreteCategory.hom (groupCohomology.H2π A))
    (show ↥(groupCohomology.cocycles₂ A) from ⟨c, hc⟩)

/-- **The class of an explicit cocycle vanishes iff the cocycle is a coboundary.** -/
theorem mkClass_eq_zero_iff (A : Rep.{u, u, u} 𝕜 Γ) (c : Γ × Γ → A.V)
    (hc : c ∈ groupCohomology.cocycles₂ A) :
    mkClass A c hc = 0 ↔
      ∃ f : Γ → A.V, ∀ g h : Γ, A.ρ g (f h) - f (g * h) + f g = c (g, h) := by
  rw [mkClass, groupCohomology.H2π_eq_zero_iff, groupCohomology.coboundaries₂,
    LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, fun g h => ?_⟩
    have := congrFun hf (g, h)
    rw [groupCohomology.d₁₂_hom_apply] at this
    exact this
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    funext p
    obtain ⟨g, h⟩ := p
    rw [groupCohomology.d₁₂_hom_apply]
    exact hf g h

end Bridge


/-! ## A finite Galois level: the coefficient map and the restriction -/

section Level

variable {k : Type} [Field k] [NumberField k]

/-- The field of a finite Galois level of `k̄/k`. -/
abbrev Lf (L : FiniteGaloisIntermediateField k (AlgebraicClosure k)) : Type :=
  ↥(L : IntermediateField k (AlgebraicClosure k))

section LevelRep

variable {k : Type} [Field k] [NumberField k]

/-- The `Gal(L/k)`-representation `Lˣ` of a finite level, with the universes pinned so that
Mathlib's `groupCohomology` API applies. -/
abbrev levelRepK (L : FiniteGaloisIntermediateField k (AlgebraicClosure k)) :
    Rep.{0, 0, 0} NK.HassePrinciple.CoeffInt (Lf L ≃ₐ[k] Lf L) :=
  NK.HassePrinciple.unitsRep k (Lf L)

end LevelRep

/-- **The coefficient map `Lˣ → k̄ˣ`** of a level, as a homomorphism of additive groups. -/
noncomputable def inclUnits (L : FiniteGaloisIntermediateField k (AlgebraicClosure k)) :
    Additive (Lf L)ˣ →+ Additive (AlgebraicClosure k)ˣ :=
  (Units.map (algebraMap (Lf L) (AlgebraicClosure k)).toMonoidHom).toAdditive

@[simp] theorem inclUnits_toMul (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (x : Additive (Lf L)ˣ) :
    Additive.toMul (inclUnits L x)
      = Units.map (algebraMap (Lf L) (AlgebraicClosure k)).toMonoidHom (Additive.toMul x) := rfl

@[simp] theorem inclUnits_ofMul (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (u : (Lf L)ˣ) :
    inclUnits L (Additive.ofMul u)
      = Additive.ofMul (Units.map (algebraMap (Lf L) (AlgebraicClosure k)).toMonoidHom u) := rfl

theorem inclUnits_injective (L : FiniteGaloisIntermediateField k (AlgebraicClosure k)) :
    Function.Injective (inclUnits L) := by
  intro a b hab
  have h : Units.map (algebraMap (Lf L) (AlgebraicClosure k)).toMonoidHom
      (Additive.toMul a) = Units.map (algebraMap (Lf L) (AlgebraicClosure k)).toMonoidHom
        (Additive.toMul b) :=
    Additive.toMul.injective hab
  exact Additive.toMul.injective
    (Units.map_injective (f := (algebraMap (Lf L) (AlgebraicClosure k)).toMonoidHom)
      (algebraMap (Lf L) (AlgebraicClosure k)).injective h)

/-- **The restriction `G_k → Gal(L/k)`** to a finite Galois level. -/
noncomputable def levelRes (L : FiniteGaloisIntermediateField k (AlgebraicClosure k)) :
    (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →* (Lf L ≃ₐ[k] Lf L) :=
  AlgEquiv.restrictNormalHom (Lf L)

theorem levelRes_surjective (L : FiniteGaloisIntermediateField k (AlgebraicClosure k)) :
    Function.Surjective (levelRes L) := by
  have h := AlgEquiv.restrictNormalHom_surjective (F := k) (E := AlgebraicClosure k) (K₁ := Lf L)
  simpa [levelRes] using h

theorem levelRes_apply (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (x : Lf L) :
    (levelRes L σ x : AlgebraicClosure k) = σ x :=
  AlgEquiv.restrictNormalHom_apply (L : IntermediateField k (AlgebraicClosure k)) σ x

theorem levelRes_mul_apply (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (σ τ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) : levelRes L (σ * τ) = levelRes L σ * levelRes L τ :=
  map_mul _ σ τ

theorem mem_ker_levelRes_iff (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :
    levelRes L σ = 1 ↔ σ ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have h2 := congrArg (fun (γ : Lf L ≃ₐ[k] Lf L) => (γ ⟨x, hx⟩ : AlgebraicClosure k)) h
    simpa [levelRes_apply] using h2
  · intro h
    ext x
    rw [levelRes_apply]
    simpa using h (x : AlgebraicClosure k) x.2

/-- The coefficient map composed with the action of a lift: `g(x) = (g|_L)(x)` on the units of the
level. -/
theorem algEquivUnitsMap_inclUnits (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (g : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (u : (Lf L)ˣ) :
    Work.AbsoluteKummer.algEquivUnitsMap k g
        (Units.map (algebraMap (Lf L) (AlgebraicClosure k)).toMonoidHom u)
      = Units.map (algebraMap (Lf L) (AlgebraicClosure k)).toMonoidHom
          (Units.map (levelRes L g).toMonoidHom u) := by
  apply Units.ext
  rw [Work.AbsoluteKummer.algEquivUnitsMap]
  change (g : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ((u : Lf L) : AlgebraicClosure k)
    = (((levelRes L g) (u : Lf L) : Lf L) : AlgebraicClosure k)
  rw [levelRes_apply]

/-- The equivariance of the coefficient map `Lˣ → k̄ˣ` for the actions of `G_k` and of
`Gal(L/k)`. -/
theorem inclUnits_smul (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (g : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (x : Additive (Lf L)ˣ) :
    inclUnits L ((levelRes L g) • x) = g • inclUnits L x := by
  cases x with
  | ofMul u =>
    apply Additive.toMul.injective
    rw [inclUnits_toMul L, Work.AbsoluteKummer.addUnits_smul_toMul]
    rw [show Additive.toMul (inclUnits L (Additive.ofMul u))
        = Units.map (algebraMap (Lf L) (AlgebraicClosure k)).toMonoidHom u from rfl]
    rw [algEquivUnitsMap_inclUnits L g u]
    congr 1

end Level

/-! ## The descended cocycle of a level and the splitting step -/

section Descend

variable {k : Type} [Field k] [NumberField k]

/-- A chosen lift of an element of `Gal(L/k)` to `G_k`. -/
noncomputable def sec (L : FiniteGaloisIntermediateField k (AlgebraicClosure k)) :
    (Lf L ≃ₐ[k] Lf L) → (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :=
  fun γ => Classical.choose (levelRes_surjective L γ)

theorem levelRes_sec (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (γ : Lf L ≃ₐ[k] Lf L) : levelRes L (sec L γ) = γ :=
  Classical.choose_spec (levelRes_surjective L γ)

/-- Two lifts with the same restriction differ by an element of the fixing subgroup. -/
theorem exists_fixing_mul_sec (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (γ : Lf L ≃ₐ[k] Lf L) (g : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
    (hg : levelRes L g = γ) :
    ∃ u ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup, sec L γ = g * u := by
  refine ⟨g⁻¹ * sec L γ, ?_, (mul_inv_cancel_left g (sec L γ)).symm⟩
  rw [← mem_ker_levelRes_iff, map_mul, map_inv, levelRes_sec, hg, inv_mul_cancel]

/-- **The descended cocycle.** A cochain on `G_k` whose values lie in a level `L` and which is
invariant under `Gal(k̄/L)` descends to a cochain on `Gal(L/k)` with values in `Lˣ`. -/
noncomputable def levelCocycle (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (d : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ)
    (hvals : ∀ g h : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      ∃ x : (Lf L)ˣ, inclUnits L (Additive.ofMul x) = d g h) :
    (Lf L ≃ₐ[k] Lf L) → (Lf L ≃ₐ[k] Lf L) → Additive (Lf L)ˣ :=
  fun γ δ => Classical.choose (hvals (sec L γ) (sec L δ))

theorem levelCocycle_spec (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (d : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ)
    (hvals : ∀ g h : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      ∃ x : (Lf L)ˣ, inclUnits L (Additive.ofMul x) = d g h)
    (γ δ : Lf L ≃ₐ[k] Lf L) :
    inclUnits L (levelCocycle L d hvals γ δ) = d (sec L γ) (sec L δ) :=
  Classical.choose_spec (hvals (sec L γ) (sec L δ))

/-- The value of the descended cocycle is independent of the chosen lifts. -/
theorem levelCocycle_value (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (d : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ)
    (hvals : ∀ g h : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      ∃ x : (Lf L)ˣ, inclUnits L (Additive.ofMul x) = d g h)
    (hfac : ∀ g h u v : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      u ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      v ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      d (g * u) (h * v) = d g h)
    (γ δ : Lf L ≃ₐ[k] Lf L) (g h : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
    (hg : levelRes L g = γ) (hh : levelRes L h = δ) :
    inclUnits L (levelCocycle L d hvals γ δ) = d g h := by
  rw [levelCocycle_spec L d hvals γ δ]
  obtain ⟨u, hu, hsu⟩ := exists_fixing_mul_sec L γ g hg
  obtain ⟨v, hv, hsv⟩ := exists_fixing_mul_sec L δ h hh
  rw [hsu, hsv, hfac g h u v hu hv]

/-- The descended cocycle is a cocycle. -/
theorem levelCocycle_isCocycle (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (d : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ)
    (hvals : ∀ g h : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      ∃ x : (Lf L)ˣ, inclUnits L (Additive.ofMul x) = d g h)
    (hfac : ∀ g h u v : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      u ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      v ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      d (g * u) (h * v) = d g h)
    (hd : ∀ g h l : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      d (g * h) l + d g h = g • d h l + d g (h * l)) :
    ∀ γ δ δ' : Lf L ≃ₐ[k] Lf L,
      levelCocycle L d hvals (γ * δ) δ' + levelCocycle L d hvals γ δ
        = γ • levelCocycle L d hvals δ δ' + levelCocycle L d hvals γ (δ * δ') := by
  intro γ δ δ'
  apply inclUnits_injective L
  have h1 : inclUnits L (levelCocycle L d hvals (γ * δ) δ')
      = d (sec L γ * sec L δ) (sec L δ') :=
    levelCocycle_value L d hvals hfac (γ * δ) δ' (sec L γ * sec L δ) (sec L δ')
      (by rw [map_mul, levelRes_sec, levelRes_sec]) (levelRes_sec L δ')
  have h2 : inclUnits L (levelCocycle L d hvals γ δ) = d (sec L γ) (sec L δ) :=
    levelCocycle_value L d hvals hfac γ δ (sec L γ) (sec L δ) (levelRes_sec L γ) (levelRes_sec L δ)
  have h3 : inclUnits L (levelCocycle L d hvals γ (δ * δ'))
      = d (sec L γ) (sec L δ * sec L δ') :=
    levelCocycle_value L d hvals hfac γ (δ * δ') (sec L γ) (sec L δ * sec L δ')
      (levelRes_sec L γ) (by rw [map_mul, levelRes_sec, levelRes_sec])
  have h4 : inclUnits L (γ • levelCocycle L d hvals δ δ')
      = (sec L γ) • d (sec L δ) (sec L δ') := by
    conv_lhs => rw [← levelRes_sec L γ]
    rw [inclUnits_smul L (sec L γ) (levelCocycle L d hvals δ δ'),
      levelCocycle_spec L d hvals δ δ']
  rw [map_add, map_add, h1, h2, h4, h3]
  exact hd (sec L γ) (sec L δ) (sec L δ')

/-- **The splitting step.** A `2`-cocycle on `Gal(L/k)` with values in `Lˣ` which is a coboundary
lifts to a coboundary on `G_k` with values in `k̄ˣ`. -/
theorem mem_B2_of_levelCoboundary (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (d : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ)
    (dL : (Lf L ≃ₐ[k] Lf L) → (Lf L ≃ₐ[k] Lf L) → Additive (Lf L)ˣ)
    (hpull : ∀ g h, inclUnits L (dL (levelRes L g) (levelRes L h)) = d g h)
    (f : (Lf L ≃ₐ[k] Lf L) → Additive (Lf L)ˣ)
    (hf : ∀ γ δ, dL γ δ = γ • f δ - f (γ * δ) + f γ) :
    (fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => d p.1 p.2)
      ∈ Work.AbsoluteKummer.B2 (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
          (Additive (AlgebraicClosure k)ˣ) := by
  rw [Work.AbsoluteKummer.mem_B2_iff]
  refine ⟨fun g => inclUnits L (f (levelRes L g)), ?_, ?_⟩
  · show Work.AbsoluteKummer.IsLocallyConstant (fun g => inclUnits L (f (levelRes L g)))
    refine Work.AbsoluteKummer.IsLocallyConstant.map (inclUnits L) ?_
    intro g
    refine ⟨{y | g⁻¹ * y ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup},
      ?_, ?_, ?_⟩
    · exact (IntermediateField.fixingSubgroup_isOpen
        (L : IntermediateField k (AlgebraicClosure k))).preimage
        (continuous_const.mul continuous_id)
    · show g⁻¹ * g ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup
      rw [inv_mul_cancel]
      exact Subgroup.one_mem _
    · intro y hy
      show f (levelRes L y) = f (levelRes L g)
      have h1 : levelRes L (g⁻¹ * y) = 1 := (mem_ker_levelRes_iff L (g⁻¹ * y)).mpr hy
      rw [map_mul, map_inv] at h1
      have h2 : levelRes L y = levelRes L g := by
        have h3 := congrArg (fun z => levelRes L g * z) h1
        rwa [mul_inv_cancel_left, mul_one] at h3
      rw [h2]
  · funext p
    obtain ⟨g, h⟩ := p
    show (Work.GroupCohomology.d1 (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
        (Additive (AlgebraicClosure k)ˣ)) (fun g => inclUnits L (f (levelRes L g))) (g, h) = d g h
    rw [Work.GroupCohomology.d1_apply,
      show levelRes L (g * h) = levelRes L g * levelRes L h from map_mul _ _ _,
      ← inclUnits_smul L g (f (levelRes L h)), ← map_sub, ← map_add,
      ← hf (levelRes L g) (levelRes L h), hpull]

end Descend

/-! ## Relative Hasse–Brauer–Noether at a finite level -/

section Hbn

variable {k : Type} [Field k] [NumberField k]

/-- **Relative Hasse–Brauer–Noether** (`NK.GlobalCFTdeep.hbnUnits`) in the explicit-cocycle
language: a `2`-cocycle on `Gal(L/k)` with values in `Lˣ` whose localisation at every place of `L`
vanishes is already zero. -/
theorem exists_levelCoboundary_of_locUnits_vanishing
    (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (c : (Lf L ≃ₐ[k] Lf L) × (Lf L ≃ₐ[k] Lf L) → Additive (Lf L)ˣ)
    (hc : c ∈ groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf L)))
    (hloc : ∀ w : NK.GlobalCFT.Place (Lf L),
      (NK.HassePrinciple.locUnits k (Lf L) w).hom
        (mkClass (NK.HassePrinciple.unitsRep k (Lf L)) c hc) = 0) :
    ∃ f : (Lf L ≃ₐ[k] Lf L) → (NK.HassePrinciple.unitsRep k (Lf L)).V,
      ∀ g h, (NK.HassePrinciple.unitsRep k (Lf L)).ρ g (f h) - f (g * h) + f g = c (g, h) :=
  (mkClass_eq_zero_iff (NK.HassePrinciple.unitsRep k (Lf L)) c hc).mp
    (NK.GlobalCFTdeep.hbnUnits (F := k) (E := Lf L) _
      (fun w => hloc w))

/-- **The class at a finite level** of a cocycle on `G_k` that factors through `L`: the class in
Mathlib's `groupCohomology` of the descended cocycle `levelCocycle`. -/
noncomputable def levelClass (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (d : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ)
    (hvals : ∀ g h : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      ∃ x : (Lf L)ˣ, inclUnits L (Additive.ofMul x) = d g h)
    (hmem : (fun p : (Lf L ≃ₐ[k] Lf L) × (Lf L ≃ₐ[k] Lf L) => levelCocycle L d hvals p.1 p.2)
      ∈ groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf L))) :
    groupCohomology (NK.HassePrinciple.unitsRep k (Lf L)) 2 :=
  mkClass (NK.HassePrinciple.unitsRep k (Lf L))
    (fun p : (Lf L ≃ₐ[k] Lf L) × (Lf L ≃ₐ[k] Lf L) => levelCocycle L d hvals p.1 p.2) hmem

end Hbn

end Work.SSGRoute.sha2_hasse
