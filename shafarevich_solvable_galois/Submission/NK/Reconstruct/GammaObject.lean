import Submission.NK.Reconstruct.ellPart
import Submission.NK.Reconstruct.ellPart_map_le
import Submission.NK.Reconstruct.normal_restrictLevelTo
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Γ_K`: the ℓ-adic abelianisation of an absolute Galois group as a profinite group

This file builds the *object* `Γ_K` of Shimizu's §4 (arXiv:2009.10431) — the ℓ-part `Γ_{L,ℓ}` of
the abelianisation `Gal(L/K)^{ab}` of the finite Galois levels `L/K`, assembled into the projective
limit

  `NK.Reconstruct.Gamma K K' ℓ  =  lim_{L} ℓ-part(Gal(L/K)^{ab})`,

where `L` runs over the finite normal number-field levels of `K'` over `K`
(`NK.Reconstruct.FrobLevel`), with the *restriction maps* `Γ_{M,ℓ} → Γ_{L,ℓ}` for `L ⊆ M`
(`NK.Reconstruct.ellRestrict`) as transition maps.

`Gamma K K' ℓ` is therefore *the ℓ-part of the abelianisation of `G_K` as a profinite quotient*: a
profinite abelian group (`NK.Reconstruct.gammaProfiniteGrp`) admitting projections onto every
finite level, and — up to the identification of the ℓ-part of the abelianisation with its
torsion-free quotient — equal to Shimizu's `Γ_K = G_K^{ab,(ℓ),/tor}`.  The ℓ-rank of `Gamma` is
`NK.Reconstruct.rankGamma` (`Gamma.lean`), and its finiteness properties are governed by the
class-field-theory input `NK.Reconstruct.RankFormulaInput`.

## The projective system

* `levelTo L M h` — the level `L` viewed as an intermediate field of `M`;
* `normal_levelTo` — normality of `L` inside `M`;
* `levelToEquiv L M h` — the identification `↥(levelTo L M h) ≃ₐ[K] ↥L`;
* `levelRestrictHom L M h` — the restriction `Gal(M/K) →* Gal(L/K)`;
* `levelRestrict L M h` — the induced map `Gal(M/K)^{ab} →* Gal(L/K)^{ab}` on abelianisations;
* `ellRestrict ℓ L M h` — its restriction to the ℓ-primary parts.

## The limit

* `Compatible ℓ f` — the coherence condition defining the projective limit;
* `Gamma K K' ℓ` — the limit, as the subgroup of the product of the finite ℓ-parts cut out by the
  coherence condition.  It carries the product topology; it is a profinite abelian group with the
  universal property `NK.Reconstruct.ext`.
* `proj L` — the projection `Γ_K →* Γ_{L,ℓ}`.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3 and Ch. XII;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false

namespace NK.Reconstruct

open scoped Pointwise

/-! ## The transition maps of the projective system -/

section Transition

variable {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K'] [IsGalois K K']

/-- The level `L` of `K'` viewed as an intermediate field of a larger level `M`. -/
abbrev levelTo (L M : FrobLevel K K') (h : L.L ≤ M.L) : IntermediateField K ↥M.L :=
  restrictLevelTo L.L M.L h

/-- **Normality of a level inside a larger one.**  If `L/K` is normal and `L ⊆ M`, then `L` is a
normal intermediate field of `M/K`. -/
theorem normal_levelTo (L M : FrobLevel K K') (h : L.L ≤ M.L) :
    Normal K (levelTo L M h) := by
  classical
  have heq : IntermediateField.lift (levelTo L M h) = L.L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, h hx⟩, hx, rfl⟩
  haveI : Normal K ↥(IntermediateField.lift (levelTo L M h)) :=
    heq.symm ▸ (inferInstance : Normal K ↥L.L)
  exact Normal.of_algEquiv
    (f := (IntermediateField.liftAlgEquiv (levelTo L M h)).symm)

/-- The identification of the level `L ⊆ M` with `L` itself. -/
noncomputable def levelToEquiv (L M : FrobLevel K K') (h : L.L ≤ M.L) :
    ↥(levelTo L M h) ≃ₐ[K] ↥L.L where
  toFun x := ⟨(x : ↥M.L).1, x.2⟩
  invFun y := ⟨⟨y.1, h y.2⟩, y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_mul' x y := rfl
  map_add' x y := rfl
  commutes' c := rfl

/-- Conjugation by an algebra isomorphism, as a homomorphism of automorphism groups. -/
noncomputable def algEquivConjHom {F X Y : Type*} [Field F] [Field X] [Field Y] [Algebra F X]
    [Algebra F Y] (e : X ≃ₐ[F] Y) : (X ≃ₐ[F] X) →* (Y ≃ₐ[F] Y) where
  toFun τ := e.symm.trans (τ.trans e)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp [AlgEquiv.mul_apply]

/-- **The transition map of the projective system, group level**: the restriction
`Gal(M/K) →* Gal(L/K)` for `L ⊆ M`. -/
noncomputable def levelRestrictHom (L M : FrobLevel K K') (h : L.L ≤ M.L) :
    Gal(↥M.L/K) →* Gal(↥L.L/K) :=
  haveI := normal_levelTo L M h
  (algEquivConjHom (levelToEquiv L M h)).comp
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M.L) (levelTo L M h))

/-- **The transition map of the projective system**: the induced map
`Gal(M/K)^{ab} →* Gal(L/K)^{ab}` on abelianisations, for `L ⊆ M`. -/
noncomputable def levelRestrict (L M : FrobLevel K K') (h : L.L ≤ M.L) :
    LevelAbelianization M.L →* LevelAbelianization L.L :=
  Abelianization.map (levelRestrictHom L M h)

/-- **The transition map of the projective system of ℓ-parts**, Shimizu's
`π_{M/L,ℓ} : Γ_{M,ℓ} → Γ_{L,ℓ}`. -/
noncomputable def ellRestrict (ℓ : ℕ) (L M : FrobLevel K K') (h : L.L ≤ M.L) :
    LevelEllPart M.L ℓ →* LevelEllPart L.L ℓ where
  toFun x := ⟨levelRestrict L M h x,
    ellPart_map_le ℓ (levelRestrict L M h)
      (Subgroup.mem_map_of_mem (levelRestrict L M h) x.2)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

@[simp] theorem ellRestrict_coe (ℓ : ℕ) (L M : FrobLevel K K') (h : L.L ≤ M.L)
    (x : LevelEllPart M.L ℓ) :
    ((ellRestrict ℓ L M h x : LevelEllPart L.L ℓ) : LevelAbelianization L.L)
      = levelRestrict L M h x := rfl

end Transition

/-! ## The projective limit -/

section Limit

variable {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K'] [IsGalois K K']

/-- **The coherence condition of the projective system of ℓ-parts**: a family of elements of the
finite levels is compatible with all the transition maps `ellRestrict`. -/
def Compatible (ℓ : ℕ) (f : ∀ L : FrobLevel K K', LevelEllPart L.L ℓ) : Prop :=
  ∀ (L M : FrobLevel K K') (h : L.L ≤ M.L), ellRestrict ℓ L M h (f M) = f L

/-- **`Γ_K`, the ℓ-adic abelianisation of `G_K`, as the projective limit of the finite ℓ-parts**
(Shimizu's `Γ_K = G_K^{ab,(ℓ),/tor}`). -/
def GammaSubgroup (ℓ : ℕ) : Subgroup (∀ L : FrobLevel K K', LevelEllPart L.L ℓ) where
  carrier := {f | Compatible ℓ f}
  mul_mem' := by
    intro f g hf hg L M h
    show ellRestrict ℓ L M h (f M * g M) = f L * g L
    rw [map_mul, hf L M h, hg L M h]
  one_mem' := by
    intro L M h
    show ellRestrict ℓ L M h 1 = 1
    rw [map_one]
  inv_mem' := by
    intro f hf L M h
    show ellRestrict ℓ L M h ((f M))⁻¹ = (f L)⁻¹
    rw [map_inv, hf L M h]

end Limit

/-- **Shimizu's `Γ_K`**: the ℓ-part of the abelianisation of `G_K`, as the projective limit of the
ℓ-parts of the abelianisations of the finite Galois levels of `K'` over `K`. -/
abbrev Gamma (K : Type*) [Field K] (K' : Type*) [Field K'] [Algebra K K'] [IsGalois K K']
    (ℓ : ℕ) : Type _ := ↥(GammaSubgroup (K := K) (K' := K') ℓ)

namespace Gamma

variable {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K'] [IsGalois K K'] {ℓ : ℕ}

/-- **The projection of `Γ_K` to a finite level** (`Γ_K → Γ_{L,ℓ}`). -/
noncomputable def proj (L : FrobLevel K K') : Gamma K K' ℓ →* LevelEllPart L.L ℓ where
  toFun f := f.1 L
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem proj_apply (L : FrobLevel K K') (f : Gamma K K' ℓ) : proj L f = f.1 L := rfl

/-- **The universal property of `Γ_K`**: two elements of the projective limit are equal as soon as
they have the same projections. -/
theorem ext {f g : Gamma K K' ℓ} (h : ∀ L : FrobLevel K K', Gamma.proj L f = Gamma.proj L g) :
    f = g :=
  Subtype.ext (funext (fun L => h L))

/-- The defining property of the projective limit: the elements of `Γ_K` are coherent families. -/
theorem proj_compatible (L M : FrobLevel K K') (h : L.L ≤ M.L) (f : Gamma K K' ℓ) :
    ellRestrict ℓ L M h (proj M f) = proj L f := f.2 L M h

/-- **The universal property of `Γ_K`, existence form**: a coherent family of elements of the
finite levels is an element of `Γ_K`. -/
def mk (f : ∀ L : FrobLevel K K', LevelEllPart L.L ℓ) (hf : Compatible ℓ f) : Gamma K K' ℓ :=
  ⟨f, hf⟩

@[simp] theorem proj_mk (f : ∀ L : FrobLevel K K', LevelEllPart L.L ℓ)
    (hf : Compatible ℓ f) (L : FrobLevel K K') : proj L (mk f hf) = f L := rfl

end Gamma

/-! ## The topology: `Γ_K` is a profinite group -/

section Topology

variable {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K'] [IsGalois K K']

/-- Each finite level carries the discrete topology: `Γ_{L,ℓ}` is a finite group. -/
instance instTopologicalSpaceLevelEllPart (L : IntermediateField K K') (ℓ : ℕ) :
    TopologicalSpace (LevelEllPart L ℓ) := ⊥

instance instDiscreteTopologyLevelEllPart (L : IntermediateField K K') (ℓ : ℕ) :
    DiscreteTopology (LevelEllPart L ℓ) := ⟨rfl⟩

/-- The carrier of `Γ_K` is closed in the product of the finite levels (it is cut out by
equalities of continuous maps). -/
theorem isClosed_gamma (ℓ : ℕ) :
    IsClosed ((GammaSubgroup (K := K) (K' := K') ℓ :
      Subgroup (∀ L : FrobLevel K K', LevelEllPart L.L ℓ)) :
      Set (∀ L : FrobLevel K K', LevelEllPart L.L ℓ)) := by
  have hset : ((GammaSubgroup (K := K) (K' := K') ℓ : Subgroup _) : Set _) =
      ⋂ (L : FrobLevel K K') (M : FrobLevel K K') (h : L.L ≤ M.L),
        {f : ∀ L : FrobLevel K K', LevelEllPart L.L ℓ |
          ellRestrict ℓ L M h (f M) = f L} := by
    ext f
    simp only [Subgroup.mem_carrier, Set.mem_iInter, Set.mem_setOf_eq, Compatible]
    exact ⟨fun h L M hh => h L M hh, fun h L M hh => h L M hh⟩
  rw [hset]
  refine isClosed_iInter (fun L => isClosed_iInter (fun M => isClosed_iInter (fun h => ?_)))
  exact isClosed_eq ((continuous_of_discreteTopology).comp (continuous_apply M))
    (continuous_apply L)

/-- **`Γ_K` is compact**: it is a closed subgroup of the product of the finite (hence compact)
level groups. -/
instance instCompactSpaceGamma (ℓ : ℕ) : CompactSpace (Gamma K K' ℓ) :=
  isCompact_iff_compactSpace.mp (isClosed_gamma (K := K) (K' := K') ℓ).isCompact

/-- **The projections of `Γ_K` are continuous** (the topology of the limit is the initial one). -/
theorem continuous_proj (ℓ : ℕ) (L : FrobLevel K K') :
    Continuous ⇑(Gamma.proj (K := K) (K' := K') (ℓ := ℓ) L) := by
  show Continuous (fun f : Gamma K K' ℓ => f.1 L)
  exact (continuous_apply L).comp continuous_subtype_val

/-- **`Γ_K` is a profinite group.** -/
noncomputable def gammaProfiniteGrp (ℓ : ℕ) : ProfiniteGrp :=
  ProfiniteGrp.of (Gamma K K' ℓ)

end Topology

end NK.Reconstruct
