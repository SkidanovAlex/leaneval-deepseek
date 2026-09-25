import Mathlib
import Submission.NK.IndecomposedDeep.TrivialTwo

open CategoryTheory Representation groupCohomology

set_option maxHeartbeats 1000000

universe u

namespace NK.IndecomposedDeep

/-! ## Generic coefficient comparison for trivial representations

The two cohomology theories which have to be compared at `p = 2` are defined over *different*
coefficient rings (`NK.BrauerTwist.CoeffInt = ULift ℤ` for the cyclotomic twist,
`NK.BrauerHasse.Coeff p = ULift (ZMod p)` for the trivial coefficients), so Mathlib's
`groupCohomology.map` — which is a map over a fixed ring — cannot compare them directly.

The comparison is therefore made on the *concrete* description of `H²` in terms of 2-cocycles and
2-coboundaries (Mathlib's `groupCohomology.cocycles₂` / `coboundaries₂` and the epimorphism
`groupCohomology.H2π`).  For a trivial representation the cocycle and coboundary conditions are
arithmetic identities in the underlying abelian group, so they are preserved by *any* additive
equivalence of the coefficient groups; this gives the level-wise comparison `H2congr`, which is
natural for `groupCohomology.map` (`H2congr_map`) and preserves the zero class (`H2congr_zero`). -/

section Generic

variable {k k' : Type u} [CommRing k] [CommRing k'] {G : Type u} [Group G]

/-- The inverse of an additive equivalence intertwining two representations is equivariant for the
inverse direction. -/
lemma equivariance_symm {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y)) :
    ∀ (g : G) (y : B.V), e.symm (B.ρ g y) = A.ρ g (e.symm y) := by
  intro g y
  apply e.injective
  rw [he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- `H²(G, A)` is the quotient of the 2-cocycles by the 2-coboundaries, so `H2π` is surjective. -/
lemma H2π_surj (A : Rep k G) : Function.Surjective (H2π A) :=
  (ModuleCat.epi_iff_surjective (H2π A)).1 inferInstance

/-- **The 2-cocycle condition is preserved by an equivariant additive equivalence of coefficients.** -/
lemma mem_cocycles₂_iff {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y)) (f : G × G → A.V) :
    (fun i => e (f i)) ∈ cocycles₂ B ↔ f ∈ cocycles₂ A := by
  rw [mem_cocycles₂_def, mem_cocycles₂_def]
  constructor
  · intro h g hh j
    have key := h g hh j
    rw [← show e (A.ρ g (f (hh, j)) - f (g * hh, j) + f (g, hh * j) - f (g, hh)) =
        B.ρ g (e (f (hh, j))) - e (f (g * hh, j)) + e (f (g, hh * j)) - e (f (g, hh)) from by
      simp only [map_sub, map_add, he]] at key
    exact e.injective (by rw [key, map_zero])
  · intro h g hh j
    rw [← show e (A.ρ g (f (hh, j)) - f (g * hh, j) + f (g, hh * j) - f (g, hh)) =
        B.ρ g (e (f (hh, j))) - e (f (g * hh, j)) + e (f (g, hh * j)) - e (f (g, hh)) from by
      simp only [map_sub, map_add, he], h g hh j, map_zero]

/-- **The 2-coboundary condition is preserved by an equivariant additive equivalence of
coefficients.** -/
lemma mem_coboundaries₂_iff {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y)) (f : G × G → A.V) :
    (fun i => e (f i)) ∈ coboundaries₂ B ↔ f ∈ coboundaries₂ A := by
  rw [coboundaries₂, coboundaries₂, LinearMap.mem_range, LinearMap.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun i => e.symm (x i), ?_⟩
    funext i
    apply e.injective
    rw [show e ((d₁₂ A).hom (fun i => e.symm (x i)) i) =
        (d₁₂ B).hom (fun i => e (e.symm (x i))) i from by
      simp only [d₁₂_hom_apply, map_sub, map_add, he,
        AddEquiv.apply_symm_apply]]
    simp only [AddEquiv.apply_symm_apply]
    exact congrFun hx i
  · rintro ⟨x, hx⟩
    refine ⟨fun i => e (x i), ?_⟩
    funext i
    rw [← hx]
    simp only [d₁₂_hom_apply, map_sub, map_add, he]

/-- The transport of a 2-cocycle along an equivariant additive equivalence of coefficients. -/
def eCocycle {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y)) (x : ↥(cocycles₂ A)) :
    ↥(cocycles₂ B) :=
  ⟨fun i => e (x.1 i), (mem_cocycles₂_iff e he x.1).mpr x.2⟩

@[simp] lemma eCocycle_apply {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y)) (x : ↥(cocycles₂ A)) (i : G × G) :
    (eCocycle e he x : G × G → B.V) i = e (x.1 i) := rfl

lemma eCocycle_val {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y)) (x : ↥(cocycles₂ A)) (i : G × G) :
    (eCocycle e he x).1 i = e (x.1 i) := rfl

lemma eCocycle_coe {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y)) (x : ↥(cocycles₂ A)) :
    ((eCocycle e he x : ↥(cocycles₂ B)) : G × G → B.V) = fun i => e (x.1 i) := rfl

/-- The transport `eCocycle` respects the equivalence relation defining `H²`. -/
lemma H2π_eCocycle_eq {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y))
    {u v : ↥(cocycles₂ A)} (h : (H2π A) u = (H2π A) v) :
    (H2π B) (eCocycle e he u) = (H2π B) (eCocycle e he v) := by
  rw [H2π_eq_iff] at h ⊢
  have hsub : (⇑(eCocycle e he u) : G × G → B.V) - ⇑(eCocycle e he v) =
      fun i => e ((⇑u - ⇑v) i) := by
    rw [eCocycle_coe, eCocycle_coe]
    funext i
    simp only [Pi.sub_apply, map_sub]
    rfl
  rw [hsub]
  exact (mem_coboundaries₂_iff e he (⇑u - ⇑v)).mpr h

/-- **The level comparison `H²(G, A) → H²(G, B)`** of two coefficient systems related by an
equivariant additive equivalence `e` of the coefficient groups. -/
noncomputable def H2congr {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y)) : H2 A → H2 B :=
  fun y => (H2π B) (eCocycle e he (Function.surjInv (H2π_surj A) y))

/-- The computation rule for `H2congr` on a class represented by a cocycle. -/
lemma H2congr_H2π {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y)) (x : ↥(cocycles₂ A)) :
    H2congr e he ((H2π A) x) = (H2π B) (eCocycle e he x) := by
  unfold H2congr
  exact H2π_eCocycle_eq e he (Function.surjInv_eq (H2π_surj A) ((H2π A) x))

lemma eCocycle_zero {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y)) :
    eCocycle e he (0 : ↥(cocycles₂ A)) = 0 := by
  apply Subtype.ext
  show (fun i => e ((0 : ↥(cocycles₂ A)).1 i)) = (0 : G × G → B.V)
  funext i
  show e ((0 : ↥(cocycles₂ A)).1 i) = (0 : G × G → B.V) i
  simp only [Pi.zero_apply, map_zero, Submodule.coe_zero]

lemma eCocycle_symm_apply {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y))
    (he' : ∀ (g : G) (y : B.V), e.symm (B.ρ g y) = A.ρ g (e.symm y))
    (x : ↥(cocycles₂ A)) : eCocycle e.symm he' (eCocycle e he x) = x := by
  apply Subtype.ext
  show (fun i => e.symm (e (x.1 i))) = x.1
  funext i
  rw [AddEquiv.symm_apply_apply]

lemma eCocycle_symm_apply' {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y))
    (he' : ∀ (g : G) (y : B.V), e.symm (B.ρ g y) = A.ρ g (e.symm y))
    (x : ↥(cocycles₂ B)) : eCocycle e he (eCocycle e.symm he' x) = x := by
  apply Subtype.ext
  show (fun i => e (e.symm (x.1 i))) = x.1
  funext i
  rw [AddEquiv.apply_symm_apply]

lemma H2congr_zero {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y)) :
    H2congr e he (0 : H2 A) = 0 := by
  have h0 : (0 : H2 A) = (H2π A) (0 : ↥(cocycles₂ A)) := (map_zero (H2π A).hom).symm
  rw [h0, H2congr_H2π, eCocycle_zero]
  exact map_zero (H2π B).hom

/-- **The level comparison is an equivalence.** -/
noncomputable def H2congrEquiv {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y)) : H2 A ≃ H2 B where
  toFun := H2congr e he
  invFun := H2congr e.symm (equivariance_symm e he)
  left_inv y := by
    obtain ⟨x, rfl⟩ := H2π_surj A y
    rw [H2congr_H2π, H2congr_H2π,
      eCocycle_symm_apply e he (equivariance_symm e he)]
  right_inv y := by
    obtain ⟨x, rfl⟩ := H2π_surj B y
    rw [H2congr_H2π, H2congr_H2π,
      eCocycle_symm_apply' e he (equivariance_symm e he)]

variable {G₀ G₁ : Type u} [Group G₀] [Group G₁]

/-- The computation rule for `mapCocycles₂` on a pair. -/
lemma mapCocycles₂_val {A : Rep k G₀} {B : Rep k G₁} (f : G₁ →* G₀)
    (φ : Rep.res f A ⟶ B) (x : ↥(cocycles₂ A)) (a b : G₁) :
    (mapCocycles₂ f φ x).1 (a, b) = φ.hom (x.1 (f a, f b)) := by
  rw [show (mapCocycles₂ f φ x).1 = (⇑(mapCocycles₂ f φ x) : G₁ × G₁ → B.V) from rfl,
    coe_mapCocycles₂]
  simp [cochainsMap₂]

/-- **Naturality of the level comparison** for a coefficient-compatible pair of representation
maps. -/
lemma H2congr_map (f : G₁ →* G₀)
    {A : Rep k G₀} {B : Rep k G₁} {A' : Rep k' G₀} {B' : Rep k' G₁}
    (φ : Rep.res f A ⟶ B) (ψ : Rep.res f A' ⟶ B')
    (e₀ : A.V ≃+ A'.V) (e₁ : B.V ≃+ B'.V)
    (he₀ : ∀ (g : G₀) (y : A.V), e₀ (A.ρ g y) = A'.ρ g (e₀ y))
    (he₁ : ∀ (g : G₁) (y : B.V), e₁ (B.ρ g y) = B'.ρ g (e₁ y))
    (hφψ : ∀ x : A.V, e₁ (φ.hom x) = ψ.hom (e₀ x))
    (y : H2 A) :
    H2congr e₁ he₁ (groupCohomology.map f φ 2 y) = groupCohomology.map f ψ 2 (H2congr e₀ he₀ y) := by
  obtain ⟨x, rfl⟩ := H2π_surj A y
  rw [H2π_comp_map_apply f φ x, H2congr_H2π, H2congr_H2π,
    H2π_comp_map_apply f ψ (eCocycle e₀ he₀ x)]
  congr 1
  apply Subtype.ext
  show (fun i => e₁ ((mapCocycles₂ f φ x).1 i)) = (mapCocycles₂ f ψ (eCocycle e₀ he₀ x)).1
  funext i
  obtain ⟨a, b⟩ := i
  rw [mapCocycles₂_val f φ x a b, mapCocycles₂_val f ψ (eCocycle e₀ he₀ x) a b,
    eCocycle_val e₀ he₀ x (f a, f b)]
  exact hφψ _

end Generic

/-! ## The coefficient identification `μ_2 ≅ Z/2` -/

section Application

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- In a field of characteristic zero — in particular over a number field — `-1` is a primitive
second root of unity. -/
theorem isPrimitiveRoot_neg_one_algebra (K : Type u) [Field K] [NumberField K] (K' : Type u)
    [Field K'] [Algebra K K'] : IsPrimitiveRoot (-1 : K') 2 := by
  have h : IsPrimitiveRoot (-1 : K) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)
  have h2 := h.map_of_injective (algebraMap K K').injective
  simpa using h2

/-- The number field `K` contains a primitive second root of unity. -/
theorem exists_isPrimitiveRoot_two (K : Type u) [Field K] [NumberField K] :
    ∃ ζ : K, IsPrimitiveRoot ζ 2 :=
  ⟨-1, IsPrimitiveRoot.neg_one 0 (by norm_num)⟩

/-- **`Z/2 ≅ μ_2(K')`**, the additive form of the identification of the trivial coefficient module
with the second roots of unity. -/
noncomputable def ruAddEquiv (K : Type u) [Field K] [NumberField K] (K' : Type u) [Field K']
    [Algebra K K'] : ULift.{u,0} (ZMod 2) ≃+ Additive ↥(rootsOfUnity 2 K') :=
  (AddEquiv.ulift (α := ZMod 2)).trans
    ((IsPrimitiveRoot.zmodEquivZPowers (IsPrimitiveRoot.isUnit_unit (by norm_num)
        (isPrimitiveRoot_neg_one_algebra K K'))).trans
      (MulEquiv.toAdditive (MulEquiv.subgroupCongr (IsPrimitiveRoot.zpowers_eq
        (IsPrimitiveRoot.isUnit_unit (by norm_num) (isPrimitiveRoot_neg_one_algebra K K'))))))

/-- The level module `μ_2(L)` is the whole group `μ_2(K')` of second roots of unity. -/
noncomputable def muTopEquiv (K : Type u) [Field K] [NumberField K] (K' : Type u) [Field K']
    [Algebra K K'] [IsSepClosure K K'] (L : FiniteGaloisIntermediateField K K') :
    ↥(NK.BrauerTwist.muLevel (K := K) (K' := K') 2 L) ≃* ↥(rootsOfUnity 2 K') :=
  (MulEquiv.subgroupCongr (NK.BrauerTwist.muLevel_eq_top_of_isPrimitiveRoot (K := K) (K' := K') L
    (exists_isPrimitiveRoot_two K))).trans Subgroup.topEquiv

/-- **The additive equivalence `μ_2(L) ≃ Z/2`**, used to compare the twisted and the trivial
coefficient systems level by level. -/
noncomputable def muAddEquiv (K : Type u) [Field K] [NumberField K] (K' : Type u) [Field K']
    [Algebra K K'] [IsSepClosure K K'] (L : FiniteGaloisIntermediateField K K') :
    Additive ↥(NK.BrauerTwist.muLevel (K := K) (K' := K') 2 L) ≃+ ULift.{u,0} (ZMod 2) :=
  (MulEquiv.toAdditive (muTopEquiv K K' L)).trans (ruAddEquiv K K').symm

/-- The inclusion `μ_2(L) ↪ μ_2(L')` of level modules corresponds to the identity of `μ_2(K')`
under the identifications `muTopEquiv`. -/
lemma muTopEquiv_muIncl (K : Type u) [Field K] [NumberField K] (K' : Type u) [Field K']
    [Algebra K K'] [IsSepClosure K K'] {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (x : Additive ↥(NK.BrauerTwist.muLevel (K := K) (K' := K') 2 L)) :
    (MulEquiv.toAdditive (muTopEquiv K K' L')) (NK.BrauerTwist.muInclAddHom h x) =
      (MulEquiv.toAdditive (muTopEquiv K K' L)) x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rfl

/-- **Compatibility of `muAddEquiv` with the coefficient inclusions**: the transition maps of the
twisted level system correspond to the identity of `Z/2`. -/
lemma muAddEquiv_muIncl (K : Type u) [Field K] [NumberField K] (K' : Type u) [Field K']
    [Algebra K K'] [IsSepClosure K K'] {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (x : Additive ↥(NK.BrauerTwist.muLevel (K := K) (K' := K') 2 L)) :
    muAddEquiv K K' L' (NK.BrauerTwist.muInclAddHom h x) = muAddEquiv K K' L x := by
  rw [muAddEquiv, muAddEquiv, AddEquiv.trans_apply, AddEquiv.trans_apply,
    muTopEquiv_muIncl K K' h x]

lemma isTrivial_apply_of {k : Type u} [CommRing k] {G V : Type u} [Group G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (h : ρ.IsTrivial) (g : G) (x : V) : ρ g x = x := by
  haveI := h
  exact isTrivial_apply ρ g x

/-- The level representation `NK.BrauerTwist.levelRep` of `μ_2(L)` is trivial. -/
lemma levelRep_ρ_eq (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (g : NK.BrauerHasse.LevelGroup U L)
    (y : Additive ↥(NK.BrauerTwist.muLevel (K := K) (K' := K') 2 L)) :
    (NK.BrauerTwist.levelRep (K := K) (K' := K') 2 U L).ρ g y = y := by
  rw [show (NK.BrauerTwist.levelRep (K := K) (K' := K') 2 U L).ρ g =
      (NK.BrauerTwist.muRep (K := K) (K' := K') 2 L).ρ
        (NK.BrauerTwist.levelGroupHom U L g) from rfl]
  exact isTrivial_apply_of ((NK.BrauerTwist.muRep (K := K) (K' := K') 2 L).ρ)
    (NK.BrauerTwist.muRep_isTrivial_of_isPrimitiveRoot L (exists_isPrimitiveRoot_two K))
    _ y

end Application

/-! ## The levelwise comparison of the twisted and the trivial level systems -/

section LevelCompare

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The twisted level representation `μ_2(L)`, with its `Rep` universe pinned. -/
noncomputable abbrev twistLevelRep (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    Rep.{u,u,u} NK.BrauerTwist.CoeffInt (NK.BrauerHasse.LevelGroup U L) :=
  NK.BrauerTwist.levelRep (K := K) (K' := K') 2 U L

/-- The trivial level representation `Z/2` of the level group. -/
noncomputable abbrev trivLevelRep (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    Rep.{u,u,u} (NK.BrauerHasse.Coeff.{u} 2) (NK.BrauerHasse.LevelGroup U L) :=
  Rep.trivial (NK.BrauerHasse.Coeff.{u} 2) (NK.BrauerHasse.LevelGroup U L)
    (NK.BrauerHasse.Coeff.{u} 2)

lemma H2_map_eq {G₀ G₁ : Type u} [Group G₀] [Group G₁] (f : G₁ →* G₀) :
    NK.BrauerHasse.H2.map (p := 2) f =
      groupCohomology.map f (NK.BrauerHasse.trivHom f) 2 := rfl

/-- The `μ_2(L) ≃ Z/2` identification is equivariant for the (trivial) actions. -/
lemma levelCompare_equivariance (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    ∀ (g : NK.BrauerHasse.LevelGroup U L)
      (y : Additive ↥(NK.BrauerTwist.muLevel (K := K) (K' := K') 2 L)),
      (muAddEquiv K K' L) ((twistLevelRep (K := K) (K' := K') U L).ρ g y) =
        (trivLevelRep U L).ρ g ((muAddEquiv K K' L) y) := by
  intro g y
  rw [levelRep_ρ_eq U L g y]
  rfl

/-- **The levelwise comparison** of the twisted and the trivial level systems. -/
noncomputable def levelCompare (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    NK.BrauerTwist.LevelH2 (K := K) (K' := K') 2 U L ≃
      NK.BrauerHasse.LevelH2 (K := K) (K' := K') 2 U L :=
  H2congrEquiv (A := twistLevelRep (K := K) (K' := K') U L)
    (B := trivLevelRep U L) (muAddEquiv K K' L) (levelCompare_equivariance U L)

/-- **Naturality of the levelwise comparison for the transition maps.** -/
lemma levelCompare_levelMap (U : Subgroup Gal(K'/K)) {L L' : FiniteGaloisIntermediateField K K'}
    (h : L ≤ L') (a : NK.BrauerTwist.LevelH2 (K := K) (K' := K') 2 U L) :
    levelCompare U L' (NK.BrauerTwist.levelMap (K := K) (K' := K') 2 U h a) =
      NK.BrauerHasse.levelMap (K := K) (K' := K') 2 (U := U) h (levelCompare U L a) := by
  show H2congr (muAddEquiv K K' L') (levelCompare_equivariance U L')
        (groupCohomology.map (NK.BrauerHasse.levelQuotHom (U := U) h)
          (NK.BrauerTwist.levelMapCoeff (K := K) (K' := K') 2 U h) 2 a) =
      groupCohomology.map (NK.BrauerHasse.levelQuotHom (U := U) h)
        (NK.BrauerHasse.trivHom (NK.BrauerHasse.levelQuotHom (U := U) h)) 2
        (H2congr (muAddEquiv K K' L) (levelCompare_equivariance U L) a)
  exact H2congr_map (NK.BrauerHasse.levelQuotHom (U := U) h)
    (NK.BrauerTwist.levelMapCoeff (K := K) (K' := K') 2 U h)
    (NK.BrauerHasse.trivHom (NK.BrauerHasse.levelQuotHom (U := U) h))
    (muAddEquiv K K' L) (muAddEquiv K K' L')
    (levelCompare_equivariance U L) (levelCompare_equivariance U L')
    (fun x => by
      change (muAddEquiv K K' L') (NK.BrauerTwist.muInclAddHom h x) = (muAddEquiv K K' L) x
      exact muAddEquiv_muIncl K K' h x) a

/-- **Naturality of the levelwise comparison for the restriction maps.** -/
lemma levelCompare_levelRes {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') (a : NK.BrauerTwist.LevelH2 (K := K) (K' := K') 2 U L) :
    levelCompare V L (NK.HasseTwist.levelRes (K := K) (K' := K') 2 h L a) =
      NK.BrauerHasse.H2.map (NK.BrauerHasse.levelInclHom h L) (levelCompare U L a) := by
  show H2congr (muAddEquiv K K' L) (levelCompare_equivariance V L)
        (groupCohomology.map (NK.BrauerHasse.levelInclHom h L)
          (NK.HasseTwist.levelResCoeff (K := K) (K' := K') 2 h L) 2 a) =
      groupCohomology.map (NK.BrauerHasse.levelInclHom h L)
        (NK.BrauerHasse.trivHom (NK.BrauerHasse.levelInclHom h L)) 2
        (H2congr (muAddEquiv K K' L) (levelCompare_equivariance U L) a)
  exact H2congr_map (NK.BrauerHasse.levelInclHom h L)
    (NK.HasseTwist.levelResCoeff (K := K) (K' := K') 2 h L)
    (NK.BrauerHasse.trivHom (NK.BrauerHasse.levelInclHom h L))
    (muAddEquiv K K' L) (muAddEquiv K K' L)
    (levelCompare_equivariance U L) (levelCompare_equivariance V L)
    (fun x => by
      change (muAddEquiv K K' L) (NK.BrauerTwist.muInclAddHom (le_refl L) x) = (muAddEquiv K K' L) x
      exact muAddEquiv_muIncl K K' (le_refl L) x) a

end LevelCompare

/-! ## The comparison of the two filtered colimits -/

section Colimit

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The twisted localisation at a place is the restriction to the decomposition group.**  Both
sides are the filtered colimit of the same levelwise cohomology, so the identification is
definitional. -/
theorem H2Twist.loc_eq_res (U : Subgroup Gal(K'/K)) (A : NK.BrauerTwist.OverFinitePrime K K')
    (x : NK.BrauerTwist.H2Twist (K := K) (K' := K') 2 U) :
    NK.BrauerTwist.H2Twist.loc (K := K) (K' := K') 2 U x A =
      NK.HasseTwist.H2Twist.res (K := K) (K' := K') 2
        (inf_le_left : U ⊓ NK.BrauerTwist.stabSubgroup A.1 ≤ U) x := by
  obtain ⟨L, a, rfl⟩ := NK.BrauerTwist.H2Twist.ofLevel_surjective (K := K) (K' := K') 2 U x
  rw [NK.BrauerTwist.H2Twist.loc_ofLevel_apply,
    NK.HasseTwist.H2Twist.res_ofLevel]
  rfl

/-- The comparison map from the twisted to the trivial profinite cohomology. -/
noncomputable def compareToFun (U : Subgroup Gal(K'/K)) :
    NK.BrauerTwist.H2Twist (K := K) (K' := K') 2 U →
      NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 U :=
  NK.BrauerTwist.H2Twist.lift (K := K) (K' := K') 2 U
    (fun L a => NK.BrauerHasse.H2Profinite.ofLevel L (levelCompare U L a))
    (by
      intro L L' h a
      rw [levelCompare_levelMap U h a, NK.BrauerHasse.H2Profinite.ofLevel_levelMap])

/-- The comparison map from the trivial to the twisted profinite cohomology. -/
noncomputable def compareInvFun (U : Subgroup Gal(K'/K)) :
    NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 U →
      NK.BrauerTwist.H2Twist (K := K) (K' := K') 2 U :=
  NK.BrauerHasse.H2Profinite.lift (p := 2) (U := U)
    (fun L a => NK.BrauerTwist.H2Twist.ofLevel (K := K) (K' := K') 2 U L
      ((levelCompare U L).symm a))
    (by
      intro L L' h a
      have key : (levelCompare U L').symm (NK.BrauerHasse.levelMap 2 (U := U) h a) =
          NK.BrauerTwist.levelMap (K := K) (K' := K') 2 U h ((levelCompare U L).symm a) := by
        have h1 := levelCompare_levelMap U h ((levelCompare U L).symm a)
        rw [Equiv.apply_symm_apply] at h1
        exact ((levelCompare U L').symm_apply_eq).mpr h1.symm
      rw [key, NK.BrauerTwist.H2Twist.ofLevel_levelMap])

lemma compareToFun_ofLevel (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (a : NK.BrauerTwist.LevelH2 (K := K) (K' := K') 2 U L) :
    compareToFun U (NK.BrauerTwist.H2Twist.ofLevel (K := K) (K' := K') 2 U L a) =
      NK.BrauerHasse.H2Profinite.ofLevel L (levelCompare U L a) := rfl

lemma compareInvFun_ofLevel (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (a : NK.BrauerHasse.LevelH2 (K := K) (K' := K') 2 U L) :
    compareInvFun U (NK.BrauerHasse.H2Profinite.ofLevel L a) =
      NK.BrauerTwist.H2Twist.ofLevel (K := K) (K' := K') 2 U L
        ((levelCompare U L).symm a) := rfl

lemma compare_left_inv (U : Subgroup Gal(K'/K)) :
    Function.LeftInverse (compareInvFun (K := K) (K' := K') U) (compareToFun (K := K) (K' := K') U) := by
  intro x
  obtain ⟨L, a, rfl⟩ := NK.BrauerTwist.H2Twist.ofLevel_surjective (K := K) (K' := K') 2 U x
  rw [compareToFun_ofLevel, compareInvFun_ofLevel, Equiv.symm_apply_apply]

lemma compare_right_inv (U : Subgroup Gal(K'/K)) :
    Function.RightInverse (compareInvFun (K := K) (K' := K') U) (compareToFun (K := K) (K' := K') U) := by
  intro y
  obtain ⟨L, b, rfl⟩ :=
    NK.BrauerHasse.H2Profinite.ofLevel_surjective (p := 2) (U := U) y
  rw [compareInvFun_ofLevel, compareToFun_ofLevel, Equiv.apply_symm_apply]

/-- **The comparison of the twisted and the trivial profinite cohomology at `p = 2`.** -/
noncomputable def compareEquiv (U : Subgroup Gal(K'/K)) :
    NK.BrauerTwist.H2Twist (K := K) (K' := K') 2 U ≃
      NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 U where
  toFun := compareToFun U
  invFun := compareInvFun U
  left_inv := compare_left_inv U
  right_inv := compare_right_inv U

/-- The levelwise comparison sends the zero class to the zero class. -/
lemma levelCompare_zero (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    levelCompare U L (0 : NK.BrauerTwist.LevelH2 (K := K) (K' := K') 2 U L) = 0 :=
  H2congr_zero (A := twistLevelRep (K := K) (K' := K') U L) (B := trivLevelRep U L)
    (muAddEquiv K K' L) (levelCompare_equivariance U L)

lemma compareEquiv_zero (U : Subgroup Gal(K'/K)) :
    compareEquiv (K := K) (K' := K') U (0 : NK.BrauerTwist.H2Twist (K := K) (K' := K') 2 U) = 0 := by
  show compareToFun U (0 : NK.BrauerTwist.H2Twist (K := K) (K' := K') 2 U) = 0
  rw [show (0 : NK.BrauerTwist.H2Twist (K := K) (K' := K') 2 U) =
      NK.BrauerTwist.H2Twist.ofLevel (K := K) (K' := K') 2 U ⊥
        (0 : NK.BrauerTwist.LevelH2 (K := K) (K' := K') 2 U ⊥) from rfl,
    compareToFun_ofLevel, levelCompare_zero]
  rfl

/-- **Naturality of the comparison in the restriction maps.** -/
theorem compareEquiv_res {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (x : NK.BrauerTwist.H2Twist (K := K) (K' := K') 2 U) :
    compareEquiv (K := K) (K' := K') V
        (NK.HasseTwist.H2Twist.res (K := K) (K' := K') 2 h x) =
      NK.LocalDecomposition.H2Profinite.res (K := K) (K' := K') 2 h
        (compareEquiv (K := K) (K' := K') U x) := by
  obtain ⟨L, a, rfl⟩ := NK.BrauerTwist.H2Twist.ofLevel_surjective (K := K) (K' := K') 2 U x
  rw [NK.HasseTwist.H2Twist.res_ofLevel]
  show NK.BrauerHasse.H2Profinite.ofLevel L
      (levelCompare V L (NK.HasseTwist.levelRes (K := K) (K' := K') 2 h L a)) =
    NK.LocalDecomposition.H2Profinite.res (K := K) (K' := K') 2 h
      (NK.BrauerHasse.H2Profinite.ofLevel L (levelCompare U L a))
  rw [NK.LocalDecomposition.H2Profinite.res_ofLevel]
  show NK.BrauerHasse.H2Profinite.ofLevel L
      (levelCompare V L (NK.HasseTwist.levelRes (K := K) (K' := K') 2 h L a)) =
    NK.BrauerHasse.H2Profinite.ofLevel L
      (NK.BrauerHasse.H2.map (NK.BrauerHasse.levelInclHom h L) (levelCompare U L a))
  rw [levelCompare_levelRes]

/-- **The comparison transfers a non-vanishing local component.** -/
theorem compareEquiv_loc (U : Subgroup Gal(K'/K)) (A : NK.BrauerTwist.OverFinitePrime K K')
    (x : NK.BrauerTwist.H2Twist (K := K) (K' := K') 2 U) :
    NK.BrauerHasse.H2Profinite.loc (K := K) (K' := K') 2 U
        (compareEquiv (K := K) (K' := K') U x) A ≠ 0 →
      NK.BrauerTwist.H2Twist.loc (K := K) (K' := K') 2 U x A ≠ 0 := by
  intro h
  by_contra hzero
  apply h
  have hres : NK.HasseTwist.H2Twist.res (K := K) (K' := K') 2
      (inf_le_left : U ⊓ NK.BrauerTwist.stabSubgroup A.1 ≤ U) x = 0 := by
    rw [← H2Twist.loc_eq_res (K := K) (K' := K') U A x]
    exact hzero
  have h2 := compareEquiv_res (K := K) (K' := K')
    (U := U) (V := U ⊓ NK.BrauerTwist.stabSubgroup A.1)
    (inf_le_left : U ⊓ NK.BrauerTwist.stabSubgroup A.1 ≤ U) x
  rw [hres, compareEquiv_zero] at h2
  rw [NK.LocalDecomposition.loc_eq_res (K := K) (K' := K') 2 U A
    (compareEquiv (K := K) (K' := K') U x)]
  exact h2.symm

end Colimit

/-! ## The theorem -/

/-- **The `μ_2`-twist is trivial in characteristic `≠ 2`.**

At `p = 2` the cyclotomic coefficient module `μ_2 = {±1}` is the trivial `ℤ/2`-module, so the
twisted profinite cohomology `NK.BrauerTwist.H2Twist 2 U` and the trivial-coefficient profinite
cohomology `NK.BrauerHasse.H2Profinite 2 U` agree, naturally in the subgroup `U` and for the
localisation at a place.  This says that the structure `NK.IndecomposedDeep.TwistTwoComparison` of
`Submission/Work/IndecomposedDeep/TrivialTwo.lean` is inhabited; its three fields are
`equiv` (the equivalence `H2Twist 2 U ≃ H2Profinite 2 U`),
`equiv_res` (naturality for the restriction maps `NK.HasseTwist.H2Twist.res` and
`NK.LocalDecomposition.H2Profinite.res`) and
`equiv_loc` (a non-vanishing local component `NK.BrauerHasse.H2Profinite.loc` transfers to a
non-vanishing `NK.BrauerTwist.H2Twist.loc`).

The comparison is built level by level: for every finite Galois level `L` the coefficient modules
`μ_2(L) = {±1}` and `ℤ/2` are identified by an additive equivalence (`muAddEquiv`), which is
compatible with the coefficient inclusions (`muAddEquiv_muIncl`); since the level representations
are trivial, this yields an equivalence of the concrete descriptions of `H²` by 2-cocycles modulo
2-coboundaries (`H2congrEquiv`), natural for `groupCohomology.map` (`H2congr_map`).  Collating over
the filtered levels gives `compareEquiv`, and the localisation statement follows from
`H2Twist.loc_eq_res` (the twisted analogue of `NK.LocalDecomposition.loc_eq_res`) and
`compareEquiv_res`. -/
theorem twistTwoComparison (K K' : Type u) [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] : Nonempty (NK.IndecomposedDeep.TwistTwoComparison K K') :=
  ⟨{ equiv := fun U => compareEquiv U
     equiv_res := fun {U V} h x => compareEquiv_res h x
     equiv_loc := fun U A x h => compareEquiv_loc U A x h }⟩

end NK.IndecomposedDeep
