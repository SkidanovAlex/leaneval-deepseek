import Mathlib
import Submission.NK.HassePrinciple.MuColimit
import Submission.NK.BrauerTwist.Profinite

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory Representation groupCohomology

namespace NK.NUV2.ABHN

universe u

variable {K₀ K₁ : Type u} [Field K₀] [Field K₁] [Algebra K₀ K₁]

/-- **Level-wise natural maps induce a map of colimits.**  A family of maps between the level data
of two level systems, compatible with the transition maps, descends to a map of the colimits. -/
noncomputable def levelSystemColimMap (S S' : NK.BrauerTwist.LevelSystem K₀ K₁)
    (f : ∀ L, S.obj L → S'.obj L)
    (hf : ∀ ⦃L L' : FiniteGaloisIntermediateField K₀ K₁⦄ (h : L ≤ L') (a : S.obj L),
      f L' (S.map h a) = S'.map h (f L a)) :
    S.Colim → S'.Colim :=
  S.lift (fun L a => S'.ofLevel L (f L a)) (fun L L' h a => by
    rw [hf h a]
    exact S'.ofLevel_map h (f L a))

@[simp]
lemma levelSystemColimMap_ofLevel (S S' : NK.BrauerTwist.LevelSystem K₀ K₁)
    (f : ∀ L, S.obj L → S'.obj L)
    (hf : ∀ ⦃L L' : FiniteGaloisIntermediateField K₀ K₁⦄ (h : L ≤ L') (a : S.obj L),
      f L' (S.map h a) = S'.map h (f L a))
    (L : FiniteGaloisIntermediateField K₀ K₁) (a : S.obj L) :
    levelSystemColimMap S S' f hf (S.ofLevel L a) = S'.ofLevel L (f L a) := rfl

/-- **A level-wise natural equivalence of level systems induces an equivalence of colimits.** -/
noncomputable def levelSystemColimEquivOfNatEquiv (S S' : NK.BrauerTwist.LevelSystem K₀ K₁)
    (e : ∀ L, S.obj L ≃ S'.obj L)
    (he : ∀ ⦃L L' : FiniteGaloisIntermediateField K₀ K₁⦄ (h : L ≤ L') (a : S.obj L),
      e L' (S.map h a) = S'.map h (e L a)) :
    S.Colim ≃ S'.Colim where
  toFun := levelSystemColimMap S S' (fun L => e L) he
  invFun := levelSystemColimMap S' S (fun L => (e L).symm) (fun L L' h b => by
    have h1 := he h ((e L).symm b)
    rw [Equiv.apply_symm_apply] at h1
    rw [← h1, Equiv.symm_apply_apply])
  left_inv x := by
    obtain ⟨L, a, rfl⟩ := S.ofLevel_surjective x
    simp
  right_inv x := by
    obtain ⟨L, b, rfl⟩ := S'.ofLevel_surjective x
    simp



open NK.BrauerTwist

/-! ## 0. Generic cocycle-level comparison of level cohomologies

The following block is the coefficient-generic machinery comparing `H²` in two coefficient systems
related by an *additive* (not necessarily linear) equivariant equivalence of the coefficient
groups; it is copied from the workspace's `Submission/Work/IndecomposedDeep/twistTwoComparison.lean`
(the `p = 2` comparison of the twisted and trivial coefficient theories), where it is used for
exactly the same purpose.  It is reproduced here because the present file must not import the heavy
`IndecomposedDeep` dependency cone (its instances disturb the typeclass search of the present
proof). -/
section Generic

variable {k k' : Type u} [CommRing k] [CommRing k'] {G : Type u} [Group G]


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

/-! ## 1. The coefficient comparison `μ_p(L) ≅ μ_p(K')^{Gal(K'/L)}` -/

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The underlying element in `K'` of a root of unity in `μ_p(L)` lies in `L`. -/
lemma muLevel_coe_mem (p : ℕ) (L : FiniteGaloisIntermediateField K K') (x : ↥(muLevel p L)) :
    (((x : rootsOfUnity p K') : (K')ˣ) : K') ∈ (L : IntermediateField K K') := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup (L : IntermediateField K K')]
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have h2 : (⟨σ, hσ⟩ : ↥L.fixingSubgroup) • (x : rootsOfUnity p K') =
      (x : rootsOfUnity p K') :=
    (FixedPoints.mem_subgroup (L.fixingSubgroup) (rootsOfUnity p K')
      (x : rootsOfUnity p K')).mp x.2 ⟨σ, hσ⟩
  rw [Subgroup.smul_def] at h2
  have h4 := congrArg (fun t : rootsOfUnity p K' => (t : (K')ˣ)) h2
  rw [coe_smul_rootsOfUnity, AlgEquiv.smul_units_def] at h4
  exact congrArg (fun u : (K')ˣ => (u : K')) h4

/-- The coercion `↥L → K'` is injective. -/
lemma algebraMap_L_injective (L : FiniteGaloisIntermediateField K K') :
    Function.Injective (algebraMap ↥L K') := by
  intro x y h
  apply Subtype.ext
  simpa only [IntermediateField.algebraMap_apply] using h

/-- **The element of `μ_p(L) ⊆ K'` read inside `L`.** -/
noncomputable def toMuLevel (p : ℕ) (L : FiniteGaloisIntermediateField K K')
    (x : ↥(muLevel p L)) : ↥(rootsOfUnity p ↥L) :=
  ⟨Units.mk0 (⟨_, muLevel_coe_mem p L x⟩ : ↥L)
      (by
        intro h
        exact (x : rootsOfUnity p K').1.ne_zero (Subtype.ext_iff.mp h)),
   by
    rw [mem_rootsOfUnity]
    apply Units.ext
    apply Subtype.ext
    rw [Units.val_pow_eq_pow_val]
    show (((x : rootsOfUnity p K') : (K')ˣ) : K') ^ p = (1 : ↥L)
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity p _).mp (x : rootsOfUnity p K').2,
      Units.val_one]
    rfl⟩

/-- **The inclusion `μ_p(L) ↪ μ_p(K')`**, landing in the fixed points of `Gal(K'/L)`: this is the
`K'`-side of the identification of the two descriptions of the level coefficient module. -/
noncomputable def ofMuLevelHom (p : ℕ) (L : FiniteGaloisIntermediateField K K') :
    ↥(rootsOfUnity p ↥L) →* ↥(muLevel p L) where
  toFun y :=
    ⟨⟨Units.map (algebraMap ↥L K').toMonoidHom (y : (↥L)ˣ), by
        rw [mem_rootsOfUnity, ← map_pow, (mem_rootsOfUnity p _).mp y.2, map_one]⟩, by
        rw [FixedPoints.mem_subgroup]
        intro σ
        rw [Subgroup.smul_def]
        apply Subtype.ext
        show (σ : Gal(K'/K)) • Units.map (algebraMap ↥L K').toMonoidHom (y : (↥L)ˣ) =
          Units.map (algebraMap ↥L K').toMonoidHom (y : (↥L)ˣ)
        rw [AlgEquiv.smul_units_def]
        apply Units.ext
        simp only [Units.coe_map]
        exact (IntermediateField.mem_fixingSubgroup_iff L (σ : Gal(K'/K))).mp σ.2
          (((y : (↥L)ˣ) : ↥L) : K') (((y : (↥L)ˣ) : ↥L).2)⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    simp
  map_mul' y z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    simp

lemma ofMuLevelHom_apply (p : ℕ) (L : FiniteGaloisIntermediateField K K')
    (y : ↥(rootsOfUnity p ↥L)) :
    ((ofMuLevelHom p L y : rootsOfUnity p K') : (K')ˣ) =
      Units.map (algebraMap ↥L K').toMonoidHom (y : (↥L)ˣ) := rfl

lemma ofMuLevelHom_injective (p : ℕ) (L : FiniteGaloisIntermediateField K K') :
    Function.Injective (ofMuLevelHom p L) := by
  intro y z h
  have h1 : Units.map (algebraMap ↥L K').toMonoidHom (y : (↥L)ˣ) =
      Units.map (algebraMap ↥L K').toMonoidHom (z : (↥L)ˣ) := by
    have := congrArg (fun w : ↥(muLevel p L) => ((w : rootsOfUnity p K') : (K')ˣ)) h
    simpa only [ofMuLevelHom_apply] using this
  have h2 : (y : (↥L)ˣ) = (z : (↥L)ˣ) :=
    Units.map_injective (algebraMap_L_injective L) h1
  exact Subtype.ext h2

lemma ofMuLevelHom_surjective (p : ℕ) (L : FiniteGaloisIntermediateField K K') :
    Function.Surjective (ofMuLevelHom p L) := by
  intro x
  refine ⟨toMuLevel p L x, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rfl

/-- **The two descriptions of the level coefficient module agree.**  The `p`-th roots of unity in
`L`, realised in `K'` as the fixed points of `Gal(K'/L)`, are the `p`-th roots of unity of `L`. -/
noncomputable def muLevelMulEquiv (p : ℕ) (L : FiniteGaloisIntermediateField K K') :
    ↥(rootsOfUnity p ↥L) ≃* ↥(muLevel p L) :=
  MulEquiv.ofBijective (ofMuLevelHom p L)
    ⟨ofMuLevelHom_injective p L, ofMuLevelHom_surjective p L⟩



/-- **The inclusion `μ_p(L) ↪ μ_p(K')` is equivariant**: the action of `Gal(K'/K)` on the fixed
points in `K'` corresponds to the action of its restriction to `L` on `μ_p(L)`. -/
lemma muLevel_coe_smul (p : ℕ) (L : FiniteGaloisIntermediateField K K') (σ : Gal(K'/K))
    (x : ↥(muLevel p L)) :
    (((σ • x : ↥(muLevel p L)) : rootsOfUnity p K') : (K')ˣ) =
      Units.map σ.toMonoidHom ((x : rootsOfUnity p K') : (K')ˣ) := by
  rw [NK.BrauerTwist.coe_smul_muLevel, NK.BrauerTwist.coe_smul_rootsOfUnity]
  rw [AlgEquiv.smul_units_def]
  rfl

lemma rootsOfUnity_units_coe_smul (p : ℕ) (L : FiniteGaloisIntermediateField K K')
    (σ : Gal(↥L/K)) (y : ↥(rootsOfUnity p ↥L)) :
    ((σ • y : ↥(rootsOfUnity p ↥L)) : (↥L)ˣ) = Units.map σ.toMonoidHom (y : (↥L)ˣ) := by
  rw [NK.HassePrinciple.coe_smul_rootsOfUnity]
  rw [AlgEquiv.smul_units_def]
  rfl

/-- The restriction `Gal(K'/K) →* Gal(L/K)` commutes with the coefficients. -/
lemma units_map_algebraMap_smul (p : ℕ) (L : FiniteGaloisIntermediateField K K')
    (v : Gal(K'/K)) (u : (↥L)ˣ) :
    Units.map (algebraMap ↥L K').toMonoidHom
        (Units.map (NK.HassePrinciple.levelRestrict L v).toMonoidHom u) =
      Units.map v.toMonoidHom (Units.map (algebraMap ↥L K').toMonoidHom u) := by
  apply Units.ext
  simp only [Units.coe_map]
  change (algebraMap ↥L K') ((NK.HassePrinciple.levelRestrict L v) ↑u) =
    v ((algebraMap ↥L K') ↑u)
  rw [IntermediateField.algebraMap_apply]
  simp only [IntermediateField.algebraMap_apply]
  exact AlgEquiv.restrictNormalHom_apply (F := K) (L : IntermediateField K K') v u

/-- **The inclusion `μ_p(L) ↪ μ_p(K')` is equivariant**: the action of `Gal(K'/K)` on the fixed
points in `K'` corresponds to the action of its restriction to `L` on `μ_p(L)`. -/
lemma ofMuLevelHom_smul (p : ℕ) (L : FiniteGaloisIntermediateField K K')
    (v : Gal(K'/K)) (y : ↥(rootsOfUnity p ↥L)) :
    ofMuLevelHom p L (NK.HassePrinciple.levelRestrict L v • y) =
      (v : Gal(K'/K) ⧸ L.fixingSubgroup) • (ofMuLevelHom p L y) := by
  rw [show (v : Gal(K'/K) ⧸ L.fixingSubgroup) • (ofMuLevelHom p L y) =
      v • (ofMuLevelHom p L y) from
    MulAction.coe_quotient_smul_fixedPoints v (ofMuLevelHom p L y)]
  apply Subtype.ext
  apply Subtype.ext
  rw [muLevel_coe_smul]
  rw [ofMuLevelHom_apply]
  rw [show (((NK.HassePrinciple.levelRestrict L v) • y : ↥(rootsOfUnity p ↥L)) : (↥L)ˣ) =
      Units.map (NK.HassePrinciple.levelRestrict L v).toMonoidHom (y : (↥L)ˣ) from
    rootsOfUnity_units_coe_smul p L _ y]
  exact units_map_algebraMap_smul p L v (y : (↥L)ˣ)


/-- **Equivariance of the coefficient comparison** for the level group actions. -/
lemma muLevelMulEquiv_smul (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    ∀ (g : NK.BrauerHasse.LevelGroup V L) (y : Additive ↥(rootsOfUnity p ↥L)),
      (muLevelMulEquiv p L).toAdditive
        ((NK.HassePrinciple.muLevelRep.{u, u} (K := K) (K' := K') p V L).ρ g y) =
      (levelRep.{u, u} (K := K) (K' := K') p V L).ρ g ((muLevelMulEquiv p L).toAdditive y) := by
  intro g y
  induction g using QuotientGroup.induction_on with
  | H v =>
    have h1 : (NK.HassePrinciple.muLevelRep.{u, u} (K := K) (K' := K') p V L).ρ
        (QuotientGroup.mk v) y =
        Additive.ofMul ((NK.HassePrinciple.levelRestrict L (v : Gal(K'/K))) • Additive.toMul y) := rfl
    have h2 : (levelRep.{u, u} (K := K) (K' := K') p V L).ρ (QuotientGroup.mk v)
        ((muLevelMulEquiv p L).toAdditive y) =
        Additive.ofMul (((v : Gal(K'/K)) : Gal(K'/K) ⧸ L.fixingSubgroup) •
          Additive.toMul ((muLevelMulEquiv p L).toAdditive y)) := rfl
    have h3 : ∀ (z : Additive ↥(rootsOfUnity p ↥L)),
        (muLevelMulEquiv p L).toAdditive z = Additive.ofMul (ofMuLevelHom p L (Additive.toMul z)) :=
      fun z => rfl
    rw [h1, h2, h3, h3]
    show Additive.ofMul (ofMuLevelHom p L ((NK.HassePrinciple.levelRestrict L (v : Gal(K'/K))) •
        Additive.toMul y)) =
      Additive.ofMul (((v : Gal(K'/K)) : Gal(K'/K) ⧸ L.fixingSubgroup) •
        ofMuLevelHom p L (Additive.toMul y))
    rw [ofMuLevelHom_smul]

@[simp] lemma muIncl_subtype (p : ℕ) {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (x : ↥(muLevel p L)) :
    ((muIncl h x : ↥(muLevel p L')) : rootsOfUnity p K') = (x : rootsOfUnity p K') := rfl

set_option synthInstance.maxHeartbeats 800000 in
/-- **The comparison of the coefficient modules is compatible with the inclusions.** -/
lemma ofMuLevelHom_incl (p : ℕ) {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (y : ↥(rootsOfUnity p ↥L)) :
    ofMuLevelHom p L' (NK.HassePrinciple.muLevelIncl p L L' h y) =
      muIncl h (ofMuLevelHom p L y) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [muIncl_subtype, ofMuLevelHom_apply, ofMuLevelHom_apply]
  apply Units.ext
  simp only [Units.coe_map]
  change (algebraMap ↥L' K') ((IntermediateField.inclusion h) ((y : (↥L)ˣ) : ↥L)) =
    (algebraMap ↥L K') ((y : (↥L)ˣ) : ↥L)
  rw [IntermediateField.algebraMap_apply, IntermediateField.algebraMap_apply]
  rfl

/-- variant A: via `change` then the inclusion compatibility -/
lemma muLevelMulEquiv_incl_A (p : ℕ) (V : Subgroup Gal(K'/K))
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (x : Additive ↥(rootsOfUnity p ↥L)) :
    (muLevelMulEquiv p L').toAdditive
        ((NK.HassePrinciple.muLevelMapCoeff.{u, u} p V h).hom x) =
      (levelMapCoeff.{u, u} p V h).hom ((muLevelMulEquiv p L).toAdditive x) := by
  change Additive.ofMul (ofMuLevelHom p L'
      (NK.HassePrinciple.muLevelIncl p L L' h (Additive.toMul x))) =
    Additive.ofMul (muIncl h (ofMuLevelHom p L (Additive.toMul x)))
  rw [ofMuLevelHom_incl]

/-- variant C: via `convert` -/
lemma muLevelMulEquiv_incl_C (p : ℕ) (V : Subgroup Gal(K'/K))
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (x : Additive ↥(rootsOfUnity p ↥L)) :
    (muLevelMulEquiv p L').toAdditive
        ((NK.HassePrinciple.muLevelMapCoeff.{u, u} p V h).hom x) =
      (levelMapCoeff.{u, u} p V h).hom ((muLevelMulEquiv p L).toAdditive x) := by
  have h1 : (NK.HassePrinciple.muLevelMapCoeff.{u, u} p V h).hom x =
      NK.HassePrinciple.muLevelInclLinearMap.{u, u} p L L' h x := rfl
  have h2 : (levelMapCoeff.{u, u} p V h).hom ((muLevelMulEquiv p L).toAdditive x) =
      NK.BrauerTwist.muInclLinearMap.{u, u} h ((muLevelMulEquiv p L).toAdditive x) := rfl
  rw [h1, h2]
  change Additive.ofMul (ofMuLevelHom p L'
      (NK.HassePrinciple.muLevelIncl p L L' h (Additive.toMul x))) =
    Additive.ofMul (muIncl h (ofMuLevelHom p L (Additive.toMul x)))
  rw [ofMuLevelHom_incl]

/-! ## 3. The level comparison and its naturality -/

/-- **The levelwise comparison** of the `μ_p` level system of `HassePrinciple` with the one of
`BrauerTwist`. -/
noncomputable def levelCompare (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L ≃
      LevelH2 (K := K) (K' := K') p V L :=
  H2congrEquiv (A := NK.HassePrinciple.muLevelRep.{u, u} (K := K) (K' := K') p V L)
    (B := levelRep.{u, u} (K := K) (K' := K') p V L)
    (muLevelMulEquiv p L).toAdditive
    (muLevelMulEquiv_smul (K := K) (K' := K') p V L)

/-- **Naturality of the levelwise comparison** with respect to the transition maps. -/
lemma levelCompare_nat (p : ℕ) (V : Subgroup Gal(K'/K))
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L) :
    levelCompare p V L' (NK.HassePrinciple.muLevelMap (K := K) (K' := K') p V h a) =
      levelMap (K := K) (K' := K') p V h (levelCompare p V L a) := by
  exact H2congr_map
    (A := NK.HassePrinciple.muLevelRep.{u, u} (K := K) (K' := K') p V L)
    (B := NK.HassePrinciple.muLevelRep.{u, u} (K := K) (K' := K') p V L')
    (A' := levelRep.{u, u} (K := K) (K' := K') p V L)
    (B' := levelRep.{u, u} (K := K) (K' := K') p V L')
    (NK.BrauerHasse.levelQuotHom (U := V) h)
    (NK.HassePrinciple.muLevelMapCoeff.{u, u} (K := K) (K' := K') p V h)
    (levelMapCoeff.{u, u} (K := K) (K' := K') p V h)
    (muLevelMulEquiv p L).toAdditive
    (muLevelMulEquiv p L').toAdditive
    (muLevelMulEquiv_smul (K := K) (K' := K') p V L)
    (muLevelMulEquiv_smul (K := K) (K' := K') p V L')
    (fun x => by
        change (muLevelMulEquiv p L').toAdditive
            ((NK.HassePrinciple.muLevelMapCoeff.{u, u} p V h).hom x) =
          (levelMapCoeff.{u, u} p V h).hom ((muLevelMulEquiv p L).toAdditive x)
        exact muLevelMulEquiv_incl_A (K := K) (K' := K') p V h x) a

/-! ## 4. The comparison of the two colimits -/

set_option synthInstance.maxHeartbeats 800000 in
/-- **The `μ_p`-twisted cohomology of a Galois group is the `μ_p` colimit of this chapter's
vocabulary** (Neukirch's `H²(U, μ_p)` in the coefficients of the cyclotomic twist). -/
theorem h2Twist_muColim_equiv (K : Type) [Field K] (K' : Type) [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (V : Subgroup Gal(K'/K)) :
    Nonempty (NK.BrauerTwist.H2Twist (K := K) (K' := K') p V ≃
      NK.HassePrinciple.MuColim (K := K) (K' := K') p V) :=
  ⟨(levelSystemColimEquivOfNatEquiv
      (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p V)
      (NK.BrauerTwist.twistSystem (K := K) (K' := K') p V)
      (fun L => levelCompare (K := K) (K' := K') p V L)
      (fun L L' h a => levelCompare_nat (K := K) (K' := K') p V h a)).symm⟩

end NK.NUV2.ABHN
