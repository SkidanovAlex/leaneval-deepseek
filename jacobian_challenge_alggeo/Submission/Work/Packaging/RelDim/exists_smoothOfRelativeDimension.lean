import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Packaging.RelDim

universe u

open CategoryTheory AlgebraicGeometry

/-! ## Auxiliary lemmas -/

/-- A standard smooth ring homomorphism admits a relative dimension. -/
lemma exists_isStandardSmoothOfRelativeDimension_of_isStandardSmooth
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (h : φ.IsStandardSmooth) :
    ∃ n, φ.IsStandardSmoothOfRelativeDimension n := by
  letI := φ.toAlgebra
  have h' : Algebra.IsStandardSmooth R S := h
  obtain ⟨ι, σ, _, hι, ⟨P⟩⟩ := h'.out
  exact ⟨P.dimension, RingHom.IsStandardSmoothOfRelativeDimension.toAlgebra P.dimension
    (Algebra.SubmersivePresentation.isStandardSmoothOfRelativeDimension P rfl)⟩

/-- The section ring of an affine open containing a point is nontrivial. -/
lemma nontrivial_sections_of_mem {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) : Nontrivial Γ(X, U) := by
  refine not_subsingleton_iff_nontrivial.mp fun h => ?_
  refine (hU.primeIdealOf ⟨x, hx⟩).isPrime.ne_top (Ideal.ext fun y => ?_)
  rw [Subsingleton.elim y 0]
  exact ⟨fun _ => trivial, fun _ => (hU.primeIdealOf ⟨x, hx⟩).asIdeal.zero_mem⟩

section morphism

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The relative dimension of the restriction of a morphism to a pair of affine opens, phrased on
the level of the induced ring homomorphism. -/
lemma smoothOfRelativeDimension_resLE_iff (n : ℕ) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    SmoothOfRelativeDimension n (f.resLE U V e) ↔
      RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (f.appLE U V e).hom := by
  haveI : IsAffine (V.toScheme) := hV
  haveI : IsAffine (U.toScheme) := hU
  rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))]
  exact RingHom.RespectsIso.arrow_mk_iso_iff
    (RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso)
    (AlgebraicGeometry.arrowResLEAppIso f U V e)

/-- Restricting the picture of a morphism to smaller open sets does not change the relative
dimension. -/
lemma locally_appLE_of_resLE {n : ℕ} {U₁ : Y.Opens} {V₁ : X.Opens} (e₁ : V₁ ≤ f ⁻¹ᵁ U₁)
    (h : SmoothOfRelativeDimension n (f.resLE U₁ V₁ e₁))
    {U : Y.Opens} {W : X.Opens} (e : W ≤ f ⁻¹ᵁ U)
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (hUU₁ : U ≤ U₁) (hWV₁ : W ≤ V₁) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (f.appLE U W e).hom := by
  rw [HasRingHomProperty.iff_appLE (P := @SmoothOfRelativeDimension n)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))] at h
  have hU' : (U₁.ι ''ᵁ (U₁.ι ⁻¹ᵁ U)) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hUU₁]
  have hV' : (V₁.ι ''ᵁ (V₁.ι ⁻¹ᵁ W)) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hWV₁]
  have hO : IsAffineOpen (U₁.ι ⁻¹ᵁ U) :=
    IsAffineOpen.preimage_of_isOpenImmersion hU U₁.ι (by rwa [Scheme.Opens.opensRange_ι])
  have hW' : IsAffineOpen (V₁.ι ⁻¹ᵁ W) :=
    IsAffineOpen.preimage_of_isOpenImmersion hW V₁.ι (by rwa [Scheme.Opens.opensRange_ι])
  have hmem : (V₁.ι ⁻¹ᵁ W) ≤ (f.resLE U₁ V₁ e₁) ⁻¹ᵁ (U₁.ι ⁻¹ᵁ U) := by
    rw [Scheme.Hom.le_resLE_preimage_iff, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_eq_right.mpr hUU₁, inf_eq_right.mpr hWV₁]
    exact e
  have h₁ : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      ((Scheme.Hom.appLE (f.resLE U₁ V₁ e₁) (U₁.ι ⁻¹ᵁ U) (V₁.ι ⁻¹ᵁ W) hmem).hom) :=
    h ⟨U₁.ι ⁻¹ᵁ U, hO⟩ ⟨V₁.ι ⁻¹ᵁ W, hW'⟩ hmem
  rw [Scheme.Hom.resLE_appLE] at h₁
  exact (Scheme.Hom.appLE_congr (f := f)
    ((Scheme.Hom.le_resLE_preimage_iff f e₁ (U₁.ι ⁻¹ᵁ U) (V₁.ι ⁻¹ᵁ W)).mp hmem) hU' hV'
    (fun {R S : CommRingCat.{u}} (g : R ⟶ S) =>
      RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
        (CommRingCat.Hom.hom g))).mp h₁

end morphism

/-- A ring with a prime ideal is nontrivial. -/
private lemma nat_nontrivial_of_isPrime {R : Type*} [CommRing R] {I : Ideal R} (h : I.IsPrime) :
    Nontrivial R := by
  have h1 : (1 : R) ∉ I := h.one_notMem
  by_contra hR
  rw [not_nontrivial_iff_subsingleton] at hR
  haveI := hR
  exact h1 (Subsingleton.elim (1 : R) 0 ▸ I.zero_mem)

/-- If `t` is not in the prime ideal `q`, the localisation away from `t` is nontrivial. -/
private lemma nontrivial_localization_away {B : Type*} [CommRing B] {q : Ideal B} [q.IsPrime]
    {t : B} (ht : t ∉ q) : Nontrivial (Localization.Away t) :=
  nat_nontrivial_of_isPrime
    (IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers t) (Localization.Away t) q
      ‹q.IsPrime› (by rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]; exact ht))

/-- An ideal spanning the unit ideal is not contained in a prime ideal. -/
private lemma exists_mem_notMem_of_span_top {B : Type*} [CommRing B] (q : Ideal B) [q.IsPrime]
    (s : Set B) (hs : Ideal.span s = ⊤) : ∃ g ∈ s, g ∉ q := by
  by_contra h
  push Not at h
  have hle : Ideal.span s ≤ q := Ideal.span_le.mpr (fun y hy => h y hy)
  rw [hs] at hle
  exact (Ideal.IsPrime.ne_top ‹q.IsPrime›) (top_le_iff.mp hle)

/-- Standard smoothness of relative dimension `n` is stable under passing to a further localisation
away from an element of the target. -/
private lemma relDim_away_mul {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ}
    (g h : B)
    (H : RingHom.IsStandardSmoothOfRelativeDimension n
      ((algebraMap B (Localization.Away g)).comp φ)) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      ((algebraMap B (Localization.Away (g * h))).comp φ) := by
  let f0 : A →+* Localization.Away g := (algebraMap B (Localization.Away g)).comp φ
  have H0 : RingHom.IsStandardSmoothOfRelativeDimension n f0 := H
  let C := Localization.Away (algebraMap B (Localization.Away g) h)
  have hCl : IsLocalization.Away (algebraMap B (Localization.Away g) h) C := inferInstance
  have hC : RingHom.IsStandardSmoothOfRelativeDimension n
      ((algebraMap (Localization.Away g) C).comp f0) :=
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
      C (algebraMap B (Localization.Away g) h) f0 H0
  have hT : IsLocalization.Away (g * h) C := inferInstance
  let e : C ≃ₐ[B] Localization.Away (g * h) :=
    IsLocalization.algEquiv (Submonoid.powers (g * h)) C _
  have hres := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).1 _ e.toRingEquiv hC
  convert hres using 2
  ext x
  simp only [RingHom.comp_apply, f0, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_ringEquiv]
  rw [← IsScalarTower.algebraMap_apply B (Localization.Away g) C (φ x)]
  exact (AlgEquiv.commutes e (φ x)).symm

/-- If a ring hom with nontrivial target is standard smooth of relative dimension `n` and of
relative dimension `m`, then `n = m`: both numbers are the rank of the module of Kähler
differentials. -/
private lemma relDim_eq_of_standardSmooth {A C : Type u} [CommRing A] [CommRing C] [Nontrivial C]
    {n m : ℕ} (Ψ : A →+* C)
    (hn : RingHom.IsStandardSmoothOfRelativeDimension n Ψ)
    (hm : RingHom.IsStandardSmoothOfRelativeDimension m Ψ) : n = m := by
  letI : Algebra A C := Ψ.toAlgebra
  have hn' : Algebra.IsStandardSmoothOfRelativeDimension n A C := hn
  have hm' : Algebra.IsStandardSmoothOfRelativeDimension m A C := hm
  have hs : Algebra.IsStandardSmooth A C := hn'.isStandardSmooth
  have h1 := (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth
    (R := A) (S := C) n).mp hn'
  have h2 := (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth
    (R := A) (S := C) m).mp hm'
  exact Nat.cast_injective (h1.symm.trans h2)

/-- **Key lemma.** A ring homomorphism that is locally standard smooth of relative dimension `n`
both for `n` and for `m`, with nontrivial target, satisfies `n = m`. -/
lemma locally_relDim_unique {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    [Nontrivial S] {n m : ℕ}
    (hn : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) φ)
    (hm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension m) φ) : n = m := by
  obtain ⟨q, hq⟩ := Ideal.exists_maximal S
  haveI : q.IsPrime := hq.isPrime
  rw [RingHom.Locally] at hn hm
  obtain ⟨sₙ, hsₙ, hsn⟩ := hn
  obtain ⟨sₘ, hsₘ, hsm⟩ := hm
  obtain ⟨g, hg_mem, hg_notin⟩ := exists_mem_notMem_of_span_top q sₙ hsₙ
  obtain ⟨g', hg'_mem, hg'_notin⟩ := exists_mem_notMem_of_span_top q sₘ hsₘ
  have hg_smooth : RingHom.IsStandardSmoothOfRelativeDimension n
      ((algebraMap S (Localization.Away g)).comp φ) := hsn g hg_mem
  have hg'_smooth : RingHom.IsStandardSmoothOfRelativeDimension m
      ((algebraMap S (Localization.Away g')).comp φ) := hsm g' hg'_mem
  have htn := relDim_away_mul φ g g' hg_smooth
  have htm' := relDim_away_mul φ g' g hg'_smooth
  rw [mul_comm g' g] at htm'
  have ht_notin : g * g' ∉ q := hq.isPrime.mul_notMem hg_notin hg'_notin
  haveI : Nontrivial (Localization.Away (g * g')) := nontrivial_localization_away ht_notin
  exact relDim_eq_of_standardSmooth ((algebraMap S (Localization.Away (g * g'))).comp φ) htn htm'

/-- If `f : X ⟶ Y` is smooth and `X` is connected (hence nonempty), then `f` is smooth of a single
relative dimension `n` on all of `X`.

Proof sketch (all ingredients are in Mathlib at this pin):
* For `x : X` choose a chart `(U, V, e)` of `f` at `x` with `(f.appLE U V e).hom.IsStandardSmooth`
  (`AlgebraicGeometry.Smooth.exists_isStandardSmooth`). From `Algebra.IsStandardSmooth.out` take a
  submersive presentation `P` and set `d x := P.dimension`, giving
  `IsStandardSmoothOfRelativeDimension (d x) (f.appLE U V e).hom`
  (`SubmersivePresentation.isStandardSmoothOfRelativeDimension`).
* Localisation transfer: for `y ∈ V` and `W` a basic open of `V` containing `y`, one has
  `f.appLE U W e' = f.appLE U V e ≫ (algebraMap Γ(X,V) Γ(X,W))` (`Scheme.Hom.appLE_map`), the
  second map is an `IsLocalization.Away` (`IsAffineOpen.isLocalization_basicOpen`), hence
  `IsStandardSmoothOfRelativeDimension (d x) (f.appLE U W e')` by
  `RingHom.StableUnderCompositionWithLocalizationAway.left`
  (`isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway`).
* Change of chart at a fixed point: if `R → S` is standard smooth of relative dimension `n` with `S`
  nontrivial, then `n = Module.rank S Ω[S⁄R]` (`IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth`,
  `IsStandardSmooth.free_kaehlerDifferential`); ranks of Kähler differentials are preserved by
  localisation, so localising a chart map at (the primes of) a point gives the same dimension, and
  `RingHom.LocalizationPreserves (IsStandardSmoothOfRelativeDimension n)`
  (`isStandardSmoothOfRelativeDimension_localizationPreserves`) together with
  `IsAffineOpen.isLocalization_stalk` / `IsAffineOpen.arrowStalkMapIso` transfers the statement to
  the stalk map `f.stalkMap x`. Hence any two charts at the same point have the same dimension.
* Combining, `x ↦ d x` is locally constant (for `x` with chart `V`, every `y ∈ V` has the chart
  `(U, W)` of the same dimension `d x`), so it is constant with value `n` since `X` is connected
  (`IsLocallyConstant.apply_eq_of_preconnectedSpace`); then `SmoothOfRelativeDimension n f` holds by
  the chart condition. -/
theorem exists_smoothOfRelativeDimension {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    [ConnectedSpace X] : ∃ n : ℕ, SmoothOfRelativeDimension n f := by
  classical
  -- For every point choose a chart with a relative dimension.
  have hchart : ∀ x : X, ∃ (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (n : ℕ),
      IsAffineOpen U ∧ IsAffineOpen V ∧ x ∈ V ∧
        RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom := by
    intro x
    obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
    obtain ⟨n, hn⟩ := exists_isStandardSmoothOfRelativeDimension_of_isStandardSmooth
      (f.appLE U V e).hom hstd
    exact ⟨U, V, e, n, hU, hV, hx, hn⟩
  choose U V e n hU hV hxV hn using hchart
  -- The relative dimension is locally constant.
  have key : ∀ x y : X, y ∈ V x → n y = n x := by
    intro x y hy
    have hfy : f y ∈ U x := e x hy
    obtain ⟨U', hU'a, hfyU', hU'sub⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      Y.isBasis_affineOpens (show f y ∈ U x ⊓ U y from ⟨hfy, e y (hxV y)⟩)
    obtain ⟨W, hWa, hyW, hWsub⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      X.isBasis_affineOpens (show y ∈ V x ⊓ (V y ⊓ f ⁻¹ᵁ U') from ⟨hy, hxV y, hfyU'⟩)
    haveI : Nontrivial Γ(X, W) := nontrivial_sections_of_mem hWa hyW
    have hWU' : W ≤ f ⁻¹ᵁ U' := fun z hz => (hWsub hz).2.2
    have h₁ : SmoothOfRelativeDimension (n x) (f.resLE (U x) (V x) (e x)) :=
      (smoothOfRelativeDimension_resLE_iff f (n x) (e x) (hU x) (hV x)).mpr
        (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ (hn x))
    have h₂ : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (n x))
        (f.appLE U' W hWU').hom :=
      locally_appLE_of_resLE f (e x) h₁ hWU' hU'a hWa (fun z hz => (hU'sub hz).1)
        (fun z hz => (hWsub hz).1)
    have h₃ : SmoothOfRelativeDimension (n y) (f.resLE (U y) (V y) (e y)) :=
      (smoothOfRelativeDimension_resLE_iff f (n y) (e y) (hU y) (hV y)).mpr
        (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ (hn y))
    have h₄ : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (n y))
        (f.appLE U' W hWU').hom :=
      locally_appLE_of_resLE f (e y) h₃ hWU' hU'a hWa (fun z hz => (hU'sub hz).2)
        (fun z hz => (hWsub hz).2.1)
    exact (locally_relDim_unique (f.appLE U' W hWU').hom h₂ h₄ (n := n x) (m := n y)).symm
  have hloc : IsLocallyConstant fun x : X => n x :=
    (IsLocallyConstant.iff_exists_open _).mpr fun x =>
      ⟨(V x : Set X), (V x).isOpen, hxV x, fun y hy => key x y hy⟩
  refine ⟨n (Classical.arbitrary X), ?_⟩
  rw [smoothOfRelativeDimension_iff]
  intro x
  refine ⟨U x, hU x, V x, hV x, hxV x, e x, ?_⟩
  have := hn x
  rw [IsLocallyConstant.apply_eq_of_preconnectedSpace hloc x (Classical.arbitrary X)] at this
  exact this

end Work.Packaging.RelDim
