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

/-! ## Localisation helpers for standard smoothness of a fixed relative dimension -/

/-- A ring with a prime ideal is nontrivial. -/
private lemma nat_nontrivial_of_isPrime {R : Type*} [CommRing R] {I : Ideal R} (h : I.IsPrime) :
    Nontrivial R := by
  have h1 : (1 : R) ∉ I := h.one_notMem
  by_contra hR
  rw [not_nontrivial_iff_subsingleton] at hR
  haveI := hR
  exact h1 (Subsingleton.elim (1:R) 0 ▸ I.zero_mem)

/-- If `t` is not in the prime ideal `q`, the localisation away from `t` is nontrivial. -/
private lemma nontrivial_localization_away {B : Type*} [CommRing B] {q : Ideal B} [q.IsPrime]
    {t : B} (ht : t ∉ q) : Nontrivial (Localization.Away t) :=
  nat_nontrivial_of_isPrime
    (IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers t) (Localization.Away t) q
      ‹q.IsPrime› (by rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]; exact ht))

/-- An ideal spanning the unit ideal is not contained in a prime ideal: some element of the
spanning set is outside the prime. -/
private lemma exists_mem_notMem_of_span_top {B : Type*} [CommRing B] (q : Ideal B) [q.IsPrime]
    (s : Set B) (hs : Ideal.span s = ⊤) : ∃ g ∈ s, g ∉ q := by
  by_contra h
  push Not at h
  have hle : Ideal.span s ≤ q := Ideal.span_le.mpr (fun y hy => h y hy)
  rw [hs] at hle
  exact (Ideal.IsPrime.ne_top ‹q.IsPrime›) (top_le_iff.mp hle)

/-- Standard smoothness of relative dimension `n` is stable under passing to a further
localisation away from an element of the target. -/
private lemma isStandardSmoothOfRelativeDimension_away_mul {A B : Type u} [CommRing A]
    [CommRing B] (φ : A →+* B) {n : ℕ} (g h : B)
    (H : RingHom.IsStandardSmoothOfRelativeDimension n ((algebraMap B (Localization.Away g)).comp φ)) :
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

/-- If a ring hom `Ψ` with nontrivial target is standard smooth of relative dimension `n` and of
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

/-- The relative dimension of a smooth morphism over a connected source is unique: if `f : X ⟶ Y` is
smooth of relative dimension `n` and of relative dimension `m` and `X` is connected (hence
nonempty), then `n = m`.

Proof sketch: `SmoothOfRelativeDimension n f` and `SmoothOfRelativeDimension m f` give, at each point
`x : X`, charts whose ring maps are standard smooth of relative dimension `n` resp. `m`; those ring
maps have nontrivial target (`V` contains `x`), so their relative dimension is the `Module.rank` of
the Kähler differentials (`IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth`), which is
preserved by localisation. Localising both charts at the primes of `x` and comparing with the stalk
map `f.stalkMap x` (`RingHom.LocalizationPreserves (IsStandardSmoothOfRelativeDimension n)`,
`isStandardSmoothOfRelativeDimension_localizationPreserves`, `IsAffineOpen.isLocalization_stalk`,
`IsAffineOpen.arrowStalkMapIso`) gives `n = m`. -/
theorem smoothOfRelativeDimension_unique {X Y : Scheme.{u}} (f : X ⟶ Y) [ConnectedSpace X] (n m : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension m f] : n = m := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  -- Pick affine opens `V ∋ x` and `U ∋ f x` with `V ≤ f ⁻¹ᵁ U`.
  obtain ⟨_, ⟨U, hU, rfl⟩, hfxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hfxU (U.2.preimage f.continuous)
  let Ua : Y.affineOpens := ⟨U, hU⟩
  let Va : X.affineOpens := ⟨V, hV⟩
  let φ : Γ(Y, U) →+* Γ(X, V) := (f.appLE U V hVU).hom
  -- On this chart both relative dimensions hold locally on the target.
  have hn : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) φ :=
    HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension n) f
      (inferInstance : SmoothOfRelativeDimension n f) Ua Va hVU
  have hm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension m) φ :=
    HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension m) f
      (inferInstance : SmoothOfRelativeDimension m f) Ua Va hVU
  rw [RingHom.Locally] at hn hm
  obtain ⟨sₙ, hsₙ, hsn⟩ := hn
  obtain ⟨sₘ, hsₘ, hsm⟩ := hm
  -- The prime of `x` in `V`, used to select a common basic open.
  let q : Ideal Γ(X, V) := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  haveI hq : q.IsPrime := (hV.primeIdealOf ⟨x, hxV⟩).isPrime
  obtain ⟨g, hg_mem, hg_notin⟩ := exists_mem_notMem_of_span_top q sₙ hsₙ
  obtain ⟨g', hg'_mem, hg'_notin⟩ := exists_mem_notMem_of_span_top q sₘ hsₘ
  have hg_smooth : RingHom.IsStandardSmoothOfRelativeDimension n
      ((algebraMap Γ(X,V) (Localization.Away g)).comp φ) := hsn g hg_mem
  have hg'_smooth : RingHom.IsStandardSmoothOfRelativeDimension m
      ((algebraMap Γ(X,V) (Localization.Away g')).comp φ) := hsm g' hg'_mem
  -- Both relative dimensions persist on the basic open `D (g * g')`, which contains `q`.
  have htn := isStandardSmoothOfRelativeDimension_away_mul φ g g' hg_smooth
  have htm' := isStandardSmoothOfRelativeDimension_away_mul φ g' g hg'_smooth
  rw [mul_comm g' g] at htm'
  have ht_notin : g * g' ∉ q := hq.mul_notMem hg_notin hg'_notin
  haveI : Nontrivial (Localization.Away (g * g')) := nontrivial_localization_away ht_notin
  exact relDim_eq_of_standardSmooth ((algebraMap Γ(X,V) (Localization.Away (g * g'))).comp φ) htn htm'

end Work.Packaging.RelDim
