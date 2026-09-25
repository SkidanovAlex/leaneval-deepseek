import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.LogDefs

/-!
# `Gal(L/K)`-equivariance of the log vector

Let `L / K` be a finite Galois extension of number fields, `T` a finite `Gal(L/K)`-stable set of
places of `L`.  The log vector `a ↦ (log |a|_w)_{w ∈ T}` is `Gal(L/K)`-equivariant with respect to
the permutation action on functions on `T`:

`(σ • logVec a) w = logVec a (σ⁻¹ • w)`.

Unfolded, this is the invariance of the normalized local absolute value under the canonical local
isomorphism `Place.localRingEquiv σ⁻¹ w : L_w ≃+* L_{σ⁻¹ w}`:

`localAbs L w (σ•a)_w = localAbs L (σ⁻¹ • w) a_{σ⁻¹ w}`.

The proof combines three ingredients:
* the compatibility of the action on idèles with the diagonal embedding
  (`NK.GlobalCFT.Galois.globalCFT_smul_principalIdele`);
* the nonarchimedean case: the canonical isomorphism `globalCFT_adicCongrEquiv` preserves the
  `v`-adic valuation (`globalCFT_adicCongrEquiv_valued`), and the normalizations of the absolute
  values at `q` and at `σ • q` coincide because the induced ring automorphism of `𝓞 L` preserves
  absolute ideal norms;
* the archimedean case: `globalCFT_infiniteCongrEquiv` is induced by the isometry
  `globalCFT_withAbsCongrEquiv` (`globalCFT_isometry_withAbsCongrEquiv`), hence preserves norms,
  and the multiplicity `w.mult` is preserved by `σ` (`isReal_smul_iff`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.LogLattice

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-! ### A few elementary auxiliary facts -/

/-- The absolute norm of an ideal is invariant under the ring automorphisms of the base: the
quotients `R ⧸ I` and `R ⧸ I.map f` are equivalent. -/
theorem absNorm_map_ringEquiv {R : Type} [CommRing R] [IsDedekindDomain R] [Infinite R]
    [Module.Free ℤ R] (f : R ≃+* R) (I : Ideal R) :
    Ideal.absNorm (I.map f) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv I (I.map f) f rfl).toEquiv.symm

/-- `WithZeroMulInt.toNNReal` depends on its base `e : ℝ≥0` only through the (proof-irrelevant)
nonvanishing hypothesis: two provably equal bases give the same map. -/
theorem toNNReal_congr_base {e₁ e₂ : NNReal} (h : e₁ = e₂) (he₁ : e₁ ≠ 0) (he₂ : e₂ ≠ 0)
    (X : WithZero (Multiplicative ℤ)) :
    WithZeroMulInt.toNNReal he₁ X = WithZeroMulInt.toNNReal he₂ X := by
  obtain rfl := h
  rw [Subsingleton.elim he₁ he₂]

/-- `Units.mk0` depends on its input only through the value: equal nonzero elements give equal
units. -/
theorem mk0_congr {α : Type} [GroupWithZero α] {a b : α} (h : a = b) (ha : a ≠ 0) (hb : b ≠ 0) :
    Units.mk0 a ha = Units.mk0 b hb := by
  obtain rfl := h
  rw [Subsingleton.elim ha hb]

/-- The multiplicity of an infinite place is preserved by the Galois action. -/
theorem mult_smul (σ : L ≃ₐ[K] L) (w : InfinitePlace L) : (σ • w).mult = w.mult := by
  by_cases h : w.IsReal
  · rw [NumberField.InfinitePlace.mult, NumberField.InfinitePlace.mult,
      if_pos h, if_pos ((NumberField.InfinitePlace.isReal_smul_iff (σ := σ)).mpr h)]
  · rw [NumberField.InfinitePlace.mult, NumberField.InfinitePlace.mult,
      if_neg h, if_neg (fun hc => h ((NumberField.InfinitePlace.isReal_smul_iff (σ := σ)).mp hc))]

/-! ### The canonical local isomorphism is an isometry for the normalized absolute values -/

/-- The canonical isomorphism of `q`-adic completions induced by `σ` preserves the norm. -/
theorem norm_adicCongrEquiv (σ : L ≃ₐ[K] L) (q : HeightOneSpectrum (𝓞 L))
    (z : q.adicCompletion L) :
    ‖NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv σ q z‖ = ‖z‖ := by
  have hbase : ((Ideal.absNorm (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q).asIdeal : ℕ) :
        NNReal) = ((Ideal.absNorm q.asIdeal : ℕ) : NNReal) := by
    rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
    exact congrArg _ (absNorm_map_ringEquiv (NK.GlobalCFT.Place.ringOfIntegersEquiv σ) q.asIdeal)
  rw [NumberField.FinitePlace.norm_def (v := NK.GlobalCFT.Place.smulHeightOneSpectrum σ q)
        (x := NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv σ q z),
      NumberField.FinitePlace.norm_def (v := q) (x := z),
      NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv_valued]
  exact congrArg (fun y : NNReal => (y : ℝ))
    (toNNReal_congr_base hbase _ _ (Valued.v z))

/-- The canonical isomorphism of archimedean completions induced by `σ` preserves the norm: it is
built from the isometry `globalCFT_withAbsCongrEquiv` on `WithAbs`, extended to completions. -/
theorem norm_infiniteCongrEquiv (σ : L ≃ₐ[K] L) (w : InfinitePlace L) (z : w.Completion) :
    ‖NK.GlobalCFT.Galois.globalCFT_infiniteCongrEquiv σ w z‖ = ‖z‖ := by
  have hnorm : ∀ y : UniformSpace.Completion (WithAbs w.1),
      ‖(UniformSpace.Completion.mapRingEquiv (NK.GlobalCFT.Galois.globalCFT_withAbsCongrEquiv σ w)
          (NK.GlobalCFT.Galois.globalCFT_isometry_withAbsCongrEquiv σ w).continuous
          (NK.GlobalCFT.Galois.globalCFT_isometry_withAbsCongrEquiv_symm σ w).continuous) y‖
        = ‖y‖ := by
    intro y
    have hiso : Isometry (UniformSpace.Completion.mapRingHom
        (NK.GlobalCFT.Galois.globalCFT_withAbsCongrEquiv σ w).toRingHom
        (NK.GlobalCFT.Galois.globalCFT_isometry_withAbsCongrEquiv σ w).continuous) :=
      (NK.GlobalCFT.Galois.globalCFT_isometry_withAbsCongrEquiv σ w).isometry_mapRingHom
    have h := hiso.dist_eq y 0
    rw [map_zero] at h
    simpa [dist_eq_norm] using h
  have h2 : ∀ y : (σ • w).1.Completion,
      ‖(NumberField.InfinitePlace.Completion.equiv (σ • w)).symm y‖ = ‖y‖ := fun y => rfl
  simp only [NK.GlobalCFT.Galois.globalCFT_infiniteCongrEquiv, RingEquiv.trans_apply]
  rw [h2, hnorm]
  rfl

/-- **Invariance of the normalized local absolute value** under the canonical local isomorphism:
`localAbs L w (σ_*(y)) = localAbs L (σ • w) y` for `y` in the local field at `σ • w`. -/
theorem localAbs_localRingEquiv_symm (σ : L ≃ₐ[K] L) (v : Place L)
    (y : (Place.localField L (σ • v))ˣ) :
    Idele.localAbs L v (Units.map (Place.localRingEquiv σ v).symm.toMonoidHom y)
      = Idele.localAbs L (σ • v) y := by
  cases v with
  | inl w =>
      change Idele.localAbs L (Place.ofInfinite w)
          (Units.map (Place.localRingEquiv σ (Place.ofInfinite w)).symm.toMonoidHom y)
        = Idele.localAbs L (Place.ofInfinite (σ • w)) y
      have hAB : ‖(((NK.GlobalCFT.Galois.globalCFT_infiniteCongrEquiv σ w).symm y :
          w.Completion))‖ = ‖(y : (σ • w).Completion)‖ := by
        have h := norm_infiniteCongrEquiv σ w
          ((NK.GlobalCFT.Galois.globalCFT_infiniteCongrEquiv σ w).symm y)
        rw [RingEquiv.apply_symm_apply] at h
        exact h.symm
      rw [Idele.localAbs_ofInfinite, Idele.localAbs_ofInfinite, mult_smul σ w]
      congr 1
      apply Units.ext
      simp only [Units.coe_map, Units.val_mk0]
      exact hAB
  | inr q =>
      change Idele.localAbs L (Place.ofFinite q)
          (Units.map (Place.localRingEquiv σ (Place.ofFinite q)).symm.toMonoidHom y)
        = Idele.localAbs L (Place.ofFinite (Place.smulHeightOneSpectrum σ q)) y
      have hAB : ‖(((NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv σ q).symm y :
          q.adicCompletion L))‖ = ‖(y : (Place.smulHeightOneSpectrum σ q).adicCompletion L)‖ := by
        have h := norm_adicCongrEquiv σ q
          ((NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv σ q).symm y)
        rw [RingEquiv.apply_symm_apply] at h
        exact h.symm
      rw [Idele.localAbs_ofFinite, Idele.localAbs_ofFinite]
      apply mk0_congr
      rw [Units.coe_map]
      exact hAB

/-! ### The main statement -/

/-- **`Gal(L/K)`-equivariance of the log vector** (Milne, *CFT*, Chapter VII §3): the log of the
normalized local absolute value of a `T`-unit is permuted by the Galois action,
`(σ • log |a|) (w) = log |a| (σ⁻¹ • w)`.

Unfolded, this is the invariance of the normalized local absolute value under the canonical local
isomorphism: `|σ a|_{w} = |a|_{σ⁻¹ w}` for every place `w` of `L`, which must be built from the
finite computation (`NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv` /
`NK.GlobalCFT.Galois.completionMap_isometry`, or `globalCFT_valuation_smulHeightOneSpectrum`)
and the archimedean one (`w.mult` is preserved by `σ`), together with
`NK.GlobalCFT.Galois.globalCFT_smul_principalIdele`. -/
theorem logVec_smul_apply {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (T : Set (NK.GlobalCFT.Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (σ : L ≃ₐ[K] L) (a : Lˣ) (w : ↥T) :
    NK.GlobalCFTdeep.logVec (L := L) T (σ • a) w =
      NK.GlobalCFTdeep.logVec (L := L) T a
        ⟨σ⁻¹ • (w : NK.GlobalCFT.Place L), hT σ⁻¹ w.2⟩ := by
  have key : Idele.localAbs L (w : NK.GlobalCFT.Place L)
        (Idele.principalIdele L (σ • a) (w : NK.GlobalCFT.Place L)) =
      Idele.localAbs L (σ⁻¹ • (w : NK.GlobalCFT.Place L))
        (Idele.principalIdele L a (σ⁻¹ • (w : NK.GlobalCFT.Place L))) := by
    have h1 : σ • a = Units.map σ.toMonoidHom a := rfl
    rw [h1, ← NK.GlobalCFT.Galois.globalCFT_smul_principalIdele σ a,
      Idele.smul_apply]
    exact localAbs_localRingEquiv_symm σ⁻¹ (w : NK.GlobalCFT.Place L) _
  simp only [NK.GlobalCFTdeep.logVec]
  rw [key]

end NK.GlobalCFTdeep.LogLattice
