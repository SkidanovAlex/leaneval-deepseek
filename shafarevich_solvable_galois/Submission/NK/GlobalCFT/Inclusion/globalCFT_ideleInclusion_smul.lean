import Mathlib.Topology.Connected.Separation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
import Submission.NK.GlobalCFT.GaloisIdelesAction
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The idèle inclusion lands in the Galois-invariants

For a finite extension `L / K` of number fields and a monoid homomorphism `φ : 𝕀[K] →* 𝕀[L]`
whose `w`-component is the canonical local embedding `K_{u w}ˣ →* L_wˣ`, the image of `φ` is
fixed by `Gal(L/K)`.

This is the statement that the idèle inclusion `𝕀[K] → 𝕀[L]` is `Gal(L/K)`-equivariant, i.e.
that the diagonal embedding lands in the Galois-invariants `(𝕀 L)^{Gal(L/K)}`; it is the
starting point for the identification `C_K ≅ C_L^{Gal(L/K)}` (`H⁰`-computation).

The mathematical content is the local statement that the canonical local isomorphism
`Place.localRingEquiv σ w : L_w ≃+* L_{σ w}` intertwines the two local algebra maps
`K_v → L_w` and `K_v → L_{σ w}`; since both are continuous and agree on the dense image of `K`,
this is an application of the uniqueness of continuous extensions.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Inclusion

open NK.GlobalCFT

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-! ### The archimedean equivariance -/

/-- The archimedean local isomorphism, evaluated on the image of the `WithAbs`-copy of `L`. -/
private lemma aux_infiniteCongrEquiv_coe (σ : L ≃ₐ[K] L) (w : InfinitePlace L)
    (y : WithAbs (w.1)) :
    Galois.globalCFT_infiniteCongrEquiv σ w (y : w.Completion) =
      (Galois.globalCFT_withAbsCongrEquiv σ w y : (σ • w).Completion) := by
  rw [Galois.globalCFT_infiniteCongrEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply,
    NumberField.InfinitePlace.Completion.equiv_apply,
    UniformSpace.Completion.mapRingEquiv_apply]
  rw [show ((y : w.Completion).toCompletion) = (y : w.1.Completion) from rfl]
  rw [UniformSpace.Completion.map_coe
    (Galois.globalCFT_isometry_withAbsCongrEquiv σ w).uniformContinuous]
  rfl

/-- At the level of the `WithAbs`-copies of `L`, the archimedean isomorphism attached to `σ`
intertwines the algebra maps `K → L`. -/
private lemma aux_withAbsCongrEquiv_algebraMap (σ : L ≃ₐ[K] L) (v : InfinitePlace K)
    (w : InfinitePlace L) [w.LiesOver v] [(σ • w).LiesOver v] (a : WithAbs (v.1)) :
    Galois.globalCFT_withAbsCongrEquiv σ w (algebraMap (WithAbs (v.1)) (WithAbs (w.1)) a) =
      algebraMap (WithAbs (v.1)) (WithAbs ((σ • w).1)) a := by
  rw [Galois.globalCFT_withAbsCongrEquiv, WithAbs.congr_apply, WithAbs.ofAbs_algebraMap,
    WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply]
  congr 1
  exact AlgEquiv.commutes σ a.ofAbs

/-- The archimedean case of the equivariance: the local isomorphism `L_w ≃+* L_{σ w}` intertwines
the completion maps `K_v →+* L_w` and `K_v →+* L_{σ w}`. -/
private lemma aux_infiniteCongrEquiv_completionMap (σ : L ≃ₐ[K] L) (v : InfinitePlace K)
    (w : InfinitePlace L) [w.LiesOver v] [(σ • w).LiesOver v] (x : v.Completion) :
    Galois.globalCFT_infiniteCongrEquiv σ w
        (NumberField.LiesOver.completionMap (v := v) (w := w) x) =
      NumberField.LiesOver.completionMap (v := v) (w := σ • w) x := by
  induction x using NumberField.InfinitePlace.Completion.induction_on
  · exact isClosed_eq
      ((Galois.continuous_localRingEquiv σ (Place.ofInfinite w)).comp
        (NumberField.LiesOver.continuous_completionMap (v := v) (w := w)))
      (NumberField.LiesOver.continuous_completionMap (v := v) (w := σ • w))
  · rw [NumberField.LiesOver.completionMap_coe (v := v) (w := w),
      NumberField.LiesOver.completionMap_coe (v := v) (w := σ • w),
      aux_infiniteCongrEquiv_coe, aux_withAbsCongrEquiv_algebraMap]

/-! ### The nonarchimedean equivariance -/

/-- The nonarchimedean case of the equivariance, on elements of the base field `K`. -/
private lemma aux_adicCongrEquiv_adicCompletionMap_base (σ : L ≃ₐ[K] L)
    (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K))
    (h : q.asIdeal.LiesOver Q.asIdeal)
    (h' : (Place.smulHeightOneSpectrum σ q).asIdeal.LiesOver Q.asIdeal) (x : K) :
    Galois.globalCFT_adicCongrEquiv σ q
        (Commons.RingTheory.Henselian.adicCompletionMap Q q h (x : Q.adicCompletion K)) =
      Commons.RingTheory.Henselian.adicCompletionMap Q (Place.smulHeightOneSpectrum σ q) h'
        (x : Q.adicCompletion K) := by
  rw [Commons.RingTheory.Henselian.adicCompletionMap_apply Q q h,
    Commons.RingTheory.Henselian.adicCompletionMap_apply Q (Place.smulHeightOneSpectrum σ q) h',
    Galois.globalCFT_adicCongrEquiv_coe]
  congr 1
  congr 1
  exact congrArg (WithVal.toVal (HeightOneSpectrum.valuation L (Place.smulHeightOneSpectrum σ q)))
    (AlgEquiv.commutes σ x)

/-- The nonarchimedean case of the equivariance: the local isomorphism `L_q ≃+* L_{σ q}`
intertwines the adic completion maps `K_Q →+* L_q` and `K_Q →+* L_{σ q}`. -/
private lemma aux_adicCongrEquiv_adicCompletionMap (σ : L ≃ₐ[K] L)
    (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K))
    (h : q.asIdeal.LiesOver Q.asIdeal)
    (h' : (Place.smulHeightOneSpectrum σ q).asIdeal.LiesOver Q.asIdeal)
    (x : Q.adicCompletion K) :
    Galois.globalCFT_adicCongrEquiv σ q
        (Commons.RingTheory.Henselian.adicCompletionMap Q q h x) =
      Commons.RingTheory.Henselian.adicCompletionMap Q (Place.smulHeightOneSpectrum σ q) h' x := by
  have hfun := DenseRange.equalizer
    (f := algebraMap K (Q.adicCompletion K))
    (g := fun z => Galois.globalCFT_adicCongrEquiv σ q
      (Commons.RingTheory.Henselian.adicCompletionMap Q q h z))
    (h := fun z => Commons.RingTheory.Henselian.adicCompletionMap Q
      (Place.smulHeightOneSpectrum σ q) h' z)
    (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) K Q)
    ((Galois.globalCFT_adicCongrEquiv_continuous σ q).comp
      (Commons.RingTheory.Henselian.adicCompletionMap_continuous Q q h))
    (Commons.RingTheory.Henselian.adicCompletionMap_continuous Q
      (Place.smulHeightOneSpectrum σ q) h')
    (by funext y; exact aux_adicCongrEquiv_adicCompletionMap_base σ q Q h h' y)
  exact congrFun hfun x

/-! ### The local equivariance of the local algebra maps -/

/-- The canonical local isomorphism `Place.localRingEquiv σ w : L_w ≃+* L_{σ w}` intertwines the
local algebra maps `K_vˣ →* L_wˣ` and `K_vˣ →* L_{σ w}ˣ`. -/
private theorem aux_localRingEquiv_localAlgebraMapUnits (σ : L ≃ₐ[K] L) {w : Place L}
    {v : Place K} (h : Place.LiesOver w v) (h' : Place.LiesOver (σ • w) v)
    (a : (Place.localField K v)ˣ) :
    Units.map (Place.localRingEquiv σ w).toMonoidHom
        (Place.localAlgebraMapUnits w v h a) =
      Place.localAlgebraMapUnits (σ • w) v h' a := by
  rcases w with w | q
  · rcases v with v | Q
    · -- archimedean place over an archimedean place
      simp only [Place.smul_ofInfinite] at h' ⊢
      haveI : w.LiesOver v := (Galois.globalCFT_liesOver_ofInfinite_iff w v).mp h
      haveI : (σ • w).LiesOver v := (Galois.globalCFT_liesOver_ofInfinite_iff (σ • w) v).mp h'
      simp only [Place.localAlgebraMapUnits, Place.localRingEquiv]
      rw [dif_pos (show w.LiesOver v from inferInstance),
        dif_pos (show (σ • w).LiesOver v from inferInstance)]
      apply Units.ext
      simp only [Units.coe_map]
      exact aux_infiniteCongrEquiv_completionMap σ v w (a : v.Completion)
    · -- archimedean place over a nonarchimedean place: both sides are trivial
      simp [Place.smul_ofInfinite, Place.localAlgebraMapUnits, Place.localRingEquiv]
      try exact map_one _
  · rcases v with v | Q
    · -- nonarchimedean place over an archimedean place: both sides are trivial
      simp [Place.smul_ofFinite, Place.localAlgebraMapUnits, Place.localRingEquiv]
      try exact map_one _
    · -- nonarchimedean place over a nonarchimedean place
      simp only [Place.smul_ofFinite] at h' ⊢
      haveI : q.asIdeal.LiesOver Q.asIdeal := (Galois.globalCFT_liesOver_ofFinite_iff q Q).mp h
      haveI : (Place.smulHeightOneSpectrum σ q).asIdeal.LiesOver Q.asIdeal :=
        (Galois.globalCFT_liesOver_ofFinite_iff (Place.smulHeightOneSpectrum σ q) Q).mp h'
      simp only [Place.localAlgebraMapUnits, Place.localRingEquiv]
      rw [dif_pos (show q.asIdeal.LiesOver Q.asIdeal from inferInstance),
        dif_pos (show (Place.smulHeightOneSpectrum σ q).asIdeal.LiesOver Q.asIdeal from
          inferInstance)]
      apply Units.ext
      simp only [Units.coe_map]
      exact aux_adicCongrEquiv_adicCompletionMap σ q Q _ _ (a : Q.adicCompletion K)

/-- Transporting the place of `K` below `w₀` in the local algebra map: the local algebra map is
insensitive to the place of `K` up to the identification of the local fields given by the
equality of places. -/
private lemma aux_localAlgebraMapUnits_cast (w₀ : Place L) {a b : Place K} (h : a = b)
    (ha : Place.LiesOver w₀ a) (hb : Place.LiesOver w₀ b) (y : (Place.localField K a)ˣ) :
    Place.localAlgebraMapUnits w₀ a ha y =
      Place.localAlgebraMapUnits w₀ b hb (h ▸ y) := by
  cases h
  rfl

/-- The `apd` identity: transporting the value of a dependent function along an equality of the
arguments gives the value at the other argument. -/
private lemma aux_eqRec_apply {α : Type*} {β : α → Type*} (f : (i : α) → β i) {a b : α}
    (h : a = b) : h ▸ f a = f b := by
  cases h
  rfl

/-- The same equivariance read in the inverse direction: the inverse local isomorphism sends the
local algebra map at `σ • w` back to the one at `w`. -/
private lemma aux_symm_localAlgebraMapUnits (τ : L ≃ₐ[K] L) (w : Place L) (v : Place K)
    (h : Place.LiesOver w v) (h' : Place.LiesOver (τ • w) v)
    (a : (Place.localField K v)ˣ) :
    Units.map (Place.localRingEquiv τ w).symm.toMonoidHom
        (Place.localAlgebraMapUnits (τ • w) v h' a) =
      Place.localAlgebraMapUnits w v h a := by
  have key : Units.map (Place.localRingEquiv τ w).symm.toMonoidHom
      (Units.map (Place.localRingEquiv τ w).toMonoidHom
        (Place.localAlgebraMapUnits w v h a)) =
      Place.localAlgebraMapUnits w v h a := by
    ext
    simp
  rw [← aux_localRingEquiv_localAlgebraMapUnits τ h h' a]
  exact key

/-! ### The idèle inclusion is Galois-equivariant -/

theorem globalCFT_ideleInclusion_smul {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w))
    (φ : 𝕀[K] →* 𝕀[L])
    (hφ : ∀ (x : 𝕀[K]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (σ : L ≃ₐ[K] L) (x : 𝕀[K]) : σ • φ x = φ x := by
  apply Idele.ext
  intro w
  rw [Idele.smul_apply, hφ, hφ]
  -- the place of `K` below `σ⁻¹ • w` is the same as the one below `w`
  have hsw : σ • (σ⁻¹ • w) = w := by
    rw [Galois.globalCFT_smul_place_smul σ⁻¹ σ w, mul_inv_cancel]
    exact Galois.globalCFT_one_smul_place w
  have h1 : Place.LiesOver w (u (σ⁻¹ • w)) := by
    have h := (Galois.globalCFT_place_smul_liesOver σ (σ⁻¹ • w) (u (σ⁻¹ • w))).mpr
      (hu (σ⁻¹ • w))
    rwa [hsw] at h
  have huw : u (σ⁻¹ • w) = u w := globalCFT_liesOver_unique h1 (hu w)
  -- the same place of `K` transported into the fibre over `σ⁻¹ • w`
  have hb : Place.LiesOver (σ⁻¹ • w) (u w) := huw ▸ hu (σ⁻¹ • w)
  -- rewrite the component at `σ⁻¹ • w` in terms of the place `u w`
  have hcast : Place.localAlgebraMapUnits (σ⁻¹ • w) (u (σ⁻¹ • w)) (hu (σ⁻¹ • w))
        (x (u (σ⁻¹ • w))) =
      Place.localAlgebraMapUnits (σ⁻¹ • w) (u w) hb (x (u w)) := by
    rw [aux_localAlgebraMapUnits_cast (σ⁻¹ • w) huw (hu (σ⁻¹ • w)) hb (x (u (σ⁻¹ • w)))]
    congr 1
    exact aux_eqRec_apply x huw
  rw [hcast]
  exact aux_symm_localAlgebraMapUnits σ⁻¹ w (u w) (hu w) hb (x (u w))

end NK.GlobalCFT.Inclusion
