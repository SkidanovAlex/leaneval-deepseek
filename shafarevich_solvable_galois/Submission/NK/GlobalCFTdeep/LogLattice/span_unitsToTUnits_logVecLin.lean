import Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.NK.GlobalCFTdeep.Herbrand.finrank_tUnits
import Submission.NK.GlobalCFTdeep.LogLattice.InfSumZero
import Submission.NK.GlobalCFTdeep.LogLattice.sum_logVec_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Dirichlet's unit theorem in the `T`-unit picture

Let `L` be a number field, `T` a finite set of places of `L` containing all infinite places, and
let `infSumZero T` be the subspace of `↥T → ℝ` of vectors vanishing at every finite place of `T`
and whose coordinates sum to zero.  This file proves that the `ℝ`-span of the log vectors of the
global units, embedded in the `T`-units via `NK.GlobalCFTdeep.unitsToTUnits`, is exactly
`infSumZero T` (`NK.GlobalCFTdeep.LogLattice.span_unitsToTUnits_logVecLin`).

This is the archimedean half of Milne, *CFT*, Chapter VII §3.  The route is the one explained in
the statement of the main theorem: Mathlib's Dirichlet result
`NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top` says that the log embedding
`NumberField.Units.logEmbedding L : Additive (𝓞 L)ˣ → logSpace L` spans the `w₀`-dropped space
`logSpace L = {w : InfinitePlace L // w ≠ w₀} → ℝ`.  We transfer it along the `ℝ`-linear map
`logSpaceToT T : logSpace L → (↥T → ℝ)` which

* places the value `g w` of `g : logSpace L` at the infinite place `w ≠ w₀`,
* places `-∑ w', g w'` at the distinguished place `w₀` (so that the sum over the infinite places
  is zero),
* places `0` at every finite place of `T`,

and identify `logVecLin T (unitsToTUnits T u)` with the image of `logEmbedding L u`.

## Main results

* `NK.GlobalCFTdeep.LogLattice.logSpaceToT`: the transfer map `logSpace L →ₗ[ℝ] (↥T → ℝ)`;
* `NK.GlobalCFTdeep.LogLattice.sum_T_eq_sum_infinite`: the sum over `↥T` of a function
  vanishing at the finite places is the sum over the infinite places;
* `NK.GlobalCFTdeep.LogLattice.exists_logSpaceToT_eq`: `logSpaceToT T` is onto `infSumZero T`;
* `NK.GlobalCFTdeep.LogLattice.logSpaceToT_logEmbedding`: the identification of
  `logSpaceToT T (logEmbedding L u)` with `logVecLin T (unitsToTUnits T u)`;
* `NK.GlobalCFTdeep.LogLattice.span_unitsToTUnits_logVecLin`: the theorem.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.LogLattice

open NK.GlobalCFT
open NK.GlobalCFTdeep NumberField.Units.dirichletUnitTheorem

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-! ### Membership in `infSumZero` in terms of the finite places -/

/-- Membership in `infSumZero T`, with the finite places indexed by `HeightOneSpectrum (𝓞 L)`
rather than by the subtype `SSet T`. -/
theorem mem_infSumZero_iff {T : Set (Place L)} [Fintype ↥T] {v : ↥T → ℝ} :
    v ∈ infSumZero (L := L) T ↔
      (∀ (q : HeightOneSpectrum (𝓞 L)) (hq : Place.ofFinite q ∈ T),
        v ⟨Place.ofFinite q, hq⟩ = 0) ∧ ∑ w : ↥T, v w = 0 := by
  rw [mem_infSumZero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun q hq => h1 ⟨q, hq⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun q => h1 q.1 q.2, h2⟩

/-! ### The transfer map `logSpace L → ↥T → ℝ` -/

/-- **The transfer map.**  A vector `g` on the `w₀`-dropped space of infinite places is sent to
the vector on `↥T` which vanishes at the finite places, takes the value `g w` at an infinite place
`w ≠ w₀`, and the value `-∑ w', g w'` at `w₀` (so that the coordinate sum over the infinite places
is `0`). -/
noncomputable def logSpaceToT (T : Set (Place L)) : logSpace L →ₗ[ℝ] (↥T → ℝ) where
  toFun g := fun w =>
    match w with
    | ⟨Sum.inl v, _⟩ => if h : v = (w₀ : InfinitePlace L) then
        -∑ w' : {w : InfinitePlace L // w ≠ (w₀ : InfinitePlace L)}, g w'
        else g ⟨v, h⟩
    | ⟨Sum.inr _, _⟩ => 0
  map_add' g₁ g₂ := by
    funext w
    obtain ⟨(v | q), hw⟩ := w
    · by_cases h : v = (w₀ : InfinitePlace L)
      · simp only [dif_pos h, Pi.add_apply, Finset.sum_add_distrib]
        ring
      · simp only [dif_neg h, Pi.add_apply]
    · simp
  map_smul' c g := by
    funext w
    obtain ⟨(v | q), hw⟩ := w
    · by_cases h : v = (w₀ : InfinitePlace L)
      · simp only [dif_pos h, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [mul_neg, Finset.mul_sum]
      · simp only [dif_neg h, Pi.smul_apply, RingHom.id_apply]
    · simp

/-- The value of the transfer map at an infinite place. -/
@[simp] theorem logSpaceToT_apply_inf (T : Set (Place L)) (g : logSpace L)
    (v : InfinitePlace L) (hv : Place.ofInfinite v ∈ T) :
    logSpaceToT T g ⟨Place.ofInfinite v, hv⟩ =
      (if h : v = (w₀ : InfinitePlace L) then
        -∑ w' : {w : InfinitePlace L // w ≠ (w₀ : InfinitePlace L)}, g w'
        else g ⟨v, h⟩) := rfl

/-- The value of the transfer map at a finite place. -/
@[simp] theorem logSpaceToT_apply_fin (T : Set (Place L)) (g : logSpace L)
    (q : HeightOneSpectrum (𝓞 L)) (hq : Place.ofFinite q ∈ T) :
    logSpaceToT T g ⟨Place.ofFinite q, hq⟩ = 0 := rfl

/-! ### Sums over `↥T` and over the infinite places -/

/-- **Comparing the sum over `↥T` with the sum over the infinite places.**  For a function on `↥T`
vanishing at every finite place of `T`, the sum over `↥T` is the sum over the infinite places
(which all lie in `T` by hypothesis); the comparison uses `tUnitsPlaceEquiv`. -/
theorem sum_T_eq_sum_infinite (T : Set (Place L)) [Fintype ↥T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) (f : ↥T → ℝ)
    (hf : ∀ (q : HeightOneSpectrum (𝓞 L)) (hq : Place.ofFinite q ∈ T),
      f ⟨Place.ofFinite q, hq⟩ = 0) :
    ∑ w : ↥T, f w = ∑ v : InfinitePlace L, f ⟨Place.ofInfinite v, hTinf _ trivial⟩ := by
  classical
  haveI : Finite T := Finite.of_fintype T
  haveI : Fintype (SSet T) := Fintype.ofFinite _
  let g : SSet T ⊕ InfinitePlace L → ℝ := fun x => match x with
    | Sum.inl q => f ⟨Place.ofFinite q.1, (q.2 : Place.ofFinite q.1 ∈ T)⟩
    | Sum.inr v => f ⟨Place.ofInfinite v, hTinf _ trivial⟩
  have h1 : ∑ w : ↥T, f w = ∑ x : SSet T ⊕ InfinitePlace L, g x := by
    refine Fintype.sum_equiv (tUnitsPlaceEquiv T hTinf) f g ?_
    intro w
    obtain ⟨(v | q), hw⟩ := w
    · rfl
    · exact congrArg f (Subtype.ext rfl)
  rw [h1, Fintype.sum_sum_type]
  have h2 : ∑ q : SSet T, g (Sum.inl q) = 0 := by
    refine Finset.sum_eq_zero (fun q _ => ?_)
    show f ⟨Place.ofFinite q.1, (q.2 : Place.ofFinite q.1 ∈ T)⟩ = 0
    exact hf q.1 q.2
  rw [h2, zero_add]

/-! ### The transfer map lands in `infSumZero` and is onto it -/

/-- The transfer map lands in `infSumZero T`: its values at the finite places are `0` and the
coordinate sum over `↥T` (equivalently over the infinite places) is `0` by construction. -/
theorem logSpaceToT_mem_infSumZero (T : Set (Place L)) [Fintype ↥T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) (g : logSpace L) :
    logSpaceToT T g ∈ infSumZero (L := L) T := by
  classical
  refine mem_infSumZero_iff.mpr ⟨fun q hq => ?_, ?_⟩
  · rw [logSpaceToT_apply_fin]
  · rw [sum_T_eq_sum_infinite T hTinf (logSpaceToT T g)
      (fun q hq => logSpaceToT_apply_fin T g q hq)]
    set F : InfinitePlace L → ℝ :=
      fun v => logSpaceToT T g ⟨Place.ofInfinite v, hTinf _ trivial⟩ with hF
    have hsub : (∑ w' : {w : InfinitePlace L // w ≠ (w₀ : InfinitePlace L)}, F w') =
        ∑ w' : {w : InfinitePlace L // w ≠ (w₀ : InfinitePlace L)}, g w' := by
      refine Finset.sum_congr rfl (fun w' _ => ?_)
      show logSpaceToT T g ⟨Place.ofInfinite w'.1, hTinf _ trivial⟩ = g w'
      rw [logSpaceToT_apply_inf, dif_neg w'.2]
    have hw0 : F (w₀ : InfinitePlace L) =
        -∑ w' : {w : InfinitePlace L // w ≠ (w₀ : InfinitePlace L)}, g w' := by
      show logSpaceToT T g ⟨Place.ofInfinite (w₀ : InfinitePlace L), hTinf _ trivial⟩ = _
      rw [logSpaceToT_apply_inf, dif_pos rfl]
    rw [Fintype.sum_eq_add_sum_subtype_ne F (w₀ : InfinitePlace L), hw0, hsub]
    simp

/-- The restriction of a function on `↥T` to the infinite places different from `w₀`. -/
noncomputable def restrictInfinite (T : Set (Place L))
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) (f : ↥T → ℝ) :
    {w : InfinitePlace L // w ≠ (w₀ : InfinitePlace L)} → ℝ :=
  fun w' => f ⟨Place.ofInfinite w'.1, hTinf _ trivial⟩

/-- **The transfer map is onto `infSumZero T`**: a vector of `infSumZero T` is determined by its
values at the infinite places different from `w₀`, and these give an element of `logSpace L`. -/
theorem exists_logSpaceToT_eq (T : Set (Place L)) [Fintype ↥T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) (f : ↥T → ℝ)
    (hf : f ∈ infSumZero (L := L) T) :
    ∃ g : logSpace L, logSpaceToT T g = f := by
  classical
  obtain ⟨hf0, hfsum⟩ := mem_infSumZero_iff.mp hf
  set F : InfinitePlace L → ℝ := fun v => f ⟨Place.ofInfinite v, hTinf _ trivial⟩ with hFdef
  have hF : ∑ v : InfinitePlace L, F v = 0 := by
    rw [← sum_T_eq_sum_infinite T hTinf f hf0]
    exact hfsum
  have hw0 : F (w₀ : InfinitePlace L) =
      -∑ w' : {w : InfinitePlace L // w ≠ (w₀ : InfinitePlace L)}, F w' := by
    have hsplit := Fintype.sum_eq_add_sum_subtype_ne F (w₀ : InfinitePlace L)
    rw [hF] at hsplit
    linarith
  refine ⟨restrictInfinite T hTinf f, ?_⟩
  funext w
  obtain ⟨(v | q), hw⟩ := w
  · rw [logSpaceToT_apply_inf]
    by_cases h : v = (w₀ : InfinitePlace L)
    · rw [dif_pos h]
      show -∑ w' : {w : InfinitePlace L // w ≠ (w₀ : InfinitePlace L)},
        restrictInfinite T hTinf f w' = f ⟨Place.ofInfinite v, hw⟩
      rw [show f ⟨Place.ofInfinite v, hw⟩ = F v from congrArg f (Subtype.ext rfl)]
      rw [h]
      exact hw0.symm
    · rw [dif_neg h]
      show restrictInfinite T hTinf f ⟨v, h⟩ = f ⟨Place.ofInfinite v, hw⟩
      exact congrArg f (Subtype.ext rfl)
  · rw [logSpaceToT_apply_fin]
    exact (hf0 q hw).symm

/-! ### The log vector of a global unit inside the `T`-units -/

/-- At a finite place, the log vector of a global unit (embedded in the `T`-units) vanishes: a
global unit is a local unit everywhere. -/
theorem logVecLin_unitsToTUnits_finite (T : Set (Place L)) (u : Additive ((𝓞 L)ˣ))
    (q : HeightOneSpectrum (𝓞 L)) (hq : Place.ofFinite q ∈ T) :
    logVecLin T (unitsToTUnits T u) ⟨Place.ofFinite q, hq⟩ = 0 := by
  have hlocal : Units.map (algebraMap L (Place.localField L (Place.ofFinite q)))
      (Units.map (algebraMap (𝓞 L) L).toMonoidHom (Additive.toMul u)) ∈
      Place.localUnits L (Place.ofFinite q) := by
    refine (expUnit_eq_zero_iff_mem_localUnits q _).mp ((expUnit_eq_zero_iff q _).mpr ?_)
    rw [show ((Units.map (algebraMap (𝓞 L) L).toMonoidHom (Additive.toMul u) : Lˣ) : L) =
      algebraMap (𝓞 L) L ((Additive.toMul u : (𝓞 L)ˣ) : 𝓞 L) from rfl,
      HeightOneSpectrum.valuation_eq_one_iff_notMem]
    intro hmem
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem q.asIdeal hmem (Units.isUnit (Additive.toMul u)))
  rw [logVecLin_apply]
  rw [show ((Additive.toMul (unitsToTUnits T u) : TUnits T) : Lˣ) =
    Units.map (algebraMap (𝓞 L) L).toMonoidHom (Additive.toMul u) from rfl]
  show Real.log (((Idele.localAbs L (Place.ofFinite q)
    (Idele.principalIdele L (Units.map (algebraMap (𝓞 L) L).toMonoidHom (Additive.toMul u))
      (Place.ofFinite q)) : ℝˣ) : ℝ)) = 0
  rw [Idele.principalIdele_apply, Idele.localAbs_ofFinite_eq_one hlocal, Units.val_one, Real.log_one]

/-- At an infinite place `v`, the log vector of a global unit (embedded in the `T`-units) is
`v.mult * log (v u)`, the corresponding component of Mathlib's `logEmbedding`. -/
theorem logVecLin_unitsToTUnits_infinite (T : Set (Place L)) (u : Additive ((𝓞 L)ˣ))
    (v : InfinitePlace L) (hv : Place.ofInfinite v ∈ T) :
    logVecLin T (unitsToTUnits T u) ⟨Place.ofInfinite v, hv⟩ =
      (v.mult : ℝ) * Real.log (v (algebraMap (𝓞 L) L ((Additive.toMul u : (𝓞 L)ˣ) : 𝓞 L))) := by
  rw [logVecLin_apply]
  rw [show ((Additive.toMul (unitsToTUnits T u) : TUnits T) : Lˣ) =
    Units.map (algebraMap (𝓞 L) L).toMonoidHom (Additive.toMul u) from rfl]
  have hval : ((Idele.localAbs L (Place.ofInfinite v)
      (Idele.principalIdele L (Units.map (algebraMap (𝓞 L) L).toMonoidHom (Additive.toMul u))
        (Place.ofInfinite v)) : ℝˣ) : ℝ)
      = v ((Units.map (algebraMap (𝓞 L) L).toMonoidHom (Additive.toMul u) : Lˣ) : L) ^ v.mult := by
    rw [Idele.principalIdele_apply, Idele.localAbs_ofInfinite, Units.val_pow_eq_pow_val, Units.val_mk0]
    congr 1
    simpa [NumberField.InfinitePlace.Completion.algebraMap_apply] using
      (NumberField.InfinitePlace.Completion.norm_coe (v := v)
        (WithAbs.toAbs v.1 (((Units.map (algebraMap (𝓞 L) L).toMonoidHom (Additive.toMul u) : Lˣ) : L))))
  show Real.log (((Idele.localAbs L (Place.ofInfinite v)
    (Idele.principalIdele L (Units.map (algebraMap (𝓞 L) L).toMonoidHom (Additive.toMul u))
      (Place.ofInfinite v)) : ℝˣ) : ℝ)) = _
  rw [hval, Real.log_pow]
  congr 1

/-- **The transfer map identifies the log embedding of the global units with their log vectors in
the `T`-units**: `logSpaceToT T (logEmbedding L u) = logVecLin T (unitsToTUnits T u)`. -/
theorem logSpaceToT_logEmbedding (T : Set (Place L)) [Fintype ↥T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) (u : Additive ((𝓞 L)ˣ)) :
    logSpaceToT T (NumberField.Units.logEmbedding L u) =
      fun w => logVecLin T (unitsToTUnits T u) w := by
  funext w
  obtain ⟨(v | q), hw⟩ := w
  · rw [logSpaceToT_apply_inf]
    by_cases h : v = (w₀ : InfinitePlace L)
    · rw [dif_pos h]
      rw [logVecLin_unitsToTUnits_infinite T u v hw]
      rw [h]
      rw [show (∑ w' : {w : InfinitePlace L // w ≠ (w₀ : InfinitePlace L)},
          NumberField.Units.logEmbedding L u w') =
          -↑(w₀ : InfinitePlace L).mult *
            Real.log ((w₀ : InfinitePlace L) (algebraMap (𝓞 L) L ((Additive.toMul u : (𝓞 L)ˣ) : 𝓞 L)))
          from by simpa using sum_logEmbedding_component (K := L) (Additive.toMul u)]
      ring
    · rw [dif_neg h]
      rw [logVecLin_unitsToTUnits_infinite T u v hw]
      simpa using NumberField.Units.dirichletUnitTheorem.logEmbedding_component (K := L)
        (x := Additive.toMul u) ⟨v, h⟩
  · rw [logSpaceToT_apply_fin, logVecLin_unitsToTUnits_finite T u q hw]

/-! ### The main theorem -/

/-- **Dirichlet's unit result in lattice form, in the `T`-unit picture.**  Let `L` be a number
field, `T` a finite set of places of `L` containing all infinite places, and let `infSumZero T` be
the subspace of `↥T → ℝ` of vectors which vanish at every finite place of `T` and whose coordinates
sum to zero.  Then the `ℝ`-span of the log vectors of the global units, embedded in the `T`-units
via `unitsToTUnits`, is exactly `infSumZero T`.

This is the archimedean half of Milne, *CFT*, Chapter VII §3.  Mathlib's Dirichlet result is
available as `NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top`
(`Submodule.span ℝ (unitLattice L) = ⊤`, where `unitLattice L` is the `ℤ`-span of the image of
`NumberField.Units.logEmbedding L`, whose components are `w.mult * Real.log (w u)`, in the
`w₀`-dropped space `logSpace L = {w : InfinitePlace L // w ≠ w₀} → ℝ`).  The intended route
transfers it along the `ℝ`-linear isomorphism `logSpace L ≅ {U : InfinitePlace L → ℝ // ∑ w, U w = 0}`
(the `w₀`-coordinate is minus the sum of the other coordinates) and the `ℝ`-linear inclusion
`{U // ∑ U = 0} ↪ ↥T → ℝ` (defined to be `0` at the finite places, using
`NK.GlobalCFTdeep.tUnitsPlaceEquiv` to compare the sum over `↥T` with the sum over the infinite
places), identifying `logVecLin T (unitsToTUnits T u)` with the image of `logEmbedding L u` via
`NumberField.InfinitePlace.Completion.norm_coe` and `Idele.localAbs_ofFinite_eq_one` (a global unit
is a local unit everywhere). -/
theorem span_unitsToTUnits_logVecLin {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (T : Set (NK.GlobalCFT.Place L)) [Fintype ↥T]
    (hTinf : ∀ w : NK.GlobalCFT.Place L, w.IsInfinite → w ∈ T) :
    Submodule.span ℝ (Set.range (fun u : Additive ((NumberField.RingOfIntegers L)ˣ) =>
      NK.GlobalCFTdeep.logVecLin (L := L) T (NK.GlobalCFTdeep.unitsToTUnits (L := L) T u)))
      = NK.GlobalCFTdeep.LogLattice.infSumZero (L := L) T := by
  classical
  -- Mathlib's Dirichlet theorem: the log embedding of the global units spans `logSpace L`.
  have hspan : Submodule.span ℝ (Set.range (NumberField.Units.logEmbedding L)) = ⊤ := by
    have h := NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top L
    rw [NumberField.Units.unitLattice] at h
    simpa only [Submodule.map_top, LinearMap.coe_range, AddMonoidHom.coe_toIntLinearMap] using h
  -- The transfer map identifies the two families of vectors.
  have himg : (logSpaceToT T) '' (Set.range (fun u : Additive ((𝓞 L)ˣ) =>
        NumberField.Units.logEmbedding L u))
      = Set.range (fun u : Additive ((𝓞 L)ˣ) => logVecLin T (unitsToTUnits T u)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, (logSpaceToT_logEmbedding T hTinf u).symm⟩
    · rintro ⟨u, rfl⟩
      exact ⟨NumberField.Units.logEmbedding L u, ⟨u, rfl⟩,
        logSpaceToT_logEmbedding T hTinf u⟩
  -- The range of the transfer map is exactly `infSumZero T`.
  have hrange : LinearMap.range (logSpaceToT T) = infSumZero (L := L) T := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [LinearMap.mem_range] at hx
      obtain ⟨g, rfl⟩ := hx
      exact logSpaceToT_mem_infSumZero T hTinf g
    · intro f hf
      rw [LinearMap.mem_range]
      exact exists_logSpaceToT_eq T hTinf f hf
  calc Submodule.span ℝ (Set.range (fun u : Additive ((𝓞 L)ˣ) =>
          logVecLin T (unitsToTUnits T u)))
      = Submodule.span ℝ ((logSpaceToT T) '' (Set.range (fun u : Additive ((𝓞 L)ˣ) =>
          NumberField.Units.logEmbedding L u))) := by rw [himg]
    _ = Submodule.map (logSpaceToT T) (Submodule.span ℝ (Set.range (fun u : Additive ((𝓞 L)ˣ) =>
          NumberField.Units.logEmbedding L u))) := (Submodule.map_span (logSpaceToT T) _).symm
    _ = Submodule.map (logSpaceToT T) ⊤ := by rw [hspan]
    _ = LinearMap.range (logSpaceToT T) := Submodule.map_top (logSpaceToT T)
    _ = infSumZero (L := L) T := hrange

end NK.GlobalCFTdeep.LogLattice
