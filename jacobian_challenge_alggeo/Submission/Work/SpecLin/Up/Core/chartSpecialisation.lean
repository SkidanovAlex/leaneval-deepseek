/-
# Namespace mirror of `Work.SpecLin.Core.chartSpecialisation`

This file is an exact copy of `Submission/Work/SpecLin/Core/chartSpecialisation.lean` (module `Work.SpecLin.Core.chartSpecialisation`), changed in exactly three ways:

* a `namespace Up` / `end Up` pair is inserted immediately inside the file's own namespace, so
  that every declaration `Work.SpecLin.<Area>.<x>` of the original appears here as
  `Work.SpecLin.<Area>.Up.<x>` (this avoids a name clash with the original, which cannot be
  removed: the original is part of the shared library);
* references to declarations *of the mirrored modules* are rewritten accordingly (full and
  area-relative forms), and imports of those modules point at their mirrors;
* an import of `Core/linEquiv_of_sections_of_chart.lean` (the module that *states* the
  affine-chart theorem) is replaced by an import of the upstream vocabulary module
  `Core/chartVocab.lean`, which declares the same chart algebra under the same names.

The point of the mirror is to break the import cycle
`vocabulary -> statement -> ... -> proof modules -> vocabulary`: the proof modules used to take
their vocabulary from the module that states the theorem, and this made a proof of that theorem
unreachable.  The mathematics is unchanged: the mirror is a verbatim copy of verified code.

The statements of the mirrored theorems mention only names that are *upstream* of the mirror, so
`Work.SpecLin.Core.Up.chartSpecialisation` (module
`Submission.Work.SpecLin.Up.Core.chartSpecialisation`) has literally the statement of
`Work.SpecLin.Core.linEquiv_of_sections_of_chart`, which is proved from it.
-/
import Mathlib
import Submission.Work.SpecLin.Conventions
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.CurveBasics.All
import Submission.Work.CurveBasics.Linear.finiteDimensional_L
import Submission.Work.CurveBasics.Basic.eq_algebraMap_of_isAlgebraic
import Submission.Work.CurveBasics.Order.deg_div
import Submission.Work.SpecLin.Up.Alt.chartMap
import Submission.Work.SpecLin.Up.Alt.chartTensorMap_isFractionRing
import Submission.Work.SpecLin.Up.Alt.chartFibreQuotMap_isFractionRing
import Submission.Work.SpecLin.Up.Alt.isLocalization_chartTensorSectionsMap
import Submission.Work.SpecLin.Up.Alt.exists_chartTensorPoint
import Submission.Work.SpecLin.Up.Alt.exists_normalized_chartTensorMap
import Submission.Work.SpecLin.Setup.unitOfGenericUnit
import Submission.Work.SpecLin.Content.isPrincipal_of_fg_of_cyclic_map_quotient
import Submission.Work.SpecLin.Core.ord_germ_eq_iff_mem_pow
import Submission.Work.SpecLin.Up.Core.mem_primeIdealOf_ptToPoint_iff
import Submission.Work.SpecLin.Up.Core.mem_primeIdealOf_closedPt_iff
import Submission.Work.SpecLin.Up.Core.section_prime_genFibre_quot
import Submission.Work.SpecLin.Core.section_prime_sup_fibre_quot
import Submission.Work.SpecLin.Alt.not_isField_chartSections
import Submission.Work.SpecLin.Up.Alt.chartTensorMap_isFractionRing
import Submission.Work.SpecLin.Chart.exists_isAffineOpen_containing
import Submission.Work.SpecLin.Up.Alt.chartReading
import Submission.Work.SpecLin.Alt.exists_num_denom_of_isUnitAt
import Submission.Work.SpecLin.Alt.exists_isAffineOpen_containing_pts
import Submission.Work.SpecLin.Alt.exists_mul_eq_iff_ordAt_of_primeIdealOf
import Submission.Work.SpecLin.Up.Alt.exists_chartTensorFibrePoint
import Submission.Work.CurveBasics.BaseChange.isAffineOpen_bcOpens
import Submission.Work.SpecLin.Up.Setup.cruxChartPull
import Submission.Work.SpecLin.Up.Core.cruxUnitAtMaximal
import Submission.Work.SpecLin.Up.Core.orderDataSectionEquation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct Classical

namespace Work.SpecLin.Core
namespace Up

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}

/-! ## Compatibility of the chart dictionary with restriction to a smaller affine open

This is the technical input for the *independence of the reduction of `h` of the auxiliary
affine chart* (step (6) of the proof plan).
-/

section Restrict

/-- Restriction of the coordinate ring of an affine chart of the curve along an inclusion of
opens, as a `K`-algebra map. -/
noncomputable def chartResAlgHom {Z W : C.left.Opens} (hZW : Z ≤ W) :
    Γ(C.left, W) →ₐ[K] Γ(C.left, Z) where
  toRingHom := (C.left.presheaf.map (homOfLE hZW).op).hom
  commutes' k := by
    show (C.left.presheaf.map (homOfLE hZW).op).hom
        (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ C.hom.appLE ⊤ W le_top).hom k)
      = (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ C.hom.appLE ⊤ Z le_top).hom k)
    have h := Scheme.Hom.appLE_map (f := C.hom) (U := (⊤ : (Spec (CommRingCat.of K)).Opens))
      (V := W) (V' := Z) le_top (homOfLE hZW).op
    have h2 := congrArg (fun (φ) => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k)) h
    simpa only [ConcreteCategory.comp_apply] using h2

variable (R : Type u) [CommRing R] [Algebra K R]

/-- Restriction of the relative chart ring `B_W = Γ(C,W) ⊗_K R` to `B_Z = Γ(C,Z) ⊗_K R`. -/
noncomputable def chartRestrict {Z W : C.left.Opens} (hZW : Z ≤ W) :
    chartTensor (K := K) (C := C) R W →ₐ[K] chartTensor (K := K) (C := C) R Z :=
  Algebra.TensorProduct.map (chartResAlgHom (K := K) (C := C) hZW) (AlgHom.id K R)

end Restrict

/-! ## The chart dictionary on pure tensors -/

section PureTensor

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]

open Work.CurveBasics in
/-- The reduction map on a pure tensor. -/
theorem chartTensorRedMap_tmul (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (a : Γ(C.left, W)) (r : R) :
    Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW (a ⊗ₜ[K] r)
      = (Curve.functionFieldMap C (IsLocalRing.ResidueField R)).hom
            ((Curve.germToFunctionField C W).hom a)
          * algebraMap (IsLocalRing.ResidueField R)
              ((C.baseChange (IsLocalRing.ResidueField R)).functionField)
              (algebraMap R (IsLocalRing.ResidueField R) r) := by
  have h : (a ⊗ₜ[K] r) = (a ⊗ₜ[K] (1 : R)) * ((1 : Γ(C.left, W)) ⊗ₜ[K] r) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, Alt.Up.chartTensorRedMap_tmul_one, Alt.Up.chartTensorRedMap_one_tmul]

open Work.CurveBasics in
/-- The generic-fibre chart map on a pure tensor. -/
theorem chartTensorMap_tmul (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (a : Γ(C.left, W)) (r : R) :
    Alt.Up.chartTensorMap (K := K) (C := C) R W hW (a ⊗ₜ[K] r)
      = (Curve.functionFieldMap C (FractionRing R)).hom
            ((Curve.germToFunctionField C W).hom a)
          * algebraMap (FractionRing R)
              ((C.baseChange (FractionRing R)).functionField)
              (algebraMap R (FractionRing R) r) := by
  have h : (a ⊗ₜ[K] r) = (a ⊗ₜ[K] (1 : R)) * ((1 : Γ(C.left, W)) ⊗ₜ[K] r) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, Alt.Up.chartTensorMap_tmul_one, Alt.Up.chartTensorMap_one_tmul]

open Work.CurveBasics in
/-- Restriction to a smaller affine open does not change the germ in the function field. -/
theorem germToFunctionField_restrict {Z W : C.left.Opens} (hZW : Z ≤ W)
    [Nonempty Z] [Nonempty W] (a : Γ(C.left, W)) :
    (Curve.germToFunctionField C Z).hom (chartResAlgHom (K := K) (C := C) hZW a)
      = (Curve.germToFunctionField C W).hom a := by
  have hmem : genericPoint C.left ∈ Z :=
    ((genericPoint_spec C.left).mem_open_set_iff Z.isOpen).mpr (by simpa using ‹Nonempty Z›)
  have h := TopCat.Presheaf.germ_res C.left.presheaf (homOfLE hZW) (genericPoint C.left) hmem
  have h2 := congrArg (fun (f : Γ(C.left, W) ⟶ C.functionField) => f.hom a) h
  rw [show (chartResAlgHom (K := K) (C := C) hZW a)
      = (C.left.presheaf.map (homOfLE hZW).op).hom a from rfl]
  exact h2

open Work.CurveBasics in
/-- **The reduction map is compatible with restriction to a smaller affine open.** -/
theorem chartTensorRedMap_restrict {Z W : C.left.Opens} (hZW : Z ≤ W)
    (hZ : IsAffineOpen Z) (hW : IsAffineOpen W) [Nonempty Z] [Nonempty W]
    (x : chartTensor (K := K) (C := C) R W) :
    Alt.Up.chartTensorRedMap (K := K) (C := C) R Z hZ
        (chartRestrict (K := K) (C := C) R hZW x)
      = Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW x := by
  induction x using TensorProduct.inductionOn with
  | tmul a r =>
    rw [show chartRestrict (K := K) (C := C) R hZW (a ⊗ₜ[K] r)
        = (chartResAlgHom (K := K) (C := C) hZW a) ⊗ₜ[K] r from rfl]
    rw [chartTensorRedMap_tmul, chartTensorRedMap_tmul, germToFunctionField_restrict]
  | add x y hx hy => simp only [map_add, hx, hy]

open Work.CurveBasics in
/-- **The generic-fibre chart map is compatible with restriction to a smaller affine open.** -/
theorem chartTensorMap_restrict {Z W : C.left.Opens} (hZW : Z ≤ W)
    (hZ : IsAffineOpen Z) (hW : IsAffineOpen W) [Nonempty Z] [Nonempty W]
    (x : chartTensor (K := K) (C := C) R W) :
    Alt.Up.chartTensorMap (K := K) (C := C) R Z hZ
        (chartRestrict (K := K) (C := C) R hZW x)
      = Alt.Up.chartTensorMap (K := K) (C := C) R W hW x := by
  induction x using TensorProduct.inductionOn with
  | tmul a r =>
    rw [show chartRestrict (K := K) (C := C) R hZW (a ⊗ₜ[K] r)
        = (chartResAlgHom (K := K) (C := C) hZW a) ⊗ₜ[K] r from rfl]
    rw [chartTensorMap_tmul, chartTensorMap_tmul, germToFunctionField_restrict]
  | add x y hx hy => simp only [map_add, hx, hy]

end PureTensor

/-! ## State of this file and the remaining gap (session notes)

### Proved in this file (sorry-free)

* `chartResAlgHom`, `chartRestrict` — restriction of the relative chart ring
  `B_W = Γ(C,W) ⊗_K R` to `B_Z = Γ(C,Z) ⊗_K R` for `Z ≤ W`;
* `chartTensorRedMap_tmul`, `chartTensorMap_tmul` — the chart dictionary maps on pure tensors,
  in the form `red_W (a ⊗ r) = fldMap_F/κ (germ_W a) * algebraMap (residue r)`;
* `germToFunctionField_restrict` — the germ of a section only depends on the chart;
* `chartTensorRedMap_restrict`, `chartTensorMap_restrict` — the chart dictionary maps are
  compatible with restriction to a smaller affine open.  This is the input for the
  *independence of the reduction `h̄` of `h` of the auxiliary chart* (and hence for the
  globalisation argument (C5)/(6) of the proof plan).
* `chartTensorRedMap_eq_zero_iff`, `chartTensorRedMap_ne_zero` — the kernel of the reduction
  map is exactly the fibre prime `P = 𝔪_R·B`.
* `chartTensorRedSectionsMap_surjective`, `ker_chartTensorRedSectionsMap` — the same map in its
  sections form `B → Γ(C_κ, W_κ)` is surjective with kernel `P`.
* `exists_chartTensorFibrePoint` — **the special-fibre point/order dictionary**: for a maximal
  `N ⊇ P` there is a *closed* point `z ∈ W_κ` with
  `x ∈ 𝒪_{C_κ,z}` (equivalently `0 ≤ ord_z x`) `↔ ∃ a b ∈ B, b ∉ N ∧ x = red a / red b`.
* `ordFrac_eq_exp_one_of_span_eq_maximalIdeal` — a generator of the maximal ideal of a discrete
  valuation ring has order one (`Ring.ordFrac = WithZero.exp 1`); the general form of
  `Work.CurveBasics.Place.ord_uniformizer`.
* `ordAt_eq_one_of_span_eq_maximalIdeal` — **the `ν_𝔫(f) = 1` half of the local reading-off**:
  if the image of `a` in `K(C_κ)` generates the maximal ideal of the local ring `𝒪_{C_κ,Q}`
  (i.e. `a` is a uniformizer), then `ord_Q a = 1`.
* `chartIdealMem`, `chartMaximalMem`, `exists_chartTensorFibrePoint_maximalIdeal` — **the
  maximal-ideal dictionary**: for a maximal `N ⊇ P` there is a closed point `z ∈ W_κ` for which

    `x = red a / red b` with `a ∈ N`, `b ∉ N`   is equivalent to   `x ∈ (𝔪_z)`

  i.e. `x` lies in the ideal generated by the image of `N` in `𝒪_{C_κ,z}` exactly when it is the
  image of an element of the maximal ideal.  (The two named predicates are needed: `∃`-binders
  parse greedily through `↔`, so the two sides must be given as atomic predicates.)

**Still missing for the full local reading-off.**  With the maximal-ideal dictionary available,
the B-side hypothesis `(f)·B_𝔫 + P·B_𝔫 = N·B_𝔫` gives (i) `red f ∈ 𝒪_{C_κ,z}` and (ii)
`(red f)·𝒪_{C_κ,z} = 𝔪_z`, so `ordAt_eq_one_of_span_eq_maximalIdeal` yields `ord_z(red f) = 1`.
The `0` case is the dual statement (if `f` generates `I` at `N` and `N ≠ I ⊔ P` then `f` is a
*unit* of `B_𝔫`, so `red f` is a unit of `𝒪_{C_κ,z}` and the order is `0`, using the dictionary
twice together with `Order.ordAt_inv`).  Remaining formalities encountered on the way:
`∃`-binders parse greedily through `↔` (give the two sides as named predicates, as done here);
`IsScalarTower.algebraMap_apply` runs in the direction `algebraMap R A x = algebraMap S A
(algebraMap R S x)`, so a tower is *collapsed* with `rw [← …]`; and
`IsLocalization.AtPrime.to_map_mem_maximal_iff`, `isUnit_to_map_iff` and `mk'_mem_maximal_iff`
must be given `(S := …)` (the localised ring) and `(I := …)` explicitly, otherwise the instance
search is stuck on a metavariable.

### The remaining gap, precisely

The affine-chart proof of `chartSpecialisation` reduces to the following statement, in the
notation of the proof plan (`B = Γ(C,W) ⊗_K R`, `P = chartFibrePrime R W = 𝔪_R·B`,
`I_m = sectionPrime` for the section `s m`, `J_m` for `t m`, `F = Frac R`, `κ = R/𝔪_R`).

Let `h' ∈ K(C_F)^×` be a rational function with

  `div_{C_F}(h') = Σ_m [s_m^F] - Σ_m [t_m^F]`  and  `h' ∈ B_P^×`

(the content normalisation `Alt.Up.exists_normalized_chartTensorMap` produces such an `h'` from any
`h` with `div h = Σ[s_m^F] - Σ[t_m^F]`, with `div h' = div h`).  Then for every maximal ideal
`𝔫 ⊇ P` of `B`, writing `h' = a/b` with `a, b ∈ B ∖ P` and `h̄ = ρ(a)/ρ(b)` for the reduction
`ρ = chartTensorRedMap`, one has

  `ord_{𝔫̄}(h̄) = #{m : 𝔫 = I_m + P} - #{m : 𝔫 = J_m + P}`.

Equivalently, `ν_𝔫(h') = #{m : 𝔫 = I_m ⊔ P} - #{m : 𝔫 = J_m ⊔ P}` where
`ν_𝔫(x) = max{k : x ∈ 𝔫^k + P}` for `x ∈ B ∖ P`.

**What is available.**  Writing `u := h' · Π_m g_m / Π_m f_m` for `f_m` (resp. `g_m`) a generator
of `I_m B_𝔫` (resp. `J_m B_𝔫`) lifted to `B`:

* `u ∈ B_P^×`, and `u` is a unit at every *vertical* height-one prime `𝔮 ⊆ P` of `B`
  (because `h', f_m, g_m ∉ P`);
* for every height-one prime `𝔮 ≤ 𝔫` one has `ord_𝔮(f_m) = [𝔮 = I_m] = ord_𝔮(g_m)⁻¹`-correctly,
  i.e. `ord_𝔮(u) = 0` — this is where the hypothesis `div h' = Σ[s^F] - Σ[t^F]` enters (via the
  chart dictionary for the generic fibre, `Alt.Up.exists_chartTensorPoint`) and where the choice of
  the lifts `f_m ∈ I_m` matters (an element of `I_m` generating `I_m B_𝔫` also generates the
  prime `I_m B_𝔫` of `B_𝔫`, whose only height-one overprime is itself; the extra zeros of the
  lift can be moved off `𝔫` but **not** in general off the whole of `Spec B`);
* the local computation `ν_𝔫(f_m) = [𝔫 = I_m + P]` is elementary
  (`Core.sectionEquation.mem_iff_eq_sup_of_span_eq` + `Core.section_prime_sup_fibre_quot`).

**The gap.**  To conclude one needs

  `u ∈ B_P^× ∧ (∀ height-one 𝔮 ≤ 𝔫, ord_𝔮(u) = 0)  ⟹  u ∈ B_𝔫^×`

(so that `ν_𝔫(u) = 0`), the "conservation of number" step (C4) of
`Alt/NOTES_chartCore.md`.  Two routes are recorded in the notes:

1. *Via integral closedness* (`Setup/NOTES_keyUnit_crux.md`): if `u` is a unit at **every**
   height-one prime of `B`, then `Setup.unitOfGenericUnit` gives `u ∈ B^×`.  This needs the
   lifts `f_m ∈ I_m` to satisfy `div_{Spec B}(f_m) = [I_m]`, which is **false** in general
   (it would force `[s_m^F] - [Q]` to be principal for a point `Q` of the complement of the
   chart; on an elliptic curve with a chart `C ∖ {q}` this fails whenever `s_m^F ≁ q`).
2. *Via Noetherianity / Krull* (`Alt.conservationNumber_noetherian`): correct when `B_𝔫` is
   Noetherian (in particular when `R` is a discrete valuation ring), but not available for a
   general (non-Noetherian) valuation ring.

**Candidate complete strategies** (not yet formalised).

* *Auxiliary element.*  Instead of `u = h'Πg/Πf` use `v := h' · Π_m f_m / Π_m g_m` with the
  lifts chosen so that `div_{Spec B}(v)` is *provably* zero; the divisor of `v` is supported on
  the ht-1 primes where the lifts have "extra" zeros, and those can be chosen (prime avoidance)
  to avoid a prescribed finite set of ht-1 primes — enough for the *pointwise* statement at
  `𝔫`, but not for the global statement used by (1).
* *Double induction on `dim R`.*  For `dim R ≥ 2` pick `0 ⊊ 𝔭 ⊊ 𝔪` and combine
  (i) the inductive statement for the DVR-ish localisation `R_𝔭` (`dim R_𝔭 = ht 𝔭 < dim R`),
  which produces the rational function `h̄` on `C_{κ(𝔭)}`, with
  (ii) the inductive statement for `R̄ = R/𝔭` (`dim R̄ = dim R - ht 𝔭 < dim R`) applied to the
  `R̄`-points `specOfMap (R → R̄) ≫ s_m` — the generic fibre of the latter is
  `specOfMap (R → κ(𝔭)) ≫ s_m = genPt R_𝔭 ≫ (RPt.map (R → R_𝔭) (s m))`, so the two applications
  match exactly.  This reduces everything to `dim R = 1` (a 1-dimensional valuation ring, not
  necessarily discrete), which is the remaining genuine case.
-/


section ReductionKernel

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]

/-- **The kernel of the reduction map is the fibre prime.**  An element of the relative chart
ring has zero reduction to the special fibre exactly when it lies in `P = 𝔪_R·B`. -/
theorem chartTensorRedMap_eq_zero_iff (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (x : chartTensor (K := K) (C := C) R W) :
    Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW x = 0
      ↔ x ∈ chartFibrePrime (K := K) (C := C) R W := by
  constructor
  · intro hx
    letI : Algebra (chartTensor (K := K) (C := C) R W ⧸
        chartFibrePrime (K := K) (C := C) R W)
        ((C.baseChange (IsLocalRing.ResidueField R)).functionField) :=
      (Alt.Up.chartFibreQuotMap (K := K) (C := C) R W hW).toAlgebra
    haveI : IsFractionRing (chartTensor (K := K) (C := C) R W ⧸
        chartFibrePrime (K := K) (C := C) R W)
        ((C.baseChange (IsLocalRing.ResidueField R)).functionField) :=
      Alt.Up.chartFibreQuotMap_isFractionRing R W hW
    have hinj : Function.Injective (algebraMap (chartTensor (K := K) (C := C) R W ⧸
        chartFibrePrime (K := K) (C := C) R W)
        ((C.baseChange (IsLocalRing.ResidueField R)).functionField)) :=
      IsFractionRing.injective _ _
    refine Ideal.Quotient.eq_zero_iff_mem.mp (hinj ?_)
    rw [map_zero, RingHom.algebraMap_toAlgebra, Alt.Up.chartFibreQuotMap_mk]
    exact hx
  · intro hx
    exact Alt.Up.chartFibrePrime_le_ker_redMap (K := K) (C := C) R W hW hx

/-- The reduction map is nonzero on elements which are units modulo the special fibre. -/
theorem chartTensorRedMap_ne_zero (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W]
    {x : chartTensor (K := K) (C := C) R W}
    (hx : x ∉ chartFibrePrime (K := K) (C := C) R W) :
    Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW x ≠ 0 :=
  fun h => hx ((chartTensorRedMap_eq_zero_iff (K := K) (C := C) R W hW x).mp h)

end ReductionKernel


/-! ## The special-fibre point/order dictionary

For a maximal ideal `N ⊇ P = chartFibrePrime R W` of the relative chart ring `B` there is a
*closed* point `z` of the chart `W_κ ⊆ C_κ` of the special fibre such that a rational function
`x ∈ K(C_κ)` lies in the local ring `𝒪_{C_κ,z}` — equivalently, has nonnegative order at `z` —
exactly when it can be written as `red a / red b` with `a, b ∈ B` and `b ∉ N`.

This is the special-fibre analogue of `Alt.Up.exists_chartTensorPoint`; it is the dictionary that
translates the local-algebra computation in `B_𝔫` into an order of vanishing on `C_κ`.
-/

section FibreDictionary

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]

open Work.CurveBasics in
/-- The sections form of the reduction map is surjective: it is the composition of the
(surjective) reduction of the second tensor factor and the identification of the sections of
the base-changed chart with the tensor product. -/
theorem chartTensorRedSectionsMap_surjective (W : C.left.Opens) (hW : IsAffineOpen W)
    [Nonempty W] :
    Function.Surjective (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW) := by
  have hmap : Function.Surjective (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left, W))
      (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a c =>
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
      refine ⟨a ⊗ₜ[K] r, ?_⟩
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply]
      rfl
    | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      exact ⟨x' + y', by rw [map_add, hx', hy']⟩
  intro y
  have hbij := Alt.Up.sectionsLift_bijective (Curve.bcSquare C (IsLocalRing.ResidueField R)) W hW
  obtain ⟨z, hz⟩ := hbij.2 y
  obtain ⟨w, hw⟩ := hmap z
  exact ⟨w, by
    rw [show Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW w
        = Curve.BCSquare.sectionsLift (Curve.bcSquare C (IsLocalRing.ResidueField R)) W hW
            (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left, W))
              (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) w) from rfl,
      hw, hz]⟩

open Work.CurveBasics in
/-- **The kernel of the sections-form reduction map is the fibre prime.** -/
theorem ker_chartTensorRedSectionsMap (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    RingHom.ker (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)
      = chartFibrePrime (K := K) (C := C) R W := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [RingHom.mem_ker] at hx
    refine (chartTensorRedMap_eq_zero_iff (K := K) (C := C) R W hW x).mp ?_
    rw [show Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW x
        = (Curve.germToFunctionField (C.baseChange (IsLocalRing.ResidueField R))
            (C.bcOpens (IsLocalRing.ResidueField R) W)).hom
            (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW x) from rfl, hx, map_zero]
  · intro x hx
    rw [RingHom.mem_ker]
    haveI : Nonempty (C.bcOpens (IsLocalRing.ResidueField R) W) :=
      C.bcOpens_nonempty (IsLocalRing.ResidueField R) W
    have hgerm : (Curve.germToFunctionField (C.baseChange (IsLocalRing.ResidueField R))
        (C.bcOpens (IsLocalRing.ResidueField R) W)).hom
        (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW x) = 0 := by
      rw [← show Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW x
        = (Curve.germToFunctionField (C.baseChange (IsLocalRing.ResidueField R))
            (C.bcOpens (IsLocalRing.ResidueField R) W)).hom
            (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW x) from rfl]
      exact (chartTensorRedMap_eq_zero_iff (K := K) (C := C) R W hW x).mpr hx
    exact Scheme.germToFunctionField_injective (C.baseChange (IsLocalRing.ResidueField R)).left
      (C.bcOpens (IsLocalRing.ResidueField R) W) (by rw [hgerm, map_zero])

open Work.CurveBasics in
/-- **The special-fibre point/order dictionary.**  Let `N ⊇ P = 𝔪_R·B` be a maximal ideal of the
relative chart ring `B = Γ(C,W) ⊗_K R`.  Then there is a closed point `z` of the chart
`W_κ ⊆ C_κ` of the special fibre such that, for every `x ∈ K(C_κ)`, `x` lies in the local ring
`𝒪_{C_κ,z}` — equivalently `0 ≤ ord_z x` — exactly when `x = red a / red b` for elements
`a, b ∈ B` with `b ∉ N`.

The proof is the special-fibre analogue of `Alt.Up.exists_chartTensorPoint`: the membership in the
local ring is translated into the existence of `a, b` by
`Alt.mem_range_algebraMap_iff_exists_mul_eq`, the point `z` is cut out by the image `N'` of `N` in
the sections `Γ(C_κ, W_κ)` (which is maximal, and nonzero because a chart ring of a curve is not a
field), and the nonnegativity of the order at a closed point is
`CurveBasics.BaseChange.mem_range_algebraMap_stalk_iff`. -/
theorem exists_chartTensorFibrePoint (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (N : Ideal (chartTensor (K := K) (C := C) R W)) [N.IsMaximal]
    (hPN : chartFibrePrime (K := K) (C := C) R W ≤ N) :
    ∃ z : (C.baseChange (IsLocalRing.ResidueField R)).Place,
      z.point ∈ C.bcOpens (IsLocalRing.ResidueField R) W ∧
      (∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
        (∃ a b : chartTensor (K := K) (C := C) R W, b ∉ N ∧
            x * Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW b
              = Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW a)
          ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z) := by
  classical
  have hSaff : IsAffineOpen (C.bcOpens (IsLocalRing.ResidueField R) W) :=
    Work.CurveBasics.BaseChange.isAffineOpen_bcOpens (IsLocalRing.ResidueField R) W hW
  have hSne : Nonempty (C.bcOpens (IsLocalRing.ResidueField R) W) :=
    C.bcOpens_nonempty (IsLocalRing.ResidueField R) W
  have hsurj := chartTensorRedSectionsMap_surjective (K := K) (C := C) R W hW
  have hker := ker_chartTensorRedSectionsMap (K := K) (C := C) R W hW
  have hN'max : (N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj (hker ▸ hPN)
  have hN'ne : N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hN'max
      (Alt.not_isField_chartSections (C.baseChange (IsLocalRing.ResidueField R))
        (C.bcOpens (IsLocalRing.ResidueField R) W) hSaff)
  have hcomap : (N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)).comap
      (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW) = N :=
    Ideal.comap_map_eq_self_of_isMaximal _ hN'max.ne_top
  let z0 : (C.baseChange (IsLocalRing.ResidueField R)).left :=
    hSaff.fromSpec
      ⟨N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW), hN'max.isPrime⟩
  have hz0mem : z0 ∈ C.bcOpens (IsLocalRing.ResidueField R) W := by
    change z0 ∈ (C.bcOpens (IsLocalRing.ResidueField R) W : Set _)
    rw [← hSaff.range_fromSpec]
    exact ⟨_, rfl⟩
  have hz0prime : hSaff.primeIdealOf ⟨z0, hz0mem⟩
      = ⟨N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW), hN'max.isPrime⟩ := by
    show hSaff.isoSpec.hom ⟨z0, hz0mem⟩ = _
    have h1 : (⟨z0, hz0mem⟩ : ↥(C.bcOpens (IsLocalRing.ResidueField R) W))
        = hSaff.isoSpec.inv
            ⟨N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW),
              hN'max.isPrime⟩ := Subtype.ext rfl
    rw [h1]
    exact Homeomorph.apply_symm_apply (Scheme.homeoOfIso hSaff.isoSpec) _
  have hz0cl : IsClosed ({z0} : Set (C.baseChange (IsLocalRing.ResidueField R)).left) := by
    rcases Curve.eq_genericPoint_or_isClosed (C.baseChange (IsLocalRing.ResidueField R)) z0 with
      hgen | hcl
    · exfalso
      have hmem : genericPoint (C.baseChange (IsLocalRing.ResidueField R)).left
          ∈ C.bcOpens (IsLocalRing.ResidueField R) W := hgen ▸ hz0mem
      have hbot : hSaff.primeIdealOf ⟨genericPoint _, hmem⟩ = (⊥ : PrimeSpectrum _) := by
        rw [hSaff.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
      have h2 : hSaff.primeIdealOf ⟨genericPoint _, hmem⟩
          = ⟨N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW),
              hN'max.isPrime⟩ := by
        rw [show (⟨genericPoint _, hmem⟩ : ↥(C.bcOpens (IsLocalRing.ResidueField R) W))
            = ⟨z0, hz0mem⟩ from Subtype.ext hgen.symm]
        exact hz0prime
      exact hN'ne (congrArg PrimeSpectrum.asIdeal (h2.symm.trans hbot))
    · exact hcl
  refine ⟨⟨z0, hz0cl⟩, hz0mem, fun x => ?_⟩
  -- the algebra structure on `K(C_κ)` induced by the reduction map
  letI : Algebra (chartTensor (K := K) (C := C) R W)
      (C.baseChange (IsLocalRing.ResidueField R)).functionField :=
    (Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW).toAlgebra
  letI : Algebra (Γ((C.baseChange (IsLocalRing.ResidueField R)).left,
      (C.bcSquare (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W))
      ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0) :=
    TopCat.Presheaf.algebra_section_stalk (C.baseChange (IsLocalRing.ResidueField R)).left.presheaf
      ⟨z0, hz0mem⟩
  haveI hN'prime : (N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)).IsPrime :=
    hN'max.isPrime
  haveI hloc : IsLocalization.AtPrime
      ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0)
      (N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)) :=
    hSaff.isLocalization_stalk' ⟨_, hN'max.isPrime⟩ hz0mem
  haveI hST : IsScalarTower (Γ((C.baseChange (IsLocalRing.ResidueField R)).left,
      (C.bcSquare (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W))
      ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0)
      (C.baseChange (IsLocalRing.ResidueField R)).functionField :=
    functionField_isScalarTower (C.baseChange (IsLocalRing.ResidueField R)).left
      (C.bcOpens (IsLocalRing.ResidueField R) W) ⟨z0, hz0mem⟩
  rw [← Work.CurveBasics.BaseChange.mem_range_algebraMap_stalk_iff
    (C.baseChange (IsLocalRing.ResidueField R)) ⟨z0, hz0cl⟩ x]
  rw [Alt.mem_range_algebraMap_iff_exists_mul_eq
      (R := Γ((C.baseChange (IsLocalRing.ResidueField R)).left,
        (C.bcSquare (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W))
      (S := (C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0)
      (K := (C.baseChange (IsLocalRing.ResidueField R)).functionField)
      (N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)) x]
  have hred : ∀ y : chartTensor (K := K) (C := C) R W,
      Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW y
        = (algebraMap (Γ((C.baseChange (IsLocalRing.ResidueField R)).left,
            (C.bcSquare (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W))
            ((C.baseChange (IsLocalRing.ResidueField R)).functionField))
            (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW y) := by
    intro y
    rw [Alt.Up.chartTensorRedMap_eq_germ_comp_sectionsMap]
    rfl
  constructor
  · rintro ⟨a, b, hb, hab⟩
    refine ⟨Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW a,
      Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW b, ?_, ?_⟩
    · intro hmem
      exact hb (by rw [← hcomap]; exact Ideal.mem_comap.mpr hmem)
    · rw [← hred b, ← hred a]
      exact hab
  · rintro ⟨a', b', hb', hab⟩
    obtain ⟨a, rfl⟩ := hsurj a'
    obtain ⟨b, rfl⟩ := hsurj b'
    refine ⟨a, b, ?_, ?_⟩
    · intro hmem
      exact hb' (Ideal.mem_map_of_mem (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW) hmem)
    · rw [hred b, hred a]
      exact hab


end FibreDictionary


/-! ## The local reading-off

With the point/order dictionary in hand, the local algebra of `B_𝔫` can be read off on `C_κ`:
an element of the relative chart ring which *generates* the maximal ideal of the local ring
`B_𝔫` modulo `P` — i.e. a "section equation" — has order of vanishing exactly `1` at the
corresponding point of the special fibre.
-/

section ReadingOff

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]

/-- **A generator of the maximal ideal of a discrete valuation ring is a uniformizer**: its
image in the fraction field has order one in `ℤᵐ⁰`. -/
theorem ordFrac_eq_exp_one_of_span_eq_maximalIdeal {A K : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (a : A) (hspan : Ideal.span ({a} : Set A) = IsLocalRing.maximalIdeal A) :
    Ring.ordFrac A (algebraMap A K a) = WithZero.exp 1 := by
  have hassoc : Associated a (Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A)) := by
    rw [← Ideal.span_singleton_eq_span_singleton, hspan]
    exact (Submodule.IsPrincipal.span_singleton_generator (IsLocalRing.maximalIdeal A)).symm
  exact Ring.ordFrac_irreducible (hassoc.irreducible_iff.mpr
    (Work.CurveBasics.irreducible_generator_maximalIdeal (R := A)))

open Work.CurveBasics in
/-- **The `ν_𝔫(f) = 1` half of the local reading-off.**  If `a` generates the maximal ideal of
the local ring of `C_κ` at a closed point `Q` (equivalently: `a` is a uniformizer of the discrete
valuation ring `𝒪_{C_κ,Q}`), then the image of `a` in `K(C_κ)` has order of vanishing one at `Q`. -/
theorem ordAt_eq_one_of_span_eq_maximalIdeal
    (Q : (C.baseChange (IsLocalRing.ResidueField R)).Place)
    (a : (C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk Q.point)
    (hspan : Ideal.span ({a} : Set _) = IsLocalRing.maximalIdeal
      ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk Q.point)) (ha : a ≠ 0) :
    (C.baseChange (IsLocalRing.ResidueField R)).ordAt
      (algebraMap ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk Q.point)
        ((C.baseChange (IsLocalRing.ResidueField R)).functionField) a) Q = 1 := by
  haveI hdvr : IsDiscreteValuationRing
      ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk Q.point) :=
    Place.isDiscreteValuationRing Q
  have hco : Order.coheight Q.point = 1 := Q.eq_coheight_one
  show Scheme.ord (algebraMap
      ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk Q.point)
      ((C.baseChange (IsLocalRing.ResidueField R)).functionField) a) Q.point = 1
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hco]
  rw [show Scheme.ordHom Q.point hco =
      Ring.ordFrac ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk Q.point)
      from rfl]
  rw [ordFrac_eq_exp_one_of_span_eq_maximalIdeal a hspan]
  simp [WithZero.exp]

end ReadingOff


section MaximalIdealDictionary

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]

open Work.CurveBasics in
/-- `x` lies in the ideal generated, in the local ring `𝒪_{C_κ,z}`, by the image of the maximal
ideal `N` of the relative chart ring: `x = red a / red b` with `a ∈ N` and `b ∉ N`. -/
noncomputable def chartIdealMem (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (N : Ideal (chartTensor (K := K) (C := C) R W))
    (x : (C.baseChange (IsLocalRing.ResidueField R)).functionField) : Prop :=
  ∃ a b : chartTensor (K := K) (C := C) R W, b ∉ N ∧ a ∈ N ∧
    x * Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW b
      = Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW a

open Work.CurveBasics in
/-- `x` is the image of an element of the maximal ideal of the local ring `𝒪_{C_κ,z}`. -/
noncomputable def chartMaximalMem (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (z : (C.baseChange (IsLocalRing.ResidueField R)).Place)
    (x : (C.baseChange (IsLocalRing.ResidueField R)).functionField) : Prop :=
  ∃ a : (C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z.point,
    (algebraMap ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z.point)
        ((C.baseChange (IsLocalRing.ResidueField R)).functionField) a = x ∧
      a ∈ IsLocalRing.maximalIdeal
        ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z.point))

open Work.CurveBasics in
/-- **The maximal-ideal dictionary.**  For a maximal ideal `N ⊇ P = chartFibrePrime R W` of the
relative chart ring `B = Γ(C,W) ⊗_K R` there is a closed point `z` of the chart `W_κ ⊆ C_κ` of
the special fibre such that, for every `x ∈ K(C_κ)`,

  "`x = red a / red b` with `a ∈ N`, `b ∉ N`"

— i.e. `x` lies in the ideal generated by the image of `N` in the local ring `𝒪_{C_κ,z}` — is
equivalent to "`x` is the image of an element of the maximal ideal `𝔪_z` of `𝒪_{C_κ,z}`".

This is the ideal/power analogue of `exists_chartTensorFibrePoint` and the input for the local
reading-off: applied to an `f` which generates `N` modulo `P` it gives
`(red f)·𝒪_{C_κ,z} = 𝔪_z`.  The proof has the same two steps: the *sections* form of the statement
is the localisation description of the maximal ideal, via
`IsLocalization.AtPrime.to_map_mem_maximal_iff` and `IsLocalization.surj` for the forward
direction and `IsLocalization.AtPrime.mk'_mem_maximal_iff` for the backward one; it is then
transferred from `Γ(C_κ, W_κ)` to `B` using that `chartTensorRedSectionsMap` is surjective with
kernel `P` and `Ideal.comap_map_eq_self_of_isMaximal`. -/
theorem exists_chartTensorFibrePoint_maximalIdeal (W : C.left.Opens) (hW : IsAffineOpen W)
    [Nonempty W] (N : Ideal (chartTensor (K := K) (C := C) R W)) [N.IsMaximal]
    (hPN : chartFibrePrime (K := K) (C := C) R W ≤ N) :
    ∃ z : (C.baseChange (IsLocalRing.ResidueField R)).Place,
      ∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
        chartMaximalMem (K := K) (C := C) R z x ↔ chartIdealMem (K := K) (C := C) R W hW N x := by
  classical
  have hSaff : IsAffineOpen (C.bcOpens (IsLocalRing.ResidueField R) W) :=
    Work.CurveBasics.BaseChange.isAffineOpen_bcOpens (IsLocalRing.ResidueField R) W hW
  have hsurj := chartTensorRedSectionsMap_surjective (K := K) (C := C) R W hW
  have hker := ker_chartTensorRedSectionsMap (K := K) (C := C) R W hW
  have hN'max : (N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj (hker ▸ hPN)
  have hN'ne : N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hN'max
      (Alt.not_isField_chartSections (C.baseChange (IsLocalRing.ResidueField R))
        (C.bcOpens (IsLocalRing.ResidueField R) W) hSaff)
  have hcomap : (N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)).comap
      (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW) = N :=
    Ideal.comap_map_eq_self_of_isMaximal _ hN'max.ne_top
  let z0 : (C.baseChange (IsLocalRing.ResidueField R)).left :=
    hSaff.fromSpec
      ⟨N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW), hN'max.isPrime⟩
  have hz0mem : z0 ∈ C.bcOpens (IsLocalRing.ResidueField R) W := by
    change z0 ∈ (C.bcOpens (IsLocalRing.ResidueField R) W : Set _)
    rw [← hSaff.range_fromSpec]
    exact ⟨_, rfl⟩
  have hz0cl : IsClosed ({z0} : Set (C.baseChange (IsLocalRing.ResidueField R)).left) := by
    rcases Curve.eq_genericPoint_or_isClosed (C.baseChange (IsLocalRing.ResidueField R)) z0 with
      hgen | hcl
    · exfalso
      have hmem : genericPoint (C.baseChange (IsLocalRing.ResidueField R)).left
          ∈ C.bcOpens (IsLocalRing.ResidueField R) W := hgen ▸ hz0mem
      have hbot : hSaff.primeIdealOf ⟨genericPoint _, hmem⟩ = (⊥ : PrimeSpectrum _) := by
        rw [hSaff.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
      have h4 : hSaff.primeIdealOf ⟨z0, hz0mem⟩
          = ⟨N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW),
              hN'max.isPrime⟩ := by
        show hSaff.isoSpec.hom ⟨z0, hz0mem⟩ = _
        have h3 : (⟨z0, hz0mem⟩ : ↥(C.bcOpens (IsLocalRing.ResidueField R) W))
            = hSaff.isoSpec.inv
                ⟨N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW),
                  hN'max.isPrime⟩ := Subtype.ext rfl
        rw [h3]
        exact Homeomorph.apply_symm_apply (Scheme.homeoOfIso hSaff.isoSpec) _
      have h2 : hSaff.primeIdealOf ⟨genericPoint _, hmem⟩
          = ⟨N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW),
              hN'max.isPrime⟩ := by
        rw [show (⟨genericPoint _, hmem⟩ : ↥(C.bcOpens (IsLocalRing.ResidueField R) W))
            = ⟨z0, hz0mem⟩ from Subtype.ext hgen.symm]
        exact h4
      exact hN'ne (congrArg PrimeSpectrum.asIdeal (h2.symm.trans hbot))
    · exact hcl
  refine ⟨⟨z0, hz0cl⟩, fun x => ?_⟩
  letI : Algebra (Γ((C.baseChange (IsLocalRing.ResidueField R)).left,
      (C.bcSquare (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W))
      ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0) :=
    TopCat.Presheaf.algebra_section_stalk (C.baseChange (IsLocalRing.ResidueField R)).left.presheaf
      ⟨z0, hz0mem⟩
  haveI hN'prime : (N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)).IsPrime :=
    hN'max.isPrime
  haveI hloc : IsLocalization.AtPrime
      ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0)
      (N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)) :=
    hSaff.isLocalization_stalk' ⟨_, hN'max.isPrime⟩ hz0mem
  haveI hST : IsScalarTower (Γ((C.baseChange (IsLocalRing.ResidueField R)).left,
      (C.bcSquare (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W))
      ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0)
      (C.baseChange (IsLocalRing.ResidueField R)).functionField :=
    functionField_isScalarTower (C.baseChange (IsLocalRing.ResidueField R)).left
      (C.bcOpens (IsLocalRing.ResidueField R) W) ⟨z0, hz0mem⟩
  have hred : ∀ y : chartTensor (K := K) (C := C) R W,
      Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW y
        = (algebraMap (Γ((C.baseChange (IsLocalRing.ResidueField R)).left,
            (C.bcSquare (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W))
            ((C.baseChange (IsLocalRing.ResidueField R)).functionField))
            (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW y) := by
    intro y
    rw [Alt.Up.chartTensorRedMap_eq_germ_comp_sectionsMap (K := K) (C := C) R W hW]
    rfl
  have hcomp : ∀ y : chartTensor (K := K) (C := C) R W,
      (algebraMap ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0)
          ((C.baseChange (IsLocalRing.ResidueField R)).functionField))
        ((algebraMap (Γ((C.baseChange (IsLocalRing.ResidueField R)).left,
          (C.bcSquare (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W))
          ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0))
          (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW y))
      = Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW y := by
    intro y
    rw [← IsScalarTower.algebraMap_apply
      (R := Γ((C.baseChange (IsLocalRing.ResidueField R)).left,
        (C.bcSquare (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W))
      (S := (C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0)
      (A := (C.baseChange (IsLocalRing.ResidueField R)).functionField),
      (hred y).symm]
  -- The two remaining steps are the transfer between `B` and the sections `Γ(C_κ, W_κ)`; the
  -- localisation input is `IsLocalization.AtPrime.to_map_mem_maximal_iff` (with `S` and `I`
  -- supplied explicitly), `IsLocalization.surj` and `IsLocalization.AtPrime.mk'_mem_maximal_iff`.
  constructor
  · rintro ⟨a, hax, ha⟩
    obtain ⟨⟨s, t⟩, ht⟩ := IsLocalization.surj (N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)).primeCompl a
    have ht' : (t : Γ((C.baseChange (IsLocalRing.ResidueField R)).left,
        (C.bcSquare (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W)) ∉ (N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)) :=
      Ideal.mem_primeCompl_iff.mp t.2
    -- `algS s = a * algS t ∈ 𝔪`, hence `s ∈ N'`
    have hsmem : s ∈ (N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)) := by
      have h1 : (algebraMap (Γ((C.baseChange (IsLocalRing.ResidueField R)).left, (C.bcSquare (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W)) ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0)) s ∈ IsLocalRing.maximalIdeal ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0) := by
        rw [← ht]
        exact Ideal.mul_mem_right _ _ ha
      have h2 : s ∈ Ideal.under (Γ((C.baseChange (IsLocalRing.ResidueField R)).left, (C.bcSquare (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W)) (IsLocalRing.maximalIdeal ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0)) :=
        (Ideal.mem_under (Γ((C.baseChange (IsLocalRing.ResidueField R)).left, (C.bcSquare (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W)) _).mpr h1
      rwa [IsLocalization.AtPrime.under_maximalIdeal (S := ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0)) (I := (N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)))] at h2
    obtain ⟨n, hnN, hn⟩ := (Ideal.mem_map_iff_of_surjective (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)
      (chartTensorRedSectionsMap_surjective (K := K) (C := C) R W hW)).mp hsmem
    obtain ⟨b, hb⟩ := (chartTensorRedSectionsMap_surjective (K := K) (C := C) R W hW)
      (t : Γ((C.baseChange (IsLocalRing.ResidueField R)).left,
        (C.bcSquare (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W))
    have hbN : b ∉ N := fun hbmem => ht' (hb ▸ Ideal.mem_map_of_mem _ hbmem)
    exact ⟨n, b, hbN, hnN, by rw [← hax, ← hcomp b, ← map_mul, hb, ht, ← hn, hcomp n]⟩
  · rintro ⟨a, b, hbN, haN, hab⟩
    have hb' : (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW) b ∉ (N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)) := by
      intro hmem
      exact hbN (by rw [← hcomap]; exact Ideal.mem_comap.mpr hmem)
    refine ⟨IsLocalization.mk' ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0) ((Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW) a)
        ⟨(Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW) b, Ideal.mem_primeCompl_iff.mpr hb'⟩, ?_, ?_⟩
    · have hspec := IsLocalization.mk'_spec ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0) ((Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW) a)
          ⟨(Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW) b, Ideal.mem_primeCompl_iff.mpr hb'⟩
      have hunit : IsUnit (algebraMap (Γ((C.baseChange (IsLocalRing.ResidueField R)).left, (C.bcSquare (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W)) ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0) ((Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW) b)) := by
        rw [IsLocalization.AtPrime.isUnit_to_map_iff (S := ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0)) (I := (N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)))]
        exact Ideal.mem_primeCompl_iff.mpr hb'
      refine mul_right_cancel₀ (hunit.map (algebraMap ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0) ((C.baseChange (IsLocalRing.ResidueField R)).functionField))).ne_zero ?_
      rw [← map_mul, hspec, hcomp a, hcomp b, hab]
    · exact (IsLocalization.AtPrime.mk'_mem_maximal_iff (S := ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z0)) (I := (N.map (Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW)))
        ((Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW) a) ⟨(Alt.Up.chartTensorRedSectionsMap (K := K) (C := C) R W hW) b, Ideal.mem_primeCompl_iff.mpr hb'⟩).mpr
        (Ideal.mem_map_of_mem _ haN)

end MaximalIdealDictionary

/-! ## Content normalisation in the function field of the generic fibre

The first step of the proof: multiplying `h ∈ K(C_F)^×` by a nonzero constant of `F` (which does
not change its divisor) lets one write it as a quotient `a/b` of two elements of the relative
chart ring `B = Γ(C,W) ⊗_K R` which are *both* units modulo the fibre prime `P = 𝔪_R·B`. -/

section ContentNormalisation

open Work.CurveBasics in
theorem exists_fraction_notMem_chartFibrePrime (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (h : (C.baseChange (FractionRing R)).functionField) (hh : h ≠ 0) :
    ∃ (c : FractionRing R) (_ : c ≠ 0) (a b : chartTensor (K := K) (C := C) R W),
      a ∉ chartFibrePrime (K := K) (C := C) R W ∧
      b ∉ chartFibrePrime (K := K) (C := C) R W ∧
      algebraMap (FractionRing R) (C.baseChange (FractionRing R)).functionField c * h
        * Alt.Up.chartTensorMap (K := K) (C := C) R W hW b
        = Alt.Up.chartTensorMap (K := K) (C := C) R W hW a := by
  let B := chartTensor (K := K) (C := C) R W
  let F := FractionRing R
  let L := (C.baseChange F).functionField
  letI : Algebra B L := (Alt.Up.chartTensorMap (K := K) (C := C) R W hW).toAlgebra
  letI : Algebra R B := Algebra.TensorProduct.rightAlgebra (R := K) (A := Γ(C.left, W)) (B := R)
  letI : Algebra R L := ((algebraMap F L).comp (algebraMap R F)).toAlgebra
  haveI hfr : IsFractionRing B L := Alt.Up.chartTensorMap_isFractionRing (K := K) (C := C) R W hW
  have hι : (algebraMap R B) = (Algebra.TensorProduct.includeRight (R := K)
      (A := Γ(C.left, W)) (B := R) : R →+* B) :=
    Algebra.TensorProduct.algebraMap_eq_includeRight
  haveI hST : IsScalarTower R B L := IsScalarTower.of_algebraMap_eq (fun r => by
    show algebraMap R L r = (Alt.Up.chartTensorMap (K := K) (C := C) R W hW) (algebraMap R B r)
    rw [hι]
    exact (Alt.Up.chartTensorMap_one_tmul (K := K) (C := C) R W hW r).symm)
  obtain ⟨a₀, b₀, hb₀nz, hdiv⟩ := IsFractionRing.div_surjective B h
  obtain ⟨c_a, a₁, ha₀, ha₁⟩ := Work.SpecLin.Core.exists_smul_notMem_chartFibrePrime
    (K := K) (C := C) R W hW a₀
  obtain ⟨c_b, b₁, hb₀, hb₁⟩ := Work.SpecLin.Core.exists_smul_notMem_chartFibrePrime
    (K := K) (C := C) R W hW b₀
  have hc_a : c_a ≠ 0 := by
    intro h0
    have : a₀ = 0 := by rw [ha₀, h0, zero_smul]
    have hh0 : h = 0 := by rw [← hdiv, this, map_zero, zero_div]
    exact hh hh0
  have hc_b : c_b ≠ 0 := by
    intro h0
    exact (nonZeroDivisors.ne_zero hb₀nz) (by rw [hb₀, h0, zero_smul])
  have hσa : algebraMap B L a₀ = algebraMap R L c_a * algebraMap B L a₁ := by
    rw [ha₀, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R B L c_a]
  have hσb : algebraMap B L b₀ = algebraMap R L c_b * algebraMap B L b₁ := by
    rw [hb₀, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R B L c_b]
  -- vanishing conditions
  have hFF : ∀ y : FractionRing R, algebraMap F L y = 0 → y = 0 :=
    fun y hy => (algebraMap F L).injective (by rw [hy]; simp)
  have hc_aL : algebraMap R L c_a ≠ 0 := by
    show algebraMap F L (algebraMap R F c_a) ≠ 0
    intro h0
    exact hc_a (IsFractionRing.injective R F ((hFF _ h0).trans (map_zero _).symm))
  have hc_bL : algebraMap R L c_b ≠ 0 := by
    show algebraMap F L (algebraMap R F c_b) ≠ 0
    intro h0
    exact hc_b (IsFractionRing.injective R F ((hFF _ h0).trans (map_zero _).symm))
  have ha₁0 : a₁ ≠ 0 := fun h0 => ha₁ (h0 ▸ Ideal.zero_mem _)
  have hb₁0 : b₁ ≠ 0 := fun h0 => hb₁ (h0 ▸ Ideal.zero_mem _)
  have hσa₁ : algebraMap B L a₁ ≠ 0 := fun h0 =>
    ha₁0 (IsFractionRing.injective B L (by rw [h0]; simp))
  have hσb₁ : algebraMap B L b₁ ≠ 0 := fun h0 =>
    hb₁0 (IsFractionRing.injective B L (by rw [h0]; simp))
  refine ⟨algebraMap R F c_b / algebraMap R F c_a, ?_, a₁, b₁, ha₁, hb₁, ?_⟩
  · exact div_ne_zero
      (fun h0 => hc_b (IsFractionRing.injective R F (by rw [map_zero]; exact h0)))
      (fun h0 => hc_a (IsFractionRing.injective R F (by rw [map_zero]; exact h0)))
  · rw [show algebraMap F L (algebraMap R F c_b / algebraMap R F c_a)
        = algebraMap R L c_b / algebraMap R L c_a from by rw [map_div₀]; rfl,
      ← hdiv, hσa, hσb]
    field_simp
    rw [RingHom.algebraMap_toAlgebra]
    ring


end ContentNormalisation

/-! ## Chart-independence of the reduction of a rational function

The reduction `h̄ := ρ_W(a)/ρ_W(b)` of a rational function `h' = φ_W(a)/φ_W(b)` (with
`a, b ∈ B_W ∖ P_W`) is an element of `K(C_κ)`, and this element does **not** depend on the chart:
if `h'` is also presented in a second chart `V` as `φ_V(a')/φ_V(b')`, then the two reductions
agree.  The proof uses a common refinement `Z ≤ W`, `Z ≤ V` and the compatibility
`Work.SpecLin.Core.Up.chartTensorRedMap_restrict` of the reduction with restriction to a smaller
affine open.
-/

section Canonicity

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]

open Work.CurveBasics in
/-- **Canonicity of the reduction of a rational function.**  If two presentations
`h' = φ_W(a)/φ_W(b)` and `h' = φ_V(a')/φ_V(b')` (with `b ∉ P_W`, `b' ∉ P_V`) of the same element
of `K(C_F)` are given, then their reductions `ρ_W(a)/ρ_W(b)` and `ρ_V(a')/ρ_V(b')` in `K(C_κ)`
agree.  The hypotheses are stated on a common refinement `Z` of `W` and `V`. -/
theorem canonicalReduction_eq {Z W V : C.left.Opens} (hZW : Z ≤ W) (hZV : Z ≤ V)
    (hZ : IsAffineOpen Z) (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    [Nonempty Z] [Nonempty W] [Nonempty V]
    (a b : chartTensor (K := K) (C := C) R W) (a' b' : chartTensor (K := K) (C := C) R V)
    (hb : b ∉ chartFibrePrime (K := K) (C := C) R W)
    (hb' : b' ∉ chartFibrePrime (K := K) (C := C) R V)
    (heq : Alt.Up.chartTensorMap (K := K) (C := C) R W hW a
              * Alt.Up.chartTensorMap (K := K) (C := C) R V hV b'
            = Alt.Up.chartTensorMap (K := K) (C := C) R V hV a'
              * Alt.Up.chartTensorMap (K := K) (C := C) R W hW b) :
    Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW a
        / Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW b
      = Alt.Up.chartTensorRedMap (K := K) (C := C) R V hV a'
        / Alt.Up.chartTensorRedMap (K := K) (C := C) R V hV b' := by
  let BZ := chartTensor (K := K) (C := C) R Z
  let L := (C.baseChange (FractionRing R)).functionField
  letI : Algebra BZ L := (Alt.Up.chartTensorMap (K := K) (C := C) R Z hZ).toAlgebra
  haveI hfrZ : IsFractionRing BZ L := Alt.Up.chartTensorMap_isFractionRing (K := K) (C := C) R Z hZ
  have hinjZ : Function.Injective (Alt.Up.chartTensorMap (K := K) (C := C) R Z hZ) := by
    intro x y hxy
    exact IsFractionRing.injective BZ L hxy
  have h2 : chartRestrict (K := K) (C := C) R hZW a * chartRestrict (K := K) (C := C) R hZV b'
      = chartRestrict (K := K) (C := C) R hZV a' * chartRestrict (K := K) (C := C) R hZW b := by
    apply hinjZ
    rw [map_mul, map_mul, chartTensorMap_restrict (K := K) (C := C) R hZW hZ hW a,
      chartTensorMap_restrict (K := K) (C := C) R hZV hZ hV b',
      chartTensorMap_restrict (K := K) (C := C) R hZV hZ hV a',
      chartTensorMap_restrict (K := K) (C := C) R hZW hZ hW b]
    exact heq
  have h3 : Alt.Up.chartTensorRedMap (K := K) (C := C) R Z hZ
          (chartRestrict (K := K) (C := C) R hZW a)
        * Alt.Up.chartTensorRedMap (K := K) (C := C) R Z hZ
          (chartRestrict (K := K) (C := C) R hZV b')
      = Alt.Up.chartTensorRedMap (K := K) (C := C) R Z hZ
          (chartRestrict (K := K) (C := C) R hZV a')
        * Alt.Up.chartTensorRedMap (K := K) (C := C) R Z hZ
          (chartRestrict (K := K) (C := C) R hZW b) := by
    rw [← map_mul, ← map_mul, h2]
  have h4 : Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW a
        * Alt.Up.chartTensorRedMap (K := K) (C := C) R V hV b'
      = Alt.Up.chartTensorRedMap (K := K) (C := C) R V hV a'
        * Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW b := by
    rw [← chartTensorRedMap_restrict (K := K) (C := C) R hZW hZ hW a,
      ← chartTensorRedMap_restrict (K := K) (C := C) R hZV hZ hV b',
      ← chartTensorRedMap_restrict (K := K) (C := C) R hZV hZ hV a',
      ← chartTensorRedMap_restrict (K := K) (C := C) R hZW hZ hW b]
    exact h3
  rw [div_eq_div_iff (chartTensorRedMap_ne_zero (K := K) (C := C) R W hW hb)
    (chartTensorRedMap_ne_zero (K := K) (C := C) R V hV hb')]
  exact h4

end Canonicity

/-! ## Two inlined auxiliary results

The modules `Submission.Work.SpecLin.Alt.place_dictionary` and
`Submission.Work.SpecLin.Setup.exists_representation_of_other_chart` both import *this* module (for
the restriction machinery `chartRestrict`/`chartTensorMap_restrict`/`chartTensorRedMap_restrict`),
so they cannot be imported back here.  Their statements are reproduced below.
-/

section FibrePointDictionary

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]

open Work.CurveBasics in
/-- **The maximal ideal of the relative chart attached to a point of the special-fibre chart.**
Every place `z` of `C_κ` lying in the chart `W_κ` is cut out by a maximal ideal
`N ⊇ P = 𝔪_R·B` of the relative chart, with the membership dictionary. -/
theorem exists_maximalIdeal_of_fibrePoint
    (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (z : (C.baseChange (IsLocalRing.ResidueField R)).Place)
    (hzW : z.point ∈ C.bcOpens (IsLocalRing.ResidueField R) W) :
    ∃ N : Ideal (chartTensor (K := K) (C := C) R W), N.IsMaximal ∧
      chartFibrePrime (K := K) (C := C) R W ≤ N ∧
      (∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
        (∃ a b : chartTensor (K := K) (C := C) R W, b ∉ N ∧
            x * Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW b
              = Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW a)
          ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z) := by
  classical
  have hU : IsAffineOpen (C.bcOpens (IsLocalRing.ResidueField R) W) :=
    Work.CurveBasics.BaseChange.isAffineOpen_bcOpens (IsLocalRing.ResidueField R) W hW
  haveI hUne : Nonempty (C.bcOpens (IsLocalRing.ResidueField R) W) :=
    Work.CurveBasics.Curve.bcOpens_nonempty C (IsLocalRing.ResidueField R) W
  let ψ : chartTensor (K := K) (C := C) R W →+* Alt.Up.fibreSections R W :=
    Alt.Up.chartTensorRedSectionsMap R W hW
  have hψ_surj : Function.Surjective ψ :=
    chartTensorRedSectionsMap_surjective (K := K) (C := C) R W hW
  have hker : RingHom.ker ψ = chartFibrePrime (K := K) (C := C) R W :=
    ker_chartTensorRedSectionsMap (K := K) (C := C) R W hW
  let m : Ideal (Alt.Up.fibreSections R W) := (hU.primeIdealOf ⟨z.point, hzW⟩).asIdeal
  haveI hm_max : m.IsMaximal :=
    hU.primeIdealOf_isMaximal_of_isClosed ⟨z.point, hzW⟩ z.isClosed
  let N : Ideal (chartTensor (K := K) (C := C) R W) := m.comap ψ
  have hN_max : N.IsMaximal := Ideal.comap_isMaximal_of_surjective (f := ψ) hψ_surj
  have hPN : chartFibrePrime (K := K) (C := C) R W ≤ N := by
    rw [← hker]; exact Ideal.ker_le_comap ψ
  refine ⟨N, hN_max, hPN, fun x => ?_⟩
  have hred : ∀ y : chartTensor (K := K) (C := C) R W,
      Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW y
        = algebraMap (Alt.Up.fibreSections R W)
            ((C.baseChange (IsLocalRing.ResidueField R)).functionField) (ψ y) := by
    intro y
    rw [Alt.Up.chartTensorRedMap_eq_germ_comp_sectionsMap (K := K) (C := C) R W hW]
    rfl
  have hiff : (∃ a b : chartTensor (K := K) (C := C) R W, b ∉ N ∧
        x * Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW b
          = Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW a)
      ↔ (∃ a b : Alt.Up.fibreSections R W, b ∉ m ∧
          x * algebraMap (Alt.Up.fibreSections R W)
                ((C.baseChange (IsLocalRing.ResidueField R)).functionField) b
            = algebraMap (Alt.Up.fibreSections R W)
                ((C.baseChange (IsLocalRing.ResidueField R)).functionField) a) := by
    constructor
    · rintro ⟨a, b, hb, h⟩
      exact ⟨ψ a, ψ b, fun hm => hb (Ideal.mem_comap.mpr hm), by rw [hred b, hred a] at h; exact h⟩
    · rintro ⟨a', b', hb', h⟩
      obtain ⟨a, rfl⟩ := hψ_surj a'
      obtain ⟨b, rfl⟩ := hψ_surj b'
      exact ⟨a, b, fun hbN => hb' (Ideal.mem_comap.mp hbN),
        by rw [hred b, hred a]; exact h⟩
  rw [hiff]
  exact Alt.exists_mul_eq_iff_ordAt_of_primeIdealOf
    (C := C.baseChange (IsLocalRing.ResidueField R))
    (C.bcOpens (IsLocalRing.ResidueField R) W) hU z hzW x

end FibrePointDictionary

/-! ## The pointwise reading-off and the globalisation

`div_reduction_apply` computes the order of the reduction of `h' = φ_W(a)/φ_W(b)` at a place of
the special fibre lying in the chart `W_κ`; `chartCoreDiv_of_crux` removes the hypothesis
"`C_κ ∖ W_κ` has at most one point" from the assembly by choosing, for every place `z` outside
`W_κ`, a second affine chart containing both the images of the sections and the image of `z`,
where `div_reduction_apply` applies, and by invoking the chart-independence
`canonicalReduction_eq` of the reduction.
-/

section Reading

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
variable (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W]
  [IsDomain (chartTensor (K := K) (C := C) R W)]

open Work.CurveBasics in
/-- **Clear denominators in the chart `Z ⊆ V`.**  Every element of the relative chart ring
`B_Z` of a nonempty affine chart `Z` contained in the nonempty affine chart `V` is a fraction of
two elements of `B_V` whose denominator is a unit at the fibre prime `P_V`. -/
private theorem chartRestrict_fraction_aux {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (Z V : C.left.Opens) (hV : IsAffineOpen V) (hZV : Z ≤ V)
    [Nonempty Z] [Nonempty V] (c : chartTensor (K := K) (C := C) R Z) :
    ∃ X Y : chartTensor (K := K) (C := C) R V,
      Y ∉ chartFibrePrime (K := K) (C := C) R V ∧
      chartRestrict (K := K) (C := C) R hZV X
        = c * chartRestrict (K := K) (C := C) R hZV Y := by
  classical
  have hfr : IsFractionRing (C.left.presheaf.obj (Opposite.op V)) C.functionField :=
    Work.SpecLin.Alt.isFractionRing_functionField V hV
  haveI := hfr
  have hP : (chartFibrePrime (K := K) (C := C) R V).IsPrime :=
    isPrime_chartFibrePrime (K := K) (C := C) R V hV
  haveI := hP
  have key : ∀ (a : C.left.presheaf.obj (Opposite.op Z)) (r : R),
      ∃ X Y : chartTensor (K := K) (C := C) R V,
        Y ∉ chartFibrePrime (K := K) (C := C) R V ∧
        chartRestrict (K := K) (C := C) R hZV X
          = (a ⊗ₜ[K] r) * chartRestrict (K := K) (C := C) R hZV Y := by
    intro a r
    obtain ⟨⟨x, y⟩, hy⟩ := IsLocalization.surj
      (nonZeroDivisors (C.left.presheaf.obj (Opposite.op V)))
      ((C.germToFunctionField Z).hom a)
    have hyne : (y : C.left.presheaf.obj (Opposite.op V)) ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp y.2
    have hkey : a * chartResAlgHom (K := K) (C := C) hZV
          (y : C.left.presheaf.obj (Opposite.op V))
        = chartResAlgHom (K := K) (C := C) hZV x := by
      refine (Scheme.germToFunctionField_injective (X := C.left) Z) ?_
      show (C.germToFunctionField Z).hom
          (a * chartResAlgHom (K := K) (C := C) hZV
            (y : C.left.presheaf.obj (Opposite.op V)))
        = (C.germToFunctionField Z).hom (chartResAlgHom (K := K) (C := C) hZV x)
      rw [map_mul, germToFunctionField_restrict hZV, germToFunctionField_restrict hZV]
      exact hy
    refine ⟨x ⊗ₜ[K] r, (y : C.left.presheaf.obj (Opposite.op V)) ⊗ₜ[K] (1 : R), ?_, ?_⟩
    · rw [← chartTensorRedMap_eq_zero_iff (K := K) (C := C) R V hV,
        Alt.Up.chartTensorRedMap_tmul_one]
      intro h0
      refine hyne ((Scheme.germToFunctionField_injective (X := C.left) V) ?_)
      rw [map_zero]
      exact Work.CurveBasics.Curve.functionFieldMap_injective C (IsLocalRing.ResidueField R)
        (by simpa using h0)
    · show chartRestrict (K := K) (C := C) R hZV (x ⊗ₜ[K] r)
        = (a ⊗ₜ[K] r) * chartRestrict (K := K) (C := C) R hZV
            ((y : C.left.presheaf.obj (Opposite.op V)) ⊗ₜ[K] (1 : R))
      rw [show chartRestrict (K := K) (C := C) R hZV (x ⊗ₜ[K] r)
            = chartResAlgHom (K := K) (C := C) hZV x ⊗ₜ[K] r from rfl,
          show chartRestrict (K := K) (C := C) R hZV
              ((y : C.left.presheaf.obj (Opposite.op V)) ⊗ₜ[K] (1 : R))
            = chartResAlgHom (K := K) (C := C) hZV
                (y : C.left.presheaf.obj (Opposite.op V)) ⊗ₜ[K] (1 : R) from rfl,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, hkey]
  refine TensorProduct.inductionOn c ?_ ?_
  · intro a r
    exact key a r
  · intro c1 c2 h1 h2
    obtain ⟨X1, Y1, hY1, h1'⟩ := h1
    obtain ⟨X2, Y2, hY2, h2'⟩ := h2
    refine ⟨X1 * Y2 + X2 * Y1, Y1 * Y2, ?_, ?_⟩
    · intro hmem
      rcases hP.mem_or_mem hmem with h | h
      · exact hY1 h
      · exact hY2 h
    · rw [map_add, map_mul, map_mul, h1', h2', map_mul]
      ring

open Work.CurveBasics in
/-- **A chart-`W` presentation of a rational function transfers to any other affine chart.**
If `h = φ_W(a)/φ_W(b)` with `a, b ∈ B_W ∖ P_W`, then also `h = φ_V(a')/φ_V(b')` with
`a', b' ∈ B_V ∖ P_V`, for every other nonempty affine chart `V`. -/
theorem exists_presentation_other_chart {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W V : C.left.Opens) (hW : IsAffineOpen W) (hV : IsAffineOpen V) [Nonempty W] [Nonempty V]
    [IsDomain (chartTensor (K := K) (C := C) R W)]
    [IsDomain (chartTensor (K := K) (C := C) R V)]
    (a b : chartTensor (K := K) (C := C) R W)
    (ha : a ∉ chartFibrePrime (K := K) (C := C) R W)
    (hb : b ∉ chartFibrePrime (K := K) (C := C) R W)
    (h : (C.baseChange (FractionRing R)).functionField) (hh : h ≠ 0)
    (hab : h * Alt.Up.chartTensorMap (K := K) (C := C) R W hW b
        = Alt.Up.chartTensorMap (K := K) (C := C) R W hW a) :
    ∃ a' b' : chartTensor (K := K) (C := C) R V,
      a' ∉ chartFibrePrime (K := K) (C := C) R V ∧
      b' ∉ chartFibrePrime (K := K) (C := C) R V ∧
      h * Alt.Up.chartTensorMap (K := K) (C := C) R V hV b'
        = Alt.Up.chartTensorMap (K := K) (C := C) R V hV a' := by
  classical
  obtain ⟨w, hw⟩ := ‹Nonempty W›
  obtain ⟨v, hv⟩ := ‹Nonempty V›
  have hηW : genericPoint C.left ∈ (W : Set C.left) :=
    (genericPoint_spec C.left).mem_open_set_iff W.isOpen |>.mpr ⟨w, trivial, hw⟩
  have hηV : genericPoint C.left ∈ (V : Set C.left) :=
    (genericPoint_spec C.left).mem_open_set_iff V.isOpen |>.mpr ⟨v, trivial, hv⟩
  have hη : genericPoint C.left ∈ (W ⊓ V : C.left.Opens) := ⟨hηW, hηV⟩
  obtain ⟨Z, hZaff, hZmem, hZsub⟩ :=
    exists_isAffineOpen_mem_and_subset (U := W ⊓ V) hη
  have hZW : Z ≤ W := fun x hx => (hZsub hx).1
  have hZV : Z ≤ V := fun x hx => (hZsub hx).2
  haveI : Nonempty Z := ⟨⟨genericPoint C.left, hZmem⟩⟩
  set aZ : chartTensor (K := K) (C := C) R Z := chartRestrict (K := K) (C := C) R hZW a
    with haZ
  set bZ : chartTensor (K := K) (C := C) R Z := chartRestrict (K := K) (C := C) R hZW b
    with hbZ
  have hφa : Alt.Up.chartTensorMap (K := K) (C := C) R Z hZaff aZ
      = Alt.Up.chartTensorMap (K := K) (C := C) R W hW a :=
    chartTensorMap_restrict (K := K) (C := C) R hZW hZaff hW a
  have hφb : Alt.Up.chartTensorMap (K := K) (C := C) R Z hZaff bZ
      = Alt.Up.chartTensorMap (K := K) (C := C) R W hW b :=
    chartTensorMap_restrict (K := K) (C := C) R hZW hZaff hW b
  have hreda : Alt.Up.chartTensorRedMap (K := K) (C := C) R Z hZaff aZ ≠ 0 := by
    rw [haZ, chartTensorRedMap_restrict (K := K) (C := C) R hZW hZaff hW a]
    exact fun h0 => ha ((chartTensorRedMap_eq_zero_iff (K := K) (C := C) R W hW a).mp h0)
  have hredb : Alt.Up.chartTensorRedMap (K := K) (C := C) R Z hZaff bZ ≠ 0 := by
    rw [hbZ, chartTensorRedMap_restrict (K := K) (C := C) R hZW hZaff hW b]
    exact fun h0 => hb ((chartTensorRedMap_eq_zero_iff (K := K) (C := C) R W hW b).mp h0)
  obtain ⟨XA, YA, hYA, hArec⟩ := chartRestrict_fraction_aux (K := K) (C := C) R Z V hV hZV aZ
  obtain ⟨XB, YB, hYB, hBrec⟩ := chartRestrict_fraction_aux (K := K) (C := C) R Z V hV hZV bZ
  have hφXA : Alt.Up.chartTensorMap (K := K) (C := C) R V hV XA
      = Alt.Up.chartTensorMap (K := K) (C := C) R Z hZaff aZ
        * Alt.Up.chartTensorMap (K := K) (C := C) R V hV YA := by
    rw [← chartTensorMap_restrict (K := K) (C := C) R hZV hZaff hV XA, hArec, map_mul,
      chartTensorMap_restrict (K := K) (C := C) R hZV hZaff hV YA]
  have hφXB : Alt.Up.chartTensorMap (K := K) (C := C) R V hV XB
      = Alt.Up.chartTensorMap (K := K) (C := C) R Z hZaff bZ
        * Alt.Up.chartTensorMap (K := K) (C := C) R V hV YB := by
    rw [← chartTensorMap_restrict (K := K) (C := C) R hZV hZaff hV XB, hBrec, map_mul,
      chartTensorMap_restrict (K := K) (C := C) R hZV hZaff hV YB]
  have hXA : XA ∉ chartFibrePrime (K := K) (C := C) R V := by
    rw [← chartTensorRedMap_eq_zero_iff (K := K) (C := C) R V hV]
    intro h0
    have h1 : Alt.Up.chartTensorRedMap (K := K) (C := C) R Z hZaff
        (chartRestrict (K := K) (C := C) R hZV XA) = 0 := by
      rw [chartTensorRedMap_restrict (K := K) (C := C) R hZV hZaff hV XA]; exact h0
    rw [hArec, map_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hreda h2
    · have h3 : Alt.Up.chartTensorRedMap (K := K) (C := C) R V hV YA = 0 := by
        rw [← chartTensorRedMap_restrict (K := K) (C := C) R hZV hZaff hV YA]; exact h2
      exact hYA ((chartTensorRedMap_eq_zero_iff (K := K) (C := C) R V hV YA).mp h3)
  have hXB : XB ∉ chartFibrePrime (K := K) (C := C) R V := by
    rw [← chartTensorRedMap_eq_zero_iff (K := K) (C := C) R V hV]
    intro h0
    have h1 : Alt.Up.chartTensorRedMap (K := K) (C := C) R Z hZaff
        (chartRestrict (K := K) (C := C) R hZV XB) = 0 := by
      rw [chartTensorRedMap_restrict (K := K) (C := C) R hZV hZaff hV XB]; exact h0
    rw [hBrec, map_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hredb h2
    · have h3 : Alt.Up.chartTensorRedMap (K := K) (C := C) R V hV YB = 0 := by
        rw [← chartTensorRedMap_restrict (K := K) (C := C) R hZV hZaff hV YB]; exact h2
      exact hYB ((chartTensorRedMap_eq_zero_iff (K := K) (C := C) R V hV YB).mp h3)
  have hP : (chartFibrePrime (K := K) (C := C) R V).IsPrime :=
    isPrime_chartFibrePrime (K := K) (C := C) R V hV
  refine ⟨XA * YB, XB * YA, ?_, ?_, ?_⟩
  · intro hmem
    rcases hP.mem_or_mem hmem with h' | h'
    · exact hXA h'
    · exact hYB h'
  · intro hmem
    rcases hP.mem_or_mem hmem with h' | h'
    · exact hXB h'
    · exact hYA h'
  · rw [map_mul, map_mul]
    have keyeq : h * Alt.Up.chartTensorMap (K := K) (C := C) R V hV XB
          * Alt.Up.chartTensorMap (K := K) (C := C) R V hV YA
        = Alt.Up.chartTensorMap (K := K) (C := C) R V hV XA
          * Alt.Up.chartTensorMap (K := K) (C := C) R V hV YB := by
      rw [hφXB, hφXA, hφb, hφa]
      calc h * (Alt.Up.chartTensorMap (K := K) (C := C) R W hW b
              * Alt.Up.chartTensorMap (K := K) (C := C) R V hV YB)
              * Alt.Up.chartTensorMap (K := K) (C := C) R V hV YA
            = (h * Alt.Up.chartTensorMap (K := K) (C := C) R W hW b)
              * (Alt.Up.chartTensorMap (K := K) (C := C) R V hV YB
                * Alt.Up.chartTensorMap (K := K) (C := C) R V hV YA) := by ring
        _ = Alt.Up.chartTensorMap (K := K) (C := C) R W hW a
              * (Alt.Up.chartTensorMap (K := K) (C := C) R V hV YB
                * Alt.Up.chartTensorMap (K := K) (C := C) R V hV YA) := by rw [hab]
        _ = Alt.Up.chartTensorMap (K := K) (C := C) R W hW a
              * Alt.Up.chartTensorMap (K := K) (C := C) R V hV YA
              * Alt.Up.chartTensorMap (K := K) (C := C) R V hV YB := by ring
    rw [← mul_assoc, keyeq]

open Work.CurveBasics in
/-- **The pointwise reading-off.** ... -/
theorem div_reduction_apply {n : ℕ} (s t : Fin n → Work.SpecLin.CurvePt C R)
    (hs : ∀ m, Set.range ((s m).left.base) ⊆ (W : Set C.left))
    (ht : ∀ m, Set.range ((t m).left.base) ⊆ (W : Set C.left))
    (a b : chartTensor (K := K) (C := C) R W)
    (ha : a ∉ chartFibrePrime (K := K) (C := C) R W)
    (hb : b ∉ chartFibrePrime (K := K) (C := C) R W)
    (h' : (C.baseChange (FractionRing R)).functionField) (hh' : h' ≠ 0)
    (hab : h' * Alt.Up.chartTensorMap (K := K) (C := C) R W hW b
        = Alt.Up.chartTensorMap (K := K) (C := C) R W hW a)
    (hdiv : (C.baseChange (FractionRing R)).div h'
      = (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (s m)))
        - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (t m))))
    (z : (C.baseChange (IsLocalRing.ResidueField R)).Place)
    (hz : z.point ∈ C.bcOpens (IsLocalRing.ResidueField R) W) :
    (C.baseChange (IsLocalRing.ResidueField R)).div
        (Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW a
          / Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW b) z
      = (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
            (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R
              (IsLocalRing.ResidueField R)) (s m))) z
        - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
            (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R
              (IsLocalRing.ResidueField R)) (t m))) z := by
  classical
  obtain ⟨N, hNmax, hPN, hdict⟩ :=
    exists_maximalIdeal_of_fibrePoint (K := K) (C := C) R W hW z hz
  haveI := hNmax
  obtain ⟨f, g, u, hfmem, hgmem, hfP, hgP, hfgen, hggen, hu0, hAB, hU⟩ :=
    cruxUnitAtMaximal (K := K) (C := C) R W hW s t hs ht a b ha hb h' hh' hab hdiv N hPN
  obtain ⟨p, q, hpN, hqN, hpq⟩ := Work.SpecLin.Alt.exists_num_denom_of_isUnitAt N u
    (a * ∏ m, g m) (b * ∏ m, f m) hu0 hU hAB
  have hpP : p ∉ chartFibrePrime (K := K) (C := C) R W := fun hh => hpN (hPN hh)
  have hqP : q ∉ chartFibrePrime (K := K) (C := C) R W := fun hh => hqN (hPN hh)
  refine Work.SpecLin.Alt.Up.div_chartTensorRedMap_div_apply (K := K) (C := C) R W hW s t hs ht
    N hPN z hdict a b p q ha hb hpP hqP ?_ ?_ f g hfP hgP hfgen hggen hpq
  · exact IsLocalization.map_units (Localization.AtPrime N)
      ⟨p, Ideal.mem_primeCompl_iff.mpr hpN⟩
  · exact IsLocalization.map_units (Localization.AtPrime N)
      ⟨q, Ideal.mem_primeCompl_iff.mpr hqN⟩

open Work.CurveBasics in
/-- **The affine-chart core.**  ... -/
theorem chartCoreDiv_of_crux {n : ℕ} (s t : Fin n → Work.SpecLin.CurvePt C R)
    (hs : ∀ m, Set.range ((s m).left.base) ⊆ (W : Set C.left))
    (ht : ∀ m, Set.range ((t m).left.base) ⊆ (W : Set C.left))
    (a b : chartTensor (K := K) (C := C) R W)
    (ha : a ∉ chartFibrePrime (K := K) (C := C) R W)
    (hb : b ∉ chartFibrePrime (K := K) (C := C) R W)
    (h' : (C.baseChange (FractionRing R)).functionField) (hh' : h' ≠ 0)
    (hab : h' * Alt.Up.chartTensorMap (K := K) (C := C) R W hW b
        = Alt.Up.chartTensorMap (K := K) (C := C) R W hW a)
    (hdiv : (C.baseChange (FractionRing R)).div h'
      = (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (s m)))
        - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (t m)))) :
    Work.SpecLin.LinEquiv C
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
        (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R
          (IsLocalRing.ResidueField R)) (s m)))
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
        (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R
          (IsLocalRing.ResidueField R)) (t m))) := by
  classical
  refine ⟨Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW a
      / Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW b,
    div_ne_zero (chartTensorRedMap_ne_zero (K := K) (C := C) R W hW ha)
      (chartTensorRedMap_ne_zero (K := K) (C := C) R W hW hb), ?_⟩
  refine Finsupp.ext fun z => ?_
  rw [Finsupp.sub_apply]
  by_cases hz : z.point ∈ C.bcOpens (IsLocalRing.ResidueField R) W
  · exact div_reduction_apply (K := K) (C := C) R W hW s t hs ht a b ha hb h' hh' hab hdiv z hz
  · set pz : C.left := (C.baseChangeFst (IsLocalRing.ResidueField R)).base z.point with hpz
    set S : Set C.left := (⋃ m : Fin n, Set.range ((s m).left.base)) ∪
      (⋃ m : Fin n, Set.range ((t m).left.base)) ∪ {pz} with hS
    have hSfin : S.Finite := by
      refine Set.Finite.union (Set.Finite.union ?_ ?_) (Set.finite_singleton pz)
      · exact Set.Finite.subset
          (Set.finite_iUnion (fun m : Fin n =>
            (Set.finite_singleton ((s m).left.base (IsLocalRing.closedPoint R))).insert
              (genericPoint C.left)))
          (Set.iUnion_mono (fun m => Work.SpecLin.Alt.range_base_subset_pair R (s m)))
      · exact Set.Finite.subset
          (Set.finite_iUnion (fun m : Fin n =>
            (Set.finite_singleton ((t m).left.base (IsLocalRing.closedPoint R))).insert
              (genericPoint C.left)))
          (Set.iUnion_mono (fun m => Work.SpecLin.Alt.range_base_subset_pair R (t m)))
    obtain ⟨Wz, hWz, hSsub⟩ := Work.SpecLin.Chart.exists_isAffineOpen_containing C S hSfin
    have hsz : ∀ m, Set.range ((s m).left.base) ⊆ (Wz : Set C.left) :=
      fun m y hy => hSsub (Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨m, hy⟩)))
    have htz : ∀ m, Set.range ((t m).left.base) ⊆ (Wz : Set C.left) :=
      fun m y hy => hSsub (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨m, hy⟩)))
    have hpzWz : pz ∈ Wz := hSsub (Or.inr (Set.mem_singleton pz))
    have hzWz : z.point ∈ C.bcOpens (IsLocalRing.ResidueField R) Wz := by
      show (C.baseChangeFst (IsLocalRing.ResidueField R)).base z.point ∈ Wz
      exact hpzWz
    haveI : Nonempty Wz := ⟨⟨pz, hpzWz⟩⟩
    haveI hdomz : IsDomain (chartTensor (K := K) (C := C) R Wz) :=
      isDomain_chartTensor (K := K) (C := C) R Wz hWz
    obtain ⟨a', b', ha', hb', hab'⟩ := exists_presentation_other_chart (K := K) (C := C) R
      W Wz hW hWz a b ha hb h' hh' hab
    have h1 := div_reduction_apply (K := K) (C := C) R Wz hWz s t hsz htz a' b' ha' hb' h'
      hh' hab' hdiv z hzWz
    have h2 : Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW a
          / Alt.Up.chartTensorRedMap (K := K) (C := C) R W hW b
        = Alt.Up.chartTensorRedMap (K := K) (C := C) R Wz hWz a'
          / Alt.Up.chartTensorRedMap (K := K) (C := C) R Wz hWz b' := by
      have hηW : genericPoint C.left ∈ (W : Set C.left) := by
        obtain ⟨w, hw⟩ := ‹Nonempty W›
        exact (genericPoint_spec C.left).mem_open_set_iff W.isOpen |>.mpr ⟨w, trivial, hw⟩
      have hηz : genericPoint C.left ∈ (Wz : Set C.left) := by
        obtain ⟨w, hw⟩ := ‹Nonempty Wz›
        exact (genericPoint_spec C.left).mem_open_set_iff Wz.isOpen |>.mpr ⟨w, trivial, hw⟩
      obtain ⟨Z, hZaff, hZmem, hZsub⟩ :=
        exists_isAffineOpen_mem_and_subset (U := W ⊓ Wz) ⟨hηW, hηz⟩
      have hZW : Z ≤ W := fun x hx => (hZsub hx).1
      have hZV : Z ≤ Wz := fun x hx => (hZsub hx).2
      haveI : Nonempty Z := ⟨⟨genericPoint C.left, hZmem⟩⟩
      refine canonicalReduction_eq (K := K) (C := C) R hZW hZV hZaff hW hWz a b a' b'
        hb hb' ?_
      have hb1 : Alt.Up.chartTensorMap (K := K) (C := C) R W hW a
          = h' * Alt.Up.chartTensorMap (K := K) (C := C) R W hW b := hab.symm
      have hb2 : Alt.Up.chartTensorMap (K := K) (C := C) R Wz hWz a'
          = h' * Alt.Up.chartTensorMap (K := K) (C := C) R Wz hWz b' := hab'.symm
      rw [hb1, hb2]; ring
    rw [h2]
    exact h1

end Reading

/-! ### UPDATE — the target is proved

The theorem below is proved and rests only on `propext`, `Classical.choice`, `Quot.sound`.
The route (no `sorry`, no `sorryAx`), in the order in which it was assembled:

* `exists_maximalIdeal_of_fibrePoint` — the point/prime dictionary of the *special* fibre
  (`z ∈ W_κ ↦ N ⊇ P`), reproduced here because
  `Submission.Work.SpecLin.Alt.place_dictionary` imports this module;
* `chartRestrict_fraction_aux`, `exists_presentation_other_chart` — change of chart for a
  presentation `h = φ_W(a)/φ_W(b)` (with `a, b ∉ P_W`), likewise reproduced because
  `Submission.Work.SpecLin.Setup.exists_representation_of_other_chart` imports this module;
* `canonicalReduction_eq` — the reduction `ρ_W(a)/ρ_W(b) ∈ K(C_κ)` is independent of the chart;
* `div_reduction_apply` — the *pointwise* reading-off: for `z ∈ W_κ`,
  `ord_z(ρ_W(a)/ρ_W(b)) = (Σ ptDiv s̄_m)(z) − (Σ ptDiv t̄_m)(z)`, from the two *delegated*
  inputs `Work.SpecLin.Core.Up.cruxUnitAtMaximal` (the unit step `u ∈ B_N^×`, itself resting on
  `Work.SpecLin.Setup.Up.cruxChartPull` and `Work.SpecLin.Core.Up.orderDataSectionEquation`) and the
  reading-off `Work.SpecLin.Alt.Up.div_chartTensorRedMap_div_apply` of `Alt/chartReading.lean`;
* `chartCoreDiv_of_crux` — the globalisation: the pointwise statement is extended from `W_κ` to
  all of `C_κ` by re-running the reading-off in a second affine chart through the image of the
  point `z` (using `Chart.exists_isAffineOpen_containing`), comparing the two chart reductions
  with `canonicalReduction_eq`; no hypothesis on `C_κ ∖ W_κ` is needed;
* `chartSpecialisation` — content normalisation (`Alt.Up.exists_normalized_chartTensorMap`) then
  the previous step.
-/

/-- **Specialisation of linear equivalence, affine-chart form.**  See the comment block above for
the proof plan and for the warning not to use the `sorry`-stubbed duplicate
`linEquiv_of_sections_of_chart`. -/
theorem chartSpecialisation {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : IsAffineOpen W)
    (s t : Fin n → Work.SpecLin.CurvePt C R)
    (hs : ∀ m, Set.range (s m).left.base ⊆ (W : Set C.left))
    (ht : ∀ m, Set.range (t m).left.base ⊆ (W : Set C.left))
    (h : (C.baseChange (FractionRing R)).functionField) (hh : h ≠ 0)
    (hdiv : (C.baseChange (FractionRing R)).div h
      = (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.genPt R ≫ s m))
        - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.genPt R ≫ t m))) :
    Work.SpecLin.LinEquiv C
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.closedPt R ≫ s m))
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.closedPt R ≫ t m)) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    exact Work.SpecLin.linEquiv_refl C
      (0 : Work.SpecLin.Dv C (IsLocalRing.ResidueField R))
  · haveI : Nonempty W :=
      ⟨⟨(s ⟨0, hn⟩).left.base (IsLocalRing.closedPoint R),
        hs ⟨0, hn⟩ ⟨IsLocalRing.closedPoint R, rfl⟩⟩⟩
    haveI : IsDomain (chartTensor (K := K) (C := C) R W) :=
      isDomain_chartTensor (K := K) (C := C) R W hW
    obtain ⟨h', a, b, hh', ha, hb, hdiv_eq, hab⟩ :=
      Alt.Up.exists_normalized_chartTensorMap (K := K) (C := C) R W hW h hh
    have hdiv' : (C.baseChange (FractionRing R)).div h'
        = (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
            (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (s m)))
          - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
            (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (t m))) := by
      rw [hdiv_eq, hdiv]
      simp only [← Work.SpecLin.Core.rPt_map_fractionRing]
    have hcore := chartCoreDiv_of_crux (K := K) (C := C) R W hW s t hs ht a b ha hb h'
      hh' hab hdiv'
    simpa only [Work.SpecLin.Core.rPt_map_residueField] using hcore

end Up
end Work.SpecLin.Core

