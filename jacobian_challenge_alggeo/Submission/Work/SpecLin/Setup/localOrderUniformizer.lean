/-
# The chart map sends a local equation of a prime to a uniformizer

Let `C` be a curve over a field `K`, `R` a `K`-valuation ring with fraction field `F`, `W ⊆ C`
an affine chart with coordinate ring `A = Γ(C,W)` and `B = A ⊗_K R` the coordinate ring of the
relative chart `W ×_K Spec R`.  The chart dictionary `chartTensorMap : B →+* K(C_F)` sends the
relative chart into the function field of the generic fibre.

The present lemma is the *generic fibre* companion of
`Work.SpecLin.Alt.ordAt_chartTensorRedMap_eq_one` (which lives on the special fibre): if `p` is a
prime of `B` and `Q` a place of `C_F` such that the local ring `B_p` is, via the chart map,
exactly the valuation ring `O_Q` of `Q` (the order dictionary `hQ`), and if `f ∈ B` generates the
maximal ideal of `B_p` (the hypothesis `hf`), then the image of `f` in `K(C_F)` vanishes to order
exactly one at `Q`: it is a uniformizer.

## Proof

By `hQ`, `ρ(B) ⊆ O_Q` and `O_Q` is the image of `B_p` under the map `ρV : a/s ↦ ρ(a)/ρ(s)`.
The hypothesis `hf` says that `m_{B_p} = (f)`, and `ρV`, being a surjection of local rings, maps
`m_{B_p}` onto `m_{O_Q}`; hence `m_{O_Q} = (ρ f)`.  The general statement
`Work.CurveBasics.Place.ordAt_eq_one_of_span_eq_maximalIdeal` then gives `ord_Q(ρ f) = 1` from
the fact that `ρ f` generates the maximal ideal of the valuation ring `O_Q`.

(For the map `ρV` to be well defined one needs `ρ(s) ≠ 0` for `s ∉ p`; this follows from the
dictionary `hQ`: if `ρ s = 0` for some `s ∉ p` then every `x ∈ K(C_F)` witnesses `∃ a b, b ∉ p ∧
x ρ b = ρ a`, so that `O_Q` would be all of `K(C_F)`, which is absurd since the inverse of a
uniformizer has order `-1`.)
-/
import Mathlib
import Submission.Work.SpecLin.Alt.chartMap
import Submission.Work.CurveBasics.Place.ordAt_eq_one_of_span_eq_maximalIdeal
import Submission.Work.CurveBasics.Order.ord_lem

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.SpecLin.Setup

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

theorem localOrderUniformizer {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    [IsDomain (Work.SpecLin.Core.chartTensor R W)]
    (p : Ideal (Work.SpecLin.Core.chartTensor R W)) [p.IsPrime]
    (Q : (C.baseChange (FractionRing R)).Place)
    (hQ : ∀ x : (C.baseChange (FractionRing R)).functionField,
      (∃ a b : Work.SpecLin.Core.chartTensor R W, b ∉ p ∧
          x * Work.SpecLin.Alt.chartTensorMap R W hW b
            = Work.SpecLin.Alt.chartTensorMap R W hW a)
        ↔ 0 ≤ (C.baseChange (FractionRing R)).ordAt x Q)
    (f : Work.SpecLin.Core.chartTensor R W)
    (hf : Ideal.span ((singleton (algebraMap (Work.SpecLin.Core.chartTensor R W)
            (Localization.AtPrime p) f)) : Set (Localization.AtPrime p))
          = IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    (C.baseChange (FractionRing R)).ordAt
      (Work.SpecLin.Alt.chartTensorMap R W hW f) Q = 1 := by
  classical
  haveI hlocRing : IsLocalRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime p) p
  -- ## Step 1: the chart map lands in the valuation subring of `Q`
  have hρmem : ∀ b : Work.SpecLin.Core.chartTensor R W,
      Work.SpecLin.Alt.chartTensorMap R W hW b ∈ Q.valuationSubring := by
    intro b
    rw [Work.CurveBasics.Place.mem_valuationSubring_iff]
    exact (hQ _).mp
      ⟨b, 1, (fun h1 => ‹p.IsPrime›.ne_top ((Ideal.eq_top_iff_one p).mpr h1)),
        by rw [map_one, mul_one]⟩
  -- ## Step 2: `ρ b ≠ 0` for `b ∉ p`
  have hρne : ∀ b : Work.SpecLin.Core.chartTensor R W, b ∉ p →
      Work.SpecLin.Alt.chartTensorMap R W hW b ≠ 0 := by
    intro b hb h0
    have huni : Q.uniformizer ≠ 0 := by
      intro hz0
      have h1 := Work.CurveBasics.Place.ord_uniformizer Q
      rw [hz0, AlgebraicGeometry.Scheme.ord_zero] at h1
      exact one_ne_zero h1.symm
    have hx : 0 ≤ (C.baseChange (FractionRing R)).ordAt (Q.uniformizer)⁻¹ Q :=
      (hQ _).mp ⟨0, b, hb, by rw [h0, mul_zero, map_zero]⟩
    have hord : (C.baseChange (FractionRing R)).ordAt (Q.uniformizer)⁻¹ Q = -1 := by
      rw [Work.CurveBasics.Curve.ordAt_inv _ huni Q,
        Work.CurveBasics.Curve.ordAt, Work.CurveBasics.Place.ord_uniformizer Q]
    omega
  -- ## Step 3: the reduction map on the local ring `B_p`, with values in `O_Q`
  set g : Work.SpecLin.Core.chartTensor R W →+* ↥(Q.valuationSubring) :=
    { toFun := fun b => ⟨Work.SpecLin.Alt.chartTensorMap R W hW b, hρmem b⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) } with hg_def
  have hgunit : ∀ y : ↥(p.primeCompl),
      IsUnit (g (y : Work.SpecLin.Core.chartTensor R W)) := by
    intro y
    have hy : (y : Work.SpecLin.Core.chartTensor R W) ∉ p := y.2
    have hyV : ((Work.SpecLin.Alt.chartTensorMap R W hW
        (y : Work.SpecLin.Core.chartTensor R W))⁻¹) ∈ Q.valuationSubring := by
      rw [Work.CurveBasics.Place.mem_valuationSubring_iff]
      rw [← hQ ((Work.SpecLin.Alt.chartTensorMap R W hW
        (y : Work.SpecLin.Core.chartTensor R W))⁻¹)]
      exact ⟨1, (y : Work.SpecLin.Core.chartTensor R W), hy, by
        rw [map_one, inv_mul_cancel₀ (hρne _ hy)]⟩
    refine IsUnit.of_mul_eq_one
      (⟨(Work.SpecLin.Alt.chartTensorMap R W hW
        (y : Work.SpecLin.Core.chartTensor R W))⁻¹, hyV⟩ : ↥(Q.valuationSubring)) ?_
    exact Subtype.ext (by
      show (Work.SpecLin.Alt.chartTensorMap R W hW
        (y : Work.SpecLin.Core.chartTensor R W))
        * (Work.SpecLin.Alt.chartTensorMap R W hW
          (y : Work.SpecLin.Core.chartTensor R W))⁻¹ = 1
      exact mul_inv_cancel₀ (hρne _ hy))
  set ρV : Localization.AtPrime p →+* ↥(Q.valuationSubring) :=
    IsLocalization.lift hgunit with hρV_def
  have hρV_alg : ∀ b : Work.SpecLin.Core.chartTensor R W,
      ρV (algebraMap (Work.SpecLin.Core.chartTensor R W) (Localization.AtPrime p) b)
        = g b :=
    fun b => IsLocalization.lift_eq (hg := hgunit) b
  have hρsurj : Function.Surjective ρV := by
    intro v
    have hvord : 0 ≤ (C.baseChange (FractionRing R)).ordAt (v : _) Q :=
      (Work.CurveBasics.Place.mem_valuationSubring_iff _ _ _).mp v.2
    obtain ⟨a, b, hb, hab⟩ := (hQ (v : _)).mpr hvord
    refine ⟨IsLocalization.mk' (Localization.AtPrime p) a
      (⟨b, hb⟩ : ↥(p.primeCompl)), ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    refine Subtype.ext ?_
    show (Work.SpecLin.Alt.chartTensorMap R W hW a : _)
      = (Work.SpecLin.Alt.chartTensorMap R W hW b : _) * (v : _)
    rw [hab.symm, mul_comm]
  -- ## Step 4: `ρ f` generates the maximal ideal of the valuation subring
  have hmapmax : Ideal.map ρV (IsLocalRing.maximalIdeal (Localization.AtPrime p))
      = IsLocalRing.maximalIdeal ↥(Q.valuationSubring) :=
    IsLocalRing.map_maximalIdeal_of_surjective ρV hρsurj
  have hmapspan : Ideal.map ρV (IsLocalRing.maximalIdeal (Localization.AtPrime p))
      = Ideal.span ({g f} : Set ↥(Q.valuationSubring)) := by
    rw [← hf, Ideal.map_span, Set.image_singleton, hρV_alg f]
  have hspan : Ideal.span ((singleton ((⟨Work.SpecLin.Alt.chartTensorMap R W hW f, hρmem f⟩ :
      ↥(Q.valuationSubring)))) : Set ↥(Q.valuationSubring))
      = IsLocalRing.maximalIdeal ↥(Q.valuationSubring) :=
    hmapspan.symm.trans hmapmax
  -- ## Step 5: a generator of the maximal ideal is a uniformizer
  exact Work.CurveBasics.Place.ordAt_eq_one_of_span_eq_maximalIdeal Q
    (Work.SpecLin.Alt.chartTensorMap R W hW f) (hρmem f) hspan

end Work.SpecLin.Setup
