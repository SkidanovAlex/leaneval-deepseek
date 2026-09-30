/-
# The reduction of a local equation of a maximal ideal is a uniformizer

The "K2 computational core" of the affine-chart computation of
`Submission/Work/SpecLin/Alt/NOTES_chartCoreDiv.md`: for a curve `C` over a field `K`, a
`K`-valuation ring `R` (`κ = R ⧸ m_R` its residue field), an affine open chart `W ⊆ C` with
coordinate ring `A = Γ(C,W)`, the relative chart `B = A ⊗_K R`, its fibre prime
`P = m_R·B = chartFibrePrime R W` and a maximal ideal `N ⊇ P` of `B`, the reduction modulo `P`
of any local equation `f` of `N` (hypothesis `hf`: `f` generates `N` modulo `P` after
localising at `N`) vanishes to order exactly one at the closed point `z` of the special fibre
`C_κ` cut out by `N` (hypothesis `hz`, the membership dictionary for the local ring of `z`).

See the discussion in `NOTES_chartCoreDiv.md` ("K2 computational core").

## Proof

The hypothesis `hz` says that the valuation subring `O_z ⊆ K(C_κ)` of the place `z` is exactly
the image of the localisation `B_N ⧸ P·B_N` of `B` at `N` along the reduction map: an element
of `K(C_κ)` is regular at `z` if and only if it can be written `ρ(a)/ρ(b)` with `b ∉ N`.  Hence
the reduction map induces a *surjective* ring homomorphism

`ρV : B_N ⟶ O_z`,   `ρV (a/s) = ρ(a)/ρ(s)`,

whose kernel is contained in the maximal ideal of `B_N`; a surjection of local rings therefore
sends `m_{B_N}` onto `m_{O_z}`.  Since `hf` computes `m_{B_N} = (f)·B_N + P·B_N` and `ρV` kills
`P·B_N`, we get `m_{O_z} = (ρ(f))`: the reduction of `f` generates the maximal ideal of `O_z`.
The last step is the general fact that a generator of the maximal ideal of the valuation subring
of a place has order of vanishing one
(`Work.CurveBasics.Place.ordAt_eq_one_of_span_eq_maximalIdeal`).

The injectivity of `ρ` needed for `hz` to identify the image with `O_z` is not needed: `hz`
already identifies the *image*, and surjectivity of `ρV` plus `ker ρV ⊆ m_{B_N}` is all that is
used.  What is used about the reduction map is only that its kernel is exactly `P`, which comes
from `chartFibreQuotMap_isFractionRing`.
-/
import Mathlib
import Submission.Work.SpecLin.Alt.chartMap
import Submission.Work.SpecLin.Alt.chartFibreQuotMap_isFractionRing
import Submission.Work.CurveBasics.Place.ord_uniformizer
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff
import Submission.Work.CurveBasics.Order.mem_maximalIdeal_pow_iff_ordAt
import Submission.Work.CurveBasics.Place.ordAt_eq_one_of_span_eq_maximalIdeal
import Submission.Work.SpecLin.Core.linEquiv_of_sections_of_chart

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

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace Work.SpecLin.Alt

theorem ordAt_chartTensorRedMap_eq_one {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type _) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (N : Ideal (Work.SpecLin.Core.chartTensor R W)) [N.IsMaximal]
    (hPN : Work.SpecLin.Core.chartFibrePrime R W ≤ N)
    (z : (C.baseChange (IsLocalRing.ResidueField R)).Place)
    (hz : ∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
      (∃ a b : Work.SpecLin.Core.chartTensor R W, b ∉ N ∧
          x * Work.SpecLin.Alt.chartTensorRedMap R W hW b
            = Work.SpecLin.Alt.chartTensorRedMap R W hW a)
        ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z)
    (f : Work.SpecLin.Core.chartTensor R W)
    (hf : (Ideal.span ({f} : Set (Work.SpecLin.Core.chartTensor R W))).map
            (algebraMap (Work.SpecLin.Core.chartTensor R W) (Localization.AtPrime N)) ⊔
          (Work.SpecLin.Core.chartFibrePrime R W).map
            (algebraMap (Work.SpecLin.Core.chartTensor R W) (Localization.AtPrime N))
        = N.map (algebraMap (Work.SpecLin.Core.chartTensor R W) (Localization.AtPrime N))) :
    (C.baseChange (IsLocalRing.ResidueField R)).ordAt
      (Work.SpecLin.Alt.chartTensorRedMap R W hW f) z = 1 := by
  classical
  haveI hNprime : N.IsPrime := ‹N.IsMaximal›.isPrime
  haveI hlocRing : IsLocalRing (Localization.AtPrime N) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime N) N
  -- ## Step 0: the reduction map kills exactly the fibre prime
  have hφinj : Function.Injective (chartFibreQuotMap (K:=K) (C:=C) R W hW) := by
    have hfr : @IsFractionRing (Work.SpecLin.Core.chartTensor R W ⧸
        Work.SpecLin.Core.chartFibrePrime R W) _
        (C.baseChange (IsLocalRing.ResidueField R)).functionField _
        ((chartFibreQuotMap (K:=K) (C:=C) R W hW).toAlgebra) :=
      chartFibreQuotMap_isFractionRing (K:=K) (C:=C) R W hW
    have hinj := @IsFractionRing.injective (Work.SpecLin.Core.chartTensor R W ⧸
        Work.SpecLin.Core.chartFibrePrime R W) _
        (C.baseChange (IsLocalRing.ResidueField R)).functionField _
        ((chartFibreQuotMap (K:=K) (C:=C) R W hW).toAlgebra) hfr
    simpa only [RingHom.algebraMap_toAlgebra] using hinj
  have hker : RingHom.ker (chartTensorRedMap (K:=K) (C:=C) R W hW)
      = Work.SpecLin.Core.chartFibrePrime R W := by
    refine le_antisymm ?_ (chartFibrePrime_le_ker_redMap (K:=K) (C:=C) R W hW)
    intro x hx
    rw [RingHom.mem_ker] at hx
    have h1 : chartFibreQuotMap (K:=K) (C:=C) R W hW
        (Ideal.Quotient.mk (Work.SpecLin.Core.chartFibrePrime R W) x) = 0 := by
      rw [chartFibreQuotMap_mk]
      exact hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hφinj (by rw [h1, map_zero]))
  have hred_ne : ∀ b : Work.SpecLin.Core.chartTensor R W,
      b ∉ N → chartTensorRedMap (K:=K) (C:=C) R W hW b ≠ 0 := by
    intro b hb h0
    have hb' : b ∈ RingHom.ker (chartTensorRedMap (K:=K) (C:=C) R W hW) := h0
    rw [hker] at hb'
    exact hb (hPN hb')
  -- ## Step 1: the reduction map into the valuation subring of `z`
  have hred_mem_V : ∀ b : Work.SpecLin.Core.chartTensor R W,
      chartTensorRedMap (K:=K) (C:=C) R W hW b ∈ z.valuationSubring := by
    intro b
    rw [Work.CurveBasics.Place.mem_valuationSubring_iff]
    rw [← hz (chartTensorRedMap (K:=K) (C:=C) R W hW b)]
    refine ⟨b, 1, ?_, ?_⟩
    · intro h1
      exact (Ideal.IsMaximal.ne_top ‹N.IsMaximal›) ((Ideal.eq_top_iff_one _).mpr h1)
    · rw [map_one, mul_one]
  set g : Work.SpecLin.Core.chartTensor R W →+* ↥(z.valuationSubring) :=
    { toFun := fun b => ⟨chartTensorRedMap (K:=K) (C:=C) R W hW b, hred_mem_V b⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) } with hg_def
  have hg : ∀ y : ↥(N.primeCompl), IsUnit (g (y : Work.SpecLin.Core.chartTensor R W)) := by
    intro y
    have hy : (y : Work.SpecLin.Core.chartTensor R W) ∉ N := y.2
    have hyV : ((chartTensorRedMap (K:=K) (C:=C) R W hW
        (y : Work.SpecLin.Core.chartTensor R W))⁻¹) ∈ z.valuationSubring := by
      rw [Work.CurveBasics.Place.mem_valuationSubring_iff]
      rw [← hz ((chartTensorRedMap (K:=K) (C:=C) R W hW
        (y : Work.SpecLin.Core.chartTensor R W))⁻¹)]
      exact ⟨1, (y : Work.SpecLin.Core.chartTensor R W), hy, by
        rw [map_one, inv_mul_cancel₀ (hred_ne _ hy)]⟩
    refine IsUnit.of_mul_eq_one
      (⟨(chartTensorRedMap (K:=K) (C:=C) R W hW
        (y : Work.SpecLin.Core.chartTensor R W))⁻¹, hyV⟩ : ↥(z.valuationSubring)) ?_
    exact Subtype.ext (by
      show (chartTensorRedMap (K:=K) (C:=C) R W hW
        (y : Work.SpecLin.Core.chartTensor R W))
        * (chartTensorRedMap (K:=K) (C:=C) R W hW
          (y : Work.SpecLin.Core.chartTensor R W))⁻¹ = 1
      exact mul_inv_cancel₀ (hred_ne _ hy))
  set ρV : Localization.AtPrime N →+* ↥(z.valuationSubring) := IsLocalization.lift hg
    with hρV_def
  have hρV_alg : ∀ b : Work.SpecLin.Core.chartTensor R W,
      ρV (algebraMap (Work.SpecLin.Core.chartTensor R W) (Localization.AtPrime N) b) = g b :=
    fun b => IsLocalization.lift_eq (hg := hg) b
  have hρsurj : Function.Surjective ρV := by
    intro v
    have hvord : 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt (v : _) z :=
      (Work.CurveBasics.Place.mem_valuationSubring_iff _ _ _).mp v.2
    obtain ⟨a, b, hb, hab⟩ := (hz (v : _)).mpr hvord
    refine ⟨IsLocalization.mk' (Localization.AtPrime N) a
      (⟨b, hb⟩ : ↥(N.primeCompl)), ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    refine Subtype.ext ?_
    show (chartTensorRedMap (K:=K) (C:=C) R W hW a : _)
      = (chartTensorRedMap (K:=K) (C:=C) R W hW b : _) * (v : _)
    rw [hab.symm, mul_comm]
  -- ## Step 2: the reduction of `f` generates the maximal ideal of the valuation subring
  have hbot : Ideal.map (ρV.comp (algebraMap (Work.SpecLin.Core.chartTensor R W)
      (Localization.AtPrime N))) (Work.SpecLin.Core.chartFibrePrime R W) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    rw [RingHom.mem_ker, RingHom.comp_apply, hρV_alg x]
    have hx' : chartTensorRedMap (K:=K) (C:=C) R W hW x = 0 := by
      have : x ∈ RingHom.ker (chartTensorRedMap (K:=K) (C:=C) R W hW) := by
        rw [hker]; exact hx
      exact this
    exact Subtype.ext hx'
  have hmapN : Ideal.map ρV (IsLocalRing.maximalIdeal (Localization.AtPrime N))
      = Ideal.span ((singleton (ρV (algebraMap (Work.SpecLin.Core.chartTensor R W)
          (Localization.AtPrime N) f))) : Set ↥(z.valuationSubring)) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (R := Work.SpecLin.Core.chartTensor R W)
        N (Localization.AtPrime N), ← hf, Ideal.map_sup, Ideal.map_map, Ideal.map_map,
      Ideal.map_span, hbot, Set.image_singleton, sup_bot_eq]
    rfl
  have hspan : Ideal.span ((singleton ((⟨chartTensorRedMap (K:=K) (C:=C) R W hW f,
        hred_mem_V f⟩ : ↥(z.valuationSubring)))) : Set ↥(z.valuationSubring))
      = IsLocalRing.maximalIdeal ↥(z.valuationSubring) := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective ρV hρsurj, hmapN, hρV_alg f]
    rfl
  -- ## Step 3: a generator of the maximal ideal is a uniformizer
  exact Work.CurveBasics.Place.ordAt_eq_one_of_span_eq_maximalIdeal z
    (chartTensorRedMap (K:=K) (C:=C) R W hW f) (hred_mem_V f) hspan

end Work.SpecLin.Alt
