/-
# Namespace mirror of `Work.SpecLin.Alt.exists_chartTensorRedMap_surjective_ker`

This file is an exact copy of `Submission/Work/SpecLin/Alt/exists_chartTensorRedMap_surjective_ker.lean` (module `Work.SpecLin.Alt.exists_chartTensorRedMap_surjective_ker`), changed in exactly three ways:

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
import Submission.Work.SpecLin.Up.Alt.chartMap
import Submission.Work.SpecLin.Up.Alt.exists_chartTensorFibrePoint
import Submission.Work.SpecLin.Up.Alt.chartFibreQuotMap_isFractionRing
import Submission.Work.SpecLin.Up.Alt.ordAt_chartTensorRedMap_eq_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace Work.SpecLin.Alt
namespace Up

/-
HINT (from the requester).  The surjectivity half of this statement is proved, sorry-free, inside
`Submission.Work.SpecLin.Alt.ordAt_chartTensorRedMap_eq_one`
(`Submission/Work/SpecLin/Alt/ordAt_chartTensorRedMap_eq_one.lean`, first half of the proof of
`ordAt_chartTensorRedMap_eq_one`): the construction of `g : chartTensor R W →+* ↥(z.valuationSubring)`
from `chartTensorRedMap` using `mem_valuationSubring_iff` and `hz`, of `ρV := IsLocalization.lift hg`,
of `hρV_alg`, and of `Function.Surjective ρV` is copied verbatim from there.  For the kernel:
`RingHom.ker (chartTensorRedMap R W hW) = chartFibrePrime R W` (use
`chartFibrePrime_le_ker_redMap` for `⊇` and the injectivity of `chartFibreQuotMap`
(`chartFibreQuotMap_isFractionRing`), together with `chartFibreQuotMap_mk`, for `⊆`), hence
`RingHom.ker ρV = Ideal.map (algebraMap (chartTensor R W) (Localization.AtPrime N)) (chartFibrePrime R W)`:
for `x = IsLocalization.mk' _ a s` with `s ∉ N`, `ρV x = 0 ↔ g a = 0 ↔ chartTensorRedMap a = 0 ↔ a ∈ chartFibrePrime`,
and conversely every `a ∈ chartFibrePrime` gives `ρV (algebraMap a) = g a = 0`.
-/
theorem exists_chartTensorRedMap_surjective_ker {K : Type _} [Field K]
    {C : Work.CurveBasics.Curve K}
    (R : Type _) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (N : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) [N.IsMaximal]
    (hPN : Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W <= N)
    (z : (C.baseChange (IsLocalRing.ResidueField R)).Place)
    (hz : forall x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
      (exists a b : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W, b ∉ N ∧
          x * Work.SpecLin.Alt.Up.chartTensorRedMap R W hW b
            = Work.SpecLin.Alt.Up.chartTensorRedMap R W hW a)
        ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z) :
    exists ρV : Localization.AtPrime N →+* ↥(z.valuationSubring),
      Function.Surjective ρV ∧
      RingHom.ker ρV = (Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W).map
        (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (Localization.AtPrime N)) := by
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
  refine ⟨ρV, hρsurj, le_antisymm ?_ ?_⟩
  · -- `ker ρV ≤ P · B_N`
    intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨⟨a, s⟩, hs_eq⟩ := IsLocalization.surj N.primeCompl x
    have hga : g a = 0 := by
      have h0 : ρV (algebraMap (Work.SpecLin.Core.chartTensor R W)
          (Localization.AtPrime N) a) = 0 := by
        rw [← hs_eq, map_mul, hx, zero_mul]
      rwa [hρV_alg a] at h0
    have hred0 : chartTensorRedMap (K:=K) (C:=C) R W hW a = 0 := by
      have h2 : ((g a : ↥(z.valuationSubring)) :
          (C.baseChange (IsLocalRing.ResidueField R)).functionField) = 0 := by
        rw [hga]; rfl
      exact h2
    have ha : a ∈ Work.SpecLin.Core.chartFibrePrime R W := by
      rw [← hker]
      exact RingHom.mem_ker.mpr hred0
    have hmem : x * algebraMap (Work.SpecLin.Core.chartTensor R W)
        (Localization.AtPrime N) (s : Work.SpecLin.Core.chartTensor R W) ∈
        (Work.SpecLin.Core.chartFibrePrime R W).map
          (algebraMap (Work.SpecLin.Core.chartTensor R W) (Localization.AtPrime N)) := by
      rw [hs_eq]
      exact Ideal.mem_map_of_mem _ ha
    obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.AtPrime N) s
    have hxu : x = (x * algebraMap (Work.SpecLin.Core.chartTensor R W)
        (Localization.AtPrime N) (s : Work.SpecLin.Core.chartTensor R W))
        * (↑u⁻¹ : Localization.AtPrime N) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [hxu]
    exact Ideal.mul_mem_right _ _ hmem
  · -- `P · B_N ≤ ker ρV`
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change algebraMap (Work.SpecLin.Core.chartTensor R W) (Localization.AtPrime N) a
      ∈ RingHom.ker ρV
    rw [RingHom.mem_ker, hρV_alg a]
    exact Subtype.ext (RingHom.mem_ker.mp
      (chartFibrePrime_le_ker_redMap (K:=K) (C:=C) R W hW ha))

end Up
end Work.SpecLin.Alt

