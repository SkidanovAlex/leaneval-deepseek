/-
# Namespace mirror of `Work.SpecLin.Alt.ordAt_chartTensorRedMap_eq_zero_iff_isUnit`

This file is an exact copy of `Submission/Work/SpecLin/Alt/ordAt_chartTensorRedMap_eq_zero_iff_isUnit.lean` (module `Work.SpecLin.Alt.ordAt_chartTensorRedMap_eq_zero_iff_isUnit`), changed in exactly three ways:

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
/-
# The order of vanishing of a reduction at a closed point of the special fibre

The "order-one dictionary" companion of `Work.SpecLin.Alt.Up.ordAt_chartTensorRedMap_eq_one`:
for a curve `C` over a field `K`, a `K`-valuation ring `R` (`κ = R ⧸ m_R` its residue field),
an affine open chart `W ⊆ C` with coordinate ring `A = Γ(C,W)`, the relative chart
`B = A ⊗_K R`, its fibre prime `P = m_R·B = chartFibrePrime R W`, a maximal ideal `N ⊇ P` of `B`
and the closed point `z` of the special fibre `C_κ` cut out by `N` (hypothesis `hz`, the
membership dictionary for the local ring of `z`), the reduction `ρ(f)` of an element
`f ∈ B ∖ P` vanishes to order `0` at `z` exactly when `f` is a unit of the local ring `B_N`.

Equivalently: the `N`-adic valuation of `B_N` (restricted to `B ∖ P`) agrees with the order of
vanishing at `z` of the reduction.  This is the "unit/order-zero" half of the local dictionary;
the "uniformizer/order-one" half is `ordAt_chartTensorRedMap_eq_one`.

## Proof

Write `ρ := chartTensorRedMap R W hW` and `y := ρ f`.  The reduction map kills exactly the fibre
prime (`ker ρ = P`, which follows from `chartFibreQuotMap_isFractionRing`), so `f ∉ P` gives
`y ≠ 0`.  The hypothesis `hz` applied to `y` shows `0 ≤ ord y` (take `a = f`, `b = 1`), while
applied to `y⁻¹` it identifies `0 ≤ ord y⁻¹` with `ρ`-membership of the fraction `y⁻¹` in the
localisation `B_N`, which by `ker ρ = P ⊆ N` is exactly `f ∉ N`.  Since a nonzero element of a
valued field has order zero exactly when both it and its inverse are regular at the place, the
equivalence follows.
-/
import Mathlib
import Submission.Work.SpecLin.Up.Alt.chartMap
import Submission.Work.SpecLin.Up.Alt.exists_chartTensorFibrePoint
import Submission.Work.SpecLin.Up.Alt.chartFibreQuotMap_isFractionRing
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedVariables false

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace Work.SpecLin.Alt
namespace Up

open Work.CurveBasics in
/-- **The order-zero dictionary, ring-theoretic form.**  For any ring homomorphism `ρ` out of the
relative chart `B = Γ(C,W) ⊗_K R` whose kernel is the fibre prime `P` and which realises the
`N`-adic localisation of `B` as the valuation subring of the place `z`, the reduction `ρ f` of an
element `f ∉ P` vanishes to order zero at `z` exactly when `f` is invertible in `B_N`. -/
private theorem ordAt_eq_zero_iff_not_mem {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type _) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens)
    (N : Ideal (Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W)) [N.IsMaximal]
    (hPN : Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W ≤ N)
    (ρ : Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W →+*
      (C.baseChange (IsLocalRing.ResidueField R)).functionField)
    (hker : RingHom.ker ρ = Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W)
    (z : (C.baseChange (IsLocalRing.ResidueField R)).Place)
    (hz : ∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
      (∃ a b : Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W, b ∉ N ∧ x * ρ b = ρ a)
        ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z)
    (f : Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W)
    (hf : f ∉ Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W) :
    (C.baseChange (IsLocalRing.ResidueField R)).ordAt (ρ f) z = 0 ↔ f ∉ N := by
  classical
  -- The reduction of `f` is nonzero, since `f` is not in the kernel of `ρ`.
  have hy : ρ f ≠ 0 := by
    intro h0
    exact hf (hker ▸ RingHom.mem_ker.mpr h0)
  -- A nonzero element has order zero exactly when its inverse has nonnegative order.
  have hcase_inv : (C.baseChange (IsLocalRing.ResidueField R)).ordAt (ρ f)⁻¹ z
      = - (C.baseChange (IsLocalRing.ResidueField R)).ordAt (ρ f) z := by
    change AlgebraicGeometry.Scheme.ord (ρ f)⁻¹ z.point
      = - AlgebraicGeometry.Scheme.ord (ρ f) z.point
    rw [Work.CurveBasics.Curve.Place.ord_eq_neg_log_valuation _ z ((ρ f)⁻¹),
        Work.CurveBasics.Curve.Place.ord_eq_neg_log_valuation _ z (ρ f),
        Valuation.map_inv, WithZero.log_inv]
  -- `ρ f` is regular at `z`: take the fraction `ρ f = ρ f / ρ 1`.
  have hnonneg : 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt (ρ f) z := by
    rw [← hz (ρ f)]
    refine ⟨f, 1, ?_, by rw [map_one, mul_one]⟩
    intro h1
    exact (Ideal.IsMaximal.ne_top ‹N.IsMaximal›) (Ideal.eq_top_iff_one N |>.mpr h1)
  have hkey : (C.baseChange (IsLocalRing.ResidueField R)).ordAt (ρ f) z = 0
      ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt (ρ f)⁻¹ z := by
    rw [hcase_inv]
    constructor
    · intro h; rw [h]; simp
    · intro h; omega
  -- The order `0 ≤ ord (ρ f)⁻¹` is the `ρ`-membership of `(ρ f)⁻¹` in `B_N`.
  rw [hkey, ← hz (ρ f)⁻¹]
  constructor
  · -- `(ρ f)⁻¹ ∈ ρ(B)_N` forces `f ∉ N`: otherwise `f ∈ N` makes the numerator divisible by `f`.
    rintro ⟨a, b, hb, hab⟩ hfN
    have hmem : b - f * a ∈ RingHom.ker ρ := by
      rw [RingHom.mem_ker, map_sub, map_mul]
      have h1 : ρ b = ρ f * ρ a := by
        rw [← hab, ← mul_assoc, mul_inv_cancel₀ hy, one_mul]
      rw [h1]; ring
    rw [hker] at hmem
    have hfa : f * a ∈ N := N.mul_mem_right a hfN
    have : b ∈ N := by
      have h2 := N.add_mem (hPN hmem) hfa
      simpa using h2
    exact hb this
  · -- Conversely `f ∉ N` realises `(ρ f)⁻¹` as the fraction `ρ 1 / ρ f`.
    intro hfN
    exact ⟨1, f, hfN, by rw [map_one, inv_mul_cancel₀ hy]⟩

theorem ordAt_chartTensorRedMap_eq_zero_iff_isUnit {K : Type _} [Field K]
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
        ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z)
    (f : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
    (hf : f ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W) :
    ((C.baseChange (IsLocalRing.ResidueField R)).ordAt
        (Work.SpecLin.Alt.Up.chartTensorRedMap R W hW f) z = 0)
      ↔ IsUnit (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (Localization.AtPrime N) f) := by
  classical
  -- ## Step 1: the reduction map kills exactly the fibre prime
  have hφinj : Function.Injective (chartFibreQuotMap (K:=K) (C:=C) R W hW) := by
    have hfr : @IsFractionRing (Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W ⧸
        Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W) _
        (C.baseChange (IsLocalRing.ResidueField R)).functionField _
        ((chartFibreQuotMap (K:=K) (C:=C) R W hW).toAlgebra) :=
      chartFibreQuotMap_isFractionRing (K:=K) (C:=C) R W hW
    have hinj := @IsFractionRing.injective (Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W ⧸
        Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W) _
        (C.baseChange (IsLocalRing.ResidueField R)).functionField _
        ((chartFibreQuotMap (K:=K) (C:=C) R W hW).toAlgebra) hfr
    simpa only [RingHom.algebraMap_toAlgebra] using hinj
  have hker : RingHom.ker (chartTensorRedMap (K:=K) (C:=C) R W hW)
      = Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W := by
    refine le_antisymm ?_ (chartFibrePrime_le_ker_redMap (K:=K) (C:=C) R W hW)
    intro x hx
    rw [RingHom.mem_ker] at hx
    have h1 : chartFibreQuotMap (K:=K) (C:=C) R W hW
        (Ideal.Quotient.mk (Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W) x) = 0 := by
      rw [chartFibreQuotMap_mk]
      exact hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hφinj (by rw [h1, map_zero]))
  -- ## Step 2: the order-zero dictionary in the local ring `B_N`
  have hmain : (C.baseChange (IsLocalRing.ResidueField R)).ordAt
      (chartTensorRedMap (K:=K) (C:=C) R W hW f) z = 0 ↔ f ∉ N :=
    ordAt_eq_zero_iff_not_mem (K:=K) (C:=C) R W N hPN
      (chartTensorRedMap (K:=K) (C:=C) R W hW) hker z hz f hf
  -- ## Step 3: units of `B_N` are the elements outside `N`
  rw [hmain, IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime N) N f,
    Ideal.mem_primeCompl_iff]

end Up
end Work.SpecLin.Alt

