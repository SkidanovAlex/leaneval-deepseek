/-
# Namespace mirror of `Work.SpecLin.Alt.le_ordAt_chartTensorMap_iff_exists`

This file is an exact copy of `Submission/Work/SpecLin/Alt/le_ordAt_chartTensorMap_iff_exists.lean` (module `Work.SpecLin.Alt.le_ordAt_chartTensorMap_iff_exists`), changed in exactly three ways:

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
# The order of vanishing in the relative chart, powers of the prime `q`

For a curve `C` over a field `K`, a `K`-valuation ring `R` and an affine open chart `W ⊆ C`, let

* `B = Γ(C,W) ⊗_K R` be the coordinate ring of the relative chart (`chartTensor`),
* `f = chartTensorMap : B →+* K(C_F)` the chart dictionary into the function field `K(C_F)` of the
  generic fibre `C_F` (`F = Frac R`),
* `q ⊆ B` a prime ideal missing all nonzero elements of `R` (so `q` is "horizontal", coming from a
  point of the generic fibre),
* `Q` a place of `C_F` whose regularity dictionary is `hQdict`:

  `∃ a b : B, b ∉ q ∧ y * f b = f a  ↔  0 ≤ ord_Q y`  for all `y : K(C_F)`.

The last condition says exactly that the local ring `B_q` of the relative chart at `q` maps onto
the valuation ring `𝒪_Q ⊆ K(C_F)` of `Q`; in particular `qB_q` maps onto the maximal ideal.

This file proves the resulting dictionary for all powers of the maximal ideal / of `q`:

  `k ≤ ord_Q (f x)  ↔  ∃ a b : B, b ∉ q ∧ f x · f b = f a ∧ a ∈ q ^ k`

for every nonzero `x : B`.  The two sides are the two descriptions of `f x ∈ 𝔪_Q ^ k`, once as a
membership in the `k`-th power of the maximal ideal of the valuation ring `𝒪_Q` and once inside the
chart as an element of `q ^ k · B_q` written as a fraction.

The proof is the `k`-fold reinforcement of the `k = 0` case (`hQdict`): the map
`g : B_q → 𝒪_Q` induced by `f` is surjective and injective, hence carries the maximal ideal `qB_q`
of the local ring `B_q` to the maximal ideal of `𝒪_Q`, and therefore `q ^ k B_q` to `𝔪_Q ^ k`.
-/
import Mathlib
import Submission.Work.SpecLin.Up.Alt.chartReading
import Submission.Work.SpecLin.Up.Alt.exists_chartTensorPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace Work.SpecLin.Alt
namespace Up

theorem le_ordAt_chartTensorMap_iff_exists {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type _) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (q : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) (hq : q.IsPrime)
    (hqmiss : ∀ r : R, r ≠ 0 → Algebra.TensorProduct.includeRight r ∉ q)
    (Q : (C.baseChange (FractionRing R)).Place)
    (hQdict : ∀ x : (C.baseChange (FractionRing R)).functionField,
      (∃ a b : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W, b ∉ q ∧
          x * chartTensorMap (K := K) (C := C) R W hW b
            = chartTensorMap (K := K) (C := C) R W hW a)
        ↔ 0 ≤ (C.baseChange (FractionRing R)).ordAt x Q)
    (x : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
    (hx : x ≠ 0) (k : ℕ) :
    ((k : ℤ) ≤ (C.baseChange (FractionRing R)).ordAt
        (chartTensorMap (K := K) (C := C) R W hW x) Q)
      ↔ ∃ a b : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W, b ∉ q ∧
          chartTensorMap (K := K) (C := C) R W hW x
              * chartTensorMap (K := K) (C := C) R W hW b
            = chartTensorMap (K := K) (C := C) R W hW a ∧ a ∈ q ^ k := by
  let B := Work.SpecLin.Core.chartTensor (K := K) (C := C) R W
  let L := (C.baseChange (FractionRing R)).functionField
  let f : B →+* L := chartTensorMap (K := K) (C := C) R W hW
  letI : Algebra B L := f.toAlgebra
  have hfr : IsFractionRing B L := chartTensorMap_isFractionRing (K:=K) (C:=C) R W hW
  -- `f` is injective, so `B` is a domain
  have hfinj : Function.Injective f := by
    have h := IsFractionRing.injective B L
    simpa [f, B, L, RingHom.algebraMap_toAlgebra] using h
  haveI : IsDomain B := hfinj.isDomain
  haveI : IsLocalRing ↥(Q.valuationSubring) := ValuationSubring.isLocalRing Q.valuationSubring
  -- the localization `S = B_q` of the relative chart at `q`
  let S := Localization.AtPrime q
  haveI : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S q
  haveI : IsDomain S := IsLocalization.isDomain_of_local_atPrime (P := q) hq
  -- `f` maps the complement of `q` to units, so it induces `g : S →+* L`
  have hunit : ∀ y : q.primeCompl, IsUnit (f (y : B)) := by
    intro y
    rw [isUnit_iff_ne_zero]
    intro h
    exact y.2 (by
      have hh : (y:B) = 0 := hfinj (by rw [h, map_zero])
      rw [hh]; exact q.zero_mem)
  let g : S →+* L := IsLocalization.lift (M := q.primeCompl) (S := S) (g := f) hunit
  have hg_eq : ∀ a : B, g (algebraMap B S a) = f a := fun a => IsLocalization.lift_eq hunit a
  have hM : q.primeCompl ≤ nonZeroDivisors B := Ideal.primeCompl_le_nonZeroDivisors q
  have hSinj : Function.Injective (algebraMap B S) := IsLocalization.injective S hM
  -- `g` is injective
  have hginj : Function.Injective g := by
    intro x' y' hxy
    have hz : g (x' - y') = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj q.primeCompl (x' - y')
    have h2 : g (x' - y') * g (algebraMap B S (s:B)) = g (algebraMap B S a) := by
      rw [← map_mul, hs]
    rw [hz, zero_mul, hg_eq] at h2
    have ha : a = 0 := hfinj (by rw [← h2, map_zero])
    have hs0 : algebraMap B S (s:B) ≠ 0 := fun h => s.2 (by
      have hh : (s:B) = 0 := hSinj (by rw [h, map_zero])
      rw [hh]; exact q.zero_mem)
    have hz0 : (x' - y') * algebraMap B S (s:B) = 0 := by rw [hs, ha, map_zero]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz0).resolve_right hs0)
  -- `hQdict` says precisely that the image of `g` is the valuation ring `𝒪_Q`
  have hrange : ∀ y : L, y ∈ Q.valuationSubring ↔ ∃ z : S, g z = y := by
    intro y
    rw [Work.CurveBasics.Place.mem_valuationSubring_iff]
    rw [← hQdict y]
    constructor
    · rintro ⟨a, b, hb, h⟩
      refine ⟨IsLocalization.mk' S a (⟨b, hb⟩ : q.primeCompl), ?_⟩
      have hspec : g (IsLocalization.mk' S a (⟨b, hb⟩ : q.primeCompl)) * f b = f a := by
        have h2 := IsLocalization.mk'_spec S a (⟨b, hb⟩ : q.primeCompl)
        calc g (IsLocalization.mk' S a (⟨b, hb⟩ : q.primeCompl)) * f b
            = g (IsLocalization.mk' S a (⟨b, hb⟩ : q.primeCompl)) * g (algebraMap B S b) := by rw [hg_eq b]
          _ = g (IsLocalization.mk' S a (⟨b, hb⟩ : q.primeCompl) * algebraMap B S b) := by rw [map_mul]
          _ = g (algebraMap B S a) := by rw [h2]
          _ = f a := hg_eq a
      have hfb : f b ≠ 0 := fun h0 => hb (by
        have hh : b = 0 := hfinj (by rw [h0, map_zero])
        rw [hh]; exact q.zero_mem)
      exact mul_right_cancel₀ hfb (hspec.trans h.symm)
    · rintro ⟨z, rfl⟩
      obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj q.primeCompl z
      refine ⟨a, (s:B), s.2, ?_⟩
      rw [← hg_eq (s:B), ← hg_eq a, ← map_mul, hs]
  -- corestrict `g` to the valuation ring, the resulting map is bijective
  let gO : S →+* ↥(Q.valuationSubring) :=
    RingHom.codRestrict g Q.valuationSubring (fun z => (hrange (g z)).mpr ⟨z, rfl⟩)
  have hgO_coe : ∀ z : S, ((gO z : ↥(Q.valuationSubring)) : L) = g z :=
    fun z => RingHom.codRestrict_apply g Q.valuationSubring _ z
  have hgOsurj : Function.Surjective gO := by
    intro o
    obtain ⟨z, hz⟩ := (hrange (o : L)).mp o.2
    exact ⟨z, Subtype.ext hz⟩
  have hgOinj : Function.Injective gO := by
    intro a b h
    apply hginj
    have h' : ((gO a : ↥(Q.valuationSubring)) : L) = ((gO b : ↥(Q.valuationSubring)) : L) :=
      congrArg (fun o : ↥(Q.valuationSubring) => (o : L)) h
    rw [hgO_coe a, hgO_coe b] at h'
    exact h'
  -- `gO` sends the maximal ideal of `S` (which is `q B_q`) to the maximal ideal of `𝒪_Q`
  have hmS : IsLocalRing.maximalIdeal S = Ideal.map (algebraMap B S) q :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal q S).symm
  have hker : RingHom.ker gO ≤ IsLocalRing.maximalIdeal S := by
    rw [(RingHom.injective_iff_ker_eq_bot gO).mp hgOinj]
    exact bot_le
  have hmax : (Ideal.map gO (IsLocalRing.maximalIdeal S)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hgOsurj hker
  have hm : Ideal.map gO (IsLocalRing.maximalIdeal S)
      = IsLocalRing.maximalIdeal ↥(Q.valuationSubring) := IsLocalRing.eq_maximalIdeal hmax
  -- consequently `gO` sends `q ^ k B_q` to the `k`-th power of the maximal ideal
  have hchain : Ideal.map gO (Ideal.map (algebraMap B S) (q^k))
      = IsLocalRing.maximalIdeal ↥(Q.valuationSubring) ^ k := by
    rw [Ideal.map_pow, Ideal.map_pow, ← hmS, hm]
  constructor
  · -- `ord_Q (f x) ≥ k ⟹ f x = f a / f b` with `a ∈ q ^ k`
    intro hk
    have hfx0 : f x ≠ 0 := fun h => hx (hfinj (by rw [h, map_zero]))
    have h0 : (0:ℤ) ≤ (C.baseChange (FractionRing R)).ordAt (f x) Q := by
      have hk0 : (0:ℤ) ≤ (k:ℤ) := Int.natCast_nonneg k
      linarith
    have huO : f x ∈ Q.valuationSubring := by
      rw [Work.CurveBasics.Place.mem_valuationSubring_iff]
      exact h0
    have hmem : (⟨f x, huO⟩ : ↥Q.valuationSubring)
        ∈ IsLocalRing.maximalIdeal ↥Q.valuationSubring ^ k :=
      (Work.CurveBasics.Order.mem_maximalIdeal_pow_iff_ordAt _ Q ⟨f x, huO⟩ hfx0 k).mpr hk
    have hmem' : (⟨f x, huO⟩ : ↥Q.valuationSubring)
        ∈ Ideal.map gO (Ideal.map (algebraMap B S) (q^k)) := hchain.symm ▸ hmem
    obtain ⟨z, hzmem, hzg⟩ := (Ideal.mem_map_iff_of_surjective gO hgOsurj).mp hmem'
    obtain ⟨⟨⟨a, ha⟩, s⟩, hs⟩ :=
      (IsLocalization.mem_map_algebraMap_iff q.primeCompl S (I := q^k) (z := z)).mp hzmem
    refine ⟨a, (s:B), s.2, ?_, ha⟩
    have h1 : g z = f x := by
      have hc := congrArg (fun o : ↥(Q.valuationSubring) => (o : L)) hzg
      rw [hgO_coe z] at hc
      exact hc
    rw [← h1, ← hg_eq (s:B), ← hg_eq a, ← map_mul, hs]
  · -- conversely `f x = f a / f b` with `a ∈ q ^ k, b ∉ q` gives `ord_Q (f x) ≥ k`
    rintro ⟨a, b, hb, h, hak⟩
    have hfb : f b ≠ 0 := fun h0 => hb (by
      have hh : b = 0 := hfinj (by rw [h0, map_zero])
      rw [hh]; exact q.zero_mem)
    have hfx0 : f x ≠ 0 := fun h0 => hx (hfinj (by rw [h0, map_zero]))
    have hmk : g (IsLocalization.mk' S a (⟨b, hb⟩ : q.primeCompl)) * f b = f a := by
      have h2 := IsLocalization.mk'_spec S a (⟨b, hb⟩ : q.primeCompl)
      calc g (IsLocalization.mk' S a (⟨b, hb⟩ : q.primeCompl)) * f b
          = g (IsLocalization.mk' S a (⟨b, hb⟩ : q.primeCompl)) * g (algebraMap B S b) := by rw [hg_eq b]
        _ = g (IsLocalization.mk' S a (⟨b, hb⟩ : q.primeCompl) * algebraMap B S b) := by rw [map_mul]
        _ = g (algebraMap B S a) := by rw [h2]
        _ = f a := hg_eq a
    have hzmem : IsLocalization.mk' S a (⟨b, hb⟩ : q.primeCompl)
        ∈ Ideal.map (algebraMap B S) (q^k) := by
      rw [IsLocalization.mk'_mem_map_algebraMap_iff]
      exact ⟨1, q.primeCompl.one_mem, by rw [one_mul]; exact hak⟩
    have hgm : gO (IsLocalization.mk' S a (⟨b, hb⟩ : q.primeCompl))
        ∈ IsLocalRing.maximalIdeal ↥Q.valuationSubring ^ k :=
      hchain ▸ Ideal.mem_map_of_mem gO hzmem
    have hgval : ((gO (IsLocalization.mk' S a (⟨b, hb⟩ : q.primeCompl)) : ↥Q.valuationSubring) : L) = f x := by
      rw [hgO_coe]
      exact mul_right_cancel₀ hfb (hmk.trans h.symm)
    have huO : f x ∈ Q.valuationSubring := by
      rw [← hgval]
      exact (gO (IsLocalization.mk' S a (⟨b, hb⟩ : q.primeCompl))).2
    have hmem : (⟨f x, huO⟩ : ↥Q.valuationSubring)
        ∈ IsLocalRing.maximalIdeal ↥Q.valuationSubring ^ k := by
      rw [show (⟨f x, huO⟩ : ↥Q.valuationSubring) = gO (IsLocalization.mk' S a (⟨b, hb⟩ : q.primeCompl))
        from Subtype.ext hgval.symm]
      exact hgm
    exact (Work.CurveBasics.Order.mem_maximalIdeal_pow_iff_ordAt _ Q ⟨f x, huO⟩ hfx0 k).mp hmem

end Up
end Work.SpecLin.Alt

