/-
# Namespace mirror of `Work.SpecLin.Core.orderDataSectionEquation`

This file is an exact copy of `Submission/Work/SpecLin/Core/orderDataSectionEquation.lean` (module `Work.SpecLin.Core.orderDataSectionEquation`), changed in exactly three ways:

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
import Submission.Work.SpecLin.Up.Alt.chartTensorMap_isFractionRing
import Submission.Work.SpecLin.Core.chartVocab
import Submission.Work.SpecLin.Up.Alt.le_ordAt_chartTensorMap_iff_exists
import Submission.Work.SpecLin.Core.unitAtAtMaximal
import Submission.Work.SpecLin.Up.Alt.horizontalHht
import Submission.Work.SpecLin.Up.Alt.mem_iff_le_of_span_map_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.SpecLin.Core
namespace Up

/-- **Localising a local equation.**  If `f` is a local equation of the ideal `I` at a maximal
ideal `N` (i.e. `I·B_N = (f)·B_N`), then it is also a local equation of `I` at every prime
`q ≤ N`:  localisation at `N` is a further localisation of localisation at `q`. -/
private theorem localEquation_localize {B : Type u} [CommRing B] [IsDomain B]
    (N : Ideal B) [N.IsMaximal] (I : Ideal B) (f : B) (q : Ideal B)
    (hq : q.IsPrime) (hqN : q ≤ N)
    (hgen : I.map (algebraMap B (Localization.AtPrime N))
        = Ideal.span {algebraMap B (Localization.AtPrime N) f}) :
    I.map (algebraMap B (Localization.AtPrime q))
      = Ideal.span {algebraMap B (Localization.AtPrime q) f} := by
  haveI hNp : N.IsPrime := ‹N.IsMaximal›.isPrime
  have key : algebraMap B (Localization.AtPrime q) f
      ∈ Ideal.map (algebraMap B (Localization.AtPrime q)) I := by
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl
      (Localization.AtPrime q) I f]
    have hmem : algebraMap B (Localization.AtPrime N) f
        ∈ I.map (algebraMap B (Localization.AtPrime N)) := by
      rw [hgen]; exact Ideal.mem_span_singleton_self _
    obtain ⟨m, hm, hmf⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff N.primeCompl
        (Localization.AtPrime N) I f).mp hmem
    exact ⟨m, fun hmq => hm (hqN hmq), hmf⟩
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    have hxS : algebraMap B (Localization.AtPrime N) x
        ∈ Ideal.span {algebraMap B (Localization.AtPrime N) f} := by
      rw [← hgen]; exact Ideal.mem_map_of_mem _ hx
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hxS
    obtain ⟨⟨d, s⟩, hs⟩ := IsLocalization.surj N.primeCompl c
    have hxs : x * (s : B) = f * d := by
      apply IsLocalization.injective (Localization.AtPrime N)
        (Ideal.primeCompl_le_nonZeroDivisors N)
      rw [map_mul, map_mul, ← hc, ← hs]
      ring
    have hs' : (s : B) ∈ q.primeCompl := fun h => s.2 (hqN h)
    obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.AtPrime q) ⟨(s : B), hs'⟩
    have hu' : (u : Localization.AtPrime q) = algebraMap B (Localization.AtPrime q) (s : B) := hu
    have h0 : algebraMap B (Localization.AtPrime q) x
          * algebraMap B (Localization.AtPrime q) (s : B)
        = algebraMap B (Localization.AtPrime q) f
          * algebraMap B (Localization.AtPrime q) d := by
      rw [← map_mul, ← map_mul, hxs]
    have hthis : algebraMap B (Localization.AtPrime q) x * (u : Localization.AtPrime q)
        = algebraMap B (Localization.AtPrime q) f
          * algebraMap B (Localization.AtPrime q) d := by
      simpa only [hu'] using h0
    rw [Ideal.mem_span_singleton']
    refine ⟨algebraMap B (Localization.AtPrime q) d * ↑u⁻¹, ?_⟩
    calc (algebraMap B (Localization.AtPrime q) d * ↑u⁻¹)
            * algebraMap B (Localization.AtPrime q) f
        = (algebraMap B (Localization.AtPrime q) f
            * algebraMap B (Localization.AtPrime q) d) * ↑u⁻¹ := by ring
      _ = (algebraMap B (Localization.AtPrime q) x * ↑u) * ↑u⁻¹ := by rw [← hthis]
      _ = algebraMap B (Localization.AtPrime q) x := by
            rw [mul_assoc, Units.mul_inv, mul_one]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact key

/-- **Order data at a horizontal prime for a local equation of a section.** In the relative
chart `B = Γ(C,W) ⊗_K R`, `I = sectionPrime R W φ = ker(B →_K R)` is the prime of a section,
`N ⊇ P = 𝔪_R·B` is maximal and `f ∈ B ∖ P` is a *local equation* of `I` at `N`
(`I·B_N = (f)·B_N`).  For a height-one prime `q ≤ N` of `B` which is *horizontal*
(`q ∩ R = 0`, expressed as `includeRight r ∉ q` for all `r ≠ 0`) and a place `Q` of the generic
fibre attached to `q` by the membership dictionary, the reduction `φ(f) ∈ K(C_F)` vanishes at
`Q` to order *one* exactly when `I ≤ q`, and to order *zero* otherwise.

Sketch: localising `hf` at `q ≤ N` gives `I·B_q = (f)·B_q`.  If `I ≤ q` then `ht I ≤ ht q = 1`
and `I ≠ 0` (`I = 0` would force `f = 0 ∈ P`, contradicting `hfP`), so `ht I = 1` and hence
`q = I`; then `f B_q = q B_q` and `f` is a uniformizer of the DVR `B_q`.  If `¬ I ≤ q` then
`I B_q = B_q`, so `f` is a unit of `B_q`.  Transfer along `hQdict` (with
`Work.SpecLin.Alt.Up.le_ordAt_chartTensorMap_iff_exists` for the `k = 1` lower bound and for the
`k = 2` contradiction `q B_q = q² B_q`). -/
theorem orderDataSectionEquation {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (φ : C.left.presheaf.obj (Opposite.op W) →ₐ[K] R)
    (N : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) [N.IsMaximal]
    (hPN : Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W ≤ N)
    (f : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
    (hfP : f ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (hf : (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W φ).map
        (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (Localization.AtPrime N))
      = Ideal.span (singleton (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (Localization.AtPrime N) f)))
    (q : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W))
    (hq : q.IsPrime) (hq1 : q.height = 1) (hqN : q ≤ N)
    (hqmiss : ∀ r : R, r ≠ 0 → Algebra.TensorProduct.includeRight r ∉ q)
    (Q : (C.baseChange (FractionRing R)).Place)
    (hQdict : ∀ x : (C.baseChange (FractionRing R)).functionField,
      (∃ a b : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W, b ∉ q ∧
          x * Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW b
            = Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW a)
        ↔ 0 ≤ (C.baseChange (FractionRing R)).ordAt x Q) :
    ((C.baseChange (FractionRing R)).ordAt
        (Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW f) Q = 1
      ↔ Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W φ ≤ q) ∧
    ((C.baseChange (FractionRing R)).ordAt
        (Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW f) Q = 0
      ↔ ¬ Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W φ ≤ q) := by
  classical
  let B := Work.SpecLin.Core.chartTensor (K := K) (C := C) R W
  let L := (C.baseChange (FractionRing R)).functionField
  let F : B →+* L := Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW
  let I : Ideal B := Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W φ
  haveI hBdom : IsDomain B := Work.SpecLin.Core.isDomain_chartTensor (K := K) (C := C) R W hW
  haveI hNp : N.IsPrime := ‹N.IsMaximal›.isPrime
  haveI hqp : q.IsPrime := hq
  show ((C.baseChange (FractionRing R)).ordAt (F f) Q = 1 ↔ I ≤ q) ∧
       ((C.baseChange (FractionRing R)).ordAt (F f) Q = 0 ↔ ¬ I ≤ q)
  -- ## The chart map is injective
  have hFinj : Function.Injective F := by
    have hfr : @IsFractionRing B _ L _ (F.toAlgebra) :=
      Work.SpecLin.Alt.Up.chartTensorMap_isFractionRing (K := K) (C := C) R W hW
    have hinj := @IsFractionRing.injective B _ L _ (F.toAlgebra) hfr
    simpa only [RingHom.algebraMap_toAlgebra] using hinj
  have hf0 : f ≠ 0 := fun h => hfP (h ▸ Ideal.zero_mem _)
  -- ## The order dictionary for all powers of `q`
  have hpow : ∀ k : ℕ, (((k : ℕ) : ℤ) ≤ (C.baseChange (FractionRing R)).ordAt (F f) Q ↔
      ∃ b : B, b ∉ q ∧ f * b ∈ q ^ k) := by
    intro k
    have h := Work.SpecLin.Alt.Up.le_ordAt_chartTensorMap_iff_exists (K := K) (C := C) R W hW
      q hq hqmiss Q hQdict f hf0 k
    constructor
    · intro hk
      obtain ⟨a, b, hb, hab, haq⟩ := h.mp hk
      have hfb : f * b = a := hFinj (by rw [map_mul]; exact hab)
      exact ⟨b, hb, by rw [hfb]; exact haq⟩
    · rintro ⟨b, hb, hfb⟩
      exact h.mpr ⟨f * b, b, hb, by rw [map_mul], hfb⟩
  have hpow1 : (1 : ℤ) ≤ (C.baseChange (FractionRing R)).ordAt (F f) Q ↔ f ∈ q :=
    (hpow 1).trans (by
      constructor
      · rintro ⟨b, hb, hfb⟩
        exact (Ideal.IsPrime.mem_or_mem hq (by simpa using hfb)).resolve_right hb
      · intro hfq
        exact ⟨1, fun h1 => (Ideal.IsPrime.ne_top hq) ((Ideal.eq_top_iff_one q).mpr h1),
          by simpa using hfq⟩)
  -- ## `f ∈ q` is equivalent to `I ≤ q`
  have hmem : (f ∈ q ↔ I ≤ q) :=
    Work.SpecLin.Alt.Up.mem_iff_le_of_span_map_eq N I f q hq hqN hf
  -- ## The local equation survives localising at `q`
  have hloc : I.map (algebraMap B (Localization.AtPrime q))
      = Ideal.span {algebraMap B (Localization.AtPrime q) f} :=
    localEquation_localize N I f q hq hqN hf
  -- ## `I ≠ ⊥`
  have hIbot : I ≠ ⊥ := by
    intro h
    have hspan' : I.map (algebraMap B (Localization.AtPrime N))
        = Ideal.span {algebraMap B (Localization.AtPrime N) f} := hf
    rw [h, Ideal.map_bot] at hspan'
    have hfz : f = 0 :=
      IsLocalization.injective (Localization.AtPrime N)
        (Ideal.primeCompl_le_nonZeroDivisors N)
        (by simpa using (Ideal.span_singleton_eq_bot.mp hspan'.symm))
    exact hfP (hfz ▸ Ideal.zero_mem _)
  -- ## If `I ≤ q` then the order is at most one
  have hkey : I ≤ q → ¬ (2 : ℤ) ≤ (C.baseChange (FractionRing R)).ordAt (F f) Q := by
    intro hIq h2
    obtain ⟨b, hb, hfb⟩ := (hpow 2).mp h2
    -- `I = q`, from the height hypothesis
    have hIeq : I = q := by
      have hIh0 : I.height ≠ 0 := fun h0 => hIbot (Ideal.height_eq_zero_iff_eq_bot.mp h0)
      by_contra hne
      have hlt : I < q := lt_of_le_of_ne hIq hne
      haveI hIpri : I.IsPrime := Work.SpecLin.Core.isPrime_sectionPrime (K := K) (C := C) R W φ
      haveI hqfin : q.FiniteHeight :=
        (Ideal.finiteHeight_iff q).mpr (Or.inr (by rw [hq1]; exact ENat.natCast_ne_top 1))
      have hh : I.height < q.height := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
      rw [hq1] at hh
      exact hIh0 (Order.lt_one_iff.mp hh)
    have hqmap : q.map (algebraMap B (Localization.AtPrime q))
        = Ideal.span {algebraMap B (Localization.AtPrime q) f} := by
      have h' := hloc
      rw [hIeq] at h'
      exact h'
    haveI hlocRing : IsLocalRing (Localization.AtPrime q) :=
      IsLocalization.AtPrime.isLocalRing (Localization.AtPrime q) q
    have hmem2 : algebraMap B (Localization.AtPrime q) f
        ∈ (q ^ 2).map (algebraMap B (Localization.AtPrime q)) := by
      rw [IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl
        (Localization.AtPrime q) (q ^ 2) f]
      refine ⟨b, hb, ?_⟩
      rw [mul_comm]
      exact hfb
    rw [Ideal.map_pow, hqmap, Ideal.span_singleton_pow] at hmem2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem2
    have hgf0 : algebraMap B (Localization.AtPrime q) f ≠ 0 := fun h =>
      hf0 (IsLocalization.injective (Localization.AtPrime q)
        (Ideal.primeCompl_le_nonZeroDivisors q) (by simpa using h))
    have hunit : IsUnit (algebraMap B (Localization.AtPrime q) f) := by
      have h3 : c * algebraMap B (Localization.AtPrime q) f = 1 := by
        refine mul_right_cancel₀ hgf0 ?_
        calc (c * algebraMap B (Localization.AtPrime q) f)
                * algebraMap B (Localization.AtPrime q) f
            = c * (algebraMap B (Localization.AtPrime q) f) ^ 2 := by ring
          _ = algebraMap B (Localization.AtPrime q) f := hc
          _ = 1 * algebraMap B (Localization.AtPrime q) f := by rw [one_mul]
      exact IsUnit.of_mul_eq_one c (by rw [mul_comm]; exact h3)
    have hmemmax : algebraMap B (Localization.AtPrime q) f
        ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q)]
      exact Ideal.mem_map_of_mem _ (hmem.mpr hIq)
    exact (IsLocalRing.notMem_maximalIdeal.mpr hunit) hmemmax
  -- ## The order is nonnegative
  have hge0 : (0 : ℤ) ≤ (C.baseChange (FractionRing R)).ordAt (F f) Q :=
    (hQdict (F f)).mp ⟨f, 1,
      fun h1 => (Ideal.IsPrime.ne_top hq) ((Ideal.eq_top_iff_one q).mpr h1),
      by rw [map_one, mul_one]⟩
  constructor
  · constructor
    · intro h1
      exact hmem.mp (hpow1.mp (le_of_eq h1.symm))
    · intro hIq
      have hge : (1 : ℤ) ≤ (C.baseChange (FractionRing R)).ordAt (F f) Q :=
        hpow1.mpr (hmem.mpr hIq)
      have hnot := hkey hIq
      omega
  · constructor
    · intro h0 hIq
      have hge : (1 : ℤ) ≤ (C.baseChange (FractionRing R)).ordAt (F f) Q :=
        hpow1.mpr (hmem.mpr hIq)
      omega
    · intro hIq
      have hn1 : ¬ (1 : ℤ) ≤ (C.baseChange (FractionRing R)).ordAt (F f) Q :=
        fun h1 => hIq (hmem.mp (hpow1.mp h1))
      omega

end Up
end Work.SpecLin.Core

