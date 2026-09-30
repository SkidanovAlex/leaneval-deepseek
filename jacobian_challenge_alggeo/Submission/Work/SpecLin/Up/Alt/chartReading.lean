/-
# Namespace mirror of `Work.SpecLin.Alt.chartReading`

This file is an exact copy of `Submission/Work/SpecLin/Alt/chartReading.lean` (module `Work.SpecLin.Alt.chartReading`), changed in exactly three ways:

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
# Reading off the divisor of the reduction on the special fibre

This module contains the *local reading-off* step (K2 of
`Submission/Work/SpecLin/Alt/NOTES_chartCoreDiv.md`) of the affine-chart proof of specialisation
of linear equivalence.

Setting: `B := Γ(C,W) ⊗_K R` is the coordinate ring of the relative affine chart, `P = m_R·B`
the prime of the generic point of the special fibre, `N ⊇ P` a maximal ideal (a closed point
`z` of the chart `W_κ` of the special fibre), and `I m` (resp. `J m`) the section ideal of the
`R`-point `s m` (resp. `t m`).  Given elements `a, b, p, q ∈ B ∖ P` and local equations
`f m ∈ I m`, `g m ∈ J m` of the section ideals at `N`, together with the identity
`a·(Π g_m) · q = b·(Π f_m) · p` in `B`, we compute the order of vanishing at `z` of the
reduction of `a/b`:

  `ord_z(red a / red b) = #{m : I m ⊔ P = N} − #{m : J m ⊔ P = N}`.

The identity is exactly what the element `u := h'·(Π g)/(Π f) = p/q` (a unit of `B_N`) produces;
it is stated here as a hypothesis so that the reading-off is independent of how the crux
`u ∈ B_N^×` is proved.
-/
import Mathlib
import Submission.Work.SpecLin.Alt.conservationNumber
import Submission.Work.SpecLin.Up.Alt.chartMap
import Submission.Work.SpecLin.Up.Alt.exists_chartTensorFibrePoint
import Submission.Work.SpecLin.Up.Alt.ordAt_chartTensorRedMap_eq_one
import Submission.Work.SpecLin.Up.Alt.ordAt_chartTensorRedMap_eq_zero_iff_isUnit
import Submission.Work.SpecLin.Up.Alt.sectionPrime_le_iff_ptPlace_eq_residue
import Submission.Work.SpecLin.Alt.sup_eq_of_le_maximal
import Submission.Work.SpecLin.Core.section_prime_sup_fibre_quot

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

namespace Work.SpecLin.Alt
namespace Up

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}

section ReadingOff

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
variable (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]

/-- The reduction map kills exactly the fibre prime: an element of the chart ring which is not in
`P = m_R·B` has nonzero reduction in the function field of the special fibre. -/
theorem chartTensorRedMap_ne_zero_of_notMem {x : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W}
    (hx : x ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W) :
    chartTensorRedMap (K := K) (C := C) R W hW x ≠ 0 := by
  intro h0
  refine hx ?_
  letI : Algebra (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W ⧸
      Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
      ((C.baseChange (IsLocalRing.ResidueField R)).functionField) :=
    (chartFibreQuotMap (K := K) (C := C) R W hW).toAlgebra
  haveI : IsFractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W ⧸
      Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
      ((C.baseChange (IsLocalRing.ResidueField R)).functionField) :=
    chartFibreQuotMap_isFractionRing R W hW
  have hinj : Function.Injective (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W ⧸
      Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
      ((C.baseChange (IsLocalRing.ResidueField R)).functionField)) :=
    IsFractionRing.injective _ _
  refine Ideal.Quotient.eq_zero_iff_mem.mp (hinj ?_)
  rw [map_zero, RingHom.algebraMap_toAlgebra, chartFibreQuotMap_mk]
  exact h0

/-- The sum `I ⊔ P` of a section ideal and the fibre prime is a maximal ideal: its quotient is
the residue field `κ`. -/
theorem sectionPrime_sup_chartFibrePrime_isMaximal
    (φ : Γ(C.left, W) →ₐ[K] R) :
    (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W φ ⊔
      Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _
    (MulEquiv.isField (Field.toIsField (IsLocalRing.ResidueField R))
      (Work.SpecLin.Core.section_prime_sup_fibre_quot (K := K) (R := R) φ).toMulEquiv)

end ReadingOff

section Order

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
variable (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]

/-- The order of vanishing of a product of nonzero rational functions is the sum of the orders. -/
theorem ordAt_prod {F : Type u} [Field F] {ι : Type*} (D : Work.CurveBasics.Curve F)
    (u : ι → D.functionField) (s : Finset ι) (hu : ∀ i ∈ s, u i ≠ 0) (Q : D.Place) :
    D.ordAt (∏ i ∈ s, u i) Q = ∑ i ∈ s, D.ordAt (u i) Q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    show Scheme.ord (1 : D.functionField) Q.point = 0
    exact Work.CurveBasics.Order.ord_one D Q
  | insert a s has ih =>
    have hau : u a ≠ 0 := hu a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, u i ≠ 0 := fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hprod : (∏ i ∈ s, u i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hs
    rw [Finset.prod_insert has, Finset.sum_insert has]
    have h1 : D.ordAt (u a * ∏ i ∈ s, u i) Q
        = D.ordAt (u a) Q + D.ordAt (∏ i ∈ s, u i) Q := by
      rw [show D.ordAt (u a * ∏ i ∈ s, u i) Q = D.div (u a * ∏ i ∈ s, u i) Q from
          (Work.CurveBasics.Curve.div_apply D _ Q).symm,
        Work.CurveBasics.Curve.div_mul D hau hprod, Finsupp.add_apply,
        Work.CurveBasics.Curve.div_apply, Work.CurveBasics.Curve.div_apply]
    rw [h1, ih hs]

end Order

section Indicator

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
variable (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
variable (N : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) [N.IsMaximal]

/-- **The order of the reduction of a local equation.**  If `x ∈ B ∖ P` generates the ideal `I`
at `N` (i.e. its image in `B_N` generates `I·B_N`), then the order of its reduction at `z` is `1`
if `I ≤ N` (the zero locus passes through `z`) and `0` otherwise.  `I` is assumed to have
`I ⊔ P` maximal, which holds for the section ideals. -/
theorem ordAt_chartTensorRedMap_eq_indicator
    (hPN : Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W ≤ N)
    (z : (C.baseChange (IsLocalRing.ResidueField R)).Place)
    (hz : ∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
      (∃ a b : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W, b ∉ N ∧
          x * chartTensorRedMap (K := K) (C := C) R W hW b
            = chartTensorRedMap (K := K) (C := C) R W hW a)
        ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z)
    (x : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
    (hxP : x ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (I : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W))
    (hImax : (I ⊔ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W).IsMaximal)
    (hI : I.map (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
        (Localization.AtPrime N))
      = Ideal.span (singleton (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
        (Localization.AtPrime N) x))) :
    (C.baseChange (IsLocalRing.ResidueField R)).ordAt
        (chartTensorRedMap (K := K) (C := C) R W hW x) z
      = if I ≤ N then 1 else 0 := by
  haveI : N.IsPrime := ‹N.IsMaximal›.isPrime
  by_cases hIN : I ≤ N
  · have hsup : I ⊔ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W = N :=
      Work.SpecLin.Alt.sup_eq_of_le_maximal hPN hIN hImax
    rw [if_pos hIN]
    refine ordAt_chartTensorRedMap_eq_one (K := K) (C := C) R W hW N hPN z hz x ?_
    have h1 : Ideal.map (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (Localization.AtPrime N)) (Ideal.span {x})
        = Ideal.map (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (Localization.AtPrime N)) I := by
      rw [Ideal.map_span, Set.image_singleton, ← hI]
    rw [h1, ← Ideal.map_sup, hsup]
  · rw [if_neg hIN]
    obtain ⟨y, hyI, hyN⟩ :
        ∃ y ∈ I, y ∉ N := by
      by_contra hcon
      exact hIN (fun y hy => by by_contra hyn; exact hcon ⟨y, hy, hyn⟩)
    have hunity : IsUnit (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
        (Localization.AtPrime N) y) :=
      IsLocalization.map_units (Localization.AtPrime N) (⟨y, hyN⟩ : N.primeCompl)
    have htop : I.map (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
        (Localization.AtPrime N)) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hyI) hunity
    have hunit : IsUnit (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
        (Localization.AtPrime N) x) := by
      refine Ideal.span_singleton_eq_top.mp ?_
      rw [← hI, htop]
    exact (ordAt_chartTensorRedMap_eq_zero_iff_isUnit (K := K) (C := C) R W hW N hPN z hz x
      hxP).mpr hunit

end Indicator


section Main

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
variable (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
variable {n : ℕ} (s t : Fin n → Work.SpecLin.CurvePt C R)
  (hs : ∀ m, Set.range ((s m).left).base ⊆ (W : Set C.left))
  (ht : ∀ m, Set.range ((t m).left).base ⊆ (W : Set C.left))

/-- **The special-fibre reading-off.**  In the relative chart `B = Γ(C,W) ⊗_K R`, with fibre
prime `P = m_R·B`, maximal ideal `N ⊇ P` and corresponding closed point `z` of the special fibre
(given by the membership dictionary `hz`), let `a, b ∈ B ∖ P` and let `f m ∈ I m`, `g m ∈ J m` be
local equations of the section ideals at `N`.  If `a·(Π g_m)·q = b·(Π f_m)·p` in `B` with
`p, q` units of `B_N`, then the order of vanishing at `z` of the reduction of `a/b` is the
difference of the numbers of sections passing through `z`. -/
theorem ordAt_chartTensorRedMap_div_eq
    (N : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) [N.IsMaximal]
    (hPN : Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W ≤ N)
    (z : (C.baseChange (IsLocalRing.ResidueField R)).Place)
    (hz : ∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
      (∃ a b : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W, b ∉ N ∧
          x * chartTensorRedMap (K := K) (C := C) R W hW b
            = chartTensorRedMap (K := K) (C := C) R W hW a)
        ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z)
    (a b p q : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
    (ha : a ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (hb : b ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (hp : p ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (hq : q ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (hpN : IsUnit (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
      (Localization.AtPrime N) p))
    (hqN : IsUnit (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
      (Localization.AtPrime N) q))
    (f g : Fin n → Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
    (hfP : ∀ m, f m ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (hgP : ∀ m, g m ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (hfgen : ∀ m, (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
          (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m))).map
        (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (Localization.AtPrime N))
      = Ideal.span (singleton (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (Localization.AtPrime N) (f m))))
    (hggen : ∀ m, (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
          (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m))).map
        (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (Localization.AtPrime N))
      = Ideal.span (singleton (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (Localization.AtPrime N) (g m))))
    (hident : a * (∏ m, g m) * q = b * (∏ m, f m) * p) :
    (C.baseChange (IsLocalRing.ResidueField R)).div
        (chartTensorRedMap (K := K) (C := C) R W hW a
          / chartTensorRedMap (K := K) (C := C) R W hW b) z
      = (Finset.univ.sum fun m : Fin n =>
            if (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
                  (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m)))
                ⊔ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W = N
              then (1 : ℤ) else 0)
        - (Finset.univ.sum fun m : Fin n =>
            if (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
                  (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m)))
                ⊔ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W = N
              then (1 : ℤ) else 0) := by
  classical
  haveI hNp : N.IsPrime := ‹N.IsMaximal›.isPrime
  set I : Fin n → Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W) :=
    fun m => Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
      (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m)) with hIdef
  set J : Fin n → Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W) :=
    fun m => Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
      (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m)) with hJdef
  have hImax : ∀ m, (I m ⊔ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W).IsMaximal :=
    fun m => sectionPrime_sup_chartFibrePrime_isMaximal (K := K) (C := C) R W
      (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m))
  have hJmax : ∀ m, (J m ⊔ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W).IsMaximal :=
    fun m => sectionPrime_sup_chartFibrePrime_isMaximal (K := K) (C := C) R W
      (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m))
  have hred : chartTensorRedMap (K := K) (C := C) R W hW a
        * (∏ m, chartTensorRedMap (K := K) (C := C) R W hW (g m))
        * chartTensorRedMap (K := K) (C := C) R W hW q
      = chartTensorRedMap (K := K) (C := C) R W hW b
        * (∏ m, chartTensorRedMap (K := K) (C := C) R W hW (f m))
        * chartTensorRedMap (K := K) (C := C) R W hW p := by
    have h := congrArg (chartTensorRedMap (K := K) (C := C) R W hW) hident
    simpa only [map_mul, map_prod] using h
  have ha0 : chartTensorRedMap (K := K) (C := C) R W hW a ≠ 0 :=
    chartTensorRedMap_ne_zero_of_notMem (K := K) (C := C) R W hW ha
  have hb0 : chartTensorRedMap (K := K) (C := C) R W hW b ≠ 0 :=
    chartTensorRedMap_ne_zero_of_notMem (K := K) (C := C) R W hW hb
  have hf0 : ∀ m, chartTensorRedMap (K := K) (C := C) R W hW (f m) ≠ 0 :=
    fun m => chartTensorRedMap_ne_zero_of_notMem (K := K) (C := C) R W hW (hfP m)
  have hg0 : ∀ m, chartTensorRedMap (K := K) (C := C) R W hW (g m) ≠ 0 :=
    fun m => chartTensorRedMap_ne_zero_of_notMem (K := K) (C := C) R W hW (hgP m)
  have hford : ∀ m, (C.baseChange (IsLocalRing.ResidueField R)).ordAt
      (chartTensorRedMap (K := K) (C := C) R W hW (f m)) z
      = if I m ⊔ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W = N
          then (1 : ℤ) else 0 := by
    intro m
    have h := ordAt_chartTensorRedMap_eq_indicator (K := K) (C := C) R W hW N hPN z hz
      (f m) (hfP m) (I m) (hImax m) (by rw [hIdef]; exact hfgen m)
    rw [h]
    by_cases hI : I m ≤ N
    · rw [if_pos hI, if_pos (Work.SpecLin.Alt.sup_eq_of_le_maximal hPN hI (hImax m))]
    · rw [if_neg hI, if_neg (fun hc => hI (le_trans le_sup_left (le_of_eq hc)))]
  have hgord : ∀ m, (C.baseChange (IsLocalRing.ResidueField R)).ordAt
      (chartTensorRedMap (K := K) (C := C) R W hW (g m)) z
      = if J m ⊔ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W = N
          then (1 : ℤ) else 0 := by
    intro m
    have h := ordAt_chartTensorRedMap_eq_indicator (K := K) (C := C) R W hW N hPN z hz
      (g m) (hgP m) (J m) (hJmax m) (by rw [hJdef]; exact hggen m)
    rw [h]
    by_cases hJ : J m ≤ N
    · rw [if_pos hJ, if_pos (Work.SpecLin.Alt.sup_eq_of_le_maximal hPN hJ (hJmax m))]
    · rw [if_neg hJ, if_neg (fun hc => hJ (le_trans le_sup_left (le_of_eq hc)))]
  have hpqord : ∀ (x : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
      (hxP : x ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
      (hxN : IsUnit (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
        (Localization.AtPrime N) x)),
      (C.baseChange (IsLocalRing.ResidueField R)).ordAt
        (chartTensorRedMap (K := K) (C := C) R W hW x) z = 0 :=
    fun x hxP hxN => (ordAt_chartTensorRedMap_eq_zero_iff_isUnit (K := K) (C := C) R W hW N hPN
      z hz x hxP).mpr hxN
  have hsplit : ∀ (x y u : (C.baseChange (IsLocalRing.ResidueField R)).functionField)
      (hx : x ≠ 0) (hy : y ≠ 0) (hu : u ≠ 0),
      (C.baseChange (IsLocalRing.ResidueField R)).ordAt (x * y * u) z
        = (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z
          + (C.baseChange (IsLocalRing.ResidueField R)).ordAt y z
          + (C.baseChange (IsLocalRing.ResidueField R)).ordAt u z := by
    intro x y u hx hy hu
    rw [show (C.baseChange (IsLocalRing.ResidueField R)).ordAt (x * y * u) z
        = (C.baseChange (IsLocalRing.ResidueField R)).div (x * y * u) z from
          (Work.CurveBasics.Curve.div_apply _ _ _).symm,
      Work.CurveBasics.Curve.div_mul _ (mul_ne_zero hx hy) hu,
      Work.CurveBasics.Curve.div_mul _ hx hy,
      Finsupp.add_apply, Finsupp.add_apply,
      Work.CurveBasics.Curve.div_apply, Work.CurveBasics.Curve.div_apply,
      Work.CurveBasics.Curve.div_apply]
  have hkey : (C.baseChange (IsLocalRing.ResidueField R)).ordAt
        (chartTensorRedMap (K := K) (C := C) R W hW a) z
        + (∑ m : Fin n, (C.baseChange (IsLocalRing.ResidueField R)).ordAt
            (chartTensorRedMap (K := K) (C := C) R W hW (g m)) z)
        + 0
      = (C.baseChange (IsLocalRing.ResidueField R)).ordAt
          (chartTensorRedMap (K := K) (C := C) R W hW b) z
        + (∑ m : Fin n, (C.baseChange (IsLocalRing.ResidueField R)).ordAt
            (chartTensorRedMap (K := K) (C := C) R W hW (f m)) z)
        + 0 := by
    have h := congrArg (fun w => (C.baseChange (IsLocalRing.ResidueField R)).ordAt w z) hred
    rw [hsplit _ _ _ ha0 (Finset.prod_ne_zero_iff.mpr (fun m _ => hg0 m))
        (chartTensorRedMap_ne_zero_of_notMem (K := K) (C := C) R W hW hq),
      hsplit _ _ _ hb0 (Finset.prod_ne_zero_iff.mpr (fun m _ => hf0 m))
        (chartTensorRedMap_ne_zero_of_notMem (K := K) (C := C) R W hW hp)] at h
    rw [ordAt_prod _ _ _ (fun m _ => hg0 m) z,
        ordAt_prod _ _ _ (fun m _ => hf0 m) z] at h
    rw [hpqord q hq hqN, hpqord p hp hpN] at h
    linarith
  have hmain : (C.baseChange (IsLocalRing.ResidueField R)).ordAt
        (chartTensorRedMap (K := K) (C := C) R W hW a) z
        - (C.baseChange (IsLocalRing.ResidueField R)).ordAt
          (chartTensorRedMap (K := K) (C := C) R W hW b) z
      = (∑ m : Fin n, if I m ⊔ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W = N
            then (1 : ℤ) else 0)
        - (∑ m : Fin n, if J m ⊔ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W = N
            then (1 : ℤ) else 0) := by
    have h := hkey
    rw [Finset.sum_congr rfl (fun m _ => hford m),
        Finset.sum_congr rfl (fun m _ => hgord m)] at h
    linarith
  rw [hIdef, hJdef] at hmain
  rw [Work.SpecLin.div_div (C := C) ha0 hb0, Finsupp.sub_apply,
      Work.CurveBasics.Curve.div_apply, Work.CurveBasics.Curve.div_apply]
  exact hmain



/-- **The reading-off, in the form of the `ptDiv` of the special fibres of the sections.**
Under the same hypotheses as `ordAt_chartTensorRedMap_div_eq`, the divisor of the reduction of
`a/b` at the closed point `z` of the special fibre is the difference of the numbers of sections
`RPt.map (R → κ) (s m)`, resp. `(t m)`, passing through `z`. -/
theorem div_chartTensorRedMap_div_apply
    (N : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) [N.IsMaximal]
    (hPN : Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W ≤ N)
    (z : (C.baseChange (IsLocalRing.ResidueField R)).Place)
    (hz : ∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
      (∃ a b : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W, b ∉ N ∧
          x * chartTensorRedMap (K := K) (C := C) R W hW b
            = chartTensorRedMap (K := K) (C := C) R W hW a)
        ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z)
    (a b p q : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
    (ha : a ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (hb : b ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (hp : p ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (hq : q ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (hpN : IsUnit (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
      (Localization.AtPrime N) p))
    (hqN : IsUnit (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
      (Localization.AtPrime N) q))
    (f g : Fin n → Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
    (hfP : ∀ m, f m ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (hgP : ∀ m, g m ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (hfgen : ∀ m, (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
          (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m))).map
        (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (Localization.AtPrime N))
      = Ideal.span (singleton (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (Localization.AtPrime N) (f m))))
    (hggen : ∀ m, (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
          (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m))).map
        (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (Localization.AtPrime N))
      = Ideal.span (singleton (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (Localization.AtPrime N) (g m))))
    (hident : a * (∏ m, g m) * q = b * (∏ m, f m) * p) :
    (C.baseChange (IsLocalRing.ResidueField R)).div
        (chartTensorRedMap (K := K) (C := C) R W hW a
          / chartTensorRedMap (K := K) (C := C) R W hW b) z
      = (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
            (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))
              (s m))) z
        - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
            (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))
              (t m))) z := by
  classical
  rw [ordAt_chartTensorRedMap_div_eq (K := K) (C := C) R W hW s t hs ht
    N hPN z hz a b p q ha hb hp hq hpN hqN f g hfP hgP hfgen hggen hident]
  congr 1
  · rw [Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Work.SpecLin.ptDiv_apply]
    by_cases h : (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
          (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m)))
        ⊔ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W = N
    · rw [if_pos h, if_pos ((sectionPrime_le_iff_ptPlace_eq_residue (K := K) (C := C) R W hW
        (s m) (hs m) N hPN z hz).mp h)]
    · rw [if_neg h, if_neg (fun hc =>
        h ((sectionPrime_le_iff_ptPlace_eq_residue (K := K) (C := C) R W hW
          (s m) (hs m) N hPN z hz).mpr hc))]
  · rw [Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Work.SpecLin.ptDiv_apply]
    by_cases h : (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
          (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m)))
        ⊔ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W = N
    · rw [if_pos h, if_pos ((sectionPrime_le_iff_ptPlace_eq_residue (K := K) (C := C) R W hW
        (t m) (ht m) N hPN z hz).mp h)]
    · rw [if_neg h, if_neg (fun hc =>
        h ((sectionPrime_le_iff_ptPlace_eq_residue (K := K) (C := C) R W hW
          (t m) (ht m) N hPN z hz).mpr hc))]

end Main

section GenericReading

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
variable (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
variable {n : ℕ} (s t : Fin n → Work.SpecLin.CurvePt C R)
  (hs : ∀ m, Set.range ((s m).left).base ⊆ (W : Set C.left))
  (ht : ∀ m, Set.range ((t m).left).base ⊆ (W : Set C.left))

/-- **The divisor hypothesis, read in the chart.**  Let `Q` be a closed point of the generic
fibre `C_F`, `q` the corresponding height-one prime of the relative chart ring
`B = Γ(C,W) ⊗_K R` (horizontal: `q ∩ R = 0`), with the membership dictionary `hQdict` as
produced by `exists_chartTensorPoint`, and let `h' ∈ K(C_F)^×` have
`div h' = Σ_m [s_m^F] − Σ_m [t_m^F]`.  If the point dictionaries `hI`, `hJ` identify the section
ideals with the fibres of the sections, then

  `ord_Q(h') = #{m : I m ≤ q} − #{m : J m ≤ q}`.

This is the "reading off `hdiv` in the chart" step of the proof plan. -/
theorem ordAt_of_div_eq_sum_ptDiv
    (Q : (C.baseChange (FractionRing R)).Place)
    (q : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W))
    (hQdict : ∀ x : (C.baseChange (FractionRing R)).functionField,
      (∃ a b : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W, b ∉ q ∧
          x * chartTensorMap (K := K) (C := C) R W hW b
            = chartTensorMap (K := K) (C := C) R W hW a)
        ↔ 0 ≤ (C.baseChange (FractionRing R)).ordAt x Q)
    (hI : ∀ m, (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
          (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m)) ≤ q)
        ↔ Work.SpecLin.ptPlace (Work.SpecLin.RPt.map
            (IsScalarTower.toAlgHom K R (FractionRing R)) (s m)) = Q)
    (hJ : ∀ m, (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
          (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m)) ≤ q)
        ↔ Work.SpecLin.ptPlace (Work.SpecLin.RPt.map
            (IsScalarTower.toAlgHom K R (FractionRing R)) (t m)) = Q)
    (h' : (C.baseChange (FractionRing R)).functionField)
    (hdiv' : (C.baseChange (FractionRing R)).div h'
      = (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
            (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (s m)))
        - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
            (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (t m)))) :
    (C.baseChange (FractionRing R)).ordAt h' Q
      = ((Finset.univ.filter fun m : Fin n =>
            Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
              (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m)) ≤ q).card : ℤ)
        - ((Finset.univ.filter fun m : Fin n =>
            Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
              (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m)) ≤ q).card : ℤ) := by
  classical
  have hdivQ := congrArg (fun (D : (C.baseChange (FractionRing R)).Div) => D Q) hdiv'
  rw [Finsupp.sub_apply, Finsupp.finset_sum_apply, Finsupp.finset_sum_apply] at hdivQ
  rw [Work.CurveBasics.Curve.div_apply] at hdivQ
  rw [show (C.baseChange (FractionRing R)).ordAt h' Q = Scheme.ord h' Q.point from rfl, hdivQ]
  congr 1
  · rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Work.SpecLin.ptDiv_apply]
    by_cases hm : Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
          (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m)) ≤ q
    · rw [if_pos ((hI m).mp hm), if_pos hm]
    · rw [if_neg (fun hc => hm ((hI m).mpr hc)), if_neg hm]
  · rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Work.SpecLin.ptDiv_apply]
    by_cases hm : Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
          (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m)) ≤ q
    · rw [if_pos ((hJ m).mp hm), if_pos hm]
    · rw [if_neg (fun hc => hm ((hJ m).mpr hc)), if_neg hm]

end GenericReading

section UnitAt

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
variable (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]

/-- **A quotient of primitive elements is a unit at the fibre prime.**  If `u ∈ Frac B` is the
quotient of two elements `a, b ∈ B ∖ P` of the relative chart, then `u` is a unit of `B_P`.

This is the "easy half" of the crux hypothesis `IsUnitAt u P`: the element
`u = h'·(Π g_m)/(Π f_m)` of the proof is of this shape, with all the factors outside `P`. -/
theorem isUnitAt_chartFibrePrime_of_map_mul_eq
    [IsDomain (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)]
    (a b : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
    (ha : a ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (hb : b ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (u : FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W))
    (hu : algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
        (FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) a
      = u * algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
        (FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) b) :
    Work.SpecLin.Alt.IsUnitAt u
      (Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W) := by
  have hu0 : u ≠ 0 := by
    intro h0
    have h1 : algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
        (FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) a = 0 := by
      rw [hu, h0, zero_mul]
    refine ha ?_
    have h2 : a = 0 :=
      IsFractionRing.injective (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
        (FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W))
        (h1.trans (map_zero _).symm)
    rw [h2]
    exact Ideal.zero_mem _
  refine ⟨⟨a, b, hb, hu.symm⟩, ⟨b, a, ha, ?_⟩⟩
  rw [inv_mul_eq_iff_eq_mul₀ hu0, hu]

/-- The "vertical half" of the crux hypothesis: a unit at the fibre prime `P` is a unit at every
prime contained in `P` (the localisation is smaller, so being a unit there is a *weaker*
condition). -/
theorem isUnitAt_of_le_chartFibrePrime
    [IsDomain (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)]
    (u : FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W))
    (q : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W))
    (hqP : q ≤ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (hP : Work.SpecLin.Alt.IsUnitAt u
      (Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)) :
    Work.SpecLin.Alt.IsUnitAt u q :=
  ⟨Work.SpecLin.Alt.InLocalization.mono hqP hP.1,
    Work.SpecLin.Alt.InLocalization.mono hqP hP.2⟩

end UnitAt

end Up
end Work.SpecLin.Alt

