/-
# Namespace mirror of `Work.SpecLin.Core.cruxUnitAtMaximal`

This file is an exact copy of `Submission/Work/SpecLin/Core/cruxUnitAtMaximal.lean` (module `Work.SpecLin.Core.cruxUnitAtMaximal`), changed in exactly three ways:

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
import Submission.Work.SpecLin.Up.Core.orderDataSectionEquation
import Submission.Work.SpecLin.Up.Setup.cruxChartPull
import Submission.Work.SpecLin.Up.Alt.exists_mem_sectionPrime_span_map_eq
import Submission.Work.SpecLin.Up.Alt.horizontalHht
import Submission.Work.SpecLin.Up.Alt.exists_chartTensorPoint
import Submission.Work.SpecLin.Up.Alt.chartReading
import Submission.Work.SpecLin.Setup.horizontal_of_height_one
import Submission.Work.SpecLin.Alt.conservationNumber
import Submission.Work.SpecLin.Up.Alt.chartTensorMap_isFractionRing
import Submission.Work.SpecLin.Up.Setup.localOrderData
import Submission.Work.SpecLin.Up.Alt.sectionPrime_le_iff_ptPlace_eq_alt
import Submission.Work.SpecLin.Up.Setup.localOrderHmiss

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.SpecLin.Core
namespace Up

/-- **The crux of the affine-chart proof, in the `IsUnitAt` form.**

`R` is a `K`-valuation ring, `W` a nonempty affine chart of the curve containing the images of
the `R`-points `s m`, `t m`, `B = Γ(C,W) ⊗_K R` the relative chart, `P = 𝔪_R·B` the fibre
prime, `N ⊇ P` maximal, and `h' ∈ K(C_F)^×` is a rational function presented in the chart as
`h' = φ_W(a)/φ_W(b)` with `a, b ∈ B ∖ P`, whose generic-fibre divisor is
`Σ_m [s_m^F] − Σ_m [t_m^F]`.

Then there exist local equations `f m ∈ I m` of the section ideals at `N`
(`I_m·B_N = (f m)·B_N`, with `f m ∉ P`) and `g m ∈ J m` similarly, and an element
`u = (a·∏ g_m)/(b·∏ f_m) ∈ Frac B` which is a **unit at `N`**.

Proof route (all pieces are sorry-free except `orderDataSectionEquation`, which is being proved
in parallel): take `f, g` from `Work.SpecLin.Alt.Up.exists_mem_sectionPrime_span_map_eq` and
`u := (a·∏g)/(b·∏f)`.  Apply `Work.SpecLin.Setup.Up.cruxChartPull` to `u`: its `hP` is
`Work.SpecLin.Alt.Up.isUnitAt_chartFibrePrime_of_map_mul_eq`, and its `hht` splits, for a
height-one prime `p ≤ N`, into the vertical case `p ≤ P` (`isUnitAt_of_le_chartFibrePrime`) and
the horizontal case, where `Work.SpecLin.Setup.horizontal_of_height_one` gives `p ∩ R = ⊥`,
`Work.SpecLin.Alt.Up.exists_chartTensorPoint` gives the place `Q` and the membership dictionary,
`Work.SpecLin.Alt.Up.ordAt_of_div_eq_sum_ptDiv` (with `sectionPrime_le_iff_ptPlace_eq_alt` for the
point dictionaries `hI`, `hJ`) gives `ord_Q h'`, and `Work.SpecLin.Core.Up.orderDataSectionEquation`
gives `ord_Q φ(f m) = [I_m ≤ p]` (resp. for `g m`); then
`Work.SpecLin.Alt.Up.inLocalization_horizontal_of_ord` gives `IsUnitAt u p` (transport the `∃ a b`
form along `chartTensorMap`, using that `φ_W(u) = h'·∏φg/∏φf`). -/
theorem cruxUnitAtMaximal {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    [IsDomain (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)]
    (s t : Fin n → Work.SpecLin.CurvePt C R)
    (hs : ∀ m, Set.range ((s m).left).base ⊆ (W : Set C.left))
    (ht : ∀ m, Set.range ((t m).left).base ⊆ (W : Set C.left))
    (a b : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
    (ha : a ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (hb : b ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)
    (h' : (C.baseChange (FractionRing R)).functionField) (hh' : h' ≠ 0)
    (hab : h' * Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW b
        = Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW a)
    (hdiv : (C.baseChange (FractionRing R)).div h'
      = (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (s m)))
        - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (t m))))
    (N : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) [N.IsMaximal]
    (hPN : Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W ≤ N) :
    ∃ (f g : Fin n → Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
      (u : FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)),
      (∀ m, f m ∈ Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
        (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m))) ∧
      (∀ m, g m ∈ Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
        (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m))) ∧
      (∀ m, f m ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W) ∧
      (∀ m, g m ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W) ∧
      (∀ m, (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
            (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m))).map
          (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
            (Localization.AtPrime N))
        = Ideal.span (singleton (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
            (Localization.AtPrime N) (f m)))) ∧
      (∀ m, (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
            (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m))).map
          (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
            (Localization.AtPrime N))
        = Ideal.span (singleton (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
            (Localization.AtPrime N) (g m)))) ∧
      u ≠ 0 ∧
      algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W))
          (a * ∏ m, g m)
        = u * algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W))
          (b * ∏ m, f m) ∧
      Work.SpecLin.Alt.IsUnitAt u N := by
  classical
  -- ## The fibre prime and the chart map
  haveI hPp : (Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W).IsPrime :=
    Work.SpecLin.Core.isPrime_chartFibrePrime (K := K) (C := C) R W hW
  set P : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W) :=
    Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W with hPdef
  have hPp' : P.IsPrime := by rw [hPdef]; exact hPp
  have hφinj : Function.Injective (Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW) := by
    letI : Algebra (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
        (C.baseChange (FractionRing R)).functionField :=
      (Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW).toAlgebra
    haveI : IsFractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
        (C.baseChange (FractionRing R)).functionField :=
      Work.SpecLin.Alt.Up.chartTensorMap_isFractionRing (K := K) (C := C) R W hW
    exact IsFractionRing.injective _ _
  -- ## Local equations of the section ideals at `N`
  have hfex : ∀ m : Fin n, ∃ f : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W,
      f ∈ Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
          (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m)) ∧
      f ∉ P ∧
      (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
          (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m))).map
        (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (Localization.AtPrime N))
        = Ideal.span (singleton (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
            (Localization.AtPrime N) f)) :=
    fun m => Work.SpecLin.Alt.Up.exists_mem_sectionPrime_span_map_eq (K := K) (C := C) R W hW
      (s m) (hs m) N hPN
  choose f hfmem hfPf hfmap using hfex
  have hgex : ∀ m : Fin n, ∃ g : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W,
      g ∈ Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
          (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m)) ∧
      g ∉ P ∧
      (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
          (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m))).map
        (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (Localization.AtPrime N))
        = Ideal.span (singleton (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
            (Localization.AtPrime N) g)) :=
    fun m => Work.SpecLin.Alt.Up.exists_mem_sectionPrime_span_map_eq (K := K) (C := C) R W hW
      (t m) (ht m) N hPN
  choose g hgmem hgPf hgmap using hgex
  -- ## Products of the local equations lie outside the fibre prime
  have hprodgP : (∏ m : Fin n, g m) ∉ P := by
    refine Finset.prod_induction g (fun x => x ∉ P) ?_ ?_ ?_
    · intro x y hx hy hxy
      rcases (Ideal.IsPrime.mul_mem_iff_mem_or_mem hPp').mp hxy with h | h
      · exact hx h
      · exact hy h
    · intro h; exact hPp'.ne_top (Ideal.eq_top_iff_one _ |>.mpr h)
    · intro m _; exact hgPf m
  have hprodfP : (∏ m : Fin n, f m) ∉ P := by
    refine Finset.prod_induction f (fun x => x ∉ P) ?_ ?_ ?_
    · intro x y hx hy hxy
      rcases (Ideal.IsPrime.mul_mem_iff_mem_or_mem hPp').mp hxy with h | h
      · exact hx h
      · exact hy h
    · intro h; exact hPp'.ne_top (Ideal.eq_top_iff_one _ |>.mpr h)
    · intro m _; exact hfPf m
  -- ## The correction element `u = (a·∏g)/(b·∏f)`
  set num : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W :=
    a * ∏ m : Fin n, g m with hnumdef
  set den : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W :=
    b * ∏ m : Fin n, f m with hdendef
  have hnumP : num ∉ P := by
    rw [hnumdef]
    intro h
    rcases (Ideal.IsPrime.mul_mem_iff_mem_or_mem hPp').mp h with h1 | h1
    · exact ha h1
    · exact hprodgP h1
  have hdenP : den ∉ P := by
    rw [hdendef]
    intro h
    rcases (Ideal.IsPrime.mul_mem_iff_mem_or_mem hPp').mp h with h1 | h1
    · exact hb h1
    · exact hprodfP h1
  have hnum0 : num ≠ 0 := fun h => hnumP (by rw [h]; exact Ideal.zero_mem P)
  have hden0 : den ≠ 0 := fun h => hdenP (by rw [h]; exact Ideal.zero_mem P)
  set u : FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W) :=
    algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
        (FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) num
      * (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
        (FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) den)⁻¹ with hUdef
  have hU : algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
      (FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) num
      = u * algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
          (FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) den := by
    rw [hUdef, mul_assoc, inv_mul_cancel₀, mul_one]
    intro h
    exact hden0 (IsFractionRing.injective _ _ (by rw [h, map_zero]))
  have hU0 : u ≠ 0 := by
    intro h0
    have h1 : algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
        (FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) num
        = (0 : FractionRing (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) := by
      rw [hU, h0, zero_mul]
    exact hnum0 (IsFractionRing.injective _ _ (by rw [h1, map_zero]))
  have hUP : Work.SpecLin.Alt.IsUnitAt u P :=
    Work.SpecLin.Alt.Up.isUnitAt_chartFibrePrime_of_map_mul_eq (K := K) (C := C) R W
      num den hnumP hdenP u hU
  -- ## `u` is a unit at every height-one prime `p ≤ N`
  have hht : ∀ p : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W),
      p.IsPrime → p.height = 1 → p ≤ N → Work.SpecLin.Alt.IsUnitAt u p := by
    intro p hp hp1 hpN
    by_cases hpP : p ≤ P
    · exact Work.SpecLin.Alt.Up.isUnitAt_of_le_chartFibrePrime (K := K) (C := C) R W u p hpP hUP
    · haveI hpI : p.IsPrime := hp
      have hmiss := Work.SpecLin.Setup.Up.localOrderHmiss (K := K) (C := C) R W hW p hp hp1 hpP
      obtain ⟨Q, hQmem, hQdict⟩ :=
        Work.SpecLin.Alt.Up.exists_chartTensorPoint (K := K) (C := C) R W hW p hp hp1 hmiss
      have hφb0 : Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW b ≠ 0 := by
        intro h
        have h0 : b = 0 := hφinj (by rw [h, map_zero])
        exact hb (by rw [h0]; exact Ideal.zero_mem P)
      have hφf0 : ∀ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m) ≠ 0 := by
        intro m h
        have h0 : f m = 0 := hφinj (by rw [h, map_zero])
        exact hfPf m (by rw [h0]; exact Ideal.zero_mem P)
      have hφg0 : ∀ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (g m) ≠ 0 := by
        intro m h
        have h0 : g m = 0 := hφinj (by rw [h, map_zero])
        exact hgPf m (by rw [h0]; exact Ideal.zero_mem P)
      have hPf0 : (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun m _ => hφf0 m)
      have hPg0 : (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (g m)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun m _ => hφg0 m)
      have hIp : ∀ m : Fin n, (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
            (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m)) ≤ p)
          ↔ Work.SpecLin.ptPlace (Work.SpecLin.RPt.map
              (IsScalarTower.toAlgHom K R (FractionRing R)) (s m)) = Q :=
        fun m => Work.SpecLin.Alt.Up.sectionPrime_le_iff_ptPlace_eq_alt (K := K) (C := C) R W hW
          (s m) (hs m) p hp hmiss Q hQmem hQdict
      have hJp : ∀ m : Fin n, (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
            (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m)) ≤ p)
          ↔ Work.SpecLin.ptPlace (Work.SpecLin.RPt.map
              (IsScalarTower.toAlgHom K R (FractionRing R)) (t m)) = Q :=
        fun m => Work.SpecLin.Alt.Up.sectionPrime_le_iff_ptPlace_eq_alt (K := K) (C := C) R W hW
          (t m) (ht m) p hp hmiss Q hQmem hQdict
      have hcount : (C.baseChange (FractionRing R)).ordAt h' Q
          = ((Finset.univ.filter (fun m : Fin n => Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
                (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m)) ≤ p)).card : ℤ)
            - ((Finset.univ.filter (fun m : Fin n => Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
                (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m)) ≤ p)).card : ℤ) :=
        Work.SpecLin.Alt.Up.ordAt_of_div_eq_sum_ptDiv (K := K) (C := C) R W hW s t hs ht Q p hQdict
          hIp hJp h' hdiv
      have hford : ∀ m : Fin n, (C.baseChange (FractionRing R)).ordAt
          (Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m)) Q
          = if (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
                (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m)) ≤ p)
              then 1 else 0 := by
        intro m
        have h := Work.SpecLin.Core.Up.orderDataSectionEquation (K := K) (C := C) R W hW
          (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m)) N hPN
          (f m) (hfPf m) (hfmap m) p hp hp1 hpN hmiss Q hQdict
        by_cases hm : Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
            (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m)) ≤ p
        · rw [if_pos hm]; exact h.1.mpr hm
        · rw [if_neg hm]; exact h.2.mpr hm
      have hgord : ∀ m : Fin n, (C.baseChange (FractionRing R)).ordAt
          (Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (g m)) Q
          = if (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
                (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m)) ≤ p)
              then 1 else 0 := by
        intro m
        have h := Work.SpecLin.Core.Up.orderDataSectionEquation (K := K) (C := C) R W hW
          (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m)) N hPN
          (g m) (hgPf m) (hgmap m) p hp hp1 hpN hmiss Q hQdict
        by_cases hm : Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
            (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m)) ≤ p
        · rw [if_pos hm]; exact h.1.mpr hm
        · rw [if_neg hm]; exact h.2.mpr hm
      -- ## The value of the chart map on `u`
      have hkey : Work.SpecLin.Setup.Up.chartTensorFracMap (K := K) (C := C) R W hW u
            * (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m))
          = h' * (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (g m)) := by
        rw [hUdef, map_mul, map_inv₀,
          Work.SpecLin.Setup.Up.chartTensorFracMap_algebraMap,
          Work.SpecLin.Setup.Up.chartTensorFracMap_algebraMap, hnumdef, hdendef,
          map_mul, map_mul, map_prod, map_prod, hab.symm, mul_inv_rev]
        have hinner : Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW b
            * ((∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m))⁻¹
              * (Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW b)⁻¹)
            * (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m)) = 1 := by
          rw [show Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW b
                * ((∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m))⁻¹
                  * (Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW b)⁻¹)
                * (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m))
              = (Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW b
                  * (Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW b)⁻¹)
                * ((∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m))⁻¹
                  * (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m)))
              from by ring]
          rw [mul_inv_cancel₀ hφb0, inv_mul_cancel₀ hPf0, mul_one]
        rw [show (h' * Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW b
              * (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (g m)))
              * ((∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m))⁻¹
                * (Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW b)⁻¹)
              * (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m))
            = h' * (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (g m))
              * (Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW b
                * ((∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m))⁻¹
                  * (Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW b)⁻¹)
                * (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m)))
              from by ring
          , hinner, mul_one]
      have hΦU : Work.SpecLin.Setup.Up.chartTensorFracMap (K := K) (C := C) R W hW u
          = h' * (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (g m))
            * (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m))⁻¹ := by
        apply mul_right_cancel₀ hPf0
        rw [hkey]
        rw [show h' * (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (g m))
              * (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m))⁻¹
              * (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m))
            = h' * (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (g m))
              * ((∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m))⁻¹
                * (∏ m : Fin n, Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m)))
              from by ring
          , inv_mul_cancel₀ hPf0, mul_one]
      have hcardI : (∑ m : Fin n, (if Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
              (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m)) ≤ p then (1 : ℤ) else 0))
          = ((Finset.univ.filter (fun m : Fin n => Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
              (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m)) ≤ p)).card : ℤ) := by
        rw [Finset.card_filter]; push_cast; rfl
      have hcardJ : (∑ m : Fin n, (if Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
              (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m)) ≤ p then (1 : ℤ) else 0))
          = ((Finset.univ.filter (fun m : Fin n => Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
              (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m)) ≤ p)).card : ℤ) := by
        rw [Finset.card_filter]; push_cast; rfl
      refine (Work.SpecLin.Setup.Up.isUnitAt_iff_ordAt_eq_zero (K := K) (C := C) R W hW p Q hQdict
        u hU0).mpr ?_
      rw [hΦU,
        Work.CurveBasics.Curve.ordAt_mul _ (mul_ne_zero hh' hPg0) (inv_ne_zero hPf0),
        Work.CurveBasics.Curve.ordAt_mul _ hh' hPg0,
        Work.CurveBasics.Curve.ordAt_inv _ hPf0,
        Work.SpecLin.Alt.Up.ordAt_prod (C.baseChange (FractionRing R))
          (fun m : Fin n => Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (f m))
          Finset.univ (fun m _ => hφf0 m) Q,
        Work.SpecLin.Alt.Up.ordAt_prod (C.baseChange (FractionRing R))
          (fun m : Fin n => Work.SpecLin.Alt.Up.chartTensorMap (K := K) (C := C) R W hW (g m))
          Finset.univ (fun m _ => hφg0 m) Q,
        Finset.sum_congr rfl (fun m _ => hgord m),
        Finset.sum_congr rfl (fun m _ => hford m),
        hcount, hcardI, hcardJ]
      ring
  -- ## The crux
  have hUN : Work.SpecLin.Alt.IsUnitAt u N :=
    Work.SpecLin.Setup.Up.cruxChartPull (K := K) (C := C) R W hW N ‹N.IsMaximal› hPN u hU0 hUP hht
  refine ⟨f, g, u, hfmem, hgmem, hfPf, hgPf, hfmap, hgmap, hU0, ?_, hUN⟩
  exact hU

end Up
end Work.SpecLin.Core

