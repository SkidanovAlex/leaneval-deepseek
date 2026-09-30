import Mathlib
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SpecLin.Core.linEquiv_of_sections_of_chart
import Submission.Work.SpecLin.Alt.chartMap
import Submission.Work.SpecLin.Alt.conservationNumber
import Submission.Work.SpecLin.Core.chartSpecialisation
import Submission.Work.CurveBasics.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace Work.SpecLin.Setup

/-! ## A change-of-chart computation for the relative chart ring

The two localisations `(B_W)_{P_W}` and `(B_V)_{P_V}` of the relative chart rings at the fibre
primes `P_W = 𝔪_R·B_W`, `P_V = 𝔪_R·B_V` are both the local ring `O_{X,ξ}` of the model
`X = C ×_K Spec R` at the generic point `ξ` of its special fibre, viewed as subrings of
`K(C_F)`.  The transfer of a presentation of a rational function from the chart `W` to the
chart `V` therefore reduces to the following elementary computation: *every element of the
relative chart ring `B_Z` of a chart `Z ⊆ V` is, inside `K(C_F)`, the quotient of two elements
of `B_V`, the denominator being a unit at `P_V*.

Concretely, the coordinate ring of `Z` is a localisation of `Γ(C,V)` (both are coordinate rings
of affine charts of the curve `C`), so every `a ∈ Γ(C,Z)` is `x/y` with `x, y ∈ Γ(C,V)`; since
`P_V ∩ (Γ(C,V) ⊗ 1) = 0` (an element of `Γ(C,V)` has nonzero reduction to the special fibre),
`y ⊗ 1` is a unit at `P_V`.  Applying this to the tensor factors of `c ∈ B_Z` and clearing
denominators gives `X, Y ∈ B_V` with `Y ∉ P_V` and `res X = c · res Y` in `B_Z`, where
`res = chartRestrict` is the restriction `B_V → B_Z`. -/

/-- **Clear denominators in the chart `Z ⊆ V`.**  Every element of the relative chart ring
`B_Z = Γ(C,Z) ⊗_K R` of a nonempty affine chart `Z` contained in the nonempty affine chart `V`
is `X/Y` with `X, Y ∈ B_V = Γ(C,V) ⊗_K R` and `Y` a unit at the fibre prime `P_V`.  More
precisely, the restriction `res : B_V → B_Z = B_V ⊗_{Γ(C,V)} Γ(C,Z)` maps `X` to `c · res Y`. -/
private theorem chartRestrict_fraction {K : Type u} [Field K]
    {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (Z V : C.left.Opens) (hV : IsAffineOpen V) (hZV : Z ≤ V)
    [Nonempty Z] [Nonempty V] (c : Work.SpecLin.Core.chartTensor R Z) :
    ∃ X Y : Work.SpecLin.Core.chartTensor R V,
      Y ∉ Work.SpecLin.Core.chartFibrePrime R V ∧
      Work.SpecLin.Core.chartRestrict R hZV X = c * Work.SpecLin.Core.chartRestrict R hZV Y := by
  classical
  -- `K(C)` is the fraction field of the chart `V`, and `P_V` is prime.
  have hfr : IsFractionRing Γ(C.left, V) C.functionField :=
    Work.SpecLin.Alt.isFractionRing_functionField V hV
  haveI := hfr
  have hP : (Work.SpecLin.Core.chartFibrePrime R V).IsPrime :=
    Work.SpecLin.Core.isPrime_chartFibrePrime R V hV
  haveI := hP
  -- A pure tensor: write the coordinate ring element as a fraction of `Γ(C,V)`.
  have key : ∀ (a : Γ(C.left, Z)) (r : R),
      ∃ X Y : Work.SpecLin.Core.chartTensor R V,
        Y ∉ Work.SpecLin.Core.chartFibrePrime R V ∧
        Work.SpecLin.Core.chartRestrict R hZV X =
          (a ⊗ₜ[K] r) * Work.SpecLin.Core.chartRestrict R hZV Y := by
    intro a r
    obtain ⟨⟨x, y⟩, hy⟩ := IsLocalization.surj (nonZeroDivisors Γ(C.left, V))
      ((C.germToFunctionField Z).hom a)
    have hyne : (y : Γ(C.left, V)) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp y.2
    -- the identity `a * y = x` in `Γ(C,Z)`, transport of the fraction expression along `germ`
    have hkey : a * Work.SpecLin.Core.chartResAlgHom (K := K) (C := C) hZV
          (y : Γ(C.left, V)) = Work.SpecLin.Core.chartResAlgHom (K := K) (C := C) hZV x := by
      refine (Scheme.germToFunctionField_injective (X := C.left) Z) ?_
      show (C.germToFunctionField Z).hom
          (a * Work.SpecLin.Core.chartResAlgHom (K := K) (C := C) hZV (y : Γ(C.left, V)))
        = (C.germToFunctionField Z).hom
            (Work.SpecLin.Core.chartResAlgHom (K := K) (C := C) hZV x)
      rw [map_mul, Work.SpecLin.Core.germToFunctionField_restrict hZV,
        Work.SpecLin.Core.germToFunctionField_restrict hZV]
      exact hy
    refine ⟨x ⊗ₜ[K] r, (y : Γ(C.left, V)) ⊗ₜ[K] (1 : R), ?_, ?_⟩
    · -- `y ⊗ 1` has nonzero reduction to the special fibre, so it is a unit at `P_V`
      rw [← Work.SpecLin.Core.chartTensorRedMap_eq_zero_iff R V hV,
        Work.SpecLin.Alt.chartTensorRedMap_tmul_one]
      intro h0
      refine hyne ((Scheme.germToFunctionField_injective (X := C.left) V) ?_)
      rw [map_zero]
      exact Work.CurveBasics.Curve.functionFieldMap_injective C (IsLocalRing.ResidueField R)
        (by simpa using h0)
    · -- and the restriction of `x ⊗ r` is `(a ⊗ r) · res (y ⊗ 1)`
      show Work.SpecLin.Core.chartRestrict R hZV (x ⊗ₜ[K] r)
        = (a ⊗ₜ[K] r) * Work.SpecLin.Core.chartRestrict R hZV
            ((y : Γ(C.left, V)) ⊗ₜ[K] (1 : R))
      rw [show Work.SpecLin.Core.chartRestrict R hZV (x ⊗ₜ[K] r)
            = Work.SpecLin.Core.chartResAlgHom (K := K) (C := C) hZV x ⊗ₜ[K] r from rfl,
          show Work.SpecLin.Core.chartRestrict R hZV ((y : Γ(C.left, V)) ⊗ₜ[K] (1 : R))
            = Work.SpecLin.Core.chartResAlgHom (K := K) (C := C) hZV (y : Γ(C.left, V))
                ⊗ₜ[K] (1 : R) from rfl,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, hkey]
  -- the general element is a sum of pure tensors; clear denominators term by term
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

/-- **A chart-W presentation of a rational function transfers to any other affine chart.**

`h ∈ K(C_F)^×` is presented in the chart `W` as `h = φ_W(a)/φ_W(b)` with `a, b ∉ P_W`, where
`φ_W = chartTensorMap R W hW` and `P_W = chartFibrePrime R W = 𝔪_R·(Γ(C,W) ⊗[K] R)`.
Then `h` has a presentation in any other nonempty affine chart `V` as
`h = φ_V(a')/φ_V(b')` with `a', b' ∉ P_V`.

The two localisations `(B_W)_{P_W}` and `(B_V)_{P_V}` are both the local ring `O_{X,ξ}` of the
model `X = C ×_K Spec R` at the generic point `ξ` of its special fibre, viewed as subrings of
`K(C_F) = K(X)`, so being a unit at `P_W` is the same as being a unit at `P_V`.  Concretely,
restrict along `W ∩ V ⊆ W` (the intersection of two affine opens of a separated scheme is
affine) and use the compatibility `chartTensorMap_restrict`
(`Work.SpecLin.Core.chartTensorMap_restrict`, `SpecLin/Core/chartSpecialisation`) to obtain
`h · φ_Z(res b) = φ_Z(res a)` with `res a, res b ∈ B_Z ∖ P_Z` for `Z = W ∩ V`; then write the
localisation `B_Z = B_V[1/g]` (`g` cutting out `V ∖ Z` inside `V`, with `g ∉ P_V` because `ξ`
lies in the nonempty `Z_κ`) and clear denominators to get `a', b' ∈ B_V`, both `∉ P_V`. -/
theorem exists_representation_of_other_chart {K : Type u} [Field K]
    {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W V : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W)
    (hV : AlgebraicGeometry.IsAffineOpen V) [Nonempty W] [Nonempty V]
    [IsDomain (Work.SpecLin.Core.chartTensor R W)]
    [IsDomain (Work.SpecLin.Core.chartTensor R V)]
    (a b : Work.SpecLin.Core.chartTensor R W)
    (ha : a ∉ Work.SpecLin.Core.chartFibrePrime R W)
    (hb : b ∉ Work.SpecLin.Core.chartFibrePrime R W)
    (h : (C.baseChange (FractionRing R)).functionField) (hh : h ≠ 0)
    (hab : h * Work.SpecLin.Alt.chartTensorMap R W hW b
        = Work.SpecLin.Alt.chartTensorMap R W hW a) :
    ∃ a' b' : Work.SpecLin.Core.chartTensor R V,
      a' ∉ Work.SpecLin.Core.chartFibrePrime R V ∧
      b' ∉ Work.SpecLin.Core.chartFibrePrime R V ∧
      h * Work.SpecLin.Alt.chartTensorMap R V hV b'
        = Work.SpecLin.Alt.chartTensorMap R V hV a' := by
  classical
  -- ### Step 0: an affine chart `Z ⊆ W ∩ V`, containing the generic point
  obtain ⟨w, hw⟩ := ‹Nonempty W›
  obtain ⟨v, hv⟩ := ‹Nonempty V›
  have hηW : genericPoint C.left ∈ (W : Set C.left) :=
    (genericPoint_spec C.left).mem_open_set_iff W.isOpen |>.mpr ⟨w, trivial, hw⟩
  have hηV : genericPoint C.left ∈ (V : Set C.left) :=
    (genericPoint_spec C.left).mem_open_set_iff V.isOpen |>.mpr ⟨v, trivial, hv⟩
  have hη : genericPoint C.left ∈ (W ⊓ V : C.left.Opens) := ⟨hηW, hηV⟩
  obtain ⟨Z, hZaff, hZmem, hZsub⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hη
  have hZW : Z ≤ W := fun x hx => (hZsub hx).1
  have hZV : Z ≤ V := fun x hx => (hZsub hx).2
  haveI : Nonempty Z := ⟨⟨genericPoint C.left, hZmem⟩⟩
  -- ### Step 1: restrict the presentation to `Z`
  set aZ : Work.SpecLin.Core.chartTensor R Z := Work.SpecLin.Core.chartRestrict R hZW a with haZ
  set bZ : Work.SpecLin.Core.chartTensor R Z := Work.SpecLin.Core.chartRestrict R hZW b with hbZ
  have hφa : Work.SpecLin.Alt.chartTensorMap R Z hZaff aZ
      = Work.SpecLin.Alt.chartTensorMap R W hW a :=
    Work.SpecLin.Core.chartTensorMap_restrict R hZW hZaff hW a
  have hφb : Work.SpecLin.Alt.chartTensorMap R Z hZaff bZ
      = Work.SpecLin.Alt.chartTensorMap R W hW b :=
    Work.SpecLin.Core.chartTensorMap_restrict R hZW hZaff hW b
  have hreda : Work.SpecLin.Alt.chartTensorRedMap R Z hZaff aZ ≠ 0 := by
    rw [haZ, Work.SpecLin.Core.chartTensorRedMap_restrict R hZW hZaff hW a]
    exact fun h0 => ha ((Work.SpecLin.Core.chartTensorRedMap_eq_zero_iff R W hW a).mp h0)
  have hredb : Work.SpecLin.Alt.chartTensorRedMap R Z hZaff bZ ≠ 0 := by
    rw [hbZ, Work.SpecLin.Core.chartTensorRedMap_restrict R hZW hZaff hW b]
    exact fun h0 => hb ((Work.SpecLin.Core.chartTensorRedMap_eq_zero_iff R W hW b).mp h0)
  -- ### Step 2: clear denominators in the chart `V`
  obtain ⟨XA, YA, hYA, hArec⟩ := chartRestrict_fraction R Z V hV hZV aZ
  obtain ⟨XB, YB, hYB, hBrec⟩ := chartRestrict_fraction R Z V hV hZV bZ
  -- the same identities after applying `φ_Z : B_Z → K(C_F)`
  have hφXA : Work.SpecLin.Alt.chartTensorMap R V hV XA
      = Work.SpecLin.Alt.chartTensorMap R Z hZaff aZ
        * Work.SpecLin.Alt.chartTensorMap R V hV YA := by
    rw [← Work.SpecLin.Core.chartTensorMap_restrict R hZV hZaff hV XA, hArec, map_mul,
      Work.SpecLin.Core.chartTensorMap_restrict R hZV hZaff hV YA]
  have hφXB : Work.SpecLin.Alt.chartTensorMap R V hV XB
      = Work.SpecLin.Alt.chartTensorMap R Z hZaff bZ
        * Work.SpecLin.Alt.chartTensorMap R V hV YB := by
    rw [← Work.SpecLin.Core.chartTensorMap_restrict R hZV hZaff hV XB, hBrec, map_mul,
      Work.SpecLin.Core.chartTensorMap_restrict R hZV hZaff hV YB]
  -- ### Step 3: the numerators are also units at `P_V`
  have hXA : XA ∉ Work.SpecLin.Core.chartFibrePrime R V := by
    rw [← Work.SpecLin.Core.chartTensorRedMap_eq_zero_iff R V hV]
    intro h0
    have h1 : Work.SpecLin.Alt.chartTensorRedMap R Z hZaff
        (Work.SpecLin.Core.chartRestrict R hZV XA) = 0 := by
      rw [Work.SpecLin.Core.chartTensorRedMap_restrict R hZV hZaff hV XA]; exact h0
    rw [hArec, map_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hreda h2
    · have h3 : Work.SpecLin.Alt.chartTensorRedMap R V hV YA = 0 := by
        rw [← Work.SpecLin.Core.chartTensorRedMap_restrict R hZV hZaff hV YA]; exact h2
      exact hYA ((Work.SpecLin.Core.chartTensorRedMap_eq_zero_iff R V hV YA).mp h3)
  have hXB : XB ∉ Work.SpecLin.Core.chartFibrePrime R V := by
    rw [← Work.SpecLin.Core.chartTensorRedMap_eq_zero_iff R V hV]
    intro h0
    have h1 : Work.SpecLin.Alt.chartTensorRedMap R Z hZaff
        (Work.SpecLin.Core.chartRestrict R hZV XB) = 0 := by
      rw [Work.SpecLin.Core.chartTensorRedMap_restrict R hZV hZaff hV XB]; exact h0
    rw [hBrec, map_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hredb h2
    · have h3 : Work.SpecLin.Alt.chartTensorRedMap R V hV YB = 0 := by
        rw [← Work.SpecLin.Core.chartTensorRedMap_restrict R hZV hZaff hV YB]; exact h2
      exact hYB ((Work.SpecLin.Core.chartTensorRedMap_eq_zero_iff R V hV YB).mp h3)
  -- ### Step 4: assemble the presentation in the chart `V`
  have hP : (Work.SpecLin.Core.chartFibrePrime R V).IsPrime :=
    Work.SpecLin.Core.isPrime_chartFibrePrime R V hV
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
    have keyeq : h * Work.SpecLin.Alt.chartTensorMap R V hV XB
        * Work.SpecLin.Alt.chartTensorMap R V hV YA
        = Work.SpecLin.Alt.chartTensorMap R V hV XA
          * Work.SpecLin.Alt.chartTensorMap R V hV YB := by
      rw [hφXB, hφXA, hφb, hφa]
      calc h * (Work.SpecLin.Alt.chartTensorMap R W hW b
            * Work.SpecLin.Alt.chartTensorMap R V hV YB)
            * Work.SpecLin.Alt.chartTensorMap R V hV YA
          = (h * Work.SpecLin.Alt.chartTensorMap R W hW b)
            * (Work.SpecLin.Alt.chartTensorMap R V hV YB
              * Work.SpecLin.Alt.chartTensorMap R V hV YA) := by ring
        _ = Work.SpecLin.Alt.chartTensorMap R W hW a
            * (Work.SpecLin.Alt.chartTensorMap R V hV YB
              * Work.SpecLin.Alt.chartTensorMap R V hV YA) := by rw [hab]
        _ = Work.SpecLin.Alt.chartTensorMap R W hW a
            * Work.SpecLin.Alt.chartTensorMap R V hV YA
            * Work.SpecLin.Alt.chartTensorMap R V hV YB := by ring
    rw [← mul_assoc, keyeq]

end Work.SpecLin.Setup
