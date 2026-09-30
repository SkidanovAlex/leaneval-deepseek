import Mathlib
import Submission.Work.GCBasics.DivApi
import Submission.Work.CurveBasics.Linear.finiteDimensional_L

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# `ℓ(D) = 1` for an effective divisor, in terms of linear equivalence

For an effective divisor `D` on `C_F` (a curve over a field, base changed to a field
extension `F/K`) the following two conditions are equivalent:

* `ℓ(D) = 1`, i.e. the Riemann–Roch space `L(D)` is one dimensional;
* `D` is the only **effective** divisor linearly equivalent to `D`.

The proof rests on the observation that, for an effective `D`, the constants form a
one-dimensional subspace of `L(D)`.  Hence `ℓ(D) = 1` if and only if `L(D)` *is* the line of
constants (`L_eq_span_one_of_l_eq_one` below); here the hypothesis `ℓ(0) = 1` is used to
identify `L(0)` with the line of constants, i.e. that a rational function with `div h ≥ 0`
is constant.

Given that, both directions are immediate.

* If `ℓ(D) = 1`, `D'` is effective and `h ≠ 0` has `div h = D - D'`, then
  `div h⁻¹ + D = D' ≥ 0`, so `h⁻¹ ∈ L(D)` is constant; hence `div h⁻¹ = 0`, that is
  `D' - D = 0`.
* Conversely, if `ℓ(D) ≠ 1` then `ℓ(D) ≥ 2`, so `L(D) ⊋ F·1`.  Choose `g ∈ L(D)` outside the
  line of constants; then `div g ≠ 0` (otherwise `g ∈ L(0) = F·1`), and
  `D' := D + div g` is effective, linearly equivalent to `D` (with witness `g⁻¹`) and
  different from `D`.
-/

namespace Work.GCBasics

open Work.CurveBasics

/-- If `D` is effective and `L(D)` is one dimensional, then `L(D)` is the line of constants.

The constants lie in `L(D)` (`Curve.algebraMap_mem_L`) and span a one-dimensional subspace,
so the claim is a comparison of finrank inside the finite dimensional module `↥(L D)`
(`Work.CurveBasics.Linear.finiteDimensional_L`). -/
theorem L_eq_span_one_of_l_eq_one {k : Type*} [Field k] (X : Curve k) {D : X.Div}
    (hD : D.IsEffective) (h : X.l D = 1) :
    X.L D = Submodule.span k ({1} : Set X.functionField) := by
  have hI : FiniteDimensional k ↥(X.L D) := Work.CurveBasics.Linear.finiteDimensional_L X D
  have hle : Submodule.span k ({1} : Set X.functionField) ≤ X.L D := by
    rw [Submodule.span_le]
    rintro x (rfl : x = 1)
    have h := X.algebraMap_mem_L (D := D) hD (1 : k)
    rw [map_one] at h
    simpa using h
  have hfin : Module.finrank k ↥(Submodule.span k ({1} : Set X.functionField)) = 1 :=
    finrank_span_singleton (one_ne_zero)
  have h2 : Module.finrank k ↥(X.L D) = 1 := h
  rw [Submodule.eq_of_le_of_finrank_eq (K := k) hle (by rw [hfin, h2])]

theorem ell_eq_one_iff {K : Type _} [Field K] {C : Work.CurveBasics.Curve K} {F : Type _}
    [Field F] [Algebra K F] {D : Work.GCBasics.Dv C F}
    (hD : Work.CurveBasics.Curve.Div.IsEffective D)
    (h0 : Work.GCBasics.ell C (0 : Work.GCBasics.Dv C F) = 1) :
    Work.GCBasics.ell C D = 1 ↔
      ∀ D' : Work.GCBasics.Dv C F, Work.CurveBasics.Curve.Div.IsEffective D' →
        Work.GCBasics.LinEquiv C D D' → D = D' := by
  -- Work on the base changed curve, over which `ell`, `div` and `LinEquiv` are the ones
  -- of `Work.CurveBasics`.
  set X : Curve F := Curve.baseChange C F with hX
  have hzero : X.L (0 : X.Div) = Submodule.span F ({1} : Set X.functionField) :=
    L_eq_span_one_of_l_eq_one X (Curve.Div.isEffective_zero) (h := h0)
  constructor
  · -- `ℓ(D) = 1`: the only effective divisor linearly equivalent to `D` is `D` itself.
    intro h D' hD' he
    obtain ⟨g, hg, hdiv⟩ := he
    have hL : X.L D = Submodule.span F ({1} : Set X.functionField) :=
      L_eq_span_one_of_l_eq_one X hD h
    -- `g⁻¹ ∈ L D` because `div g⁻¹ + D = D' ≥ 0`.
    have hmem : g⁻¹ ∈ X.L D := by
      rw [Curve.mem_L_iff]
      right
      have hginv : X.div g⁻¹ = -(D - D') := by
        rw [Work.CurveBasics.Order.div_inv X hg, hdiv]
      rw [hginv]
      have : -(D - D') + D = D' := by abel
      rw [this]
      exact hD'
    -- Hence `g⁻¹` is a constant, and therefore has zero divisor.
    rw [hL, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hgc : g⁻¹ = algebraMap F X.functionField c := by
      rw [Algebra.smul_def, mul_one] at hc
      exact hc.symm
    have hzero' : X.div g⁻¹ = 0 := by
      rw [hgc]
      exact Work.CurveBasics.Order.div_algebraMap_eq_zero X c
    have h4 : X.div g⁻¹ = -(D - D') := by
      rw [Work.CurveBasics.Order.div_inv X hg, hdiv]
    rw [h4] at hzero'
    exact sub_eq_zero.mp (neg_eq_zero.mp hzero')
  · -- Conversely, if every effective divisor linearly equivalent to `D` is `D`, then `ℓ(D) = 1`.
    intro hUP
    -- The line of constants sits inside `L D`, so `1 ≤ ℓ(D)`.
    have hmem1 : (1 : X.functionField) ∈ X.L D := by
      have h := X.algebraMap_mem_L (D := D) hD (1 : F)
      rw [map_one] at h
      simpa using h
    have hspan_le : Submodule.span F ({1} : Set X.functionField) ≤ X.L D := by
      rw [Submodule.span_le]
      rintro x (rfl : x = 1)
      exact hmem1
    have hI : FiniteDimensional F ↥(X.L D) := Work.CurveBasics.Linear.finiteDimensional_L X D
    have h1 : 1 ≤ X.l D := by
      have hmono := Submodule.finrank_mono hspan_le
      rw [finrank_span_singleton one_ne_zero] at hmono
      exact hmono
    -- It remains to show `ℓ(D) ≤ 1`: otherwise `L D` strictly contains the line of constants
    -- and any element `g` of `L D` outside it gives a new effective divisor `D + div g ~ D`.
    have hlD : X.l D ≤ 1 := by
      by_contra hne
      have h2 : 2 ≤ X.l D := by omega
      have hnle : ¬ (X.L D ≤ Submodule.span F ({1} : Set X.functionField)) := by
        intro hle'
        have heq : X.L D = Submodule.span F ({1} : Set X.functionField) :=
          le_antisymm hle' hspan_le
        have hcon : X.l D = 1 := by
          have hfin' : Module.finrank F ↥(X.L D) = 1 := by
            rw [heq]
            exact finrank_span_singleton one_ne_zero
          exact hfin'
        omega
      obtain ⟨g, hgL, hgs⟩ := Set.not_subset.mp hnle
      have hgne : g ≠ 0 := fun hg0 => hgs (hg0 ▸ Submodule.zero_mem _)
      -- `div g ≠ 0`, since `div g = 0` would put `g` in `L(0) = F·1`.
      have hdivne : X.div g ≠ 0 := by
        intro hd0
        have hmem0 : g ∈ X.L 0 := by
          rw [Curve.mem_L_iff]
          right
          rw [hd0]
          exact Curve.Div.isEffective_zero
        rw [hzero] at hmem0
        exact hgs hmem0
      have heff : (X.div g + D).IsEffective :=
        (Curve.mem_L_iff X).mp hgL |>.resolve_left hgne
      have heq : LinEquiv C D (X.div g + D) := by
        refine ⟨g⁻¹, inv_ne_zero hgne, ?_⟩
        rw [Work.CurveBasics.Order.div_inv X hgne]
        show -X.div g = D - (X.div g + D)
        abel
      have hne' : X.div g + D ≠ D := by
        intro hc
        refine hdivne ?_
        have hh : (X.div g + D) - D = 0 := by rw [hc, sub_self]
        rwa [add_sub_cancel_right] at hh
      exact hne' (hUP (X.div g + D) heff heq).symm
    exact le_antisymm hlD h1

end Work.GCBasics
