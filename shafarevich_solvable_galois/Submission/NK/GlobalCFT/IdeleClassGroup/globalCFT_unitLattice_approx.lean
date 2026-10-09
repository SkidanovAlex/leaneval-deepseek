/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bounded approximation by the logarithmic embedding of the units

Let `K` be a number field and `logEmbedding K : Additive (𝓞 K)ˣ →+ logSpace K` the logarithmic
embedding of the units, `logEmbedding K u w = mult w * log (w u)`, into the space
`logSpace K = {w : InfinitePlace K // w ≠ w₀} → ℝ`.  By Dirichlet's unit theorem the image
`unitLattice K` of `logEmbedding` is a full `ℤ`-lattice in `logSpace K`; consequently the quotient
of `logSpace K` by this lattice is compact, i.e. every vector is within a bounded distance of a
lattice point.  This file makes that effective: there is a constant `R ≥ 0`, depending only on `K`,
such that for every `x : logSpace K` one finds a unit `u` whose logarithmic embedding differs from
`x` by at most `R` in every coordinate.

The main result of the file removes the distinguished place `w₀`: the logarithmic embedding of a
unit also has sum `0` over *all* infinite places (`NumberField.InfinitePlace.sum_mult_mul_log`), so
control at the places different from `w₀` controls the remaining one as well.
-/

namespace NK.GlobalCFT.IdeleClassGroup

open scoped Classical
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem Module

/-- **Bounded approximation in the log-space.**  For a number field `K` there is a constant
`R ≥ 0` such that every `x` in `logSpace K = {w : InfinitePlace K // w ≠ w₀} → ℝ` is within
distance `R` (in every coordinate) of the logarithmic embedding of a unit.

The proof uses the fact that `unitLattice K` is a full `ℤ`-lattice: taking the basis
`B = (basisUnitLattice K).ofZLatticeBasis ℝ` of `logSpace K` whose `ℤ`-span is exactly
`unitLattice K`, the element `ZSpan.floor B x` is a lattice point, hence the logarithmic embedding
of a unit `u`, and the remainder `ZSpan.fract B x = x - logEmbedding u` has fundamental-domain
coordinates in `[0,1)`, which bounds its coordinates by `∑ i, ‖B i‖`. -/
private lemma unitLattice_approx_logSpace (K : Type*) [Field K] [NumberField K] :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : logSpace K, ∃ u : (𝓞 K)ˣ,
      ∀ w : {w : InfinitePlace K // w ≠ w₀}, |x w - logEmbedding K (Additive.ofMul u) w| ≤ R := by
  classical
  let B : Basis (Fin (NumberField.Units.rank K)) ℝ (logSpace K) :=
    (basisUnitLattice K).ofZLatticeBasis ℝ
  refine ⟨∑ i, ‖B i‖, Finset.sum_nonneg (fun i _ => norm_nonneg _), ?_⟩
  intro x
  have hspan : Submodule.span ℤ (Set.range B) = unitLattice K :=
    Module.Basis.ofZLatticeBasis_span ℝ (unitLattice K) (basisUnitLattice K)
  have hmem : (ZSpan.floor B x : logSpace K) ∈ unitLattice K := by
    rw [← hspan]; exact (ZSpan.floor B x).property
  obtain ⟨a, -, ha⟩ := (Submodule.mem_map.mp hmem)
  refine ⟨Additive.toMul a, ?_⟩
  have hu : logEmbedding K (Additive.ofMul (Additive.toMul a)) = (ZSpan.floor B x : logSpace K) :=
    ha
  have hbound : ∀ v : {w : InfinitePlace K // w ≠ w₀}, |(ZSpan.fract B x) v| ≤ ∑ i, ‖B i‖ := by
    intro v
    have hsum : (ZSpan.fract B x) v = ∑ i, (B.repr (ZSpan.fract B x) i) * (B i v) := by
      nth_rewrite 1 [← B.sum_repr (ZSpan.fract B x)]
      simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum]
    calc |∑ i, (B.repr (ZSpan.fract B x) i) * (B i v)|
        ≤ ∑ i, |(B.repr (ZSpan.fract B x) i) * (B i v)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |(B.repr (ZSpan.fract B x) i)| * |(B i v)| := by simp [abs_mul]
      _ ≤ ∑ i, 1 * ‖B i‖ := Finset.sum_le_sum (fun i _ => by
            refine mul_le_mul ?_ ?_ (abs_nonneg _) (by norm_num)
            · rw [ZSpan.repr_fract_apply, abs_of_nonneg (Int.fract_nonneg ((B.repr x) i))]
              linarith [Int.fract_lt_one ((B.repr x) i)]
            · simpa [Real.norm_eq_abs] using norm_le_pi_norm (B i) v)
      _ = ∑ i, ‖B i‖ := by simp
  intro w
  have hxz : x - logEmbedding K (Additive.ofMul (Additive.toMul a)) = ZSpan.fract B x := by
    rw [hu, ZSpan.fract_apply]
  rw [← Pi.sub_apply, hxz]
  exact hbound w

theorem globalCFT_unitLattice_approx {K : Type*} [Field K] [NumberField K] :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ b : NumberField.InfinitePlace K → ℝ,
      (∑ w : NumberField.InfinitePlace K, b w = 0) →
      ∃ u : (NumberField.RingOfIntegers K)ˣ,
        ∀ w : NumberField.InfinitePlace K,
          |b w - (w.mult : ℝ) * Real.log (w (algebraMap (NumberField.RingOfIntegers K) K ↑u))| ≤ R := by
  classical
  obtain ⟨R₀, hR₀, hcore⟩ := unitLattice_approx_logSpace K
  refine ⟨(Fintype.card (NumberField.InfinitePlace K) : ℝ) * R₀,
    mul_nonneg (Nat.cast_nonneg _) hR₀, ?_⟩
  intro b hb
  obtain ⟨u, hu⟩ := hcore (fun v : {w : InfinitePlace K // w ≠ w₀} => b v.val)
  have hcard_pos : (1 : ℝ) ≤ (Fintype.card (NumberField.InfinitePlace K) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := NumberField.InfinitePlace K)
  have hle : R₀ ≤ (Fintype.card (NumberField.InfinitePlace K) : ℝ) * R₀ := by
    nth_rewrite 1 [← one_mul R₀]
    exact mul_le_mul_of_nonneg_right hcard_pos hR₀
  refine ⟨u, ?_⟩
  intro w
  by_cases hw : w = w₀
  · subst hw
    have hbsum : b w₀ = - ∑ v : {w : InfinitePlace K // w ≠ w₀}, b v.val := by
      have h := hb
      rw [Fintype.sum_eq_add_sum_subtype_ne b w₀] at h
      linarith
    have husum : ((w₀ : InfinitePlace K).mult : ℝ) * Real.log (w₀ (algebraMap (𝓞 K) K ↑u)) =
        - ∑ v : {w : InfinitePlace K // w ≠ w₀}, logEmbedding K (Additive.ofMul u) v := by
      have h := NumberField.Units.dirichletUnitTheorem.sum_logEmbedding_component (K := K) u
      linarith
    have hkey : b w₀ - ((w₀ : InfinitePlace K).mult : ℝ) *
          Real.log (w₀ (algebraMap (𝓞 K) K ↑u)) =
        - ∑ v : {w : InfinitePlace K // w ≠ w₀},
            (b v.val - logEmbedding K (Additive.ofMul u) v) := by
      rw [hbsum, husum, Finset.sum_sub_distrib]
      ring
    rw [hkey]
    refine le_trans (le_of_eq (abs_neg _)) ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have h1 : (∑ v : {w : InfinitePlace K // w ≠ w₀},
          |b v.val - logEmbedding K (Additive.ofMul u) v|) ≤
        (Fintype.card {w : InfinitePlace K // w ≠ w₀} : ℝ) * R₀ := by
      refine le_trans (Finset.sum_le_sum (fun v _ => hu v)) ?_
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    refine le_trans h1 ?_
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast Fintype.card_subtype_le (fun w : InfinitePlace K => w ≠ w₀)) hR₀
  · have hcomp : logEmbedding K (Additive.ofMul u) ⟨w, hw⟩ =
        (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 K) K ↑u)) :=
      NumberField.Units.dirichletUnitTheorem.logEmbedding_component u ⟨w, hw⟩
    rw [← hcomp]
    exact le_trans (hu ⟨w, hw⟩) hle

end NK.GlobalCFT.IdeleClassGroup
