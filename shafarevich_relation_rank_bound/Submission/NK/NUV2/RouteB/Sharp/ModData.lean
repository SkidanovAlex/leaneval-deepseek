/-
# Modulus data and congruence subgroups of the idèle group (local copy)

This module defines, for a number field `K`, the congruence subgroup `U(𝔪) ≤ 𝕀 K` attached to
*modulus data* `𝔪` (a finitely supported exponent function at the finite places together with a
set of real places at which positivity is imposed).  It is a local copy of the corresponding
definitions of `Submission.NK.NUV2.RouteB.RayModulus.Defs`, kept here so that the development of
the ray-class counting theorem does not depend on that file.
-/
import Mathlib
import Submission.NK.HeckeL.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.NUV2.RouteB.Sharp

variable (K : Type) [Field K] [NumberField K]

/-- A modulo function on the primes of `𝓞 K` has **finite support**. -/
def HasFiniteSupport (m : HeightOneSpectrum (RingOfIntegers K) → ℕ) : Prop :=
  ∀ᶠ q in Filter.cofinite, m q = 0

/-- A local unit `x` of the completion `K_𝔮` is `1` modulo the `n`-th power of the maximal
ideal. -/
def IsCongAt (m : HeightOneSpectrum (RingOfIntegers K) → ℕ)
    (q : HeightOneSpectrum (RingOfIntegers K)) (x : (q.adicCompletion K)ˣ) : Prop :=
  Valued.v ((x : q.adicCompletion K) - 1) ≤ WithZero.exp (-(m q : ℤ))

/-- **A modulus**: finitely many congruence conditions at the finite places, and positivity at
the archimedean places in `pos`. -/
structure Modulus (K : Type) [Field K] [NumberField K] where
  /-- the exponents of the modulus at the finite places -/
  exps : HeightOneSpectrum (RingOfIntegers K) → ℕ
  /-- the modulus has finite support -/
  finite_support : HasFiniteSupport K exps
  /-- the archimedean places at which positivity is imposed -/
  pos : Set (InfinitePlace K)

namespace Modulus

variable {K}

/-- The finite primes carrying a non-trivial congruence condition. -/
def support (𝔪 : Modulus K) : Set (HeightOneSpectrum (RingOfIntegers K)) :=
  {q | 𝔪.exps q ≠ 0}

/-- The finite primes carrying a non-trivial congruence condition, as a finite set. -/
noncomputable def supportFinset (𝔪 : Modulus K) : Finset (HeightOneSpectrum (RingOfIntegers K)) :=
  (Filter.eventually_cofinite.mp 𝔪.finite_support).toFinset

theorem mem_supportFinset (𝔪 : Modulus K) {q} (hq : 𝔪.exps q ≠ 0) : q ∈ 𝔪.supportFinset := by
  classical
  rw [supportFinset, Set.Finite.mem_toFinset]
  exact fun h => hq h

theorem exps_eq_zero_of_not_mem (𝔪 : Modulus K) {q} (hq : q ∉ 𝔪.supportFinset) :
    𝔪.exps q = 0 := by
  classical
  by_contra h
  exact hq (𝔪.mem_supportFinset h)

end Modulus

/-- The congruence subgroup `U(𝔪) ≤ 𝕀 K` of a modulus. -/
noncomputable def CongSubgroup (𝔪 : Modulus K) : Subgroup (NK.GlobalCFT.Idele K) where
  carrier := {x | (∀ q : HeightOneSpectrum (RingOfIntegers K),
        Valued.v (((x (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) :
            q.adicCompletion K)) = 1 ∧
          IsCongAt K 𝔪.exps q (x (NK.GlobalCFT.Place.ofFinite q))) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal), w ∈ 𝔪.pos →
        0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
          ((x (NK.GlobalCFT.Place.ofInfinite w) : w.Completion)))}
  mul_mem' := by
    intro a b ha hb
    refine ⟨fun q => ?_, fun w hw hpos => ?_⟩
    · obtain ⟨ha1, ha2⟩ := ha.1 q
      obtain ⟨hb1, hb2⟩ := hb.1 q
      refine ⟨?_, ?_⟩
      · rw [NK.GlobalCFT.Idele.mul_apply, Units.val_mul, Valuation.map_mul, ha1, hb1, mul_one]
      · rw [IsCongAt] at ha2 hb2 ⊢
        have h1 : (((a * b) (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) :
            q.adicCompletion K) =
            ((a (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K) *
            ((b (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K) := by
          rw [NK.GlobalCFT.Idele.mul_apply, Units.val_mul]
        rw [h1]
        have h2 : (((a (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K) *
            ((b (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K)) - 1
            = (((a (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K) - 1) *
                ((b (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K)
              + (((b (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K) - 1) := by
          ring
        rw [h2]
        refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
        · rw [Valuation.map_mul, hb1, mul_one]; exact ha2
        · exact hb2
    · have h := mul_pos (ha.2 w hw hpos) (hb.2 w hw hpos)
      have h1 : (((a * b) (NK.GlobalCFT.Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion) =
          ((a (NK.GlobalCFT.Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion) *
          ((b (NK.GlobalCFT.Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion) := by
        rw [NK.GlobalCFT.Idele.mul_apply, Units.val_mul]
      rw [h1, map_mul]
      exact h
  one_mem' := by
    refine ⟨fun q => ?_, fun w hw _ => ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [NK.GlobalCFT.Idele.one_apply]; simp
      · rw [IsCongAt, NK.GlobalCFT.Idele.one_apply]; simp
    · rw [NK.GlobalCFT.Idele.one_apply]; simp
  inv_mem' := by
    intro a ha
    refine ⟨fun q => ?_, fun w hw hpos => ?_⟩
    · obtain ⟨ha1, ha2⟩ := ha.1 q
      refine ⟨?_, ?_⟩
      · rw [NK.GlobalCFT.Idele.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, ha1, inv_one]
      · rw [IsCongAt] at ha2 ⊢
        have hx : (((a⁻¹) (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) :
            q.adicCompletion K) =
            (((a (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K))⁻¹ := by
          rw [NK.GlobalCFT.Idele.inv_apply, Units.val_inv_eq_inv_val]
        rw [hx]
        set x : q.adicCompletion K := (a (NK.GlobalCFT.Place.ofFinite q) : q.adicCompletion K)
        have hne : x ≠ 0 := Units.ne_zero _
        have h2 : x⁻¹ - 1 = -((x - 1) * x⁻¹) := by
          rw [sub_mul, mul_inv_cancel₀ hne, one_mul, neg_sub]
        have hval : Valued.v (x⁻¹) = 1 := by
          have h1 : Valued.v x * Valued.v x⁻¹ = 1 := by
            rw [← Valuation.map_mul, mul_inv_cancel₀ hne, Valuation.map_one]
          rw [ha1, one_mul] at h1
          exact h1
        have h3 : Valued.v (x⁻¹ - 1) = Valued.v (x - 1) := by
          rw [h2, Valuation.map_neg, Valuation.map_mul, hval, mul_one]
        rw [h3]
        exact ha2
    · have h := ha.2 w hw hpos
      have h1 : (((a⁻¹) (NK.GlobalCFT.Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion) =
          (((a (NK.GlobalCFT.Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion))⁻¹ := by
        rw [NK.GlobalCFT.Idele.inv_apply, Units.val_inv_eq_inv_val]
      rw [h1, map_inv₀]
      exact inv_pos.mpr h

end NK.NUV2.RouteB.Sharp
