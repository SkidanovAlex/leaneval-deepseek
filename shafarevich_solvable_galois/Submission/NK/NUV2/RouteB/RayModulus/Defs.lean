import Mathlib
import Submission.NK.HeckeL.Basic
import Submission.NK.NUV2.RouteB.HeckePartialSum.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Moduli, congruence subgroups of the idèle group, and congruence classes of ideals

This file fixes the vocabulary for the ray-class counting theorem
`NK.NUV2.RouteB.rayClassCountRateUniform`.

A **modulus** is
* a finitely supported function `m : HeightOneSpectrum (𝓞 K) → ℕ` of exponents, together with
* a set `pos` of archimedean places at which positivity is imposed.

* `NK.NUV2.RouteB.CongSubgroup K 𝔪` is the congruence subgroup `U(𝔪) ≤ 𝕀 K` of idèles which are
  local units at every finite place, congruent to `1` modulo the `𝔪 q`-th power of the maximal
  ideal at `q`, and positive at the archimedean places in `𝔪.pos` (arbitrary at the others).
* `NK.NUV2.RouteB.IsCongElem K 𝔪 α` is the element-wise congruence condition `α ≡ 1 (𝔪)`
  together with the positivity at the places in `𝔪.pos`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.NUV2.RouteB

variable (K : Type) [Field K] [NumberField K]

-- `HasFiniteSupport` and `IsCongAt` are imported from
-- `Submission.NK.NUV2.RouteB.HeckePartialSum.Defs` (identical definitions), so that the two
-- vocabularies can be used together.

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

/-- The element-wise congruence condition: `α ≡ 1 (𝔪)` and positive at the places in `𝔪.pos`. -/
def IsCongElem (𝔪 : Modulus K) (α : K) : Prop :=
  (∀ q : HeightOneSpectrum (RingOfIntegers K), 𝔪.exps q ≠ 0 →
      Valued.v (algebraMap K (q.adicCompletion K) (α - 1)) ≤ WithZero.exp (-(𝔪.exps q : ℤ))) ∧
    (∀ (w : InfinitePlace K) (hw : w.IsReal), w ∈ 𝔪.pos →
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        (algebraMap K w.Completion α))

namespace Modulus

variable {K}

theorem mem_congSubgroup_iff {𝔪 : Modulus K} {x : NK.GlobalCFT.Idele K} :
    x ∈ CongSubgroup K 𝔪 ↔
      (∀ q : HeightOneSpectrum (RingOfIntegers K),
        Valued.v (((x (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) :
            q.adicCompletion K)) = 1 ∧
          IsCongAt K 𝔪.exps q (x (NK.GlobalCFT.Place.ofFinite q))) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal), w ∈ 𝔪.pos →
        0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
          ((x (NK.GlobalCFT.Place.ofInfinite w) : w.Completion))) := Iff.rfl

end Modulus

end NK.NUV2.RouteB

namespace NK.NUV2.RouteB

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

namespace Modulus

variable {K}

/-- The **integral ideal of a modulus**: the product of the prime powers prescribed by the
exponents. -/
noncomputable def ideal (𝔪 : Modulus K) : Ideal (RingOfIntegers K) :=
  ∏ q ∈ 𝔪.supportFinset, q.asIdeal ^ (𝔪.exps q)

theorem ideal_ne_zero (𝔪 : Modulus K) : 𝔪.ideal ≠ 0 := by
  classical
  rw [ideal, Finset.prod_ne_zero_iff]
  intro q _
  exact pow_ne_zero _ (fun h => q.ne_bot (by simpa using h))

/-- The integral ideal of a modulus, as a nonzero ideal. -/
noncomputable def ideal0 (𝔪 : Modulus K) : (Ideal (RingOfIntegers K))⁰ :=
  ⟨𝔪.ideal, by simpa [mem_nonZeroDivisors_iff_ne_zero] using 𝔪.ideal_ne_zero⟩

/-- The fractional ideal `𝔪·𝔡⁻¹` attached to a modulus and a nonzero ideal `𝔡`. -/
noncomputable def fracIdeal (𝔪 : Modulus K) (𝔡 : (Ideal (RingOfIntegers K))⁰) :
    (FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K)ˣ :=
  FractionalIdeal.mk0 K 𝔪.ideal0 * (FractionalIdeal.mk0 K 𝔡)⁻¹

end Modulus

/-- The **narrow cone**: the elements of the mixed space lying in the fundamental cone and having
positive real coordinates (i.e. the "totally positive" part of the fundamental cone). -/
def NarrowCone : Set (NumberField.mixedEmbedding.mixedSpace K) :=
  {a | a ∈ NumberField.mixedEmbedding.fundamentalCone K ∧
    ∀ (w : InfinitePlace K) (hw : w.IsReal), 0 < a.1 ⟨w, hw⟩}

/-- The narrow analogue of `normLeOne`: the narrow cone truncated by the norm ball. -/
def narrowNormLeOne : Set (NumberField.mixedEmbedding.mixedSpace K) :=
  NarrowCone K ∩ {a | NumberField.mixedEmbedding.norm a ≤ 1}

end NK.NUV2.RouteB
