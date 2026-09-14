import Mathlib.Analysis.Convex.Gauge
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.TotallySplit

namespace Commons.GeometryOfNumbers.SuccessiveMinima

open MeasureTheory Set
open scoped Pointwise

/-- The dilation of the image of a set under a linear map equals the image of the dilation.
This is the elementary set identity `t • (U '' S) = U '' (t • S)`. -/
private lemma smul_image_linearMap {E : Type*} [AddCommGroup E] [Module ℝ E]
    (U : E →ₗ[ℝ] E) (t : ℝ) (S : Set E) : t • (U '' S) = U '' (t • S) := by
  ext y
  simp only [Set.mem_smul_set, Set.mem_image]
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨t • w, ⟨w, hw, rfl⟩, map_smul U t w⟩
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨U v, ⟨v, hv, rfl⟩, (map_smul U t v).symm⟩

/-- **Invariance of the successive minima and the volume under a unimodular map.**

`U : ℝ^N →ₗ ℝ^N` maps `ℤ^N` bijectively onto `ℤ^N` (both directions given as hypotheses) and
`|det U| = 1`.  Then, for the "dilated-body" definition of the successive minima
`λ ℓ = sInf {t > 0 | ∃ v : Fin ℓ → (Fin N → ℤ), v ℝ-independent, ∀ a, (v a : ℝ^N) ∈ t • K}`,
the successive minima of the image body `U '' K` coincide with those of `K`, the volume is
preserved, and so is the gauge: `gauge (U '' K) (U x) = gauge K x`.

Hints: `U` is a bijection (surjectivity on `ℤ^N` implies surjectivity on `ℝ^N` since `ℤ^N`
spans; injectivity on `ℤ^N` gives trivial kernel by clearing denominators), `t • (U '' K) =
U '' (t • K)`, and `MeasureTheory.Measure.addHaar_image_linearMap` with `|det U| = 1` for the
volume. -/
theorem successive_minima_unimodular (N : ℕ) (K : Set (Fin N → ℝ))
    (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) (hclosed : IsClosed K)
    (hint : (interior K).Nonempty)
    (U : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))
    (hUZ : ∀ x : Fin N → ℤ, ∃ y : Fin N → ℤ, U (fun k => (x k : ℝ)) = fun k => (y k : ℝ))
    (hUZi : ∀ y : Fin N → ℤ, ∃ x : Fin N → ℤ, U (fun k => (x k : ℝ)) = fun k => (y k : ℝ))
    (hdet : |LinearMap.det U| = 1) (ℓ : ℕ) :
    (sInf {t : ℝ | 0 < t ∧ ∃ v : Fin ℓ → (Fin N → ℤ),
        LinearIndependent ℝ (fun a => fun k => (v a k : ℝ)) ∧
        ∀ a, (fun k => (v a k : ℝ)) ∈ t • (U '' K)}
      = sInf {t : ℝ | 0 < t ∧ ∃ v : Fin ℓ → (Fin N → ℤ),
        LinearIndependent ℝ (fun a => fun k => (v a k : ℝ)) ∧
        ∀ a, (fun k => (v a k : ℝ)) ∈ t • K}) ∧
    (volume.real (U '' K) = volume.real K) ∧
    (∀ x : Fin N → ℝ, gauge (U '' K) (U x) = gauge K x) := by
  classical
  -- `|det U| = 1` gives `det U ≠ 0`, hence `U` is injective (and surjective).
  have hdet' : LinearMap.det U ≠ 0 := abs_ne_zero.mp (by rw [hdet]; exact one_ne_zero)
  have hker : LinearMap.ker U = ⊥ := by
    rw [← LinearMap.isUnit_iff_ker_eq_bot]
    exact (LinearMap.isUnit_iff_isUnit_det U).mpr (isUnit_iff_ne_zero.mpr hdet')
  have hUinj : Function.Injective U := LinearMap.ker_eq_bot.mp hker
  -- The key membership flip: `U x ∈ t • (U '' K) ↔ x ∈ t • K`.
  have hint' : ∀ (t : ℝ) (x : Fin N → ℝ), U x ∈ t • (U '' K) ↔ x ∈ t • K := by
    intro t x
    rw [smul_image_linearMap U t K]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [hUinj hyx] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · -- the successive minima agree: the two defining sets of `t` are equal
    set A : Set ℝ := {t : ℝ | 0 < t ∧ ∃ v : Fin ℓ → (Fin N → ℤ),
        LinearIndependent ℝ (fun a => fun k => (v a k : ℝ)) ∧
        ∀ a, (fun k => (v a k : ℝ)) ∈ t • (U '' K)} with hA
    set B : Set ℝ := {t : ℝ | 0 < t ∧ ∃ v : Fin ℓ → (Fin N → ℤ),
        LinearIndependent ℝ (fun a => fun k => (v a k : ℝ)) ∧
        ∀ a, (fun k => (v a k : ℝ)) ∈ t • K} with hB
    show sInf A = sInf B
    have hAB : A = B := by
      refine Set.Subset.antisymm ?_ ?_
      · -- integer points of `t • (U '' K)`: pull back by the integral inverse of `U`
        rintro t ⟨ht, v, hv_li, hv_mem⟩
        refine ⟨ht, (fun a => Classical.choose (hUZi (v a))), ?_, ?_⟩
        · have hspec : ∀ a, U (fun k => ((Classical.choose (hUZi (v a))) k : ℝ))
              = (fun k => (v a k : ℝ)) := fun a => Classical.choose_spec (hUZi (v a))
          have heq : (U ∘ fun a => fun k => ((Classical.choose (hUZi (v a))) k : ℝ))
              = (fun a => fun k => (v a k : ℝ)) := funext hspec
          exact LinearIndependent.of_comp U (by rw [heq]; exact hv_li)
        · intro a
          have hspec : U (fun k => ((Classical.choose (hUZi (v a))) k : ℝ))
              = (fun k => (v a k : ℝ)) := Classical.choose_spec (hUZi (v a))
          have h1 : (fun k => (v a k : ℝ)) ∈ t • (U '' K) := hv_mem a
          rw [smul_image_linearMap U t K] at h1
          obtain ⟨y, hy, hyU⟩ := h1
          have hy' : y = (fun k => ((Classical.choose (hUZi (v a))) k : ℝ)) :=
            hUinj (by rw [hyU, hspec])
          rwa [hy'] at hy
      · -- conversely, push integer points of `t • K` forward by `U`
        rintro t ⟨ht, w, hw_li, hw_mem⟩
        refine ⟨ht, (fun a => Classical.choose (hUZ (w a))), ?_, ?_⟩
        · have hspec : ∀ a, U (fun k => (w a k : ℝ))
              = (fun k => ((Classical.choose (hUZ (w a))) k : ℝ)) :=
            fun a => Classical.choose_spec (hUZ (w a))
          have heq : (fun a => fun k => ((Classical.choose (hUZ (w a))) k : ℝ))
              = (U ∘ fun a => fun k => (w a k : ℝ)) := funext fun a => (hspec a).symm
          rw [heq]
          exact hw_li.map' U hker
        · intro a
          have hspec : U (fun k => (w a k : ℝ))
              = (fun k => ((Classical.choose (hUZ (w a))) k : ℝ)) :=
            Classical.choose_spec (hUZ (w a))
          rw [smul_image_linearMap U t K]
          exact ⟨(fun k => (w a k : ℝ)), hw_mem a, by simpa using hspec⟩
    rw [hAB]
  · -- the volume is preserved because `|det U| = 1`
    rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.real_def,
      Measure.addHaar_image_linearMap volume U K, hdet, ENNReal.ofReal_one, one_mul]
  · -- the gauge is preserved because the defining sets are equal
    intro x
    have hset : {r : ℝ | r ∈ Set.Ioi 0 ∧ U x ∈ r • (U '' K)}
        = {r : ℝ | r ∈ Set.Ioi 0 ∧ x ∈ r • K} := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_Ioi]
      exact and_congr_right (fun _ => hint' r x)
    rw [gauge_def, gauge_def, hset]

end Commons.GeometryOfNumbers.SuccessiveMinima