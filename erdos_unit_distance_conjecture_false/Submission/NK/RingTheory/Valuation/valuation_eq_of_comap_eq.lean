import Mathlib
import Submission.NK.RingTheory.Valuation.comap_valuation_le
import Submission.Commons.RingTheory.Valuation.exists_pow_eq_algebraMap_of_isAlgebraic

/-!
# Equality of two valuations with the same pulled-back valuation ring

Let `K ⊆ E ⊆ L` be a tower of fields with `E/K` algebraic, let `W` be a valuation subring of `L`
and let `ψ : E →ₐ[K] L` be a `K`-embedding.  If `ψ` and the inclusion `E ↪ L` pull `W` back to the
same valuation subring of `E`, then the induced valuations of `ψ z` and of `z` agree for all
`z : E`.

The proof is the usual uniqueness argument for the extension of a valuation to an algebraic
extension: since `E/K` is algebraic, some positive power of `W.valuation (ψ z)` is the value of an
element of `K` (`exists_pow_eq_algebraMap_of_isAlgebraic`).  Hence the element
`u = z ^ n / y` of `E` has value `1` with respect to the valuation pulled back along `ψ`; because
the pulled-back valuation rings agree, `u` also has value `1` with respect to the valuation
restricted from `W`.  Comparing the two computations gives
`W.valuation (ψ z) ^ n = W.valuation z ^ n`, and a linearly ordered group is torsion free, so the
common power can be cancelled.
-/

namespace NK.RingTheory.Valuation

lemma valuation_eq_of_comap_eq {K E L : Type*} [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    (hE : Algebra.IsAlgebraic K E) (W : ValuationSubring L) (ψ : E →ₐ[K] L)
    (hcomap : W.comap (ψ : E →+* L) = W.comap (algebraMap E L)) :
    ∀ z : E, W.valuation (ψ z) = W.valuation (algebraMap E L z) := by
  intro z
  by_cases hz : z = 0
  · subst hz
    simp
  -- A positive power of the value of `ψ z` is the value of an element of `K`.
  obtain ⟨n, hn, y, hy, hpow⟩ :=
    Commons.RingTheory.Valuation.exists_pow_eq_algebraMap_of_isAlgebraic
      (Valuation.comap (ψ : E →+* L) W.valuation) (hE.isAlgebraic z) hz
  have hpow' : W.valuation (ψ z) ^ n = W.valuation (ψ (algebraMap K E y)) := hpow
  -- Nonvanishing of the elements and of their values which occur below.
  have hyE : algebraMap K E y ≠ 0 := by
    intro h
    have h1 : algebraMap K E y * algebraMap K E y⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hy, map_one]
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  have hAy : W.valuation (ψ (algebraMap K E y)) ≠ 0 := by
    refine (Valuation.ne_zero_iff W.valuation).mpr ?_
    intro h
    have h1 : ψ (algebraMap K E y) * ψ ((algebraMap K E y)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hyE, map_one]
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  -- The element `u := z ^ n / y` of `E`.
  set u : E := z ^ n / algebraMap K E y with hu
  have huz : u * algebraMap K E y = z ^ n := by
    rw [hu]
    exact div_mul_cancel₀ _ hyE
  have hu_ne : u ≠ 0 := by
    rw [hu]
    exact div_ne_zero (pow_ne_zero n hz) hyE
  -- Its value with respect to the valuation pulled back along `ψ` is `1`.
  have hmem_u : W.valuation (ψ u) = 1 := by
    have h1 : W.valuation (ψ (u * algebraMap K E y)) = W.valuation (ψ (z ^ n)) := by rw [huz]
    simp only [map_mul, map_pow] at h1
    rw [hpow'] at h1
    exact mul_right_cancel₀ hAy (by simpa using h1)
  -- Hence `u` is a unit of the pulled-back valuation ring.
  have hψuW : ψ u ∈ W := (ValuationSubring.valuation_le_one_iff W (ψ u)).mp (le_of_eq hmem_u)
  have hψuinvW : ψ u⁻¹ ∈ W := by
    have h : W.valuation (ψ u⁻¹) = 1 := by
      rw [map_inv₀, Valuation.map_inv, hmem_u, inv_one]
    exact (ValuationSubring.valuation_le_one_iff W (ψ u⁻¹)).mp (le_of_eq h)
  have huW : algebraMap E L u ∈ W := by
    have h : u ∈ W.comap (ψ : E →+* L) := ValuationSubring.mem_comap.mpr hψuW
    exact ValuationSubring.mem_comap.mp (hcomap ▸ h)
  have huinvW : (algebraMap E L u)⁻¹ ∈ W := by
    have h : u⁻¹ ∈ W.comap (ψ : E →+* L) := ValuationSubring.mem_comap.mpr hψuinvW
    have h' : u⁻¹ ∈ W.comap (algebraMap E L) := hcomap ▸ h
    have h'' := ValuationSubring.mem_comap.mp h'
    rwa [map_inv₀] at h''
  have halu_ne : algebraMap E L u ≠ 0 := by
    intro h
    have h1 : algebraMap E L u * algebraMap E L u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hu_ne, map_one]
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  -- So `u` also has value `1` with respect to the valuation restricted from `W`.
  have hmem_u' : W.valuation (algebraMap E L u) = 1 := by
    refine le_antisymm ?_ ?_
    · exact (ValuationSubring.valuation_le_one_iff W (algebraMap E L u)).mpr huW
    · have h := (ValuationSubring.valuation_le_iff W (1 : L) (algebraMap E L u)).mpr
        ⟨⟨(algebraMap E L u)⁻¹, huinvW⟩, inv_mul_cancel₀ halu_ne⟩
      simpa using h
  -- Comparing the two computations of the value of `u`.
  have hψval : W.valuation (algebraMap E L (algebraMap K E y)) = W.valuation (ψ z) ^ n := by
    rw [← IsScalarTower.algebraMap_apply K E L, ← ψ.commutes, ← hpow']
  have hkey : W.valuation (ψ z) ^ n = W.valuation (algebraMap E L z) ^ n := by
    have h1 : W.valuation (algebraMap E L (u * algebraMap K E y))
        = W.valuation (algebraMap E L (z ^ n)) := by rw [huz]
    rw [map_mul, Valuation.map_mul, map_pow, Valuation.map_pow, hmem_u', one_mul, hψval] at h1
    exact h1
  exact pow_left_injective (Nat.pos_iff_ne_zero.mp hn) hkey

end NK.RingTheory.Valuation
