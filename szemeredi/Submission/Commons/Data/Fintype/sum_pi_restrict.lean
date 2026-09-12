import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

namespace Commons.Data.Fintype

theorem sum_pi_restrict {κ : Type*} [Fintype κ] [DecidableEq κ] {W : κ → Type*}
    [∀ k, Fintype (W k)] [∀ k, DecidableEq (W k)] [∀ k, Nonempty (W k)]
    (S : Finset κ) (f : ((k : {k // k ∈ S}) → W k.val) → ℝ) :
    (∑ v : (k : κ) → W k, f (fun k' => v k'.val))
      = (Fintype.card ((k : {k // k ∉ S}) → W k.val) : ℝ) * (∑ u, f u) := by
  have h1 : (∑ v : (k : κ) → W k, f (fun k' => v k'.val))
      = ∑ p : ((k : {k // k ∈ S}) → W k.val) × ((k : {k // k ∉ S}) → W k.val),
          f p.1 := by
    have := Equiv.sum_comp (Equiv.piEquivPiSubtypeProd (fun k => k ∈ S) W)
      (fun p : ((k : {k // k ∈ S}) → W k.val) × ((k : {k // k ∉ S}) → W k.val) => f p.1)
    simpa using this
  calc (∑ v : (k : κ) → W k, f (fun k' => v k'.val))
      = ∑ p : ((k : {k // k ∈ S}) → W k.val) × ((k : {k // k ∉ S}) → W k.val),
          f p.1 := h1
    _ = ∑ u : (k : {k // k ∈ S}) → W k.val,
          ∑ _w : (k : {k // k ∉ S}) → W k.val, f u := Fintype.sum_prod_type _
    _ = ∑ u : (k : {k // k ∈ S}) → W k.val,
          (Fintype.card ((k : {k // k ∉ S}) → W k.val) : ℝ) * f u := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_const, nsmul_eq_mul]
        rfl
    _ = (Fintype.card ((k : {k // k ∉ S}) → W k.val) : ℝ) *
          ∑ u : (k : {k // k ∈ S}) → W k.val, f u := by
        rw [Finset.mul_sum]

end Commons.Data.Fintype