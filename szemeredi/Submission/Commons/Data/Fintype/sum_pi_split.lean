import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

namespace Commons.Data.Fintype

theorem sum_pi_split {κ : Type*} [Fintype κ] [DecidableEq κ] {W : κ → Type*}
    [∀ k, Fintype (W k)] [∀ k, DecidableEq (W k)] [∀ k, Nonempty (W k)]
    (S : Finset κ) (f : ((k : κ) → W k) → ℝ) :
    (∑ v : (k : κ) → W k, f v)
      = ∑ u : (k : {k // k ∈ S}) → W k.val, ∑ w : (k : {k // k ∉ S}) → W k.val,
          f (fun k => if h : k ∈ S then u ⟨k, h⟩ else w ⟨k, h⟩) := by
  rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd (fun k => k ∈ S) W).symm f]
  rw [Fintype.sum_prod_type]
  rfl

end Commons.Data.Fintype