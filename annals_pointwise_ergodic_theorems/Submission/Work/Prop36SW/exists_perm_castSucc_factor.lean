import Mathlib

namespace Work.Prop36SW

/-- Given an injection `e : Fin t ↪ Fin (n+1)` with `t ≤ n`, one can permute `Fin (n+1)`
so that the whole range of `e` is moved into the copy `Fin n` of the first `n` elements.

This is the "reindexing" step used when a bilinear/non-conventional average over
`Fin (n+1)` has to be reduced to an average over `Fin n`: the extra index is never hit.

The proof is Mathlib's `Equiv.Perm.exists_extending_pair`: the two injections
`e` and `i ↦ Fin.castSucc (Fin.castLE ht i)` (whose range lies in `Fin n ⊆ Fin (n+1)`)
from the finite type `Fin t` are matched by a single permutation of `Fin (n+1)`. -/
theorem exists_perm_castSucc_factor {t n : ℕ} (ht : t ≤ n) (e : Fin t ↪ Fin (n + 1)) :
    ∃ (τ : Equiv.Perm (Fin (n + 1))) (e' : Fin t ↪ Fin n),
      ∀ i : Fin t, τ (e i) = Fin.castSucc (e' i) := by
  classical
  have hg : Function.Injective (fun i : Fin t => Fin.castSucc (Fin.castLE ht i)) :=
    fun i j h => Fin.ext (by simpa using congrArg Fin.val h)
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair (α := Fin t) (β := Fin (n + 1))
    (fun i => e i) (fun i => Fin.castSucc (Fin.castLE ht i)) e.injective hg
  exact ⟨τ, ⟨fun i => Fin.castLE ht i, fun i j h => Fin.ext (by simpa using congrArg Fin.val h)⟩,
    fun i => hτ i⟩

end Work.Prop36SW
