import Mathlib.LinearAlgebra.ExteriorPower.Basis

set_option autoImplicit true

namespace Commons.LinearAlgebra.ExteriorPower

open exteriorPower
open Set

/-- Over a field, the exterior product of a linearly independent family of `k` vectors is
nonzero in the `k`th exterior power. -/
lemma iMulti_ne_zero_of_linearIndependent {K : Type*} [Field K] {E : Type*} [AddCommGroup E]
    [Module K E] {k : ℕ} (v : Fin k → E) (hv : LinearIndependent K v) :
    exteriorPower.ιMulti K k v ≠ 0 := by
  classical
  let s : ↑(Set.powersetCard (Fin k) k) := ⟨Finset.univ, by simp [Finset.card_univ]⟩
  have hli : LinearIndependent K (exteriorPower.ιMulti_family K k v) :=
    exteriorPower.ιMulti_family_linearIndependent_field (K := K) (E := E) (n := k) hv
  have hne : exteriorPower.ιMulti_family K k v s ≠ 0 := by
    exact LinearIndependent.ne_zero s hli
  let τ : Fin k ↪o Fin k := Set.powersetCard.ofFinEmbEquiv.symm s
  have τinj : Function.Injective (fun i : Fin k => τ i) := by
    exact RelEmbedding.injective τ
  have τbij : Function.Bijective (fun i : Fin k => τ i) := τinj.bijective_of_finite
  let σ : Equiv.Perm (Fin k) := Equiv.ofBijective (fun i : Fin k => τ i) τbij
  have hval : exteriorPower.ιMulti_family K k v s =
      exteriorPower.ιMulti K k (v ∘ (fun i : Fin k => σ i)) := by
    simp [exteriorPower.ιMulti_family, σ, τ]
  have hperm : exteriorPower.ιMulti K k (v ∘ (fun i : Fin k => σ i)) =
      (Equiv.Perm.sign σ) • exteriorPower.ιMulti K k v := by
    simpa using (exteriorPower.ιMulti K k (M := E)).map_perm v σ
  by_contra hz
  apply hne
  calc
    exteriorPower.ιMulti_family K k v s =
        exteriorPower.ιMulti K k (v ∘ (fun i : Fin k => σ i)) := hval
    _ = (Equiv.Perm.sign σ) • exteriorPower.ιMulti K k v := hperm
    _ = 0 := by simp [hz]

end Commons.LinearAlgebra.ExteriorPower
