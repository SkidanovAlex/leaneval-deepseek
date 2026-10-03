import Mathlib
import Submission.Work.Pert.RBlock

namespace Work.Pert

/-- `Rlow` is `T`-equivariant in the last argument: shifting `w` by one shifts the value by one.

This is the content behind `PertData`'s requirement that the lifted return map satisfies
`R (w+1) = R w + 1`.  It is a purely combinatorial consequence of the definition
`Rlow f Qp' τ Φp φ m k dlow w = Φp (invOn τ Qp' (f^[m] (φ w))) - m - k + dlow`,
of the Abel relation `Φp (F z) = Φp z + 1` on `Qp`, and of the orbit relation
`τ (F z) = f (τ z)`:  the preimage `invOn τ Qp' (f^[m] (φ w))` of the level `m` of `w` is moved by `F`
onto the preimage of the level `m` of `w + 1`, because `f^[m] (φ (w+1)) = f^[m+1] (φ w)`. -/
theorem Rlow_add_one {f F Φp φ τ : ℂ → ℂ} {Qp' Qp : Set ℂ} {α : ℂ} {m : ℕ} {k : ℤ} {dlow : ℂ}
    {w : ℂ}
    (hφ : φ (w + 1) = f (φ w))
    (hτF : ∀ z ∈ Qp, τ (F z) = f (τ z))
    (hsub : Qp' ⊆ Qp)
    (hinjτ : Set.InjOn τ Qp')
    (hFmem : ∀ z ∈ Qp', F z ∈ Qp')
    (hAbel : ∀ z ∈ Qp, F z ∈ Qp → Φp (F z) = Φp z + 1)
    (hz : f^[m] (φ w) ∈ τ '' Qp')
    (hz1 : f^[m] (φ (w + 1)) ∈ τ '' Qp') :
    Work.Pert.Rlow f Qp' τ Φp φ m k dlow (w + 1)
      = Work.Pert.Rlow f Qp' τ Φp φ m k dlow w + 1 := by
  have hzQ : invOn τ Qp' (f^[m] (φ w)) ∈ Qp' := invOn_mem hz
  have hzτ : τ (invOn τ Qp' (f^[m] (φ w))) = f^[m] (φ w) := invOn_spec hz
  have hFQ : F (invOn τ Qp' (f^[m] (φ w))) ∈ Qp' := hFmem _ hzQ
  have hτF' : τ (F (invOn τ Qp' (f^[m] (φ w)))) = f (f^[m] (φ w)) := by
    rw [hτF _ (hsub hzQ), hzτ]
  -- the level-`m` point of `w + 1` is the `f`-image of the level-`m` point of `w`
  have hiter : f (f^[m] (φ w)) = f^[m] (φ (w + 1)) := by
    rw [hφ, ← Function.iterate_succ_apply' f m (φ w), Function.iterate_succ_apply f m (φ w)]
  have hτF'' : τ (F (invOn τ Qp' (f^[m] (φ w)))) = f^[m] (φ (w + 1)) :=
    hτF'.trans hiter
  -- moving the preimage of the level-`m` point of `w` by `F` gives the preimage of that of `w + 1`
  have hinv_eq : invOn τ Qp' (f^[m] (φ (w + 1))) = F (invOn τ Qp' (f^[m] (φ w))) :=
    invOn_eq hinjτ ⟨_, hFQ, hτF''⟩ hFQ hτF''
  -- Abel relation at that preimage
  have hAbelz : Φp (F (invOn τ Qp' (f^[m] (φ w))))
      = Φp (invOn τ Qp' (f^[m] (φ w))) + 1 :=
    hAbel _ (hsub hzQ) (hsub hFQ)
  simp only [Rlow]
  rw [hinv_eq, hAbelz]
  ring

end Work.Pert
