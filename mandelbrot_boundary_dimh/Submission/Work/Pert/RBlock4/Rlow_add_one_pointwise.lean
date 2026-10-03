import Mathlib
import Submission.Work.Pert.RBlock
import Submission.Work.Pert.Rlow_add_one

/-!
# PERT · `Work.Pert.RBlock4.Rlow_add_one_pointwise`

`Work.Pert.Rlow_add_one` proves the `T`-equivariance step
`Rlow (w+1) = Rlow w + 1` of the low piece of the lifted return map, but it needs the **global**
clause `hFmem : ∀ z ∈ Qp', F z ∈ Qp'`.  That clause is FALSE for the `Qp'` the crux produces
(`Qp' = ⋃_{w ∈ K} ball (τ₀ (f₀^[m] (d.φ w))) 4`, `crux_limit_v2.lean:524`), which is only known to
satisfy the **pointwise** clause `F (invOn τ Qp' (f^[m] (φ w))) ∈ Qp'` for `w ∈ K`
(`crux_limit_v2.lean:160`).

The present file therefore restates the same lemma with `hFmem` replaced by that pointwise clause.
The proof is verbatim the proof of `Work.Pert.Rlow_add_one`: `F` sends the chosen `τ`-preimage of
the level-`m` point of `w` to the chosen `τ`-preimage of the level-`m` point of `w + 1` (both have
`τ`-image `f^[m] (φ (w+1))` and `τ` is injective on `Qp'`), and the Abel equation moves the `Φp`
value by one.
-/

namespace Work.Pert.RBlock4

open MandelDim Complex Set

noncomputable section

/-- **The `T`-equivariance step of `Rlow`, pointwise form.**  Under the pointwise clause
`F (invOn τ Qp' (f^[m] (φ w))) ∈ Qp'` (supplied by the crux for `w ∈ K̂`) and the landing clauses
at `w` and `w + 1`, the low piece moves by one under `w ↦ w + 1`. -/
theorem Rlow_add_one_pointwise {f F Φp φ τ : ℂ → ℂ} {Qp' Qp : Set ℂ} {m : ℕ} {k : ℤ}
    {dlow : ℂ} {w : ℂ}
    (hφ : φ (w + 1) = f (φ w))
    (hτF : ∀ z ∈ Qp, τ (F z) = f (τ z))
    (hsub : Qp' ⊆ Qp)
    (hinjτ : Set.InjOn τ Qp')
    (hFz : F (invOn τ Qp' (f^[m] (φ w))) ∈ Qp')
    (hAbel : ∀ z ∈ Qp, F z ∈ Qp → Φp (F z) = Φp z + 1)
    (hz : f^[m] (φ w) ∈ τ '' Qp')
    (hz1 : f^[m] (φ (w + 1)) ∈ τ '' Qp') :
    Work.Pert.Rlow f Qp' τ Φp φ m k dlow (w + 1)
      = Work.Pert.Rlow f Qp' τ Φp φ m k dlow w + 1 := by
  have hzQ : invOn τ Qp' (f^[m] (φ w)) ∈ Qp' := invOn_mem hz
  have hzτ : τ (invOn τ Qp' (f^[m] (φ w))) = f^[m] (φ w) := invOn_spec hz
  have hτF' : τ (F (invOn τ Qp' (f^[m] (φ w)))) = f (f^[m] (φ w)) := by
    rw [hτF _ (hsub hzQ), hzτ]
  have hiter : f (f^[m] (φ w)) = f^[m] (φ (w + 1)) := by
    rw [hφ, ← Function.iterate_succ_apply' f m (φ w), Function.iterate_succ_apply f m (φ w)]
  have hτF'' : τ (F (invOn τ Qp' (f^[m] (φ w)))) = f^[m] (φ (w + 1)) := hτF'.trans hiter
  have hinv_eq : invOn τ Qp' (f^[m] (φ (w + 1))) = F (invOn τ Qp' (f^[m] (φ w))) :=
    invOn_eq hinjτ ⟨_, hFz, hτF''⟩ hFz hτF''
  have hAbelz : Φp (F (invOn τ Qp' (f^[m] (φ w))))
      = Φp (invOn τ Qp' (f^[m] (φ w))) + 1 :=
    hAbel _ (hsub hzQ) (hsub hFz)
  simp only [Work.Pert.Rlow]
  rw [hinv_eq, hAbelz]
  ring

end

end Work.Pert.RBlock4
