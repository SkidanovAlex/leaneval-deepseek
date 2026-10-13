import Mathlib
import Submission.Work.DSEQP.Basic

namespace Work.DSEQP

/-- **Frobenius twist of an `A`-linear map.**  Let `S` be a perfect ring of exponential
characteristic `p` (so `S` has characteristic `p` and `x ↦ x ^ p` is bijective) and let `B` be
an `A`-algebra of characteristic `p`.  Then any `A`-linear map `s : B →ₗ[A] S` can be modified,
by precomposing with the `p ^ e`-power Frobenius on `B` and postcomposing with its inverse on
`S`, into an `A`-linear map `s'` whose value at `1` is a `p ^ e`-th root of `s 1`.

The construction is `s' b = (s (b ^ (p ^ e))) ^ (1 / p ^ e)`; the key point is that the
`p ^ e`-th root map of `S` is a ring homomorphism (as `S` has characteristic `p`) and that
`(a • b) ^ (p ^ e) = a ^ (p ^ e) • b ^ (p ^ e)` (as `B` has characteristic `p`). -/
theorem frobeniusTwist {A S B : Type*} [CommRing A] [CommRing S] [Algebra A S] [CommRing B]
    [Algebra A B] (p : ℕ) [Fact p.Prime] [CharP B p] [ExpChar S p] [PerfectRing S p]
    (s : B →ₗ[A] S) (e : ℕ) : ∃ s' : B →ₗ[A] S, (s' 1) ^ (p ^ e) = s 1 := by
  -- σ is the inverse `p ^ e`-th power Frobenius on `S`, a ring isomorphism because `S` is perfect.
  let σ : S ≃+* S := (iterateFrobeniusEquiv S p e).symm
  have hσ : ∀ x : S, σ (x ^ (p ^ e)) = x := by
    intro x
    have h := RingEquiv.symm_apply_apply (iterateFrobeniusEquiv S p e) x
    simp only [iterateFrobeniusEquiv_def] at h
    exact h
  have hσ' : ∀ x : S, (σ x) ^ (p ^ e) = x := by
    intro x
    have h := RingEquiv.apply_symm_apply (iterateFrobeniusEquiv S p e) x
    simp only [iterateFrobeniusEquiv_def] at h
    exact h
  -- Frobenius on `B` is additive and multiplicative (char `p`), and commutes with the scalars.
  have hB : ∀ (a : A) (b : B),
      iterateFrobenius B p e (a • b) = a ^ (p ^ e) • (iterateFrobenius B p e b) := by
    intro a b
    rw [Algebra.smul_def, Algebra.smul_def, map_mul (iterateFrobenius B p e),
      map_pow (algebraMap A B) a (p ^ e), iterateFrobenius_def]
  have hS : ∀ (a : A) (w : S), σ (a ^ (p ^ e) • w) = a • σ w := by
    intro a w
    rw [Algebra.smul_def, Algebra.smul_def, RingEquiv.map_mul σ,
      map_pow (algebraMap A S) a (p ^ e), hσ]
  -- `s' b = σ (s (b ^ (p ^ e)))`.
  let φ : B →+ S := AddMonoidHom.mk' (fun b => σ (s (iterateFrobenius B p e b))) (by
    intro b b'; simp only [map_add])
  have hφ : ∀ b : B, φ b = σ (s (iterateFrobenius B p e b)) := fun b => rfl
  refine ⟨{ toAddHom := φ, map_smul' := ?_ }, ?_⟩
  · intro a b
    show φ (a • b) = a • φ b
    rw [hφ, hφ, hB a b, map_smul s (a ^ (p ^ e)) (iterateFrobenius B p e b),
      hS a (s (iterateFrobenius B p e b))]
  · show (φ 1) ^ (p ^ e) = s 1
    rw [hφ, map_one (iterateFrobenius B p e)]
    exact hσ' (s 1)

end Work.DSEQP
