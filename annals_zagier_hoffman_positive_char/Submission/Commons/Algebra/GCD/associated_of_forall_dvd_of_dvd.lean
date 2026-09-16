import Mathlib.RingTheory.RegularLocalRing.Defs

namespace Commons.Algebra.GCD

/-- **A divisibility-decreasing sequence in a PID stabilises up to associates.**

If `a (k+1) ∣ a k` for all `k` — equivalently the chain of principal ideals `(a k)` is increasing —
then there is `K` such that `a k` is associated to `a K` for every `k ≥ K`.

Proof: `Ideal.span {a k}` is an increasing chain of ideals in a Noetherian ring
(`IsPrincipalIdealRing` gives Noetherian, or use `isNoetherianRing`), so it is eventually constant;
`(a k) = (a K)` says exactly that `a k` and `a K` are associates.

Motivation: this is the step that turns "the gcd of the σ-orbit of `Q` shrinks at each stage" into
"it stabilises", for `R = K[X]` and `a k = gcd(Q, σ⁻¹Q, …, σ⁻ᵏQ)`. -/
theorem associated_of_forall_dvd_of_dvd {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (a : ℕ → R) (h : ∀ k : ℕ, a (k + 1) ∣ a k) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → Associated (a k) (a K) := by
  -- downward divisibility along the sequence
  have hdvd : ∀ {i j : ℕ}, i ≤ j → a j ∣ a i := by
    intro i j hij
    induction hij with
    | refl => exact dvd_rfl
    | step hij ih => exact (h _).trans ih
  -- the associated chain of principal ideals is monotone
  have hmono : Monotone (fun k : ℕ => Ideal.span ({a k} : Set R)) := by
    intro i j hij
    rw [Ideal.span_singleton_le_span_singleton]
    exact hdvd hij
  obtain ⟨K, hK⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance
    ({ toFun := fun k : ℕ => Ideal.span ({a k} : Set R), monotone' := hmono })
  refine ⟨K, fun k hk => ?_⟩
  exact (Ideal.span_singleton_eq_span_singleton.mp (hK k hk)).symm

end Commons.Algebra.GCD