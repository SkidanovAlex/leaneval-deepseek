import Mathlib
import Submission.Work.PTCert.fourierTransport.Common

namespace Work.PTCert

/-- Transport of an `M`-pair along the permutation `τ` of the `(ℤ/2)^m`-action.

Writing `G = (Fin m → ZMod 2)` and letting `act` be a `G`-action on `ι`, `τ` an
automorphism of `ι` whose underlying coordinate map is `p` (so that
`act b (τ x) = τ (act (b ∘ p) x)`, see `tau_act`), and fixing a system of
representatives `rep` with `act (ν x) (rep x) = x`, the `τ`-invariance of `M`
gives
`M (rep (τ u)) (act a (rep (τ v))) = M (act (ν (τ u) ∘ p) u) (act a (act (ν (τ v) ∘ p) v))`
expressed purely through `u`, `v`. -/
theorem transportMPair {m : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι)
    (hact_add : ∀ a b x, act (a + b) x = act a (act b x)) (hact_zero : ∀ x, act 0 x = x)
    (M : Matrix ι ι ℝ)
    (rep : ι → ι) (nu : ι → (Fin m → ZMod 2)) (hnu : ∀ x, act (nu x) (rep x) = x)
    (τ : ι ≃ ι) (p : Equiv.Perm (Fin m))
    (hτ : ∀ a x, τ (act a x) = act (fun i => a (p.symm i)) (τ x))
    (hMτ : ∀ x y, M (τ x) (τ y) = M x y)
    (a : Fin m → ZMod 2) (u v : ι) :
    M (rep (τ u)) (act a (rep (τ v))) =
      M (act (fun i => nu (τ u) (p i)) u)
        (act (fun i => a (p i)) (act (fun i => nu (τ v) (p i)) v)) := by
  -- `rep x = act (ν x) x`, because `act (ν x)` is an involution and `act (ν x) (rep x) = x`.
  have hrep : ∀ x, rep x = act (nu x) x := by
    intro x
    have h := act_neg act hact_add hact_zero (nu x) (rep x)
    rw [hnu x] at h
    exact h.symm
  -- Push `τ` off the representatives: `act b (τ x) = τ (act (b ∘ p) x)`.
  have key1 : rep (τ u) = τ (act (fun i => nu (τ u) (p i)) u) := by
    rw [hrep (τ u), tau_act act τ p hτ (nu (τ u)) u]
  have key2 : act a (rep (τ v)) =
      τ (act (fun i => (a + nu (τ v)) (p i)) v) := by
    rw [hrep (τ v)]
    rw [← hact_add a (nu (τ v)) (τ v)]
    rw [tau_act act τ p hτ (a + nu (τ v)) v]
  rw [key1, key2, hMτ]
  -- Split the combined coordinate: `(a + ν (τ v)) ∘ p = (a ∘ p) + (ν (τ v) ∘ p)`.
  have hV : act (fun i => (a + nu (τ v)) (p i)) v =
      act (fun i => a (p i)) (act (fun i => nu (τ v) (p i)) v) := by
    have hf : (fun i => (a + nu (τ v)) (p i)) =
        (fun i => a (p i)) + (fun i => nu (τ v) (p i)) := by
      funext i; rfl
    rw [hf, hact_add]
  rw [hV]

end Work.PTCert
