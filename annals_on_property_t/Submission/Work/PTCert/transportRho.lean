import Mathlib
import Submission.Work.PTCert.fourierTransport.Common

namespace Work.PTCert

/-- `rep` is the identity up to orbit: if `act a z = y` then `rep y = rep z`. -/
lemma rep_eq_of_act_eq {m : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι)
    (rep : ι → ι) (hrepact : ∀ a x, rep (act a x) = rep x)
    {a : Fin m → ZMod 2} {z y : ι} (h : act a z = y) : rep y = rep z := by
  rw [← h, hrepact]

theorem transportRho {m : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι)
    (hact_add : ∀ a b x, act (a + b) x = act a (act b x)) (hact_zero : ∀ x, act 0 x = x)
    (rep : ι → ι) (nu : ι → (Fin m → ZMod 2))
    (hnu : ∀ x, act (nu x) (rep x) = x)
    (hrepact : ∀ a x, rep (act a x) = rep x)
    (τ : ι ≃ ι) (p : Equiv.Perm (Fin m))
    (hτ : ∀ a x, τ (act a x) = act (fun i => a (p.symm i)) (τ x)) :
    (∀ x, rep (τ (rep (τ.symm x))) = rep x) ∧
      (∀ x, rep (τ.symm (rep (τ x))) = rep x) := by
  constructor
  · intro x
    -- `x` lies in the orbit of `τ (rep (τ.symm x))`, whence `rep x = rep (τ (rep (τ.symm x)))`.
    have h := congrArg τ (hnu (τ.symm x))
    rw [hτ] at h
    rw [Equiv.apply_symm_apply] at h
    exact (rep_eq_of_act_eq act rep hrepact h).symm
  · intro x
    -- `x` lies in the orbit of `τ.symm (rep (τ x))`, using the inverse normalisation form.
    have h := congrArg τ.symm (hnu (τ x))
    rw [Equiv.symm_apply_apply] at h
    have h2 := tau_symm_act act τ p hτ (nu (τ x)) (rep (τ x))
    rw [h] at h2
    exact (rep_eq_of_act_eq act rep hrepact h2.symm).symm

end Work.PTCert
