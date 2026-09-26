import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.twistedFourierCriterion

namespace Work.PTCert.Klein

/-- Admissibility (`χ_S = 1` on the stabiliser) is inherited by the representatives of the
`kap`-orbit: the stabiliser of `rep (kap b x)` has trivial `S`-sign character as soon as the one
of `x` does.

The proof uses the fact that the two `(ℤ/2)^m`-actions are intertwined by `kap` with a twist
`θ` that leaves `χ_S` unchanged (`hchiθ`), together with `kap b` being an involution *on the orbit
of* `x`: `kap b (kap b x) = x` because `b + b = 0` and `kap` is a composition law. -/
theorem admKap {m m2 : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι)
    (kap : (Fin m2 → ZMod 2) → ι → ι)
    (θ : (Fin m2 → ZMod 2) → (Fin m → ZMod 2) → (Fin m → ZMod 2))
    (nu : ι → (Fin m → ZMod 2)) (rep : ι → ι) (S : Finset (Fin m))
    (hact : ∀ a b x, act (a + b) x = act a (act b x))
    (hactnu : ∀ x, act (nu x) (rep x) = x)
    (hcomm : ∀ b a x, kap b (act a x) = act (θ b a) (kap b x))
    (hkap : ∀ a b x, kap (a + b) x = kap a (kap b x)) (hkap0 : ∀ x, kap 0 x = x)
    (hchiθ : ∀ b a, Submission.PTCert.chiS S (θ b a) = Submission.PTCert.chiS S a)
    (x : ι) (hx : rep x = x) (hadm : ∀ a, act a x = x → Submission.PTCert.chiS S a = 1)
    (b : Fin m2 → ZMod 2) :
    ∀ a', act a' (rep (kap b x)) = rep (kap b x) → Submission.PTCert.chiS S a' = 1 := by
  -- `0` acts trivially, obtained from `hactnu` and the composition law `hact`.
  have hact0 : ∀ y, act 0 y = y := by
    intro y
    calc act 0 y = act 0 (act (nu y) (rep y)) := by rw [hactnu y]
      _ = act (0 + nu y) (rep y) := (hact 0 (nu y) (rep y)).symm
      _ = act (nu y) (rep y) := by rw [zero_add]
      _ = y := hactnu y
  -- every element of `(ℤ/2)^m` (resp. `(ℤ/2)^m2`) is its own inverse.
  have hself : ∀ a : Fin m → ZMod 2, a + a = 0 := by
    intro a; funext i; exact CharTwo.add_self_eq_zero (a i)
  have hself2 : ∀ a : Fin m2 → ZMod 2, a + a = 0 := by
    intro a; funext i; exact CharTwo.add_self_eq_zero (a i)
  -- `kap b` is an involution at `x`.
  have hz : kap b (kap b x) = x := by
    have h := hkap b b x
    rw [hself2 b, hkap0] at h
    exact h.symm
  intro a' ha'
  -- `nu (kap b x)` carries `kap b x` to the representative of its `act`-class, so it is an
  -- involution on that class.
  have hy : act (nu (kap b x)) (kap b x) = rep (kap b x) := by
    have h1 : act (nu (kap b x)) (rep (kap b x)) = kap b x := hactnu (kap b x)
    calc act (nu (kap b x)) (kap b x)
        = act (nu (kap b x)) (act (nu (kap b x)) (rep (kap b x))) := by rw [h1]
      _ = act (nu (kap b x) + nu (kap b x)) (rep (kap b x)) := (hact _ _ _).symm
      _ = act 0 (rep (kap b x)) := by rw [hself]
      _ = rep (kap b x) := hact0 _
  -- hence `a'`, which fixes the representative by hypothesis, actually fixes `kap b x`.
  have hzy : act a' (kap b x) = kap b x := by
    have hc : act a' (rep (kap b x)) = rep (kap b x) := ha'
    rw [← hy] at hc
    have h2 : act (a' + nu (kap b x)) (kap b x) = act (nu (kap b x)) (kap b x) := by
      rw [hact]; exact hc
    have h3 := congrArg (act (nu (kap b x))) h2
    rw [← hact (nu (kap b x)) (a' + nu (kap b x)) (kap b x),
        ← hact (nu (kap b x)) (nu (kap b x)) (kap b x),
        hself (nu (kap b x)), hact0] at h3
    rwa [show nu (kap b x) + (a' + nu (kap b x)) = a' from by
      rw [add_comm a' (nu (kap b x)), ← add_assoc, hself (nu (kap b x)), zero_add]] at h3
  -- transport along `hcomm` back to `x`, were `hadm` applies.
  have hstab : act (θ b a') x = x := by
    have h := hcomm b a' (kap b x)
    rw [hzy, hz] at h
    exact h.symm
  have hfin := hadm (θ b a') hstab
  rwa [hchiθ b a'] at hfin

end Work.PTCert.Klein
