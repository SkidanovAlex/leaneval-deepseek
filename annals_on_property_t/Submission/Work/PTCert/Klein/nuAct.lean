import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.twistedFourierCriterion

/-!
# `nuAct`: the `nu`-label of a translate

`act` is an action of the elementary abelian 2-group `A = (Fin m → ZMod 2)` on `ι`, `rep` picks
an orbit representative and `nu x` is a group element carrying `rep x` to `x`
(`act (nu x) (rep x) = x`).  If `S` is such that every element of `A` fixing the representative
`rep z` lies in the kernel of the sign character `χ_S = chiS S`, then for `z' = act a z` the label
`nu z'` differs from `nu z` by `a` *at the level of the character*:

  `χ_S (nu z') = χ_S a · χ_S (nu z)`.

Since `A` has exponent two, applied to `act (nu z') (rep z) = z' = act (a + nu z) (rep z)`, the
element `nu z' + (a + nu z)` fixes `rep z`; by hypothesis `χ` of it is `1`, so `χ (nu z')` and
`χ a · χ (nu z)` are mutually inverse square roots of unity, hence equal.
-/

set_option autoImplicit false

namespace Work.PTCert.Klein

/-- `(Fin m → ZMod 2)` has exponent two. -/
private lemma zmod2_vec_add_self {m : ℕ} (v : Fin m → ZMod 2) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

theorem nuAct {m : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι) (nu : ι → (Fin m → ZMod 2))
    (rep : ι → ι) (S : Finset (Fin m))
    (hact : ∀ a b x, act (a + b) x = act a (act b x)) (hact0 : ∀ x, act 0 x = x)
    (hactnu : ∀ x, act (nu x) (rep x) = x)
    {z z' : ι} (hzz : rep z = rep z')
    (hadm : ∀ a, act a (rep z) = rep z → Submission.PTCert.chiS S a = 1)
    (a : Fin m → ZMod 2) (hz' : z' = act a z) :
    Submission.PTCert.chiS S (nu z') = Submission.PTCert.chiS S a * Submission.PTCert.chiS S (nu z) := by
  -- Both `nu z'` and `a + nu z` carry `rep z` to `z'`.
  have h1 : act (nu z') (rep z) = z' := by
    have h := hactnu z'
    rwa [← hzz] at h
  have h2 : act (a + nu z) (rep z) = z' := by
    rw [hact, hactnu z, hz']
  -- Since `act b` is an involution, `nu z' + (a + nu z)` fixes `rep z`.
  have huz' : act (nu z') z' = rep z := by
    have h : act (nu z') (act (nu z') (rep z)) = rep z := by
      rw [← hact (nu z') (nu z') (rep z), zmod2_vec_add_self (nu z'), hact0]
    rwa [h1] at h
  have h3 : act (nu z' + (a + nu z)) (rep z) = rep z := by
    rw [hact, h2, huz']
  have h4 : Submission.PTCert.chiS S (nu z' + (a + nu z)) = 1 := hadm _ h3
  -- Expand `χ` of the sum.
  rw [Work.PTCert.chiS_add, Work.PTCert.chiS_add] at h4
  -- Use `χ (nu z') · χ (nu z') = 1` to cancel.
  calc Submission.PTCert.chiS S (nu z')
      = Submission.PTCert.chiS S (nu z') * 1 := (mul_one _).symm
    _ = Submission.PTCert.chiS S (nu z') *
          (Submission.PTCert.chiS S (nu z') *
            (Submission.PTCert.chiS S a * Submission.PTCert.chiS S (nu z))) := by rw [h4]
    _ = (Submission.PTCert.chiS S (nu z') * Submission.PTCert.chiS S (nu z')) *
          (Submission.PTCert.chiS S a * Submission.PTCert.chiS S (nu z)) := by ring
    _ = 1 * (Submission.PTCert.chiS S a * Submission.PTCert.chiS S (nu z)) := by
          rw [Work.PTCert.chiS_sq]
    _ = Submission.PTCert.chiS S a * Submission.PTCert.chiS S (nu z) := by rw [one_mul]

end Work.PTCert.Klein
