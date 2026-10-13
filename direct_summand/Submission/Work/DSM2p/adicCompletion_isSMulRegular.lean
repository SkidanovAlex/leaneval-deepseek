import Mathlib
import Submission.Work.DSM2p.pow_torsion_factorPow

/-!
# `p` is a nonzerodivisor on the `p`-adic completion

This module proves `Work.DSM2p.adicCompletion_isSMulRegular`: if multiplication by `p` is
injective on a commutative ring `E`, then multiplication by `p` is injective on the
`(p)`-adic completion `Ê = AdicCompletion (Ideal.span {(p : E)}) E` of `E`.

## Mathematics

Let `I = (p) ⊆ E` and let `x ∈ Ê` with `p · x = 0`.  Reducing modulo `I^{n+1}` (i.e. applying
`AdicCompletion.evalₐ I (n+1)`) gives an element of `E ⧸ I^{n+1}` which is again killed by `p`.
Lifting a representative `a ∈ E` of it, this says `p * a ∈ I^{n+1} = (p^{n+1})`; writing
`p * a = p * (p^n * c)` and using that `p` is a nonzerodivisor on `E` we get `a ∈ (p^n) = I^n`.
The compatibility of the family `x` then forces `evalₐ I n x = 0`, for every `n`.  Since `Ê` is
the limit of the `E ⧸ I^n`, we conclude `x = 0`.

So the whole content is the "`p`-torsion is supported in the kernel of the transition map"
statement, which is isolated as `Work.DSM2p.pow_torsion_factorPow` in the sibling module
`Submission.Work.DSM2p.pow_torsion_factorPow`.  Note that no separatedness, Noetherianness or
flatness hypothesis is needed: `p`-torsion in `E ⧸ p^{n+1} E` is always contained in
`p^n E ⧸ p^{n+1} E`.
-/

namespace Work.DSM2p

/-- **`p` remains a nonzerodivisor on the `p`-adic completion.**  If `p` is a nonzerodivisor on a
commutative ring `E`, then it is a nonzerodivisor on `AdicCompletion (p) E`. -/
theorem adicCompletion_isSMulRegular {E : Type*} [CommRing E] {p : ℕ}
    (hp : IsSMulRegular E (p : E)) :
    IsSMulRegular (AdicCompletion (Ideal.span {(p : E)}) E)
      (p : AdicCompletion (Ideal.span {(p : E)}) E) := by
  let I : Ideal E := Ideal.span {(p : E)}
  change IsSMulRegular (AdicCompletion I E) (p : AdicCompletion I E)
  -- It is enough to know that `p`-torsion in the completion is trivial.
  have key : ∀ w : AdicCompletion I E, (p : AdicCompletion I E) • w = 0 → w = 0 := by
    intro w hw
    have hw' : (p : AdicCompletion I E) * w = 0 := by
      rw [smul_eq_mul] at hw; exact hw
    -- A compatible family with all components zero is zero.
    apply AdicCompletion.ext
    intro n
    show w.val n = 0
    -- At level `n + 1`, the class of `p · w` is zero, i.e. `p` kills `w.val (n+1)`.
    have h1 : ((p : AdicCompletion I E) * w).val (n + 1) = 0 := by rw [hw']; rfl
    have h3 : (p : E ⧸ (I ^ (n + 1) • ⊤ : Submodule E E)) * w.val (n + 1) = 0 := by
      have h := AdicCompletion.val_mul I (n + 1) (p : AdicCompletion I E) w
      rw [h1] at h
      rw [show ((p : AdicCompletion I E)).val (n + 1) =
        (p : E ⧸ (I ^ (n + 1) • ⊤ : Submodule E E)) from rfl] at h
      exact h.symm
    -- So `w.val (n+1)` lies in the `p`-torsion of `E ⧸ I^{n+1}`, hence dies in `E ⧸ I^n` …
    have hmem : Submodule.factorPow I E (Nat.le_succ n) (w.val (n + 1)) = 0 :=
      pow_torsion_factorPow hp n (w.val (n + 1)) h3
    -- … and `w.val n` is exactly the image of `w.val (n+1)` under that transition map.
    rw [← AdicCompletion.transitionMap_comp_eval_apply (I := I) (M := E) (Nat.le_succ n) w]
    exact hmem
  intro a b hab
  have hab' : (p : AdicCompletion I E) • a = (p : AdicCompletion I E) • b := hab
  exact sub_eq_zero.mp (key (a - b) (by rw [smul_sub, hab', sub_self]))

end Work.DSM2p
