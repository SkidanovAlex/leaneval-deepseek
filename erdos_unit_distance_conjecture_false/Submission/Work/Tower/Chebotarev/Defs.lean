import Mathlib
import Submission.Work.Defs.Basic

/-!
# The elementary split-prime theorem ("Chebotarev-lite")

This file sets up the working vocabulary for the existence of completely split primes in a
finite Galois extension of `ℚ`, proved by an elementary Euclid argument on the values of a
minimal polynomial together with Dedekind's factorisation theorem.

The predicate `Work.Tower.Splits q L` packages complete splitting of the rational prime `q`
in the number field `L` in the form in which the Kummer–Dedekind argument naturally delivers
it: every prime ideal factor of `q 𝓞 L` (i.e. every element of the normalised factorisation
of the ideal `q 𝓞 L`) is unramified (ramification index `1`) with residue field `𝔽_q`, and
the number of prime ideals above `q` equals `[L : ℚ]`.

Note that an ideal `P` of `𝓞 L` lies in `normalizedFactors (q 𝓞 L)` exactly when it is a
prime ideal containing `q`, so this really is the condition "all primes above `q` have
`e = f = 1`, and there are `[L : ℚ]` of them", i.e. complete splitting.
-/

open NumberField Polynomial
open scoped Classical nonZeroDivisors NumberField

namespace Work
namespace Tower

/-- `q` splits completely in the number field `L`. Formulated as: every prime ideal factor of
`q 𝓞 L` has ramification index and inertia degree one and residue field `𝔽_q`, and the number
of such prime ideals is `[L : ℚ]`. -/
def Splits (q : ℕ) (L : Type) [Field L] [NumberField L] : Prop :=
  0 < q ∧
  (∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(q : 𝓞 L)}),
      P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1) ∧
  (∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(q : 𝓞 L)}),
      Nonempty (𝓞 L ⧸ P ≃+* ZMod q)) ∧
  (UniqueFactorizationMonoid.normalizedFactors
      (Ideal.span {(q : 𝓞 L)})).toFinset.card = Module.finrank ℚ L

namespace Splits

variable {q : ℕ} {L : Type} [Field L] [NumberField L]

theorem pos (h : Splits q L) : 0 < q := h.1

theorem span_ne_bot (h : Splits q L) : Ideal.span {(q : 𝓞 L)} ≠ ⊥ := by
  intro hc
  rw [Ideal.span_singleton_eq_bot] at hc
  have hco : ((q : 𝓞 L) : L) = (q : L) := by simp
  have hL : (q : L) = 0 := by rw [← hco, hc]; simp
  exact h.pos.ne' (Nat.cast_eq_zero.mp hL)

/-- Every prime ideal above `q` has ramification index one. -/
theorem ramificationIdx_eq_one_of_isPrime (h : Splits q L) {P : Ideal (𝓞 L)} (hP : P.IsPrime)
    (hPq : (q : 𝓞 L) ∈ P) : P.ramificationIdx ℤ = 1 :=
  (h.2.1 P ((Ideal.mem_normalizedFactors_iff h.span_ne_bot).mpr
    ⟨hP, Ideal.span_singleton_le_iff_mem _ |>.mpr hPq⟩)).1

/-- Every prime ideal above `q` has inertia degree one. -/
theorem inertiaDeg_eq_one_of_isPrime (h : Splits q L) {P : Ideal (𝓞 L)} (hP : P.IsPrime)
    (hPq : (q : 𝓞 L) ∈ P) : P.inertiaDeg ℤ = 1 :=
  (h.2.1 P ((Ideal.mem_normalizedFactors_iff h.span_ne_bot).mpr
    ⟨hP, Ideal.span_singleton_le_iff_mem _ |>.mpr hPq⟩)).2

/-- The residue field of every prime ideal above `q` is `𝔽_q`. -/
theorem residue_of_isPrime (h : Splits q L) {P : Ideal (𝓞 L)} (hP : P.IsPrime)
    (hPq : (q : 𝓞 L) ∈ P) : Nonempty (𝓞 L ⧸ P ≃+* ZMod q) :=
  h.2.2.1 P ((Ideal.mem_normalizedFactors_iff h.span_ne_bot).mpr
    ⟨hP, Ideal.span_singleton_le_iff_mem _ |>.mpr hPq⟩)

end Splits

end Tower
end Work
