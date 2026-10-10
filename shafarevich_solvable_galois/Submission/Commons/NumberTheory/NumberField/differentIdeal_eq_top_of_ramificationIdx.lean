import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Different
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open scoped Classical NumberField

noncomputable section

namespace Commons.NumberTheory.NumberField

/-- A prime ideal `Q` of `𝓞 K` divides the relative different
`differentIdeal (𝓞 E) (𝓞 K)` iff it is ramified over `𝓞 E`, i.e. iff its
ramification index differs from one. -/
theorem ramificationIdx_one_iff_not_dvd_differentIdeal {E K : Type*} [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K]
    (Q : Ideal (𝓞 K)) (hQ : Q.IsPrime) :
    ¬ Q ∣ differentIdeal (𝓞 E) (𝓞 K) ↔ Q.ramificationIdx (𝓞 E) = 1 := by
  letI : Q.IsPrime := hQ
  rw [not_dvd_differentIdeal_iff (A := 𝓞 E) (B := 𝓞 K) (P := Q)]
  rw [Ideal.ramificationIdx_eq_one_iff (q := Q) (R := 𝓞 E)]

/-- Pure ideal-theoretic fact behind "no ramified prime implies the relative
different is the unit ideal": for a number-field extension `E ⊆ K`, if no
prime ideal `Q` of `𝓞 K` divides `differentIdeal (𝓞 E) (𝓞 K)`, then the
different is `⊤`.

Proof: by contradiction. If the different is not `⊤`, `Ideal.exists_le_maximal`
gives a maximal (hence prime) `M` of `𝓞 K` containing it; in a Dedekind domain
containment `D ≤ M` gives divisibility `M ∣ D` (`Ideal.dvd_iff_le`), so
`M ∣ differentIdeal (𝓞 E) (𝓞 K)`, contradicting the hypothesis at `M`. -/
theorem differentIdeal_eq_top_of_forall_not_dvd {E K : Type*} [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K]
    (h : ∀ Q : Ideal (𝓞 K), Q.IsPrime → ¬ Q ∣ differentIdeal (𝓞 E) (𝓞 K)) :
    differentIdeal (𝓞 E) (𝓞 K) = ⊤ := by
  by_contra hne
  obtain ⟨M, hMmax, hDleM⟩ := Ideal.exists_le_maximal _ hne
  have hMprime : M.IsPrime := hMmax.isPrime
  exact h M hMprime (Ideal.dvd_iff_le.mpr hDleM)

/-- If a number-field extension `E ⊆ K` is unramified at every finite prime
(equivalently: every prime ideal `Q` of `𝓞 K` has ramification index
`Q.ramificationIdx (𝓞 E) = 1` over `𝓞 E`), then its relative different is
the unit ideal: `differentIdeal (𝓞 E) (𝓞 K) = ⊤`.

This is the hypothesis shape a class-field-theoretic tower (Martinet /
Hajir-Maire asymptotically-good totally real towers) supplies at each step.

Proof hints (two helper facts inside the same file are allowed):
1. pure ideal theory: from `∀ Q, Q.IsPrime → ¬ Q ∣ differentIdeal (𝓞 E) (𝓞 K)`
conclude `differentIdeal (𝓞 E) (𝓞 K) = ⊤` by contradiction using
`Ideal.exists_le_maximal` and `Ideal.dvd_iff_le`;
2. connect `Q.ramificationIdx (𝓞 E) = 1` to `¬ Q ∣ differentIdeal (𝓞 E) (𝓞 K)`
via `Ideal.ramificationIdx_eq_one_iff` and `not_dvd_differentIdeal_iff`
(RHS `Algebra.IsUnramifiedAt (𝓞 E) Q`; register `Q.IsPrime` as a local
instance where those statements need it). -/
theorem differentIdeal_eq_top_of_ramificationIdx {E K : Type*} [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K]
    (h : ∀ Q : Ideal (𝓞 K), Q.IsPrime → Q.ramificationIdx (𝓞 E) = 1) :
    differentIdeal (𝓞 E) (𝓞 K) = ⊤ := by
  refine differentIdeal_eq_top_of_forall_not_dvd ?_
  intro Q hQ
  exact (ramificationIdx_one_iff_not_dvd_differentIdeal (E := E) (K := K) Q hQ).mpr (h Q hQ)

end Commons.NumberTheory.NumberField