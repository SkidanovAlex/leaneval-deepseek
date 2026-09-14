import Mathlib
import Submission.Vdw.LocalField.QpAlgebra

open scoped NumberField WithZero
open IsDedekindDomain

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Local-field chapter (G2, the `padicEquiv` identification): `QpAdic p` IS `ℚ_[p]`

Mathlib's `Rat.HeightOneSpectrum.adicCompletion.padicEquiv v` identifies
`v.adicCompletion ℚ` with `ℚ_[primesEquiv v]` as a continuous `ℚ`-algebra.
Specialising to `v := qprime p` (the height-one prime `(p)` of `ℤ`, whose
`primesEquiv`-value is `p` — `primesEquiv_qprime`), this module bundles the
identification in the ℕ-spelled form that the rest of the development wants:

* `primesEquiv_qprime` — `(primesEquiv (qprime p) : ℕ) = p`
  (via `span_natGenerator`; the map by `intEquiv ℤ` is the identity;
  equal principal spans force equal positive generators);
* `padicEquiv_congr_index` — generic transport: for any height-one prime
  `v` of `ℤ` whose `primesEquiv`-value is `p`,
  `v.adicCompletion ℚ ≃A[ℚ] Padic p` (Mathlib's `padicEquiv` with the index
  renamed; the proof is `subst p` + a local `Fact (Nat.Prime ↑(primesEquiv v))`
  from the `Nat.Primes` witness — the type renaming is pure instance
  bookkeeping, no mathematics);
* **`qpPadicEquiv p`** — `QpAdic p ≃A[ℚ] Padic p`, the identification of our
  completion of `ℚ` at `(p)` with the standard `p`-adic numbers
  (`ℚ_[p]`-spelled `Padic p`);
* `qpPadicEquiv_rat` — on rational scalars the identification is the
  `ℚ`-algebra map (`commutes'` + Rat-cast);
* **`kpAdicAlgebraPadic`** — rebase: with the identification in place the
  `QpAdic p`-algebra structure on `K_P` (`kpAdicAlgebraQp`) transports to an
  `Algebra (Padic p) (kpAdic p P)` (algebraMap =
  `(qpPadicEquiv p).symm ∘ algebraMap (QpAdic p) (kpAdic p P)`), so statements
  over `K_P` can take their scalars in the standard `ℚ_[p]`;
* **`isScalarTower_Padic`** — `IsScalarTower ℚ (Padic p) (kpAdic p P)` (the
  rebased algebra extends the canonical `ℚ`-algebra; the tower law the
  `Module.Finite` / `finrank` statements over `ℚ_[p]` need).

This is the vocabulary transfer of the Session-61 roadmap item (a): later
`Module.Finite (Padic p) (kpAdic p P)`/`finrank = e·f` statements and the
cyclotomic degree argument can be phrased over the standard `ℚ_[p]` scalars.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The `primesEquiv`-value of the height-one prime `(p)` of `ℤ` is `p`
itself. -/
lemma primesEquiv_qprime (p : ℕ) [Fact (Nat.Prime p)] :
    (Rat.HeightOneSpectrum.primesEquiv (qprime p) : ℕ) = p := by
  unfold Rat.HeightOneSpectrum.primesEquiv
  dsimp
  have hspan : Ideal.span ({(Rat.HeightOneSpectrum.natGenerator (qprime p) : ℤ)} : Set ℤ) =
      Ideal.span ({(p : ℤ)} : Set ℤ) := by
    rw [Rat.HeightOneSpectrum.span_natGenerator]
    have hid : (Rat.IsIntegralClosure.intEquiv ℤ).toRingHom = RingHom.id ℤ := by
      ext z
      simp
    change Ideal.map ((Rat.IsIntegralClosure.intEquiv ℤ).toRingHom) (qprime p).asIdeal = Ideal.span ({(p : ℤ)} : Set ℤ)
    rw [hid]
    simp [qprime]
  have hmem_p : (p : ℤ) ∈ Ideal.span ({(Rat.HeightOneSpectrum.natGenerator (qprime p) : ℤ)} : Set ℤ) := by
    rw [hspan]
    exact Ideal.mem_span_singleton_self (p : ℤ)
  have hdiv1 : Rat.HeightOneSpectrum.natGenerator (qprime p) ∣ p := by
    exact Int.ofNat_dvd.mp ((Ideal.mem_span_singleton.mp hmem_p))
  have hmem_ng : ((Rat.HeightOneSpectrum.natGenerator (qprime p) : ℤ)) ∈
      Ideal.span ({(p : ℤ)} : Set ℤ) := by
    rw [← hspan]
    exact Ideal.mem_span_singleton_self (Rat.HeightOneSpectrum.natGenerator (qprime p) : ℤ)
  have hdiv2 : p ∣ Rat.HeightOneSpectrum.natGenerator (qprime p) := by
    exact Int.ofNat_dvd.mp ((Ideal.mem_span_singleton.mp hmem_ng))
  exact Nat.dvd_antisymm hdiv1 hdiv2

/-- Generic transport of Mathlib's `padicEquiv` to the `p`-spelled `ℚ_[p]`:
for a height-one prime `v` of `ℤ` whose `primesEquiv`-value is `p`, the
completion is `ℚ_[p]` (the index renaming is instance bookkeeping via
`subst`; no mathematics). -/
noncomputable def padicEquiv_congr_index (p : ℕ) [Fact (Nat.Prime p)]
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p) :
    v.adicCompletion ℚ ≃A[ℚ] Padic p := by
  subst p
  haveI : Fact (Nat.Prime ↑(Rat.HeightOneSpectrum.primesEquiv v)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  exact Rat.HeightOneSpectrum.adicCompletion.padicEquiv v

/-- **The `ℚ_p`-identification**: `QpAdic p ≃ₐ[ℚ] ℚ_[p]` (Mathlib's
`padicEquiv` at `qprime p`, with the index `primesEquiv (qprime p)` renamed
to `p`). -/
noncomputable def qpPadicEquiv (p : ℕ) [Fact (Nat.Prime p)] : QpAdic p ≃A[ℚ] Padic p :=
  padicEquiv_congr_index p (qprime p) (primesEquiv_qprime p)

/-- On rational scalars the identification is the `ℚ`-algebra map:
`qpPadicEquiv (algebraMap ℚ (QpAdic p) q) = (q : Padic p)`. -/
lemma qpPadicEquiv_rat (p : ℕ) [Fact (Nat.Prime p)] (q : ℚ) :
    qpPadicEquiv p (algebraMap ℚ (QpAdic p) q) = (q : Padic p) := by
  change (qpPadicEquiv p).toFun (algebraMap ℚ (QpAdic p) q) = (q : Padic p)
  rw [(qpPadicEquiv p).commutes' q]
  exact eq_ratCast (algebraMap ℚ (Padic p)) q

/-- **Rebased algebra**: with the identification, `K_P` is a `ℚ_[p]`-algebra
(the `QpAdic p`-algebra of `kpAdicAlgebraQp` transported along
`(qpPadicEquiv p).symm`). -/
noncomputable instance kpAdicAlgebraPadic (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Algebra (Padic p) (kpAdic p P) :=
  RingHom.toAlgebra ((algebraMap (QpAdic p) (kpAdic p P)).comp
    ((qpPadicEquiv p).symm.toRingEquiv.toRingHom))

/-- The algebraMap of the rebased structure is
`(qpPadicEquiv p).symm ∘ algebraMap (QpAdic p) (kpAdic p P)`. -/
lemma algebraMap_eq_qpPadic (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    algebraMap (Padic p) (kpAdic p P) =
      (algebraMap (QpAdic p) (kpAdic p P)).comp ((qpPadicEquiv p).symm.toRingEquiv.toRingHom) := by
  rfl

/-- Rational scalars act through the rebased structure exactly as through the
canonical `ℚ`-algebra: the scalar tower `ℚ → ℚ_[p] → K_P`. -/
instance isScalarTower_Padic (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    IsScalarTower ℚ (Padic p) (kpAdic p P) := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro q
  have hq : (qpPadicEquiv p).symm (algebraMap ℚ (Padic p) q) = algebraMap ℚ (QpAdic p) q := by
    have h3 := congrArg (fun x : Padic p => (qpPadicEquiv p).symm x)
      ((qpPadicEquiv p).commutes' q).symm
    exact h3.trans ((qpPadicEquiv p).symm_apply_apply (algebraMap ℚ (QpAdic p) q))
  calc
    algebraMap ℚ (kpAdic p P) q
        = (algebraMap (QpAdic p) (kpAdic p P)) (algebraMap ℚ (QpAdic p) q) := by
          exact IsScalarTower.algebraMap_apply ℚ (QpAdic p) (kpAdic p P) q
    _ = (algebraMap (QpAdic p) (kpAdic p P)) ((qpPadicEquiv p).symm (algebraMap ℚ (Padic p) q)) := by
          exact congrArg (algebraMap (QpAdic p) (kpAdic p P)) hq.symm
    _ = algebraMap (Padic p) (kpAdic p P) (algebraMap ℚ (Padic p) q) := by
          exact congrArg (fun φ : (Padic p) →+* kpAdic p P => φ (algebraMap ℚ (Padic p) q))
            (algebraMap_eq_qpPadic p P).symm

