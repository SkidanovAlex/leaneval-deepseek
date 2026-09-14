import Mathlib
import Submission.Vdw.LocalField.RankIdentity
import Submission.Vdw.LocalField.RamificationCompat
import Submission.Vdw.LocalField.KpVal
import Submission.Commons.LinearAlgebra.FreeModule.nonempty_quotient_ideal_free_equiv

open scoped NumberField WithZero Valued
open IsDedekindDomain

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# Local-field chapter (G2(b) freeness): `kpInt` is a free `QpInt`-module of rank `e·f`

With `Module.Finite (QpInt p) (kpInt p P)` (`QpIntFinite`) and
`kpInt_torsionFree` (`RankIdentity`), `kpInt p P` is a finite-type
torsion-free module over the principal ideal domain `QpInt p`
(`QpInt` is a DVR, `IsDiscreteValuationRing`, hence `IsPrincipalIdealRing`),
so it is FREE:

* `free_kpInt_QpInt` — `Module.Free (QpInt p) (kpInt p P)` (Mathlib
  `Module.free_of_finite_type_torsion_free'` over a PID);
* `finrank_kpInt_eq_mul` — `Module.finrank (QpInt p) (kpInt p P) =
  P.ramificationIdx ℤ * P.inertiaDeg ℤ` (from
  `RankIdentity.finrank_field_eq_finrank_int` + the global rank identity
  `RamificationCompat.finrank_kpAdic_eq_global`);
* `kpIntBasis` — an explicit `Module.Basis (Fin (P.ramificationIdx ℤ *
  P.inertiaDeg ℤ)) (QpInt p) (kpInt p P)` (`Module.finBasis` reindexed by
  the finrank identity).

This is the module-level content of "`𝒪_{K_P} ≅ ℤ_p^(e·f)`": the ring of
integers of the completed field `K_P` is free of rank `e_P·f_P` over
`ℤ_p`, the first half of the Session-120 next-lemma
(`kpInt/(p^(k+1)) ≅ (QpInt/(p^(k+1)))^(e·f)`, quotient-freeness corollary
to follow once the generic quotient lemma is in the commons).
-/

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

namespace Submission.Vdw.LocalField

/-- `kpInt p P` is free as a `QpInt p`-module: finite-type torsion-free over
the PID `QpInt p`. -/
instance free_kpInt_QpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Module.Free (QpInt p) (kpInt p P) := by
  haveI : Module.IsTorsionFree (QpInt p) (kpInt p P) := kpInt_torsionFree p P
  exact Module.free_of_finite_type_torsion_free' (R := QpInt p) (M := kpInt p P)

/-- The rank of `kpInt p P` over `QpInt p` equals `P.ramificationIdx ℤ *
P.inertiaDeg ℤ` (= `[K_P : ℚ_p]`): `finrank_field_eq_finrank_int` +
the global rank identity. -/
theorem finrank_kpInt_eq_mul (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Module.finrank (QpInt p) (kpInt p P) = P.ramificationIdx ℤ * P.inertiaDeg ℤ := by
  exact (finrank_field_eq_finrank_int p P).symm.trans (finrank_kpAdic_eq_global p P)

/-- An explicit `QpInt`-basis of `kpInt p P` indexed by `Fin (e·f)` where
`e = P.ramificationIdx ℤ`, `f = P.inertiaDeg ℤ`. -/
noncomputable def kpIntBasis (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Module.Basis (Fin (P.ramificationIdx ℤ * P.inertiaDeg ℤ)) (QpInt p) (kpInt p P) := by
  classical
  let b := Module.finBasis (QpInt p) (kpInt p P)
  exact b.reindex (Fintype.equivFinOfCardEq (by
    simp [finrank_kpInt_eq_mul p P]))

/-- **Quotient freeness (Session-120 next-lemma, module form)**: the
quotient of `kpInt p P` by the `QpInt`-submodule `(p^n)·kpInt` is
`QpInt`-linearly equivalent to `(QpInt ⧸ (p^n))^(e·f)` (rank `e·f`), via
the basis `kpIntBasis` (fleet
`Commons.LinearAlgebra.FreeModule.nonempty_quotient_ideal_free_equiv`). -/
theorem kpInt_quotient_pow_eqv_nonempty (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (n : ℕ) :
    Nonempty ((kpInt p P ⧸ ((Ideal.span ({((p ^ n : ℕ) : QpInt p)} : Set (QpInt p))) • ⊤ :
        Submodule (QpInt p) (kpInt p P))) ≃ₗ[QpInt p]
      (Fin (P.ramificationIdx ℤ * P.inertiaDeg ℤ) → QpInt p ⧸
        (Ideal.span ({((p ^ n : ℕ) : QpInt p)} : Set (QpInt p))))) := by
  classical
  exact Commons.LinearAlgebra.FreeModule.nonempty_quotient_ideal_free_equiv
    (R := QpInt p) (M := kpInt p P) (ι := Fin (P.ramificationIdx ℤ * P.inertiaDeg ℤ))
    (kpIntBasis p P) (Ideal.span ({((p ^ n : ℕ) : QpInt p)} : Set (QpInt p)))

/-- **The ring-quotient identification**: the quotient of `kpInt` by the
principal ideal `(p^n)` is (as a ring) the quotient by the maximal-ideal
power `𝔪^(e·n)` (`kpInt_span_pow_eq_maximalIdeal_pow`), i.e.
`kpInt/(p^n) = kpInt/𝔪^(e·n)`. -/
noncomputable def kpInt_quot_eq_quot_maximalIdeal_pow (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (n : ℕ) :
    (kpInt p P ⧸ (Ideal.span ({((p ^ n : ℕ) : kpInt p P)} : Set (kpInt p P)))) ≃+*
      (kpInt p P ⧸ ((IsLocalRing.maximalIdeal (kpInt p P)) ^ (P.ramificationIdx ℤ * n))) := by
  classical
  exact Ideal.quotEquivOfEq (kpInt_span_pow_eq_maximalIdeal_pow p P n).symm

end Submission.Vdw.LocalField
end
