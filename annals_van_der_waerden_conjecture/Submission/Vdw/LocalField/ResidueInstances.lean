import Mathlib
import Submission.Vdw.LocalField.Completion
import Submission.Vdw.LocalField.Unramified
import Submission.Vdw.LocalField.ResidueChar
import Submission.Commons.Algebra.CharP.charP_of_ringEquiv

open scoped NumberField
open IsDedekindDomain
open IsLocalRing

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

/-!
# Local-field chapter (stone 3, groundwork): ring-theoretic instances at the
completion residue `kpInt p P ⧸ 𝔪`

For the Teichmüller-lift step of stone 3 the valuation ring `R := kpInt p P`
of the completion `K_P` must be used with its maximal ideal
`I := maximalIdeal (kpInt p P)`.  `Perfection.teichmuller` needs
`[CharP (R ⧸ I) p]` (plus `[IsAdicComplete I R]` and, for the finite-field
section `κ → R`, that the residue is finite / perfect).  This module supplies
the characteristic and finiteness data at `kpInt ⧸ 𝔪`:

* `charP_of_ringEquiv` (generic, local copy — the fleet version lands as
  `Commons.Algebra.CharP.charP_of_ringEquiv`): `CharP` is invariant under
  ring equivalences;
* `kpIntResidueField` — `Field (kpInt p P ⧸ 𝔪)` (maximal-ideal quotient of
  the DVR `kpInt p P`);
* `kpIntResidue_charP` — the completion residue has characteristic `p`
  (transport of `charP_quotient_of_liesOver` along
  `completion_residueField_equiv`);
* `kpIntResidue_finite` / `kpIntResidue_perfectField` — the residue is a
  finite field, hence perfect (`PerfectField.ofFinite`).

The remaining Teichmüller input — `IsAdicComplete 𝔪 (kpInt p P)` — is a
separate stone (no Mathlib instance registers it for `adicCompletionIntegers`;
the `IsNonarchimedeanLocalField` API covers `Valued.integer` of local fields
but no `IsNonarchimedeanLocalField (adicCompletion K v)` instance exists).
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The residue ring `kpInt p P ⧸ 𝔪` of the completion is a field (a
maximal-ideal quotient of the commutative ring `kpInt p P`, `𝔪` maximal since
`kpInt p P` is a local ring). -/
noncomputable instance kpIntResidueField (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Field (kpInt p P ⧸ maximalIdeal (kpInt p P)) :=
  Ideal.Quotient.field (maximalIdeal (kpInt p P))

/-- The completion residue `kpInt p P ⧸ 𝔪` has characteristic `p`:
transport of the base-prime residue character `CharP (𝓞 K ⧸ P) p`
(`charP_quotient_of_liesOver`) along the ring equivalence
`completion_residueField_equiv`, crossing the `asIdeal` spelling via
`Ideal.quotEquivOfEq (kprime_asIdeal)`. -/
noncomputable instance kpIntResidue_charP (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    CharP (kpInt p P ⧸ maximalIdeal (kpInt p P)) p := by
  classical
  obtain ⟨e⟩ := completion_residueField_equiv (K := K) (p := p) (P := P)
  -- e : kpInt p P ⧸ maximalIdeal (kpInt p P) ≃+* 𝓞 K ⧸ (kprime p P).asIdeal
  have j : 𝓞 K ⧸ P ≃+* 𝓞 K ⧸ (kprime p P).asIdeal :=
    Ideal.quotEquivOfEq (kprime_asIdeal (K := K) p P).symm
  haveI hcpP : CharP (𝓞 K ⧸ P) p := charP_quotient_of_liesOver (K := K) (p := p) P
  haveI hcpCod : CharP (𝓞 K ⧸ (kprime p P).asIdeal) p := Commons.Algebra.CharP.charP_of_ringEquiv j p
  exact Commons.Algebra.CharP.charP_of_ringEquiv e.symm p

/-- The completion residue is finite (isomorphic, by
`completion_residueField_equiv`, to the finite residue field `𝓞 K ⧸ P` of
the base prime). -/
noncomputable instance kpIntResidue_finite (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Finite (kpInt p P ⧸ maximalIdeal (kpInt p P)) := by
  classical
  obtain ⟨e⟩ := completion_residueField_equiv (K := K) (p := p) (P := P)
  have j : 𝓞 K ⧸ P ≃+* 𝓞 K ⧸ (kprime p P).asIdeal :=
    Ideal.quotEquivOfEq (kprime_asIdeal (K := K) p P).symm
  haveI hfinP : Finite (𝓞 K ⧸ P) := inferInstance
  haveI hfinCod : Finite (𝓞 K ⧸ (kprime p P).asIdeal) := Finite.of_equiv (𝓞 K ⧸ P) j
  exact Finite.of_equiv (𝓞 K ⧸ (kprime p P).asIdeal) e.symm

/-- The completion residue is a perfect field (finite, hence perfect). -/
noncomputable instance kpIntResidue_perfectField (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    PerfectField (kpInt p P ⧸ maximalIdeal (kpInt p P)) := by
  infer_instance
/-- The completion residue has `p^f` elements, `f := P.inertiaDeg ℤ`
— the completion identifies with the base residue field
(`completion_residueField_equiv`), whose cardinality is `residue_card`. -/
theorem kpIntResidue_card (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Nat.card (kpInt p P ⧸ maximalIdeal (kpInt p P)) = p ^ P.inertiaDeg ℤ := by
  classical
  obtain ⟨e⟩ := completion_residueField_equiv (K := K) (p := p) (P := P)
  have j : 𝓞 K ⧸ P ≃+* 𝓞 K ⧸ (kprime p P).asIdeal :=
    Ideal.quotEquivOfEq (kprime_asIdeal (K := K) p P).symm
  calc
    Nat.card (kpInt p P ⧸ maximalIdeal (kpInt p P))
        = Nat.card (𝓞 K ⧸ (kprime p P).asIdeal) := Nat.card_congr e.toEquiv
    _ = Nat.card (𝓞 K ⧸ P) := Nat.card_congr j.toEquiv.symm
    _ = p ^ P.inertiaDeg ℤ := by simpa [kResidue] using (residue_card (K := K) p P)

end
end Submission.Vdw.LocalField
