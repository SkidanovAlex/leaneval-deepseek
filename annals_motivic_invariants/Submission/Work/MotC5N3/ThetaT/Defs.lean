import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.ASRul.sAS2_ruling_mem
import Submission.Work.MotAS.ASRul.kernel_basis
import Submission.Work.MotAS.ASRulV2.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.ThetaT.Defs` — verbatim copies of the AS ruling presentation (unblocking shim)

⚠ **Temporary shim, 2026-10-06.**  The module `Submission.Work.MotC5N3.ASRulingMainV2Gen`, which
defines `Work.MotC5N3.ASrulA`, `ASrulEpsA`, `ASrulTheta`, currently has no `.olean` (its file
`Submission/Work/MotAS/ASRulingMain.lean`, which sits in the import closure via
`MotC5N3.hparam_kernel`, does not compile — see `NOTE_BLOCKER_ASRulingMain.md`).  The definitions
below are **copies with the same bodies** (up to the copied `abbrev`/`def` names), in the private
namespace `Work.MotC5N3.ThetaT`, so that the certificate `ASrulTheta (sAS2 a b g) = 0` can be
developed and verified now; once the blocker is lifted the theorem is re-stated for the original
names (the bodies are syntactically equal, so the statements are definitionally equal).

The naturality lemmas are copies of `Work.MotAS.Nodes.map_kbRv` / `map_kbRw` / `map_zcubAS`
(same proofs) and of the scratch proof `_asrulwork/dev2.lean` (`map_sAS2`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.MotC5N3.ThetaT

open MvPolynomial

section Defs

variable {K : Type} [Field K]

/-- Verbatim copy of `Work.MotC5N3.ASrulA`. -/
abbrev ASrulAT (a b g : K) : Type :=
  MvPolynomial (Fin 3) K ⧸ Ideal.radical (Work.MotAS.ZIAS a b g)

/-- Verbatim copy of `Work.MotC5N3.ASrulEpsA`. -/
noncomputable def ASrulEpsAT (a b g : K) : ASrulAT a b g :=
  Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g)) (Work.MotAS.ASRul.kbRw a b g 4)

end Defs

section Theta

variable {K : Type} [Field K] [CharP K 5]

/-- Verbatim copy of `Work.MotC5N3.ASrulTheta`. -/
noncomputable def ASrulThetaT (a b g : K) (hDZ : IsDomain (ASrulAT a b g)) :
    MvPolynomial (Fin 3) K →ₐ[K] Localization.Away (Polynomial.C (ASrulEpsAT a b g)) := by
  letI := hDZ
  let R := Polynomial (ASrulAT a b g)
  let S := Localization.Away (Polynomial.C (ASrulEpsAT a b g))
  exact MvPolynomial.aeval (fun j : Fin 3 =>
    IsLocalization.mk' S
      (Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
          (Work.MotAS.ASRul.kbRv a b g (Work.MotAS.asCh3 j))) * Polynomial.X
        + Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
          (Work.MotAS.ASRul.kbRw a b g (Work.MotAS.asCh3 j))))
      ⟨Polynomial.C (ASrulEpsAT a b g), Submonoid.mem_powers _⟩)

end Theta

section Abbrevs

variable {K : Type} [Field K] (a b g : K)

/-- The polynomial ring `A[T]` over the AS residual curve. -/
abbrev ASrulRT : Type := Polynomial (ASrulAT a b g)

/-- The normaliser `ε` as an element of `A[T]`. -/
noncomputable abbrev ASrulEpsRT : ASrulRT a b g := Polynomial.C (ASrulEpsAT a b g)

/-- The localisation `A[T][1/ε]` in which the ruling presentation lands. -/
abbrev ASrulST : Type := Localization.Away (ASrulEpsRT a b g)

/-- The fraction field of `A[T]`, in which the certificate is proved. -/
abbrev ASrulKT : Type := FractionRing (ASrulRT a b g)

/-- The `j`-th generator image of the ruling presentation: `C (kbRv (j+1))·T + C (kbRw (j+1))`. -/
noncomputable abbrev ASrulQT (j : Fin 3) : ASrulRT a b g :=
  Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
      (Work.MotAS.ASRul.kbRv a b g (Work.MotAS.asCh3 j))) * Polynomial.X
    + Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
      (Work.MotAS.ASRul.kbRw a b g (Work.MotAS.asCh3 j)))

/-- The image in the function field of the first ruling vector at the generic point. -/
noncomputable abbrev ASrulWT (k : Fin 5) : ASrulKT a b g :=
  algebraMap (ASrulAT a b g) (ASrulKT a b g)
    (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
      (Work.MotAS.ASRul.kbRv a b g k))

/-- The image in the function field of the second ruling vector at the generic point. -/
noncomputable abbrev ASrulVT (k : Fin 5) : ASrulKT a b g :=
  algebraMap (ASrulAT a b g) (ASrulKT a b g)
    (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
      (Work.MotAS.ASRul.kbRw a b g k))

end Abbrevs

section Naturality

/-! ## Naturality of the AS link data under a ring homomorphism -/

/-- Naturality of the first AS ruling vector (copy of `Work.MotAS.Nodes.map_kbRv`). -/
theorem map_kbRvT {K L : Type*} [Field K] [Field L] (φ : K →+* L) (a b g : K) (i : Fin 5) :
    MvPolynomial.map φ (Work.MotAS.ASRul.kbRv a b g i)
      = Work.MotAS.ASRul.kbRv (φ a) (φ b) (φ g) i := by
  fin_cases i <;> simp [Work.MotAS.ASRul.kbRv, map_ofNat]

/-- Naturality of the second AS ruling vector (copy of `Work.MotAS.Nodes.map_kbRw`). -/
theorem map_kbRwT {K L : Type*} [Field K] [Field L] (φ : K →+* L) (a b g : K) (i : Fin 5) :
    MvPolynomial.map φ (Work.MotAS.ASRul.kbRw a b g i)
      = Work.MotAS.ASRul.kbRw (φ a) (φ b) (φ g) i := by
  fin_cases i <;> simp [Work.MotAS.ASRul.kbRw, map_ofNat]

/-- Naturality of the residual-curve cubics (copy of `Work.MotAS.Nodes.map_zcubAS`). -/
theorem map_zcubAST {K L : Type*} [Field K] [Field L] (φ : K →+* L) (a b g : K) (j : Fin 5) :
    MvPolynomial.map φ (Work.MotAS.zcubAS a b g j)
      = Work.MotAS.zcubAS (φ a) (φ b) (φ g) j := by
  have h := congrFun (Work.MotAS.KleinTwScalarAS_map_kleinRAS
    (φ := MvPolynomial.map φ) (a := MvPolynomial.C a) (b := MvPolynomial.C b)
    (g := MvPolynomial.C g)
    (z := (![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0] :
      Fin 5 → MvPolynomial (Fin 3) K))) j
  rw [MvPolynomial.map_C, MvPolynomial.map_C, MvPolynomial.map_C] at h
  have hz : (fun i => MvPolynomial.map φ ((![1, MvPolynomial.X 0, MvPolynomial.X 1,
        MvPolynomial.X 2, 0] : Fin 5 → MvPolynomial (Fin 3) K) i))
      = (![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0] :
          Fin 5 → MvPolynomial (Fin 3) L) := by
    funext i
    fin_cases i <;> simp
  rw [hz] at h
  exact h.symm

/-- Naturality of the source ruling quintic (scratch proof of `_asrulwork/dev2.lean`). -/
theorem map_sAS2T {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (a b g : A) :
    (Work.MotAS.sAS2 (φ a) (φ b) (φ g)) = MvPolynomial.map φ (Work.MotAS.sAS2 a b g) := by
  have h1 : MvPolynomial.map φ (Work.MotAS.sAS2 a b g)
      = Work.MotAS.kleinSecAS (MvPolynomial.C (φ a)) (MvPolynomial.C (φ b))
          (MvPolynomial.C (φ g))
          (Work.MotAS.kleinStereoAS (MvPolynomial.C (φ a)) (MvPolynomial.C (φ b))
            (Work.MotAS.pAS0 B) (Work.MotK.chart3 B)) := by
    rw [Work.MotAS.sAS2]
    rw [← Work.MotAS.KleinTwScalarAS_map_kleinSecAS (MvPolynomial.map φ)
      (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (Work.MotAS.kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b)
        (Work.MotAS.pAS0 A) (Work.MotK.chart3 A))]
    congr 2
    · rw [MvPolynomial.map_C]
    · rw [MvPolynomial.map_C]
    · rw [MvPolynomial.map_C]
    · rw [← Work.MotAS.map_kleinStereoAS (MvPolynomial.map φ) (MvPolynomial.C a)
        (MvPolynomial.C b) (Work.MotAS.pAS0 A) (Work.MotK.chart3 A)]
      congr 1
      · rw [MvPolynomial.map_C]
      · rw [MvPolynomial.map_C]
      · funext i; fin_cases i <;> simp [Work.MotAS.pAS0]
      · funext i; fin_cases i <;> simp [Work.MotK.chart3]
  rw [h1]
  rfl

end Naturality

end Work.MotC5N3.ThetaT
