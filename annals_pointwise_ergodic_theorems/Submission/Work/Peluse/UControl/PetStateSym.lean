import Submission.Work.Peluse.UControl.PetStepChain

/-!
# Symbolic PET states (Peluse's weight vector, computed over the parameter ring)

`NOTES_petChapter5.md` §10 records the design finding that the weight vector of Peluse's §4 must be
read at a **generic** parameter: her shifts live in `ℤ[a_1,…,a_k][y]`, where the parameters
introduced so far are formal variables, and `V j` counts *distinct leading coefficients* — a
symbolic condition (two leading-coefficient polynomials may coincide at a special `a`, and two
slot polynomials may have the same degree over the ring but not after specialisation).

* `PetStateSym k` — the shifts as polynomials over `MvPolynomial (Fin k) ℤ`;
* `PetStateSym.weight` — Peluse's weight vector `V j` (the number of *distinct* leading
  coefficients among the slots of degree `j`), computed over the ring;
* `PetStateSym.step` — the PET step, which introduces the `k`-th formal parameter (so a state with
  `k` parameters goes to one with `k+1`);
* `PetStateSym.evalAt` — the specialisation to a concrete parameter, as a `PetStateP`.

The analytic half of the chain (`PetState.lam_step`, `petChainDrop`, `petChainEvalStep`,
`petChainMD`) is independent of this file; the weight lemmas (`petChainWeight`, `petChainWeightTop`,
`petChainWeightDeg`) will have to be re-stated for `PetStateSym`, where their `huniq`-type
hypotheses become *symbolic* non-vanishing statements.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl.PetStep

open Polynomial

/-- A **symbolic PET state** with `k` formal parameters: the shifts are polynomials in `y` whose
coefficients are polynomials in the `k` parameters introduced so far.  (The slot functions and the
base function are analytic and live in the concrete state `PetStateP`, see `PetStateSym.evalAt`.) -/
structure PetStateSym (k : ℕ) where
  ι : Type
  finι : Fintype ι
  decι : DecidableEq ι
  P : ι → Polynomial (MvPolynomial (Fin k) ℤ)

attribute [instance] PetStateSym.finι PetStateSym.decι

/-- Peluse's **weight vector** (`Definition 4.3`): `V j` is the number of *distinct leading
coefficients* among the slots whose shift has degree `j`, read over the parameter ring. -/
noncomputable def PetStateSym.weight {k : ℕ} (S : PetStateSym k) (d : ℕ) : Fin (d + 1) → ℕ :=
  fun j => (((Finset.univ : Finset S.ι).filter
      (fun i => (S.P i).natDegree = (j : ℕ))).image (fun i => (S.P i).leadingCoeff)).card

/-- The **PET step**: the slot `(i,ε)` gets `P_i(X + ε·h) - P_{i₀}(X)` where `h` is the *new* formal
parameter (the `k`-th one, so the result has `k+1` parameters). -/
noncomputable def PetStateSym.step {k : ℕ} (S : PetStateSym k) (i₀ : S.ι) :
    PetStateSym (k + 1) where
  ι := {j : S.ι × Bool // j ≠ (i₀, false)}
  finι := inferInstance
  decι := inferInstance
  P := fun j =>
    (((S.P j.1.1).map (MvPolynomial.rename Fin.castSucc).toRingHom).comp
        (Polynomial.X + Polynomial.C
          (if j.1.2 then MvPolynomial.X (Fin.last k) else 0)))
      - (S.P i₀).map (MvPolynomial.rename Fin.castSucc).toRingHom

/-- The **specialisation** of a symbolic state at a concrete parameter: the coefficients are
evaluated by `MvPolynomial.eval a`, giving a pointwise `PetStateP`. -/
noncomputable def PetStateSym.evalAt {k : ℕ} (S : PetStateSym k) (a : Fin k → ℤ)
    (F : S.ι → ℤ → ℂ) (f : ℤ → ℂ) : PetStateP where
  Ω := Fin 1
  ι := S.ι
  finΩ := inferInstance
  decΩ := inferInstance
  finι := S.finι
  decι := S.decι
  P := fun i _ => (S.P i).map (MvPolynomial.eval a)
  f := fun _ => f
  F := F
  ν := fun _ => 1

end Work.Peluse.UControl.PetStep
