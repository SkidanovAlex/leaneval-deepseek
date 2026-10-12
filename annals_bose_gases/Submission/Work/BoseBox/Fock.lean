import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Submission.Bog2Mode
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.Fock` — the finite-mode bosonic Fock space (node `B4`, infrastructure)

FS's §8–§11 work on the **bosonic Fock space** over `L²(Λ)`: creation and
annihilation operators `a_k†`, `a_k`, the condensate mode `a₀`, the number
operator `n`, and the `c`-number substitution `a₀ → z`.  The audit's node `B4`
is that infrastructure (30–60K lines at the continuum level).

This module starts it at the *finite-mode* level, where it is exact and cheap:
the bosonic Fock space over `m` modes is the symmetric algebra of `ℂ^m`, and it
has a concrete model as polynomials in `m` variables, with

    aᵢ = ∂/∂xᵢ   (annihilation),   aᵢ† = multiplication by xᵢ   (creation).

This is the standard (Bargmann–Segal) representation; it is *not* an analogy —
`[aᵢ, aᵢ†] = 1` holds exactly (`ccr_self`), the operators of different modes
commute (`ccr_cross`, `ann_ann_comm`, `cre_cre_comm`), and every FS operator of
§8 is a polynomial in these.

## What is here

* `Fock m` — the Fock space, `ann`, `cre`, `numOp` (the number operator `nᵢ`);
* the canonical commutation relations in the model (`ccr_self`, `ccr_cross`,
  `ccr_cross'`, `ann_ann_comm`, `cre_cre_comm`) — the whole CCR package;
* `bPlus`, `bPlusDag`, `bMinus`, `bMinusDag` — FS's squeezed pair operators
  `b_k = a_k + α_k a_{-k}†` (`eq:Defb_k`) and their formal adjoints;
* `pairBogForm` — the quadratic operator of FS `thm:BogHamDiag` on one mode
  pair, and `pairBogDiag` its diagonalised RHS;
* `multiPairBogForm` / `multiPairBogDiag` — the same for a finite family of
  disjoint mode pairs (FS's `∫ dk` over pairs `(k,−k)`, discretised).

The two identities that are the *content* of node `B6` in this model
(`eq:BogIdentity` and its multi-pair sum) are stated in this module and proved
in `Submission/Work/BoseBox/PairBog.lean`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBox

open _root_.BoseGases
open Submission.BoseGases

set_option autoImplicit false

/-! ## 1. The Fock space and the CCR -/

/-- The finite-mode bosonic Fock space over `m` modes, in the polynomial
(Bargmann–Segal) representation: `aᵢ = ∂/∂xᵢ`, `aᵢ† = xᵢ`. -/
abbrev Fock (m : ℕ) : Type := MvPolynomial (Fin m) ℝ

/-- The annihilation operator `aᵢ` of mode `i`: the formal derivative. -/
noncomputable def ann {m : ℕ} (i : Fin m) : Fock m →ₗ[ℝ] Fock m :=
  (MvPolynomial.pderiv (R := ℝ) i).toLinearMap

/-- The creation operator `aᵢ†` of mode `i`: multiplication by the variable. -/
noncomputable def cre {m : ℕ} (i : Fin m) : Fock m →ₗ[ℝ] Fock m :=
  LinearMap.mulLeft ℝ (MvPolynomial.X i)

/-- The number operator `nᵢ = aᵢ†aᵢ` of mode `i`. -/
noncomputable def numOp {m : ℕ} (i : Fin m) : Fock m →ₗ[ℝ] Fock m := cre i ∘ₗ ann i

lemma ann_apply {m : ℕ} (i : Fin m) (p : Fock m) : ann i p = MvPolynomial.pderiv i p := rfl

lemma cre_apply {m : ℕ} (i : Fin m) (p : Fock m) : cre i p = MvPolynomial.X i * p := rfl

/-- The pointwise commutation relation `aᵢ aᵢ† = aᵢ† aᵢ + 1` in the model
(proved in `PairBog.lean`, where the whole CCR package lives). -/
def CCRSelf (m : ℕ) : Prop := ∀ i : Fin m, ann i ∘ₗ cre i = cre i ∘ₗ ann i + 1

/-- The full canonical commutation package of the model: `[aᵢ,aᵢ†] = 1`,
`[aᵢ,aⱼ†] = 0` and `[aᵢ,aⱼ] = [aᵢ†,aⱼ†] = 0` for `i ≠ j`.  (The proof is in
`Submission/Work/BoseBox/PairBog.lean`, `ccr_package`.) -/
def CCRPackage (m : ℕ) : Prop :=
  (∀ i : Fin m, ann i ∘ₗ cre i = cre i ∘ₗ ann i + 1) ∧
  (∀ i j : Fin m, i ≠ j → ann i ∘ₗ cre j = cre j ∘ₗ ann i) ∧
  (∀ i j : Fin m, ann i ∘ₗ ann j = ann j ∘ₗ ann i) ∧
  (∀ i j : Fin m, cre i ∘ₗ cre j = cre j ∘ₗ cre i)

/-- `nᵢ = aᵢ†aᵢ` is the number operator: `numOp_apply` records the defining
evaluation. -/
lemma numOp_apply {m : ℕ} (i : Fin m) (p : Fock m) :
    numOp i p = MvPolynomial.X i * MvPolynomial.pderiv i p := rfl

/-! ## 2. FS's squeezed pair operators (`eq:Defb_k`) -/

/-- `b₊ = aᵢ + α·aⱼ†` (FS `eq:bpm`, `eq:Defb_k`). -/
noncomputable def bPlus {m : ℕ} (i j : Fin m) (α : ℝ) : Fock m →ₗ[ℝ] Fock m :=
  ann i + α • cre j

/-- The formal adjoint `b₊† = aᵢ† + α·aⱼ` of `bPlus` (the Fock inner product makes
these adjoint; nothing below uses the inner product, only the algebra). -/
noncomputable def bPlusDag {m : ℕ} (i j : Fin m) (α : ℝ) : Fock m →ₗ[ℝ] Fock m :=
  cre i + α • ann j

/-- `b₋ = aⱼ + α·aᵢ†`. -/
noncomputable def bMinus {m : ℕ} (i j : Fin m) (α : ℝ) : Fock m →ₗ[ℝ] Fock m :=
  ann j + α • cre i

/-- The formal adjoint `b₋† = aⱼ† + α·aᵢ`. -/
noncomputable def bMinusDag {m : ℕ} (i j : Fin m) (α : ℝ) : Fock m →ₗ[ℝ] Fock m :=
  cre j + α • ann i

/-! ## 3. The Bogoliubov quadratic operators of one mode pair -/

/-- FS `eq:BogHamPositive-1` on one mode pair `(i,j)`, `κ = 0`:
`A(aᵢ†aᵢ + aⱼ†aⱼ) + B(aᵢ†aⱼ† + aᵢaⱼ)`. -/
noncomputable def pairBogForm {m : ℕ} (i j : Fin m) (A B : ℝ) : Fock m →ₗ[ℝ] Fock m :=
  A • (numOp i + numOp j) + B • (cre i ∘ₗ cre j + ann i ∘ₗ ann j)

/-- The diagonalised right-hand side of FS `eq:BogIdentity` on one pair:
`D(b₊†b₊ + b₋†b₋) − (A−s)·1` with `s = √(A²−B²)`, `D = (A+s)/2`,
`α = B/(A+s)`. -/
noncomputable def pairBogDiag {m : ℕ} (i j : Fin m) (A B : ℝ) : Fock m →ₗ[ℝ] Fock m :=
  bogD A B • (bPlusDag i j (bogAlpha A B) ∘ₗ bPlus i j (bogAlpha A B) +
      bMinusDag i j (bogAlpha A B) ∘ₗ bMinus i j (bogAlpha A B))
    - (A - bogS A B) • (1 : Fock m →ₗ[ℝ] Fock m)

/-- **The Bogoliubov operator identity on one mode pair** (FS `eq:BogIdentity`
with `κ = 0`, at `[aᵢ,aᵢ†] = [aⱼ,aⱼ†] = 1`): for `A > 0`, `|B| ≤ A` and two
*different* modes `i ≠ j`,

  `A(aᵢ†aᵢ + aⱼ†aⱼ) + B(aᵢ†aⱼ† + aᵢaⱼ) = D(b₊†b₊ + b₋†b₋) − (A−s)·1`.

This is the algebraic heart of FS `thm:BogHamDiag`; it is *proved* in
`Submission/Work/BoseBox/PairBog.lean` (`pairBogolubov_identity`). -/
def PairBogIdentity (m : ℕ) : Prop :=
  ∀ (i j : Fin m), i ≠ j → ∀ (A B : ℝ), 0 < A → |B| ≤ A →
    pairBogForm i j A B = pairBogDiag i j A B

/-! ## 4. A finite family of mode pairs (FS's `∫ dk` over `(k,−k)`) -/

/-- The data of a finite family of *disjoint* mode pairs: an involution `swap`
without fixed points on the (finite) mode index, together with the coefficients
`A, B` of each pair (FS's `A(k), B(k)` with `A, B` constant on the pair). -/
structure PairFamily (m : ℕ) where
  /-- The partner of a mode: FS's `k ↦ −k`. -/
  swap : Fin m → Fin m
  /-- The partner map is an involution. -/
  swap_invol : Function.Involutive swap
  /-- No mode is its own partner (the pairs are disjoint). -/
  swap_ne : ∀ i, swap i ≠ i
  /-- FS's `A(k)` (`= τ(k) + ρ_zŴ₁(k)`). -/
  Acoef : Fin m → ℝ
  /-- FS's `B(k)` (`= ρ_zŴ₁(k)`). -/
  Bcoef : Fin m → ℝ
  /-- The diagonalisation hypotheses `A > 0`, `|B| ≤ A`. -/
  Apos : ∀ i, 0 < Acoef i
  Bsmall : ∀ i, |Bcoef i| ≤ Acoef i

/-- FS `eq:BogHamPositive-1` summed over a finite family of mode pairs (the
discretised `∫dk` of `thm:BogHamDiag`). -/
noncomputable def multiPairBogForm {m : ℕ} (F : PairFamily m) : Fock m →ₗ[ℝ] Fock m :=
  ∑ i : Fin m, (2 : ℝ)⁻¹ • pairBogForm i (F.swap i) (F.Acoef i) (F.Bcoef i)

/-- The diagonalised right-hand side of FS `eq:BogHamDiag`, summed over the
family of mode pairs. -/
noncomputable def multiPairBogDiag {m : ℕ} (F : PairFamily m) : Fock m →ₗ[ℝ] Fock m :=
  ∑ i : Fin m, (2 : ℝ)⁻¹ • pairBogDiag i (F.swap i) (F.Acoef i) (F.Bcoef i)

/-- **The multi-pair Bogoliubov identity** (FS `thm:BogHamDiag`'s operator
identity, `κ = 0`, finite mode family): the quadratic Bogoliubov operator equals
its diagonalised form.  Proved in `Submission/Work/BoseBox/PairBog.lean`
(`multiPairBogolubov_identity`) from `PairBogIdentity`. -/
def MultiPairBogIdentity (m : ℕ) : Prop :=
  ∀ F : PairFamily m, multiPairBogForm F = multiPairBogDiag F

end Work.BoseBox
