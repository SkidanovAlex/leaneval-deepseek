/-
# The `𝒪[F]`-action on the Lubin–Tate torsion points `Λ_n`

Milne, *Classical Field Theory*, §I.3: for `a ∈ 𝒪[F]` and a `π^n`-torsion point `x` of the
Lubin–Tate group of `π`, the point `a · x = [a](x)` is again `π^n`-torsion.  This is what makes
`Λ_n` an `𝒪[F]`-module — with the Lubin–Tate group law as addition and the `a`-multiplication
series `[a]` as scalar multiplication — and it is the input to the isomorphism
`Λ_n ≅ (𝒪[F]/π^n)^+` of Milne's Theorem I.3.1.

This file proves `NK.LocalReciprocityLubinTate.Eval.smulDiv_mem`: for `x ∈ Λ_n` and `a ∈ 𝒪[F]`,
the point `a · x = evMap x ([a]_n)` of `Eval/TorsionAction.lean` again lies in `Λ_n`, i.e.
`f^{(n)}(a · x) = 0` for the standard series `f(T) = πT + T^q`.

## The proof

Everything happens in the finite ring `T_n = 𝒪[F][T]/(f^{(n)}(T))` of `Eval/TorsionRing.lean`.
Write `E = evalTau : 𝒪[F]⟦X⟧ →+* T_n` for Milne's evaluation at `τ` and

`Φ_k = M.action (π^k) = [π^k] ∈ 𝒪[F]⟦X⟧`

for the `π^k`-multiplication series of the Lubin–Tate module.  The core statement is the
**bridge**

  `f^{(k)}(E ψ) = E (ψ ∘ Φ_k)`     (`ψ` of zero constant coefficient),

identifying the polynomial iterate `f^{(k)}` of `f = πX + X^q` with the substituted multiplication
series `Φ_k`.  It is proved by induction on `k`: the successor step is the compatibility of
substitution with the polynomial composition `f^{(k+1)} = f^{(k)} ∘ f` (`LTpolyIter_succ`,
`Polynomial.aeval_comp`) and the equation `subst1 ψ [π] = π·ψ + ψ^q` in which the hypothesis
`M.toLaw.piEndo = πX + X^q` is used.  The induction is closed by Milne's substitution rule

  `E (ψ ∘ φ) = eval₂ ![E ψ] φ`     (`MvPowerSeries.eval₂_subst`),

i.e. `evalTau_subst'` below.

Two inputs complete the argument:

* `E Φ_n = f^{(n)}(τ) = 0`, i.e. `τ` is a `π^n`-torsion point (`LTtorsionRing.tau_spec`);
* the `𝒪[F]`-module axiom `[a] ∘ [π^n] = [π^n] ∘ [a] = [a π^n]` (`M.action_mul`) together with the
  classical computation rule for evaluating a power series at `0`: a series of zero constant
  coefficient takes the value `0` at `0` (`eval₂_zero_eq`).

Finally, `evMap x` transports the identity from `T_n` to the algebraic closure, which is the
naturality `Polynomial.hom_eval₂` of polynomial evaluation under a ring homomorphism
(`aeval_evMap`).
-/
import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Eval.TorsionAction
import Submission.NK.LocalReciprocityLubinTate.LubinTate.ModuleAux

namespace NK.LocalReciprocityLubinTate.Eval

noncomputable section

universe u

open scoped ValuativeRel

open NK.LocalReciprocityLubinTate.LubinTate (subst1 subst1_apply subst1_comp subst1_self
  subst1_X subst1_constantCoeff hasSubst_vec1)

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-! ### Milne's evaluation at `τ` -/

/-- Milne's evaluation at the torsion class `τ`, as a function: `evalTau` is by definition the
evaluation homomorphism of `MvPowerSeries`, so it is `eval₂` at the constant family `τ`
(`MvPowerSeries.coe_eval₂Hom`). -/
private theorem evalTau_apply (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (f : MvPowerSeries (Fin 1) (O F)) :
    evalTau π hπ q n hq f
      = MvPowerSeries.eval₂ (algebraMap (O F) (LTtorsionRing F π q n))
          (fun _ : Fin 1 => LTtorsionRing.tau π q n) f := by
  haveI : CompleteSpace (LTtorsionRing F π q n) := completeSpace_ltTorsionRing π hπ q n hq
  haveI : T2Space (LTtorsionRing F π q n) := t2Space_ltTorsionRing π hπ q n hq
  rw [evalTau, MvPowerSeries.coe_eval₂Hom]

private theorem evalTau_X (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q) :
    evalTau π hπ q n hq (MvPowerSeries.X 0) = LTtorsionRing.tau π q n := by
  rw [evalTau_apply, MvPowerSeries.eval₂_X]

private theorem evalTau_C (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q) (c : O F) :
    evalTau π hπ q n hq (MvPowerSeries.C c)
      = algebraMap (O F) (LTtorsionRing F π q n) c := by
  rw [evalTau_apply, MvPowerSeries.eval₂_C]

/-- **Milne's substitution rule**, at the torsion class `τ`: evaluating the composite of two
power series at `τ` is evaluating the outer series at the value of the inner one.  This is
`MvPowerSeries.eval₂_subst` for the family `![ψ]` and the point `τ`, which admits evaluation
(`hasEval_ltTorsionRing`). -/
private theorem evalTau_subst' (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (ψ φ : MvPowerSeries (Fin 1) (O F))
    (hψ : MvPowerSeries.HasSubst (![ψ] : Fin 1 → MvPowerSeries (Fin 1) (O F))) :
    evalTau π hπ q n hq (MvPowerSeries.subst ![ψ] φ)
      = MvPowerSeries.eval₂ (algebraMap (O F) (LTtorsionRing F π q n))
          (fun _ : Fin 1 => evalTau π hπ q n hq ψ) φ := by
  haveI : CompleteSpace (LTtorsionRing F π q n) := completeSpace_ltTorsionRing π hπ q n hq
  haveI : T2Space (LTtorsionRing F π q n) := t2Space_ltTorsionRing π hπ q n hq
  have hb : MvPowerSeries.HasEval (fun _ : Fin 1 => LTtorsionRing.tau π q n) :=
    hasEval_ltTorsionRing π q n hq
  rw [evalTau_apply]
  rw [MvPowerSeries.eval₂_subst hψ hb]
  congr 1
  funext s
  fin_cases s
  simp only [Matrix.cons_val_fin_one]
  rw [evalTau_apply]

/-- **Evaluation at `0` of a power series**: a power series of zero constant coefficient takes the
value `0` at `0`.  Equivalently, for an arbitrary series `f`, substitution of `0` produces its
constant coefficient.

This is Milne's computation `[a](0) = 0`, and it is the reason the action of `𝒪[F]` fixes `0 ∈ Λ_n`.
The proof substitutes `0` into `f` first (`MvPowerSeries.subst_zero_eq_C_constantCoeff`) and then
evaluates the resulting constant series at the *torsion* point `τ`, where evaluation is available;
Milne's substitution rule (`MvPowerSeries.eval₂_subst`) computes both sides. -/
private theorem eval₂_zero_eq (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (f : MvPowerSeries (Fin 1) (O F)) :
    MvPowerSeries.eval₂ (algebraMap (O F) (LTtorsionRing F π q n))
        (fun _ : Fin 1 => (0 : LTtorsionRing F π q n)) f
      = algebraMap (O F) (LTtorsionRing F π q n) (MvPowerSeries.constantCoeff f) := by
  haveI : CompleteSpace (LTtorsionRing F π q n) := completeSpace_ltTorsionRing π hπ q n hq
  haveI : T2Space (LTtorsionRing F π q n) := t2Space_ltTorsionRing π hπ q n hq
  have hb : MvPowerSeries.HasEval (fun _ : Fin 1 => LTtorsionRing.tau π q n) :=
    hasEval_ltTorsionRing π q n hq
  have hzero : MvPowerSeries.eval₂ (algebraMap (O F) (LTtorsionRing F π q n))
      (fun _ : Fin 1 => LTtorsionRing.tau π q n) (0 : MvPowerSeries (Fin 1) (O F)) = 0 := by
    simp only [← MvPolynomial.coe_zero]
    rw [MvPowerSeries.eval₂_coe]
    simp
  have h := MvPowerSeries.eval₂_subst (R := O F) (S := O F) (T := LTtorsionRing F π q n)
    (a := (0 : Fin 1 → MvPowerSeries (Fin 1) (O F)))
    (b := fun _ : Fin 1 => LTtorsionRing.tau π q n) MvPowerSeries.HasSubst.zero hb f
  rw [MvPowerSeries.subst_zero_eq_C_constantCoeff] at h
  simp only [MvPowerSeries.map_C] at h
  rw [MvPowerSeries.eval₂_C] at h
  simp only [Pi.zero_apply, hzero] at h
  exact h.symm

/-! ### The `π^k`-multiplication series `Φ_k = [π^k]` -/

/-- The `a`-multiplication series `[a]` of a Lubin–Tate module has zero constant coefficient: it
is congruent to `aX` modulo degree two (`M.action_linear`). -/
private theorem action_constantCoeff_zero (π : O F) (q : ℕ) (M : LubinTateModule (O F) π q)
    (a : O F) : MvPowerSeries.constantCoeff (M.action a) = 0 := by
  have h := M.action_linear a
  have h0 : MvPowerSeries.coeff (0 : Fin 1 →₀ ℕ) (M.action a)
      = MvPowerSeries.coeff (0 : Fin 1 →₀ ℕ)
          (MvPowerSeries.C a * MvPowerSeries.X 0) :=
    h 0 (by simp)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [h0, MvPowerSeries.coeff_C_mul]
  simp

/-- **The recurrence of the `π^k`-multiplication series**: `Φ_{k+1} = Φ_k ∘ [π]`, i.e.
`[π^{k+1}] = [π^k] ∘ [π]`.  This is the multiplicativity `M.action_mul` of the `𝒪[F]`-module
structure applied to `π ^ (k+1) = π^k · π`. -/
private theorem action_pow_succ (π : O F) (q : ℕ) (M : LubinTateModule (O F) π q) (k : ℕ) :
    M.action (π ^ (k + 1)) = subst1 (M.action π) (M.action (π ^ k)) := by
  rw [pow_succ, M.action_mul, subst1_apply]

/-- **Substituting into `[π]`**: for a series `ψ` of zero constant coefficient,
`subst1 ψ [π] = π·ψ + ψ^q`.  This is the standard series `f(T) = πT + T^q` of the Lubin–Tate
module (`hpi`), substituted. -/
private theorem subst1_action_pi (π : O F) (q : ℕ) (M : LubinTateModule (O F) π q)
    (hpi : M.toLaw.piEndo = piXAddXq π q) (ψ : MvPowerSeries (Fin 1) (O F))
    (hψ : MvPowerSeries.constantCoeff ψ = 0) :
    subst1 ψ (M.action π) = MvPowerSeries.C π * ψ + ψ ^ q := by
  have hsub : MvPowerSeries.HasSubst (![ψ] : Fin 1 → MvPowerSeries (Fin 1) (O F)) :=
    hasSubst_vec1 hψ
  have hpi' : M.action π
      = MvPowerSeries.C π * MvPowerSeries.X 0 + MvPowerSeries.X 0 ^ q := by
    rw [M.action_pi, hpi]
    rfl
  rw [hpi', subst1_apply, MvPowerSeries.subst_add hsub, MvPowerSeries.subst_mul hsub,
    MvPowerSeries.subst_pow hsub, MvPowerSeries.subst_C, MvPowerSeries.subst_X hsub]
  simp only [Matrix.cons_val_fin_one]

/-- **The standard series `πX + X^q` computed at `E ψ`**: evaluating the polynomial `πX + X^q` at
the value `E ψ` of a series `ψ` of zero constant coefficient agrees with evaluating the series
`ψ ∘ [π]` at `τ`. -/
private theorem aeval_LTpoly_evalTau (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (O F) π q) (hpi : M.toLaw.piEndo = piXAddXq π q)
    (ψ : MvPowerSeries (Fin 1) (O F)) (hψ : MvPowerSeries.constantCoeff ψ = 0) :
    Polynomial.aeval (evalTau π hπ q n hq ψ) (LTpoly π q)
      = evalTau π hπ q n hq (subst1 ψ (M.action π)) := by
  rw [subst1_action_pi π q M hpi ψ hψ]
  simp only [map_add, map_mul, map_pow, evalTau_C, LTpoly, Polynomial.aeval_C,
    Polynomial.aeval_X]

/-- **The bridge between the polynomial iterate and the substituted multiplication series.**

For every series `ψ` of zero constant coefficient and every `k`,
`f^{(k)}(E ψ) = E (ψ ∘ [π^k])`, i.e. the polynomial iterate `f^{(k)}` of `πX + X^q` and the
`k`-th iterate `Φ_k = [π^k]` of the formal group match under Milne's evaluation at `τ`.

The induction is over `k`, keeping `ψ` universally quantified so that the successor step may apply
the hypothesis to the series `ψ ∘ [π]`. -/
private theorem bridge (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (O F) π q) (hpi : M.toLaw.piEndo = piXAddXq π q)
    (ψ : MvPowerSeries (Fin 1) (O F)) (hψ : MvPowerSeries.constantCoeff ψ = 0) (k : ℕ) :
    Polynomial.aeval (evalTau π hπ q n hq ψ) (LTpolyIter π q k)
      = evalTau π hπ q n hq (subst1 ψ (M.action (π ^ k))) := by
  revert ψ
  induction k with
  | zero =>
    intro ψ hψ
    rw [LTpolyIter_zero, Polynomial.aeval_X, pow_zero, M.action_one,
      subst1_self (hasSubst_vec1 hψ)]
  | succ k ih =>
    intro ψ hψ
    rw [LTpolyIter_succ, Polynomial.aeval_comp]
    rw [aeval_LTpoly_evalTau π hπ q n hq M hpi ψ hψ]
    rw [ih (subst1 ψ (M.action π))
      (subst1_constantCoeff hψ (action_constantCoeff_zero π q M π))]
    rw [action_pow_succ π q M k]
    rw [← subst1_comp
      (hasSubst_vec1 (action_constantCoeff_zero π q M π)) (hasSubst_vec1 hψ)]

/-- **`τ` is a `π^n`-torsion point**: `E Φ_n = f^{(n)}(τ) = 0`.**  This is the bridge at
`ψ = X` together with the defining property of `τ` (`LTtorsionRing.tau_spec`). -/
private theorem evalTau_action_pow_eq_zero (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (O F) π q) (hpi : M.toLaw.piEndo = piXAddXq π q) :
    evalTau π hπ q n hq (M.action (π ^ n)) = 0 := by
  have hbr := bridge π hπ q n hq M hpi (MvPowerSeries.X (0 : Fin 1))
    (MvPowerSeries.constantCoeff_X (0 : Fin 1)) n
  have hsub : subst1 (MvPowerSeries.X (0 : Fin 1)) (M.action (π ^ n)) = M.action (π ^ n) :=
    subst1_X
  rw [← hsub, ← hbr, evalTau_X]
  exact LTtorsionRing.tau_spec π q n

/-- **The main computation in `T_n`**: for the Lubin–Tate module `M` of the standard series,
`[a](τ)`, i.e. the class in `T_n` of the `a`-multiplication series at `τ`, is again a
`π^n`-torsion point: `f^{(n)}(E [a]) = 0`.

The proof uses the bridge at `ψ = [a]`, the commutativity `[a] ∘ [π^n] = [π^n] ∘ [a] = [aπ^n]` of
the `𝒪[F]`-module structure, Milne's substitution rule, and `E Φ_n = 0`. -/
private theorem aeval_actionTau_LTpolyIter (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (O F) π q) (hpi : M.toLaw.piEndo = piXAddXq π q) (a : O F) :
    Polynomial.aeval (evalTau π hπ q n hq (M.action a)) (LTpolyIter π q n) = 0 := by
  rw [bridge π hπ q n hq M hpi (M.action a) (action_constantCoeff_zero π q M a) n]
  have hcomm : subst1 (M.action a) (M.action (π ^ n))
      = subst1 (M.action (π ^ n)) (M.action a) := by
    rw [subst1_apply, subst1_apply, ← M.action_mul (π ^ n) a, ← M.action_mul a (π ^ n),
      mul_comm (π ^ n) a]
  rw [hcomm, subst1_apply]
  rw [evalTau_subst' π hπ q n hq (M.action (π ^ n)) (M.action a)
    (hasSubst_vec1 (action_constantCoeff_zero π q M (π ^ n)))]
  have hfam : (fun _ : Fin 1 => evalTau π hπ q n hq (M.action (π ^ n)))
      = (fun _ : Fin 1 => (0 : LTtorsionRing F π q n)) :=
    funext fun _ => evalTau_action_pow_eq_zero π hπ q n hq M hpi
  rw [hfam, eval₂_zero_eq π hπ q n hq, action_constantCoeff_zero π q M a]
  simp

/-! ### Transport along `evMap` -/

/-- The evaluation `evMap x : T_n →+* F̄` is a homomorphism of `𝒪[F]`-algebras, where `𝒪[F]`
acts on the algebraic closure through `F`. -/
private theorem evMap_comp_algebraMap (π : O F) (q n : ℕ) (hq : 2 ≤ q)
    (x : AlgebraicClosure F) (hx : x ∈ LTdivisionSet F (π : F) q n) :
    (evMap π q n hq x hx).comp (algebraMap (O F) (LTtorsionRing F π q n))
      = (algebraMap F (AlgebraicClosure F)).comp (algebraMap (O F) F) := by
  ext c
  show evMap π q n hq x hx (algebraMap (O F) (LTtorsionRing F π q n) c) = _
  unfold evMap
  rw [AdjoinRoot.algebraMap_eq (LTpolyIter π q n)]
  simp only [AdjoinRoot.of, RingHom.comp_apply, AdjoinRoot.lift_mk, Polynomial.eval₂_C]

/-- **Naturality of polynomial evaluation under `evMap`**: evaluating a polynomial of `𝒪[F][X]` at
the point `evMap x y` of the algebraic closure is the same as evaluating its image in `F[X]` at
`y` inside `T_n`.  This is `Polynomial.hom_eval₂`. -/
private theorem aeval_evMap (π : O F) (q n : ℕ) (hq : 2 ≤ q) (x : AlgebraicClosure F)
    (hx : x ∈ LTdivisionSet F (π : F) q n) (y : LTtorsionRing F π q n)
    (Q : Polynomial (O F)) :
    Polynomial.aeval (evMap π q n hq x hx y) (Q.map (algebraMap (O F) F))
      = evMap π q n hq x hx (Polynomial.aeval y Q) := by
  rw [Polynomial.aeval_def (A := AlgebraicClosure F), Polynomial.aeval_def]
  rw [Polynomial.eval₂_map]
  rw [← evMap_comp_algebraMap π q n hq x hx]
  exact (Polynomial.hom_eval₂ Q (algebraMap (O F) (LTtorsionRing F π q n))
    (evMap π q n hq x hx) y).symm

/-- **The `𝒪[F]`-action on the `π^n`-torsion points**: if `x ∈ Λ_n` then `a · x ∈ Λ_n` for every
`a ∈ 𝒪[F]`.

Here `a · x = evMap x ([a]_n)` is the evaluation at `x` of the `a`-multiplication series
`[a]` of the Lubin–Tate module, computed in the torsion ring `T_n` of `Eval/TorsionRing.lean`
(`Eval.smulDiv`).  The result is the classical statement that `Λ_n` is an `𝒪[F]`-module
(Milne, *CFT*, §I.3), which is why `Λ_n` is a free `𝒪[F]/π^n`-module of rank one.

The hypothesis `M.toLaw.piEndo = πX + X^q` identifies the `π`-multiplication series of the module
with the standard Lubin–Tate series whose iterates define `Λ_n`; it is exactly the extra
information carried by the canonical Lubin–Tate module over `𝒪[F]`
(`NK.LocalReciprocityLubinTate.lubinTateModule_integers`). -/
theorem smulDiv_mem {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (↥(ValuativeRel.valuation F).integer) π q)
    (hpi : M.toLaw.piEndo = NK.LocalReciprocityLubinTate.piXAddXq π q)
    (x : AlgebraicClosure F) (hx : x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q n)
    (a : ↥(ValuativeRel.valuation F).integer) :
    NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ q n hq M hx a
      ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q n := by
  rw [NK.LocalReciprocityLubinTate.mem_LTdivisionSet_iff (π : F) q n hq]
  show Polynomial.aeval
      (evMap π q n hq x hx (evalTau π hπ q n hq (M.action a)))
      (LTpolyIter (π : F) q n) = 0
  have hpoly : LTpolyIter (π : F) q n = (LTpolyIter π q n).map (algebraMap (O F) F) :=
    (LTpolyIter_map (algebraMap (O F) F) π q n).symm
  rw [hpoly]
  rw [aeval_evMap π q n hq x hx (evalTau π hπ q n hq (M.action a)) (LTpolyIter π q n)]
  rw [aeval_actionTau_LTpolyIter π hπ q n hq M hpi a, map_zero]


/-- **The `π^m`-action on a torsion point is the polynomial iterate `f^{(m)}`.**

For `x ∈ Λ_n` and `m : ℕ`, the point `π^m · x = smulDiv π hπ q n hq M hx (π^m)`, computed inside the
torsion ring `T_n`, is the value `f^{(m)}(x)` of the `m`-th iterate of the standard Lubin–Tate
polynomial `f(T) = πT + T^q` at `x`.  This bridges the formal-group action and the explicit
polynomials defining the levels; it is the input for the annihilator computation
`{a : a · x = 0} = (π^n)` of `Eval/smulDiv_ker.lean`.

The right-hand side is *independent of the level* `n`. -/
theorem smulDiv_pi_pow {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (↥(ValuativeRel.valuation F).integer) π q)
    (hpi : M.toLaw.piEndo = NK.LocalReciprocityLubinTate.piXAddXq π q)
    (x : AlgebraicClosure F) (hx : x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q n)
    (m : ℕ) :
    NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ q n hq M hx (π ^ m)
      = Polynomial.aeval x (NK.LocalReciprocityLubinTate.LTpolyIter (π : F) q m) := by
  have hbr := bridge π hπ q n hq M hpi (MvPowerSeries.X (0 : Fin 1))
    (MvPowerSeries.constantCoeff_X (0 : Fin 1)) m
  rw [subst1_X, evalTau_X] at hbr
  have haev := aeval_evMap π q n hq x hx (LTtorsionRing.tau π q n) (LTpolyIter π q m)
  rw [evMap_tau] at haev
  rw [show NK.LocalReciprocityLubinTate.LTpolyIter (π : F) q m
      = (NK.LocalReciprocityLubinTate.LTpolyIter π q m).map (algebraMap (O F) F) from
    (NK.LocalReciprocityLubinTate.LTpolyIter_map (algebraMap (O F) F) π q m).symm]
  show NK.LocalReciprocityLubinTate.Eval.evMap π q n hq x hx
      (NK.LocalReciprocityLubinTate.Eval.evalTau π hπ q n hq
        (M.action (π ^ m))) = _
  rw [← hbr]
  exact haev.symm

end

end NK.LocalReciprocityLubinTate.Eval
