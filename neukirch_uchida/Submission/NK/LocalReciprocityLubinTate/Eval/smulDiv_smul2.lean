/-
# Functoriality of the Lubin–Tate `𝒪[F]`-action on the torsion points

Milne, *Classical Field Theory*, §I.3: the action of `a ∈ 𝒪[F]` on the `π^n`-torsion points `Λ_n`
of the Lubin–Tate group of `π` is `a · x = [a](x)`, the evaluation of the `a`-multiplication
series `[a]` at `x` (`Eval/TorsionAction.lean`).  This file proves that it is an action of the
multiplicative monoid `𝒪[F]`:

  `a · (b · x) = (a * b) · x`     (`smulDiv_smul2`),

which, together with `1 · x = x` (`smulDiv_one`), gives the first two axioms of Milne's
`𝒪[F]/π^n`-module structure on `Λ_n ≅ (𝒪[F]/π^n)^+` (Milne, *CFT*, Theorem I.3.1).

## The proof

Everything happens in the finite ring `T_n = 𝒪[F][T]/(f^{(n)}(T))` of `Eval/TorsionRing.lean`
with its class `τ` and its `𝒪[F]`-algebra homomorphism `evMap x : T_n → F̄` for `x ∈ Λ_n`.

Write `c = [b]_n = E [b] ∈ T_n` for the class of the `b`-multiplication series at `τ` (where
`E = evalTau`), and `y = evMap x c = b · x`.  The main point is that the evaluation at the *point*
`y` can be computed inside `T_n` by the substitution `τ ↦ c`:

* `c` is again a `π^n`-torsion class of `T_n`, i.e. `f^{(n)}(c) = 0`
  (`sD_aeval_actionTau_LTpolyIter`: the bridge `f^{(k)}(E ψ) = E (ψ ∘ [π^k])` of
  `Eval/smulDiv_mem.lean` at `ψ = [b]`), so the substitution
  `Sub = AdjoinRoot.lift (algebraMap (O F) T_n) c` is a ring homomorphism `T_n →+* T_n` with
  `Sub τ = c`;
* `evMap y = evMap x ∘ Sub` (`evMap_Sub`): by `AdjoinRoot.ringHom_ext`, since both sides are
  `𝒪[F]`-algebra maps `T_n → F̄` sending `τ` to `y = evMap x c`;
* `Sub (E f) = eval₂ ![c] f` (`SubEval`): both sides are continuous and agree on polynomials, and
  `𝒪[F][X]` is dense in `𝒪[F]⟦X⟧` (`MvPowerSeries.eval₂_unique`).  Continuity of `Sub` is the
  adic-topology criterion `continuous_ringHom_adicTopology_of_map_le`, and continuity of `E` is
  Milne's evaluation of a power series at a topologically nilpotent point.

The goal then follows from the multiplication rule `[a * b] = [a] ∘ [b]` read at `τ`
(`actionTau_mul`, `MvPowerSeries.eval₂_subst`):

  `a · (b · x) = evMap y ([a]_n) = evMap x (Sub [a]_n) = evMap x ([a ∘ b]_n) = (a * b) · x`.
-/
import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Eval.TorsionAction
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_mem
import Submission.NK.LocalReciprocityLubinTate.Eval.actionTau_mul

namespace NK.LocalReciprocityLubinTate.Eval

noncomputable section

universe u

open scoped ValuativeRel

open NK.LocalReciprocityLubinTate.LubinTate (subst1 subst1_apply subst1_comp subst1_self
  subst1_X subst1_constantCoeff hasSubst_vec1)

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

set_option linter.style.haveILetI false

/-! ### The bridge of `Eval/smulDiv_mem.lean`

The following lemmas are the private working lemmas of `Eval/smulDiv_mem.lean`, reproduced here
(they are not exported there).  Their content is the **bridge**

  `f^{(k)}(E ψ) = E (ψ ∘ [π^k])`   (`ψ` of zero constant coefficient)

between the polynomial iterates `f^{(k)}` of `f = πX + X^q` and the `π^k`-multiplication series of
the Lubin–Tate module, together with its immediate consequences.  They are used below only through
`sD_aeval_actionTau_LTpolyIter`, which says that the class `[a]_n` of `T_n` is a `π^n`-torsion
point of `T_n` itself. -/


/-! ### Milne's evaluation at `τ` -/

/-- Milne's evaluation at the torsion class `τ`, as a function: `evalTau` is by definition the
evaluation homomorphism of `MvPowerSeries`, so it is `eval₂` at the constant family `τ`
(`MvPowerSeries.coe_eval₂Hom`). -/
private theorem sD_evalTau_apply (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (f : MvPowerSeries (Fin 1) (O F)) :
    evalTau π hπ q n hq f
      = MvPowerSeries.eval₂ (algebraMap (O F) (LTtorsionRing F π q n))
          (fun _ : Fin 1 => LTtorsionRing.tau π q n) f := by
  haveI : CompleteSpace (LTtorsionRing F π q n) := completeSpace_ltTorsionRing π hπ q n hq
  haveI : T2Space (LTtorsionRing F π q n) := t2Space_ltTorsionRing π hπ q n hq
  rw [evalTau, MvPowerSeries.coe_eval₂Hom]

private theorem sD_evalTau_X (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q) :
    evalTau π hπ q n hq (MvPowerSeries.X 0) = LTtorsionRing.tau π q n := by
  rw [sD_evalTau_apply, MvPowerSeries.eval₂_X]

private theorem sD_evalTau_C (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q) (c : O F) :
    evalTau π hπ q n hq (MvPowerSeries.C c)
      = algebraMap (O F) (LTtorsionRing F π q n) c := by
  rw [sD_evalTau_apply, MvPowerSeries.eval₂_C]

/-- **Milne's substitution rule**, at the torsion class `τ`: evaluating the composite of two
power series at `τ` is evaluating the outer series at the value of the inner one.  This is
`MvPowerSeries.eval₂_subst` for the family `![ψ]` and the point `τ`, which admits evaluation
(`hasEval_ltTorsionRing`). -/
private theorem sD_evalTau_subst' (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (ψ φ : MvPowerSeries (Fin 1) (O F))
    (hψ : MvPowerSeries.HasSubst (![ψ] : Fin 1 → MvPowerSeries (Fin 1) (O F))) :
    evalTau π hπ q n hq (MvPowerSeries.subst ![ψ] φ)
      = MvPowerSeries.eval₂ (algebraMap (O F) (LTtorsionRing F π q n))
          (fun _ : Fin 1 => evalTau π hπ q n hq ψ) φ := by
  haveI : CompleteSpace (LTtorsionRing F π q n) := completeSpace_ltTorsionRing π hπ q n hq
  haveI : T2Space (LTtorsionRing F π q n) := t2Space_ltTorsionRing π hπ q n hq
  have hb : MvPowerSeries.HasEval (fun _ : Fin 1 => LTtorsionRing.tau π q n) :=
    hasEval_ltTorsionRing π q n hq
  rw [sD_evalTau_apply]
  rw [MvPowerSeries.eval₂_subst hψ hb]
  congr 1
  funext s
  fin_cases s
  simp only [Matrix.cons_val_fin_one]
  rw [sD_evalTau_apply]

/-- **Evaluation at `0` of a power series**: a power series of zero constant coefficient takes the
value `0` at `0`.  Equivalently, for an arbitrary series `f`, substitution of `0` produces its
constant coefficient.

This is Milne's computation `[a](0) = 0`, and it is the reason the action of `𝒪[F]` fixes `0 ∈ Λ_n`.
The proof substitutes `0` into `f` first (`MvPowerSeries.subst_zero_eq_C_constantCoeff`) and then
evaluates the resulting constant series at the *torsion* point `τ`, where evaluation is available;
Milne's substitution rule (`MvPowerSeries.eval₂_subst`) computes both sides. -/
private theorem sD_eval₂_zero_eq (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
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
private theorem sD_action_constantCoeff_zero (π : O F) (q : ℕ) (M : LubinTateModule (O F) π q)
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
private theorem sD_action_pow_succ (π : O F) (q : ℕ) (M : LubinTateModule (O F) π q) (k : ℕ) :
    M.action (π ^ (k + 1)) = subst1 (M.action π) (M.action (π ^ k)) := by
  rw [pow_succ, M.action_mul, subst1_apply]

/-- **Substituting into `[π]`**: for a series `ψ` of zero constant coefficient,
`subst1 ψ [π] = π·ψ + ψ^q`.  This is the standard series `f(T) = πT + T^q` of the Lubin–Tate
module (`hpi`), substituted. -/
private theorem sD_subst1_action_pi (π : O F) (q : ℕ) (M : LubinTateModule (O F) π q)
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
private theorem sD_aeval_LTpoly_evalTau (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (O F) π q) (hpi : M.toLaw.piEndo = piXAddXq π q)
    (ψ : MvPowerSeries (Fin 1) (O F)) (hψ : MvPowerSeries.constantCoeff ψ = 0) :
    Polynomial.aeval (evalTau π hπ q n hq ψ) (LTpoly π q)
      = evalTau π hπ q n hq (subst1 ψ (M.action π)) := by
  rw [sD_subst1_action_pi π q M hpi ψ hψ]
  simp only [map_add, map_mul, map_pow, sD_evalTau_C, LTpoly, Polynomial.aeval_C,
    Polynomial.aeval_X]

/-- **The bridge between the polynomial iterate and the substituted multiplication series.**

For every series `ψ` of zero constant coefficient and every `k`,
`f^{(k)}(E ψ) = E (ψ ∘ [π^k])`, i.e. the polynomial iterate `f^{(k)}` of `πX + X^q` and the
`k`-th iterate `Φ_k = [π^k]` of the formal group match under Milne's evaluation at `τ`.

The induction is over `k`, keeping `ψ` universally quantified so that the successor step may apply
the hypothesis to the series `ψ ∘ [π]`. -/
private theorem sD_bridge (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
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
    rw [sD_aeval_LTpoly_evalTau π hπ q n hq M hpi ψ hψ]
    rw [ih (subst1 ψ (M.action π))
      (subst1_constantCoeff hψ (sD_action_constantCoeff_zero π q M π))]
    rw [sD_action_pow_succ π q M k]
    rw [← subst1_comp
      (hasSubst_vec1 (sD_action_constantCoeff_zero π q M π)) (hasSubst_vec1 hψ)]

/-- **`τ` is a `π^n`-torsion point**: `E Φ_n = f^{(n)}(τ) = 0`.**  This is the sD_bridge at
`ψ = X` together with the defining property of `τ` (`LTtorsionRing.tau_spec`). -/
private theorem sD_evalTau_action_pow_eq_zero (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (O F) π q) (hpi : M.toLaw.piEndo = piXAddXq π q) :
    evalTau π hπ q n hq (M.action (π ^ n)) = 0 := by
  have hbr := sD_bridge π hπ q n hq M hpi (MvPowerSeries.X (0 : Fin 1))
    (MvPowerSeries.constantCoeff_X (0 : Fin 1)) n
  have hsub : subst1 (MvPowerSeries.X (0 : Fin 1)) (M.action (π ^ n)) = M.action (π ^ n) :=
    subst1_X
  rw [← hsub, ← hbr, sD_evalTau_X]
  exact LTtorsionRing.tau_spec π q n

/-- **The main computation in `T_n`**: for the Lubin–Tate module `M` of the standard series,
`[a](τ)`, i.e. the class in `T_n` of the `a`-multiplication series at `τ`, is again a
`π^n`-torsion point: `f^{(n)}(E [a]) = 0`.

The proof uses the sD_bridge at `ψ = [a]`, the commutativity `[a] ∘ [π^n] = [π^n] ∘ [a] = [aπ^n]` of
the `𝒪[F]`-module structure, Milne's substitution rule, and `E Φ_n = 0`. -/
private theorem sD_aeval_actionTau_LTpolyIter (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (O F) π q) (hpi : M.toLaw.piEndo = piXAddXq π q) (a : O F) :
    Polynomial.aeval (evalTau π hπ q n hq (M.action a)) (LTpolyIter π q n) = 0 := by
  rw [sD_bridge π hπ q n hq M hpi (M.action a) (sD_action_constantCoeff_zero π q M a) n]
  have hcomm : subst1 (M.action a) (M.action (π ^ n))
      = subst1 (M.action (π ^ n)) (M.action a) := by
    rw [subst1_apply, subst1_apply, ← M.action_mul (π ^ n) a, ← M.action_mul a (π ^ n),
      mul_comm (π ^ n) a]
  rw [hcomm, subst1_apply]
  rw [sD_evalTau_subst' π hπ q n hq (M.action (π ^ n)) (M.action a)
    (hasSubst_vec1 (sD_action_constantCoeff_zero π q M (π ^ n)))]
  have hfam : (fun _ : Fin 1 => evalTau π hπ q n hq (M.action (π ^ n)))
      = (fun _ : Fin 1 => (0 : LTtorsionRing F π q n)) :=
    funext fun _ => sD_evalTau_action_pow_eq_zero π hπ q n hq M hpi
  rw [hfam, sD_eval₂_zero_eq π hπ q n hq, sD_action_constantCoeff_zero π q M a]
  simp

/-! ### Continuity of a ring homomorphism for adic topologies -/

/-- A ring homomorphism `R →+* S` which sends the ideal `I` into the ideal `J` is continuous for the
`I`-adic topology on `R` and the `J`-adic topology on `S`.  (Only the additive structure is used,
via `continuous_of_continuousAt_zero`, so it suffices to check continuity at `0`, where the adic
neighbourhood bases are the powers of `I` and `J`.) -/
theorem continuous_ringHom_adicTopology_of_map_le {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (J : Ideal S) (h : I.map f ≤ J) :
    @Continuous R S I.adicTopology J.adicTopology f := by
  letI : TopologicalSpace R := I.adicTopology
  letI : TopologicalSpace S := J.adicTopology
  haveI : IsTopologicalRing R := (Ideal.nonarchimedean I).toIsTopologicalRing
  haveI : IsTopologicalRing S := (Ideal.nonarchimedean J).toIsTopologicalRing
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt]
  simp only [map_zero]
  rw [(I.hasBasis_nhds_zero_adic).tendsto_iff (J.hasBasis_nhds_zero_adic)]
  intro m _
  refine ⟨m, trivial, fun y hy => ?_⟩
  have hmap : (I ^ m).map f ≤ J ^ m := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono h m
  exact hmap (Ideal.mem_map_of_mem f hy)

open scoped MvPowerSeries.WithPiTopology

/-! ### The `𝒪[F]`-action is an action

From here on the product topology on power series (and hence continuity of Milne's evaluation) is
in scope. -/

/-- **The class `[b]_n = E [b]` is a `π^n`-torsion point of the ambient ring `T_n`**, so the family
`![[b]_n]` admits the evaluation of power series.  This is the nilpotence criterion
`isTopologicallyNilpotent_adicTopology_of_pow_mem` applied to the root property
`f^{(n)}([b]_n) = 0` (`sD_aeval_actionTau_LTpolyIter`) and the congruence
`f^{(n)}(X) ≡ X^{q^n} (mod π)`. -/
private theorem sD_hasEval_actionTau (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (O F) π q) (hpi : M.toLaw.piEndo = piXAddXq π q) (b : O F) :
    MvPowerSeries.HasEval (fun _ : Fin 1 => actionTau π hπ q n hq M b) := by
  have hroot : Polynomial.aeval (actionTau π hπ q n hq M b) (LTpolyIter π q n) = 0 :=
    sD_aeval_actionTau_LTpolyIter π hπ q n hq M hpi b
  have hq1 : 1 ≤ q := by omega
  have hmem : actionTau π hπ q n hq M b ^ q ^ n ∈ LTtorsionRing.adicIdeal π q n := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp (ltpolyIter_sub_X_pow_mem_span π q n hq1)
    have h1 : (Polynomial.aeval (actionTau π hπ q n hq M b))
        (LTpolyIter π q n - Polynomial.X ^ (q ^ n))
        = -(actionTau π hπ q n hq M b ^ q ^ n) := by
      rw [map_sub, hroot, map_pow, Polynomial.aeval_X, zero_sub]
    rw [ha, map_mul, Polynomial.aeval_C] at h1
    have h2 : actionTau π hπ q n hq M b ^ q ^ n
        = -(LTtorsionRing.piT π q n * (Polynomial.aeval (actionTau π hπ q n hq M b)) a) := by
      have hh := congrArg Neg.neg h1
      rw [neg_neg] at hh
      exact hh.symm
    rw [h2]
    exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _)))
  refine ⟨fun _ => ?_, ?_⟩
  · exact isTopologicallyNilpotent_adicTopology_of_pow_mem (LTtorsionRing.adicIdeal π q n)
      (Nat.pow_pos (by omega : 0 < q)) hmem
  · simp

/-- **The `𝒪[F]`-action on the `π^n`-torsion points is an action**: for `x ∈ Λ_n` and
`a b ∈ 𝒪[F]`,

  `a · (b · x) = (a * b) · x`,

i.e. `[a]([b](x)) = [a*b](x)` (Milne, *CFT*, §I.3).  With `smulDiv_one` this is the first axiom of
the `𝒪[F]`-module structure on `Λ_n`.

The evaluation at the point `y = b · x = evMap x ([b]_n)` is computed inside `T_n` by the
substitution `Sub : τ ↦ [b]_n` (`evMap_Sub`, `SubEval`), and the multiplication rule
`[a * b] = [a] ∘ [b]` is Milne's substitution rule read at `τ` (`actionTau_mul`). -/
theorem smulDiv_smul2 {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (↥(ValuativeRel.valuation F).integer) π q)
    (hpi : M.toLaw.piEndo = NK.LocalReciprocityLubinTate.piXAddXq π q)
    (x : AlgebraicClosure F) (hx : x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q n)
    (a b : ↥(ValuativeRel.valuation F).integer) :
    NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ q n hq M
        (NK.LocalReciprocityLubinTate.Eval.smulDiv_mem π hπ q n hq M hpi x hx b) a
      = NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ q n hq M hx (a * b) := by
  haveI : CompleteSpace (LTtorsionRing F π q n) := completeSpace_ltTorsionRing π hπ q n hq
  haveI : T2Space (LTtorsionRing F π q n) := t2Space_ltTorsionRing π hπ q n hq
  -- the class of the `b`-multiplication series at `τ` is a `π^n`-torsion point of `T_n`
  have hcA : Polynomial.aeval (actionTau π hπ q n hq M b) (LTpolyIter π q n) = 0 :=
    sD_aeval_actionTau_LTpolyIter π hπ q n hq M hpi b
  have hcE : Polynomial.eval₂ (algebraMap (O F) (LTtorsionRing F π q n))
      (actionTau π hπ q n hq M b) (LTpolyIter π q n) = 0 := by
    simpa [Polynomial.aeval_def] using hcA
  -- the substitution `τ ↦ [b]_n` of `T_n`
  let Sub : LTtorsionRing F π q n →+* LTtorsionRing F π q n :=
    AdjoinRoot.lift (algebraMap (O F) (LTtorsionRing F π q n)) (actionTau π hπ q n hq M b) hcE
  have Sub_root : Sub (LTtorsionRing.tau π q n) = actionTau π hπ q n hq M b :=
    AdjoinRoot.lift_root hcE
  have Sub_of : Sub.comp (AdjoinRoot.of (LTpolyIter π q n))
      = algebraMap (O F) (LTtorsionRing F π q n) := AdjoinRoot.lift_comp_of hcE
  have Sub_alg : ∀ r : O F, Sub (algebraMap (O F) (LTtorsionRing F π q n) r)
      = algebraMap (O F) (LTtorsionRing F π q n) r := by
    intro r
    show (AdjoinRoot.lift (algebraMap (O F) (LTtorsionRing F π q n))
        (actionTau π hπ q n hq M b) hcE) (algebraMap (O F) (LTtorsionRing F π q n) r)
      = algebraMap (O F) (LTtorsionRing F π q n) r
    simpa only [AdjoinRoot.algebraMap_eq] using
      (AdjoinRoot.lift_of (f := LTpolyIter π q n) (i := algebraMap (O F) (LTtorsionRing F π q n))
        (a := actionTau π hπ q n hq M b) (h := hcE) (x := r))
  have Sub_cont : Continuous Sub := by
    refine continuous_ringHom_adicTopology_of_map_le Sub (LTtorsionRing.adicIdeal π q n)
      (LTtorsionRing.adicIdeal π q n) ?_
    rw [LTtorsionRing.adicIdeal, Ideal.map_span, Set.image_singleton, Ideal.span_le,
      Set.singleton_subset_iff]
    have hpiT : Sub (LTtorsionRing.piT π q n) = LTtorsionRing.piT π q n := by
      show Sub (algebraMap (O F) (LTtorsionRing F π q n) π)
        = algebraMap (O F) (LTtorsionRing F π q n) π
      exact Sub_alg π
    rw [hpiT]
    exact Ideal.subset_span (Set.mem_singleton _)
  have evalTau_cont : Continuous (evalTau π hπ q n hq) := by
    rw [evalTau, MvPowerSeries.coe_eval₂Hom]
    exact MvPowerSeries.continuous_eval₂ continuous_of_discreteTopology
      (hasEval_ltTorsionRing π q n hq)
  -- `Sub` commutes with Milne's evaluation at `τ`
  have SubEval : ∀ f : MvPowerSeries (Fin 1) (O F), Sub (evalTau π hπ q n hq f)
      = MvPowerSeries.eval₂ (algebraMap (O F) (LTtorsionRing F π q n))
          (fun _ : Fin 1 => actionTau π hπ q n hq M b) f := by
    have hcomp : Sub.comp (MvPolynomial.eval₂Hom (algebraMap (O F) (LTtorsionRing F π q n))
          (fun _ : Fin 1 => LTtorsionRing.tau π q n))
        = MvPolynomial.eval₂Hom (algebraMap (O F) (LTtorsionRing F π q n))
            (fun _ : Fin 1 => actionTau π hπ q n hq M b) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
        exact Sub_alg r
      · intro i
        rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
        exact Sub_root
    have hcont : Continuous (fun f : MvPowerSeries (Fin 1) (O F) =>
        Sub (evalTau π hπ q n hq f)) := Sub_cont.comp evalTau_cont
    have hagree : ∀ p : MvPolynomial (Fin 1) (O F), Sub (evalTau π hπ q n hq ↑p)
        = MvPolynomial.eval₂ (algebraMap (O F) (LTtorsionRing F π q n))
            (fun _ : Fin 1 => actionTau π hπ q n hq M b) p := by
      intro p
      rw [sD_evalTau_apply π hπ q n hq, MvPowerSeries.eval₂_coe]
      exact congr_fun (congr_arg DFunLike.coe hcomp) p
    intro f
    exact congr_fun (MvPowerSeries.eval₂_unique (φ := algebraMap (O F) (LTtorsionRing F π q n))
      (a := fun _ : Fin 1 => actionTau π hπ q n hq M b) continuous_of_discreteTopology
      (sD_hasEval_actionTau π hπ q n hq M hpi b) hcont hagree) f
  -- evaluation at the point `b · x` is evaluation at `x` after substitution
  have evMap_Sub : evMap π q n hq (evMap π q n hq x hx (actionTau π hπ q n hq M b))
        (smulDiv_mem π hπ q n hq M hpi x hx b)
      = (evMap π q n hq x hx).comp Sub := by
    have h1 : (evMap π q n hq (evMap π q n hq x hx (actionTau π hπ q n hq M b))
          (smulDiv_mem π hπ q n hq M hpi x hx b)).comp (AdjoinRoot.of (LTpolyIter π q n))
        = (algebraMap F (AlgebraicClosure F)).comp (algebraMap (O F) F) := by
      delta evMap
      exact AdjoinRoot.lift_comp_of _
    have h2 : (evMap π q n hq x hx).comp (algebraMap (O F) (LTtorsionRing F π q n))
        = (algebraMap F (AlgebraicClosure F)).comp (algebraMap (O F) F) := by
      rw [AdjoinRoot.algebraMap_eq (LTpolyIter π q n), evMap]
      exact AdjoinRoot.lift_comp_of _
    have h3 : ((evMap π q n hq x hx).comp Sub).comp (AdjoinRoot.of (LTpolyIter π q n))
        = (algebraMap F (AlgebraicClosure F)).comp (algebraMap (O F) F) := by
      rw [RingHom.comp_assoc, Sub_of, h2]
    have h4 : (evMap π q n hq (evMap π q n hq x hx (actionTau π hπ q n hq M b))
          (smulDiv_mem π hπ q n hq M hpi x hx b)) (AdjoinRoot.root (LTpolyIter π q n))
        = evMap π q n hq x hx (actionTau π hπ q n hq M b) := by
      delta evMap
      exact AdjoinRoot.lift_root _
    apply AdjoinRoot.ringHom_ext (p := LTpolyIter π q n)
    · rw [h1, h3]
    · rw [h4, RingHom.comp_apply, show Sub (AdjoinRoot.root (LTpolyIter π q n))
            = actionTau π hπ q n hq M b from Sub_root]
  have key : evMap π q n hq (evMap π q n hq x hx (actionTau π hπ q n hq M b))
        (smulDiv_mem π hπ q n hq M hpi x hx b) (actionTau π hπ q n hq M a)
      = evMap π q n hq x hx
          (MvPowerSeries.eval₂ (algebraMap (O F) (LTtorsionRing F π q n))
            (fun _ : Fin 1 => actionTau π hπ q n hq M b) (M.action a)) := by
    rw [show evMap π q n hq (evMap π q n hq x hx (actionTau π hπ q n hq M b))
          (smulDiv_mem π hπ q n hq M hpi x hx b) (actionTau π hπ q n hq M a)
        = (evMap π q n hq x hx) (Sub (actionTau π hπ q n hq M a)) from
      congrArg (fun g : LTtorsionRing F π q n →+* AlgebraicClosure F =>
        g (actionTau π hπ q n hq M a)) evMap_Sub]
    congr 1
    exact SubEval (M.action a)
  -- unfold the goal and conclude with Milne's multiplication rule `[a * b] = [a] ∘ [b]`
  show evMap π q n hq (evMap π q n hq x hx (actionTau π hπ q n hq M b))
      (smulDiv_mem π hπ q n hq M hpi x hx b) (actionTau π hπ q n hq M a)
    = evMap π q n hq x hx (actionTau π hπ q n hq M (a * b))
  rw [key]
  rw [show (fun _ : Fin 1 => actionTau π hπ q n hq M b) = ![actionTau π hπ q n hq M b] from by
    funext i
    fin_cases i
    rfl]
  rw [← actionTau_mul π hπ q n hq M a b]

end

end NK.LocalReciprocityLubinTate.Eval
