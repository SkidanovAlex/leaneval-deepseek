import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Submission.NK.LocalReciprocityLubinTate.Eval.evalTau_subst
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_smul2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped ValuativeRel
open Polynomial MvPowerSeries
open scoped MvPowerSeries.WithPiTopology

namespace NK.LocalReciprocityLubinTate.Eval

noncomputable section

universe u

set_option linter.style.haveILetI false

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- **The iterates do not leave the torsion level.**  In any commutative ring, if `y` is a root of
the `m`-th iterate `f^{(m)}` of the standard Lubin–Tate polynomial `f(T) = πT + T^q`, then it is a
root of `f^{(N)}` for every `N ≥ m`.

Indeed `f^{(n+1)} = f^{[n]} · f^{(n)}` (`LTpolyIter_succ_eq_mul`), so the vanishing is transported
along the tower of factors `f^{[n]}`. -/
theorem aeval_LTpolyIter_eq_zero_of_le {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {π : A} {q : ℕ} (hq : 1 ≤ q)
    {m N : ℕ} (hmN : m ≤ N) {y : B} (h : (Polynomial.aeval y) (LTpolyIter π q m) = 0) :
    (Polynomial.aeval y) (LTpolyIter π q N) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmN
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Nat.add_succ, LTpolyIter_succ_eq_mul π q (m + k) hq, Polynomial.aeval_mul, ih (by omega),
      mul_zero]

/-- **Compatibility of the Lubin–Tate `𝒪[F]`-action with the level.**  If `x` is a `π^N`-torsion
point and a `π^m`-torsion point with `m ≤ N`, then the point `a · x = [a](x)` (Milne, *CFT*, §I.3)
is the same, whether it is computed in `T_N = 𝒪[F][T]/(f^{(N)}(T))` or in `T_m`. -/
theorem smulDiv_compat {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (q : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (↥(ValuativeRel.valuation F).integer) π q)
    {N m : ℕ} (hmN : m ≤ N) {x : AlgebraicClosure F}
    (hxN : x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q N)
    (hxm : x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q m)
    (a : ↥(ValuativeRel.valuation F).integer) :
    NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ q N hq M hxN a =
      NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ q m hq M hxm a := by
  show evMap π q N hq x hxN (actionTau π hπ q N hq M a)
      = evMap π q m hq x hxm (actionTau π hπ q m hq M a)
  haveI : CompleteSpace (LTtorsionRing F π q N) := completeSpace_ltTorsionRing π hπ q N hq
  haveI : T2Space (LTtorsionRing F π q N) := t2Space_ltTorsionRing π hπ q N hq
  haveI : CompleteSpace (LTtorsionRing F π q m) := completeSpace_ltTorsionRing π hπ q m hq
  haveI : T2Space (LTtorsionRing F π q m) := t2Space_ltTorsionRing π hπ q m hq
  have hq1 : 1 ≤ q := by omega
  -- `f^{(N)}(τ_m) = 0`
  have hroot : (Polynomial.aeval (LTtorsionRing.tau π q m)) (LTpolyIter π q N) = 0 :=
    aeval_LTpolyIter_eq_zero_of_le (π := π) (q := q) hq1 hmN (LTtorsionRing.tau_spec π q m)
  have hcE : Polynomial.eval₂ (algebraMap (O F) (LTtorsionRing F π q m))
      (LTtorsionRing.tau π q m) (LTpolyIter π q N) = 0 := by
    simpa [Polynomial.aeval_def] using hroot
  -- the quotient map `T_N →+* T_m`, `τ_N ↦ τ_m`
  let Sub : LTtorsionRing F π q N →+* LTtorsionRing F π q m :=
    AdjoinRoot.lift (algebraMap (O F) (LTtorsionRing F π q m)) (LTtorsionRing.tau π q m) hcE
  have Sub_root : Sub (LTtorsionRing.tau π q N) = LTtorsionRing.tau π q m :=
    AdjoinRoot.lift_root hcE
  have Sub_of : Sub.comp (AdjoinRoot.of (LTpolyIter π q N))
      = algebraMap (O F) (LTtorsionRing F π q m) := AdjoinRoot.lift_comp_of hcE
  have Sub_alg : ∀ r : O F, Sub (algebraMap (O F) (LTtorsionRing F π q N) r)
      = algebraMap (O F) (LTtorsionRing F π q m) r := by
    intro r
    show (AdjoinRoot.lift (algebraMap (O F) (LTtorsionRing F π q m))
        (LTtorsionRing.tau π q m) hcE) (algebraMap (O F) (LTtorsionRing F π q N) r)
      = algebraMap (O F) (LTtorsionRing F π q m) r
    simpa only [AdjoinRoot.algebraMap_eq] using
      (AdjoinRoot.lift_of (f := LTpolyIter π q N)
        (i := algebraMap (O F) (LTtorsionRing F π q m))
        (a := LTtorsionRing.tau π q m) (h := hcE) (x := r))
  have Sub_cont : Continuous Sub := by
    refine continuous_ringHom_adicTopology_of_map_le Sub (LTtorsionRing.adicIdeal π q N)
      (LTtorsionRing.adicIdeal π q m) ?_
    rw [LTtorsionRing.adicIdeal, Ideal.map_span, Set.image_singleton, Ideal.span_le,
      Set.singleton_subset_iff]
    have hpiT : Sub (LTtorsionRing.piT π q N) = LTtorsionRing.piT π q m := by
      show Sub (algebraMap (O F) (LTtorsionRing F π q N) π)
        = algebraMap (O F) (LTtorsionRing F π q m) π
      exact Sub_alg π
    rw [hpiT]
    exact Ideal.subset_span (Set.mem_singleton _)
  have evalTau_cont : Continuous (evalTau π hπ q N hq) := by
    rw [evalTau, MvPowerSeries.coe_eval₂Hom]
    exact MvPowerSeries.continuous_eval₂ continuous_of_discreteTopology
      (hasEval_ltTorsionRing π q N hq)
  -- `Sub` commutes with Milne's evaluation at `τ`
  have SubEval : ∀ f : MvPowerSeries (Fin 1) (O F),
      Sub (evalTau π hπ q N hq f) = evalTau π hπ q m hq f := by
    have hcomp : Sub.comp (MvPolynomial.eval₂Hom (algebraMap (O F) (LTtorsionRing F π q N))
          (fun _ : Fin 1 => LTtorsionRing.tau π q N))
        = MvPolynomial.eval₂Hom (algebraMap (O F) (LTtorsionRing F π q m))
            (fun _ : Fin 1 => LTtorsionRing.tau π q m) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
        exact Sub_alg r
      · intro i
        rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
        exact Sub_root
    have hcont : Continuous (fun f : MvPowerSeries (Fin 1) (O F) =>
        Sub (evalTau π hπ q N hq f)) := Sub_cont.comp evalTau_cont
    have hagree : ∀ p : MvPolynomial (Fin 1) (O F),
        Sub (evalTau π hπ q N hq ↑p)
          = MvPolynomial.eval₂ (algebraMap (O F) (LTtorsionRing F π q m))
              (fun _ : Fin 1 => LTtorsionRing.tau π q m) p := by
      intro p
      rw [evalTau_eq_eval₂ π hπ q N hq, MvPowerSeries.eval₂_coe]
      exact congr_fun (congr_arg DFunLike.coe hcomp) p
    intro f
    rw [evalTau_eq_eval₂ π hπ q m hq]
    exact congr_fun (MvPowerSeries.eval₂_unique (φ := algebraMap (O F) (LTtorsionRing F π q m))
      (a := fun _ : Fin 1 => LTtorsionRing.tau π q m) continuous_of_discreteTopology
      (hasEval_ltTorsionRing π q m hq) hcont hagree) f
  -- evaluation at the point `x` at level `N` factors through `Sub`
  have evMap_Sub : (evMap π q m hq x hxm).comp Sub = evMap π q N hq x hxN := by
    have h1 : ((evMap π q m hq x hxm).comp Sub).comp (AdjoinRoot.of (LTpolyIter π q N))
        = (algebraMap F (AlgebraicClosure F)).comp (algebraMap (O F) F) := by
      rw [RingHom.comp_assoc, Sub_of, AdjoinRoot.algebraMap_eq (LTpolyIter π q m), evMap]
      exact AdjoinRoot.lift_comp_of _
    have h2 : (evMap π q N hq x hxN).comp (AdjoinRoot.of (LTpolyIter π q N))
        = (algebraMap F (AlgebraicClosure F)).comp (algebraMap (O F) F) := by
      rw [← AdjoinRoot.algebraMap_eq (LTpolyIter π q N), evMap]
      exact AdjoinRoot.lift_comp_of _
    apply AdjoinRoot.ringHom_ext (p := LTpolyIter π q N)
    · rw [h1, h2]
    · rw [RingHom.comp_apply, show Sub (AdjoinRoot.root (LTpolyIter π q N))
            = LTtorsionRing.tau π q m from Sub_root]
      rw [show AdjoinRoot.root (LTpolyIter π q N) = LTtorsionRing.tau π q N from rfl,
        evMap_tau π q m hq x hxm, evMap_tau π q N hq x hxN]
  rw [← evMap_Sub]
  show (evMap π q m hq x hxm) (Sub (evalTau π hπ q N hq (M.action a)))
      = (evMap π q m hq x hxm) (evalTau π hπ q m hq (M.action a))
  rw [SubEval (M.action a)]

end

end NK.LocalReciprocityLubinTate.Eval
