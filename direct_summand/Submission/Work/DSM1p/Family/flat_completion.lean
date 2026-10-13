import Mathlib
import Submission.Work.DSM1p.Family
import Submission.Work.DSM1p.Family.flat_closure
import Submission.Work.DSM1p.Family.torsionFree_completion
import Submission.Work.DSM1p.Family.isAdicComplete
import Submission.Work.DSM1p.Assembly.flat_completion
import Submission.Work.DSM2b.assembly_aux

/-!
# Flatness of the `p`-adic completion of the multi-parameter root closure

Let `R` be a commutative ring, `p ≠ 0` a non-zero-divisor of `R` and `x : Fin d → R`.  The
multi-parameter root closure

`A = A_∞ = R[x₁^{1/p^∞}, …, x_d^{1/p^∞}]`  (`Work.DSM1p.FamClosure R p x`)

is the filtered colimit of the stages `A_n = R[Z₁,…,Z_d]/(Z_i^{p^n} - x_i)`, and
`A′ = AdicCompletion (p) A` is its `p`-adic completion (`Work.DSM1p.FamCompletion R p x`).
This module proves that `A′` is a *flat* `R`-module — the flatness part of Bhatt's
Proposition 4.1 (arXiv:1608.08882) in the multi-parameter case; this is one of the two inputs of
the construction of the perfectoid cover of a complete regular local ring.

## The proof

The proof runs Bhatt's flatness criterion in the dévissage form
`Work.DSM2b.flat_of_flat_mod_base_aux`, whose hypotheses are exactly the ones available in this
workspace.  The inputs are:

* `flat_closure` : `A` is a filtered colimit of the free (hence flat) `R`-modules `A_n`;
* `flat_mod_pow_completion` (below) : the dévissage `A′ ⧸ pⁿA′` is flat over `R ⧸ pⁿR`, obtained
  from `A ⧸ pⁿA` (base change of the flat `A`) and the canonical identification
  `A′ ⧸ pⁿA′ ≅ A ⧸ pⁿA` (`AdicCompletion.evalₐ` is surjective with kernel `pⁿ`);
* `smulRegular_famClosure` and `torsionFree_completion` : `p` is a non-zero-divisor of `A′`;
* `isAdicComplete` : `A′` is `p`-adically complete;
* `Work.DSM2b.exists_pow_sub_mem_ker_aux` : the elementwise Artin–Rees lemma over Noetherian `R`;
* `Work.DSM1p.Assembly.syzygy_mod_pow` : syzygies modulo `pⁿ` with the Artin–Rees loss.
-/

namespace Work.DSM1p.Family

open Work.DSM1p

universe u

/-- **Dévissage for the `p`-adic completion of the root closure.**  The `n`-th layer
`A′ ⧸ pⁿA′` of the `p`-adic completion of `A` is flat over `R ⧸ pⁿR`.

The level-`n` coordinate projection `evalₙ : A′ → A ⧸ pⁿA` of the adic completion is surjective
with kernel `pⁿA′` (the ideal `p A` being finitely generated), and it is compatible with the
`R ⧸ pⁿ`-algebra structures; hence `A′ ⧸ pⁿA′ ≅ A ⧸ pⁿA` as `R ⧸ pⁿ`-algebras, and the latter is
flat because `A` is flat over `R` (`flat_closure`) and reduction modulo `pⁿ` is base change. -/
private theorem flat_mod_pow_completion (R : Type u) [CommRing R] (p : ℕ) (hp0 : p ≠ 0)
    {d : ℕ} (x : Fin d → R) (n : ℕ) :
    Module.Flat (R ⧸ Ideal.span {(p : R) ^ n})
      (FamCompletion R p x ⧸
        (Ideal.span {(p : R) ^ n}).map (algebraMap R (FamCompletion R p x))) := by
  haveI : Module.Flat R (FamClosure R p x) := flat_closure R p x hp0
  have hS : Module.Flat (R ⧸ Ideal.span {(p : R) ^ n})
      (FamClosure R p x ⧸
        (Ideal.span {(p : R) ^ n}).map (algebraMap R (FamClosure R p x))) :=
    Work.DSM1p.Root.flat_quot_map R (FamClosure R p x) (Ideal.span {(p : R) ^ n})
  have hI : (Ideal.span {(p : R) ^ n}).map (algebraMap R (FamClosure R p x))
      = Ideal.span {(p : FamClosure R p x)} ^ n := by
    rw [Ideal.span_singleton_pow, Ideal.map_span]
    simp
  have hcomp : (algebraMap (FamClosure R p x) (FamCompletion R p x)).comp
        (algebraMap R (FamClosure R p x)) = algebraMap R (FamCompletion R p x) := by
    ext y
    rfl
  have hIB : (Ideal.span {(p : FamClosure R p x)} ^ n).map
        (algebraMap (FamClosure R p x) (FamCompletion R p x))
      = (Ideal.span {(p : R) ^ n}).map (algebraMap R (FamCompletion R p x)) := by
    rw [← hI, Ideal.map_map, hcomp]
  have hFG : (Ideal.span {(p : FamClosure R p x)}).FG := ⟨{(p : FamClosure R p x)}, by simp⟩
  have hker := Work.DSM1p.Assembly.ker_evalₐ_eq_map (Ideal.span {(p : FamClosure R p x)}) hFG n
  let eB : (FamCompletion R p x ⧸
        (Ideal.span {(p : R) ^ n}).map (algebraMap R (FamCompletion R p x)))
      ≃ₐ[FamClosure R p x]
      (FamClosure R p x ⧸
        (Ideal.span {(p : R) ^ n}).map (algebraMap R (FamClosure R p x))) :=
    (Ideal.quotientEquivAlgOfEq (FamClosure R p x) hIB.symm).trans <|
      (Ideal.quotientEquivAlgOfEq (FamClosure R p x) hker).symm.trans <|
      (Ideal.quotientKerAlgEquivOfSurjective
        (AdicCompletion.surjective_evalₐ (Ideal.span {(p : FamClosure R p x)}) n)).trans <|
      (Ideal.quotientEquivAlgOfEq (FamClosure R p x) hI.symm)
  have e : (FamCompletion R p x ⧸
      (Ideal.span {(p : R) ^ n}).map (algebraMap R (FamCompletion R p x)))
      ≃ₐ[R ⧸ Ideal.span {(p : R) ^ n}]
      (FamClosure R p x ⧸
        (Ideal.span {(p : R) ^ n}).map (algebraMap R (FamClosure R p x))) :=
    { eB.toRingEquiv with
      commutes' := fun y => by
        induction y using Quotient.inductionOn with
        | _ r =>
          show eB.toRingEquiv (algebraMap (R ⧸ Ideal.span {(p : R) ^ n})
              (FamCompletion R p x ⧸
                (Ideal.span {(p : R) ^ n}).map (algebraMap R (FamCompletion R p x)))
              (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}) r))
            = algebraMap (R ⧸ Ideal.span {(p : R) ^ n})
              (FamClosure R p x ⧸
                (Ideal.span {(p : R) ^ n}).map (algebraMap R (FamClosure R p x)))
              (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}) r)
          rw [show algebraMap (R ⧸ Ideal.span {(p : R) ^ n})
                (FamCompletion R p x ⧸
                  (Ideal.span {(p : R) ^ n}).map (algebraMap R (FamCompletion R p x)))
                (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}) r)
              = Ideal.Quotient.mk ((Ideal.span {(p : R) ^ n}).map
                  (algebraMap R (FamCompletion R p x)))
                  (algebraMap R (FamCompletion R p x) r) from Ideal.quotientMap_mk,
            show algebraMap (R ⧸ Ideal.span {(p : R) ^ n})
                (FamClosure R p x ⧸
                  (Ideal.span {(p : R) ^ n}).map (algebraMap R (FamClosure R p x)))
                (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}) r)
              = Ideal.Quotient.mk ((Ideal.span {(p : R) ^ n}).map
                  (algebraMap R (FamClosure R p x)))
                  (algebraMap R (FamClosure R p x) r) from Ideal.quotientMap_mk]
          change eB.toRingEquiv (Ideal.Quotient.mk ((Ideal.span {(p : R) ^ n}).map
                (algebraMap R (FamCompletion R p x)))
                (algebraMap R (FamCompletion R p x) r))
            = Ideal.Quotient.mk ((Ideal.span {(p : R) ^ n}).map
                (algebraMap R (FamClosure R p x))) (algebraMap R (FamClosure R p x) r)
          dsimp only [eB]
          simp only [AlgEquiv.coe_toRingEquiv, Function.comp_apply,
            AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_symm,
            Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk,
            AdicCompletion.evalₐ_of,
            show algebraMap R (FamCompletion R p x) r
              = AdicCompletion.of (Ideal.span {(p : FamClosure R p x)})
                  (FamClosure R p x) (algebraMap R (FamClosure R p x) r) from rfl]
          exact Ideal.quotientEquivAlgOfEq_mk (R₁ := FamClosure R p x) (h := hI.symm)
            (x := algebraMap R (FamClosure R p x) r) }
  haveI := hS
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- `p`, viewed in the root closure, is a non-zero-divisor: this follows from the flatness of the
root closure and the regularity of `p` on `R` (a non-zero-divisor of the base stays a
non-zero-divisor on any flat module). -/
private theorem smulRegular_famClosure (R : Type u) [CommRing R] (p : ℕ) (hp0 : p ≠ 0)
    {d : ℕ} (x : Fin d → R) (hp : IsSMulRegular R p) :
    IsSMulRegular (FamClosure R p x) (p : FamClosure R p x) := by
  haveI : Module.Flat R (FamClosure R p x) := flat_closure R p x hp0
  have h1 : IsSMulRegular (FamClosure R p x) ((p : ℕ) : R) :=
    Module.Flat.isSMulRegular_of_isRegular (isRegular_natCast.mpr hp)
  have h2 : IsSMulRegular (FamClosure R p x)
      (algebraMap R (FamClosure R p x) ((p : ℕ) : R)) :=
    (isSMulRegular_algebraMap_iff (M := FamClosure R p x) (A := FamClosure R p x)).mpr h1
  rwa [map_natCast] at h2

theorem flat_completion (R : Type*) [CommRing R] [IsNoetherianRing R] (p : ℕ) (hp0 : p ≠ 0)
    (hp : IsSMulRegular R p) {d : ℕ} (x : Fin d → R) :
    Module.Flat R (Work.DSM1p.FamCompletion R p x) := by
  -- `A′` is `p`-adically complete
  haveI hcomp : IsAdicComplete (Ideal.span {algebraMap R (FamCompletion R p x) (p : R)})
      (FamCompletion R p x) := by
    rw [map_natCast]
    exact isAdicComplete R p x
  -- `p` is a non-zero-divisor of `A′`
  have hregB : IsSMulRegular (FamCompletion R p x)
      (algebraMap R (FamCompletion R p x) (p : R)) := by
    rw [map_natCast]
    exact torsionFree_completion R p x (smulRegular_famClosure R p hp0 x hp)
  refine Work.DSM2b.flat_of_flat_mod_base_aux (R := R) (B := FamCompletion R p x) (p : R)
    hregB (fun n => flat_mod_pow_completion R p hp0 x n)
    (fun g => Work.DSM2b.exists_pow_sub_mem_ker_aux (p : R) g)
    (fun g c hAR hflat => Work.DSM1p.Assembly.syzygy_mod_pow (R := R)
      (B := FamCompletion R p x) (p : R) g c hAR hflat)

end Work.DSM1p.Family
