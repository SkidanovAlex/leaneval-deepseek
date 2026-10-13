import Mathlib
import Submission.Work.DSM5c.Lp.chartDToLp_existsU
import Submission.Work.DSM5c.Lp.LpDefs
import Submission.Work.DSM5c.Lp.PiHelpers

namespace Work.DSM5c.Lp

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits
open scoped Simplicial

universe u

/-! ## The `(p) • ⊤ = ⊥` lemmas

The argument is in three steps, all of which are independent of the specific complex:

* `smul_top_quot_eq_bot`: the quotient `M ⧸ (I • ⊤)` is killed by `I` (it is a quotient of `M` by a
  submodule containing `I • ⊤`);
* `smul_top_bot_pi`: a (possibly infinite) product of modules killed by `I` is killed by `I`;
* `chartLQObj_smul_top_bot`: each term `L_S = D_S ⧸ (p) • ⊤` of the presheaf `chartLQ` is killed by
  `(p)`. -/

/-- The quotient of a module by `I • ⊤` is killed by `I`: `I • ⊤ = ⊥` there. -/
lemma smul_top_quot_eq_bot {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    I • (⊤ : Submodule R (M ⧸ (I • (⊤ : Submodule R M)))) = ⊥ := by
  rw [eq_bot_iff]
  refine Submodule.smul_le.2 (fun r hr x _ => ?_)
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (I • (⊤ : Submodule R M)) x
  rw [Submodule.mem_bot, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hr Submodule.mem_top

/-- A product of `R`-modules killed by `I` is killed by `I`.  (No finiteness is needed: an
element of a product is determined by its components, and `I` acts componentwise.) -/
lemma smul_top_bot_pi {R : Type*} [CommRing R] {ι : Type*} (Z : ι → ModuleCat R) (I : Ideal R)
    (h : ∀ i, I • (⊤ : Submodule R (Z i)) = ⊥) :
    I • (⊤ : Submodule R ↥(∏ᶜ Z)) = ⊥ := by
  rw [eq_bot_iff]
  refine Submodule.smul_le.2 (fun r hr x _ => ?_)
  rw [Submodule.mem_bot]
  have key : r • ((ModuleCat.piIsoPi Z).toLinearEquiv x) = 0 := by
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, CategoryTheory.Iso.toLinearEquiv_apply,
      ModuleCat.piIsoPi_hom_ker_subtype_apply]
    have hmem : r • ((Pi.π Z i).hom x) ∈ I • (⊤ : Submodule R (Z i)) :=
      Submodule.smul_mem_smul hr Submodule.mem_top
    rw [h i] at hmem
    simpa using hmem
  have hx : x = (ModuleCat.piIsoPi Z).toLinearEquiv.symm ((ModuleCat.piIsoPi Z).toLinearEquiv x) :=
    (LinearEquiv.symm_apply_apply _ _).symm
  rw [hx, ← map_smul, key, map_zero]

/-- Each term `L_S = D_S ⧸ (p) • ⊤` of the presheaf `chartLQ` is killed by `(p)`. -/
lemma chartLQObj_smul_top_bot {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W]
    [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [Finite ι]
    [DecidableEq ι] (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : (Finset ι)ᵒᵖᵒᵖ) :
    Ideal.span {(p : W)} • (⊤ : Submodule W
      (Work.DSM5c.Lp.chartLQObj Q hθ t tr htr0 htr j₀ e S)) = ⊥ := by
  letI := Work.DSM5c.chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
  exact smul_top_quot_eq_bot (R := W) (Ideal.span {(p : W)})

/-- **The ideal `(p)` acts by `0` on the mod-`p` chart Čech complex.**  Each term `L_S = D_S ⧸ (p)·⊤`
of `Č(chartLQ)` is a module killed by `p` (the `p`-multiple of the whole module `D_S` was quotiented
out by construction), so `(p) • ⊤ = ⊥` termwise, hence also on the finite products that are the
terms of the Čech complex.  Blueprint: `Submission/Work/DSM5c/Lp/probe/Stmts.lean`
(`stmt_chartLQ_smul_top_bot`).  Useful ingredients: `Work.DSM5c.mem_chartDpTop` (`rfl`-form of
`chartDpTop = (p) • ⊤`), `Submodule.Quotient.mk_surjective`, `ModuleCat.piIsoPi`,
`Work.DSM5c.Lp.mem_smul_top_pi_iff`. -/
theorem chartLQ_smul_top_botU {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W]
    [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [Finite ι]
    [DecidableEq ι] (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (q : ℕ) :
    Ideal.span {(p : W)} • (⊤ : Submodule W
      (((cechComplexFunctor (chartIdx ι)).obj
        (Work.DSM5c.Lp.chartLQ Q hθ t tr htr0 htr j₀ e)).X q)) = ⊥ := by
  -- The degree-`q` term of `Č(chartLQ)` is a product of copies of the term-objects
  -- `chartLQObj ... S` of the presheaf at the `q`-fold products of the cover `chartIdx ι`.
  change Ideal.span {(p : W)} • (⊤ : Submodule W ↥(∏ᶜ (fun i =>
    (Work.DSM5c.Lp.chartLQ Q hθ t tr htr0 htr j₀ e).obj
      (Opposite.op (((Functor.rightOp (FormalCoproduct.cechFunctor.obj
        (FormalCoproduct.mk ι (chartIdx ι)))).obj ⦋q⦌).unop.obj i))))) = ⊥
  exact smul_top_bot_pi _ _ (fun i => chartLQObj_smul_top_bot Q hθ t tr htr0 htr j₀ e _)

end Work.DSM5c.Lp
