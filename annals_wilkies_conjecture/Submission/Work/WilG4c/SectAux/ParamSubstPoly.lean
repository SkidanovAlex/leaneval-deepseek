import Mathlib
import Submission.Work.WilG4c.graphOfCompGen
import Submission.Work.WilG4c.ParCompGraphMem
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.YbddAux
import Submission.Work.WilG4c.FLemAPI

/-!
# Parametric substitution of a family into `Ω`

`Work.WilG4c.ParCompGraphMem` proves that the *parametric composition* of an `Ω`-definable
family with an `Ω`-definable parameter map is again `Ω`-definable, but it absorbs the two
given formats into a single constant `a = a(F₀, A₀)` computed from `F₀` and `A₀`, and it
expresses the degree by evaluating a polynomial at the two given degrees.

The consumer of this file needs the two bounds *separately*: the format as the sum
`F₀ + A₀ + C₁` of the two given formats plus a constant, and the degree as
`D + (q+n) * A + C₂` in terms of the given degrees.  `famGraph_paramComp` below re-runs the
construction of `ParCompGraphMem` (the rectangular composition lemma `graphOfCompGen` applied
to the uncurried family and the parameter substitution) with these shapes, and
`ParamSubstPoly` specialises it to the situation where the two degrees are themselves the
values of given polynomials at `![D, r]`, so that the resulting degree bound can be written as
the evaluation of the single polynomial `bχ + (q+n) * bμ + C₂`.
-/

namespace Work.WilG4c.SectAux

open WilkiesDesign

/-- **Parametric composition of `Ω`-definable families, with separated constants.**
If the graph of the family `f` (in `q` parameters and `n` variables) is `Ω F₀ D` and each of
the `q` coordinate functions of the parameter map `g` has an `Ω A₀ A` graph, then the graph of
the composed family `(l, u) ↦ f (g l) u` is `Ω (F₀ + A₀ + C₁) (D + (q+n) * A + C₂)` for
constants `C₁, C₂` depending only on `S`, `p`, `q` and `n`. -/
theorem famGraph_paramComp (S : WilkiesDesign.SOMin) (p q n : ℕ) :
    ∃ (C₁ C₂ : ℕ),
      ∀ (F₀ A₀ D A : ℕ) (f : (Fin q → ℝ) → (Fin n → ℝ) → ℝ)
        (g : (Fin p → ℝ) → (Fin q → ℝ)),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F₀ D (q + n + 1) →
        (∀ j : Fin q, WilkiesDesign.graphOf (fun l : Fin p → ℝ => g l j) ∈
          S.Ω A₀ A (p + 1)) →
        WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (u : Fin n → ℝ) => f (g l) u) ∈
          S.Ω (F₀ + A₀ + C₁) (D + (q + n) * A + C₂) (p + n + 1) := by
  obtain ⟨C1, C2, hcomp⟩ := Work.WilG4c.graphOfCompGen S (q + n) (p + n)
  refine ⟨(2 * ((p + n + 1) + (p + 1)) + 1) + ((p + n) + 1) + C1, (q + n) * 2 + C2, ?_⟩
  intro F₀ A₀ D A f g hf hg
  -- the `q + n` coordinate graphs of the parameter substitution `pcgm_parIdx g`, at a common
  -- format and degree: the `q` parameter coordinates are the coordinate preimages of the
  -- graphs of `g` (degree `A + 2`), the `n` remaining ones are coordinate hyperplanes
  -- (degree `1`, padded up to `A + 2`).
  have hcoord : ∀ i : Fin (q + n),
      WilkiesDesign.graphOf (fun z : Fin (p + n) → ℝ => Work.WilG4c.pcgm_parIdx g z i) ∈
        S.Ω (A₀ + (2 * ((p + n + 1) + (p + 1)) + 1) + ((p + n) + 1)) (A + 2)
          (p + n + 1) := by
    intro i
    refine Fin.addCases (fun i' => ?_) (fun k => ?_) i
    · -- the `q` parameter coordinates
      have h : WilkiesDesign.graphOf
          (fun z : Fin (p + n) → ℝ => Work.WilG4c.pcgm_parIdx g z (Fin.castAdd n i')) ∈
          S.Ω (A₀ + 2 * ((p + n + 1) + (p + 1)) + 1) (A + 2) (p + n + 1) := by
        rw [Work.WilG4c.pcgm_graphOf_parIdx_fst g i']
        exact Work.WilG4c.GraphComp.subst_mem S (Work.WilG4c.pcgm_liftParIdx p n) (hg i')
      exact Work.WilG1.Omega.mono h (by omega) le_rfl
    · -- the `n` remaining coordinates
      have hset : (fun z : Fin (p + n) → ℝ => Work.WilG4c.pcgm_parIdx g z (Fin.natAdd q k))
          = (fun z : Fin (p + n) → ℝ => z (Fin.natAdd p k)) := by
        funext z
        simp [Work.WilG4c.pcgm_parIdx, Fin.append_right]
      rw [hset]
      exact Work.WilG1.Omega.mono
        (Work.WilG4c.pcgm_graphOf_projCoord_mem S (p + n) (Fin.natAdd p k))
        (by omega) (by omega)
  -- the rectangular composition lemma, applied to the uncurried family and the substitution
  have hcomp' := hcomp F₀ (A₀ + (2 * ((p + n + 1) + (p + 1)) + 1) + ((p + n) + 1)) D (A + 2)
    (Work.WilG4c.pcgm_compGFam f) (Work.WilG4c.pcgm_parIdx g)
    (by rwa [Work.WilG4c.pcgm_graphOf_compGFam]) hcoord
  rw [← Work.WilG4c.pcgm_famGraph_parComp f g] at hcomp'
  refine Work.WilG1.Omega.mono hcomp' (by omega) ?_
  rw [Nat.mul_add]
  omega

theorem ParamSubstPoly (S : WilkiesDesign.SOMin) (p q n : ℕ) :
    ∃ (C₁ C₂ : ℕ),
      ∀ (Aμ : ℕ) (bμ : MvPolynomial (Fin 2) ℕ) (a : ℕ) (bχ : MvPolynomial (Fin 2) ℕ)
        (D r : ℕ) (μ : (Fin p → ℝ) → (Fin q → ℝ)) (χ : Work.WilkG4c.ChartTuple q n),
        (∀ j : Fin q, WilkiesDesign.graphOf (fun l : Fin p → ℝ => μ l j) ∈
          S.Ω Aμ (MvPolynomial.eval ![D, r] bμ) (p + 1)) →
        (∀ j : Fin n, WilkiesDesign.CG.famGraph (χ j) ∈
          S.Ω a (MvPolynomial.eval ![D, r] bχ) (q + n + 1)) →
        ∀ j : Fin n,
          WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (t : Fin n → ℝ) => χ j (μ l) t) ∈
          S.Ω (Aμ + a + C₁)
            (MvPolynomial.eval ![D, r]
              (bχ + MvPolynomial.C (q + n) * bμ + MvPolynomial.C C₂)) (p + n + 1) := by
  obtain ⟨C₁, C₂, h⟩ := famGraph_paramComp S p q n
  refine ⟨C₁, C₂, ?_⟩
  intro Aμ bμ a bχ D r μ χ hμ hχ j
  have hmain := h a Aμ (MvPolynomial.eval ![D, r] bχ) (MvPolynomial.eval ![D, r] bμ)
    (χ j) μ (hχ j) hμ
  have hdeg : MvPolynomial.eval ![D, r]
        (bχ + MvPolynomial.C (q + n) * bμ + MvPolynomial.C C₂)
      = MvPolynomial.eval ![D, r] bχ + (q + n) * MvPolynomial.eval ![D, r] bμ + C₂ := by
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  rw [hdeg]
  exact Work.WilG1.Omega.mono hmain (by omega) le_rfl

end Work.WilG4c.SectAux
