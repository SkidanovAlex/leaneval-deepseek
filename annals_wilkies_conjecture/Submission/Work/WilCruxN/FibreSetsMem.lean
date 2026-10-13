import Mathlib
import Submission.Work.WilCruxN.FSMemFail

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilCruxN

open WilkiesDesign WilkiesDesign.CG
open Work.WilG4c
open Work.WilCruxN.FSA

/-- **N4d plumbing: the pointwise failure set and the modulus sets are `Ω`-definable.**

Same statement as `Work.WilCrux.FibreSetsMem` (`Submission/Work/WilCrux/FibreSetsMem.lean`, whose
proof body is complete but currently does not compile; the sibling files `FibreSetsShapes.lean`,
`FibreSetsAux.lean`, `FibreSetsFail.lean`, `PowSetMem.lean`, `supBall_mem.lean` under
`Submission/Work/WilCrux/` contain the shape-calculus scaffolding: `failShape`, `modShape`,
`failShape_Real`, `modShape_Real`, `supBallSet`, `ballConstSet`, `supBallSet_mem`,
`ballConstSet_mem`).  Port that proof into your own module(s) (fixing the errors), or re-prove it
with `Work.WilG4c.PKS` (`Real_mem_Omega`, `Deg_le`, `exb`, `allb`, ...).

Route: both sets are first-order conditions over the single atom `famGraph f` — read `u = f w z`
from `(w,z,u) ∈ famGraph f`.  The first conjunct is the shape `∃ε>0 ∀δ>0 ∃z, z ≠ 0 ∧ ‖z‖ < δ ∧
ε ≤ |f w z|` (this is `¬ Tendsto (f w) (𝓝[{0}ᶜ] 0) (𝓝 0)`; bridge with
`Work.WilCrux.not_tendsto_punctured_iff`, or reprove the ε-δ translation locally, using
`Work.WilkG4c.forall_sq_lt_sq_iff_norm` to pass from the sup-norm to coordinatewise absolute
values).  The second conjunct is `∀z, z ≠ 0 → ‖z‖ < t/(n+1) → |f w z| < 1/(k+1)`, where `z ≠ 0`
is handled by the `supBallSet` trick (`∀ j, |z j| < c` plus `∃ j, z j ≠ 0`).  The bounds `t/(n+1)`
and `1/(k+1)` enter only as coefficients of degree-≤4 polynomial atoms, so the resulting format
depends only on `a, b, F` and the degree is `Atoms * (D + Δ + 10)` for a constant `Δ` — i.e.
`c.eval D` for a polynomial `c` of the required shape.  Keep each file you write under ~15 KB
(`maxHeartbeats` at most 4000000) so that the build guard accepts it; split into several modules
if needed.  Do NOT `sorry` and do NOT use any declaration whose `#print axioms` mentions `sorryAx`
(in particular not `Work.WilCrux.FibreSetsMem` while it does not compile, and not
`Work.WilCrux.FibreSetsFail`/`FibreSetsAux`/`FibreSetsShapes` unless you have checked them — you
may copy their `sorry`-free parts into your own module). -/
theorem FibreSetsMem (S : WilkiesDesign.SOMin) {a b F : ℕ} (t : ℝ) :
    (∃ (A : ℕ) (c : Polynomial ℕ), ∀ (D : ℕ) (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F D (a + b + 1) →
      {w : Fin a → ℝ | ¬ Filter.Tendsto (f w)
        (nhdsWithin (0 : Fin b → ℝ) {(0 : Fin b → ℝ)}ᶜ) (nhds 0)} ∈ S.Ω A (c.eval D) a) ∧
    (∃ (A : ℕ) (c : Polynomial ℕ), ∀ (D : ℕ) (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F D (a + b + 1) → ∀ (k n : ℕ),
      {w : Fin a → ℝ | ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < t / ((n : ℝ) + 1) →
        |f w z| < 1 / ((k : ℝ) + 1)} ∈ S.Ω A (c.eval D) a) := by
  set Δ : ℕ := max 4 (4 * b) + 1 with hΔdef
  set F' : ℕ := F + ((a + b + 1) + (b + 6) + 4) with hF'def
  have hzero : WilkiesDesign.CG.famGraph
      (fun (_ : Fin a → ℝ) (_ : Fin b → ℝ) => (0 : ℝ)) ∈ S.Ω F' Δ (a + b + 1) := by
    have h := S.hyp (a + b + 1)
      (MvPolynomial.X (Fin.last (a + b)) : MvPolynomial (Fin (a + b + 1)) ℝ)
    have htd : (MvPolynomial.X (Fin.last (a + b)) :
        MvPolynomial (Fin (a + b + 1)) ℝ).totalDegree ≤ 1 := by
      rw [MvPolynomial.totalDegree_X]
    have hset : {x : Fin (a + b + 1) → ℝ |
          MvPolynomial.eval x (MvPolynomial.X (Fin.last (a + b))) = 0}
        = WilkiesDesign.CG.famGraph (fun (_ : Fin a → ℝ) (_ : Fin b → ℝ) => (0 : ℝ)) := by
      rw [← Work.WilG4c.graphOf_famFun (p := a) (N := b)
        (f := fun (_ : Fin a → ℝ) (_ : Fin b → ℝ) => (0 : ℝ))]
      ext x
      simp only [graphOf, Set.mem_ofPred_eq, Work.WilG4c.famFun, MvPolynomial.eval_X]
    rw [← hset]
    refine Work.WilG5.mem_mono
      (Work.WilG5.mem_mono h (a + b + 1) 1 le_rfl htd) F' Δ ?_ ?_
    · rw [hF'def]; omega
    · rw [hΔdef]; omega
  have hsup : supBallSet b ∈ S.Ω F' Δ (b + 1) :=
    supBallSet_mem S b F' Δ (by rw [hF'def]; omega) (by rw [hΔdef]; omega)
  let d0 : PKS S F' Δ a :=
    failShape S F' Δ (fun (_ : Fin a → ℝ) (_ : Fin b → ℝ) => (0 : ℝ)) hzero hsup
  let c0 : PKS S F' Δ a :=
    modShape S F' Δ (fun (_ : Fin a → ℝ) (_ : Fin b → ℝ) => (0 : ℝ)) hzero 0 0
      (ballConstSet_mem S b F' Δ 0 (by rw [hF'def]; omega) (by rw [hΔdef]; omega))
  refine ⟨?_, ?_⟩
  · refine ⟨d0.Fmt, Polynomial.C (d0.Atoms * (Δ + 10)) + Polynomial.C d0.Atoms * Polynomial.X, ?_⟩
    intro D f hf
    have hf' : WilkiesDesign.CG.famGraph f ∈ S.Ω F' (D + Δ) (a + b + 1) :=
      Work.WilG5.mem_mono hf F' (D + Δ) (by rw [hF'def]; omega) (by omega)
    have hsup' : supBallSet b ∈ S.Ω F' (D + Δ) (b + 1) :=
      supBallSet_mem S b F' (D + Δ) (by rw [hF'def]; omega) (by rw [hΔdef]; omega)
    have hmem := Work.WilG4c.PKS.Real_mem_Omega (failShape S F' (D + Δ) f hf' hsup')
    have hreal := failShape_Real S F' (D + Δ) f hf' hsup'
    rw [hreal] at hmem
    have hFmt : (failShape S F' (D + Δ) f hf' hsup').Fmt = d0.Fmt :=
      failShape_Fmt_eq S F' (D + Δ) Δ f hf' hsup'
        (fun (_ : Fin a → ℝ) (_ : Fin b → ℝ) => (0 : ℝ)) hzero hsup
    rw [hFmt] at hmem
    have hAtoms : (failShape S F' (D + Δ) f hf' hsup').Atoms = d0.Atoms :=
      failShape_Atoms_eq S F' (D + Δ) Δ f hf' hsup'
        (fun (_ : Fin a → ℝ) (_ : Fin b → ℝ) => (0 : ℝ)) hzero hsup
    have hDeg : (failShape S F' (D + Δ) f hf' hsup').Deg ≤ d0.Atoms * (D + Δ + 2 + 8) := by
      have h := Work.WilG4c.PKS.Deg_le (failShape S F' (D + Δ) f hf' hsup')
      rw [hAtoms] at h
      exact h
    have hset : {w : Fin a → ℝ | ¬ Filter.Tendsto (f w)
          (nhdsWithin (0 : Fin b → ℝ) {(0 : Fin b → ℝ)}ᶜ) (nhds 0)}
        = {w : Fin a → ℝ | ∃ ε > 0, ∀ δ > 0, ∃ z : Fin b → ℝ,
          z ≠ 0 ∧ (∀ j, (z j) ^ 2 < δ ^ 2) ∧ ε ≤ |f w z|} := by
      ext w
      constructor
      · intro h
        simp only [Set.mem_ofPred_eq] at h ⊢
        rw [not_punctured_limit_iff] at h
        obtain ⟨ε, hε, hδ⟩ := h
        exact ⟨ε, hε, fun δ hd => by
          obtain ⟨z, hz0, hzc, hzε⟩ := hδ δ hd
          exact ⟨z, hz0, (forall_sq_lt_sq_iff_norm hd).mpr hzc, hzε⟩⟩
      · intro h
        simp only [Set.mem_ofPred_eq] at h ⊢
        rw [not_punctured_limit_iff]
        obtain ⟨ε, hε, hδ⟩ := h
        exact ⟨ε, hε, fun δ hd => by
          obtain ⟨z, hz0, hzc, hzε⟩ := hδ δ hd
          exact ⟨z, hz0, (forall_sq_lt_sq_iff_norm hd).mp hzc, hzε⟩⟩
    rw [hset]
    have hb : (Polynomial.C (d0.Atoms * (Δ + 10)) + Polynomial.C d0.Atoms * Polynomial.X).eval D
        = d0.Atoms * (D + Δ + 2 + 8) := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      ring
    have hgoal : {w : Fin a → ℝ | ∃ ε > 0, ∀ δ > 0, ∃ z : Fin b → ℝ,
          z ≠ 0 ∧ (∀ j, (z j) ^ 2 < δ ^ 2) ∧ ε ≤ |f w z|}
        ∈ S.Ω d0.Fmt (d0.Atoms * (D + Δ + 2 + 8)) a :=
      Work.WilG5.mem_mono hmem d0.Fmt (d0.Atoms * (D + Δ + 2 + 8)) le_rfl hDeg
    rwa [← hb] at hgoal
  · refine ⟨c0.Fmt, Polynomial.C (c0.Atoms * (Δ + 10)) + Polynomial.C c0.Atoms * Polynomial.X, ?_⟩
    intro D f hf k n
    have hf' : WilkiesDesign.CG.famGraph f ∈ S.Ω F' (D + Δ) (a + b + 1) :=
      Work.WilG5.mem_mono hf F' (D + Δ) (by rw [hF'def]; omega) (by omega)
    have hball' : ballConstSet b (t / ((n : ℝ) + 1)) ∈ S.Ω F' (D + Δ) b :=
      ballConstSet_mem S b F' (D + Δ) (t / ((n : ℝ) + 1))
        (by rw [hF'def]; omega) (by rw [hΔdef]; omega)
    have hmem := Work.WilG4c.PKS.Real_mem_Omega
      (modShape S F' (D + Δ) f hf' (t / ((n : ℝ) + 1)) (1 / ((k : ℝ) + 1)) hball')
    have hreal := modShape_Real S F' (D + Δ) f hf' (t / ((n : ℝ) + 1))
      (1 / ((k : ℝ) + 1)) hball'
    rw [hreal] at hmem
    have hFmt : (modShape S F' (D + Δ) f hf' (t / ((n : ℝ) + 1)) (1 / ((k : ℝ) + 1))
        hball').Fmt = c0.Fmt :=
      modShape_Fmt_eq S F' (D + Δ) Δ f hf' (t / ((n : ℝ) + 1)) (1 / ((k : ℝ) + 1)) hball'
        (fun (_ : Fin a → ℝ) (_ : Fin b → ℝ) => (0 : ℝ)) hzero 0 0
        (ballConstSet_mem S b F' Δ 0 (by rw [hF'def]; omega) (by rw [hΔdef]; omega))
    rw [hFmt] at hmem
    have hAtoms : (modShape S F' (D + Δ) f hf' (t / ((n : ℝ) + 1)) (1 / ((k : ℝ) + 1))
        hball').Atoms = c0.Atoms :=
      modShape_Atoms_eq S F' (D + Δ) Δ f hf' (t / ((n : ℝ) + 1)) (1 / ((k : ℝ) + 1)) hball'
        (fun (_ : Fin a → ℝ) (_ : Fin b → ℝ) => (0 : ℝ)) hzero 0 0
        (ballConstSet_mem S b F' Δ 0 (by rw [hF'def]; omega) (by rw [hΔdef]; omega))
    have hDeg : (modShape S F' (D + Δ) f hf' (t / ((n : ℝ) + 1)) (1 / ((k : ℝ) + 1))
        hball').Deg ≤ c0.Atoms * (D + Δ + 2 + 8) := by
      have h := Work.WilG4c.PKS.Deg_le
        (modShape S F' (D + Δ) f hf' (t / ((n : ℝ) + 1)) (1 / ((k : ℝ) + 1)) hball')
      rw [hAtoms] at h
      exact h
    have hb : (Polynomial.C (c0.Atoms * (Δ + 10)) + Polynomial.C c0.Atoms * Polynomial.X).eval D
        = c0.Atoms * (D + Δ + 2 + 8) := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      ring
    have hgoal : {w : Fin a → ℝ | ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < t / ((n : ℝ) + 1) →
          |f w z| < 1 / ((k : ℝ) + 1)}
        ∈ S.Ω c0.Fmt (c0.Atoms * (D + Δ + 2 + 8)) a :=
      Work.WilG5.mem_mono hmem c0.Fmt (c0.Atoms * (D + Δ + 2 + 8)) le_rfl hDeg
    rwa [← hb] at hgoal

end Work.WilCruxN
