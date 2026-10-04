import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Galerkin
import Submission.Work.Diff.STE.D.ChartData_Rstar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer D: the Galerkin coefficient map `genMap` has smooth chart data

`Work.Diff.STE.D.ChartData h` is the smoothness of the chart matrix of a section `h : Bil I M` (in
the coordinate frame of `extChartAt I x₀`), on every chart target.  It is exactly the analytic input
which turns a positive definite section into a global smooth metric (`Work.Diff.STE.D.smetOf`).

The present file proves that the coefficient-to-section map of the Galerkin scheme

  `genMap D ε c = Σ_z c z • jSym D ε z`,   `jSym D ε z = jFamily D ε z + jFamily D ε (idxSwap ε z)`

satisfies `ChartData` for **every** coefficient family `c`.

The proof has two ingredients:

* `ChartData` is preserved by addition, scalar multiplication and finite sums (the chart matrix
  `y ↦ (i j ↦ h (χ⁻¹y) (eᵢ) (eⱼ))` is linear in `h`, so this is `ContDiffOn.add`,
  `ContDiffOn.const_smul`, `contDiffOn_const`);
* every spanning vector `jVec D ε i a b q` satisfies `ChartData`.  This is the smoothness of a
  *single* summand of a reconstruction: `jVec D ε i a b q` is `D.Rstar i u` for the coefficient
  family `u c d = if (c,d) = (a,b) then modeFun q else 0` (`Rstar_expand`), and `modeFun` is the
  real or imaginary part of a Fourier character, hence `C^∞`; so
  `Work.Diff.STE.D.ChartData_Rstar` applies.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.D

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/- Auxiliary lemmas for `ChartData_genMap`; they live in their own namespace so that they can never
clash with the (identically shaped) ingredients proved elsewhere in the workspace. -/
namespace GenMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless] [T2Space M]

noncomputable section

/-! ## `ChartData` is preserved by finite linear combinations -/

/-- The zero section has smooth chart data. -/
lemma chartData_zero :
    ChartData (I := I) (M := M) (0 : Work.Diff.STE.Bil (I := I) (M := M)) := by
  intro x₀
  change ContDiffOn ℝ (⊤ : ℕ∞)
    (chartMat (I := I) (0 : Work.Diff.STE.Bil (I := I) (M := M)) x₀)
    (extChartAt I x₀).target
  have h3 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun _ : E => (0 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ))
      (extChartAt I x₀).target := contDiffOn_const
  exact h3.congr (fun y hy => rfl)

/-- The sum of two sections with smooth chart data has smooth chart data. -/
lemma chartData_add {h k : Work.Diff.STE.Bil (I := I) (M := M)}
    (hh : ChartData (I := I) (M := M) h) (hk : ChartData (I := I) (M := M) k) :
    ChartData (I := I) (M := M) (h + k) := by
  intro x₀
  change ContDiffOn ℝ (⊤ : ℕ∞) (chartMat (I := I) (h + k) x₀) (extChartAt I x₀).target
  exact ((hh x₀).add (hk x₀)).congr (fun y hy => rfl)

/-- A scalar multiple of a section with smooth chart data has smooth chart data. -/
lemma chartData_smul (r : ℝ) {h : Work.Diff.STE.Bil (I := I) (M := M)}
    (hh : ChartData (I := I) (M := M) h) :
    ChartData (I := I) (M := M) (r • h) := by
  intro x₀
  change ContDiffOn ℝ (⊤ : ℕ∞) (chartMat (I := I) (r • h) x₀) (extChartAt I x₀).target
  exact ((hh x₀).const_smul r).congr (fun y hy => rfl)

/-- A finite linear combination of sections with smooth chart data has smooth chart data. -/
lemma chartData_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Work.Diff.STE.Bil (I := I) (M := M))
    (h : ∀ i ∈ s, ChartData (I := I) (M := M) (f i)) :
    ChartData (I := I) (M := M) (∑ i ∈ s, f i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using chartData_zero (I := I) (M := M)
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    exact chartData_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-! ## The Fourier character and the modes are smooth -/

/-- The Fourier character `x ↦ exp (2πi k·x)` is smooth. -/
lemma contDiff_fourierExp (n : ℕ) (m : Fin n → ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.fourierExp m) := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ =>
      ((∑ i, ((m i : ℝ)) * z i : ℝ) : ℂ)) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => (∑ i, ((m i : ℝ)) * z i : ℝ)) := by
      fun_prop
    exact Complex.ofRealCLM.contDiff.comp h1
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ =>
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
        ((∑ i, ((m i : ℝ)) * z i : ℝ) : ℂ))) :=
    Complex.contDiff_exp.comp
      ((contDiff_const (c := 2 * (Real.pi : ℂ) * Complex.I)).mul hlin)
  have heq : (fun z : Fin n → ℝ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
      ((∑ i, ((m i : ℝ)) * z i : ℝ) : ℂ))) = Work.Diff.STE.fourierExp m := by
    funext z
    simp only [Work.Diff.STE.fourierExp]
    push_cast
    ring
  rwa [heq] at h2

/-- The selected real Fourier mode `modeFun q` is smooth. -/
lemma contDiff_modeFun (n : ℕ) {ε : ℝ} (q : Work.Diff.STE.B3.QIdx n ε) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.modeFun n q) := by
  obtain ⟨⟨m, _hm⟩, b⟩ := q
  cases b
  · show ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => (Work.Diff.STE.fourierExp m z).re)
    exact Complex.reCLM.contDiff.comp (contDiff_fourierExp n m)
  · show ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => (Work.Diff.STE.fourierExp m z).im)
    exact Complex.imCLM.contDiff.comp (contDiff_fourierExp n m)

/-! ## The spanning vectors of the Galerkin family -/

/-- **A spanning vector is a single-summand reconstruction**: `jVec D ε i a b q` is `Rstar i u`
for the coefficient family which is `modeFun q` at the single pair `(a,b)` and `0` elsewhere. -/
lemma jVec_eq_Rstar {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    (q : Work.Diff.STE.B3.QIdx (Module.finrank ℝ E) ε) :
    Work.Diff.STE.B3.jVec (I := I) (M := M) D ε i a b q
      = D.Rstar i (fun c d z =>
          if c = a ∧ d = b then Work.Diff.STE.B3.modeFun (Module.finrank ℝ E) q z else 0) := by
  rw [Work.Diff.STE.B3.Rstar_expand]
  funext p
  simp only [Finset.sum_apply, Work.Diff.STE.B3.jVec]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro d _ hd
      have h : (Work.Diff.STE.B3.jWgt (I := I) (M := M) D i p *
          (if a = a ∧ d = b then
            Work.Diff.STE.B3.modeFun (Module.finrank ℝ E) q
              (Work.Diff.STE.coord (I := I) (D.x₀ i) p) else 0)) = 0 := by
        rw [if_neg (by simp [hd]), mul_zero]
      rw [h]
      ext u w
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, smul_eq_mul,
        zero_mul]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · intro c _ hc
    refine Finset.sum_eq_zero (fun d _ => ?_)
    have h : (Work.Diff.STE.B3.jWgt (I := I) (M := M) D i p *
        (if c = a ∧ d = b then
          Work.Diff.STE.B3.modeFun (Module.finrank ℝ E) q
            (Work.Diff.STE.coord (I := I) (D.x₀ i) p) else 0)) = 0 := by
      rw [if_neg (by simp [hc]), mul_zero]
    rw [h]
    ext u w
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, smul_eq_mul,
      zero_mul]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- **Every spanning vector of the Galerkin family has smooth chart data.**  This is
`ChartData_Rstar` applied to the single-summand coefficient family of `jVec_eq_Rstar`. -/
theorem jVec_chartData {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    (q : Work.Diff.STE.B3.QIdx (Module.finrank ℝ E) ε) :
    ChartData (I := I) (M := M) (Work.Diff.STE.B3.jVec (I := I) (M := M) D ε i a b q) := by
  rw [jVec_eq_Rstar (I := I) (M := M) D ε i a b q]
  refine ChartData_Rstar D i _ ?_
  intro c d
  split_ifs with h
  · exact contDiff_modeFun _ q
  · exact contDiff_const

end

end GenMap

theorem ChartData_genMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless] [T2Space M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Work.Diff.STE.D.ChartData (I := I) (M := M)
      (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c) := by
  classical
  -- `genMap` is the finite sum `Σ_z c z • jSym D ε z`: the closure of `ChartData` under finite
  -- linear combinations reduces the claim to the individual symmetrised spanning vectors.
  refine GenMap.chartData_finset_sum (I := I) (M := M) Finset.univ
    (fun z => c z • jSym (I := I) (M := M) D ε z) ?_
  intro z _
  refine GenMap.chartData_smul (I := I) (M := M) (c z) ?_
  have h1 : ChartData (I := I) (M := M)
      (Work.Diff.STE.B3.jFamily (I := I) (M := M) D ε z) := by
    simpa only [Work.Diff.STE.B3.jFamily] using
      GenMap.jVec_chartData (I := I) (M := M) D ε z.1 z.2.1 z.2.2.1 z.2.2.2
  have h2 : ChartData (I := I) (M := M)
      (Work.Diff.STE.B3.jFamily (I := I) (M := M) D ε
        (idxSwap (E := E) (ι₀ := ι₀) ε z)) := by
    simpa only [Work.Diff.STE.B3.jFamily] using
      GenMap.jVec_chartData (I := I) (M := M) D ε
        (idxSwap (E := E) (ι₀ := ι₀) ε z).1 (idxSwap (E := E) (ι₀ := ι₀) ε z).2.1
        (idxSwap (E := E) (ι₀ := ι₀) ε z).2.2.1 (idxSwap (E := E) (ι₀ := ι₀) ε z).2.2.2
  rw [jSym]
  exact GenMap.chartData_add (I := I) (M := M) h1 h2

end Work.Diff.STE.D
