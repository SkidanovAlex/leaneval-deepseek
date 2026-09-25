import Mathlib
import Submission.Work.NN.Final.l2SolverRegion
import Submission.Work.NN.Core.dbarLocalSolver
import Submission.Work.NN.Final.nabla_arr_Pi10
import Submission.Work.NN.Final.dbarCn_eq_of_basis
import Submission.Work.NN.Final.eLpNormEndgame

/-!
# The flat case of the uniform `L²`-solvability of `∂̄`, with the conclusion region as a parameter

`Work.NN.Final.UniformDbarL2` is the flat-model uniform solvability statement of the project.  This
file proves its *unperturbed* case (`A = 0`, i.e. the standard structure `Jstd`) with the conclusion
region as an arbitrary parameter `σ < 4`:

for every `0 < α < 1`, positive radii `ρ` and `0 < σ < 4` there is `C > 0` such that every smooth
`Jstd`-antilinear `(0,1)`-form `f` which is `∂̄`-closed on `pd n ρ 4` admits a `C¹` primitive `u` on
`pd n ρ σ` with

  `eLpNorm u 2 (vol.restrict (pd n ρ σ)) ≤ C · ∑_j holderNorm 0 α (f · e_j) (pd n ρ 4)`.

The proof is a direct application of the local `∂̄`-solver `Work.NN.Core.dbarLocalSolver` with data
region `pd n ρ 4` and solution region `pd n ρ σ` (the strict inclusion `σ ρ_j < 4 ρ_j` is exactly
`σ < 4`), together with:

* the array/form dictionary `Work.NN.Final.nabla_arr_Pi10`: the `(1,0)`-part `Pi10 f` of an
  antilinear form vanishes, so the form-level closedness `proj02 Jstd (dOne f) = 0` implies the
  array-level closedness `dbarCoord j (f · e_l) = dbarCoord l (f · e_j)` required by the solver;
* `Work.NN.Final.dbarCn_eq_of_basis` (with `A = 0`), which upgrades the componentwise equation
  `∂̄ u · e_j = f · e_j` to the form-level equation;
* the `L²`-endgame `Work.NN.Final.eLpNorm_le_holderNorm_zero_pd`, which converts the
  `holderNorm 1` estimate of the solver into the required `L²` bound.
-/

namespace Work.NN.Final

open scoped NNReal ENNReal ContDiff Topology
open MeasureTheory Set

open Work.NN.Core
open Work.CR.Flat

/-- On a set where a `1`-form is `Jstd`-antilinear its `(1,0)`-part `Pi10` vanishes. -/
private lemma pi10_eq_zero_of_antilinear {n : ℕ} {ρ : Fin n → ℝ} {w : Cn n → Cn n →L[ℝ] ℂ}
    (hanti : ∀ z, z ∈ pd n ρ 4 → ∀ V, w z (JstdCn n z V) = -Complex.I * w z V) :
    ∀ z ∈ pd n ρ 4, Pi10 w z = 0 := by
  intro z hz
  ext V
  have h := hanti z hz V
  rw [JstdCn_apply] at h
  simp only [Pi10_apply, zero_apply]
  rw [h]
  have hI : Complex.I * (-Complex.I * w z V) = w z V := by
    rw [← mul_assoc]
    rw [show Complex.I * -Complex.I = (1 : ℂ) by rw [mul_neg, Complex.I_mul_I]; ring]
    rw [one_mul]
  rw [hI, sub_self, mul_zero]

/-- **The flat case of the uniform `L²`-solvability of `∂̄`, with the conclusion region as a
parameter.**  See the module docstring for the proof. -/
theorem uniformDbarL2_flatCase {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {σ : ℝ} (hσ0 : 0 < σ) (hσ4 : σ < 4) : ∃ C : ℝ, 0 < C ∧ ∀ f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ, (∀ m : ℕ, ContDiff ℝ m f) → (∀ z, z ∈ Work.NN.Final.pd n ρ 4 → ∀ V : Work.NN.Core.Cn n, f z (Work.NN.Core.JstdCn n z V) = -Complex.I * f z V) → (∀ z, z ∈ Work.NN.Final.pd n ρ 4 → ∀ V W : Work.NN.Core.Cn n, Work.NN.Final.proj02 (Work.NN.Core.JstdCn n) (fun z' => Work.NN.Final.dOne f z') z V W = 0) → ∃ u : Work.NN.Core.Cn n → ℂ, ContDiffOn ℝ 1 u (Work.NN.Final.pd n ρ σ) ∧ (∀ z, z ∈ Work.NN.Final.pd n ρ σ → ∀ V : Work.NN.Core.Cn n, Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n) u z V = f z V) ∧ MeasureTheory.eLpNorm u 2 (MeasureTheory.volume.restrict (Work.NN.Final.pd n ρ σ)) ≤ ENNReal.ofReal C * ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α (fun z => f z (Pi.single j 1)) (Work.NN.Final.pd n ρ 4) := by
  classical
  -- the two radius families, and the unfoldings of the two regions
  have hpd4 : pd n ρ 4 = polydisc 0 (fun j => (4 : ℝ) * ρ j) := rfl
  have hpdσ : pd n ρ σ = polydisc 0 (fun j => σ * ρ j) := rfl
  have hρ4 : ∀ j, 0 < (4 : ℝ) * ρ j := fun j => by linarith [hρ j]
  have hρσ : ∀ j, 0 < σ * ρ j := fun j => mul_pos hσ0 (hρ j)
  have hlt : ∀ j, σ * ρ j < (4 : ℝ) * ρ j := fun j => by nlinarith [hρ j, hσ4]
  -- the local `∂̄`-solver: data region `pd n ρ 4`, solution region `pd n ρ σ`
  obtain ⟨T1, Cc, hCcpos, hT1solve, hT1est, -, hT1smooth⟩ :=
    dbarLocalSolver (n := n) hn hα0 hα1 (ρ := fun j => (4 : ℝ) * ρ j)
      (ρ' := fun j => σ * ρ j) hρ4 hρσ hlt
  -- the `L²`-endgame constant on the solution region
  obtain ⟨K, hKpos, hK⟩ := eLpNorm_le_holderNorm_zero_pd (n := n) (α := α) hρ hσ0
  refine ⟨K * Cc 0 + 1, by have h := mul_pos hKpos (hCcpos 0); linarith, ?_⟩
  intro f hf hanti hcl
  -- the coefficient array of `f`
  let F : Fin n → Cn n → ℂ := fun j z => f z (Pi.single j 1)
  -- smoothness of the array
  have hFcd1 : ∀ j, ContDiffOn ℝ 1 (F j) (polydisc 0 (fun j => (4 : ℝ) * ρ j)) := fun j =>
    (hf 1).contDiffOn.clm_apply contDiffOn_const
  have hFcdtop : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (F j)
      (polydisc 0 (fun j => (4 : ℝ) * ρ j)) := fun j =>
    contDiffOn_infty.2 fun m => (hf m).contDiffOn.clm_apply contDiffOn_const
  -- closedness of the array, from the form-level closedness and `Pi10 f = 0`
  have hFclosed : ∀ j l z, z ∈ polydisc 0 (fun j => (4 : ℝ) * ρ j) →
      dbarCoord j (F l) z = dbarCoord l (F j) z := by
    intro j l z hz
    have hz4 : z ∈ pd n ρ 4 := by rw [hpd4]; exact hz
    have h0 : ∀ m i : Fin n, dbarCoord i (fun z' => Pi10 f z' (Pi.single m 1)) z = 0 := by
      intro m i
      have hev : (fun z' => Pi10 f z' (Pi.single m 1)) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
        filter_upwards [(isOpen_pd ρ 4).mem_nhds hz4] with z' hz'
        rw [pi10_eq_zero_of_antilinear hanti z' hz']
        rfl
      rw [Work.CR.Flat.Cauchy.dbarCoord_congr_eventually i hev, dbarCoord]
      simp
    have hkey : dbarCoord j (fun z' => f z' (Pi.single l 1)) z
        - dbarCoord l (fun z' => f z' (Pi.single j 1)) z = 0 := by
      rw [nabla_arr_Pi10 (ξ := f) (hf 1) j l z,
        hcl z hz4 (Pi.single j 1) (Pi.single l 1), h0 l j, h0 j l]
      ring
    exact sub_eq_zero.mp hkey
  -- the solver's clauses, specialised to `F`
  have hFsolve : ∀ j (z : Cn n), z ∈ polydisc 0 (fun j => σ * ρ j) →
      dbarCoord j (T1 F) z = F j z := hT1solve F hFcd1 hFclosed
  have hFest : holderNorm 1 α (T1 F) (polydisc 0 (fun j => σ * ρ j))
      ≤ ENNReal.ofReal (Cc 0) *
          ∑ j, holderNorm 0 α (F j) (polydisc 0 (fun j => (4 : ℝ) * ρ j)) :=
    hT1est F hFcd1 hFclosed
  have hFsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (T1 F) (polydisc 0 (fun j => σ * ρ j)) :=
    hT1smooth F hFcdtop hFclosed
  refine ⟨T1 F, ?_, ?_, ?_⟩
  · -- regularity of the primitive
    rw [hpdσ]
    exact (contDiffOn_infty.mp hFsmooth) 1
  · -- the equation `∂̄ u = f`
    intro z hz V
    have hz4 : z ∈ pd n ρ 4 := pd_mono hρ (le_of_lt hσ4) hz
    have hJ0 : (JstdCn n + 0 : Cn n → Cn n →L[ℝ] Cn n) = JstdCn n := by
      ext z' v
      simp
    have h := dbarCn_eq_of_basis (n := n) (A := (0 : Cn n → Cn n →L[ℝ] Cn n)) (u := T1 F)
      (f := f) (z := z) (ε := 0) (by norm_num)
      (fun v => by rw [hJ0]; exact JstdCn_sq n z v)
      (fun j => by simp)
      (fun v => by rw [hJ0]; exact hanti z hz4 v)
      (fun j => by
        rw [hJ0, stdForm_coef_dbar_std]
        exact hFsolve j z hz)
    rw [hJ0] at h
    exact h V
  · -- the `L²`-estimate
    have hFest' : holderNorm 1 α (T1 F) (pd n ρ σ)
        ≤ ENNReal.ofReal (Cc 0) *
            ∑ j : Fin n, holderNorm 0 α (fun z => f z (Pi.single j 1)) (pd n ρ 4) := by
      rw [hpdσ, hpd4]
      exact hFest
    have hM : holderNorm 0 α (T1 F) (pd n ρ σ)
        ≤ ENNReal.ofReal (Cc 0) *
            ∑ j : Fin n, holderNorm 0 α (fun z => f z (Pi.single j 1)) (pd n ρ 4) :=
      (holderNorm_mono_k (Nat.zero_le 1) α (T1 F) (pd n ρ σ)).trans hFest'
    have haesm : AEStronglyMeasurable (T1 F) (volume.restrict (pd n ρ σ)) :=
      ((contDiffOn_infty.mp hFsmooth) 1).continuousOn.aestronglyMeasurable
        (isOpen_pd ρ σ).measurableSet
    have hmain := hK (T1 F) haesm
      (ENNReal.ofReal (Cc 0) *
        ∑ j : Fin n, holderNorm 0 α (fun z => f z (Pi.single j 1)) (pd n ρ 4)) hM
    refine hmain.trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul hKpos.le]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith [hCcpos 0])) _

end Work.NN.Final
