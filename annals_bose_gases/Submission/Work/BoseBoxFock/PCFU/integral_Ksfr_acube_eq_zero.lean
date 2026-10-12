import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.dictBricks
import Submission.Work.BoseBoxFock.pcfFrameDefs
import Submission.Work.BoseFixR.sampling_sq_sum_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.integral_Ksfr_acube_eq_zero`

The `s`-frame `Ksfr v fc μ N z = Σ_{s ∈ excited (Lab N)} f_L(s)·e^{i⟪kmom s, z⟫}`
(`Work.BoseBoxFock.pcfFrameDefs`) is the sum of the *excited* lattice plane waves: the mode `s = 0`
is the condensate and is excluded (`Work.BoseB7.excited = Finset.univ.erase 0`).  Its integral over
the box `acube ℓ`, `ℓ = ellH v μ`, therefore vanishes identically — the lattice orthogonality
`∫_{acube ℓ} e^{i⟪k,z⟫} dz = 0` for every non-zero lattice momentum `k = ℓ⁻¹•vec m`.

Nothing is changed by the shift `u ↦ u − b` (`b` is a constant): the phase factorises as
`e^{i⟪k,u−b⟫} = e^{i⟪k,−b⟫}·e^{i⟪k,u⟫}` and the first factor is a constant, pulled out of the
integral.  Equivalently (via the pointwise evaluation `Ksfr_eq_lowKer`), this is the statement that
the low-momentum kernel `lowKer` has total integral one — but the direct plane-wave route below
needs neither the Poisson summation nor the `tsum`-interchange.

## The bricks

* `acube_eq_abs_cube` — the centred cube `acube ℓ` is the box `{y | ∀ i, |y i| ≤ ℓ/2}` used by
  `Work.BoseFixR.box_exp_orthogonal`;
* `integral_acube_exp_lattice` — `∫_{acube ℓ} e^{i⟪ℓ⁻¹•vec m,·⟫} = ℓ³·δ_{m,0}`
  (`Work.BoseFixR.box_exp_orthogonal`, itself the scaled change of variables `u = ℓ•y` of the
  unit-cell orthogonality `Work.BoseFixR.integral_unitCell_exp_lattice`);
* `integral_acube_exp_lattice_sub` — the shifted version, with the constant phase pulled out;
* the assembly: `Ksfr` is a *finite* sum over `excited (Lab N)`, so the integral splits
  (`MeasureTheory.integral_finsetSum`, the summands are continuous, hence integrable on the box by
  `MeasureTheory.IntegrableOn.of_bound`), and every summand vanishes because `s ≠ 0` in
  `Lab N = Fin 3 → ZMod (2N+1)` forces `labVec N s ≠ 0` (`Work.BoseFixR.labVec_injective`).

Everything here is axiom-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`, probe
`Submission/Work/BoseBoxFock/PCFU/_probeIKA.lean`).
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The centred cube `acube ℓ` is the "absolute value" box `{y : E3 | ∀ i, |y i| ≤ ℓ/2}`. -/
lemma acube_eq_abs_cube (ℓ : ℝ) :
    Submission.BoseGases.acube ℓ = {y : E3 | ∀ i, |y i| ≤ ℓ / 2} := by
  ext y
  simp only [Submission.BoseGases.mem_acube_iff, Set.mem_ofPred_eq, Set.mem_Icc, abs_le, neg_div]

/-- **Lattice orthogonality of the plane waves on the centred cube.**  For `ℓ > 0` and an integer
label `m : Fin 3 → ℤ`, the integral of the character `u ↦ e^{i⟪ℓ⁻¹•vec m, u⟫}` over `acube ℓ` is
`ℓ³` when `m = 0` and `0` otherwise.  (This is `Work.BoseFixR.box_exp_orthogonal` rewritten on the
centred cube; that lemma is in turn the rescaled unit-cell orthogonality
`Work.BoseFixR.integral_unitCell_exp_lattice`.) -/
lemma integral_acube_exp_lattice {ℓ : ℝ} (hℓ : 0 < ℓ) (m : Fin 3 → ℤ) :
    ∫ u in Submission.BoseGases.acube ℓ,
        Complex.exp (Complex.I * (inner ℝ ((ℓ⁻¹ : ℝ) • Work.BoseB4.vec m) u : ℂ))
      = if m = 0 then ((ℓ : ℂ) ^ 3) else 0 := by
  rw [acube_eq_abs_cube ℓ]
  exact Work.BoseFixR.box_exp_orthogonal hℓ m

/-- **The shifted plane-wave integral vanishes.**  For `ℓ > 0`, a *non-zero* label `m` and any
translation `b`, the phase `u ↦ e^{i⟪ℓ⁻¹•vec m, u−b⟫}` has zero integral over `acube ℓ`: the phase
factorises as `e^{i⟪ℓ⁻¹•vec m,−b⟫}·e^{i⟪ℓ⁻¹•vec m,u⟫}` with a constant first factor, and the second
factor integrates to zero by `integral_acube_exp_lattice`. -/
lemma integral_acube_exp_lattice_sub {ℓ : ℝ} (hℓ : 0 < ℓ) {m : Fin 3 → ℤ} (hm : m ≠ 0)
    (b : E3) :
    ∫ u in Submission.BoseGases.acube ℓ,
        Complex.exp (Complex.I * (inner ℝ ((ℓ⁻¹ : ℝ) • Work.BoseB4.vec m) (u - b) : ℂ)) = 0 := by
  have hpt : (fun u : E3 =>
        Complex.exp (Complex.I * (inner ℝ ((ℓ⁻¹ : ℝ) • Work.BoseB4.vec m) (u - b) : ℂ)))
      = fun u : E3 =>
          Complex.exp (Complex.I * (inner ℝ ((ℓ⁻¹ : ℝ) • Work.BoseB4.vec m) (-b) : ℂ))
          * Complex.exp (Complex.I * (inner ℝ ((ℓ⁻¹ : ℝ) • Work.BoseB4.vec m) u : ℂ)) := by
    funext u
    rw [← Complex.exp_add]
    congr 1
    rw [inner_sub_right, inner_neg_right]
    push_cast
    ring
  rw [hpt, MeasureTheory.integral_const_mul, integral_acube_exp_lattice hℓ m, if_neg hm, mul_zero]

/-- **The `s`-frame integrates to zero over the box.**  `Ksfr` is the sum of the *excited* lattice
plane waves (the condensate mode `s = 0` is excluded), so its integral over `acube (ellH v μ)`
vanishes for every shift `b`. -/
theorem integral_Ksfr_acube_eq_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ} (b : EuclideanSpace ℝ (Fin 3)) :
    ∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
        Work.BoseBoxFock.Ksfr v fc μ N (u - b) = 0 := by
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  -- unfold the frame: a finite sum of shifted plane waves
  have hK : (fun u : E3 => Work.BoseBoxFock.Ksfr v fc μ N (u - b))
      = fun u : E3 => ∑ s ∈ Work.BoseB7.excited (Lab N),
          ((Work.BoseBoxFock.fLh v fc μ N s : ℝ) : ℂ)
            * Complex.exp (Complex.I *
                (inner ℝ (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s) (u - b) : ℂ)) := by
    funext u
    rfl
  rw [hK]
  -- the sum is finite, so the integral splits (continuity: integrable on the box of finite volume)
  rw [MeasureTheory.integral_finsetSum (Work.BoseB7.excited (Lab N)) ?_]
  · -- every summand vanishes: the label is excited, hence its momentum is non-zero
    refine Finset.sum_eq_zero fun s hs => ?_
    have hs0 : s ≠ 0 := (Finset.mem_erase.mp hs).1
    have hm : Work.BoseBoxFock.labVec N s ≠ 0 := by
      intro h
      have h0 : Work.BoseBoxFock.labVec N (0 : Lab N) = 0 := by
        funext i
        simp [Work.BoseBoxFock.labVec]
      refine hs0 (Work.BoseFixR.labVec_injective N ?_)
      rw [h0]
      exact h
    simp only [Work.BoseBoxFock.kmomLab]
    rw [MeasureTheory.integral_const_mul, integral_acube_exp_lattice_sub hℓ hm b, mul_zero]
  · -- integrability of each summand on the box
    intro s _
    refine MeasureTheory.IntegrableOn.of_bound (μ := volume)
      (s := Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ))
      (f := fun u : E3 => ((Work.BoseBoxFock.fLh v fc μ N s : ℝ) : ℂ)
        * Complex.exp (Complex.I *
            (inner ℝ (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s) (u - b) : ℂ)))
      (C := ‖((Work.BoseBoxFock.fLh v fc μ N s : ℝ) : ℂ)‖)
      (Submission.BoseGases.acube_lt_top _ hℓ.le) ?_ ?_
    · exact (by fun_prop : Continuous (fun u : E3 =>
          ((Work.BoseBoxFock.fLh v fc μ N s : ℝ) : ℂ)
            * Complex.exp (Complex.I *
                (inner ℝ (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s)
                  (u - b) : ℂ)))).aestronglyMeasurable
    · filter_upwards with u
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]

end Work.BoseBoxFock.PCFU
