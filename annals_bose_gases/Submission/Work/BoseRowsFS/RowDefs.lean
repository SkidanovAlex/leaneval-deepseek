import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.sampling_sq_sum_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.RowDefs` — the vocabulary of the honest lattice row

The FS §11 row `Σ_{q} Ŵ₁(q)²/‖q‖² ≲ ℓ³ (2π)⁻³∫Ŵ₁(p)²/‖p‖² dp` compares a *lattice* sum
(the box modes `Lab N` of the honest model, i.e. the points `(2π/ℓ)·ℤ³`) with a *continuum*
integral.  This module fixes the small vocabulary that both the row itself and the helper
lemmas about it use:

* `vecZ m` — the lattice vector `m : ℤ³` as a point of `ℝ³` (so that
  `Work.BoseB4.vec m = (2π) • vecZ m` and `kmomLab ℓ N n = (2π/ℓ) • vecZ (labVec N n)`);
* `Kt t z` — the heat kernel `(4πt)^{-3/2}e^{-‖z‖²/4t}` of mass `1`, whose `t`-integral is
  the Newtonian kernel `1/(4π‖z‖)` (`Commons.Analysis.Fourier.heat_integral_Ioi`).

Nothing here is mathematical content beyond bookkeeping; the substance lives in
`Work.BoseRowsFS.honest_lattice_W1sq_le`.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

namespace Work.BoseRowsFS

set_option autoImplicit false

/-! ## 1. The integer lattice as a subset of `ℝ³` -/

/-- The lattice vector `m : ℤ³` as a point of `ℝ³`.  This is `Work.BoseB4.vec m` divided by
`2π`. -/
def vecZ (m : Fin 3 → ℤ) : ℝ³ := WithLp.toLp 2 (fun i : Fin 3 => (m i : ℝ))

lemma vec_eq_smul_vecZ (m : Fin 3 → ℤ) : Work.BoseB4.vec m = (2 * Real.pi) • vecZ m := by
  show WithLp.toLp 2 (fun i : Fin 3 => 2 * Real.pi * (m i : ℝ))
      = (2 * Real.pi) • WithLp.toLp 2 (fun i : Fin 3 => (m i : ℝ))
  rw [← WithLp.toLp_smul]
  congr 1

@[simp] lemma vecZ_zero : vecZ (0 : Fin 3 → ℤ) = 0 := by
  have h : (fun i : Fin 3 => (((0 : Fin 3 → ℤ) i : ℤ) : ℝ)) = (0 : Fin 3 → ℝ) := by
    funext i; simp
  rw [vecZ, h, WithLp.toLp_zero]

lemma vecZ_neg (m : Fin 3 → ℤ) : vecZ (-m) = -vecZ m := by
  have h : (fun i : Fin 3 => (((-m) i : ℤ) : ℝ))
      = -(fun i : Fin 3 => ((m i : ℤ) : ℝ)) := by
    funext i; simp
  rw [vecZ, vecZ, h, WithLp.toLp_neg]

lemma vecZ_sub (m m' : Fin 3 → ℤ) : vecZ (m - m') = vecZ m - vecZ m' := by
  have h : (fun i : Fin 3 => (((m - m') i : ℤ) : ℝ))
      = (fun i : Fin 3 => ((m i : ℤ) : ℝ)) - (fun i : Fin 3 => ((m' i : ℤ) : ℝ)) := by
    funext i; simp
  rw [vecZ, vecZ, vecZ, h, WithLp.toLp_sub]

lemma norm_vec (m : Fin 3 → ℤ) : ‖Work.BoseB4.vec m‖ = 2 * Real.pi * ‖vecZ m‖ := by
  rw [vec_eq_smul_vecZ, norm_smul, Real.norm_of_nonneg (by positivity)]

lemma vecZ_eq_zero_iff (m : Fin 3 → ℤ) : vecZ m = 0 ↔ m = 0 := by
  rw [vecZ, ← WithLp.ofLp_eq_zero, WithLp.ofLp_toLp, funext_iff]
  simp only [Pi.zero_apply]
  constructor
  · intro h
    funext i
    exact_mod_cast h i
  · intro h i
    rw [h]
    simp

lemma norm_vecZ_nonneg (m : Fin 3 → ℤ) : 0 ≤ ‖vecZ m‖ := norm_nonneg _

lemma norm_vecZ_pos {m : Fin 3 → ℤ} (hm : m ≠ 0) : 0 < ‖vecZ m‖ := by
  rw [norm_pos_iff]
  intro h
  exact hm ((vecZ_eq_zero_iff m).mp h)

/-- The squared norm of a lattice vector is the sum of the squares of the coordinates. -/
lemma norm_vecZ_sq (m : Fin 3 → ℤ) : ‖vecZ m‖ ^ 2 = ∑ i, ((m i : ℝ)) ^ 2 := by
  rw [vecZ, EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- A nonzero lattice point is at distance at least `1` from the origin. -/
lemma norm_vecZ_ge_one {m : Fin 3 → ℤ} (hm : m ≠ 0) : 1 ≤ ‖vecZ m‖ := by
  have hsq : (1 : ℝ) ≤ ‖vecZ m‖ ^ 2 := by
    rw [norm_vecZ_sq]
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h
      push Not at h
      exact hm (funext h)
    have h2 : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
    have h3 : (1 : ℝ) ≤ |(((m i : ℤ)) : ℝ)| := by exact_mod_cast h2
    have h4 : (1 : ℝ) ≤ ((m i : ℝ)) ^ 2 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (((m i : ℤ)) : ℝ)]
    have h5 := Finset.single_le_sum (f := fun j : Fin 3 => ((m j : ℝ)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    exact le_trans h4 h5
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_one] at h

/-! ## 2. The heat kernel `Kt` -/

/-- The heat kernel `Kt t z = (4πt)^{-3/2}e^{-‖z‖²/(4t)}` (of total mass `1`). -/
def Kt (t : ℝ) (z : ℝ³) : ℝ := (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-‖z‖ ^ 2 / (4 * t))

@[simp] lemma Kt_even (t : ℝ) (z : ℝ³) : Kt t (-z) = Kt t z := by
  simp only [Kt, norm_neg]

lemma Kt_nonneg {t : ℝ} (ht : 0 < t) (z : ℝ³) : 0 ≤ Kt t z := by
  refine mul_nonneg ?_ (Real.exp_pos _).le
  exact Real.rpow_nonneg (by positivity) _

lemma Kt_pos {t : ℝ} (ht : 0 < t) (z : ℝ³) : 0 < Kt t z := by
  refine mul_pos ?_ (Real.exp_pos _)
  exact Real.rpow_pos_of_pos (by positivity) _

lemma Kt_le {t : ℝ} (ht : 0 ≤ t) (z : ℝ³) : Kt t z ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := by
  rw [Kt]
  refine mul_le_of_le_one_right ?_ ?_
  · exact Real.rpow_nonneg (by positivity) _
  · rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

/-! ## 3. The box lattice `Lab N` inside `ℤ³` -/

@[simp] lemma labVec_zero (N : ℕ) :
    Work.BoseBoxFock.labVec N (0 : Work.BoseBoxFock.Lab N) = 0 := by
  funext i
  simp [Work.BoseBoxFock.labVec]

lemma kmomLab_eq (ℓ : ℝ) (N : ℕ) (n : Work.BoseBoxFock.Lab N) :
    Work.BoseBoxFock.kmomLab ℓ N n
      = (2 * Real.pi / ℓ) • vecZ (Work.BoseBoxFock.labVec N n) := by
  rw [Work.BoseBoxFock.kmomLab, vec_eq_smul_vecZ, smul_smul]
  congr 1
  ring

lemma norm_kmomLab {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (n : Work.BoseBoxFock.Lab N) :
    ‖Work.BoseBoxFock.kmomLab ℓ N n‖
      = (2 * Real.pi / ℓ) * ‖vecZ (Work.BoseBoxFock.labVec N n)‖ := by
  rw [kmomLab_eq, norm_smul, Real.norm_of_nonneg (by positivity)]

end Work.BoseRowsFS
