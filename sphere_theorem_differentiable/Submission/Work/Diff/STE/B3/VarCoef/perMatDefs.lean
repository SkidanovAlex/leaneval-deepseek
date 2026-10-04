import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The periodised chart objects of the SESSION-22 assembly

`perMat D η l h a b` is the periodisation of the **cut-off chart matrix** `η · D.mat l h a b`, and
`perPhi D l` is the periodisation of the chart weight `φ_l = ψ_l · √dens_l`.

They are the objects in which the SESSION-22 assembly of
`Work.Diff.STE.B3.ENormB_pair_J_commutator_v2` is phrased: `η` is a smooth cutoff which is `1` on
the centred cube and whose support lies inside the open centred cube, so that

* `perMat D η l h a b z = D.mat l h a b z` for `z` in the open centred cube
  (lemma `perMat_eq_of_mem_cube` below), while `perMat` is a genuine `1`-periodic function to
  which `flatCut`/`lapPow` (the flat cutoff and the flat Laplacian power) can be applied;
* `perPhi D l z = φ_l z` for `z` in the open centred cube, while `perPhi D l` is `1`-periodic.

The point of this device is that `flatCut ρ ε` and `lapPow k` are Fourier multipliers on the torus,
so every input must be an honest periodic function; on the other hand the CE identity
(`VarCoef.R_Qk_chartExpr_sym`) is stated with the *non*-periodic `D.mat l h a b`, and a differential
operator only sees germs, so replacing `D.mat l h a b` by `perMat D η l h a b` does not change the
action of the operator at the points where the weight `φ_l` is non-zero.
-/

noncomputable section

namespace Work.Diff.STE.B3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The **periodisation of the cut-off chart matrix** `η · D.mat l h a b`. -/
noncomputable def perMat (D : B3Data (I := I) (M := M) ι₀ g₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (l : ι₀) (h : Bil (I := I) (M := M))
    (a b : Fin (Module.finrank ℝ E)) : (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
  fun z => ∑' m : Fin (Module.finrank ℝ E) → ℤ,
    ((η (z + Work.Diff.STE.iVec m) * D.mat l h a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ)

/-- The **periodisation of the chart weight** `φ_l = ψ_l · √dens_l`. -/
noncomputable def perPhi (D : B3Data (I := I) (M := M) ι₀ g₀) (l : ι₀) :
    (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
  fun z => ∑' m : Fin (Module.finrank ℝ E) → ℤ,
    ((D.psi l (z + Work.Diff.STE.iVec m)
      * Real.sqrt (D.dens l (z + Work.Diff.STE.iVec m)) : ℝ) : ℂ)

/-- A lattice translate of a point of the open centred cube leaves the cube as soon as the vector is
non-zero.  (This is the elementary geometric input of the two periodisation lemmas below.) -/
lemma lattice_add_eq_zero_of_mem_cube {n : ℕ} {z : Fin n → ℝ}
    (hz : ∀ j, z j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) {m : Fin n → ℤ}
    (hmem : ∀ j, (z + Work.Diff.STE.iVec m) j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) : m = 0 := by
  funext j
  have h1 : |z j| < 1 / 2 := abs_lt.mpr (hz j)
  have h2 : |(z + Work.Diff.STE.iVec m) j| < 1 / 2 := abs_lt.mpr (hmem j)
  have hi : (Work.Diff.STE.iVec m) j = (m j : ℝ) := rfl
  have h3 : ((m j : ℤ) : ℝ) = (z + Work.Diff.STE.iVec m) j - z j := by
    rw [Pi.add_apply, hi]; ring
  have h4 : |((m j : ℤ) : ℝ)| < 1 := by
    rw [h3]
    calc |(z + Work.Diff.STE.iVec m) j - z j|
        ≤ |(z + Work.Diff.STE.iVec m) j| + |z j| := abs_sub _ _
      _ < 1 / 2 + 1 / 2 := add_lt_add h2 h1
      _ = 1 := by norm_num
  by_contra hne
  have h5 : (1 : ℝ) ≤ |((m j : ℤ) : ℝ)| := by
    have := Int.one_le_abs hne
    exact_mod_cast this
  linarith [h4, h5]

/-- On the ball `‖z‖ ≤ 1/4` the periodised cut-off chart matrix is the chart matrix itself. -/
lemma perMat_eq_of_mem_ball (D : B3Data (I := I) (M := M) ι₀ g₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hη1 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 1 / 4 → η z = 1)
    (hηt : tsupport η ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (l : ι₀) (h : Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E))
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 1 / 4) :
    perMat (I := I) (M := M) D η l h a b z = ((D.mat l h a b z : ℝ) : ℂ) := by
  have hzc : ∀ j : Fin (Module.finrank ℝ E), |z j| ≤ 1 / 4 := fun j =>
    le_trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z j) hz
  have hcube : ∀ j, z j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := fun j =>
    abs_lt.mp (lt_of_le_of_lt (hzc j) (by norm_num))
  rw [perMat]
  rw [tsum_eq_single (0 : Fin (Module.finrank ℝ E) → ℤ)]
  · have h0 : z + Work.Diff.STE.iVec (0 : Fin (Module.finrank ℝ E) → ℤ) = z := by
      funext j
      simp [Work.Diff.STE.iVec]
    rw [h0, hη1 z hz]
    simp
  · intro m hm
    have hzero : η (z + Work.Diff.STE.iVec m) = 0 := by
      by_contra hne
      have hmem := hηt (subset_closure (Function.mem_support.mpr hne))
      rw [Set.mem_pi] at hmem
      exact hm (lattice_add_eq_zero_of_mem_cube hcube
        (fun j => hmem j (Set.mem_univ j)))
    simp [hzero]

/-- On the ball `‖z‖ ≤ 1/4` the periodised weight is `ψ_l · √dens_l`. -/
lemma perPhi_eq_of_mem_ball (D : B3Data (I := I) (M := M) ι₀ g₀) (l : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 1 / 4) :
    perPhi (I := I) (M := M) D l z
      = ((D.psi l z * Real.sqrt (D.dens l z) : ℝ) : ℂ) := by
  have hzc : ∀ j : Fin (Module.finrank ℝ E), |z j| ≤ 1 / 4 := fun j =>
    le_trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z j) hz
  have hcube : ∀ j, z j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := fun j =>
    abs_lt.mp (lt_of_le_of_lt (hzc j) (by norm_num))
  rw [perPhi]
  rw [tsum_eq_single (0 : Fin (Module.finrank ℝ E) → ℤ)]
  · have h0 : z + Work.Diff.STE.iVec (0 : Fin (Module.finrank ℝ E) → ℤ) = z := by
      funext j
      simp [Work.Diff.STE.iVec]
    rw [h0]
  · intro m hm
    have hχ : D.χ l (z + Work.Diff.STE.iVec m) = 0 := by
      by_contra hne
      have hmem := D.hχsupp l (Function.mem_support.mpr hne)
      rw [Set.mem_pi] at hmem
      exact hm (lattice_add_eq_zero_of_mem_cube hcube
        (fun j => hmem j (Set.mem_univ j)))
    have hpsi : D.psi l (z + Work.Diff.STE.iVec m) = 0 := by
      simp only [B3Data.psi, hχ, zero_mul]
    simp [hpsi]

end Work.Diff.STE.B3
