import Mathlib
import Submission.Commons.Lattice.SuccessiveMinima.Basic
import Submission.Commons.Lattice.SuccessiveMinima.realisation_linearIndependent

/-!
# Covering radius of a lattice in terms of its successive minima (shared commons)

Every point of the ambient space is within `m·(λ_m + ε)` of a lattice point, where
`λ_m` is the largest successive minimum of a full-rank lattice of rank `m` and `ε > 0`
is arbitrary (`covering_radius_le`).  Proof: a family of `m` realising vectors
(`exists_linearIndependent_of_successiveMinimum`) is an `ℝ`-basis of the space; rounding
the coefficients of any `x` in that basis to the nearest integers gives a lattice point at
distance bounded by the sum of the realising norms, itself `≤ m·(λ_m + ε)` by
monotonicity of successive minima.

Also here:

- `successiveMinimum_sublattice_ge`: successive minima are antitone in the lattice order
  (a sublattice has larger successive minima);
- `exists_latticePoint_near_direction`: a lattice point approximating `M·u` (`‖u‖ = 1`,
  `M ≥ 0`) within the same tolerance, with norm within the tolerance of `M` — the metric
  core of the "fundamental domain inside a ball of radius `C·λ`" step in de Saxcé's
  Prop 5 (§3 of the paper): lattice points near prescribed unit directions with controlled
  sizes.

All declarations are Mathlib-only apart from the Commons successive-minima API.
-/

noncomputable section

open Set Filter Metric
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Commons.Lattice.SuccessiveMinima

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]



lemma finrank_E_of_finrank_L (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (m : ℕ) (hm : Module.finrank ℤ L = m) : Module.finrank ℝ E = m := by
  rw [← ZLattice.rank ℝ L, hm]

/-- Covering: every point of `E` is within `m·(λ_m + ε)` of a lattice point. -/
lemma covering_radius_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (m : ℕ) (hm : Module.finrank ℤ L = m) (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : L, ‖x - (v : E)‖ ≤ (m : ℝ) * (successiveMinimum L m + ε) := by
  classical
  obtain ⟨w, hwlin, hwn⟩ := exists_linearIndependent_of_successiveMinimum L m hm hε
  let fam : Fin m → E := fun j => (w j : E)
  have hcard : Fintype.card (Fin m) = Module.finrank ℝ E := by
    simp [finrank_E_of_finrank_L L m hm]
  let b : Module.Basis (Fin m) ℝ E :=
    basisOfLinearIndependentOfCardEqFinrank' (b := fam) hwlin hcard
  have hbe : ∀ j : Fin m, b j = fam j := by
    intro j
    simp [b, fam]
  let a : Fin m → ℝ := fun j => (b.repr x) j
  let n : Fin m → ℤ := fun j => Int.floor (a j)
  let v : L := ∑ j : Fin m, (n j : ℤ) • w j
  refine ⟨v, ?_⟩
  have hvE' : (v : E) = ∑ j : Fin m, ((n j : ℤ) : ℝ) • (w j : E) := by
    simp [v]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Int.cast_smul_eq_zsmul ℝ (n j) (w j : E)]
  have hx : x = ∑ j : Fin m, a j • fam j := by
    calc
      x = ∑ j : Fin m, (b.repr x) j • b j := (Module.Basis.sum_repr b x).symm
      _ = ∑ j : Fin m, (b.repr x) j • fam j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hbe j]
      _ = ∑ j : Fin m, a j • fam j := by
        simp [a]
  have hxw : x = ∑ j : Fin m, a j • (w j : E) := by
    simpa [fam] using hx
  have hdiff : x - (v : E) = ∑ j : Fin m, (a j - ((n j : ℤ) : ℝ)) • (w j : E) := by
    calc
      x - (v : E) = (∑ j : Fin m, a j • (w j : E)) - (∑ j : Fin m, ((n j : ℤ) : ℝ) • (w j : E)) := by
        rw [hxw, hvE']
      _ = ∑ j : Fin m, (a j • (w j : E) - ((n j : ℤ) : ℝ) • (w j : E)) := by
        rw [← Finset.sum_sub_distrib]
      _ = ∑ j : Fin m, (a j - ((n j : ℤ) : ℝ)) • (w j : E) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [sub_smul]
  calc
    ‖x - (v : E)‖ ≤ ∑ j : Fin m, ‖((a j - ((n j : ℤ) : ℝ)) • (w j : E))‖ := by
      rw [hdiff]
      exact norm_sum_le _ _
    _ = ∑ j : Fin m, |a j - ((n j : ℤ) : ℝ)| * ‖(w j : E)‖ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ j : Fin m, 1 * ‖(w j : E)‖ := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (by
        have hge : 0 ≤ a j - ((n j : ℤ) : ℝ) := by
          dsimp [n]
          exact sub_nonneg.mpr (Int.floor_le (a j))
        have hle : a j - ((n j : ℤ) : ℝ) ≤ 1 := by
          dsimp [n]
          have hlt : a j - (Int.floor (a j) : ℝ) < 1 := by
            exact (sub_lt_iff_lt_add).mpr (by simpa [add_comm] using (Int.lt_floor_add_one (a j)))
          exact le_of_lt hlt
        have habs : |a j - ((n j : ℤ) : ℝ)| = a j - ((n j : ℤ) : ℝ) := abs_of_nonneg hge
        rw [habs]
        exact hle) (norm_nonneg _)
    _ = ∑ j : Fin m, ‖(w j : E)‖ := by
      simp
    _ ≤ ∑ j : Fin m, (successiveMinimum L (j.val + 1) + ε) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hwn j
    _ ≤ (m : ℝ) * (successiveMinimum L m + ε) := by
      have hmono : ∀ j : Fin m, successiveMinimum L (j.val + 1) ≤ successiveMinimum L m := by
        intro j
        apply successiveMinimum_mono (L := L)
        · omega
        · rw [hm]
      calc
        ∑ j : Fin m, (successiveMinimum L (j.val + 1) + ε)
            ≤ ∑ j : Fin m, (successiveMinimum L m + ε) := by
          apply Finset.sum_le_sum
          intro j hj
          exact add_le_add (hmono j) (le_rfl)
        _ = (m : ℝ) * (successiveMinimum L m + ε) := by
          simp [Finset.sum_const]
          ring_nf

/-- Successive minima are antitone in the lattice: a sublattice has (weakly) larger
successive minima than the ambient lattice. -/
lemma successiveMinimum_sublattice_ge (L₁ L₂ : Submodule ℤ E) (hle : L₁ ≤ L₂)
    [DiscreteTopology L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₁] [IsZLattice ℝ L₂]
    (i : ℕ) (hi₁ : i ≤ Module.finrank ℤ L₁) :
    successiveMinimum L₂ i ≤ successiveMinimum L₁ i := by
  classical
  have hsub : successiveMinimumSet L₁ i ⊆ successiveMinimumSet L₂ i := by
    intro r hr
    rcases hr with ⟨hr0, f, hlin, hnorm⟩
    let g : Fin i → L₂ := fun j => ⟨(f j : E), hle (f j).property⟩
    have hglin : LinearIndependent ℤ (fun j : Fin i => (g j : E)) := by
      simpa [g] using hlin
    have hgnorm : ∀ j : Fin i, ‖(g j : E)‖ ≤ r := by
      intro j
      simpa [g] using hnorm j
    exact ⟨hr0, g, hglin, hgnorm⟩
  unfold successiveMinimum
  apply le_csInf (nonempty_successiveMinimumSet L₁ i hi₁)
  intro r hr
  exact csInf_le (bddBelow_successiveMinimumSet L₂ i) (hsub hr)

/-- Approximating a point of controlled norm by lattice points at controlled distance:
for `M ≥ 0` and `‖u‖ = 1`, there is a lattice point within distance
`m·(λ_m+ε)` of `M·u`, whose norm is within the same tolerance of `M`. -/
lemma exists_latticePoint_near_direction
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (m : ℕ) (hm : Module.finrank ℤ L = m) (u : E) {ε : ℝ} (hε : 0 < ε)
    {M : ℝ} (hM : 0 ≤ M) (hu : ‖u‖ = 1) :
    ∃ v : L, ‖(v : E) - M • u‖ ≤ (m : ℝ) * (successiveMinimum L m + ε) ∧
      ‖(v : E)‖ ≤ M + (m : ℝ) * (successiveMinimum L m + ε) ∧
      M - (m : ℝ) * (successiveMinimum L m + ε) ≤ ‖(v : E)‖ := by
  classical
  let c : ℝ := (m : ℝ) * (successiveMinimum L m + ε)
  obtain ⟨v, hv⟩ := covering_radius_le L m hm (M • u) hε
  have hvM : ‖M • u - (v : E)‖ ≤ c := by simpa [c] using hv
  have hvM' : ‖(v : E) - M • u‖ ≤ c := by
    simpa [norm_sub_rev] using hvM
  have hmul : ‖M • u‖ = M := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hM, hu, mul_one]
  refine ⟨v, ?_, ?_, ?_⟩
  · simpa [c] using hvM'
  · have hveq : ((v : E) - M • u) + M • u = (v : E) := by abel
    have hmain : ‖((v : E) - M • u) + M • u‖ ≤ ‖(v : E) - M • u‖ + ‖M • u‖ :=
      norm_add_le _ _
    have h₀ : ‖(v : E)‖ ≤ ‖(v : E) - M • u‖ + ‖M • u‖ := by
      simpa [hveq] using hmain
    rw [hmul] at h₀
    linarith
  · have hveq : (M • u - (v : E)) + (v : E) = M • u := by abel
    have hmain : ‖(M • u - (v : E)) + (v : E)‖ ≤ ‖M • u - (v : E)‖ + ‖(v : E)‖ :=
      norm_add_le _ _
    have h₀ : ‖M • u‖ ≤ ‖M • u - (v : E)‖ + ‖(v : E)‖ := by
      simpa [hveq] using hmain
    rw [hmul] at h₀
    linarith

end Commons.Lattice.SuccessiveMinima
