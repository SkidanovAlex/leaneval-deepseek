import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Neumann
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# R1 — Neumann box energies (second file: elementary facts)

Foundational facts for the Neumann family of `Submission.Neumann`:

  * the volume of the box (needed for trial states and density normalisations);
  * constant trial states are admissible (`const_neu`, `nonempty_CNeu`);
  * the Neumann energy is nonnegative (`eNeu_nonneg`);
  * every admissible state gives an upper bound on the Neumann energy
    (`eNeu_le_quot`).

Note on the volume: `X N = Fin N → EuclideanSpace ℝ (Fin 3)` with the product
measure; the box `{x | ∀ i k, x i k ∈ Icc 0 L}` is a product of `3·N` intervals
of length `L`, so its volume is `L^(3N)`.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

local notation "⟪" f ", " g "⟫_["N "," L"]" => ∫ x in box N L, f x * g x

/-! ## Volume of the box

The volume of the box is computed by writing it as a product of coordinate
intervals:  `box N L` is a product of `3N` intervals of length `L`.
-/

/-- Volume of the coordinate box `{y | ∀ k, (ofLp y) k ∈ Icc 0 L}` in
`EuclideanSpace ℝ ι`, viewed through the measure-preserving identification of
`EuclideanSpace ℝ ι` with `ι → ℝ`. -/
private lemma volume_coord_box (ι : Type) [Fintype ι] {L : ℝ} (hL : 0 ≤ L) :
    (volume {y : EuclideanSpace ℝ ι | ∀ k : ι, y.ofLp k ∈ Set.Icc 0 L}) =
      ENNReal.ofReal (L ^ (Fintype.card ι)) := by
  let C : Set (ι → ℝ) := {f | ∀ k : ι, f k ∈ Set.Icc 0 L}
  have hCpi : C = (Set.univ : Set ι).pi (fun _ : ι => (Set.Icc 0 L : Set ℝ)) := by
    ext f
    change (∀ k : ι, f k ∈ Set.Icc 0 L) ↔
      ∀ i : ι, i ∈ (Set.univ : Set ι) → f i ∈ Set.Icc 0 L
    exact ⟨fun h i hi => h i, fun h k => h k (Set.mem_univ k)⟩
  have hbox : ({y : EuclideanSpace ℝ ι | ∀ k : ι, y.ofLp k ∈ Set.Icc 0 L}) =
      ((fun y : EuclideanSpace ℝ ι => y.ofLp) ⁻¹' C) := by
    ext y
    change (∀ k : ι, y.ofLp k ∈ Set.Icc 0 L) ↔
      ∀ k : ι, y.ofLp k ∈ Set.Icc 0 L
    exact Iff.rfl
  rw [hbox]
  have hCmeas : MeasurableSet C := by
    rw [hCpi]
    exact MeasurableSet.pi (Set.countable_univ) (fun k hk => measurableSet_Icc)
  have hpre := MeasurePreserving.measure_preimage (PiLp.volume_preserving_ofLp ι)
    hCmeas.nullMeasurableSet
  rw [hpre]
  rw [hCpi]
  rw [MeasureTheory.volume_pi]
  rw [MeasureTheory.Measure.pi_pi (μ := fun _ : ι => (volume : Measure ℝ))
    (s := fun _ : ι => (Set.Icc 0 L : Set ℝ))]
  · simp only [Real.volume_Icc, sub_zero]
    calc
      (∏ i : ι, ENNReal.ofReal L) = (ENNReal.ofReal L) ^ (Fintype.card ι) := by
        simp [Finset.prod_const]
      _ = ENNReal.ofReal (L ^ (Fintype.card ι)) := by
        rw [← ENNReal.ofReal_pow hL]

/-- The coordinate cube `[0,L]³ ⊆ ℝ³` has volume `L³`. -/
private lemma volume_cube {L : ℝ} (hL : 0 ≤ L) :
    (volume (cube L)) = ENNReal.ofReal (L ^ 3) := by
  have h := volume_coord_box (Fin 3) (L := L) hL
  -- rewrite cube in terms of the explicit ofLp coordinates
  rw [show cube L = {y : ℝ³ | ∀ m : Fin 3, y.ofLp m ∈ Set.Icc 0 L} by
    ext y
    simp [cube]]
  simpa using h

/-- `box N L` is a product of `N` copies of the coordinate cube. -/
private lemma volume_box_ennreal {N : ℕ} {L : ℝ} (hL : 0 ≤ L) :
    (volume (box N L)) = ENNReal.ofReal (L ^ (3 * N : ℕ)) := by
  rw [box_eq_pi_cube]
  rw [MeasureTheory.volume_pi]
  rw [MeasureTheory.Measure.pi_pi (μ := fun _ : Fin N => (volume : Measure ℝ³))
    (s := fun _ : Fin N => cube L)]
  · calc
      (∏ i : Fin N, volume (cube L)) = ∏ i : Fin N, ENNReal.ofReal (L ^ 3) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [volume_cube hL]
      _ = (ENNReal.ofReal (L ^ 3)) ^ N := by
        simp [Finset.prod_const]
      _ = (ENNReal.ofReal L ^ 3) ^ N := by
        rw [ENNReal.ofReal_pow hL]
      _ = ENNReal.ofReal L ^ (3 * N) := by
        rw [pow_mul]
      _ = ENNReal.ofReal (L ^ (3 * N : ℕ)) := by
        rw [← ENNReal.ofReal_pow hL (3 * N : ℕ)]

/-- The real volume of the box is `L^(3N)`. -/
lemma volume_box_real {N : ℕ} {L : ℝ} (hL : 0 ≤ L) :
    (volume (box N L)).toReal = L ^ (3 * N : ℕ) := by
  rw [volume_box_ennreal hL]
  rw [ENNReal.toReal_ofReal]
  exact pow_nonneg hL (3 * N : ℕ)

/-- The box volume is positive for `0 < L`. -/
lemma volume_box_pos {N : ℕ} {L : ℝ} (hL : 0 < L) : 0 < (volume (box N L)).toReal := by
  rw [volume_box_real hL.le]
  exact pow_pos hL (3 * N : ℕ)

/-- The constant function `a` is an admissible Neumann state (`a ≠ 0`, `0 < L`). -/
noncomputable def const_neu (N : ℕ) {L : ℝ} (hL : 0 < L) (a : ℝ) (ha : a ≠ 0) : CNeu N L where
  toFun := fun _ : X N => a
  contDiff := by
    exact contDiff_const
  nezero := by
    intro hfun
    have ha0 : a = 0 := by simpa using congrFun hfun (0 : X N)
    exact ha ha0
  sq_pos := by
    have hvol : 0 < (volume (box N L)).toReal := volume_box_pos hL
    have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    change 0 < (∫ x in box N L, a ^ 2)
    rw [setIntegral_const]
    rw [measureReal_def]
    simp
    exact mul_pos hvol ha2

/-- The Neumann trial space is nonempty (`0 < L`). -/
lemma nonempty_CNeu (N : ℕ) {L : ℝ} (hL : 0 < L) : Nonempty (CNeu N L) := by
  exact ⟨const_neu N hL 1 one_ne_zero⟩

/-- The box norm of the constant state is `|a|·L^(3N/2)`; in particular the
box integral of its square equals `a²·L^(3N)`. -/
lemma const_sq_box {N : ℕ} {L : ℝ} (hL : 0 ≤ L) (a : ℝ) :
    (∫ x in box N L, ((fun _ : X N => a) x) ^ 2) = a ^ 2 * L ^ (3 * N : ℕ) := by
  rw [setIntegral_const]
  rw [measureReal_def]
  simp
  rw [volume_box_real hL]
  ring

/-- The Neumann ground-state energy is nonnegative (`0 < L`, `0 ≤ v`). -/
lemma eNeu_nonneg {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v) :
    0 ≤ eNeu N L v := by
  let Phi₀ : CNeu N L := const_neu N hL 1 one_ne_zero
  unfold eNeu
  exact le_csInf (s := Set.range (fun Φ : CNeu N L =>
      (kinNeu N L Φ + intNeu N L v Φ) / (∫ x in box N L, ((Φ : X N → ℝ) x) ^ 2)))
    ⟨_, ⟨Phi₀, rfl⟩⟩ (by
      intro y hy
      rcases hy with ⟨Φ, rfl⟩
      exact eNeu_quot_nonneg (N := N) (L := L) (v := v) hv Φ)

/-- Every admissible state gives an upper bound on the Neumann energy. -/
lemma eNeu_le_quot {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hv : 0 ≤ v) (Φ : CNeu N L) :
    eNeu N L v ≤ (kinNeu N L Φ + intNeu N L v Φ) /
      (∫ x in box N L, ((Φ : X N → ℝ) x) ^ 2) := by
  unfold eNeu
  exact ciInf_le (eNeu_quot_bddBelow (N := N) (L := L) (v := v) hv) Φ

end BoseGases

end Submission
