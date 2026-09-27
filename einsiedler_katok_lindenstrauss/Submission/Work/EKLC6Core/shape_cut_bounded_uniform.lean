import Mathlib
import Submission.Work.EKLC6Core.cutSetup
import Submission.Work.EKLC6Core.atom_gen_cut
import Submission.Work.EKLC6Core.margin_shape
import Submission.Work.EKLProd.prodBox_mul_inv_entries_bound

/-!
# `Work.EKLC6Core.shape_cut_bounded_uniform` — uniform entrywise bound for the cut shape

`S : CutData μ U ε` is the cell/lift data of the "cut" construction (Pisa 7.38) and
`M = σ (range (genCell S O ·) ∪ {S.bad})` is the cut σ-algebra.  `atom_gen_cut` computes, for
`y ∈ S.cell i`,

`atom_M y = {w ∈ cell i | ∃ v ∈ U, lift i w = v * lift i y}`.

Hence a `u ∈ U` with `u • y ∈ atom_M y` satisfies

`lift i (u • y) = v * lift i y` with `v ∈ U`, and since both `lift i (u • y)` and `lift i y`
lie in `V (10 ρ) · (S.g i)`, say `lift i (u • y) = ca * S.g i` and `lift i y = cb * S.g i`
with `ca, cb ∈ V (10 ρ)`, right cancellation of `S.g i` gives `v = ca * cb⁻¹`.  Freeness of
the `U`-orbit of `y` upgrades `v • y = u • y` to `v = u`.  So

`shape M U y ⊆ (V (10 ρ)) · (V (10 ρ))⁻¹`,

and the entries of such a product are bounded by an absolute constant (the `3 × 3` product of
the entrywise bounds `1 + 10ρ` for `V (10ρ)` and `2 (1 + 10ρ)²` for its inverse):

`|(u - 1) i j| < 3 (1 + 10ρ) (2 (1 + 10ρ)²) + 1 < 100 (1 + 10ρ)³`.

This is the uniform (= explicit constant) form of `shape_cut_bounded`, which is what the
downstream margin argument (`margin_shape`) needs, since the constant has to be exhibited.
-/

open MeasureTheory Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- Entrywise bound for `a * b⁻¹` with `a, b ∈ V ε`: every entry of `a * b⁻¹ - 1` is smaller
than `100 (1 + ε)³`, for `ε > 0`.

The entries of `a` and `b` are bounded by `1 + ε` (`abs_entry_le_of_mem_V`), those of `b⁻¹` by
`2 (1 + ε)²` (`inv_entry_le`, the entries of the inverse being `2 × 2` minors), and an entry of a
product of two `3 × 3` matrices by `3` times the product of the entrywise bounds
(`abs_mul_entries_le`); finally `|x - 1 i j| ≤ |x| + 1` and `(1 + ε)³ ≥ 1`, so the crude constant
`100 (1 + ε)³` absorbs the `6 (1 + ε)³ + 1` obtained this way. -/
lemma entry_bound_V_mul_inv {ε : ℝ} (hε : 0 < ε) {a b : SL3} (ha : a ∈ V ε) (hb : b ∈ V ε)
    (i j : Fin 3) :
    |(a * b⁻¹ : SL3) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < 100 * (1 + ε) ^ 3 := by
  have hmul : |(a * b⁻¹ : SL3) i j| ≤ 3 * ((1 + ε) * (2 * (1 + ε) ^ 2)) :=
    Work.EKLProd.abs_mul_entries_le (A := a) (B := b⁻¹) (by positivity) (by positivity)
      (fun p q => Work.EKLProd.abs_entry_le_of_mem_V ha p q)
      (fun p q => Work.EKLProd.inv_entry_le hε hb p q) i j
  have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  have htri : |(a * b⁻¹ : SL3) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
      ≤ |(a * b⁻¹ : SL3) i j| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by
    simpa [sub_eq_add_neg] using abs_add_le ((a * b⁻¹ : SL3) i j)
      (-(1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
  have hcube : 1 ≤ (1 + ε) ^ 3 := by nlinarith [hε, sq_nonneg ε, sq_nonneg (1 + ε)]
  nlinarith [htri, hmul, hone, hcube]

theorem shape_cut_bounded_uniform {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {U : Subgroup Work.EKLContract.SL3} {ε : ℝ}
    (S : Work.EKLC6Core.CutData μ U ε) (O : ℕ → Set Work.EKLContract.SL3)
    (hOopen : ∀ m, IsOpen (O m))
    (hvis : ∀ z : Work.EKLContract.SL3, ∃ m, z ∈ Work.EKLC6Core.sat U (O m))
    (hsep : ∀ z w : Work.EKLContract.SL3,
      (∀ m, (z ∈ Work.EKLC6Core.sat U (O m) ↔ w ∈ Work.EKLC6Core.sat U (O m))) →
      w ∈ Work.EKLC6Core.sat U ({z} : Set Work.EKLContract.SL3)) :
    ∀ (i : Fin S.N) (y : Work.EKLContract.X3), y ∈ S.cell i →
      (∀ u ∈ U, u • y = y → u = 1) →
      Work.EKLContract.shape (MeasurableSpace.generateFrom (Set.range
        (fun p : Fin S.N × ℕ => Work.EKLC6Core.genCell S O p.1 p.2) ∪ {S.bad})) U y
      ⊆ Work.EKLComp.Uball U (100 * (1 + 10 * S.ρ) ^ 3) := by
  intro i y hy hfree u hu
  -- `shape` unfolds: `u ∈ U` and `u • y` lies in the atom of `y`
  simp only [Work.EKLContract.shape, Set.mem_ofPred_eq] at hu
  obtain ⟨huU, huatom⟩ := hu
  -- the atom of a point of a cell, computed by `atom_gen_cut`
  have hatom := atom_gen_cut S O hOopen hvis hsep i y hy
  rw [hatom] at huatom
  simp only [Set.mem_ofPred_eq] at huatom
  obtain ⟨hcell, v, hvU, hvrel⟩ := huatom
  -- both lifts lie in `V (10ρ) · (S.g i)`
  have h1 := S.lift_bdd i (u • y) hcell
  simp only [shift, Set.mem_ofPred_eq] at h1
  obtain ⟨ca, hca, hca_eq⟩ := h1
  have h2 := S.lift_bdd i y hy
  simp only [shift, Set.mem_ofPred_eq] at h2
  obtain ⟨cb, hcb, hcb_eq⟩ := h2
  -- `v` and `u` induce the same point of `X₃`, hence agree by freeness of the orbit of `y`
  have hvs : v • y = u • y := by
    have h1' : mkX (v * S.lift i y) = v • y := by
      change v • mkX (S.lift i y) = v • y
      rw [S.lift_mk i y hy]
    have h2' : mkX (S.lift i (u • y)) = u • y := S.lift_mk i (u • y) hcell
    rw [← h1', ← hvrel, h2']
  have hfix : (u⁻¹ * v) • y = y := by
    rw [mul_smul, hvs, inv_smul_smul]
  have huv : u⁻¹ * v = 1 := hfree (u⁻¹ * v) (U.mul_mem (U.inv_mem huU) hvU) hfix
  have hufree : u = v := by
    calc u = u * (u⁻¹ * v) := by rw [huv, mul_one]
         _ = v := by group
  -- cancelling `S.g i` turns `ca * S.g i = v * cb * S.g i` into `v = ca * cb⁻¹`
  have hfac : v = ca * cb⁻¹ := by
    have h : ca * S.g i = v * (cb * S.g i) := by rw [hca_eq, hvrel, hcb_eq]
    have h' : ca = v * cb := by
      calc ca = ca * S.g i * (S.g i)⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
           _ = v * (cb * S.g i) * (S.g i)⁻¹ := by rw [h]
           _ = v * cb := by rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
    rw [h']
    group
  rw [hufree, hfac]
  exact ⟨by rw [← hfac, ← hufree]; exact huU,
    fun p q => entry_bound_V_mul_inv (by linarith [S.hρ]) hca hcb p q⟩

end Work.EKLC6Core
