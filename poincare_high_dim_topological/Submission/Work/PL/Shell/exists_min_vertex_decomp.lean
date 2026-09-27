import Mathlib
import Submission.Work.PL.Shell.Basic

set_option linter.unusedVariables false

namespace Work.PL.Shell

theorem exists_min_vertex_decomp {N : ℕ} {τ : Finset (PL.E N)} {w : PL.E N → ℝ} {v x : PL.E N}
    (hv : v ∈ τ) (hw0 : ∀ y ∈ τ, 0 ≤ w y) (hmin : ∀ y ∈ τ, w v ≤ w y)
    (hsum : ∑ y ∈ τ, w y = 1) (hx : x = ∑ y ∈ τ, w y • y)
    (ht : (τ.card : ℝ) * w v < 1) :
    ∃ z ∈ PL.simp (τ.erase v),
      x = ((τ.card : ℝ) * w v) • Work.PL.Shell.bary τ + (1 - (τ.card : ℝ) * w v) • z := by
  classical
  -- Write `c = |τ| w v`, `d = 1 - c` and `T = τ \ {v}`.
  set T : Finset (PL.E N) := τ.erase v with hT
  set c : ℝ := (τ.card : ℝ) * w v with hc
  set d : ℝ := 1 - c with hd
  have hcard : (τ.card : ℝ) ≠ 0 := by
    have hpos : 0 < τ.card := Finset.card_pos.mpr ⟨v, hv⟩
    exact_mod_cast (ne_of_gt hpos)
  have hdpos : 0 < d := by rw [hd, hc]; linarith [ht]
  have hdne : d ≠ 0 := ne_of_gt hdpos
  -- `c • bary τ = ∑_{y∈τ} w v • y`
  have hsc : ((τ.card : ℝ) * w v) * (τ.card : ℝ)⁻¹ = w v := by
    rw [mul_assoc, mul_comm (w v) ((τ.card : ℝ)⁻¹), ← mul_assoc,
      mul_inv_cancel₀ hcard, one_mul]
  have hA : c • bary τ = ∑ y ∈ τ, w v • y := by
    rw [hc, bary, smul_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun y _ => by rw [hsc]
  -- the scalar identity `∑_{y∈τ}(w y - w v) = 1 - c = d`
  have hτsum : ∑ y ∈ τ, (w y - w v) = 1 - c := by
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, hc, nsmul_eq_mul]
  have hTsum : ∑ y ∈ T, (w y - w v) = d := by
    rw [hT]
    have h := Finset.sum_erase_add τ (fun y => w y - w v) hv
    rw [sub_self, add_zero] at h
    rw [h, hτsum, hd]
  -- `x = c • bary τ + ∑_{y∈τ}(w y - w v) • y`
  have hx1 : x = c • bary τ + ∑ y ∈ τ, (w y - w v) • y := by
    rw [hx, hA, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← add_smul]
    congr 1
    ring
  -- drop the (vanishing) `v`-term, moving to `T = τ \ {v}`
  have hx2 : ∑ y ∈ τ, (w y - w v) • y = ∑ y ∈ T, (w y - w v) • y := by
    rw [hT]
    have h := Finset.sum_erase_add τ (fun y => (w y - w v) • y) hv
    rw [sub_self, zero_smul, add_zero] at h
    exact h.symm
  -- the explicit convex combination `z`, which lies in the simplex on `T`
  have hzmem : T.centerMass (fun y => w y - w v) id ∈ PL.simp T := by
    show T.centerMass (fun y => w y - w v) id ∈ convexHull ℝ (T : Set (PL.E N))
    apply Finset.centerMass_id_mem_convexHull
    · intro y hy
      rw [hT] at hy
      have := hmin y (Finset.mem_of_mem_erase hy)
      linarith
    · rw [hTsum]; exact hdpos
  refine ⟨T.centerMass (fun y => w y - w v) id, hzmem, ?_⟩
  have hdz : d • (T.centerMass (fun y => w y - w v) id)
      = ∑ y ∈ T, (w y - w v) • y := by
    rw [Finset.centerMass, hTsum, smul_smul, mul_inv_cancel₀ hdne, one_smul]
    rfl
  rw [hx1, hx2, hdz]

end Work.PL.Shell
