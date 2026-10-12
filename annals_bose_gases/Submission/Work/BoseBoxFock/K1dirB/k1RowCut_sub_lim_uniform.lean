import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseBoxFock.K1pairingDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1dirB.k1RowCut_sub_lim_uniform`

The cut lattice row `k1RowCut ℓ fu N' F` converges **uniformly in the position variable** to the
full lattice series `k1RowLim ℓ F`, for every coefficient family `F` with the order-`52` lattice
decay

    ‖F n‖ ≤ C · (1 + ‖vec n‖²)⁻⁵² .

## Route

Split the difference into the two already-proved halves of the truncation:

* `k1Row ℓ N' F − k1RowCut ℓ fu N' F` — the *cut* part.  By `k1uvCut_eq_one` the cut-off `uvCut`
  equals `1` on every lattice mode of the cube `Lab N'` whose momentum vector lies in the ball of
  radius `N'/4`, so the difference is supported on that ball's exterior and is bounded by the
  ball tail `Σ'_{‖latVec n‖ ≥ N'/4} ‖F n‖` (`k1Row_sub_cut_le`);
* `k1Row ℓ N' F − k1RowLim ℓ F` — the *truncation* part, bounded by the cube tail
  (`k1Row_tendsto`).

The first tail is small for `N'` large: the family `n ↦ ‖F n‖` is summable (dominance by the
summable order-`52` weight, `summable_vec_inv_one_add_norm_sq`), so its tails over the exterior of
any lattice ball of radius `Λ` are small at large `Λ` (`tail_le_of_summable`).  Taking
`N ≥ 4Λ` turns the threshold `N'/4` into `Λ`.

Both halves are `ε/2`-small and the triangle inequality finishes the proof.  No analytic input
beyond the two proved rows is used.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock.K1dirB

theorem k1RowCut_sub_lim_uniform {ℓ : ℝ} (hℓ : 0 < ℓ)
    (fu : Work.BoseBoxFix.LowCut) {F : (Fin 3 → ℤ) → ℂ}
    (hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖F n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' → ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseBoxFock.k1RowCut ℓ fu N' F z - Work.BoseBoxFock.k1RowLim ℓ F z‖ ≤ ε := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  -- the modulus family is summable, by dominance with the order-`52` lattice weight
  have hsummF : Summable (fun n : Fin 3 → ℤ => ‖F n‖) := by
    obtain ⟨C, _hC0, hC⟩ := hF
    exact Summable.of_nonneg_of_le
      (f := fun n : Fin 3 → ℤ => C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹)
      (g := fun n : Fin 3 → ℤ => ‖F n‖)
      (fun n => norm_nonneg _) (fun n => hC n)
      ((summable_vec_inv_one_add_norm_sq (k := 52) (by norm_num)).mul_left C)
  -- the exterior of every large lattice ball carries an arbitrarily small amount of `‖F‖`
  obtain ⟨Λ, hΛ⟩ := tail_le_of_summable
    (k := fun n : Fin 3 → ℤ => ‖Work.BoseBoxFock.latVec n‖)
    (f := fun n : Fin 3 → ℤ => ‖F n‖) (fun n => norm_nonneg _) hsummF (ε / 2) hε2
  -- the cube tail
  obtain ⟨N₂, hN₂⟩ := k1Row_tendsto hℓ hF (ε / 2) hε2
  refine ⟨max (max ⌈4 * Λ⌉₊ N₂) 1, fun N' hN' z => ?_⟩
  have hNΛ : ⌈4 * Λ⌉₊ ≤ N' :=
    le_trans (le_trans (le_max_left ⌈4 * Λ⌉₊ N₂) (le_max_left (max ⌈4 * Λ⌉₊ N₂) 1)) hN'
  have hN₂' : N₂ ≤ N' :=
    le_trans (le_trans (le_max_right ⌈4 * Λ⌉₊ N₂) (le_max_left (max ⌈4 * Λ⌉₊ N₂) 1)) hN'
  have hN₁ : 1 ≤ N' := le_trans (le_max_right (max ⌈4 * Λ⌉₊ N₂) 1) hN'
  have hthr : Λ ≤ (N' : ℝ) / 4 := by
    have h1 : 4 * Λ ≤ ((⌈4 * Λ⌉₊ : ℕ) : ℝ) := Nat.le_ceil (4 * Λ)
    have h2 : ((⌈4 * Λ⌉₊ : ℕ) : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hNΛ
    linarith
  have hball : (∑' n : Fin 3 → ℤ,
      (if (N' : ℝ) / 4 ≤ ‖Work.BoseBoxFock.latVec n‖ then ‖F n‖ else 0)) ≤ ε / 2 :=
    hΛ ((N' : ℝ) / 4) hthr
  have hcut : ‖k1Row ℓ N' F z - k1RowCut ℓ fu N' F z‖
      ≤ ∑' n : Fin 3 → ℤ,
        (if (N' : ℝ) / 4 ≤ ‖Work.BoseBoxFock.latVec n‖ then ‖F n‖ else 0) :=
    k1Row_sub_cut_le hℓ fu hN₁ hF z
  have hrow : ‖k1Row ℓ N' F z - k1RowLim ℓ F z‖ ≤ ε / 2 := hN₂ N' hN₂' z
  have htri : ‖k1RowCut ℓ fu N' F z - k1RowLim ℓ F z‖
      ≤ ‖k1RowCut ℓ fu N' F z - k1Row ℓ N' F z‖ + ‖k1Row ℓ N' F z - k1RowLim ℓ F z‖ := by
    have h := norm_add_le (k1RowCut ℓ fu N' F z - k1Row ℓ N' F z)
      (k1Row ℓ N' F z - k1RowLim ℓ F z)
    rwa [sub_add_sub_cancel] at h
  rw [norm_sub_rev] at hcut
  linarith

end Work.BoseBoxFock.K1dirB
