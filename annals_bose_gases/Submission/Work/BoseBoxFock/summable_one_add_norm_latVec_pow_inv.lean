import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.farK0_summable_lattice_inv_fourth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv`

The lattice series `Σ_{m ∈ ℤ³} (1 + ‖latVec m‖)^{-N}` converges for every `N ≥ 4`.

The arithmetic content is three-dimensionality: for `m ≠ 0` the integer lattice vector has
Euclidean norm `≥ 1`, hence

`(1 + ‖latVec m‖)^{-N} ≤ (1 + ‖latVec m‖)^{-4} ≤ (‖latVec m‖)^{-4}`,

and `m ↦ (‖latVec m‖⁴)⁻¹` is summable
(`Work.BoseBoxFock.farK0_summable_lattice_inv_fourth`, ultimately
`ZLattice.summable_norm_pow_inv` at rank `3 < 4`).  The single point `m = 0`, where the majorant
vanishes but the summand equals `1`, is absorbed by an explicit delta mass.
-/

namespace Work.BoseBoxFock

noncomputable section

/-- A non-zero integer lattice vector has Euclidean norm at least `1`: some coordinate is a
non-zero integer. -/
private lemma one_le_norm_latVec_summableAux {m : Fin 3 → ℤ} (hm : m ≠ 0) :
    1 ≤ ‖latVec m‖ := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := Function.ne_iff.mp hm
  have h1 : (1 : ℝ) ≤ |((m i : ℤ) : ℝ)| := by
    have h2 : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
    exact_mod_cast h2
  have h2 : ‖(latVec m).ofLp i‖ = |((m i : ℤ) : ℝ)| := by
    have h3 : (latVec m).ofLp i = ((m i : ℤ) : ℝ) := by
      simp [latVec, WithLp.ofLp_toLp]
    rw [h3, Real.norm_eq_abs]
  calc (1 : ℝ) ≤ ‖(latVec m).ofLp i‖ := by rw [h2]; exact h1
    _ ≤ ‖latVec m‖ := PiLp.norm_apply_le (latVec m) i

theorem summable_one_add_norm_latVec_pow_inv {N : ℕ} (hN : 4 ≤ N) :
    Summable (fun m : Fin 3 → ℤ => ((1 + ‖Work.BoseBoxFock.latVec m‖) ^ N)⁻¹) := by
  have hdelta : Summable (fun m : Fin 3 → ℤ => if m = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq (b := (0 : Fin 3 → ℤ)) (a := (1 : ℝ))).summable
  have hmaj : Summable (fun m : Fin 3 → ℤ =>
      (‖latVec m‖ ^ 4)⁻¹ + (if m = 0 then (1 : ℝ) else 0)) :=
    farK0_summable_lattice_inv_fourth.add hdelta
  refine Summable.of_nonneg_of_le
    (f := fun m : Fin 3 → ℤ => (‖latVec m‖ ^ 4)⁻¹ + (if m = 0 then (1 : ℝ) else 0))
    (g := fun m : Fin 3 → ℤ => ((1 + ‖latVec m‖) ^ N)⁻¹)
    (fun m => inv_nonneg.mpr (pow_nonneg (by positivity) N)) (fun m => ?_) hmaj
  by_cases hm : m = 0
  · subst hm
    have hl : latVec (0 : Fin 3 → ℤ) = 0 := by ext i; simp [latVec]
    simp [hl]
  · have ht1 : 1 ≤ ‖latVec m‖ := one_le_norm_latVec_summableAux hm
    have htpos : 0 < ‖latVec m‖ := lt_of_lt_of_le zero_lt_one ht1
    have h3 : ‖latVec m‖ ^ 4 ≤ (1 + ‖latVec m‖) ^ N := by
      have h1 : ‖latVec m‖ ^ 4 ≤ (1 + ‖latVec m‖) ^ 4 :=
        pow_le_pow_left₀ (norm_nonneg _) (by linarith) 4
      have h2 : (1 + ‖latVec m‖) ^ 4 ≤ (1 + ‖latVec m‖) ^ N :=
        pow_le_pow_right₀ (by linarith) hN
      linarith
    have hkey : ((1 + ‖latVec m‖) ^ N)⁻¹ ≤ (‖latVec m‖ ^ 4)⁻¹ :=
      (inv_le_inv₀ (by positivity) (pow_pos htpos 4)).mpr h3
    rw [if_neg hm]
    simpa using hkey

end

end Work.BoseBoxFock
