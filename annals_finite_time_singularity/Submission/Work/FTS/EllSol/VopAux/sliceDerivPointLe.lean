import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllSol.VopAux.SliceDDefs
import Submission.Work.EllipticEst.Blocks.slice_d_alg_core
import Submission.Work.FTS.EllSol.VopAux.SliceTraceDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux

open Work.FTS.EllipticEst

/-- Declare inside `namespace Work.FTS.EllSol.VopAux` so the full name is `Work.FTS.EllSol.VopAux.sliceDerivPointLe`.

Context: `L u θ = sin(2θ)·u'(θ)`, `LopIter i u = (L^[i]) u`, `sliceV u = u''`,
`thEta θ = sin(2θ)^{-η}`, `thGam α θ = sin(2θ)^{-γ}`, `γ = gam α = 1+α/10`,
`sliceW K α w θ = (w θ)²·thEta θ + ∑_{m∈Icc 1 K}(L^m w θ)²·thGam α θ`.

ROUTE. `L (deriv u) = sin(2·) * sliceV u` definitionally, so for `i = j+1`,
`LopIter i (deriv u) = LopIter j (sin(2·) * sliceV u)`; the iterated Leibniz rule on
`sdU = Ioo 0 (π/2)` is `Work.FTS.EllSol.VopAux.sd_LopIter_mul_eqOn` (in `SliceDDefs.lean`,
which also provides `sd_contDiffOn_smoothOrder`, `sd_contDiffOn_deriv`,
`sd_two_sub_gam_le_thEta` (`sin(2θ)^{2-γ} ≤ thEta`, needs `α ≤ 1`),
`sd_four_sub_gam_le_thGam`, `sd_LopIter_sin_sq_bound`, `sd_sum_sq_mul_le`,
`sd_choose_sq_sum_le`), so with `c a = (j.choose a : ℝ)`, `S a = LopIter a sin(2·) θ`,
`Y a = LopIter (j-a) (sliceV u) θ`, `σ = sin(2θ)`, `γ = gam α`:
`LopIter i (deriv u) θ = ∑_{a∈range(j+1)} c a * S a * Y a` (LEFT-associated products).
Then `|c a| ≤ 2^i`, `|S a| ≤ Cs·σ` (hypothesis), and `Y a^2 * σ^(2-γ) ≤ Φ := sliceW K α (sliceV u) θ`:
for `a = j` (`Y = sliceV u`) by `sd_two_sub_gam_le_thEta`; for `a < j` since
`σ^{2-γ} ≤ σ^{-γ} = thGam α θ` (`sin_two_rpow_le_rpow`, `σ ≤ 1` on `Iθ`) and
`LopIter (j-a) (sliceV u) θ²·thGam α θ ≤ sliceW K α (sliceV u) θ` (index in `Icc 1 K`).
Close with `Work.EllipticEst.Blocks.slice_d_alg_core` (`Cc = 2^K`), which gives
`≤ (2^K)²·Cs²·i²·Φ ≤ max 1 ((2^K)²·K²·Cs²)·Φ` using `i ≤ K`, `Φ ≥ 0` (`sliceW_nonneg`). -/
theorem sliceDerivPointLe {u : ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) {K : ℕ} {Cs : ℝ}
    (hCs : 0 ≤ Cs)
    (hSb : ∀ a ≤ K, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.EllipticEst.LopIter a (fun θ : ℝ => Real.sin (2 * θ)) θ|
        ≤ Cs * Real.sin (2 * θ))
    {α : ℝ} (hα1 : α ≤ 1) {i : ℕ} (hi : i ∈ Finset.Icc 1 K) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ
      ≤ max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2)
          * Work.FTS.EllSol.VopAux.sliceW K α (Work.FTS.EllipticEst.sliceV u) θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self hθ
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hiK : i ≤ K := (Finset.mem_Icc.mp hi).2
  obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  subst i
  have hjK : j ≤ K := by omega
  -- `L (deriv u) = sin(2·) · sliceV u` definitionally
  have hiter : LopIter (j + 1) (deriv u)
      = LopIter j ((fun θ : ℝ => Real.sin (2 * θ)) * sliceV u) := by
    simp only [LopIter]
    rw [Function.iterate_succ_apply]
    rfl
  have huso : ContDiffOn ℝ Work.Stability.smoothOrder u sdU := sd_contDiffOn_smoothOrder hu
  have hf : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin (2 * θ)) sdU := by
    fun_prop
  have hg : ContDiffOn ℝ Work.Stability.smoothOrder (sliceV u) sdU := by
    have h := sd_contDiffOn_deriv (sd_contDiffOn_deriv huso)
    simpa only [sliceV] using h
  -- the iterated Leibniz expansion of `L^{j+1}(deriv u)`
  have hleib : LopIter (j + 1) (deriv u) θ
      = ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)
          * (LopIter a (fun θ : ℝ => Real.sin (2 * θ)) θ * LopIter (j - a) (sliceV u) θ) := by
    rw [hiter]
    exact sd_LopIter_mul_eqOn hf hg j hθ
  have hΦ : 0 ≤ sliceW K α (sliceV u) θ := sliceW_nonneg K α (sliceV u) hθI
  have hσ : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθI
  have hCc : 0 ≤ (2 : ℝ) ^ K := by positivity
  have hc : ∀ a ∈ Finset.range (j + 1), |(j.choose a : ℝ)| ≤ (2 : ℝ) ^ K := by
    intro a _
    have h1 : j.choose a ≤ 2 ^ j := Nat.choose_le_two_pow j a
    have h2 : 2 ^ j ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hjK
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    calc ((j.choose a : ℕ) : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast le_trans h1 h2
      _ = (2 : ℝ) ^ K := by push_cast; ring
  have hS : ∀ a ∈ Finset.range (j + 1),
      |LopIter a (fun θ : ℝ => Real.sin (2 * θ)) θ| ≤ Cs * Real.sin (2 * θ) := by
    intro a ha
    exact hSb a (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) hjK) θ hθI
  have hbase : (sliceV u θ) ^ 2 * thEta θ ≤ sliceW K α (sliceV u) θ := by
    rw [sliceW]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun m _ =>
      mul_nonneg (sq_nonneg _) (thGam_nonneg hθI))
  -- the datum slots `Y a²·σ^{2-γ} ≤ Φ`
  have hY : ∀ a ∈ Finset.range (j + 1),
      (LopIter (j - a) (sliceV u) θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        ≤ sliceW K α (sliceV u) θ := by
    intro a ha
    have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    rcases eq_or_lt_of_le haj with h | h
    · -- `a = j`: `Y = sliceV u`, compared through `sd_two_sub_gam_le_thEta`
      subst h
      rw [Nat.sub_self, LopIter_zero]
      have hσγ := sd_two_sub_gam_le_thEta hα1 hθI
      have h2 := mul_le_mul_of_nonneg_left hσγ (sq_nonneg (sliceV u θ))
      linarith [h2, hbase]
    · -- `a < j`: the index `j - a` lies in `Icc 1 K`, so the slot is in `sliceW`
      have hm1 : 1 ≤ j - a := by omega
      have hmK : j - a ≤ K := by omega
      have hσg : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) ≤ thGam α θ := by
        have h := sin_two_rpow_le_rpow (a := 2 - Work.Spaces.gam α)
          (b := -(Work.Spaces.gam α)) (by rw [Work.Spaces.gam]; linarith) (by linarith) hθI
        simpa only [thGam] using h
      have hterm : (LopIter (j - a) (sliceV u) θ) ^ 2 * thGam α θ ≤ sliceW K α (sliceV u) θ := by
        have hsingle := Finset.single_le_sum
          (f := fun m => (LopIter m (sliceV u) θ) ^ 2 * thGam α θ)
          (fun m _ => mul_nonneg (sq_nonneg _) (thGam_nonneg hθI))
          (Finset.mem_Icc.mpr ⟨hm1, hmK⟩)
        rw [sliceW]
        linarith [hsingle, mul_nonneg (sq_nonneg (sliceV u θ)) (thEta_nonneg hθI)]
      have h2 := mul_le_mul_of_nonneg_left hσg (sq_nonneg (LopIter (j - a) (sliceV u) θ))
      linarith [h2, hterm]
  have hcore := Work.EllipticEst.Blocks.slice_d_alg_core (j := j)
      (σ := Real.sin (2 * θ)) (γ := Work.Spaces.gam α)
      (Φ := sliceW K α (sliceV u) θ) (Cc := (2 : ℝ) ^ K) (Cs := Cs)
      hσ hCc hCs hΦ (c := fun a => (j.choose a : ℝ))
      (S := fun a => LopIter a (fun θ : ℝ => Real.sin (2 * θ)) θ)
      (Y := fun a => LopIter (j - a) (sliceV u) θ) hc hS hY
  have hnj : ((j + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by
    have : j + 1 ≤ K := by omega
    exact_mod_cast this
  have hsq : (((j + 1 : ℕ) : ℝ)) ^ 2 ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hnj 2
  have step1 : ((2 : ℝ) ^ K) ^ 2 * Cs ^ 2 * (((j + 1 : ℕ) : ℝ)) ^ 2
      ≤ ((2 : ℝ) ^ K) ^ 2 * Cs ^ 2 * (K : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have step2 : ((2 : ℝ) ^ K) ^ 2 * Cs ^ 2 * (K : ℝ) ^ 2
      ≤ max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2) := by
    refine le_trans (le_of_eq ?_) (le_max_right _ _)
    ring
  calc (LopIter (j + 1) (deriv u) θ) ^ 2 * thGam α θ
      = (∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)
          * (LopIter a (fun θ : ℝ => Real.sin (2 * θ)) θ * LopIter (j - a) (sliceV u) θ)) ^ 2
          * thGam α θ := by rw [hleib]
    _ = (∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)
          * LopIter a (fun θ : ℝ => Real.sin (2 * θ)) θ * LopIter (j - a) (sliceV u) θ) ^ 2
          * thGam α θ := by simp only [mul_assoc]
    _ ≤ ((2 : ℝ) ^ K) ^ 2 * Cs ^ 2 * (((j + 1 : ℕ) : ℝ)) ^ 2
          * (sliceW K α (sliceV u) θ) := hcore
    _ ≤ max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2)
          * sliceW K α (sliceV u) θ :=
        mul_le_mul_of_nonneg_right (le_trans step1 step2) hΦ

end Work.FTS.EllSol.VopAux
