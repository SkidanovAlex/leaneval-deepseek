/-
The pointwise decay estimate for `χ · u` near the closed exterior of the polydisc.

`bumpMul_le_dist_of_flat` is the analytic input of the `C^{k,α}` product estimate
`Work.NN.Core.TelTwoDF.holderNorm_bump_mul_le`: for a `C^{k+1}` cut-off `χ` which vanishes on the
closed exterior `{z | ∃ j, ρ j ≤ ‖z j‖}` of the open polydisc `polydisc 0 ρ` (and whose
derivatives up to order `k+1` are bounded by `L`), and a function `u` which is `C^k` on the
polydisc with all iterated derivatives up to order `k` bounded by `Mu` there, the `m`-th
derivative of the product `χ · u` at an interior point `x` is bounded by
`2 ^ m * L * Mu * ‖x - y‖` for every exterior point `y`.

The gain `‖x - y‖` comes from the first-order flatness of `χ` at the exterior: the Leibniz rule
expresses `D^m (χ · u)` as a sum `∑_i C(m,i) D^i χ · D^{m-i} u`, each factor `D^i χ` carries a
factor `‖x - y‖` (from `Work.NN.Core.TelTwoDF.norm_iteratedFDeriv_le_dist`, which uses the
vanishing of `D^i χ` at `y`), while `D^{m-i} u` is bounded by `Mu`.  Summing the binomial
coefficients `∑_i C(m,i) = 2^m` produces the stated constant.
-/
import Mathlib
import Submission.Work.NN.Core.TelTwoDF.bumpFlatAux

namespace Work.NN.Core.TelTwoDF

theorem bumpMul_le_dist_of_flat {n k : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (k + 1) χ)
    (hχ0 : ∀ z : Fin n → ℂ, (∃ j, ρ j ≤ ‖z j‖) → χ z = 0)
    {L : ℝ} (hL : ∀ i, i ≤ k + 1 → ∀ z, ‖iteratedFDeriv ℝ i χ z‖ ≤ L)
    {u : (Fin n → ℂ) → ℂ} (hu : ContDiffOn ℝ (k : ℕ∞) u (Work.CR.Flat.polydisc 0 ρ))
    {Mu : ℝ} (hu_bd : ∀ j ≤ k, ∀ x, x ∈ Work.CR.Flat.polydisc 0 ρ →
        ‖iteratedFDerivWithin ℝ j u (Work.CR.Flat.polydisc 0 ρ) x‖ ≤ Mu)
    {m : ℕ} (hm : m ≤ k) :
    ∀ x, x ∈ Work.CR.Flat.polydisc 0 ρ → ∀ y, (∃ j, ρ j ≤ ‖y j‖) →
      ‖iteratedFDeriv ℝ m (fun z => χ z * u z) x‖ ≤ 2 ^ m * L * Mu * ‖x - y‖ := by
  intro x hx y hy
  set P : Set (Fin n → ℂ) := Work.CR.Flat.polydisc 0 ρ with hP
  have hPopen : IsOpen P := by rw [hP]; exact Work.CR.Flat.isOpen_polydisc 0 ρ
  have hLnn : 0 ≤ L := le_trans (norm_nonneg _) (hL 0 (by omega) 0)
  have hMunn : 0 ≤ Mu := by
    have h0 : (0 : Fin n → ℂ) ∈ P := by
      rw [hP, Work.CR.Flat.mem_polydisc]; intro j; simpa using hρ j
    exact le_trans (norm_nonneg _) (hu_bd 0 (by omega) 0 h0)
  have hχon : ContDiffOn ℝ (k : ℕ∞) χ P :=
    (hχ.of_le (by exact_mod_cast Nat.le_succ k)).contDiffOn
  have hleib := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (s := P) (f := χ) (g := u)
      (N := (k : ℕ∞)) hχon hu hPopen.uniqueDiffOn hx (n := m) (by exact_mod_cast hm)
  rw [iteratedFDerivWithin_of_isOpen m hPopen hx] at hleib
  refine hleib.trans ?_
  have hterm : ∀ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i χ P x‖ * ‖iteratedFDerivWithin ℝ (m - i) u P x‖
        ≤ (m.choose i : ℝ) * (L * ‖x - y‖) * Mu := by
    intro i hi
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hik : i ≤ k := le_trans him hm
    have hχi : ‖iteratedFDerivWithin ℝ i χ P x‖ ≤ L * ‖x - y‖ := by
      rw [iteratedFDerivWithin_of_isOpen i hPopen hx]
      exact norm_iteratedFDeriv_le_dist hρ hχ hχ0 hL hik x hy
    have hui : ‖iteratedFDerivWithin ℝ (m - i) u P x‖ ≤ Mu :=
      hu_bd (m - i) (le_trans (Nat.sub_le m i) hm) x hx
    exact mul_le_mul (mul_le_mul_of_nonneg_left hχi (Nat.cast_nonneg _)) hui (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hLnn (norm_nonneg _)))
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  have hchoose : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) = (2:ℝ) ^ m := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
  ring

end Work.NN.Core.TelTwoDF
