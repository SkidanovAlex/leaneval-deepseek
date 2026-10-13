/-
Copyright: work module for the Elgindi finite-time singularity project.

# `T45AslotLe` — the pointwise `𝒲^{6,∞}`-bound for the slot `D_z^j D_θ^i A`

The level-six rows `T45aRow`/`T6RowGen` pair a slot of the perturbation `A` (bounded
in `𝒲^{6,∞}` by `K`) against a slot of the datum `f`.  The pointwise input of the
assembly is

  `|D_z^j D_θ^i A| ≤ C·K·Abnd α i θ`   (`i + j ≤ 6`, `z > 0`, `θ ∈ (0,π/2)`),

with the angular factor `Abnd α i θ = 1` for `i = 0` and
`Abnd α i θ = (α + sin 2θ)·sin(2θ)^{α/5}` for `i ≥ 1` (the shape produced by
`Spaces.pz_Dth_sup_bound`).

The proof is elementary: `D_z = z ∂_z` expands by the Stirling numbers of the second
kind (`Spaces.DzIter_eq_sum_scoef_diffOn`, which only needs differentiability of the
`z`-slices on the open half-line `(0,∞)`, available from `SmoothOpen`), and each
occurring term `z^k D_θ^i ∂_z^k A` is bounded by

* `Spaces.WlInf_z_bound` (`i = 0`, `|(z+1)^k ∂_z^k A| ≤ |A|_𝒲`), resp.
* `Spaces.pz_Dth_sup_bound` (`i ≥ 1`, `|∂_z^k D_θ^i A| ≤ |A|_𝒲 (1+z)^{-k} Abnd α i θ`),

using only `z^k / (1+z)^k ≤ 1`.  The total coefficient is the Bell number `bell j`,
which is at most `203` for `j ≤ 6`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45Defs
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.DzIter_eq_sum_scoef_diffOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false

/-- The angular factor `(α + sin 2θ)·sin(2θ)^{α/5}` occurring in `Abnd` for `i ≥ 1`. -/
def Xfac (α θ : ℝ) : ℝ := (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)

/-- Unfolding of `Abnd` in terms of `Xfac`. -/
theorem Abnd_eq_Xfac (α : ℝ) (i : ℕ) (θ : ℝ) :
    Abnd α i θ = if i = 0 then 1 else Xfac α θ := rfl

/-- `Abnd α i θ` is the pure angular factor as soon as `i ≠ 0`. -/
theorem Abnd_of_ne_zero {α : ℝ} {i : ℕ} (hi : i ≠ 0) (θ : ℝ) :
    Abnd α i θ = Xfac α θ := by
  simp [Abnd_eq_Xfac, hi]

/-- `Abnd α 0 θ = 1`. -/
theorem Abnd_zero (α θ : ℝ) : Abnd α 0 θ = 1 := by
  simp [Abnd_eq_Xfac]

/-- `Xfac` is nonnegative on the angular interval. -/
theorem Xfac_nonneg {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ : 0 ≤ Real.sin (2 * θ)) :
    0 ≤ Xfac α θ :=
  mul_nonneg (by linarith) (Real.rpow_nonneg hθ _)

/-- `WlInf` is nonnegative whenever it is the honest sum of `L^∞`-norms. -/
theorem WlInf_nonneg (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.WlInfMem α l f) :
    0 ≤ Work.Spaces.WlInf α l f := by
  rw [Work.Spaces.WlInf]
  exact add_nonneg (Work.Spaces.wlZSum_nonneg α l f hmem)
    (Work.Spaces.wlThSum_nonneg α l f hmem)

/-- The Bell numbers of the rows `j ≤ 6` are at most `203`. -/
theorem bell_le_six (j : ℕ) (hj : j ≤ 6) : Work.Spaces.bell j ≤ 203 := by
  interval_cases j <;> decide

/-- The Stirling-weighted sum bound for the rows `j ≤ 6`: if `|z^k ∂_z^k h| ≤ M` for
`k ≤ j` then `|∑_k S(j,k) z^k ∂_z^k h| ≤ 203·M`. -/
theorem abs_sum_scoef_le_six {h : ℝ → ℝ → ℝ} {z θ M : ℝ} {j : ℕ} (hj : j ≤ 6) (hM : 0 ≤ M)
    (hx : ∀ k ≤ j, |z ^ k * Work.Spaces.pzIter k h z θ| ≤ M) :
    |∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ)
        * (z ^ k * Work.Spaces.pzIter k h z θ)| ≤ 203 * M :=
  (Work.Spaces.abs_sum_scoef_mul_le j M (fun k => z ^ k * Work.Spaces.pzIter k h z θ) hx).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast bell_le_six j hj) hM)

/-- **The pointwise slot bound in terms of the `𝒲^{6,∞}`-norm.** -/
theorem mixed_le_WlInf (α : ℝ) (hα : 0 < α) (A : ℝ → ℝ → ℝ)
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hmem : Work.Spaces.WlInfMem α 6 A) :
    ∀ (j i : ℕ), i + j ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i A z θ| ≤ 203 * Work.Spaces.WlInf α 6 A * Abnd α i θ := by
  intro j i hij z θ hz hθ0 hθ1
  have hz0 : 0 ≤ z := le_of_lt hz
  have hz1 : 0 < z + 1 := by linarith
  have hzI : z ∈ Work.Spaces.Iz := hz0
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hθIoo : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ1⟩
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 A := WlInf_nonneg α 6 A hmem
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · -- no angular derivative: `|D_z^j A| ≤ 203·|A|_𝒲`
    have hj6 : j ≤ 6 := by omega
    have hd : ∀ k ≤ j,
        DifferentiableOn ℝ (fun y : ℝ => Work.Spaces.pzIter k A y θ) (Set.Ioi 0) :=
      fun k _ => ((hA.pzIter k).curry_z hθIoo).differentiableOn (by simp)
    have hx : ∀ k ≤ j, |z ^ k * Work.Spaces.pzIter k A z θ| ≤ Work.Spaces.WlInf α 6 A := by
      intro k hk
      have hk6 : k ≤ 6 := by omega
      have h2 : (z + 1) ^ k * |Work.Spaces.pzIter k A z θ| ≤ Work.Spaces.WlInf α 6 A := by
        have h := Work.Spaces.WlInf_z_bound α 6 A hmem k hk6 z θ hzI hθI
        rwa [abs_mul, abs_of_pos (pow_pos hz1 k)] at h
      calc |z ^ k * Work.Spaces.pzIter k A z θ|
          = z ^ k * |Work.Spaces.pzIter k A z θ| := by
            rw [abs_mul, abs_of_nonneg (pow_nonneg hz0 k)]
        _ ≤ (z + 1) ^ k * |Work.Spaces.pzIter k A z θ| :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz0 (by linarith) k) (abs_nonneg _)
        _ ≤ Work.Spaces.WlInf α 6 A := h2
    have hsum := abs_sum_scoef_le_six (h := A) (z := z) (θ := θ)
      (M := Work.Spaces.WlInf α 6 A) hj6 hWnn hx
    have hexp := Work.FTS.EllipticEst.Cores.DiagEstEllT.DzIter_eq_sum_scoef_diffOn
      (h := A) (θ := θ) (U := Set.Ioi 0) (n := j) isOpen_Ioi hd z hz
    rw [Work.Spaces.mixed_zero_right, hexp]
    refine hsum.trans (le_of_eq ?_)
    rw [Abnd_zero]
    ring
  · -- at least one angular derivative
    have hi1 : 1 ≤ i := hipos
    have hi0 : ¬ i = 0 := by omega
    have hj6 : j ≤ 6 := by omega
    have hd : ∀ k ≤ j,
        DifferentiableOn ℝ
          (fun y : ℝ => Work.Spaces.pzIter k (Work.Spaces.DthIter i A) y θ) (Set.Ioi 0) :=
      fun k _ => (((hA.DthIter i).pzIter k).curry_z hθIoo).differentiableOn (by simp)
    have hXnn : 0 ≤ Xfac α θ := Xfac_nonneg hα hs0
    have hx : ∀ k ≤ j,
        |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i A) z θ|
          ≤ Work.Spaces.WlInf α 6 A * Xfac α θ := by
      intro k hk
      have hki : k + i ≤ 6 := by omega
      have hb := Work.Spaces.pz_Dth_sup_bound α hα 6 A hmem i k hi1 hki z θ hzI hθI
      have hzk : 0 ≤ z ^ k := pow_nonneg hz0 k
      have hz1k : 0 < (z + 1) ^ k := pow_pos hz1 k
      have hq : z ^ k / (z + 1) ^ k ≤ 1 :=
        div_le_one_of_le₀ (pow_le_pow_left₀ hz0 (by linarith) k) (le_of_lt hz1k)
      calc |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i A) z θ|
          = z ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter i A) z θ| := by
            rw [abs_mul, abs_of_nonneg hzk]
        _ ≤ z ^ k * (Work.Spaces.WlInf α 6 A / (z + 1) ^ k * Xfac α θ) :=
            mul_le_mul_of_nonneg_left hb hzk
        _ = (z ^ k / (z + 1) ^ k) * (Work.Spaces.WlInf α 6 A * Xfac α θ) := by ring
        _ ≤ 1 * (Work.Spaces.WlInf α 6 A * Xfac α θ) :=
            mul_le_mul_of_nonneg_right hq (mul_nonneg hWnn hXnn)
        _ = Work.Spaces.WlInf α 6 A * Xfac α θ := one_mul _
    have hsum := abs_sum_scoef_le_six (h := Work.Spaces.DthIter i A) (z := z) (θ := θ)
      (M := Work.Spaces.WlInf α 6 A * Xfac α θ) hj6 (mul_nonneg hWnn hXnn) hx
    have hexp := Work.FTS.EllipticEst.Cores.DiagEstEllT.DzIter_eq_sum_scoef_diffOn
      (h := Work.Spaces.DthIter i A) (θ := θ) (U := Set.Ioi 0) (n := j) isOpen_Ioi hd z hz
    change |Work.Spaces.DzIter j (Work.Spaces.DthIter i A) z θ|
      ≤ 203 * Work.Spaces.WlInf α 6 A * Abnd α i θ
    rw [hexp]
    refine hsum.trans (le_of_eq ?_)
    rw [Abnd_of_ne_zero hi0]
    ring

theorem T45AslotLe : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (A : ℝ → ℝ → ℝ) (K : ℝ),
    Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
    Work.Spaces.WlInf α 6 A ≤ K →
    ∀ (j i : ℕ), i + j ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i A z θ|
        ≤ C * K * Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ := by
  refine ⟨203, by norm_num, ?_⟩
  intro α hα A K hA hmem hWK j i hij z θ hz hθ0 hθ1
  have hbase := mixed_le_WlInf α hα.1 A hA hmem j i hij z θ hz hθ0 hθ1
  have hAnn : 0 ≤ Abnd α i θ := Abnd_nonneg hα.1 ⟨le_of_lt hθ0, le_of_lt hθ1⟩ i
  calc |Work.Spaces.mixed j i A z θ|
      ≤ 203 * Work.Spaces.WlInf α 6 A * Abnd α i θ := hbase
    _ ≤ 203 * K * Abnd α i θ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWK (by norm_num)) hAnn

end Work.FTS.StrongPersist.H6Pair6Aux
