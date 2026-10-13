import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.zslot_le_winf6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mixedMul_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_le_WlInf6_cd6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# `zslot_le_winf6_cd6` — the radial `D_z`-slots of the `𝒲^{6,∞}`-priced product rule,
in the `C⁶`-on-the-open-quadrant class

This is the finite-order (`C⁶` on `Q0 = (0,∞) × (0,π/2)`, rather than `C^∞`) version of
`Work.FTS.StrongPersist.H6Rows.wprod6.zslot_le_winf6`.  For `f` of class
`ContDiffOn ℝ 6 (uncurry f) Q0` and of class `𝒲^{6,∞}` (`WlInfMem α 6 f`), and for an
arbitrary `C⁶` `g`, every pure radial slot of the product `f·g` is dominated pointwise by the
`𝒲^{6,∞}`-norm of the coefficient times the `ℋ⁶`-integrand of `g`:

`(D_z^i (f·g)(z,θ) · w(z)/sin(2θ)^{η/2})² ≤ C |f|²_{𝒲^{6,∞}} · HkIntegrand α 6 g z θ`,
`i ≤ 6`,

with a universal constant `C` (here `10^12`), at every *interior* point `z > 0`,
`0 < θ < π/2`.

The proof is the same as in the `SmoothOpen` case; the only change is that the Leibniz
expansion of `D_z^i` in the open quadrant is taken from `mixedMul_cd6` (the `b = 0` case,
isolated as `DzIter_mul_cd6` below) instead of
`Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz`:

* expand `D_z^i (f·g)` with the Leibniz rule for `D_z = z∂_z`;
* bound the square of the finite sum by `card • Σ (·)²` (`sq_sum_le_card_mul_sum_sq`);
* bound each `f`-factor by `1000 |f|_𝒲` (`dzIter_le_WlInf6_cd6`) and each `g`-factor by the
  corresponding slot of `HkIntegrand α 6 g` (`Work.Spaces.sq_le_HkIntegrand_z`);
* bound the binomial coefficients by `4096` (`Nat.choose_le_two_pow`, `n ≤ 6`).

-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6

/-- The binomial coefficients of the rows `0 ≤ n ≤ 6` are at most `64`, in particular
`squared` they are at most `4096` (via the coarse but purely structural bound
`n.choose k ≤ 2^n ≤ 2^6 = 64`). -/
private theorem choose_sq_le_4096 (n k : ℕ) (_hkn : k ≤ n) (hn : n ≤ 6) :
    ((n.choose k : ℕ) : ℝ) ^ 2 ≤ 4096 := by
  have h1 : n.choose k ≤ 64 := by
    have h2 : n.choose k ≤ 2 ^ n := Nat.choose_le_two_pow n k
    have h3 : 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn
    have h4 : (2 : ℕ) ^ 6 = 64 := by norm_num
    omega
  have h1' : ((n.choose k : ℕ) : ℝ) ≤ 64 := by exact_mod_cast h1
  have h0 : (0 : ℝ) ≤ ((n.choose k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm := mul_self_le_mul_self h0 h1'
  rw [sq]
  norm_num at hm ⊢
  linarith [hm]

/-- **The Leibniz rule for `D_z^i` in the `C⁶`-class on the open quadrant.**
Isolated from `mixedMul_cd6` at `b = 0` (where `D_θ^0 = id`). -/
theorem DzIter_mul_cd6 {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {i : ℕ} (hi : i ≤ 6) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
      = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) *
          (Work.Spaces.DzIter b f z θ * Work.Spaces.DzIter (i - b) g z θ) := by
  have h := mixedMul_cd6 hf hg i 0 (by omega) z θ hz hθ0 hθ1
  simp only [Work.Spaces.mixed, Work.Spaces.DthIter_zero, Nat.zero_sub] at h
  rw [h]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num

theorem zslot_le_winf6_cd6 : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.WlInfMem α 6 f →
      ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
      ∀ i : ℕ, i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ C * (Work.Spaces.WlInf α 6 f) ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
  refine ⟨10 ^ 12, by norm_num, ?_⟩
  intro α f g _hα _hα1 hf hfm hg i hi z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hW : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfm
  set Hv : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hHv
  -- the Leibniz expansion of `D_z^i (f·g)` in the open quadrant
  have heq := DzIter_mul_cd6 hf hg hi hz hθ0 hθ1
  have hsplit : (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv) ^ 2
      = (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
            * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2 := by
    rw [heq, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun b _ => by ring)
  rw [hsplit]
  -- Cauchy-Schwarz for the finite sum
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
      * (Work.Spaces.DzIter (i - b) g z θ * Hv))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  -- the per-term bound: the `f`-factor costs `1000 |f|_𝒲`, the binomial coefficient costs `4096`
  have hper : ∀ b ∈ Finset.range (i + 1),
      (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
          * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
        ≤ 4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2
          * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hDf : |Work.Spaces.DzIter b f z θ| ≤ 1000 * Work.Spaces.WlInf α 6 f :=
      dzIter_le_WlInf6_cd6 hf hfm (by omega) hz hθ
    have hx : (Work.Spaces.DzIter b f z θ) ^ 2
        ≤ (1000 * Work.Spaces.WlInf α 6 f) ^ 2 := by
      have hB : (0 : ℝ) ≤ 1000 * Work.Spaces.WlInf α 6 f := mul_nonneg (by norm_num) hW
      have h1 := (abs_le.mp hDf).1
      have h2 := (abs_le.mp hDf).2
      nlinarith [hB, h1, h2]
    have hch : ((i.choose b : ℝ)) ^ 2 ≤ 4096 := choose_sq_le_4096 i b hbi hi
    calc (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
          * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
        = ((i.choose b : ℝ)) ^ 2 * (Work.Spaces.DzIter b f z θ) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by ring
      _ ≤ 4096 * (1000 * Work.Spaces.WlInf α 6 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by gcongr
      _ = 4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by ring
  -- each surviving `g`-factor is a pure slot of `HkIntegrand α 6 g`
  have hsumsq : ∑ b ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2
      ≤ 7 * Work.Spaces.HkIntegrand α 6 g z θ := by
    calc ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2
        ≤ ∑ _b ∈ Finset.range (i + 1), Work.Spaces.HkIntegrand α 6 g z θ :=
          Finset.sum_le_sum (fun b _ =>
            Work.Spaces.sq_le_HkIntegrand_z α 6 g z θ (i - b) (by omega))
      _ = ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 6 g z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ 7 * Work.Spaces.HkIntegrand α 6 g z θ := by
          have hnn := Work.Spaces.HkIntegrand_nonneg α 6 g z θ
          have hI2 : (i : ℝ) + 1 ≤ 7 := by exact_mod_cast (by omega : i + 1 ≤ 7)
          nlinarith
  calc (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
            * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
      ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) *
          ∑ b ∈ Finset.range (i + 1),
            (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
              * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2 := hcs
    _ ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1),
          (4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
    _ = 4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2 * (((i : ℝ) + 1)
          * ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2
          * (7 * (7 * Work.Spaces.HkIntegrand α 6 g z θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hI2 : (i : ℝ) + 1 ≤ 7 := by exact_mod_cast (by omega : i + 1 ≤ 7)
        exact mul_le_mul hI2 hsumsq (Finset.sum_nonneg (fun b _ => sq_nonneg _)) (by norm_num)
    _ ≤ 10 ^ 12 * (Work.Spaces.WlInf α 6 f) ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
        have hnn := Work.Spaces.HkIntegrand_nonneg α 6 g z θ
        have h2 : 0 ≤ (Work.Spaces.WlInf α 6 f) ^ 2 := sq_nonneg _
        have hh : 4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2
              * (7 * (7 * Work.Spaces.HkIntegrand α 6 g z θ))
            = 200704000000 * ((Work.Spaces.WlInf α 6 f) ^ 2
              * Work.Spaces.HkIntegrand α 6 g z θ) := by ring
        rw [hh, show (10 : ℝ) ^ 12 * (Work.Spaces.WlInf α 6 f) ^ 2
              * Work.Spaces.HkIntegrand α 6 g z θ
            = 10 ^ 12 * ((Work.Spaces.WlInf α 6 f) ^ 2
              * Work.Spaces.HkIntegrand α 6 g z θ) from by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg h2 hnn)

end Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6
