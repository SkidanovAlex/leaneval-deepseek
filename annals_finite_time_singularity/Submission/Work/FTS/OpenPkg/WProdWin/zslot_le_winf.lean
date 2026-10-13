import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.WProdWin.Basic
import Submission.Work.FTS.OpenPkg.DzIter_le_WlInf_open
import Submission.Work.FTS.OpenPkg.Mixed_le_WlInf_open
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# `zslot_le_winf` — the radial `D_z`-slots of the `𝒲^{4,∞}`-priced product rule

For `f` of class `Work.FTS.EllipticEst.SmoothOpen` (`C^∞` on the *open* quadrant) and of class
`𝒲^{4,∞}` (`Work.Spaces.WlInfMem α 4 f`), and for an arbitrary `SmoothOpen` `g`, every pure
radial slot of the product `f·g` is dominated pointwise by the `𝒲^{4,∞}`-norm of the
coefficient times the `ℋ⁴`-integrand of `g`:

`(D_z^i (f·g)(z,θ) · w(z)/sin(2θ)^{η/2})² ≤ C |f|²_{𝒲^{4,∞}} · HkIntegrand α 4 g z θ`,  `i ≤ 4`,

with a universal constant `C` (here `10^8`), at every *interior* point `z > 0`, `0 < θ < π/2`.

This is the open-quadrant instance of `Work.Spaces.z_term_le` (which is stated for the
`SmoothInt`/`SmoothNbhd` classes, i.e. with smoothness through the boundary `z = 0` and the
angular endpoints).  The proof is the same:

* expand `D_z^i (f·g)` with the Leibniz rule for `D_z = z∂_z` in the open quadrant
  (`Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz`, which needs only `SmoothOpen f`, `SmoothOpen g`
  at `z > 0`, `0 < θ < π/2`);
* bound the square of the finite sum by `card • Σ (·)²` (`sq_sum_le_card_mul_sum_sq`);
* bound each `f`-factor by `100 |f|_𝒲` (`Work.FTS.OpenPkg.DzIter_le_WlInf_open`) and each
  `g`-factor by the corresponding slot of `HkIntegrand α 4 g`
  (`Work.Spaces.sq_le_HkIntegrand_z`, which needs no hypothesis at all since `HkIntegrand` is a
  sum of squares).

Note that `g` is *not* required to lie in `ℋ⁴`: the `g`-side only appears through the
(nonnegative, always finite) integrand `HkIntegrand α 4 g`, which is exactly what the consumer
of this slot bounds by the `ℋ⁴`-norm.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.FTS.OpenPkg.WProdWin

/-- **The radial `D_z`-slot bound.**  Every pure `D_z`-slot `i ≤ 4` of the product `f·g`
(weighted as in `HkIntegrand`) is dominated by `10^8 |f|²_{𝒲^{4,∞}} HkIntegrand α 4 g z θ` at
interior points, for `f` of class `SmoothOpen` ∩ `𝒲^{4,∞}` and `g` merely `SmoothOpen`. -/
theorem zslot_le_winf : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.EllipticEst.SmoothOpen g →
      ∀ i : ℕ, i ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ C * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkIntegrand α 4 g z θ := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro α f g _hα _hα1 hf hfm hg i hi z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hfm
  set Hv : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hHv
  -- the Leibniz expansion of `D_z^i (f·g)` in the open quadrant
  have heq := Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz i f g hf hg z θ hz hθ0 hθ1
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
  -- the per-term bound: the `f`-factor costs `100 |f|_𝒲`, the binomial coefficient costs `16`
  have hper : ∀ b ∈ Finset.range (i + 1),
      (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
          * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
        ≤ 2560000 * (Work.Spaces.WlInf α 4 f) ^ 2
          * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hDf : |Work.Spaces.DzIter b f z θ| ≤ 100 * Work.Spaces.WlInf α 4 f :=
      Work.FTS.OpenPkg.DzIter_le_WlInf_open hf hfm (by omega) hz hθ
    have hx : (Work.Spaces.DzIter b f z θ) ^ 2
        ≤ (100 * Work.Spaces.WlInf α 4 f) ^ 2 := by
      have hB : (0 : ℝ) ≤ 100 * Work.Spaces.WlInf α 4 f := mul_nonneg (by norm_num) hW
      have h1 := (abs_le.mp hDf).1
      have h2 := (abs_le.mp hDf).2
      nlinarith [hB, h1, h2]
    have hch : ((i.choose b : ℝ)) ^ 2 ≤ 256 := Work.Spaces.choose_sq_le_256 i b hbi hi
    calc (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
          * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
        = ((i.choose b : ℝ)) ^ 2 * (Work.Spaces.DzIter b f z θ) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by ring
      _ ≤ 256 * (100 * Work.Spaces.WlInf α 4 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by gcongr
      _ = 2560000 * (Work.Spaces.WlInf α 4 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by ring
  -- each surviving `g`-factor is a pure slot of `HkIntegrand α 4 g`
  have hsumsq : ∑ b ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2
      ≤ 5 * Work.Spaces.HkIntegrand α 4 g z θ := by
    calc ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2
        ≤ ∑ _b ∈ Finset.range (i + 1), Work.Spaces.HkIntegrand α 4 g z θ :=
          Finset.sum_le_sum (fun b _ =>
            Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ (i - b) (by omega))
      _ = ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 4 g z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ 5 * Work.Spaces.HkIntegrand α 4 g z θ := by
          have hnn := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
          have hI2 : (i : ℝ) + 1 ≤ 5 := by exact_mod_cast (by omega : i + 1 ≤ 5)
          nlinarith
  calc (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
            * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
      ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) *
          ∑ b ∈ Finset.range (i + 1),
            (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
              * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2 := hcs
    _ ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1),
          (2560000 * (Work.Spaces.WlInf α 4 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
    _ = 2560000 * (Work.Spaces.WlInf α 4 f) ^ 2 * (((i : ℝ) + 1)
          * ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 2560000 * (Work.Spaces.WlInf α 4 f) ^ 2
          * (5 * (5 * Work.Spaces.HkIntegrand α 4 g z θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hI2 : (i : ℝ) + 1 ≤ 5 := by exact_mod_cast (by omega : i + 1 ≤ 5)
        exact mul_le_mul hI2 hsumsq (Finset.sum_nonneg (fun b _ => sq_nonneg _)) (by norm_num)
    _ ≤ 10 ^ 8 * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkIntegrand α 4 g z θ := by
        have hnn := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
        have h2 : 0 ≤ (Work.Spaces.WlInf α 4 f) ^ 2 := sq_nonneg _
        have hh : 2560000 * (Work.Spaces.WlInf α 4 f) ^ 2
              * (5 * (5 * Work.Spaces.HkIntegrand α 4 g z θ))
            = 64000000 * ((Work.Spaces.WlInf α 4 f) ^ 2
              * Work.Spaces.HkIntegrand α 4 g z θ) := by ring
        rw [hh, show (10 : ℝ) ^ 8 * (Work.Spaces.WlInf α 4 f) ^ 2
              * Work.Spaces.HkIntegrand α 4 g z θ
            = 10 ^ 8 * ((Work.Spaces.WlInf α 4 f) ^ 2
              * Work.Spaces.HkIntegrand α 4 g z θ) from by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg h2 hnn)

end Work.FTS.OpenPkg.WProdWin
