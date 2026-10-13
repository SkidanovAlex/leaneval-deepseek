import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.WProdWin.zslot_le_winf
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ProductRuleInW

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# `zslot_le_winf6` — the radial `D_z`-slots of the `𝒲^{6,∞}`-priced product rule

For `f` of class `Work.FTS.EllipticEst.SmoothOpen` (`C^∞` on the *open* quadrant) and of class
`𝒲^{6,∞}` (`Work.Spaces.WlInfMem α 6 f`), and for an arbitrary `SmoothOpen` `g`, every pure
radial slot of the product `f·g` is dominated pointwise by the `𝒲^{6,∞}`-norm of the coefficient
times the `ℋ⁶`-integrand of `g`:

`(D_z^i (f·g)(z,θ) · w(z)/sin(2θ)^{η/2})² ≤ C |f|²_{𝒲^{6,∞}} · HkIntegrand α 6 g z θ`,  `i ≤ 6`,

with a universal constant `C` (here `10^12`), at every *interior* point `z > 0`, `0 < θ < π/2`.

This is the level-six instance of `Work.FTS.OpenPkg.WProdWin.zslot_le_winf` (the proved level-four
statement).  The proof is the same:

* expand `D_z^i (f·g)` with the Leibniz rule for `D_z = z∂_z` in the open quadrant
  (`Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz`, which needs only `SmoothOpen f`, `SmoothOpen g`
  at `z > 0`, `0 < θ < π/2`);
* bound the square of the finite sum by `card • Σ (·)²` (`sq_sum_le_card_mul_sum_sq`);
* bound each `f`-factor by `1000 |f|_𝒲` (`Work.FTS.StrongPersist.N6Trans.dzIter_le_WlInf6`,
  the level-six instance of the `𝒲^{6,∞}`-bound on the radial derivatives) and each `g`-factor by
  the corresponding slot of `HkIntegrand α 6 g` (`Work.Spaces.sq_le_HkIntegrand_z`, which needs no
  hypothesis at all since `HkIntegrand` is a sum of squares);
* bound the binomial coefficients by `4096` (`Nat.choose_le_two_pow`: `i.choose b ≤ 2^i ≤ 2^6 = 64`
  for `i ≤ 6`).

Note that `g` is *not* required to lie in `ℋ⁶`: the `g`-side only appears through the
(nonnegative, always finite) integrand `HkIntegrand α 6 g`, which is exactly what the consumer
of this slot bounds by the `ℋ⁶`-norm.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.FTS.StrongPersist.H6Rows.wprod6

/-- The binomial coefficients of the rows `0 ≤ n ≤ 6` are at most `20`, in particular
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

theorem zslot_le_winf6 : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
      Work.FTS.EllipticEst.SmoothOpen g →
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
  -- the per-term bound: the `f`-factor costs `1000 |f|_𝒲`, the binomial coefficient costs `4096`
  have hper : ∀ b ∈ Finset.range (i + 1),
      (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
          * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
        ≤ 4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2
          * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hDf : |Work.Spaces.DzIter b f z θ| ≤ 1000 * Work.Spaces.WlInf α 6 f :=
      Work.FTS.StrongPersist.N6Trans.dzIter_le_WlInf6 hf hfm (by omega) hz hθ
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

end Work.FTS.StrongPersist.H6Rows.wprod6
